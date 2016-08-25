/*++
 Copyright (c) 2016 Microsoft Corporation

 Module Name:

  rareqs.cpp

 Abstract:
 Implementation of the RAReQS architecture for solving quantified problems based on Janota et al., SAT '12.


 Author:

 Mikolas Janota (MikolasJanota)

 Revision History:
--*/

#include "smt_kernel.h"
#include "qe_mbp.h"
#include "smt_params.h"
#include "ast_util.h"
#include "quant_hoist.h"
#include "ast_pp.h"
#include "model_v2_pp.h"
#include "rareqs.h"
#include "expr_abstract.h"
#include "qe.h"
#include "qe_strategy.h"
#include "label_rewriter.h"
#include "expr_replacer.h"
#include "th_rewriter.h"
#include "model_evaluator.h"
#include "smt_solver.h"
#include "solver.h"
#include "mus.h"
#include "th_rewriter.h"

#include"model_smt2_pp.h"

namespace qe {
namespace rareqs {
    /**
      \brief reference counted block of variables (as vector)
     */
    class var_block {
    protected:
        unsigned       m_ref_count;
        app_ref_vector m_vars;
    public:
        var_block(ast_manager& m) : m_ref_count(0), m_vars(m) {}
        var_block(var_block& o) : m_vars(o.m_vars.m()) { UNREACHABLE(); }
        ast_manager& m() { return m_vars.m(); }
        void append(const var_block& o) { m_vars.append(o.m_vars); }
        void append(const app_ref_vector& o) { m_vars.append(o); }
        void reset() { m_vars.reset(); }
        void push_back(app* a) { m_vars.push_back(a); }
        bool empty() const { return m_vars.empty(); }
        unsigned size() const { return m_vars.size(); }
        app* get(unsigned i) const { return m_vars.get(i); }

        const app_ref_vector&  vars() const { return m_vars;  }
        //
        // Reference counting
        //
        void inc_ref() { ++m_ref_count; }
        void dec_ref() {
            --m_ref_count;
            if (m_ref_count == 0) {
                dealloc(this);
            }
        }
    };

    std::ostream& operator <<(std::ostream& o, const var_block& vb) {
        return o << vb.vars();
    }

    typedef ref<var_block> var_block_ref;
    typedef vector<var_block_ref> prefix;

    /**
      \brief A wrapper for non-quantified solver.
     */
    class kernel {
        ast_manager& m;
        params_ref   m_params;
        ref<solver>  m_solver;

    public:
        kernel(ast_manager& m):
            m(m),
            m_solver(mk_smt_solver(m, m_params, symbol::null))
        {
            m_params.set_bool("model", true);
            m_params.set_uint("relevancy_lvl", 0);
            m_params.set_uint("case_split_strategy", CS_ACTIVITY_WITH_CACHE);
            m_solver->updt_params(m_params);
        }


        solver& s() { return *m_solver; }
        solver const& s() const { return *m_solver; }

        void reset() {
            m_solver = mk_smt_solver(m, m_params, symbol::null);
        }
        void assert_expr(expr* e) {
            m_solver->assert_expr(e);
        }

        void get_core(expr_ref_vector& core) {
            core.reset();
            m_solver->get_unsat_core(core);
            TRACE("qe", m_solver->display(tout << "core: " << core << "\n") << "\n";);
        }
    };

    /**
      \brief create a tail starting at start, from prefix in into prefix out.
     */
    void tail(unsigned start, const prefix& in, prefix& out) {
        for (unsigned i = start; i < in.size(); ++i)
            out.push_back(in[i]);
    }

    void model2substitution(var_block_ref const& vars,
            model_ref const& model, expr_substitution& subs) {
        expr_ref val(vars->m());
        for (unsigned i = 0; i < vars->size(); ++i) {
            model->eval(vars->get(i), val, true);
            subs.insert(vars->get(i), val);
        }
    }

    void get_free_vars(expr* fml, var_block_ref& vars) {
        ast_fast_mark1 mark;
        ptr_vector<expr> todo;
        todo.push_back(fml);
        while (todo.size()) {
            expr* e = todo.back();
            todo.pop_back();
            if (mark.is_marked(e) || is_var(e)) {
                continue;
            }
            mark.mark(e);
            if (is_quantifier(e)) {
                todo.push_back(to_quantifier(e)->get_expr());
                continue;
            }
            SASSERT(is_app(e));
            app* a = to_app(e);
            if (is_uninterp_const(a)) { // TBD generalize for uninterpreted functions.
                vars->push_back(a);
            }
            for (unsigned i = 0; i < a->get_num_args(); ++i) {
                todo.push_back(a->get_arg(i));
            }
        }
    }

    struct prefixed_formula {
        prefixed_formula(ast_manager& m) : m_f(m) {}
        prefix     m_prefix;
        expr_ref   m_f;
        const prefix&  prefix() const { return m_prefix; }
        const expr_ref& f() const { return m_f; }

        std::ostream& display(std::ostream& o) const {
            o << '[' << std::endl;
            for (unsigned i = 0; i < prefix().size(); ++i)
                o << *(prefix().get(i)) << std::endl;
            return o << f() << ']' << std::endl;
        }
    };

    enum quantifier_type {universal, existential};

    quantifier_type opponent(quantifier_type qt) {
        switch (qt) {
        case universal: return existential;
        case existential: return universal;
        }
        UNREACHABLE();
        return existential;
    }

    /**
      The solver creates instances of itself throughout its life.

      If the solver is solving a problem of type EXAYEZ . F the the outermost
      block X is kept as free and F is inserted as a game with the prefix AYEZ.

      If a solver is solving (EAEA), counterexamples are used to instantiate
      the second quantifier resulting into an abstraction of the prefix EA.

      The chain of abstractions share a solver for the unquantified part
      designated as m_sat.  A solver that was not created as an abstraction of
      another solver is called top-level and is responsible for the  creation
      and deletion of m_sat.
    **/
    class rareqs_solver {
        ast_manager&                 m;
        quantifier_type              m_qt;  //!<  quantifier type of the solver
        kernel* const                m_sat; //!<  solver for the unquantified part
        const bool                   m_top_level; //!<  determines if the solver is top-level
        var_block_ref                m_free; //!<  the free variables for which value is computed if a winning move is found
        rareqs_solver*               m_abstraction; //!<  abstraction, i.e. instantiations, of the inserted games
        ptr_vector<prefixed_formula> m_games; //!< sub-games to be solved
        model_ref                    m_model; //!< an assignment to the free variables if a winning move was found

        rareqs_solver(ast_manager& m, quantifier_type qt, kernel* sat)
            : m(m), m_qt(qt), m_sat(sat), m_top_level(false), m_abstraction(NULL) {}
    public:
        rareqs_solver(ast_manager& m, quantifier_type qt)
            : m(m), m_qt(qt), m_sat(alloc(kernel, m)), m_top_level(true), m_abstraction(NULL) {}

        void add_free_vars(var_block_ref& vs) {
            if (m_abstraction) m_abstraction->add_free_vars(vs);
            if (m_free.get() == NULL || m_free->empty()) m_free = vs;
            else m_free->append(*(vs.get()));
        }


        void add_game(prefixed_formula& pf) {
            SASSERT(pf.f().get());
            if (pf.m_prefix.empty()) {
                m_sat->assert_expr(m_qt == existential ? pf.m_f.get() : m.mk_not(pf.m_f));
            }
            else {
                if (m_abstraction == NULL) allocate_abstraction();
                m_games.push_back(alloc(prefixed_formula, m));
                *(m_games.back()) = pf;
            }
        }

        lbool check_winning(const expr_ref_vector& assumptions) {
            if (m_games.empty()) {
                const lbool retv = (m_sat->s()).check_sat(assumptions);
                if (retv == l_true) make_model();
                return retv;
            }

            model_ref cex_model;
            while (1) {
                const lbool has_cand = check_cand(assumptions);
                switch (has_cand) {
                case l_undef: return l_undef;
                case l_false: return l_false;
                }
                unsigned game_index = 0;
                bool cand_winning = true;
                for (; game_index < m_games.size(); ++game_index) {
                    switch (check_cex(assumptions, *(m_games[game_index]), cex_model)) {
                    case l_undef: return l_undef;
                    case l_true:  cand_winning = false; break;
                    case l_false: break;
                    }
                    if (!cand_winning) break;
                }
                if (cand_winning) {
                    make_model();
                    return l_true;
                }
                refine(*(m_games[game_index]), cex_model);
            }
        }

        /**
         \brief Get a winning move, provided that check_winning returned l_true.
         **/
        void get_winning(model_ref& out) {
            SASSERT(m_model.get() != NULL);
            out = m_model;
        }

        virtual ~rareqs_solver() {
            if (m_abstraction) dealloc(m_abstraction);
            std::for_each(m_games.begin(), m_games.end(), delete_proc<prefixed_formula>());
            if (m_top_level) dealloc(m_sat);
        }

        std::ostream& display(std::ostream& o) {
            o << '[' << std::endl;
            o << (m_qt == existential ? 'E' : 'A') << ' ';
            o << *(m_free.get()) << std::endl;
            if (m_abstraction == NULL) { m_sat->s().display(o); o << std::endl; }
            for (unsigned i = 0; i < m_games.size(); ++i) {
                const prefixed_formula& g = *(m_games[i]);
                g.display(o << '[') << ']' << std::endl;
            }
            return o << ']' << std::endl;
        }
    protected:
        lbool check_cand(const expr_ref_vector& assumptions) {
            return m_abstraction ? m_abstraction->check_winning(assumptions)
                                 : m_sat->s().check_sat(assumptions);
        }

        void make_model() {
            model_ref a_model;
            if (m_abstraction) {
                m_abstraction->get_winning(a_model);
            } else {
                m_sat->s().get_model(a_model);
            }
            m_model.reset();
            m_model = alloc(model, m);
            if (m_free.get() == NULL)
                return;
            for (unsigned i = 0; i < m_free->size(); ++i) {
                func_decl * const cd = m_free->get(i)->get_decl();
                if (cd->get_arity()) {
                    SASSERT(0); // TODO
                }
                else {
                    expr* ci = a_model ? a_model->get_const_interp(cd) : NULL;
                    if (!ci) ci = m.get_some_value(cd->get_range());
                    m_model->register_decl(cd, ci);
                }
            }
        }

        /**
        \brief Check if the current candidate is a winning move for the given game.
               If it isn't return the winning move for the counterexample.
        */
        lbool check_cex(const expr_ref_vector& assumptions,
            prefixed_formula& game, /*out*/model_ref& cex_model) {
            model_ref mod;
            // get a candidate from the abstraction
            if (m_abstraction) m_abstraction->get_winning(mod);
            else m_sat->s().get_model(mod);
            TRACE("qe", model_smt2_pp(tout << "candidate\n", m, *(mod.get()), 2););

            prefixed_formula next_game(m); // game for the counterexample

            //  plug in the candidate into the given game
            if (m_free.get()) {
                scoped_ptr<expr_replacer> er = mk_default_expr_replacer(m);
                expr_substitution subst(m);
                model2substitution(m_free, mod, subst);
                er->set_substitution(&subst);
                (*er)(game.f(), next_game.m_f);

                //  simplify the problem
                th_rewriter thw(m);
                thw(next_game.m_f);
            }

            // create a solver for the counterexample
            rareqs_solver game_solver(m, opponent(m_qt));
            game_solver.add_free_vars(game.m_prefix[0]);
            tail(1, game.prefix(), next_game.m_prefix);

            // insert the new game into the new solver
            game_solver.add_game(next_game);
            TRACE("qe", next_game.display(tout << "cex game\n"););
            TRACE("qe", game_solver.display(tout << "cex check\n"););

            // run the new solver
            const lbool retv = game_solver.check_winning(assumptions);
            if (retv == l_true) game_solver.get_winning(cex_model);
            return retv;
        }

        void refine(const prefixed_formula& game, model_ref& cex_model) {
            TRACE("qe", model_smt2_pp(tout << "cex_model\n", m, *(cex_model.get()), 2););
            const prefix& orig_prefix = game.m_prefix;
            expr_substitution strategy(m);
            //model2substitution(orig_prefix[0], cex_model, strategy);
            mk_strategy mk_strategy(m);
            mk_strategy((game.prefix())[0]->vars(), *(cex_model.get()), game.f(), strategy);
            scoped_ptr<expr_replacer> er = mk_default_expr_replacer(m);
            er->set_substitution(&strategy);
            prefixed_formula refined_game(m);
            (*er)(game.f(), refined_game.m_f);
            tail(2, game.prefix(), refined_game.m_prefix);
            if (game.prefix().size() > 1) {
                var_block_ref fresh_vs(alloc(var_block, m));
                freshen(game.prefix().get(1), fresh_vs, refined_game.m_f);
                m_abstraction->add_free_vars(fresh_vs);
            }
            th_rewriter thw(m);
            thw(refined_game.m_f);
            m_abstraction->add_game(refined_game);
            TRACE("qe", refined_game.display(tout << "refined game\n"););
            TRACE("qe", m_abstraction->display(tout << "after refinement\n"););
        }

        void freshen(const var_block_ref& vs, var_block_ref& fresh_vs, expr_ref& f) {
            expr_substitution subst(m);
            for (unsigned i = 0; i < vs->size(); ++i) {
                app * const v = vs->get(i);
                app * const fv = m.mk_fresh_const(v->get_decl()->get_name().str().c_str(),
                    v->get_decl()->get_range());
                subst.insert(v, fv);
                fresh_vs->push_back(fv);
            }
            scoped_ptr<expr_replacer> er = mk_default_expr_replacer(m);
            er->set_substitution(&subst);
            prefixed_formula refined_game(m);
            (*er)(f, f);
        }

        void allocate_abstraction() {
            m_abstraction = alloc(rareqs_solver, m, m_qt, m_sat);
            if (m_free.get())
                m_abstraction->add_free_vars(m_free);
        }
    };

    class rareqs : public tactic {

        struct stats {
            stats() { reset(); }
            void reset() { memset(this, 0, sizeof(*this)); }
        };

        ast_manager&               m;
        params_ref                 m_params;
        stats                      m_stats;
        statistics                 m_st;

        quantifier_type hoist(var_block_ref free_vars, prefixed_formula& game) {
            proof_ref pr(m);
            label_rewriter rw(m);
            rw.remove_labels(game.m_f, pr);
            quantifier_hoister hoist(m);
            get_free_vars(game.f(), free_vars);
            app_ref_vector vars(m);
            hoist.pull_quantifier(false/*existential*/, game.m_f, vars);
            free_vars->append(vars);
            vars.reset();
            const bool no_top_exists = free_vars->empty();
            if (no_top_exists) {
                hoist.pull_quantifier(true/*universal*/, game.m_f, vars);
                free_vars->append(vars);
                vars.reset();
            }
            const quantifier_type top_qt = no_top_exists && free_vars->size() ? universal : existential;
            quantifier_type qt = top_qt;
            while (1) {
                qt = opponent(qt);
                vars.reset();
                hoist.pull_quantifier(qt == universal, game.m_f, vars);
                if (vars.empty()) break;
                var_block_ref tmp(alloc(var_block, m));
                tmp->append(vars);
                game.m_prefix.push_back(tmp);
            }
            return top_qt;
        }
    public:

        rareqs(ast_manager& m, params_ref const& p)
            : m(m)
            , m_params(p)
        {
            reset();
        }

        virtual ~rareqs() {
            reset();
        }

        void updt_params(params_ref const & p) {
        }

        void collect_param_descrs(param_descrs & r) {
        }

        void operator()(/* in */  goal_ref const & in,
            /* out */ goal_ref_buffer & result,
            /* out */ model_converter_ref & mc,
            /* out */ proof_converter_ref & pc,
            /* out */ expr_dependency_ref & core) {
            tactic_report report("rareqs-tactic", *in);
            ptr_vector<expr> fmls;
            mc = 0; pc = 0; core = 0;
            in->get_formulas(fmls);
            prefixed_formula game(m);
            game.m_f = mk_and(m, fmls.size(), fmls.c_ptr());

            // for now:
            // fail if cores.  (TODO)
            // fail if proofs. (TODO)
            fail_if_unsat_core_generation("rareqs", in);
            fail_if_proof_generation("rareqs", in);
            reset();
            TRACE("qe", tout << game.f() << "\n";);

            var_block_ref free_vars(alloc(var_block,m));
            const quantifier_type top_qt = hoist(free_vars, game);
            rareqs_solver rs(m, top_qt);
            rs.add_free_vars(free_vars);
            rs.add_game(game);
            const expr_ref_vector assumptions(m);
            const lbool wins = rs.check_winning(assumptions);
            const lbool is_sat = wins == l_undef ? l_undef
                : (top_qt == existential) == (wins == l_true) ?
                l_true : l_false;
            switch (is_sat) {
            case l_false:
                in->reset();
                in->inc_depth();
                in->assert_expr(m.mk_false());
                result.push_back(in.get());
                break;
            case l_true:
                in->reset();
                in->inc_depth();
                result.push_back(in.get());
                // TODO models
                break;
            case l_undef:
                result.push_back(in.get());
                std::string s = "unknown";
                // TODO message from solver
                throw tactic_exception(s.c_str());
            }
        }

        void collect_statistics(statistics & st) const {
            st.copy(m_st);
        }

        void reset_statistics() {
            m_stats.reset();
        }

        void reset() {
        }

        void cleanup() {
            reset();
        }

        void set_logic(symbol const & l) {
        }

        void set_progress_callback(progress_callback * callback) {
        }

        tactic * translate(ast_manager & m) {
            return alloc(rareqs, m, m_params);
        }
    };
};
};

tactic * mk_rareqs_tactic(ast_manager& m, params_ref const& p) {
    return alloc(qe::rareqs::rareqs, m, p);
}
