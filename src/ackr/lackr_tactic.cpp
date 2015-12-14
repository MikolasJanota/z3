/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

lackr_tactic.cpp

Abstract:

Author:

Mikolas Janota

Revision History:
--*/
#include"tactical.h"
///////////////
#include"inc_sat_solver.h"
#include"qfaufbv_tactic.h"
#include"qfbv_tactic.h"
#include"tactic2solver.h"
///////////////
#include"solve_eqs_tactic.h"
#include"simplify_tactic.h"
#include"propagate_values_tactic.h"
#include"bit_blaster_tactic.h"
#include"elim_uncnstr_tactic.h"
#include"max_bv_sharing_tactic.h"
#include"bv_size_reduction_tactic.h"
#include"ctx_simplify_tactic.h"
#include"nnf_tactic.h"
#include"macro_finder_tactic.h"
///////////////
#include"array_decl_plugin.h"
#include"th_rewriter.h"
#include"ackr_info.h"
#include"lackr_model_converter.h"
#include"model_constructor.h"
///////////////
#include"model_smt2_pp.h"
#include"lackr_params.h"
#include"cooperate.h"
///////////////
#include"array_decl_plugin.h"
#include"simplifier_plugin.h"
#include"basic_simplifier_plugin.h"
#include"array_simplifier_params.h"
#include"array_simplifier_plugin.h"
#include"bv_simplifier_plugin.h"
#include"bool_rewriter.h"

struct simp_wrap {
    inline void operator() (expr * s, expr_ref & r) {
        proof_ref dummy(m);
        simp(s, r, dummy);
    }
    simp_wrap(ast_manager& m)
        : m(m)
        , simp(m)
        , bsp(m)
        , bvsp(m, bsp, bv_par)
        , asp(m, bsp, simp, ar_par)
    {
        params_ref p;
        p.set_bool("local_ctx", true);
        p.set_uint("local_ctx_limit", 10000000);
        p.set_bool("ite_extra_rules", true);
        bsp.get_rewriter().updt_params(p);

        simp.register_plugin(&bsp);
        simp.register_plugin(&bvsp);
    }

    ~simp_wrap() {
        simp.release_plugins();
    }

    ast_manager& m;
    simplifier simp;
    basic_simplifier_plugin bsp;
    bv_simplifier_params bv_par;
    bv_simplifier_plugin bvsp;
    array_simplifier_params ar_par;
    array_simplifier_plugin asp;
};


class lackr_tactic : public tactic {
public:
    lackr_tactic(ast_manager& m, params_ref const& p)
        : m_m(m)
        , m_p(p) {}

    virtual void operator()(goal_ref const & g,
        goal_ref_buffer & result,
        model_converter_ref & mc,
        proof_converter_ref & pc,
        expr_dependency_ref & core) {
        mc = 0;
        ast_manager& m(g->m());
        TRACE("lackr", g->display(tout << "Goal:\n"););
        // conflate all assertions into one conjunction
        ptr_vector<expr> flas;
        g->get_formulas(flas);
        expr_ref f(m);
        f=m.mk_and(flas.size(), flas.c_ptr());
        // running implementation
        m_imp = alloc(imp, m, m_p, f);
        const lbool o = m_imp->operator()();
        flas.reset();
        // report result
        goal_ref resg(alloc(goal, *g, true));
        if (o == l_false) resg->assert_expr(m.mk_false());
        if (o != l_undef) result.push_back(resg.get());
        // report model
        if (g->models_enabled() && (o == l_true)) {
            model_ref abstr_model = m_imp->get_model();
            mc = mk_lackr_model_converter(m, m_imp->get_info(), abstr_model);
        }
    }

    virtual void cleanup() { }

    virtual tactic* translate(ast_manager& m) {
        return alloc(lackr_tactic, m, m_p);
    }

    virtual void set_cancel(bool f) {
        #pragma omp critical (lackr_tactic) 
        {
            if (m_imp) m_imp->set_cancel(f);
        }
    }
private:
    struct imp {
      public:
        imp(ast_manager& m, params_ref p, expr_ref _f)
          : m_m(m)
          , m_p(p)
          , m_fla(m)
          , m_abstr(m)
          , m_sat(0)
          , m_bvutil(m)
          , m_simp(m)
          , m_ackrs(m)
        {
            //simp_wrap _s(m_m);
            //_s(_f, m_fla);     
            m_fla = _f;
        }

        void setup_sat() {
            if (1) {
                //std::cout << "; qfbv sat\n";
                tactic_ref t = mk_qfbv_tactic(m_m, m_p);
                m_sat = mk_tactic2solver(m_m, t.get(), m_p);
            }
            else {
                //std::cout << "; smt sat\n";
                tactic_ref t = mk_qfaufbv_tactic(m_m, m_p);
                m_sat = mk_tactic2solver(m_m, t.get(), m_p);
            }
            SASSERT(m_sat);
            m_sat->set_produce_models(true);
        }

        lbool operator() () {
            setup_sat();
            const bool ok = init();
            if (!ok) return l_undef;
            TRACE("lackr", tout << "sat goal\n"; m_sat->display(tout););
            TRACE("lackr", tout << "run sat\n"; );
            const lbool rv = 1 ? eager() : lazy();
            if (rv == l_true) m_sat->get_model(m_model);

            TRACE("lackr", tout << "sat:" << rv << '\n'; );
            CTRACE("lackr", rv == l_true,
                model_smt2_pp(tout << "abstr_model(\n", m_m, *(m_model.get()), 2); tout << ")\n"; );
            return rv;
          }

        lbool eager() {
            if (!eager_enc()) return l_undef;
            m_sat->assert_expr(m_abstr);
            if (m_sat->check_sat(0, 0) == l_false)
               return l_false;
            checkpoint();
            expr_ref all(m_m);
            all = m_m.mk_and(m_ackrs.size(), m_ackrs.c_ptr());
            m_simp(all);
            m_sat->assert_expr(all);
            return m_sat->check_sat(0, 0);
        }


        lbool lazy() {
            model_constructor mc(m_m, m_info);
            m_sat->assert_expr(m_abstr);
            unsigned ackr_head = 0;
            unsigned it = 0;
            while (1) {
                checkpoint();
                //std::cout << "it: " << ++it << "\n";
                TRACE("lackr", tout << "lazy check\n";);
                const lbool r = m_sat->check_sat(0, 0);
                if (r == l_undef) return l_undef; // give up
                if (r == l_false) return l_false; // abstraction unsat
                // reconstruct model
                model_ref am;
                m_sat->get_model(am);
                const bool mc_res = mc.check(am);
                if (mc_res) return l_true; // model okay
                // refine abstraction
                const vector<model_constructor::app_pair>& conflicts = mc.get_conflicts();
                for (vector<model_constructor::app_pair>::const_iterator i = conflicts.begin();
                     i != conflicts.end(); ++i) {
                    ackr(i->first, i->second);
                }
                while (ackr_head < m_ackrs.size()) {
                    m_sat->assert_expr(m_ackrs.get(ackr_head++));
                }
            }            
        }


        ~imp() {
            const fun2terms_map::iterator e = m_fun2terms.end();
            for (fun2terms_map::iterator i = m_fun2terms.begin(); i != e; ++i) {
                dealloc(i->get_value());
            }
        }

        virtual void set_cancel(bool f) {
            #pragma omp critical (lackr)
            {
                m_cancel = f;
                if (m_sat == NULL) return;
                if (f) m_sat->cancel();
                else m_sat->reset_cancel();
            }
        }

        void checkpoint() {
            if (m_cancel)
                throw tactic_exception(TACTIC_CANCELED_MSG);
            cooperate("lackr");
        }

        ackr_info_ref get_info() {return m_info;}
        model_ref get_model() { return m_model; }
      private:
        typedef obj_hashtable<app>           app_set;
        typedef obj_map<func_decl, app_set*> fun2terms_map;
        ast_manager&                         m_m;
        params_ref                           m_p;
        expr_ref                             m_fla;
        expr_ref                             m_abstr;
        fun2terms_map                        m_fun2terms;
        ackr_info_ref                        m_info;
        scoped_ptr<solver>                   m_sat;
        bv_util                              m_bvutil;
        th_rewriter                          m_simp;
        expr_ref_vector                      m_ackrs;
        model_ref                            m_model;
        volatile bool                        m_cancel;


        bool init() {
            params_ref simp_p(m_p);
//            simp_p.set_bool("pull_cheap_ite", true);
 //           simp_p.set_bool("ite_extra_rules", true);
            m_simp.updt_params(simp_p);
            m_info = alloc(ackr_info, m_m);
            bool iok = collect_terms() && abstract();
            if (!iok) return false;
            return true;
        }

        //
        // Introduce ackermann lemma for the two given terms.
        //
        bool ackr(app * const t1, app * const t2) {
            TRACE("lackr", tout << "ackr "
                << mk_ismt2_pp(t1, m_m, 2)
                << " , "
                << mk_ismt2_pp(t2, m_m, 2) << "\n";);
            const unsigned sz = t1->get_num_args();
            expr_ref_vector eqs(m_m);
            for (unsigned gi = 0; gi < sz; ++gi) {
                expr * const arg1 = t1->get_arg(gi);
                expr * const arg2 = t2->get_arg(gi);
                if (arg1 == arg2) continue;
                if (m_bvutil.is_numeral(arg1) && m_bvutil.is_numeral(arg2)) {
                    SASSERT(arg1 != arg2);
                    TRACE("lackr", tout << "never eq\n";);
                    return true;
                }
                eqs.push_back(m_m.mk_eq(arg1, arg2));
            }
            app * const a1 = m_info->get_abstr(t1);
            app * const a2 = m_info->get_abstr(t2);
            SASSERT(a1);
            SASSERT(a2);
            TRACE("lackr", tout << "abstr1 " << mk_ismt2_pp(a1, m_m, 2) << "\n";);
            TRACE("lackr", tout << "abstr2 " << mk_ismt2_pp(a2, m_m, 2) << "\n";);
            expr_ref lhs(m_m.mk_and(eqs.size(), eqs.c_ptr()), m_m);
            TRACE("lackr", tout << "ackr constr lhs" << mk_ismt2_pp(lhs, m_m, 2) << "\n";);
            expr_ref rhs(m_m.mk_eq(a1, a2),m_m);
            TRACE("lackr", tout << "ackr constr rhs" << mk_ismt2_pp(rhs, m_m, 2) << "\n";);
            expr_ref cg(m_m.mk_implies(lhs, rhs), m_m);
            TRACE("lackr", tout << "ackr constr" << mk_ismt2_pp(cg, m_m, 2) << "\n";);
            expr_ref cga(m_m);
            m_info->abstract(cg, cga);
            m_simp(cga);
            TRACE("lackr", tout << "ackr constr abs:" << mk_ismt2_pp(cga, m_m, 2) << "\n";);
            if (!m_m.is_true(cga)) m_ackrs.push_back(cga);
            return true;
        }

        //
        // Introduce the ackermann lemma for each pair of terms.
        //
        bool eager_enc() {
            const fun2terms_map::iterator e = m_fun2terms.end();
            for (fun2terms_map::iterator i = m_fun2terms.begin(); i != e; ++i) {
                checkpoint();
                func_decl* const fd = i->m_key;
                app_set * const ts = i->get_value();
                const app_set::iterator r = ts->end();
                for (app_set::iterator j = ts->begin(); j != r; ++j) {
                    app_set::iterator k = j;
                    ++k;
                    for (;  k != r; ++k) {
                        app * const t1 = *j;
                        app * const t2 = *k;
                        SASSERT(t1->get_decl() == fd);
                        SASSERT(t2->get_decl() == fd);
                        if (t1 == t2) continue;
                        if (!ackr(t1,t2)) return false;
                    }
                }
            }
            return true;
        }

        bool abstract() {
            const fun2terms_map::iterator e = m_fun2terms.end();
            for (fun2terms_map::iterator i = m_fun2terms.begin(); i != e; ++i) {
                func_decl* const fd = i->m_key;
                app_set * const ts = i->get_value();
                sort* const s = fd->get_range();
                const app_set::iterator r = ts->end();
                for (app_set::iterator j = ts->begin(); j != r; ++j) {
                    app * const fc = m_m.mk_fresh_const(fd->get_name().str().c_str(), s);
                    app * const t = *j;
                    SASSERT(t->get_decl() == fd);
                    m_info->set_abstr(t, fc);
                    TRACE("lackr", tout << "abstr term "
                        << mk_ismt2_pp(t, m_m, 2)
                        << " -> "
                        << mk_ismt2_pp(fc, m_m, 2)
                        << "\n";);
                }
            }
            m_info->seal();
            m_info->abstract(m_fla.get(), m_abstr);
            TRACE("lackr", tout << "abs(\n" << mk_ismt2_pp(m_abstr.get(), m_m, 2) << ")\n";);
            return true;
        }

        void add_term(app* a) {
            //TRACE("lackr", tout << "inspecting term(\n" << mk_ismt2_pp(m_abstr, m_m, 2) << ")\n";);
            if (a->get_num_args() == 0) return;
            func_decl* const fd = a->get_decl();
            if (!is_uninterp(a)) return;
            SASSERT(m_bvutil.is_bv_sort(fd->get_range()) || m_m.is_bool(m_abstr));
            app_set* ts = 0;
            if (!m_fun2terms.find(fd, ts)) {
                ts = alloc(app_set);
                m_fun2terms.insert(fd, ts);
            }
            TRACE("lackr", tout << "term(" << mk_ismt2_pp(m_abstr, m_m, 2) << ")\n";);
            ts->insert(a);
        }

        bool collect_terms() {
            ptr_vector<expr> stack;
            expr *           curr;
            expr_mark        visited;
            stack.push_back(m_fla.get());
            while (!stack.empty()) {
                curr = stack.back();
                if (visited.is_marked(curr)) {
                    stack.pop_back();
                    continue;
                }

                switch (curr->get_kind()) {
                    case AST_VAR:
                        visited.mark(curr, true);
                        stack.pop_back();
                        break;

                    case AST_APP:
                        if (for_each_expr_args(stack, visited,
                                    to_app(curr)->get_num_args(), to_app(curr)->get_args())) {
                            visited.mark(curr, true);
                            stack.pop_back();
                            add_term(to_app(curr));
                        }
                        break;
                    case AST_QUANTIFIER:
                        if (visited.is_marked(to_quantifier(curr)->get_expr())) {
                            visited.mark(curr, true);
                            stack.pop_back();
                        }
                        else {
                            stack.push_back(to_quantifier(curr)->get_expr());
                        }
                        break;
                    default:
                        UNREACHABLE();
                        return false;
                }
            }
            visited.reset();
            return true;
        }
    };
private:
    ast_manager&                         m_m;
    params_ref                           m_p;
    scoped_ptr<imp>                      m_imp;
};

tactic * mk_lackr_tactic(ast_manager & m, params_ref const & p) {
    //return and_then(mk_nnf_tactic(m_m, m_p), alloc(lackr_tactic, m_m, m_p));
    //return alloc(lackr_tactic, m_m, m_p);
    //params_ref main_p;
    //main_p.set_bool("elim_and", true);
    //main_p.set_bool("sort_store", true);
    //main_p.set_bool("expand_select_store", true);
    //main_p.set_bool("expand_store_eq", true);

    params_ref simp2_p = p;
    simp2_p.set_bool("som", true);
    simp2_p.set_bool("pull_cheap_ite", true);
    simp2_p.set_bool("push_ite_bv", false);
    simp2_p.set_bool("local_ctx", true);
    simp2_p.set_uint("local_ctx_limit", 10000000);

    simp2_p.set_bool("ite_extra_rules", true);
    //simp2_p.set_bool("blast_eq_value", true);
    //simp2_p.set_bool("bv_sort_ac", true);

    params_ref ctx_simp_p;
    ctx_simp_p.set_uint("max_depth", 32);
    ctx_simp_p.set_uint("max_steps", 5000000);

    tactic * const preamble_t = and_then(
        mk_simplify_tactic(m),
        mk_propagate_values_tactic(m),
        //using_params(mk_ctx_simplify_tactic(m_m), ctx_simp_p),
        mk_solve_eqs_tactic(m),
        mk_elim_uncnstr_tactic(m),
        if_no_proofs(if_no_unsat_cores(mk_bv_size_reduction_tactic(m))),       
        mk_max_bv_sharing_tactic(m),
        mk_macro_finder_tactic(m, p),
        using_params(mk_simplify_tactic(m), simp2_p)
        //mk_nnf_tactic(m_m, m_p)
        );

    return and_then(
        preamble_t,
        alloc(lackr_tactic, m, p));
}
