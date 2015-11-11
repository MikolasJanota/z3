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
#include"expr_replacer.h"
#include"array_decl_plugin.h"

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
        ast_manager& m(g->m());
        TRACE("lackr", g->display(tout << "Goal:\n"););
        ptr_vector<expr> flas;
        g->get_formulas(flas);
        expr_ref f(m);
        f=m.mk_and(flas.size(), flas.c_ptr());
        // Running implementation
        imp i(m, m_p, f);
        const lbool o = i();
        flas.reset();
        // Report result
        goal_ref resg(alloc(goal, *g, true));
        if (o == l_false) resg->assert_expr(m.mk_false());
        if (o != l_undef) result.push_back(resg.get());
        // TODO Report model
    }
    virtual void cleanup() { }

    virtual tactic* translate(ast_manager& m) {
        return alloc(lackr_tactic, m, m_p);
    }
private:
    struct imp {
      public:
        imp(ast_manager& m, params_ref p, expr_ref f)
          : m(m)
          , p(p)
          , f(f)
          , a(m)
          , sat(0)
          , bu(m)
          , au(m)
        {}

        lbool operator() () {
            sat = mk_inc_sat_solver(m, p);
            //tactic_ref t = mk_qfaufbv_tactic(m, p);
            //sat = mk_tactic2solver(m, t.get(), p);
            sat->set_produce_models(true);
            SASSERT(sat);
            const bool ok = init();
            if (!ok) return l_undef;
            //sat->display(std::cout);
            TRACE("lackr", tout << "run sat\n"; );
            const lbool rv = sat->check_sat(0, 0);
            TRACE("lackr", tout << "sat:" << rv << '\n'; );
            return rv;
          }

        ~imp() {
            const f2tt::iterator e = f2t.end();
            for (f2tt::iterator i = f2t.begin(); i != e; ++i) {
                dealloc(i->get_value());
            }
        }
      private:
        typedef obj_hashtable<app> app_set;
        typedef obj_map<func_decl, app_set*> f2tt;
        typedef obj_map<expr, app*> t2ct;
        ast_manager& m;
        params_ref p;
        expr_ref f;
        expr_ref a;
        f2tt f2t;
        t2ct t2c;
        scoped_ptr<solver> sat;
        bv_util bu;
        array_util au;

        bool init() {
          return get_terms() && abstract() && ackr();
        }

        bool ackr(app * const t1, app * const t2) {
            TRACE("lackr", tout << "ackr"
                << mk_ismt2_pp(t1, m, 2)
                << " , "
                << mk_ismt2_pp(t2, m, 2) << "\n";);
            app * const a1 = t2c[t1];
            app * const a2 = t2c[t2];
            const unsigned sz = t1->get_num_args();
            expr_ref cg(m.mk_true(), m);
            expr_ref_vector eqs(m);
            const unsigned six = au.is_select(t1) ? 1 : 0;
            for (unsigned gi = six; gi < sz; ++gi) {
                //cg = m.mk_and(m.mk_eq(t1->get_arg(gi), t2->get_arg(gi)), cg);
                expr * const arg1 = t1->get_arg(gi);
                expr * const arg2 = t2->get_arg(gi);
                if (arg1 == arg2) continue;
                if (bu.is_numeral(arg1) && bu.is_numeral(arg2)) {
                    SASSERT(arg1 != arg2);
                    TRACE("lackr", tout << "never eq\n";);
                    return true;
                }
                eqs.push_back(m.mk_eq(arg1, arg2));
            }
            cg = m.mk_and(eqs.size(), eqs.c_ptr());
            cg = m.mk_implies(cg, m.mk_eq(a1, a2));
            TRACE("lackr", tout << "ackr constr" << mk_ismt2_pp(cg, m, 2) << "\n";);
            sat->assert_expr(cg.get());
            return true;
        }

        bool ackr() {
            const f2tt::iterator e = f2t.end();
            for (f2tt::iterator i = f2t.begin(); i != e; ++i) {
                func_decl* const fd = i->m_key;
                app_set * const ts = i->get_value();
                sort* const s = fd->get_range();
                const app_set::iterator r = ts->end();
                for (app_set::iterator j = ts->begin(); j != r; ++j) {
                    for (app_set::iterator k = j; k != r; ++k) {
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
            const f2tt::iterator e = f2t.end();
            expr_substitution subst(m);
            for (f2tt::iterator i = f2t.begin(); i != e; ++i) {
                func_decl* const fd = i->m_key;
                app_set * const ts = i->get_value();
                sort* const s = fd->get_range();
                const app_set::iterator r = ts->end();
                for (app_set::iterator j = ts->begin(); j != r; ++j) {
                    app * const fc = m.mk_fresh_const(fd->get_name().str().c_str(), s);
                    app * const t = *j;
                    SASSERT(t->get_decl() == fd);
                    t2c.insert(t, fc);
                    subst.insert(t, fc);
                    TRACE("lackr", tout << "abstr term "
                        << mk_ismt2_pp(t, m, 2)
                        << " -> "
                        << mk_ismt2_pp(fc, m, 2)
                        << "\n";);
                }
            }
            scoped_ptr<expr_replacer> er = mk_default_expr_replacer(m);
            er->set_substitution(&subst);
            (*er)(f.get(), a);
            sat->assert_expr(a);
            TRACE("lackr", tout << "abs(\n" << mk_ismt2_pp(a.get(), m, 2) << ")\n";);
            return true;
        }


        void add_term(app* a) {
            //TRACE("lackr", tout << "inspecting term(\n" << mk_ismt2_pp(a, m, 2) << ")\n";);
            if (a->get_num_args() == 0) return;
            func_decl* const fd = a->get_decl();
            if (!is_uninterp(a) && !au.is_select(a)) return;
            SASSERT(bu.is_bv_sort(fd->get_range()) || m.is_bool(a));
            app_set* ts = 0;
            if (!f2t.find(fd, ts)) {
                ts = alloc(app_set);
                f2t.insert(fd, ts);
            }
            TRACE("lackr", tout << "term(" << mk_ismt2_pp(a, m, 2) << ")\n";);
            ts->insert(a);
        }

        bool get_terms() {
          ptr_vector<expr> stack;
          expr *           curr;
          expr_mark        visited;
          stack.push_back(f.get());
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
    ast_manager& m_m;
    params_ref m_p;
};

tactic * mk_lackr_tactic(ast_manager & m, params_ref const & p) {
    //return alloc(lackr_tactic, m, p);
    params_ref main_p;
    main_p.set_bool("elim_and", true);
    main_p.set_bool("sort_store", true);
    //main_p.set_bool("expand_select_store", true);
    //main_p.set_bool("expand_store_eq", true);

    params_ref simp2_p = p;
    simp2_p.set_bool("som", true);
    simp2_p.set_bool("pull_cheap_ite", true);
    simp2_p.set_bool("push_ite_bv", false);
    simp2_p.set_bool("local_ctx", true);
    simp2_p.set_uint("local_ctx_limit", 10000000);

    params_ref ctx_simp_p;
    ctx_simp_p.set_uint("max_depth", 32);
    ctx_simp_p.set_uint("max_steps", 5000000);

    tactic * const preamble_t = and_then(
        mk_simplify_tactic(m),
        mk_propagate_values_tactic(m),
        //using_params(mk_ctx_simplify_tactic(m), ctx_simp_p),
        mk_solve_eqs_tactic(m),
        mk_elim_uncnstr_tactic(m),
        if_no_proofs(if_no_unsat_cores(mk_bv_size_reduction_tactic(m))),
        using_params(mk_simplify_tactic(m), simp2_p),
        mk_max_bv_sharing_tactic(m),
        mk_macro_finder_tactic(m, p),
        mk_nnf_tactic(m, p)
        );

    return and_then(
        preamble_t,
        alloc(lackr_tactic, m, p));
}
