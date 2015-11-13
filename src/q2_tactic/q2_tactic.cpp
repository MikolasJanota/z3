/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

q2_tactic.cpp

Abstract:

Tactic for 2 level quantification a la AReQS.

Author:

Mikolas Janota

Revision History:
--*/
#include"q2_tactic.h"
#include"q2.h"
#include"qfbv_tactic.h"
#include"expr_substitution.h"
#include"expr_replacer.h"
#include"extension_model_converter.h"
#include"solver.h"
#include"array.h"
#include"tactic2solver.h"
#include"decl_collector.h"
#include"ast_util.h"
#include"inc_sat_solver.h"
#include"simplifier.h"
#include"bv_simplifier_plugin.h"
#include"nnf_tactic.h"
#include"macro_finder_tactic.h"
#include"qfaufbv_tactic.h"
#include"model_smt2_pp.h"
#include"model_evaluator.h"
#include"smt_tactic.h"
#include"smt_solver.h"
#include"array_decl_plugin.h"
#include"simplifier_plugin.h"
#include"basic_simplifier_plugin.h"
#include"array_simplifier_params.h"
#include"array_simplifier_plugin.h"
#include"solve_eqs_tactic.h"
#include"simplify_tactic.h"
#include"propagate_values_tactic.h"
#include"bit_blaster_tactic.h"
#include"elim_uncnstr_tactic.h"
#include"max_bv_sharing_tactic.h"
#include"bv_size_reduction_tactic.h"
#include"ctx_simplify_tactic.h"
#include"th_rewriter.h"
#include"smt2parser.h"
#include <strstream>


#define RUN_EXT 0

class label_removal {
public:
    label_removal(ast_manager& m)
        : m(m) {}

    void operator () (expr * in, expr_ref& out) {
        ptr_vector<expr> stack;
        expr *           curr;
        expr_mark        visited;
        obj_map<expr, expr*> e2e;
        stack.push_back(in);
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
                e2e.insert(curr, curr);
                break;

            case AST_APP: {
                app *  a = to_app(curr);
                if (for_each_expr_args(stack, visited, a->get_num_args(), a->get_args())) {
                    visited.mark(curr, true);
                    stack.pop_back();
                    buffer<symbol>  names;
                    if (m.is_label_lit(a,names)) {
                        SASSERT(names.size()==1);
                        e2e.insert(curr, m.mk_true());
                    }
                    else if (m.is_label(a)) {
                        e2e.insert(a, e2e[a->get_arg(0)]);
                    }
                    else {
                        ptr_vector<expr> ags;
                        bool c = false;
                        for (unsigned i = 0; i < a->get_num_args(); ++i) {
                            const expr *  const old = a->get_arg(i);
                            expr *  const n = e2e[a->get_arg(i)];
                            if (old != n) c = true;
                            if (n) ags.push_back(n);
                        }
                        if (c) e2e.insert(curr, m.mk_app(a->get_decl(), ags.size(), ags.c_ptr()));
                        else e2e.insert(curr, curr);
                    }
                }
            }
                break;
            case AST_QUANTIFIER: {
                quantifier * const q = to_quantifier(curr);
                if (visited.is_marked(q->get_expr())) {
                    e2e.insert(q, m.update_quantifier(q, e2e[q->get_expr()]));
                    visited.mark(curr, true);
                    stack.pop_back();
                }
                else {
                    stack.push_back(q->get_expr());
                }
            }
                break;
            default:
                UNREACHABLE();
            }
        }
        out = e2e[in];
        e2e.reset();
        visited.reset();
    }
protected:
    ast_manager& m;
};

/* CEGAR-Based approach to two level quantification problems a la AReQS. */
class q2_tactic : public tactic {
public:
    enum Mode { BV, UFBV }; // pure a bit-vectors or also uninterpreted functions in the matrix. 
                                //TODO set by params

    q2_tactic(ast_manager& m, params_ref const& p)
        : m_m(m)
        , m_p(p) {}

    virtual void operator()(goal_ref const & g,
        goal_ref_buffer & result,
        model_converter_ref & mc,
        proof_converter_ref & pc,
        expr_dependency_ref & core) {
        ast_manager& m(g->m());
        ptr_vector<expr> flas;
        TRACE("q2", g->display(tout << "Goal:\n"););
        expr_ref_vector flas_refs(m);
        if (!(RUN_EXT)) {
            g->get_formulas(flas);
        }
        else {
            for (unsigned i = 0; i < g->size(); i++) {
                expr_ref sc(m);
                expr_ref tmp(m);
                label_removal lr(m);
                sc=g->form(i);
                lr(sc, tmp);
                sc=tmp;
                flas_refs.push_back(sc);
                flas.push_back(sc.get());
                if (sc.get() != g->form(i)) {
                    TRACE("q2",
                        tout << "orig:(\n" << mk_ismt2_pp(g->form(i), m, 2) << ")\n";
                    tout << "no lb:(\n" << mk_ismt2_pp(sc.get(), m, 2) << ")\n";
                    );
                }
            }
        }
        // Running implementation
        scoped_ptr<q2_solver> i = mk_q2_solver(m, m_p, flas);
        const lbool o = (*i)();
        flas.reset();
        flas_refs.reset();
        // Report result
        goal_ref resg(alloc(goal, *g, true));
        if (o == l_false) resg->assert_expr(m.mk_false());
        if (o != l_undef) result.push_back(resg.get());
        // TODO Report model
    }

    virtual void cleanup() { }

    virtual tactic* translate(ast_manager& m) {
        return alloc(q2_tactic, m, m_p);
    }
private:
    ast_manager& m_m;
    params_ref m_p;
};

tactic * mk_q2_tactic(ast_manager & m, params_ref const & p) {
    //return and_then(mk_nnf_tactic(m, p), alloc(q2_tactic, m, p));
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

    //simp2_p.set_bool("expand_select_store", true);
    //simp2_p.set_bool("sort_store", true);



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
        alloc(q2_tactic, m, p));
}
