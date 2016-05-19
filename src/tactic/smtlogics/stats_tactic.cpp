/*++
 Copyright (c) 2016 Microsoft Corporation

 Module Name:

  stats_tactic.cpp

 Abstract:


 Author:

 Mikolas Janota

 Revision History:
--*/
#include"tactical.h"
#include"stats_tactic.h"
#include"propagate_values_tactic.h"
#include"solve_eqs_tactic.h"
#include"elim_uncnstr_tactic.h"
#include"smt_tactic.h"
#include"max_bv_sharing_tactic.h"
#include"bv_size_reduction_tactic.h"
#include"reduce_args_tactic.h"
#include"simplify_tactic.h"


class stats_tactic : public tactic {
public:
    stats_tactic(ast_manager& m, params_ref const& p)
        : m_m(m)
        , m_p(p)
        , m_bv_util(m)
    {
        reset_stats();
    }

    virtual ~stats_tactic() { }

    virtual void operator()(goal_ref const & g,
        goal_ref_buffer & result,
        model_converter_ref & mc,
        proof_converter_ref & pc,
        expr_dependency_ref & core) {
        mc = 0;
        ast_manager& m(g->m());
        tactic_report report("stats", *g);
        fail_if_unsat_core_generation("stats", g);
        fail_if_proof_generation("stats", g);

        TRACE("stats_tactic", g->display(tout << "goal:\n"););
        const unsigned sz = g->size();
        for (unsigned i = 0; i < sz; i++) visit(g->form(i));
    }

    void updt_params(params_ref const & _p) { }

    virtual void collect_statistics(statistics & st) const { collect_stats(st); }

    virtual void reset_statistics() { reset_stats(); }

    virtual void cleanup() { }

    virtual tactic* translate(ast_manager& m) { return alloc(stats_tactic, m, m_p); }
protected:
    ast_manager&                         m_m;
    params_ref                           m_p;
    bv_util                              m_bv_util;
    unsigned                             m_non_bin_bvmul;
    unsigned                             m_rem_div_by_const;
    void reset_stats() {
        m_non_bin_bvmul = 0;
        m_rem_div_by_const = 0;
    }

    void collect_stats(statistics & st) const {
        st.update("non_bin_bvmul", m_non_bin_bvmul);
        st.update("rem_div_by_const", m_rem_div_by_const);
    }

    bool is_rem_div(const app * a) const {
        if (a->get_family_id() != m_bv_util.get_fid()) return false;
        switch (a->get_decl_kind())
        {
        case OP_BSDIV:
        case OP_BUDIV:
        case OP_BUREM:
        case OP_BSREM:
        case OP_BSDIV_I:
        case OP_BUDIV_I:
        case OP_BUREM_I:
        case OP_BSREM_I:
            return true;
        default:
            return false;
        }
    }

    void visit_var(var * v) { }

    void visit_app(app * a) {
        if (m_bv_util.is_bv_mul(a) && a->get_num_args() > 2) ++m_non_bin_bvmul;
        if (a->get_num_args() == 2 && is_rem_div(a) && m_bv_util.is_numeral(a->get_arg(1))) m_rem_div_by_const++;
    }

    void visit(expr * e) {
        ptr_vector<expr> stack;
        expr *           curr;
        expr_mark        visited;

        stack.push_back(e);

        while (!stack.empty()) {
            curr = stack.back();
            if (visited.is_marked(curr)) {
                stack.pop_back();
                continue;
            }

            switch (curr->get_kind()) {
                case AST_VAR:
                    visit_var(to_var(curr));
                    visited.mark(curr, true);
                    stack.pop_back();
                    break;
                case AST_APP:
                    {
                        app * const a = to_app(curr);
                        if (for_each_expr_args(stack, visited, a->get_num_args(), a->get_args())) {
                            visited.mark(curr, true);
                            stack.pop_back();
                            visit_app(a);
                        }
                    }
                    break;
                case AST_QUANTIFIER:
                    stack.push_back(to_quantifier(curr)->get_expr());
                default:
                    UNREACHABLE();
                    return;
            }
        }
    }
};


static tactic * mk_preamble(ast_manager & m, params_ref const & p) {
    params_ref simp2_p = p;
    simp2_p.set_bool("pull_cheap_ite", true);
    simp2_p.set_bool("push_ite_bv", false);
    simp2_p.set_bool("local_ctx", true);
    simp2_p.set_uint("local_ctx_limit", 10000000);

    simp2_p.set_bool("ite_extra_rules", true);
    simp2_p.set_bool("mul2concat", true);

    params_ref ctx_simp_p;
    ctx_simp_p.set_uint("max_depth", 32);
    ctx_simp_p.set_uint("max_steps", 5000000);

    return and_then(
        mk_simplify_tactic(m),
        mk_propagate_values_tactic(m),
        //using_params(mk_ctx_simplify_tactic(m_m), ctx_simp_p),
        mk_solve_eqs_tactic(m),
        mk_elim_uncnstr_tactic(m),
        if_no_proofs(if_no_unsat_cores(mk_bv_size_reduction_tactic(m))),
        mk_max_bv_sharing_tactic(m),
        using_params(mk_simplify_tactic(m), simp2_p)
    );
}

tactic * mk_stats_tactic(ast_manager & m, params_ref const & p) {
    return and_then(mk_preamble(m, p), alloc(stats_tactic, m, p));
}
