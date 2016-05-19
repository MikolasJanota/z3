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
    unsigned m_non_bin_bvmul;
    void reset_stats() {
        m_non_bin_bvmul = 0;
    }

    void collect_stats(statistics & st) const {
        st.update("non_bin_bvmul", m_non_bin_bvmul);
    }

    void visit_var(var * v) { }

    void visit_app(app * a) {
        if (m_bv_util.is_bv_mul(a) && a->get_num_args() > 2) ++m_non_bin_bvmul;
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


tactic * mk_stats_tactic(ast_manager & m, params_ref const & p) {
    return alloc(stats_tactic, m, p);
}
