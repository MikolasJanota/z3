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
    unsigned m_count_BV_NUM;
    unsigned m_count_BADD;
    unsigned m_count_BMUL;
    unsigned m_count_BSDIV;
    unsigned m_count_BUDIV;
    unsigned m_count_BSREM;
    unsigned m_count_BUREM;
    unsigned m_count_BSMOD;
    unsigned m_count_BSDIV0;
    unsigned m_count_BUDIV0;
    unsigned m_count_BSREM0;
    unsigned m_count_BUREM0;
    unsigned m_count_BSMOD0;
    unsigned m_count_BSDIV_I;
    unsigned m_count_BUDIV_I;
    unsigned m_count_BSREM_I;
    unsigned m_count_BUREM_I;
    unsigned m_count_BSMOD_I;
    unsigned m_count_ULEQ;
    unsigned m_count_SLEQ;
    unsigned m_count_BOR;
    unsigned m_count_BNOT;
    unsigned m_count_BXOR;
    unsigned m_count_CONCAT;
    unsigned m_count_SIGN_EXT;
    unsigned m_count_EXTRACT;
    unsigned m_count_BREDOR;
    unsigned m_count_BREDAND;
    unsigned m_count_BSHL;
    unsigned m_count_BLSHR;
    unsigned m_count_BASHR;
    unsigned m_count_EXT_ROTATE_LEFT;
    unsigned m_count_EXT_ROTATE_RIGHT;
    unsigned m_count_BUMUL_NO_OVFL;
    unsigned m_count_BSMUL_NO_OVFL;
    unsigned m_count_BSMUL_NO_UDFL;
    unsigned m_count_BIT2BOOL;
    unsigned m_count_MKBV;
    unsigned m_count_INT2BV;
    unsigned m_count_BV2INT;

    void reset_stats() {
        m_non_bin_bvmul = 0;
        m_rem_div_by_const = 0;
        m_count_BV_NUM = 0;
        m_count_BADD = 0;
        m_count_BMUL = 0;
        m_count_BSDIV = 0;
        m_count_BUDIV = 0;
        m_count_BSREM = 0;
        m_count_BUREM = 0;
        m_count_BSMOD = 0;
        m_count_BSDIV0 = 0;
        m_count_BUDIV0 = 0;
        m_count_BSREM0 = 0;
        m_count_BUREM0 = 0;
        m_count_BSMOD0 = 0;
        m_count_BSDIV_I = 0;
        m_count_BUDIV_I = 0;
        m_count_BSREM_I = 0;
        m_count_BUREM_I = 0;
        m_count_BSMOD_I = 0;
        m_count_ULEQ = 0;
        m_count_SLEQ = 0;
        m_count_BOR = 0;
        m_count_BNOT = 0;
        m_count_BXOR = 0;
        m_count_CONCAT = 0;
        m_count_SIGN_EXT = 0;
        m_count_EXTRACT = 0;
        m_count_BREDOR = 0;
        m_count_BREDAND = 0;
        m_count_BSHL = 0;
        m_count_BLSHR = 0;
        m_count_BASHR = 0;
        m_count_EXT_ROTATE_LEFT = 0;
        m_count_EXT_ROTATE_RIGHT = 0;
        m_count_BUMUL_NO_OVFL = 0;
        m_count_BSMUL_NO_OVFL = 0;
        m_count_BSMUL_NO_UDFL = 0;
        m_count_BIT2BOOL = 0;
        m_count_MKBV = 0;
        m_count_INT2BV = 0;
        m_count_BV2INT = 0;
    }

    void collect_stats(statistics & st) const {
        st.update("non_bin_bvmul", m_non_bin_bvmul);
        st.update("rem_div_by_const", m_rem_div_by_const);

        st.update("BV_NUM", m_count_BV_NUM);
        st.update("BADD", m_count_BADD);
        st.update("BMUL", m_count_BMUL);
        st.update("BSDIV", m_count_BSDIV);
        st.update("BUDIV", m_count_BUDIV);
        st.update("BSREM", m_count_BSREM);
        st.update("BUREM", m_count_BUREM);
        st.update("BSMOD", m_count_BSMOD);
        st.update("BSDIV0", m_count_BSDIV0);
        st.update("BUDIV0", m_count_BUDIV0);
        st.update("BSREM0", m_count_BSREM0);
        st.update("BUREM0", m_count_BUREM0);
        st.update("BSMOD0", m_count_BSMOD0);
        st.update("BSDIV_I", m_count_BSDIV_I);
        st.update("BUDIV_I", m_count_BUDIV_I);
        st.update("BSREM_I", m_count_BSREM_I);
        st.update("BUREM_I", m_count_BUREM_I);
        st.update("BSMOD_I", m_count_BSMOD_I);
        st.update("ULEQ", m_count_ULEQ);
        st.update("SLEQ", m_count_SLEQ);
        st.update("BOR", m_count_BOR);
        st.update("BNOT", m_count_BNOT);
        st.update("BXOR", m_count_BXOR);
        st.update("CONCAT", m_count_CONCAT);
        st.update("SIGN_EXT", m_count_SIGN_EXT);
        st.update("EXTRACT", m_count_EXTRACT);
        st.update("BREDOR", m_count_BREDOR);
        st.update("BREDAND", m_count_BREDAND);
        st.update("BSHL", m_count_BSHL);
        st.update("BLSHR", m_count_BLSHR);
        st.update("BASHR", m_count_BASHR);
        st.update("EXT_ROTATE_LEFT", m_count_EXT_ROTATE_LEFT);
        st.update("EXT_ROTATE_RIGHT", m_count_EXT_ROTATE_RIGHT);
        st.update("BUMUL_NO_OVFL", m_count_BUMUL_NO_OVFL);
        st.update("BSMUL_NO_OVFL", m_count_BSMUL_NO_OVFL);
        st.update("BSMUL_NO_UDFL", m_count_BSMUL_NO_UDFL);
        st.update("BIT2BOOL", m_count_BIT2BOOL);
        st.update("MKBV", m_count_MKBV);
        st.update("INT2BV", m_count_INT2BV);
        st.update("BV2INT", m_count_BV2INT);
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

    void count(app * a) {
        if (a->get_family_id() != m_bv_util.get_fid()) return;
        switch (a->get_decl_kind())
        {
            case OP_BV_NUM: ++m_count_BV_NUM; break;
            case OP_BADD: ++m_count_BADD; break;
            case OP_BMUL: ++m_count_BMUL; break;
            case OP_BSDIV: ++m_count_BSDIV; break;
            case OP_BUDIV: ++m_count_BUDIV; break;
            case OP_BSREM: ++m_count_BSREM; break;
            case OP_BUREM: ++m_count_BUREM; break;
            case OP_BSMOD: ++m_count_BSMOD; break;
            case OP_BSDIV0: ++m_count_BSDIV0; break;
            case OP_BUDIV0: ++m_count_BUDIV0; break;
            case OP_BSREM0: ++m_count_BSREM0; break;
            case OP_BUREM0: ++m_count_BUREM0; break;
            case OP_BSMOD0: ++m_count_BSMOD0; break;
            case OP_BSDIV_I: ++m_count_BSDIV_I; break;
            case OP_BUDIV_I: ++m_count_BUDIV_I; break;
            case OP_BSREM_I: ++m_count_BSREM_I; break;
            case OP_BUREM_I: ++m_count_BUREM_I; break;
            case OP_BSMOD_I: ++m_count_BSMOD_I; break;
            case OP_ULEQ: ++m_count_ULEQ; break;
            case OP_SLEQ: ++m_count_SLEQ; break;
            case OP_BOR: ++m_count_BOR; break;
            case OP_BNOT: ++m_count_BNOT; break;
            case OP_BXOR: ++m_count_BXOR; break;
            case OP_CONCAT: ++m_count_CONCAT; break;
            case OP_SIGN_EXT: ++m_count_SIGN_EXT; break;
            case OP_EXTRACT: ++m_count_EXTRACT; break;
            case OP_BREDOR: ++m_count_BREDOR; break;
            case OP_BREDAND: ++m_count_BREDAND; break;
            case OP_BSHL: ++m_count_BSHL; break;
            case OP_BLSHR: ++m_count_BLSHR; break;
            case OP_BASHR: ++m_count_BASHR; break;
            case OP_EXT_ROTATE_LEFT: ++m_count_EXT_ROTATE_LEFT; break;
            case OP_EXT_ROTATE_RIGHT: ++m_count_EXT_ROTATE_RIGHT; break;
            case OP_BUMUL_NO_OVFL: ++m_count_BUMUL_NO_OVFL; break;
            case OP_BSMUL_NO_OVFL: ++m_count_BSMUL_NO_OVFL; break;
            case OP_BSMUL_NO_UDFL: ++m_count_BSMUL_NO_UDFL; break;
            case OP_BIT2BOOL: ++m_count_BIT2BOOL; break;
            case OP_MKBV: ++m_count_MKBV; break;
            case OP_INT2BV: ++m_count_INT2BV; break;
            case OP_BV2INT: ++m_count_BV2INT; break;
            default: std::cerr<<"Warning unsupported op." <<std::endl;
        }
    }

    void visit_app(app * a) {
        if (m_bv_util.is_bv_mul(a) && a->get_num_args() > 2) ++m_non_bin_bvmul;
        if (a->get_num_args() == 2 && is_rem_div(a) && m_bv_util.is_numeral(a->get_arg(1))) m_rem_div_by_const++;
        count(a);
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
