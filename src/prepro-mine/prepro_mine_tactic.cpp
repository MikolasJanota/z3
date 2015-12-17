/*++
 Copyright (c) 2015 Microsoft Corporation

 Module Name:

  prepro_mine_tactic.cpp

 Abstract:


 Author:

 Mikolas Janota

 Revision History:
--*/
#include"prepro_mine_tactic.h"
#include"miner.h"
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
class prepro_mine_tactic : public tactic {
    ast_manager&    m_m;
    params_ref      m_params;
public:
    prepro_mine_tactic(ast_manager& m, params_ref const& p)
        : m_m(m)
        , m_params(p)
     {}

    virtual void operator()(/* in */  goal_ref const & g,
                            /* out */ goal_ref_buffer & result,
                            /* out */ model_converter_ref & mc,
                            /* out */ proof_converter_ref & pc,
                            /* out */ expr_dependency_ref & core) {
        mc = 0;
        ast_manager& m(g->m());
        TRACE("miner", g->display(tout << "Goal:\n"););
        // conflate all assertions into one conjunction
        ptr_vector<expr> flas;
        g->get_formulas(flas);
        expr_ref f(m);
        f = m.mk_and(flas.size(), flas.c_ptr());
        // running implementation
        miner imp(m);
        imp(f);
        flas.reset();
    }

    virtual tactic* translate(ast_manager& m) {
        return alloc(prepro_mine_tactic, m, m_params);
    }

    virtual void cleanup() { }

    inline void checkpoint() {
        //if (m_m.cancel()) throw tactic_exception(TACTIC_CANCELED_MSG);
    }
};

tactic * mk_prepro_mine_tactic(ast_manager& m, params_ref const & p) {
    params_ref simp2_p = p;
    simp2_p.set_bool("som", true);
    simp2_p.set_bool("pull_cheap_ite", true);
    simp2_p.set_bool("push_ite_bv", false);
    simp2_p.set_bool("local_ctx", true);
    simp2_p.set_uint("local_ctx_limit", 10000000);

    simp2_p.set_bool("ite_extra_rules", true);
    params_ref ctx_simp_p;
    ctx_simp_p.set_uint("max_depth", 32);
    ctx_simp_p.set_uint("max_steps", 5000000);

    tactic * const preamble_t = and_then(
            mk_simplify_tactic(m),
            mk_propagate_values_tactic(m),
//            using_params(mk_ctx_simplify_tactic(m), ctx_simp_p),
            mk_solve_eqs_tactic(m),
            mk_elim_uncnstr_tactic(m),
            if_no_proofs(if_no_unsat_cores(mk_bv_size_reduction_tactic(m))),
            mk_max_bv_sharing_tactic(m),
            mk_macro_finder_tactic(m, p),
            using_params(mk_simplify_tactic(m), simp2_p)
            );

    return and_then(
            preamble_t,
            alloc(prepro_mine_tactic, m, p));
}
