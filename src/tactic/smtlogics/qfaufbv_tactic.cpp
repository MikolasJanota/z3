/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    qfaufbv_tactic.cpp

Abstract:

    Tactic for QF_AUFBV benchmarks.

Author:

    Leonardo (leonardo) 2012-02-23

Notes:

--*/
#include"solve_eqs_tactic.h"
#include"simplify_tactic.h"
#include"propagate_values_tactic.h"
#include"bit_blaster_tactic.h"
#include"elim_uncnstr_tactic.h"
#include"max_bv_sharing_tactic.h"
#include"bv_size_reduction_tactic.h"
#include"ctx_simplify_tactic.h"
#include"sat_tactic.h"
#include"smt_tactic.h"
///////////////
#include"model_smt2_pp.h"
#include"cooperate.h"
#include"lackr_arrays.h"
#include"ackermannization_params.hpp"
#include"qfufbv_ackr_model_converter.h"
///////////////
#include"inc_sat_solver.h"
#include"qfaufbv_tactic.h"
#include"qfbv_tactic.h"
#include"tactic2solver.h"
///////////////
#include"qfufbv_tactic_params.hpp" // TODO

class qfaufbv_ackr_tactic : public tactic {
public:
    qfaufbv_ackr_tactic(ast_manager& m, params_ref const& p)
        : m_m(m)
        , m_p(p)
        , m_use_sat(false)
        , m_inc_use_sat(false)
    {}

    virtual ~qfaufbv_ackr_tactic() { }

    virtual void operator()(goal_ref const & g,
        goal_ref_buffer & result,
        model_converter_ref & mc,
        proof_converter_ref & pc,
        expr_dependency_ref & core) {
        mc = 0;
        ast_manager& m(g->m());
        tactic_report report("qfaufbv_ackr", *g);
        fail_if_unsat_core_generation("qfaufbv_ackr", g);
        fail_if_proof_generation("qfaufbv_ackr", g);

        TRACE("qfaufbv_ackr_tactic", g->display(tout << "goal:\n"););
        // running implementation
        expr_ref_vector flas(m);
        const unsigned sz = g->size();
        for (unsigned i = 0; i < sz; i++) flas.push_back(g->form(i));
        scoped_ptr<solver> uffree_solver = setup_sat();
        scoped_ptr<lackr_arrays> imp = alloc(lackr_arrays, m, m_p, m_st, flas, uffree_solver.get());
        const lbool o = imp->operator()();
        flas.reset();
        // report result
        goal_ref resg(alloc(goal, *g, true));
        if (o == l_false) resg->assert_expr(m.mk_false());
        if (o != l_undef) result.push_back(resg.get());
        // report model
        if (g->models_enabled() && (o == l_true)) {
            model_ref abstr_model = imp->get_model();
            mc = mk_qfufbv_ackr_model_converter(m, imp->get_info(), abstr_model);
        }
    }

    void updt_params(params_ref const & _p) {
        qfufbv_tactic_params p(_p);
        m_use_sat = p.sat_backend();
        m_inc_use_sat = p.inc_sat_backend();
    }

    virtual void collect_statistics(statistics & st) const {
        ackermannization_params p(m_p);
        if (!p.eager()) st.update("lackr-its", m_st.m_it);
        st.update("ackr-constraints", m_st.m_ackrs_sz);
    }

    virtual void reset_statistics() { m_st.reset(); }

    virtual void cleanup() { }

    virtual tactic* translate(ast_manager& m) {
        return alloc(qfaufbv_ackr_tactic, m, m_p);
    }
private:
    ast_manager&                         m_m;
    params_ref                           m_p;
    lackr_stats                          m_st;
    bool                                 m_use_sat;
    bool                                 m_inc_use_sat;

    solver* setup_sat() {
        solver * sat(NULL);
        if (m_use_sat) {
            if (m_inc_use_sat) {
                sat = mk_inc_sat_solver(m_m, m_p);
            }
            else {
                tactic_ref t = mk_qfbv_tactic(m_m, m_p);
                sat = mk_tactic2solver(m_m, t.get(), m_p);
            }
        }
        else {
            tactic_ref t = mk_qfaufbv_tactic(m_m, m_p);
            sat = mk_tactic2solver(m_m, t.get(), m_p);
        }
        SASSERT(sat != NULL);
        sat->set_produce_models(true);
        return sat;
    }


};

tactic * mk_qfaufbv_ackr_tactic(ast_manager & m, params_ref const & p) {
    params_ref main_p;
    main_p.set_bool("elim_and", true);
    main_p.set_bool("sort_store", true);

    params_ref simp2_p = p;
    simp2_p.set_bool("som", true);
    simp2_p.set_bool("pull_cheap_ite", true);
    simp2_p.set_bool("push_ite_bv", false);
    simp2_p.set_bool("local_ctx", true);
    simp2_p.set_uint("local_ctx_limit", 10000000);

    params_ref ctx_simp_p;
    ctx_simp_p.set_uint("max_depth", 32);
    ctx_simp_p.set_uint("max_steps", 5000000);

    params_ref solver_p;
    solver_p.set_bool("array.simplify", false); // disable array simplifications at old_simplify module

    tactic * preamble_st = and_then(mk_simplify_tactic(m),
        mk_propagate_values_tactic(m),
        // using_params(mk_ctx_simplify_tactic(m), ctx_simp_p),
        mk_solve_eqs_tactic(m),
        mk_elim_uncnstr_tactic(m),
        if_no_proofs(if_no_unsat_cores(mk_bv_size_reduction_tactic(m))),
        using_params(mk_simplify_tactic(m), simp2_p),
        mk_max_bv_sharing_tactic(m)
    );

    tactic * st = using_params(and_then(
        preamble_st,
        alloc(qfaufbv_ackr_tactic, m, solver_p)),
        main_p);

    st->updt_params(p);
    return st;
}



tactic * mk_qfaufbv_tactic(ast_manager & m, params_ref const & p) {
    params_ref main_p;
    main_p.set_bool("elim_and", true);
    main_p.set_bool("sort_store", true);

    params_ref simp2_p = p;
    simp2_p.set_bool("som", true);
    simp2_p.set_bool("pull_cheap_ite", true);
    simp2_p.set_bool("push_ite_bv", false);
    simp2_p.set_bool("local_ctx", true);
    simp2_p.set_uint("local_ctx_limit", 10000000);

    params_ref ctx_simp_p;
    ctx_simp_p.set_uint("max_depth", 32);
    ctx_simp_p.set_uint("max_steps", 5000000);

    params_ref solver_p;
    solver_p.set_bool("array.simplify", false); // disable array simplifications at old_simplify module

    tactic * preamble_st = and_then(mk_simplify_tactic(m),
                                    mk_propagate_values_tactic(m),
                                    // using_params(mk_ctx_simplify_tactic(m), ctx_simp_p),
                                    mk_solve_eqs_tactic(m),
                                    mk_elim_uncnstr_tactic(m),
                                    if_no_proofs(if_no_unsat_cores(mk_bv_size_reduction_tactic(m))),
                                    using_params(mk_simplify_tactic(m), simp2_p),
                                    mk_max_bv_sharing_tactic(m)
                                    );

    tactic * st = using_params(and_then(preamble_st,
                                        using_params(mk_smt_tactic(), solver_p)),
                               main_p);
    
    st->updt_params(p);
    return st;
}
