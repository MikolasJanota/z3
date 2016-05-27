/*++
 Copyright (c) 2016 Microsoft Corporation

 Module Name:

  lackr_arrays.cpp

 Abstract:


 Author:

 Mikolas Janota (MikolasJanota)

 Revision History:
--*/
#include"lackr_arrays.h"
#include"lackr_arrays_model_constructor.h"

lackr_arrays::lackr_arrays(ast_manager& m, params_ref p, lackr_stats& st,
            expr_ref_vector& formulas, solver * uffree_solver)
: lackr(m, p, st, formulas, uffree_solver)
, m_ar_util(m)
, m_mc(NULL)
{
    updt_params(p);
}

void lackr_arrays::updt_params(params_ref const & _p) {
    lackr::updt_params(_p);
    m_eager = false;
}

lbool lackr_arrays::operator() () {
    return lackr::operator() ();
}

bool lackr_arrays::add_term(app* a) {
    if (lackr::add_term(a)) return true;
    if (m_ar_util.is_select(a)) {
        m_selects.insert(a);
        return true;
    }
    if (m_ar_util.is_store(a)) {
        m_stores.insert(a);
        return true;
    }
    expr* lhs;
    expr* rhs;
    if (m_m.is_eq(a, lhs, rhs) && m_ar_util.is_array(lhs)) {
        SASSERT(m_ar_util.is_array(rhs));
        m_eqs.insert(a);
        return true;
    }
    return false;
}

void lackr_arrays::build_abstraction_map() {
    for (app_set::iterator i = m_selects.begin(); i != m_selects.end(); ++i) {
        app * const a = *i;
        SASSERT(m_ar_util.is_select(a));
        sort* const s = a->get_decl()->get_range();
        app * const fc = m_m.mk_fresh_const("select", s);
        m_info->set_abstr(a, fc);
        TRACE("lackr", tout << "abstr term "
            << mk_ismt2_pp(a, m_m, 2) << " -> " << mk_ismt2_pp(fc, m_m, 2) << "\n";);
    }

    for (app_set::iterator i = m_eqs.begin(); i != m_eqs.end(); ++i) {
        app * const a = *i;
        SASSERT(m_m.is_eq(a));
        sort* const s = m_m.mk_bool_sort();
        app * const fc = m_m.mk_fresh_const("eq", s);
        m_info->set_abstr(a, fc);
        TRACE("lackr", tout << "abstr eq "
            << mk_ismt2_pp(a, m_m, 2) << " -> " << mk_ismt2_pp(fc, m_m, 2) << "\n";);
    }

    lackr::build_abstraction_map();
}

model_constructor* lackr_arrays::mk_model_constructor(ast_manager& m, ackr_info_ref& info) {
    return alloc(lackr_arrays_model_constructor, m, info);
}

lbool lackr_arrays::lazy() {
    SASSERT(m_is_init);
    if (m_mc) dealloc(m_mc);
    m_mc = static_cast<lackr_arrays_model_constructor*>(mk_model_constructor(m_m, m_info));
    push_abstraction();
    unsigned ackr_head = 0;
    while (1) {
        m_st.m_it++;
        checkpoint();
        TRACE("lackr", tout << "lazy check: " << m_st.m_it << "\n";);
        TRACE("lackr", m_sat->display(tout););
        const lbool r = m_sat->check_sat(0, 0);
        if (r == l_undef) return l_undef; // give up
        if (r == l_false) return l_false; // abstraction unsat
        // reconstruct model
        model_ref am;
        m_sat->get_model(am);
        const bool mc_res = m_mc->check(am);
        if (mc_res) {
            TRACE("lackr", tout << "lazy check OK" << std::endl;);
            return l_true; // model okay
        }
        TRACE("lackr", tout << "lazy check confl" << std::endl;);
        // refine abstraction
        const lackr_arrays_model_constructor::conflict_list conflicts = m_mc->get_conflicts();
        for (lackr_arrays_model_constructor::conflict_list::const_iterator i = conflicts.begin();
             i != conflicts.end(); ++i) {
            ackr(i->first, i->second);
        }
        while (ackr_head < m_ackrs.size()) {
            m_sat->assert_expr(m_ackrs.get(ackr_head++));
        }
        const expr_ref_vector& lemmas = m_mc->get_array_lemmas();
        for (expr_ref_vector::iterator i = lemmas.begin(); i != lemmas.end(); ++i) {
            m_st.m_arr_lemmas_sz++;
            m_sat->assert_expr(*i);
        }
    }
}


void lackr_arrays::make_model(model_ref& m) {
    m_mc->make_model(m);
}
