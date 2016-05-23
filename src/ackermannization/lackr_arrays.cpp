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
            << mk_ismt2_pp(a, m_m, 2)
            << " -> "
            << mk_ismt2_pp(fc, m_m, 2)
            << "\n";);
    }

    for (app_set::iterator i = m_eqs.begin(); i != m_eqs.end(); ++i) {
        app * const a = *i;
        SASSERT(m_m.is_eq(a));
        sort* const s = m_m.mk_bool_sort();
        app * const fc = m_m.mk_fresh_const("eq", s);
        m_info->set_abstr(a, fc);
        TRACE("lackr", tout << "abstr term "
            << mk_ismt2_pp(a, m_m, 2)
            << " -> "
            << mk_ismt2_pp(fc, m_m, 2)
            << "\n";);
    }

    lackr::build_abstraction_map();
}

model_constructor* lackr_arrays::mk_model_constructor(ast_manager& m, ackr_info_ref& info) {
    return alloc(lackr_arrays_model_constructor, m, info);
}
