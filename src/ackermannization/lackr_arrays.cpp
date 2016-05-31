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
, m_refs(m)
{
    updt_params(p);
}

lackr_arrays::~lackr_arrays() {
    if (m_mc) dealloc(m_mc);
}

void lackr_arrays::updt_params(params_ref const & _p) {
    lackr::updt_params(_p);
    m_eager = false;
}

lbool lackr_arrays::operator() () {
    SASSERT(!m_eager);
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

app* lackr_arrays::abstract_select(app * a) {
    SASSERT(m_ar_util.is_select(a));
    sort* const s = a->get_decl()->get_range();
    app * const fc = m_m.mk_fresh_const("select", s);
    m_info->set_abstr(a, fc);
    TRACE("lackr", tout << "abstr term "
            << mk_ismt2_pp(a, m_m, 2) << " -> " << mk_ismt2_pp(fc, m_m, 2) << "\n";);
    return fc;
}

void lackr_arrays::build_abstraction_map() {
    for (app_set::iterator i = m_selects.begin(); i != m_selects.end(); ++i) {
        abstract_select(*i);
    }

    expr* lhs;
    expr* rhs;
    const app_set::iterator e = m_eqs.end();
    for (app_set::iterator i = m_eqs.begin(); i != e; ++i) {
        app * const eq = *i;
        VERIFY(m_m.is_eq(eq, lhs, rhs));
        SASSERT(m_ar_util.is_array(lhs));
        sort * const arr_s = to_app(lhs)->get_decl()->get_range();
        SASSERT(get_array_arity(arr_s) == 1);
        sort * const dom_s = get_array_domain(arr_s, 0);
        app * const w_fc = m_m.mk_fresh_const("w", dom_s);
        expr * args[2] = { lhs, w_fc };
        app * const sel_lhs = m_ar_util.mk_select(2, args);
        args[0] = rhs;
        app * const sel_rhs = m_ar_util.mk_select(2, args);
        app * const sel_lhs_a = abstract_select(sel_lhs);
        app * const sel_rhs_a = abstract_select(sel_rhs);
        m_refs.push_back(expr_ref(sel_rhs, m_m));
        m_refs.push_back(expr_ref(sel_lhs, m_m));

        sort* const s = m_m.mk_bool_sort();
        app * const eq_fc = m_m.mk_fresh_const("eq", s);
        m_info->set_abstr(eq, eq_fc);

        m_sat->assert_expr(m_m.mk_or(eq_fc, m_m.mk_not(m_m.mk_eq(sel_lhs_a, sel_rhs_a))));
        TRACE("lackr", tout << "abstr eq "
            << mk_ismt2_pp(eq, m_m, 2) << " -> " << mk_ismt2_pp(eq_fc, m_m, 2) << "\n";);
    }

    lackr::build_abstraction_map();
}


lbool lackr_arrays::lazy() {
    SASSERT(m_is_init);
    if (m_mc) dealloc(m_mc);
    m_mc = alloc(lackr_arrays_model_constructor, m_m, m_info);
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
        TRACE("lackr", tout << "lazy check " << (mc_res ? "OK" : "confl") << std::endl;);
        if (mc_res) return l_true; // model okay
        // refine abstraction
        lackr_arrays_model_constructor::conflict_list::const_iterator i = m_mc->get_conflicts().begin();
        const lackr_arrays_model_constructor::conflict_list::const_iterator e = m_mc->get_conflicts().end();
        for ( ; i != e; ++i) {
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
    SASSERT(m_mc);
    m_mc->make_model(m);
}
