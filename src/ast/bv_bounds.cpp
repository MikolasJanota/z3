/*++
 Copyright (c) 2016 Microsoft Corporation

 Module Name:

  bv_bounds.cpp

 Abstract:


 Author:

 Mikolas Janota

 Revision History:
--*/
#include "bv_bounds.h"
#include"ast_smt2_pp.h"

void bv_bounds::add_constraint(expr* e) {
    TRACE("bv_bounds", tout << "new constraint" << mk_ismt2_pp(e, m_m) << std::endl;);
    expr *lhs, *rhs;
    if (m_bv_util.is_bv_ule(e, lhs, rhs)) {
        numeral val;
        unsigned bv_sz = m_bv_util.get_bv_size(lhs);
        if (is_uninterp_const(lhs) && m_bv_util.is_numeral(rhs, val, bv_sz)) bound_lo(to_app(lhs), val);
        else if (is_uninterp_const(rhs) && m_bv_util.is_numeral(lhs, val, bv_sz)) bound_up(to_app(rhs), val);
    }

    if (m_bv_util.is_bv_sle(e, lhs, rhs)) {
        numeral val;
        unsigned bv_sz = m_bv_util.get_bv_size(lhs);
        SASSERT(bv_sz > 1);
        if (bv_sz == 1) return;
        const numeral middle = rational::power_of_two(bv_sz - 1);
        if (is_uninterp_const(lhs) && m_bv_util.is_numeral(rhs, val, bv_sz)) { // v <= val
            app * const v = to_app(lhs);
            if (val >= middle) { // val < 0
                bound_lo(v, middle);
                bound_up(v, val);
            }
            else { // val >= 0
                interval ni;
                ni.first = val + numeral(1);
                ni.second = middle - numeral(1);
                if (ni.first<=ni.second) neg_bound(v, ni);
            }
        }
        else if (is_uninterp_const(rhs) && m_bv_util.is_numeral(lhs, val, bv_sz)) { // val <= v
                app * const v = to_app(rhs);
                if (val >= middle) { // val < 0
                    interval ni;
                    ni.first = middle;
                    ni.second = val - numeral(1);
                    if (ni.first <= ni.second) neg_bound(v, ni);

                }
                else { // val >= 0
                    bound_up(v, middle - numeral(1));
                    bound_lo(v, val);
                }
            }
    }

}

bool bv_bounds::bound_lo(app * v, numeral l) {
    SASSERT(l >= numeral(0));
    TRACE("bv_bounds", tout << "lower " << mk_ismt2_pp(v, m_m) << ":" << l << std::endl;);
    // l <= v
    bound_map::obj_map_entry * const entry = m_unsigned_lowers.insert_if_not_there2(v, l);
    if (!(entry->get_data().m_value < l)) return false;
    // improve bound
    entry->get_data().m_value = l;
    return true;
}

bool bv_bounds::bound_up(app * v, numeral u) {
    SASSERT(u >= numeral(0));
    TRACE("bv_bounds", tout << "upper " << mk_ismt2_pp(v, m_m) << ":" << u << std::endl;);
    // v <= u
    bound_map::obj_map_entry * const entry = m_unsigned_uppers.insert_if_not_there2(v, u);
    if (!(u < entry->get_data().m_value)) return false;
    // improve bound
    entry->get_data().m_value = u;
    return true;
}

void bv_bounds::neg_bound(app * v, const bv_bounds::interval& negative_interval) {
    TRACE("bv_bounds", tout << "negative bound " << mk_ismt2_pp(v, m_m) << ":" << negative_interval.first<<"-"<< negative_interval.second << std::endl;);
    SASSERT(m_bv_util.is_bv(v));
    SASSERT(negative_interval.first >= rational(0));
    SASSERT(negative_interval.second < rational::power_of_two(m_bv_util.get_bv_size(v)));
    SASSERT(negative_interval.first <= negative_interval.second);

    intervals_map::obj_map_entry * const e = m_negative_intervals.find_core(v);
    intervals * ivs(NULL);
    if (e == 0) {
        ivs = alloc(intervals);
        m_negative_intervals.insert(v, ivs);
    }
    else { 
        ivs = e->get_data().get_value();
    }
    ivs->push_back(negative_interval);
}


bool bv_bounds::is_sat() {
    obj_hashtable<app>   seen;
    obj_hashtable<app>::entry *dummy;

    for (bound_map::iterator i = m_unsigned_lowers.begin(); i != m_unsigned_lowers.end(); ++i) {
        app * const v = i->m_key;
        if (!seen.insert_if_not_there_core(v, dummy)) continue;
        if (!is_sat(v)) return false;
    }

    for (bound_map::iterator i = m_unsigned_uppers.begin(); i != m_unsigned_uppers.end(); ++i) {
        app * const v = i->m_key;
        if (!seen.insert_if_not_there_core(v, dummy)) continue;
        if (!is_sat(v)) return false;
    }

    for (intervals_map::iterator i = m_negative_intervals.begin(); i != m_negative_intervals.end(); ++i) {
        app * const v = i->m_key;
        if (!seen.insert_if_not_there_core(v, dummy)) continue;
        if (!is_sat(v)) return false;
    }

    return true;
}

struct interval_comp_t {
    bool operator() (bv_bounds::interval i, bv_bounds::interval j) {
        return (i.first<j.first);
    }
} interval_comp;

bool bv_bounds::is_sat(app * v) {
    TRACE("bv_bounds", tout << "is_sat " << mk_ismt2_pp(v, m_m) << std::endl;);
    SASSERT(m_bv_util.is_bv(v));
    func_decl * const d = v->get_decl();
    unsigned const bv_sz = m_bv_util.get_bv_size(v);
    numeral lower, upper;
    const bool has_upper = m_unsigned_uppers.find(v, upper);
    const bool has_lower = m_unsigned_lowers.find(v, lower);
    if (has_upper && has_lower && lower > upper) return false;
    if (!has_lower) lower = numeral(0);
    if (!has_upper) upper = (rational::power_of_two(bv_sz) - rational(1));
    TRACE("bv_bounds", tout << "is_sat bound:" << lower << "-" << upper << std::endl;);
    intervals * negative_intervals;
    const bool has_intervals = m_negative_intervals.find(v, negative_intervals);
    if (!has_intervals) return true;
    SASSERT(negative_intervals);
    std::sort(negative_intervals->begin(), negative_intervals->end(), interval_comp);
    intervals::const_iterator e = negative_intervals->end();
    for (intervals::const_iterator i = negative_intervals->begin(); i != e; ++i) {
        const numeral negative_lower = i->first;
        const numeral negative_upper = i->second;
        if (lower < negative_lower) return true;
        lower = negative_upper + rational(1);
        TRACE("bv_bounds", tout << "is_sat bound:" << lower << "-" << upper << std::endl;);
        if (lower > upper) return false;
    }
    SASSERT(upper <= lower);
    return true;
}