/*++
 Copyright (c) 2016 Microsoft Corporation

 Module Name:

  bv_bounds.cpp

 Abstract:


 Author:

 Mikolas Janota (MikolasJanota)

 Revision History:
--*/
#include "bv_bounds.h"
#include"ast_smt2_pp.h"

bool bv_bounds::add_constraint(expr* e) {
    TRACE("bv_bounds", tout << "new constraint" << mk_ismt2_pp(e, m_m) << std::endl;);
    if (!m_okay) return false;

    bool negated = false;
    if (m_m.is_not(e)) {
        negated = true;
        e = to_app(e)->get_arg(0);
    }

    expr *lhs, *rhs;
    numeral val;

    if (m_bv_util.is_bv_ule(e, lhs, rhs)) {
        unsigned bv_sz = m_bv_util.get_bv_size(lhs);
        // unsigned inequality with one variable and a constant
        if (is_uninterp_const(lhs) && m_bv_util.is_numeral(rhs, val, bv_sz)) // v <= val
            return add_bound_unsigned(to_app(lhs), rational(0), val, negated);
        if (is_uninterp_const(rhs) && m_bv_util.is_numeral(lhs, val, bv_sz)) // val <= v
            return add_bound_unsigned(to_app(rhs), val, rational::power_of_two(bv_sz) - rational(1), negated);

        // unsigned inequality with one variable, constant, and addition
        expr *t1, *t2;
        if (m_bv_util.is_bv_add(lhs, t1, t2)
            && m_bv_util.is_numeral(t1, val, bv_sz)
            && is_uninterp_const(t2)
            && t2 == rhs) {  // val + v <= v
            const numeral mod = rational::power_of_two(bv_sz);
            return add_bound_unsigned(to_app(rhs), mod - val, mod - rational(1), negated);
        }
    }

    if (m_bv_util.is_bv_sle(e, lhs, rhs)) { 
        unsigned bv_sz = m_bv_util.get_bv_size(lhs);
        // signed inequality with one variable and a constant
        if (is_uninterp_const(lhs) && m_bv_util.is_numeral(rhs, val, bv_sz)) { // v <= val
            val = m_bv_util.norm(val, bv_sz, true);
            return add_bound_signed(to_app(lhs), -rational::power_of_two(bv_sz - 1), val, negated);
        }
        if (is_uninterp_const(rhs) && m_bv_util.is_numeral(lhs, val, bv_sz)) { // val <= v
            val = m_bv_util.norm(val, bv_sz, true);
            return add_bound_signed(to_app(rhs), val, rational::power_of_two(bv_sz - 1) - rational(1), negated);
        }

        app * v1(NULL), * v2(NULL);
        numeral val1, val2;
        if (is_constant_add(bv_sz, lhs, v1, val1)
            && is_constant_add(bv_sz, rhs, v2, val2)
            && v1 == v2) {
            if (val1 == val2) return m_okay;
            const numeral mod = rational::power_of_two(bv_sz);
            if (val1 < val2) {
                SASSERT(val1 < (mod - rational(1)));
                SASSERT(val2 > rational(0));
                return add_bound_unsigned(v1, mod - val2, mod - val1 - rational(1), !negated);
            }
            else {
                SASSERT(val1 > val2);
                SASSERT(val2 < (mod - rational(1)));
                SASSERT(val1 > rational(0));
                return add_bound_unsigned(v1, mod - val1, mod - val2 - rational(1), negated);
            }
        }
    }

    return m_okay;
}

bool bv_bounds::add_bound_unsigned(app * v, numeral a, numeral b, bool negate) {
    TRACE("bv_bounds", tout << "bound_unsigned " << mk_ismt2_pp(v, m_m) << ":" << (negate ? "~" : " ") << a << ";" << b << std::endl;);
    const unsigned bv_sz = m_bv_util.get_bv_size(v);
    SASSERT(rational(0) <= a);
    SASSERT(a <= b);
    SASSERT(b < rational::power_of_two(bv_sz));
    const bool a_min = a == rational(0);
    const bool b_max = b == (rational::power_of_two(bv_sz) - rational(1));
    if (negate) {
        if (a_min && b_max) return m_okay = false;
        if (a_min) return bound_lo(v, b + rational(1));
        if (b_max) return bound_up(v, a - rational(1));
        return add_neg_bound(v, a, b);
    }
    else {
        if (!a_min) m_okay &= bound_lo(v, a);
        if (!b_max) m_okay &= bound_up(v, b);
        return m_okay;
    }
}

bool bv_bounds::add_bound_signed(app * v, numeral a, numeral b, bool negate) {
    TRACE("bv_bounds", tout << "bound_signed " << mk_ismt2_pp(v, m_m) << ":" << (negate ? "~" : " ") << a << ";" << b << std::endl;);
    const unsigned bv_sz = m_bv_util.get_bv_size(v);
    SASSERT(a <= b);
    const bool a_neg = a < rational(0);
    const bool b_neg = b < rational(0);
    if (!a_neg && !b_neg) return add_bound_unsigned(v, a, b, negate);
    const numeral mod = rational::power_of_two(bv_sz);
    if (a_neg && b_neg) return add_bound_unsigned(v, mod + a, mod + b, negate);
    SASSERT(a_neg && !b_neg);
    if (negate) {
        return add_bound_unsigned(v, mod + a, mod - rational(1), true)
            && add_bound_unsigned(v, rational(0), b, true);
    }
    else {
        const numeral l = b + rational(1);
        const numeral u = mod + a - rational(1);
        return (l <= u) ? add_bound_unsigned(v, l, u, true) : m_okay;
    }
}

bool bv_bounds::bound_lo(app * v, numeral l) {
    SASSERT(in_range(v, l));
    TRACE("bv_bounds", tout << "lower " << mk_ismt2_pp(v, m_m) << ":" << l << std::endl;);
    // l <= v
    bound_map::obj_map_entry * const entry = m_unsigned_lowers.insert_if_not_there2(v, l);
    if (!(entry->get_data().m_value < l)) return m_okay;
    // improve bound
    entry->get_data().m_value = l;
    return m_okay;
}

bool bv_bounds::bound_up(app * v, numeral u) {
    SASSERT(in_range(v, u));
    TRACE("bv_bounds", tout << "upper " << mk_ismt2_pp(v, m_m) << ":" << u << std::endl;);
    // v <= u
    bound_map::obj_map_entry * const entry = m_unsigned_uppers.insert_if_not_there2(v, u);
    if (!(u < entry->get_data().m_value)) return m_okay;
    // improve bound
    entry->get_data().m_value = u;
    return m_okay;
}

bool bv_bounds::add_neg_bound(app * v, numeral a, numeral b) {
    TRACE("bv_bounds", tout << "negative bound " << mk_ismt2_pp(v, m_m) << ":" << a << ";" << b << std::endl;);
    bv_bounds::interval negative_interval(a, b);
    SASSERT(m_bv_util.is_bv(v));
    SASSERT(a >= rational(0));
    SASSERT(b < rational::power_of_two(m_bv_util.get_bv_size(v)));
    SASSERT(a <= b);

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
    return m_okay;
}


bool bv_bounds::is_sat() {
    if (!m_okay) return false;
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
    if (!m_okay) return false;
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
