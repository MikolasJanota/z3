 /*++
 Copyright (c) 2016 Microsoft Corporation

 Module Name:

  bv_bounds.h

 Abstract:

 A class used to determine bounds on bit-vector variables.
 The satisfiability procedure is polynomial.


 Author:

 Mikolas Janota (MikolasJanota)

 Revision History:
 --*/
#ifndef BV_BOUNDS_H_23754
#define BV_BOUNDS_H_23754
#include"ast.h"
#include"bv_decl_plugin.h"

/* 
 * All bounds/intervals are closed. Methods that add new constraints 
 * return false if inconsistency has already been reached.  
 * Typical usage is to call add_constraint(e) repeatedly and call is_sat() in the end.  
 */
class bv_bounds {
public:
    typedef rational numeral;
    typedef std::pair<numeral, numeral> interval;
    bv_bounds(ast_manager& m) : m_m(m), m_bv_util(m), m_okay(true) {};
public: // bounds addition methods
    bool bound_up(app * v, numeral u); // v <= u
    bool bound_lo(app * v, numeral l); // l <= v
    inline bool add_neg_bound(app * v, numeral a, numeral b); // not (a<=v<=b)
    bool add_bound_signed(app * v, numeral a, numeral b, bool negate);
    bool add_bound_unsigned(app * v,  numeral a, numeral b, bool negate);
    bool add_constraint(expr* e); // identify special types of expressions to determine bounds
public:
    bool is_sat();
    bool is_okay();
protected:
    typedef vector<interval>            intervals;
    typedef obj_map<app, intervals*>    intervals_map; 
    typedef obj_map<app, numeral>       bound_map;
    ast_manager&              m_m;
    bound_map                 m_unsigned_lowers;
    bound_map                 m_unsigned_uppers;
    intervals_map             m_negative_intervals;
    bv_util                   m_bv_util;
    bool                      m_okay;
    bool                      is_sat(app * v);
    inline bool               in_range(app *v, numeral l);
    inline bool               is_constant_add(unsigned bv_sz, expr * e, app*& v, numeral& val);
};


inline bool bv_bounds::is_okay() { return m_okay; }

inline bool bv_bounds::in_range(app *v, bv_bounds::numeral n) {
    const unsigned bv_sz = m_bv_util.get_bv_size(v);
    const bv_bounds::numeral zero(0);
    const bv_bounds::numeral mod(rational::power_of_two(bv_sz));
    return (zero <= n) && (n < mod);
}

inline bool bv_bounds::is_constant_add(unsigned bv_sz, expr * e, app*& v, numeral& val) {
    SASSERT(e && !v);
    SASSERT(m_bv_util.get_bv_size(e) == bv_sz);
    if (is_uninterp_const(e)) {
        v = to_app(e);
        val = rational(0);
        return true;
    }
    expr *lhs(NULL), *rhs(NULL);
    if (!m_bv_util.is_bv_add(e, lhs, rhs)) return false;
    if (is_uninterp_const(lhs) && m_bv_util.is_numeral(rhs, val, bv_sz)) {
        v = to_app(lhs);
        return true;
    }
    if (is_uninterp_const(rhs) && m_bv_util.is_numeral(lhs, val, bv_sz)) {
        v = to_app(rhs);
        return true;
    }
    return false;
}


#endif /* BV_BOUNDS_H_23754 */
