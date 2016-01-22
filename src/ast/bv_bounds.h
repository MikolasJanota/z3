 /*++
 Copyright (c) 2016 Microsoft Corporation

 Module Name:

  bv_bounds.h

 Abstract:


 Author:

 Mikolas Janota

 Revision History:
 --*/
#ifndef BV_BOUNDS_H_23754
#define BV_BOUNDS_H_23754
#include"ast.h"
#include"bv_decl_plugin.h"

class bv_bounds {
public:
    typedef rational numeral;
    typedef std::pair<numeral, numeral> interval;
    bv_bounds(ast_manager& m) : m_m(m), m_bv_util(m) {};
    bool bound_up(app * v, numeral u);
    bool bound_lo(app * v, numeral l);
    void neg_bound(app * v, const interval& negative_interval);
    bool is_sat();
    void add_constraint(expr* e);
protected:
    typedef vector<interval>            intervals;
    typedef obj_map<app, intervals*>    intervals_map; 
    typedef obj_map<app, numeral>       bound_map;
    ast_manager&              m_m;
    bound_map                 m_unsigned_lowers;
    bound_map                 m_unsigned_uppers;
    intervals_map             m_negative_intervals;
    bv_util                   m_bv_util;
    bool is_sat(app * v);
};


#endif /* BV_BOUNDS_H_23754 */
