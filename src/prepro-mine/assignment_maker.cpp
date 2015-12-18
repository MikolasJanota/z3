/*++
 Copyright (c) 2015 Microsoft Corporation

 Module Name:

  assignment_maker.cpp

 Abstract:


 Author:

 Mikolas Janota

 Revision History:
--*/
#include"assignment_maker.h"
#include"bool_rewriter.h"
#include"bv_rewriter.h"
#include"ast_smt2_pp.h"
struct assignment_maker::imp {
    ast_manager&                    m_m;
    bool                            m_polarity;
    bool_rewriter                   m_b_rw;
    //bv_rewriter                     m_bv_rw;
    bv_util                         m_bv_util;

    imp(ast_manager& m)
        : m_m(m)
        , m_polarity(false)
        , m_b_rw(m)
        //, m_bv_rw(m)
        , m_bv_util(m)
    {}


    void make_value(sort * s, /*out*/expr_ref& v) {
        if (s->get_family_id() == m_b_rw.get_fid()) {
            v =  m_polarity ? m_m.mk_true() : m_m.mk_false();
            return;
        }
        if (s->get_family_id() == m_bv_util.get_fid()) {
            const int width = m_bv_util.get_bv_size(s);
            const rational rv = m_polarity ? rational::power_of_two(width) - rational(1)
                                           : rational(0);
            v = m_bv_util.mk_numeral(rv, width);
            return;
        }
        v = m_m.get_some_value(s);
    }

    void set_polarity(bool polarity) { m_polarity = polarity; }

    void operator() (/*in*/unsigned count,
            /*in*/func_decl* const * declarations,
            /*out*/model_ref& assignment) {
        for (unsigned i = 0; i < count; ++i) {
            func_decl * const declaration = declarations[i];
            expr_ref value(m_m);
            make_value(declaration->get_range(), value);
            const unsigned arity = declaration->get_arity();
            if (arity == 0) {
                assignment->register_decl(declaration, value);
            }
            else {
                func_interp * fi = alloc(func_interp, m_m, arity);
                fi->set_else(value.get());
                assignment->register_decl(declaration, fi);
            }
        }
    }
};

assignment_maker::assignment_maker(ast_manager& m)
    : m_imp(alloc(imp, m))
{ }

assignment_maker::~assignment_maker() { dealloc(m_imp); }

void assignment_maker::set_polarity(bool polarity) {
    m_imp->set_polarity(polarity);
}

void assignment_maker::operator() (/*in*/unsigned count,
    /*in*/func_decl* const * declarations,/*out*/model_ref& assignment) {
    m_imp->operator() (count, declarations, assignment);
}
