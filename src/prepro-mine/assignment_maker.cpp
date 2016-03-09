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
    typedef assignment_maker::gen_mode  gen_mode;
    ast_manager&                    m_m;
    gen_mode                        m_mode;
    bool_rewriter                   m_b_rw;
    //bv_rewriter                     m_bv_rw;
    bv_util                         m_bv_util;
    random_gen                      m_rnd;

    imp(ast_manager& m)
        : m_m(m)
        , m_mode(assignment_maker::RANDOM)
        , m_b_rw(m)
        //, m_bv_rw(m)
        , m_bv_util(m)
    {}

    bool make_polarity() {
        switch (m_mode) {
            case ONE: return true;
            case ZERO: return false;
            case RANDOM: return m_rnd() & 1;
            default: UNREACHABLE();
        }
        return false;
    }

    expr * mk_bv(unsigned sz) {
        rational two(2);
        rational one(rational::one());
        rational retv(rational::zero());
        for (unsigned i = 0; i < sz; ++i) {
           if (make_polarity()) retv = retv + one;
           retv = retv * two;
        }
        return m_bv_util.mk_numeral(retv, sz);
    }

    void make_value(sort * s, /*out*/expr_ref& v) {
        if (s->get_family_id() == m_b_rw.get_fid()) {
            v =  make_polarity() ? m_m.mk_true() : m_m.mk_false();
            return;
        }
        if (s->get_family_id() == m_bv_util.get_fid()) {
            const int sz = m_bv_util.get_bv_size(s);
            v = mk_bv(sz);
            return;
        }
        v = m_m.get_some_value(s);
    }

    void set_mode(gen_mode mode) { m_mode = mode; }

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

void assignment_maker::set_mode(assignment_maker::gen_mode mode) {
    m_imp->set_mode(static_cast<imp::gen_mode>(mode));
}

void assignment_maker::operator() (/*in*/unsigned count,
    /*in*/func_decl* const * declarations,/*out*/model_ref& assignment) {
    m_imp->operator() (count, declarations, assignment);
}
