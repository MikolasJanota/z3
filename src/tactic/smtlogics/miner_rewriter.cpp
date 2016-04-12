/*++
 Copyright (c) 2015 Microsoft Corporation

 Module Name:

  miner_rewriter.cpp

 Abstract:


 Author:

 Mikolas Janota

 Revision History:
--*/
#include"miner_rewriter.h"
#include"miner_rewriter_params.hpp"
#include"miner.h"
#include"rewriter_types.h"
#include"bool_rewriter.h"
#include"arith_rewriter.h"
#include"bv_rewriter.h"
#include"pb_rewriter.h"
#include"datatype_rewriter.h"
#include"array_rewriter.h"
#include"fpa_rewriter.h"
#include"rewriter_def.h"
#include"cooperate.h"

struct rewriter_cfg : public default_rewriter_cfg {
    ast_manager&                    m_m;
    bool_rewriter                   m_b_rw;
    arith_rewriter                  m_a_rw;
    bv_rewriter                     m_bv_rw;
    array_rewriter                  m_ar_rw;
    datatype_rewriter               m_dt_rw;
    pb_rewriter                     m_pb_rw;
    fpa_rewriter                    m_f_rw;
    miner                           m_miner;
    unsigned long long              m_max_memory;
    unsigned                        m_max_steps;
    bool                            m_model_completion;
    bool                            m_cache;

    rewriter_cfg(ast_manager & m, params_ref const & p)
        : m_m(m)
        , m_b_rw(m)
        , m_a_rw(m, p)
        , m_bv_rw(m)
        , m_ar_rw(m, p)
        , m_dt_rw(m)
        , m_pb_rw(m)
        , m_f_rw(m)
        , m_miner(m)
    {
        m_b_rw.set_flat(false);
        m_a_rw.set_flat(false);
        m_bv_rw.set_flat(false);
        m_bv_rw.set_mkbv2num(true);
        updt_params(p);
    }

    void updt_params(params_ref const & _p) {
        miner_rewriter_params p(_p);
        m_max_memory       = megabytes_to_bytes(p.max_memory());
        m_max_steps        = p.max_steps();
        m_cache            = p.cache();
    }

    br_status reduce_app(func_decl * f,
            unsigned num, expr * const * args,
            expr_ref & result, proof_ref & result_pr) {
        app_ref term(m_m);
        term = m_m.mk_app(f, num, args);
        if (m_miner.test_term(term.get(), result))
            return BR_DONE;

        br_status st = BR_FAILED;
        const family_id fid = f->get_family_id();
        if (fid == m_b_rw.get_fid()) {
            decl_kind k = f->get_decl_kind();
            if (k == OP_EQ) {
                // theory dispatch for =
                SASSERT(num == 2);
                family_id s_fid = m_m.get_sort(args[0])->get_family_id();
                if (s_fid == m_a_rw.get_fid())
                    st = m_a_rw.mk_eq_core(args[0], args[1], result);
                else if (s_fid == m_bv_rw.get_fid())
                    st = m_bv_rw.mk_eq_core(args[0], args[1], result);
                else if (s_fid == m_dt_rw.get_fid())
                    st = m_dt_rw.mk_eq_core(args[0], args[1], result);
                else if (s_fid == m_f_rw.get_fid())
                    st = m_f_rw.mk_eq_core(args[0], args[1], result);
                if (st != BR_FAILED)
                    return st;
            }
            return m_b_rw.mk_app_core(f, num, args, result);
        }

        if (fid == m_a_rw.get_fid())
            st = m_a_rw.mk_app_core(f, num, args, result);
        else if (fid == m_bv_rw.get_fid())
            st = m_bv_rw.mk_app_core(f, num, args, result);
        else if (fid == m_ar_rw.get_fid())
            st = m_ar_rw.mk_app_core(f, num, args, result);
        else if (fid == m_dt_rw.get_fid())
            st = m_dt_rw.mk_app_core(f, num, args, result);
        else if (fid == m_pb_rw.get_fid())
            st = m_pb_rw.mk_app_core(f, num, args, result);
        else if (fid == m_f_rw.get_fid())
            st = m_f_rw.mk_app_core(f, num, args, result);
        return st;
    }


    bool max_steps_exceeded(unsigned num_steps) const {
        cooperate("miner evaluator");
        if (memory::get_allocation_size() > m_max_memory)
            throw rewriter_exception(Z3_MAX_MEMORY_MSG);
        return num_steps > m_max_steps;
    }

    bool cache_results() const { return m_cache; }
};

template class rewriter_tpl<rewriter_cfg>;

struct miner_rewriter::imp : public rewriter_tpl<rewriter_cfg> {
    rewriter_cfg m_cfg;
    imp(ast_manager& m, params_ref const & p)
        : rewriter_tpl<rewriter_cfg>(m,false,m_cfg)
        , m_cfg(m, p) { }
};

miner_rewriter::miner_rewriter(ast_manager& m, params_ref const & p) {
    m_imp = alloc(imp, m, p);
}

miner_rewriter::~miner_rewriter() {
    dealloc(m_imp);
}

void miner_rewriter::updt_params(params_ref const & p) {
    m_imp->cfg().updt_params(p);
}


void miner_rewriter::operator()(expr * t, expr_ref & result) {
    expr_ref e(m_imp->m_cfg.m_m);
    e = t;
    m_imp->m_cfg.m_miner.init(e);
    m_imp->operator()(t, result);
}



