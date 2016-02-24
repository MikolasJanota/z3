/*++
 Copyright (c) 2016 Microsoft Corporation

 Module Name:

  bv_ternary_simplifier.cpp

 Abstract:


 Author:

 Mikolas Janota (MikolasJanota)

 Revision History:
--*/
#include"bv_ternary_simplifier.h"
#include"rewriter_params.hpp"
#include"bool_rewriter.h"
#include"bv_rewriter.h"
#include"ast_smt2_pp.h"
#include"cooperate.h"
#include"ast_util.h"
#include"well_sorted.h"
#include"rewriter_def.h"
#include"lbool.h"
#include"ref.h"


class tvec {
public:
    tvec() : m_data(0), m_ref_count(0) {}
    tvec(vector<lbool>::const_iterator b, unsigned size)
        : m_data(0), m_ref_count(0)
    {
        m_data = static_cast<lbool*>(memory::allocate(sizeof(lbool) * size));
        for (unsigned i = 0; i < size; ++i,++b) m_data[i] = *b;
    }

    ~tvec() {
        if (m_data) memory::deallocate(m_data);
    }

    void inc_ref() {
        SASSERT(m_ref_count < UINT_MAX);
        m_ref_count++;
    }

    void dec_ref() {
        SASSERT(m_ref_count > 0);
        m_ref_count--;
    }
private:
    lbool *    m_data;
    unsigned   m_ref_count;
};

typedef ref<tvec> tvec_ref;

struct bv_ternary_simplifier_cfg : public default_rewriter_cfg {
    bool_rewriter       m_b_rw;
    bv_rewriter         m_bv_rw;
    bv_util             m_bv_util;
    unsigned long long  m_max_memory; // in bytes
    unsigned            m_max_steps;
    bool                m_pull_cheap_ite;
    bool                m_flat;
    bool                m_cache_all;
    bool                m_push_ite_arith;
    bool                m_push_ite_bv;

    ast_manager & m() const { return m_b_rw.m(); }

    void updt_local_params(params_ref const & _p) {
        rewriter_params p(_p);
        m_flat = p.flat();
        m_max_memory = megabytes_to_bytes(p.max_memory());
        m_max_steps = p.max_steps();
        m_pull_cheap_ite = p.pull_cheap_ite();
        m_cache_all = p.cache_all();
        m_push_ite_arith = p.push_ite_arith();
        m_push_ite_bv = p.push_ite_bv();
    }

    void updt_params(params_ref const & p) {
        m_b_rw.updt_params(p);
        m_bv_rw.updt_params(p);
        updt_local_params(p);
    }

    bool flat_assoc(func_decl * f) const {
        if (!m_flat) return false;
        family_id fid = f->get_family_id();
        if (fid == null_family_id)
            return false;
        decl_kind k = f->get_decl_kind();
        if (fid == m_b_rw.get_fid())
            return k == OP_AND || k == OP_OR;
        if (fid == m_bv_rw.get_fid())
            return k == OP_BADD || k == OP_BOR || k == OP_BAND || k == OP_BXOR;
        return false;
    }

    bool rewrite_patterns() const { return false; }

    bool cache_all_results() const { return m_cache_all; }

    bool max_steps_exceeded(unsigned num_steps) const {
        cooperate("bv_ternary_simplifier");
        if (memory::get_allocation_size() > m_max_memory)
            throw rewriter_exception(Z3_MAX_MEMORY_MSG);
        return num_steps > m_max_steps;
    }

    br_status reduce_app_core(func_decl * f, unsigned num, expr * const * args, expr_ref & result) {
        family_id fid = f->get_family_id();
        if (fid == null_family_id)
            return BR_FAILED;
        br_status st = BR_FAILED;
        if (fid == m_b_rw.get_fid()) {
            decl_kind k = f->get_decl_kind();
            if (k == OP_EQ) {
                // theory dispatch for =
                SASSERT(num == 2);
                family_id s_fid = m().get_sort(args[0])->get_family_id();
                if (s_fid == m_bv_rw.get_fid())
                    st = m_bv_rw.mk_eq_core(args[0], args[1], result);

                if (st != BR_FAILED)
                    return st;
            }
            return m_b_rw.mk_app_core(f, num, args, result);
        }
        if (fid == m_bv_rw.get_fid())
            return m_bv_rw.mk_app_core(f, num, args, result);
        return BR_FAILED;
    }

    br_status reduce_app(func_decl * f, unsigned num, expr * const * args, expr_ref & result, proof_ref & result_pr) {
        result_pr = 0;
        br_status st = reduce_app_core(f, num, args, result);
        if (st != BR_DONE && st != BR_FAILED) {
            CTRACE("bv_ternary_simplifier_step", st != BR_FAILED,
                tout << f->get_name() << "\n";
            for (unsigned i = 0; i < num; i++) tout << mk_ismt2_pp(args[i], m()) << "\n";
            tout << "---------->\n" << mk_ismt2_pp(result, m()) << "\n";);
            return st;
        }
        CTRACE("bv_ternary_simplifier_step", st != BR_FAILED,
            tout << f->get_name() << "\n";
        for (unsigned i = 0; i < num; i++) tout << mk_ismt2_pp(args[i], m()) << "\n";
        tout << "---------->\n" << mk_ismt2_pp(result, m()) << "\n";);
        return st;
    }


    bv_ternary_simplifier_cfg(ast_manager & m, params_ref const & p) :
        m_b_rw(m, p),
        m_bv_rw(m, p),
        m_bv_util(m) {
        updt_local_params(p);
    }

};

template class rewriter_tpl<bv_ternary_simplifier_cfg>;

struct bv_ternary_simplifier::imp : public rewriter_tpl<bv_ternary_simplifier_cfg> {
    bv_ternary_simplifier_cfg m_cfg;
    imp(ast_manager & m, params_ref const & p) :
        rewriter_tpl<bv_ternary_simplifier_cfg>(m, m.proofs_enabled(), m_cfg),
        m_cfg(m, p) {
    }
};

bv_ternary_simplifier::bv_ternary_simplifier(ast_manager & m, params_ref const & p) :
    m_params(p) {
    m_imp = alloc(imp, m, p);
}

ast_manager & bv_ternary_simplifier::m() const {
    return m_imp->m();
}

void bv_ternary_simplifier::updt_params(params_ref const & p) {
    m_params = p;
    m_imp->cfg().updt_params(p);
}

void bv_ternary_simplifier::get_param_descrs(param_descrs & r) {
    bool_rewriter::get_param_descrs(r);
    bv_rewriter::get_param_descrs(r);
    rewriter_params::collect_param_descrs(r);
}

bv_ternary_simplifier::~bv_ternary_simplifier() {
    dealloc(m_imp);
}

unsigned bv_ternary_simplifier::get_cache_size() const {
    return m_imp->get_cache_size();
}

unsigned bv_ternary_simplifier::get_num_steps() const {
    return m_imp->get_num_steps();
}


void bv_ternary_simplifier::cleanup() {
    ast_manager & m = m_imp->m();
    dealloc(m_imp);
    m_imp = alloc(imp, m, m_params);
}

void bv_ternary_simplifier::reset() {
    m_imp->reset();
    m_imp->cfg().reset();
}

void bv_ternary_simplifier::operator()(expr_ref & term) {
    expr_ref result(term.get_manager());
    m_imp->operator()(term, result);
    term = result;
}

void bv_ternary_simplifier::operator()(expr * t, expr_ref & result) {
    m_imp->operator()(t, result);
}

void bv_ternary_simplifier::operator()(expr * t, expr_ref & result, proof_ref & result_pr) {
    m_imp->operator()(t, result, result_pr);
}