/*++
 Copyright (c) 2016 Microsoft Corporation

 Module Name:

  bv_ternary_tactic.cpp

 Abstract:


 Author:

 Mikolas Janota (MikolasJanota)

 Revision History:
--*/
#include"bv_ternary_tactic.h"
#include"ast.h"
#include"rewriter.h"
#include"rewriter_def.h"
#include"rewriter_params.hpp"
#include"bool_rewriter.h"
#include"cooperate.h"
#include"bv_ternary_simplifier.h"

class bv_ternary_tactic : public tactic {
    class imp;
    imp *                     m_imp;
    params_ref                m_params;
    bv_ternary_stats          m_stats;
public:
    bv_ternary_tactic(ast_manager & m, params_ref const & p);
    virtual ~bv_ternary_tactic();
    void operator()(goal_ref const & g,
        goal_ref_buffer & result,
        model_converter_ref & mc,
        proof_converter_ref & pc,
        expr_dependency_ref & core);
    virtual tactic * translate(ast_manager & m);
    virtual void updt_params(params_ref const & p);
    void cleanup();
    void collect_statistics(statistics & st) const;
    void reset_statistics();
};

class bv_ternary_tactic::imp {
    bv_ternary_simplifier      m_rw;
    //bv_ternary_stats&           m_stats;
public:
    imp(ast_manager & m, params_ref const & p, bv_ternary_stats& stats)
        : m_rw(m, p, stats) {    }

    virtual ~imp() {    }

    ast_manager& m() { return m_rw.m(); }

    void operator()(goal_ref const & g) {
        SASSERT(g->is_well_sorted());
        tactic_report report("bv_ternary", *g);
        ast_manager& m(g->m());
        expr_ref   new_curr(m);
        const unsigned size = g->size();
        for (unsigned idx = 0; idx < size; idx++) {
            if (g->inconsistent()) break;
            expr * curr = g->form(idx);
            m_rw(curr, new_curr);
            g->update(idx, new_curr);
        }
        //m_rw.m_cfg.cleanup();
    }

    virtual void updt_params(params_ref const & p) {
        //m_rw.updt_params(p);
    }

    void collect_statistics(statistics & st) const {
        m_rw.collect_statistics(st);
    }

    void reset_statistics() {
        m_rw.reset_statistics();
    }
};

bv_ternary_tactic::bv_ternary_tactic(ast_manager & m, params_ref const & p)
    : m_params(p)
{
    m_imp = alloc(imp, m, p, m_stats);
}


bv_ternary_tactic::~bv_ternary_tactic() {
    dealloc(m_imp);
}

void bv_ternary_tactic::operator()(goal_ref const & g,
    goal_ref_buffer & result,
    model_converter_ref & mc,
    proof_converter_ref & pc,
    expr_dependency_ref & core) {
    SASSERT(g->is_well_sorted());
    fail_if_proof_generation("bv-bound-chk", g);
    fail_if_unsat_core_generation("bv-bound-chk", g);
    TRACE("bv-bound-chk", g->display(tout << "before:"); tout << std::endl;);
    mc = 0; pc = 0; core = 0; result.reset();
    m_imp->operator()(g);
    g->inc_depth();
    result.push_back(g.get());
    TRACE("bv-bound-chk", g->display(tout << "after:"););
    SASSERT(g->is_well_sorted());
}

tactic * bv_ternary_tactic::translate(ast_manager & m) {
    return alloc(bv_ternary_tactic, m, m_params);
}


void bv_ternary_tactic::updt_params(params_ref const & p) {
    m_params = p;
    m_imp->updt_params(p);
}

void bv_ternary_tactic::cleanup() {
    imp * d = alloc(imp, m_imp->m(), m_params, m_stats);
    std::swap(d, m_imp);
    dealloc(d);
}

void bv_ternary_tactic::collect_statistics(statistics & st) const {
    m_imp->collect_statistics(st);
}

void bv_ternary_tactic::reset_statistics() {
    m_imp->reset_statistics();
}

tactic * mk_bv_ternary_tactic(ast_manager & m, params_ref const & p) {
    return alloc(bv_ternary_tactic, m, p);
}
