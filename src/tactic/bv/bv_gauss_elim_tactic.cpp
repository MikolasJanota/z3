/*++
 Copyright (c) 2016 Microsoft Corporation

 Module Name:

  bv_gauss_elim_tactic.cpp

 Abstract:


 Author:

 Mikolas Janota

 Revision History:
--*/
#include"bv_gauss_elim_tactic.h"
#include"bv_gauss_elim.h"
#include"bv_decl_plugin.h"
#include"ast_pp.h"
#include "tactical.h"
class bv_gauss_elim_tactic : public tactic {
    struct imp;
    imp *      m_imp;
public:
    bv_gauss_elim_tactic(ast_manager & m);

    virtual tactic * translate(ast_manager & m) {
        return alloc(bv_gauss_elim_tactic, m);
    }

    virtual ~bv_gauss_elim_tactic();

    virtual void operator()(goal_ref const & g, goal_ref_buffer & result, model_converter_ref & mc, proof_converter_ref & pc, expr_dependency_ref & core);

    virtual void cleanup();
};

tactic * mk_bv_gauss_elim_tactic(ast_manager & m, params_ref const & p) {
    return clean(alloc(bv_gauss_elim_tactic, m));
}

struct bv_gauss_elim_tactic::imp {
    typedef rational numeral;

    ast_manager &             m_m;
    bv_util                   m_util;

    imp(ast_manager & m):
        m_m(m),
        m_util(m)
        { }

    void checkpoint() {
        if (m_m.canceled())
            throw tactic_exception(m_m.limit().get_cancel_msg());
    }

    void operator()(goal_ref const &  g, goal_ref_buffer & result, model_converter_ref & mc) {
        if (g->inconsistent())
            return;
        TRACE("before_bv_gauss_elim", g->display(tout););
        mc = 0;
		ptr_vector<expr> flas;
		g->get_formulas(flas);
		ast_manager& m = g->m();
		vector<bool> used;
		bv_gauss_elim ge(m);
        for (unsigned i = 0; i < flas.size(); ++i) {
			const bool ir = ge.is_row(flas[i]);
			used.push_back(ir);
			if (!ir) continue;
			ge.add_row(flas[i]);
        }
		ge.elim();

		goal_ref resg(alloc(goal, *g, true));
        if (!ge.is_consistent()) {
			resg->assert_expr(m.mk_false());
        } else {
			expr_ref tmp(m);
            unsigned row_idx = 0;
            for (unsigned i = 0; i < flas.size(); ++i) {
				if (!used[i]) {
					resg->assert_expr(flas[i]);
					continue;
				}
                SASSERT(row_idx < ge.row_count());
				ge.output(row_idx, tmp);
                ++row_idx;
				if (m.is_true(tmp)) continue;
				resg->assert_expr(tmp);
            }
        }

		resg->inc_depth();
		SASSERT(resg->is_well_sorted());
		result.push_back(resg.get());
		tactic_report report("bv-gauss-elim", *resg);
        TRACE("after_bv_gauss_elim", resg->display(tout););
    }

};

bv_gauss_elim_tactic::bv_gauss_elim_tactic(ast_manager & m) {
    m_imp = alloc(imp, m);
}

bv_gauss_elim_tactic::~bv_gauss_elim_tactic() {
    dealloc(m_imp);
}

void bv_gauss_elim_tactic::operator()(goal_ref const & g,
                                      goal_ref_buffer & result,
                                      model_converter_ref & mc,
                                      proof_converter_ref & pc,
                                      expr_dependency_ref & core) {
    SASSERT(g->is_well_sorted());
    fail_if_proof_generation("bv-gauss-elim", g);
    fail_if_unsat_core_generation("bv-gauss-elim", g);
    mc = 0; pc = 0; core = 0; result.reset();
    m_imp->operator()(g, result, mc);
}

void bv_gauss_elim_tactic::cleanup() {
    imp * d = alloc(imp, m_imp->m_m);
    std::swap(d, m_imp);
    dealloc(d);
}
