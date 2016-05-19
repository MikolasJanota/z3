/*++
 Copyright (c) 2016 Microsoft Corporation

 Module Name:

  ctx_bv_gauss_elim.cpp

 Abstract:


 Author:

 Mikolas Janota

 Revision History:
--*/
#include "bv_bounds_tactic.h"
#include "ctx_simplify_tactic.h"
#include "bv_decl_plugin.h"
#include "ast_pp.h"
#include"bv_gauss_elim.h"

class ctx_bv_gauss_elim : public ctx_simplify_tactic::simplifier {
    typedef obj_map<expr, bool> expr_set;
    typedef obj_map<expr, unsigned> expr_cnt;

    ast_manager&       m_m;
    params_ref         m_params;
    bool               m_propagate_eq;
    bv_util            m_bv;
    svector<expr_set*> m_expr_vars;
    svector<expr_cnt*> m_bound_exprs;
    bv_gauss_elim*     m_ge;

    expr_set* get_expr_vars(expr* t) {
        unsigned id = t->get_id();
        m_expr_vars.reserve(id + 1);
        expr_set*& entry = m_expr_vars[id];
        if (entry)
            return entry;

        expr_set* set = alloc(expr_set);
        entry = set;

        if (!m_bv.is_numeral(t))
            set->insert(t, true);

        if (!is_app(t))
            return set;

        app* a = to_app(t);
        for (unsigned i = 0; i < a->get_num_args(); ++i) {
            expr_set* set_arg = get_expr_vars(a->get_arg(i));
            for (expr_set::iterator I = set_arg->begin(), E = set_arg->end(); I != E; ++I) {
                set->insert(I->m_key, true);
            }
        }
        return set;
    }

public:
    ctx_bv_gauss_elim(ast_manager& m, params_ref const& p) : m_m(m), m_params(p), m_bv(m) {
        updt_params(p);
        m_ge = alloc(bv_gauss_elim, m);
    }

    virtual void updt_params(params_ref const & p) {
        m_propagate_eq = p.get_bool("propagate_eq", false);
    }

    static void get_param_descrs(param_descrs& r) {
        r.insert("propagate-eq", CPK_BOOL, "(default: false) propagate equalities from inequalities");
    }

    virtual ~ctx_bv_gauss_elim() {
        dealloc(m_ge);

        for (unsigned i = 0, e = m_expr_vars.size(); i < e; ++i) {
            dealloc(m_expr_vars[i]);
        }
        for (unsigned i = 0, e = m_bound_exprs.size(); i < e; ++i) {
            dealloc(m_bound_exprs[i]);
        }
    }

    virtual bool assert_expr(expr * t, bool sign) {
        //if (sign) return false;
        
        if (m_ge->is_row(t)) {
            std::cout << (sign ? "not " : "") << "row: " << mk_pp(t, m_m) << std::endl;
        }
        return false;
    }

    virtual bool simplify(expr* t, expr_ref& result) {
        return false;
    }

    virtual bool may_simplify(expr* t) {
        return true;
    }

    virtual void pop(unsigned num_scopes) {
        std::cerr << "pop" << std::endl;
        dealloc(m_ge);
        m_ge = alloc(bv_gauss_elim, m_m);
    }

    virtual simplifier * translate(ast_manager & m) {
        return alloc(ctx_bv_gauss_elim, m, m_params);
    }

    virtual unsigned scope_level() const {
        return 0;
    }
};

tactic * mk_ctx_bv_gauss_elim_tactic(ast_manager & m, params_ref const & p ) {
    return clean(alloc(ctx_simplify_tactic, m, alloc(ctx_bv_gauss_elim, m, p), p));
}
