/*++
 Copyright (c) 2016 Microsoft Corporation

 Module Name:

  propagate_antecedent.cpp

 Abstract:


 Author:

 Mikolas Janota (MikolasJanota)

 Revision History:
--*/
#include "push_antecedent.h"
#include "expr_replacer.h"
#include "ast_util.h"
#include "ast_pp.h"

using namespace qe;

class propagate_antecedent::impl {
    ast_manager& m;
public:
    impl(ast_manager& m) : m(m) {}
    ~impl() {}

    bool operator () (expr * src, expr_ref& dst) {
        const bool retv = run(src, dst);
        TRACE("propagate_antecedent", tout << mk_pp(src, m, 2) << "\n--->\n"; 
                                      if (retv) tout << mk_pp(dst.get(), m, 2) << "\n";
                                      else tout << "\n unchanged\n"; );
        return retv;
    }

    bool run(expr * src, expr_ref& dst) {
        expr *lhs, *rhs;
        dst = src;
        if (!m.is_implies(src, lhs, rhs)) return false;
        expr_ref_vector dom(m);
        expr_ref_vector rng(m);
        if (!find_defs(lhs, dom, rng)) return false;
        expr_ref new_rhs(rhs, m);
        apply_defs(rhs, dom, rng, new_rhs);
        dst = m.mk_implies(lhs, new_rhs.get());
        return true;
    }

    bool is_def(expr * e, app_ref& v, expr_ref& t) {
        expr *lhs, *rhs;
        if (!m.is_eq(e, lhs, rhs)) return false;
        if (is_uninterp_const(rhs)) std::swap(lhs, rhs);
        if (!is_uninterp_const(lhs))  return false;
        if ((contains_app(m, to_app(lhs)))(rhs)) return false;
        v = to_app(lhs);
        t = rhs;
        return true;
    }

    bool find_defs(expr * lhs, expr_ref_vector& dom, expr_ref_vector& rng) {
        expr_ref_vector conjuncts(m);
        flatten_and(lhs, conjuncts);
        app_ref v(m);
        expr_ref t(m);
        for (unsigned i = 0; i < conjuncts.size(); ++i) {
            if (!is_def(conjuncts.get(i), v, t)) continue;
            dom.push_back(v);
            rng.push_back(t);
        }
        return !dom.empty();
    }

    bool apply_defs(expr * e, expr_ref_vector& dom, expr_ref_vector& rng, expr_ref& out) {
        const unsigned sz = dom.size();
        SASSERT(rng.size() == sz);
        expr_ref tmp(m);
        out = e;
        for (unsigned i = 0; i < sz; ++i) {
            expr_substitution subst(m);
            subst.insert(dom.get(i), rng.get(i));
            scoped_ptr<expr_replacer> er = mk_default_expr_replacer(m);
            er->set_substitution(&subst);
            (*er)(out.get(), tmp);
            out = tmp;
        }
        return true;
    }
};

propagate_antecedent::propagate_antecedent(ast_manager& m) {
    m_impl = alloc(impl, m);
}

propagate_antecedent::~propagate_antecedent() {
    dealloc(m_impl);
}

bool propagate_antecedent::operator()(expr * src, expr_ref& dst) {
    return (*m_impl)(src, dst);
}
