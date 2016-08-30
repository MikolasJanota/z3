/*++
 Copyright (c) 2016 Microsoft Corporation

 Module Name:

  qe_strategy.cpp

 Abstract:


 Author:

 Mikolas Janota (MikolasJanota)

 Revision History:
--*/
#include "qe_strategy.h"
#include "qe_mbp.h"
#include "model_smt2_pp.h"
#include "ast_pp.h"
#include "th_rewriter.h"
#include "expr_safe_replace.h"
#include "expr_functors.h"
//using namespace qe;
using namespace qe::rareqs;

std::ostream& qe::rareqs::prn_strategy(std::ostream& o,
    app_ref_vector const& vars, expr_substitution& strategy) {
    expr *  def;
    proof * pr;
    ast_manager& m = vars.m();
    o << "[";
    for (unsigned i = 0; i < vars.size(); ++i) {
        app * const v = vars.get(i);
        VERIFY(strategy.find(v, def, pr));
        if (i) o << ",";
        o << mk_pp(v, m) << "--->" << mk_pp(def, m) << '\n';
    }
    return o << "]";
}

unsigned filter(const expr_mark& to_remove, app_ref_vector& vars) {
    unsigned j = 0;
    for (unsigned i = 0; i < vars.size(); ++i) {
        if (to_remove.is_marked(vars[i].get())) continue;
        if (i != j) vars[j] = vars[i].get();
        ++j;
    }
    return j;
}


class mk_strategy::impl {
    ast_manager& m;
    th_rewriter m_rw;
public:
    impl(ast_manager& m):m(m), m_rw(m) { }

    void operator()(app_ref_vector const& vars, model & mdl, expr_ref const & fml,
            /*out*/expr_substitution& strategy) {
        TRACE("qe",
            tout << "mk_strategy in: " << vars << "\n" << mk_pp(fml, m) << "\n";
            model_smt2_pp(tout << "model\n", m, mdl, 2); tout << "\n";
            );


        mbp aux(m);
        expr_ref_vector lits(m);
        lits.push_back(fml);
        aux.extract_literals(mdl, lits);

        expr_ref_vector defs_dom(m);
        expr_ref_vector defs_rng(m);
        expr_mark is_rem;
        reduce_equalities(mdl, vars, lits, defs_dom, defs_rng, is_rem);

        expr_ref val(vars.m());
        for (unsigned i = 0; i < vars.size(); ++i) {
            expr_ref v(vars.get(i), m);
            if (is_rem.is_marked(v)) continue;
            mdl.eval(v, val, true);
            add_to_strategy(v, val, defs_dom, defs_rng);
        }

        for (unsigned di = 0; di < defs_rng.size(); ++di) {
            strategy.insert(defs_dom.get(di), defs_rng.get(di));
        }
        //if (reduced)
        //filter(is_rem, vars);

        TRACE("qe", prn_strategy(tout << "mk_strategy out:\n", vars, strategy) << "\n";);
    }

    ~impl() {
    }

    void add_to_strategy(const expr_ref& v, const expr_ref& t,
            /*out*/expr_ref_vector& defs_dom, /*out*/expr_ref_vector& defs_rng) {
        expr_safe_replace sub(m);
        sub.insert(v, t);
        expr_ref tmp(m);
        for (unsigned di = 0; di < defs_rng.size(); ++di) {
            sub(defs_rng.get(di), tmp);
            m_rw(tmp);
            defs_rng[di] = tmp;
        }
        defs_dom.push_back(v);
        defs_rng.push_back(t);
    }

    bool reduce_equalities(model& mdl, app_ref_vector const& vars, expr_ref_vector& lits,
        /*out*/expr_ref_vector& defs_dom, /*out*/expr_ref_vector& defs_rng,
        /*out*/expr_mark& is_rem) {
        TRACE("qe", tout << "reduce_equalities in: " << "vars: " << vars << "\nlits: \n" << lits << "\n";
                    model_smt2_pp(tout << "mdl\n", m, mdl, 2); tout << "\n";);
        expr_mark is_var;
        if (vars.empty())
            return false;
        bool reduced = false;
        for (unsigned i = 0; i < vars.size(); ++i)
            is_var.mark(vars.get(i));

        expr_ref tmp(m), t(m), v(m);
        for (unsigned i = 0; i < lits.size(); ++i) {
            expr* const e = lits[i].get();
            expr *l, *r;
            if (!m.is_eq(e, l, r) || !reduce_eq(is_var, l, r, v, t))
                continue;
            reduced = true;
            project_plugin::erase(lits, i);
            add_to_strategy(v, t, defs_dom, defs_rng);
            is_rem.mark(v);
            expr_safe_replace sub(m);
            sub.insert(v, t);
            for (unsigned j = 0; j < lits.size(); ++j) {
                sub(lits[j].get(), tmp);
                m_rw(tmp);
                lits[j] = tmp;
            }
        }
        return reduced;
    }

    bool reduce_eq(expr_mark& is_var, expr* l, expr* r, expr_ref& v, expr_ref& t) {
        if (is_var.is_marked(r)) {
            std::swap(l, r);
        }
        if (is_var.is_marked(l)) {
            contains_app cont(m, to_app(l));
            if (!cont(r)) {
                v = to_app(l);
                t = r;
                TRACE("qe", tout << "eq: " << mk_pp(l, m) << " := " << t << "\n";);
                return true;
            }
        }
        return false;
    }

};

mk_strategy::mk_strategy(ast_manager& m) {
    m_impl = alloc(impl, m);
}

mk_strategy::~mk_strategy() {
    dealloc(m_impl);
}

void mk_strategy::operator()(app_ref_vector const & vars, model& mdl, expr_ref const & fml,
                /*out*/expr_substitution& strategy) {
    (*m_impl)(vars, mdl, fml, strategy);
}
