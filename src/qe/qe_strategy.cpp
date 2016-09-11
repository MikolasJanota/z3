/*++
 Copyright (c) 2016 Microsoft Corporation

 Module Name:

  qe_strategy.cpp

 Abstract:


 Author:

 Mikolas Janota (MikolasJanota)

 Revision History:
--*/
#include"qe_strategy.h"
#include"qe_mbp.h"
#include"model_smt2_pp.h"
#include"ast_pp.h"
#include"th_rewriter.h"
#include"expr_safe_replace.h"
#include"expr_functors.h"
#include"obj_pair_hashtable.h"
//using namespace qe;
using namespace qe::rareqs;

struct strategy_maker {
    strategy_maker(th_rewriter& rw)
        : m_rw(rw), m_dom(rw.m()), m_rng(rw.m()), m_sub(rw.m())  {}
    expr_ref_vector m_dom;
    expr_ref_vector m_rng;
    expr_mark       m_is_def;
    expr_mark       m_can_def;
    expr_safe_replace m_sub;

    th_rewriter&    m_rw;

    bool is_defined(expr *  v) const {
         return m_is_def.is_marked(v);
    }

    bool can_def(expr *  v) const {
        return m_can_def.is_marked(v) && !is_defined(v);
    }

    void add_definable(expr * v) {
        m_can_def.mark(v);
    }

    void add(const expr_ref& v, const expr_ref& t) {
        ast_manager& m = m_dom.m();
        TRACE("qe", tout << "set def: \n" << mk_pp(v, m, 2) << "\n" << mk_pp(t.get(), m, 2) << "\n" ;);
        expr_safe_replace sub(m);
        sub.insert(v, t);
        expr_ref tmp(m);
        for (unsigned di = 0; di < m_rng.size(); ++di) {
            sub(m_rng.get(di), tmp);
            m_rw(tmp);
            m_rng[di] = tmp;
        }
        m_dom.push_back(v);
        m_rng.push_back(t);
        m_is_def.mark(v.get());
        m_sub.insert(v, t);
    }

    void sub(expr * v, expr_ref& e) {
        m_sub(v, e);
    }

    void mk(expr_substitution& strategy) {
        SASSERT(m_rng.size() == m_dom.size());
        for (unsigned di = 0; di < m_rng.size(); ++di) {
            strategy.insert(m_dom.get(di), m_rng.get(di));
        }
    }
};

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

        strategy_maker st_mk(m_rw);
        for (unsigned i = 0; i < vars.size(); ++i)
            st_mk.add_definable(vars.get(i));
        if (vars.size()) {
            reduce_equalities(mdl, lits, st_mk);
        }

        expr_ref val(vars.m());
        for (unsigned i = 0; i < vars.size(); ++i) {
            expr_ref v(vars.get(i), m);
            if (st_mk.is_defined(v)) continue;
            mdl.eval(v, val, true);
            st_mk.add(v, val);
        }

        st_mk.mk(strategy);
        //if (reduced)
        //filter(is_rem, vars);

        TRACE("qe", prn_strategy(tout << "mk_strategy out:\n", vars, strategy) << "\n";);
    }

    ~impl() {
    }


    bool reduce_equalities(model& mdl, expr_ref_vector& lits, /*in/out*/strategy_maker& st_mk) {
//        TRACE("qe", tout << "reduce_equalities in: " << "vars: " << vars << "\nlits: \n" << lits << "\n";
  //                  model_smt2_pp(tout << "mdl\n", m, mdl, 2); tout << "\n";);
        bool reduced = false;

        expr_ref tmp(m), t(m), v(m);
        for (unsigned i = 0; i < lits.size(); ++i) {
            expr* const e = lits[i].get();
            expr *l, *r;
            if (!m.is_eq(e, l, r) || !mk_eq(l, r, st_mk))
                continue;
            reduced = true;
            project_plugin::erase(lits, i);
            for (unsigned j = 0; j < lits.size(); ++j) {
                st_mk.sub(lits[j].get(), tmp);
                m_rw(tmp);
                lits[j] = tmp;
            }
        }
        return reduced;
    }

    typedef std::pair<expr*, expr*> epair;

    bool mk_eq(expr* top_l, expr* top_r, strategy_maker& st_mk) {
        vector<epair> todo;
        todo.push_back(std::make_pair(top_l, top_r));
        expr_ref v(m), t(m);
        obj_pair_hashtable<expr, expr> mark;
        bool retv = true;
        while (todo.size() && retv) {
            const epair ep = todo.back();
            expr * const l = ep.first;
            expr * const r = ep.second;
            TRACE("qe", tout << "mk_eq: \n" << mk_pp(l, m, 2) << "\n" << mk_pp(r, m, 2) << "\n";);

            todo.pop_back();
            if (mark.contains(ep)) continue;
            mark.insert(ep);
            if (m.are_equal(l, r)) continue;
            if (reduce_eq(st_mk, l, r, v, t)) {
                st_mk.add(v, t);
                continue;
            }
            if (!is_app(l) || !is_app(r)) {
                retv = false;
                continue;
            }
            app * const la = to_app(l);
            app * const ra = to_app(r);
            if (la->get_kind() != ra->get_kind() || la->get_num_args() != ra->get_num_args()) {
                retv = false;
                continue;
            }
            for (unsigned i = 0; i < ra->get_num_args(); ++i)
                todo.push_back(std::make_pair(la->get_arg(i), ra->get_arg(i)));
        }
        TRACE("qe", tout << "mk_eq result: " << (retv ? "true" : "false") << "\n";);
        return retv;
    }

    bool reduce_eq(strategy_maker& st_mk, expr* l, expr* r, expr_ref& v, expr_ref& t) {
        if (st_mk.can_def(r)) {
            std::swap(l, r);
        }
        if (st_mk.can_def(l)) {
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
