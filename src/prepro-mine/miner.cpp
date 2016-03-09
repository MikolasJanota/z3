/*++
 Copyright (c) 2015 Microsoft Corporation

 Module Name:

  miner.cpp

 Abstract:


 Author:

 Mikolas Janota

 Revision History:
--*/
#include"miner.h"
#include"assignment_maker.h"
#include"for_each_expr.h"
#include"model_evaluator.h"
#include"decl_collector.h"
#include"lbool.h"
#include"ast_smt2_pp.h"
#include"tactic2solver.h"
#include"qfaufbv_tactic.h"
#include"tactic.h"
#include"solver.h"

#define __PL std::cout << __FILE__ << ":" << __LINE__ << "\n";

struct miner::imp {
    ast_manager&                   m_m;
    vector<model_ref>              m_assignments;
    ptr_vector<model_evaluator>    m_evaluators;
    decl_collector*                m_collector;
    bool                           m_print;
    bv_util                        m_bv_util;

    imp(ast_manager & m)
        : m_m(m)
        , m_collector(NULL)
        , m_print(false)
        , m_bv_util(m)
    {}

    ~imp() { cleanup(); }

    void operator() (expr_ref f) {
        TRACE("miner", tout << "mining: " << mk_ismt2_pp(f, m_m, 2) << std::endl;);
        const bool _print = m_print;
        m_print = true;
        init(f);
        traverse(f);
        m_print = _print;
    }

    void mine_term(app * term);

    void make_values(app* a, expr_ref_vector& a_values) {
        a_values.reset();
        expr_ref tmp(m_m);
        for (unsigned i = 0; i < m_evaluators.size(); i++) {
            m_evaluators[i]->operator() (a, tmp);
            a_values.push_back(tmp);
        }
    }

    lbool check_equality(app * a, expr_ref_vector& a_values,
        expr_ref& e) {
        SASSERT(a_values.size() == m_evaluators.size());
        SASSERT(is_app(e));
        if (!is_app(e)) return l_false;
        if (a->get_decl()->get_range() != to_app(e)->get_decl()->get_range())
            return l_false;
        expr_ref a_value(m_m);
        expr_ref tmp(m_m);
        for (unsigned i = 0; i < m_evaluators.size(); i++) {
            m_evaluators[i]->operator() (e, tmp);
            expr * const a_value = a_values.get(i);
            if (!m_m.are_equal(tmp.get(), a_value))
                return l_false;
        }
        expr_ref eq(m_m.mk_eq(a, e), m_m);
        return decide(eq);
    }

    void init(expr_ref& f) {
        cleanup();
        m_collector = alloc(decl_collector, m_m, false);
        m_collector->visit(f.get());
        init_models();
    }

    void cleanup() {
        m_assignments.reset();
        while (m_evaluators.size()) {
            dealloc(m_evaluators.back());
            m_evaluators.pop_back();
        }
        if (m_collector) {
            dealloc(m_collector);
            m_collector = NULL;
        }
    }

    void init_models() {
        for (unsigned i = 0; i < m_collector->get_num_sorts(); ++i) {//TODO: needed?
            if (((m_collector->get_sorts())[i])->get_family_id() == null_family_id)
                UNREACHABLE();
        }
        assignment_maker am(m_m);
        const unsigned size = m_collector->get_num_decls();
        func_decl * const * const declarations = m_collector->get_func_decls();
        for (unsigned i = 0; i < 2; ++i) {
          am.set_polarity(i & 1);
          model_ref a(alloc(model, m_m));
          am(size, declarations, a);
          m_assignments.push_back(a);
          m_evaluators.push_back(alloc(model_evaluator, *(a.get())));
        }
    }

    inline bool is_val(expr * a) const { return m_m.is_value(a); }

    bool find_upper_bound(app * term, rational& h) {
        SASSERT(term);
        if (term->get_depth() > 5) return false; //TODO: introduce a parameter
        if (is_val(term)) return false;
        if (!m_bv_util.is_bv(term)) return false;
        const unsigned bv_sz = m_bv_util.get_bv_size(term);
        const rational max = rational::power_of_two(bv_sz) - rational(1);
        h = max;
        rational l = rational(0);
        expr_ref mid_e(m_m);
        expr_ref query(m_m);
        query = m_m.mk_eq(term, m_bv_util.mk_numeral(h, bv_sz));
        if (decide(query) != l_false) return false;
        --h;
        while (l < h) {
            std::cout << mk_ismt2_pp(term, m_m, 2) << " lh:" << l << " " << h << "\n";
            const rational mid_v = l + ceil((h - l) / rational(2));
            //std::cout << "mid_v:" << mid_v << "\n";
            mid_e = m_bv_util.mk_numeral(mid_v, bv_sz);
            query = m_bv_util.mk_ule(mid_e.get(), term);
            const lbool t = decide(query);
            switch (t)
            {
            case l_true:  l = mid_v; break;
            case l_false: h = mid_v - rational(1); break;
            case l_undef: return false;
            default:
                UNREACHABLE();
                break;
            }
        }
        SASSERT(l == h);
        const bool interesting = h < max;
        if (m_print && interesting)
            std::cout << "ubound: " << mk_ismt2_pp(term, m_m, 2) << "->" << h << "\n";
        return interesting;
    }

	bool find_lower_bound(app * term, rational& l) {
		SASSERT(term);
		if (term->get_depth() > 5) return false; //TODO: introduce a parameter
		if (is_val(term)) return false;
		if (!m_bv_util.is_bv(term)) return false;
		const unsigned bv_sz = m_bv_util.get_bv_size(term);
		const rational max = rational::power_of_two(bv_sz) - rational(1);
		rational h = max;
		l = rational(0);
		expr_ref mid_e(m_m);
		expr_ref query(m_m);
		query = m_m.mk_eq(term, m_bv_util.mk_numeral(l, bv_sz));
		if (decide(query) != l_false) return false;
		++l;
		while (l < h) {
			std::cout << mk_ismt2_pp(term, m_m, 2) << " lh:" << l << " " << h << "\n";
			const rational mid_v = l + floor((h - l) / rational(2));
			//std::cout << "mid_v:" << mid_v << "\n";
			mid_e = m_bv_util.mk_numeral(mid_v, bv_sz);
			query = m_bv_util.mk_ule(term, mid_e.get());
			const lbool t = decide(query);
			switch (t)
			{
			case l_true:  h = mid_v; break;
			case l_false: l = mid_v + rational(1); break;
			case l_undef: return false;
			default:
				UNREACHABLE();
				break;
			}
		}
		SASSERT(l == h);
		const bool interesting = rational(0) < l;
		if (m_print && interesting)
			std::cout << "lbound: " << mk_ismt2_pp(term, m_m, 2) << "->" << l << "\n";
		return interesting;
	}


    bool test_term(app * term, expr_ref& value) {
        SASSERT(term);
        if (term->get_depth() > 5) return false; //TODO: introduce a parameter
        if (is_val(term)) return false;
        expr_ref value1(m_m);
        m_evaluators[0]->operator() (term, value);
        for (unsigned i = 1; i < m_evaluators.size(); i++) {
            m_evaluators[i]->operator() (term, value1);
            if (value != value1) return false;
        }
        SASSERT(is_val(value.get()));
        expr_ref eq(m_m.mk_eq(term, value), m_m);
        const lbool t = is_tautology(eq);
        if (t != l_true) return false;
        if(m_print) std::cout << "const: " << mk_ismt2_pp(term, m_m, 2) << "->" << mk_ismt2_pp(value, m_m, 2) << "\n";
        TRACE("miner", tout << "const: " << mk_ismt2_pp(term, m_m, 2) << "->" << mk_ismt2_pp(value, m_m, 2) << "\n";);
        return true;
    }

    void traverse(expr_ref f) {
        ptr_vector<expr> stack;
        expr *           curr;
        expr_mark        visited;
        stack.push_back(f.get());

        while (!stack.empty()) {
            curr = stack.back();
            if (visited.is_marked(curr)) {
                stack.pop_back();
                continue;
            }

            switch (curr->get_kind()) {
                case AST_VAR:
                    visited.mark(curr, true);
                    stack.pop_back();
                    break;

                case AST_APP:
                    {
                        app * const a = to_app(curr);
                        if (for_each_expr_args(stack, visited,
                                               a->get_num_args(), a->get_args())) {
                            visited.mark(a, true);
                            stack.pop_back();
                            mine_term(a);
                        }
                    }
                    break;
                case AST_QUANTIFIER:
                    break; // let's bailout now
                default:
                    UNREACHABLE();
            }
        }
        visited.reset();
    }

    lbool is_tautology(expr_ref e) {
        expr_ref n(m_m);
        n = m_m.mk_not(e);
        const lbool dv = decide(n);
        if (dv == l_undef) return l_undef;
        if (dv == l_false) return l_true;
        SASSERT(dv == l_true);
        return l_false;
    }

    lbool decide(expr_ref& e) {
        tactic_ref t = mk_qfaufbv_tactic(m_m);
        scoped_ptr<solver> sat = mk_tactic2solver(m_m, t.get());
        sat->assert_expr(e);
        return sat->check_sat(0, 0);
    }
};


void miner::imp::mine_term(app * term) {
    SASSERT(term);
    if (term->get_depth() > 5) return; //TODO: introduce a parameter
    if (is_val(term)) return;
    if (term->get_num_args() == 0) return;
    expr_ref  constant_value(m_m);
    expr_ref_vector term_values(m_m);
    make_values(term, term_values);
    constant_value = term_values.get(0);
    if (check_equality(term, term_values, constant_value) == l_true) {
        if (m_print) std::cout << "const: " << mk_ismt2_pp(term, m_m, 2) << "->" << mk_ismt2_pp(constant_value, m_m, 2) << std::endl;
        TRACE("miner", tout << "const: " << mk_ismt2_pp(term, m_m, 2) << "->" << mk_ismt2_pp(constant_value, m_m, 2) << "\n";);
        return;
    }
    decl_collector  collector(m_m, false);
    if (!m_bv_util.is_bv(term)) return;// for now only check bit vectors
    collector.visit(term);
    func_decl * const * const declarations = m_collector->get_func_decls();
    const unsigned decl_num = m_collector->get_num_decls();
    for (unsigned i = 0; i < decl_num; ++i) {
        func_decl * const declaration = declarations[i];
        expr_ref v(m_m.mk_const(declaration), m_m);
        if (check_equality(term, term_values, v) == l_true) {
            if (m_print) std::cout << "rewrite: "
                << mk_ismt2_pp(term, m_m, 2)
                << "->"
                << mk_ismt2_pp(v, m_m, 2)
                << std::endl;
        }
    }
}

miner::miner(ast_manager& m) : m_imp(alloc(imp, m)) {}
void miner::operator() (expr_ref f) { m_imp->operator() (f); }
void miner::init(expr_ref f) { m_imp->init(f); }

bool miner::test_term(app * term, expr_ref& value) {
    return m_imp->test_term(term, value);
}


miner::~miner() { if (m_imp) dealloc(m_imp); }
