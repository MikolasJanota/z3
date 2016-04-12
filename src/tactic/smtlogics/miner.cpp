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
#include"model_pp.h"
#include"tactic2solver.h"
#include"qfaufbv_tactic.h"
#include"tactic.h"
#include"solver.h"
#include"expr_gen.h"
#include"for_each_ast.h"
#include"th_rewriter.h"

//#define __PL std::cout << __FILE__ << ":" << __LINE__ << "\n";
//#define __PL tout << __FILE__ << ":" << __LINE__ << "\n";

class expr_collector {
    ast_manager&                   m_m;
    sort * const                   m_esort;
    ast *   const                  m_n;
    expr_ref_vector                m_collected;
public:
    expr_collector(ast_manager& m,
        sort * esort,
        ast * n)
        : m_m(m)
        , m_esort(esort)
        , m_n(n)
        , m_collected(m)
       , m_exact(false)
    {}

    bool m_exact;
    void set_exact(bool e) { m_exact = e; }

    expr_ref_vector&   collected() {
        return m_collected;
    }

    void visit() {
        ptr_vector<ast> todo;
        ast_mark visited;
        todo.push_back(m_n);
        while (!todo.empty()) {
            ast * const n = todo.back();
            todo.pop_back();
            if (!visited.is_marked(n)) {
                visited.mark(n, true);
                switch (n->get_kind()) {
                case AST_APP: {
                    app * a = to_app(n);
                    sort * as =  a->get_decl()->get_range();
                    const bool p = m_exact ? as == m_esort : as->get_family_id()==m_esort->get_family_id();
                    if (p) m_collected.push_back(a);
                    for (unsigned i = 0; i < a->get_num_args(); ++i) {
                        todo.push_back(a->get_arg(i));
                    }
                    break;
                }
                case AST_QUANTIFIER: {
                    quantifier * q = to_quantifier(n);
                    todo.push_back(q->get_expr());
                    break;
                }
                case AST_VAR:
                    break;
                default:
                    UNREACHABLE();
                }
            }
        }
    }
};

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

    void mine_term_bf(app * term);
    void mine_term(app * term);

    void make_values(app* a, expr_ref_vector& a_values) {
        a_values.reset();
        expr_ref tmp(m_m);
        for (unsigned i = 0; i < m_evaluators.size(); i++) {
            m_evaluators[i]->operator() (a, tmp);
            a_values.push_back(tmp);
        }
    }

    lbool check_equality(app * a, expr_ref_vector& a_values, expr_ref& e) {
        const lbool retv = check_equality_core(a, a_values, e);
        TRACE("miner", tout << "check_eq: "
                << mk_ismt2_pp(a, m_m, 2)
                << " = "
                << mk_ismt2_pp(e.get(), m_m, 2)
                << ":" << retv << std::endl;);
        return retv;
    }

    lbool check_equality_core(app * a, expr_ref_vector& a_values, expr_ref& e) {
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
        return is_tautology(eq);
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
        for (unsigned i = 0; i < 10; ++i) {
            assignment_maker::gen_mode m =
                i == 0 ? assignment_maker::ZERO
                : (i == 1 ? assignment_maker::ONE
                          : assignment_maker::RANDOM);
          am.set_mode(m);
          model_ref a(alloc(model, m_m));
          am(size, declarations, a);
          TRACE("miner", model_pp(tout << "test assignment:", *(a.get())); tout << std::endl;);
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
        if (is_sat(query) != l_false) return false;
        --h;
        while (l < h) {
            std::cout << mk_ismt2_pp(term, m_m, 2) << " lh:" << l << " " << h << "\n";
            const rational mid_v = l + ceil((h - l) / rational(2));
            //std::cout << "mid_v:" << mid_v << "\n";
            mid_e = m_bv_util.mk_numeral(mid_v, bv_sz);
            query = m_bv_util.mk_ule(mid_e.get(), term);
            const lbool t = is_sat(query);
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
		if (is_sat(query) != l_false) return false;
		++l;
		while (l < h) {
			std::cout << mk_ismt2_pp(term, m_m, 2) << " lh:" << l << " " << h << "\n";
			const rational mid_v = l + floor((h - l) / rational(2));
			//std::cout << "mid_v:" << mid_v << "\n";
			mid_e = m_bv_util.mk_numeral(mid_v, bv_sz);
			query = m_bv_util.mk_ule(term, mid_e.get());
			const lbool t = is_sat(query);
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
                            //mine_term_bf(a);
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
        std::cerr << '+';
        TRACE("miner", tout << "sat call" << mk_ismt2_pp(e, m_m, 2) << std::endl;);
        const lbool dv = is_sat(n);
        std::cerr << '-';
        if (dv == l_undef) return l_undef;
        if (dv == l_false) return l_true;
        SASSERT(dv == l_true);
        return l_false;
    }

    lbool is_sat(expr_ref& e) {
        tactic_ref t = mk_qfaufbv_tactic(m_m);
        scoped_ptr<solver> sat = mk_tactic2solver(m_m, t.get());
        sat->assert_expr(e);
        return sat->check_sat(0, 0);
    }


    bool test_conc_preffix(
        rational term_val0, unsigned term_sz,
        expr_ref sub_e, rational sub_val0, unsigned sub_sz,
        /*out*/expr_ref& tested_expression) {
        TRACE("miner", tout << "szs: " << term_sz << ":" << sub_sz << std::endl;);
        if (term_sz <= sub_sz) return false;
        const rational two(2);
        const rational one(rational::one());
        const unsigned pref_sz = term_sz - sub_sz;
        rational pref(rational::zero());;
        for (unsigned i = 0; i < term_sz; ++i) {
            if (i >= sub_sz && !term_val0.is_even())
                pref += rational::power_of_two(i);
            term_val0 = div(term_val0, two);
        }
        expr * const n = m_bv_util.mk_numeral(pref, pref_sz);
        tested_expression = m_bv_util.mk_concat(n, sub_e);
        return true;
    }


    bool test_conc_suffix(
            rational term_val0, unsigned term_sz,
            expr_ref sub_e, rational sub_val0, unsigned sub_sz,
            /*out*/expr_ref& tested_expression) {
        TRACE("miner", tout << "szs: " << term_sz << ":" << sub_sz <<std::endl;);
        if (term_sz <= sub_sz) return false;
        const rational two(2);
        const rational one(rational::one());
        const unsigned suff_sz = term_sz - sub_sz;
        rational suff(rational::zero());;
        for (unsigned i = 0; i < suff_sz; ++i) {
            if (!term_val0.is_even())
                suff += rational::power_of_two(i);
            term_val0 = div(term_val0, two);
        }
        expr * const n = m_bv_util.mk_numeral(suff, suff_sz);
        tested_expression = m_bv_util.mk_concat(sub_e, n);
        return true;
    }

    bool test_add_correction(
            rational& term_val0, unsigned term_sz,
            expr_ref& sub_e, rational& sub_val0, unsigned sub_sz,
            /*out*/expr_ref& tested_expression) {
        if (term_sz != sub_sz) return false;
        if (term_val0 == sub_val0) return false;
        const rational mod  = rational::power_of_two(sub_sz);
        const rational correction_value = (term_val0 >= sub_val0) ?
            term_val0 - sub_val0 : term_val0  + mod - sub_val0;
        SASSERT(correction_value > rational::zero() && correction_value <= mod);
        expr * const n = m_bv_util.mk_numeral(correction_value, term_sz);
        tested_expression = m_bv_util.mk_bv_add(n, sub_e);
        return true;
    }

    void get_val0(expr* e, /*out*/rational& val0, /*out*/unsigned& sz) {
        expr_ref eval0(m_m);
        (*m_evaluators[0])(e, eval0);
        const bool isn = m_bv_util.is_numeral(eval0, val0, sz);
        SASSERT(isn);
        if (!isn) UNREACHABLE();
    }
};


void miner::imp::mine_term_bf(app * term) {
    if (term->get_depth() > 5) return; //TODO: introduce a parameter
    if (is_val(term)) return;
    if (term->get_num_args() == 0) return;
    if (!m_bv_util.is_bv(term)) return;// for now only check bit vectors
    const unsigned term_size = get_num_nodes(term);
    if (term_size <= 3) return;

    expr_collector  collector(m_m, term->get_decl()->get_range(), term);
    collector.set_exact(true);
    collector.visit();
    const unsigned bv_sz = m_bv_util.get_bv_size(term);
    expr_ref_vector exprs = collector.collected();
    unsigned i = 0;
    while (i < exprs.size()) {
        expr * e = exprs.get(i);
        const unsigned e_sz = m_bv_util.get_bv_size(e);
        const bool del = !is_app(e) || to_app(e)->get_num_args() || e_sz != bv_sz;
        if (del) {
            exprs[i] = exprs.back();
            exprs.pop_back();
        }
        else {
            ++i;
        }
    }
    if (exprs.empty()) return;

    expr_ref_vector term_values(m_m);
    make_values(term, term_values);

	
    bool done = false;
    const unsigned B = 20;
    expr_ref tested_expression(m_m);
    unsigned min_size = term_size;
    TRACE("miner", tout << "mining: " << mk_ismt2_pp(term, m_m, 2) << "(" << term_size << ")" << std::endl;);
    std::cout << "mining: " << mk_ismt2_pp(term, m_m, 2) << "(" << term_size << ")" << std::endl;
    th_rewriter tr(m_m);
    expr_gen* eg = mk_expr_gen(m_m, 3, bv_sz, exprs);
    unsigned itc = 0;
    while (!done) {        
        const bool s = eg->gen(tested_expression);
        unsigned budget = min_size / 2;
        done = (eg->inc(budget));
        if(done) break;

        if (m_m.are_equal(tested_expression.get(), term)) continue;
        //tr(tested_expression);
        const unsigned   tested_size = get_num_nodes(tested_expression.get());
        //std::cout << "sz: " << term_size << "  " << tested_size << " "  << min_size<< std::endl;
        if (min_size <= tested_size)  continue;
        TRACE("miner", tout << "testing: " << mk_ismt2_pp(tested_expression.get(), m_m, 2) << "(" <<  tested_size <<  ")" << std::endl;);
        if (check_equality(term, term_values, tested_expression) == l_true) {
            std::cout << "cost: " << term_size << " -> " <<tested_size << std::endl;
            min_size = tested_size;
            if (m_print) std::cout << "rewrite: "
                << mk_ismt2_pp(term, m_m, 2) << "->"
                    << mk_ismt2_pp(tested_expression, m_m, 2)
                    << std::endl;
        }
        if (itc++ > 10000) done = true;
    }
    dealloc(eg);
}

void miner::imp::mine_term(app * term) {
    SASSERT(term);
    if (term->get_depth() > 5) return; //TODO: introduce a parameter
    if (is_val(term)) return;
    if (term->get_num_args() == 0) return;
    TRACE("miner", tout << "mining: " << mk_ismt2_pp(term, m_m, 2) << std::endl;);
    expr_ref constant_value(m_m);
    expr_ref_vector term_values(m_m);
    make_values(term, term_values);
    constant_value = term_values.get(0);
    TRACE("miner", tout << "testing constant: " << mk_ismt2_pp(constant_value.get(), m_m, 2) << std::endl;);
    if (check_equality(term, term_values, constant_value) == l_true) {
        if (m_print) std::cout << "const: " << mk_ismt2_pp(term, m_m, 2) << "->" << mk_ismt2_pp(constant_value, m_m, 2) << std::endl;
        TRACE("miner", tout << "const: " << mk_ismt2_pp(term, m_m, 2) << "->" << mk_ismt2_pp(constant_value, m_m, 2) << "\n";);
        return;
    }
    if (!m_bv_util.is_bv(term)) return;// for now only check bit vectors
    expr_collector  collector(m_m, term->get_decl()->get_range(), term);
    collector.set_exact(true);
    collector.visit();
    expr_ref_vector& exprs = collector.collected();
    const unsigned e_num = exprs.size();
    const rational zero = rational::zero();
    rational term_val0;
    unsigned term_sz;
    get_val0(term, term_val0, term_sz);
    for (unsigned i = 0; i < e_num; ++i) {
        expr_ref sub_e(exprs.get(i), m_m);
        TRACE("miner", tout << "sub_e: " << mk_ismt2_pp(sub_e.get(), m_m, 2) << std::endl;);
        rational sub_e_val0;
        unsigned sub_e_sz;
        get_val0(sub_e, sub_e_val0, sub_e_sz);
        for (int op = 0; op < 4; ++op) {
            TRACE("miner", tout << "op: " << op << std::endl;);
            expr_ref tested_expression(m_m);
            switch (op) {
            case 0:
                if (term_val0 != sub_e_val0) continue;
                tested_expression = sub_e;
                break;
            case 1:
                if (!test_add_correction(term_val0, term_sz,
                    sub_e, sub_e_val0, sub_e_sz,
                    tested_expression)) continue;
                break;
            case 2:
                if (!test_conc_suffix(term_val0, term_sz,
                    sub_e, sub_e_val0, sub_e_sz,
                    tested_expression)) continue;
                break;
            case 3:
                if (!test_conc_preffix(term_val0, term_sz,
                    sub_e, sub_e_val0, sub_e_sz,
                    tested_expression)) continue;
                break;
            }
            SASSERT(tested_expression.get());
            if (tested_expression.get() == term) continue;
            TRACE("miner", tout << "testing: " << mk_ismt2_pp(tested_expression.get(), m_m, 2) << std::endl;);
            if (check_equality(term, term_values, tested_expression) == l_true) {
                if (m_print) std::cout << "rewrite(" << op << "): "
                    << mk_ismt2_pp(term, m_m, 2) << "->"
                    << mk_ismt2_pp(tested_expression, m_m, 2)
                    << std::endl;
            }
        }
    }
}

miner::miner(ast_manager& m) : m_imp(alloc(imp, m)) {}
void miner::operator() (expr_ref f) { m_imp->operator() (f); }
void miner::init(expr_ref f) { m_imp->init(f); }

bool miner::test_term(app * term, expr_ref& value) {
    return m_imp->test_term(term, value);
}

bool miner::test_term(expr * term) {
    if (!is_app(term)) return false;
    ast_manager m(m_imp->m_m);
    expr_ref value(m);
    m_imp->m_print = true;
    return test_term(to_app(term), value);
}


miner::~miner() { if (m_imp) dealloc(m_imp); }
