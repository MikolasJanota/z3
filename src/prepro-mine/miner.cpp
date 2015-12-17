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

struct miner::imp {
    ast_manager&                   m_m;
    model_ref                      m_assignment;
    scoped_ptr<model_evaluator>    m_evaluator;

    imp(ast_manager & m)
        :m_m(m)
    {}

    void operator()(expr_ref f) {
        decl_collector collector(m_m, false);
        collector.visit(f.get());
        for (unsigned i = 0; i < collector.get_num_sorts(); ++i) {
            if (((collector.get_sorts())[i])->get_family_id() == null_family_id) UNREACHABLE();
        }
        assignment_maker am(m_m);
        m_assignment = alloc(model, m_m);
        am(collector.get_num_decls(), collector.get_func_decls(), m_assignment);
        m_evaluator = alloc(model_evaluator, *(m_assignment.get()));
        traverse(f);
    }

    inline bool is_val(const expr * e) {
        if (!is_app(e)) return false;
        return is_val_ap(to_app(e));
    }

    inline bool is_val_ap(const app * a) const {
        const family_id fid = a->get_decl()->get_family_id();
        const bool rv = fid != null_family_id && a->get_num_args() == 0;
        return rv;
    }

    bool test_term(app * term) {
        if (term->get_depth() > 5) return false; //TODO: introduce a parameter
        if (is_val_ap(term)) return false;
        expr_ref value(m_m);
        (*m_evaluator)(term, value);
        SASSERT(is_val(value.get()));
        expr_ref eq(m_m.mk_eq(term, value), m_m);
        const lbool t = is_tautology(eq);
        if (t != l_true) return false;
        std::cout << "const: " << mk_ismt2_pp(term, m_m, 2) << "->" <<
            mk_ismt2_pp(value, m_m, 2) << "\n";
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
                            test_term(a);
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

    lbool decide(expr_ref e) {
        tactic_ref t = mk_qfaufbv_tactic(m_m);
        scoped_ptr<solver> sat = mk_tactic2solver(m_m, t.get());
        sat->assert_expr(e);
        return sat->check_sat(0, 0);
    }
};

miner::miner(ast_manager& m) : m_imp(alloc(imp, m)) {}
void miner::operator() (expr_ref f) { m_imp->operator() (f); }
miner::~miner() { if (m_imp) dealloc(m_imp); }
