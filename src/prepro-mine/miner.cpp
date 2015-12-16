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
#include "decl_collector.h"

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
        am(collector.get_num_decls(),
            collector.get_func_decls(),
            m_assignment);
        m_evaluator = alloc(model_evaluator, *(m_assignment.get()));
        traverse(f);
    }

    bool test_term(expr * term) {
        return false;
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
                    if (for_each_expr_args(stack, visited,
                                to_app(curr)->get_num_args(), to_app(curr)->get_args())) {
                        visited.mark(curr, true);
                        stack.pop_back();
                        test_term(to_app(curr));
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
};

miner::miner(ast_manager& m) : m_imp(alloc(imp, m)) {}
void miner::operator() (expr_ref f) { m_imp->operator() (f); }