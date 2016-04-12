 /*++
 Copyright (c) 2016 Microsoft Corporation

 Module Name:

  expr_gen.h

 Abstract:


 Author:

 Mikolas Janota (MikolasJanota)

 Revision History:
 --*/
#ifndef EXPR_GEN_H_
#define EXPR_GEN_H_
#include"ast.h"
class expr_gen {
public:
    virtual bool inc(unsigned & budget) = 0;
    virtual bool gen(expr_ref& out) = 0;
};

expr_gen * mk_expr_gen(ast_manager& m, unsigned limit, unsigned sz, expr_ref_vector& leafs);
void test_expr_gen(ast_manager& m);
#endif /* EXPR_GEN_H_ */
