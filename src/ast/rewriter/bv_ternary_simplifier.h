 /*++
 Copyright (c) 2016 Microsoft Corporation

 Module Name:

  bv_ternary_simplifier.h

 Abstract:


 Author:

 Mikolas Janota (MikolasJanota)

 Revision History:
 --*/
#ifndef BV_TERNARY_SIMPLIFIER_H_
#define BV_TERNARY_SIMPLIFIER_H_

#include"ast.h"
#include"params.h"

class bv_ternary_simplifier {
    struct     imp;
    imp *      m_imp;
    params_ref m_params;
public:
    bv_ternary_simplifier(ast_manager & m, params_ref const & p = params_ref());
    ~bv_ternary_simplifier();

    ast_manager & m() const;

    void updt_params(params_ref const & p);
    static void get_param_descrs(param_descrs & r);
    unsigned get_cache_size() const;
    unsigned get_num_steps() const;

    void operator()(expr_ref& term);
    void operator()(expr * t, expr_ref & result);
    void operator()(expr * t, expr_ref & result, proof_ref & result_pr);

    void cleanup();
    void reset();
};

#endif /* BV_TERNARY_SIMPLIFIER_H_ */
