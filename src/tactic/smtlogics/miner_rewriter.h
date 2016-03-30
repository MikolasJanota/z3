 /*++
 Copyright (c) 2015 Microsoft Corporation

 Module Name:

  miner_rewriter.h

 Abstract:


 Author:

 Mikolas Janota

 Revision History:
 --*/
#ifndef MINER_REWRITER_H_21748
#define MINER_REWRITER_H_21748
#include"ast.h"
#include"rewriter_types.h"
#include"params.h"
class miner_rewriter {
    struct imp;
    imp *  m_imp;
public:
    miner_rewriter(ast_manager& m, params_ref const & p = params_ref());
    ~miner_rewriter();

    void updt_params(params_ref const & p);

    void operator()(expr * t, expr_ref & r);
};
#endif /* MINER_REWRITER_H_21748 */
