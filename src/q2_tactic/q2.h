/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

q2.h

Abstract:

2 level quantification a la AReQS.

Author:

Mikolas Janota

Revision History:
--*/

#ifndef _Q2_H_
#define _Q2_H_
#include"lbool.h"

class q2_solver {
public:
    virtual lbool operator() () = 0;
};

q2_solver* mk_q2_solver(ast_manager& m, params_ref p, const ptr_vector<expr>& fmls);

#endif

