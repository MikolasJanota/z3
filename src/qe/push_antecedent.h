 /*++
 Copyright (c) 2016 Microsoft Corporation

 Module Name:

  propagate_antecedent.h

 Abstract:


 Author:

 Mikolas Janota (MikolasJanota)

 Revision History:
 --*/
#ifndef PUSH_ANTECEDENT_H_
#define PUSH_ANTECEDENT_H_
#include "ast.h"
#include "params.h"
#include "model.h"
#include "model_based_opt.h"
#include "expr_functors.h"
namespace qe {
    class propagate_antecedent {
        class impl;
        impl * m_impl;
    public:
        propagate_antecedent(ast_manager& m);
        ~propagate_antecedent();
        bool operator()(expr * src, expr_ref& dst);
    };
}
#endif /* PUSH_ANTECEDENT_H_ */
