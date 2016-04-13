 /*++
 Copyright (c) 2015 Microsoft Corporation

 Module Name:

  miner.h

 Abstract:


 Author:

 Mikolas Janota

 Revision History:
 --*/
#ifndef MINER_H_17438
#define MINER_H_17438
#include"ast.h"
#include"params.h"
class miner {
    public:
        miner(ast_manager& m, params_ref const & p);
        virtual ~miner();
        void operator() (expr_ref f);
        void init(expr_ref f);
        bool test_term(app * term, expr_ref& value);
        bool test_term(expr * term);
    private:
        struct            imp;
        imp*              m_imp;
};
#endif /* MINER_H_17438 */
