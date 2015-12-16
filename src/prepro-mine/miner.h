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
class miner {
    public:
        miner(ast_manager& m);
        void operator() (expr_ref f);
    private:
        struct            imp;
        scoped_ptr<imp>   m_imp;
};
#endif /* MINER_H_17438 */
