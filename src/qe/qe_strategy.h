 /*++
 Copyright (c) 2016 Microsoft Corporation

 Module Name:

  qe_strategy.h

 Abstract:


 Author:

 Mikolas Janota (MikolasJanota)

 Revision History:
 --*/
#ifndef QE_STRATEGY_H_
#define QE_STRATEGY_H_
#include "ast.h"
#include "model.h"
#include "expr_substitution.h"
#include <ostream>
namespace qe {
namespace rareqs {
    std::ostream& prn_strategy(std::ostream& o, app_ref_vector const& vars, expr_substitution& strategy);

    class mk_strategy {
        class impl;
        impl * m_impl;
    public:
        mk_strategy(ast_manager& m);

        ~mk_strategy();

        /**
           \brief
        */
        void operator()(app_ref_vector const & vars, model& mdl, expr_ref const & fml,
                /*out*/expr_substitution& strategy);

    };
} /* namespace rareqs */
} /* namespace qe */

#endif /* QE_STRATEGY_H_ */
