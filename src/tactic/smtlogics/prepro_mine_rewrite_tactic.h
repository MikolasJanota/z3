 /*++
 Copyright (c) 2015 Microsoft Corporation

 Module Name:

  prepro_mine_rewrite_tactic.h

 Abstract:


 Author:

 Mikolas Janota

 Revision History:
 --*/
#ifndef PREPRO_MINE_REWRITE_TACTIC_H_724
#define PREPRO_MINE_REWRITE_TACTIC_H_724
#include"tactical.h"
tactic * mk_prepro_mine_rewrite_tactic(ast_manager& m, params_ref const & p);

/*
ADD_TACTIC("prepro-mine-rewriter", "prepro-mine-rewriter.", "mk_prepro_mine_rewrite_tactic(m, p)")
*/


#endif /* PREPRO_MINE_TACTIC_H_724 */
