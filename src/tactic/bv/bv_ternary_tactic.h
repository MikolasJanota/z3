 /*++
 Copyright (c) 2016 Microsoft Corporation

 Module Name:

  bv_ternary_tactic.h

 Abstract:


 Author:

 Mikolas Janota (MikolasJanota)

 Revision History:
 --*/
#ifndef BV_TERNARY_TACTIC_H_
#define BV_TERNARY_TACTIC_H_
#include "tactic.h"

tactic * mk_bv_ternary_tactic(ast_manager & m, params_ref const & p = params_ref());

/*
  ADD_TACTIC("bv_ternary", "", "mk_bv_ternary_tactic(m, p)")
*/

#endif /* BV_TERNARY_TACTIC_H_ */
