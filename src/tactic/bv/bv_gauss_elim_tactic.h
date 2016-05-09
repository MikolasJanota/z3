 /*++
 Copyright (c) 2016 Microsoft Corporation

 Module Name:

  bv_gauss_elim_tactic.h

 Abstract:


 Author:

 Mikolas Janota

 Revision History:
 --*/
#ifndef BV_GAUSS_ELIM_TACTIC_H_
#define BV_GAUSS_ELIM_TACTIC_H_
#include "tactic.h"

tactic * mk_bv_gauss_elim_tactic(ast_manager & m, params_ref const & p = params_ref());

/*
  ADD_TACTIC("bv-gauss_elim", "bit-vector gauss elimination, if applicable.", "mk_bv_gauss_elim_tactic(m, p)")
*/

#endif /* BV_GAUSS_ELIM_TACTIC_H_ */
