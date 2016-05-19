 /*++
 Copyright (c) 2016 Microsoft Corporation

 Module Name:

  ctx_bv_gauss_elim.h

 Abstract:


 Author:

 Mikolas Janota

 Revision History:
 --*/
#ifndef CTX_BV_GAUSS_ELIM_H_16163
#define CTX_BV_GAUSS_ELIM_H_16163
#include "tactic.h"

tactic * mk_ctx_bv_gauss_elim_tactic(ast_manager & m, params_ref const & p = params_ref());

/*
  ADD_TACTIC("ctx-bv-gauss_elim", "", "mk_ctx_bv_gauss_elim_tactic(m, p)")
*/
#endif /* CTX_BV_GAUSS_ELIM_H_16163 */
