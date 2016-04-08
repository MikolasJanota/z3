 /*++
 Copyright (c) 2016 Microsoft Corporation

 Module Name:

  ackermannize_tactic.h

 Abstract:


 Author:

 Mikolas Janota

 Revision History:
 --*/
#ifndef ACKERMANNIZE_TACTIC_H_20711
#define ACKERMANNIZE_TACTIC_H_20711
#include"tactical.h"

tactic * mk_ackermannize_tactic(ast_manager & m, params_ref const & p);

/*
  ADD_TACTIC("ackermannize", "A tactic for performing full Ackermannization.", "mk_ackermannize_tactic(m, p)")
*/
#endif /* ACKERMANNIZE_TACTIC_H_20711 */
