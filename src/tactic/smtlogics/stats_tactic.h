 /*++
 Copyright (c) 2016 Microsoft Corporation

 Module Name:

  stats_tactic.h

 Abstract:


 Author:

 Mikolas Janota

 Revision History:
 --*/
#ifndef STATS_TACTIC_H_13304
#define STATS_TACTIC_H_13304
#include"params.h"
#include"tactical.h"

tactic * mk_stats_tactic(ast_manager & m, params_ref const & p = params_ref());

/*
  ADD_TACTIC("stats",  "tactic to collect information about the input problem.", "mk_stats_tactic(m, p)")
*/
#endif /* STATS_TACTIC_H_13304 */
