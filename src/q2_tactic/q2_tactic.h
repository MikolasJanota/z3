/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

q2_tactic.h

Abstract:

Tactic for 2 level quantification a la AReQS.

Author:

Mikolas Janota

Revision History:
--*/

#ifndef _Q2_TACTIC_H_
#define _Q2_TACTIC_H_
#include"tactical.h"

tactic * mk_q2_tactic(ast_manager & m, params_ref const & p);

/*
ADD_TACTIC("q2", "q2.", "mk_q2_tactic(m, p)")
*/

#endif

