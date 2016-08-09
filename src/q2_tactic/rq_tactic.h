#ifndef _RQ_TACTIC_H_
#define _RQ_TACTIC_H_
#include"tactical.h"

tactic * mk_rq_tactic(ast_manager & m, params_ref const & p);

/*
ADD_TACTIC("rq", "rq.", "mk_rq_tactic(m, p)")
*/

#endif

