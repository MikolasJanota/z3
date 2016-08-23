 /*++
 Copyright (c) 2016 Microsoft Corporation

 Module Name:

  rareqs.h

 Abstract:
 Implementation of the RAReQS architecture for solving quantified problems based on Janota et al., SAT '12.


 Author:

 Mikolas Janota (MikolasJanota)

 Revision History:
 --*/
#ifndef RAREQS_H_
#define RAREQS_H_

#include "tactic.h"
#include "filter_model_converter.h"
#include "qe_mbp.h"

tactic * mk_rareqs_tactic(ast_manager & m, params_ref const& p = params_ref());

/*
  ADD_TACTIC("rareqs", "apply a RAReQS solver.", "mk_rareqs_tactic(m, p)")
*/
#endif
