 /*++
 Copyright (c) 2016 Microsoft Corporation

 Module Name:

  ackermannize_model_converter.h

 Abstract:


 Author:

 Mikolas Janota

 Revision History:
 --*/
#ifndef ACKERMANNIZE_MODEL_CONVERTER_H_21501
#define ACKERMANNIZE_MODEL_CONVERTER_H_21501
#include"model_converter.h"
#include"ackr_info.h"

model_converter * mk_ackermannize_model_converter(ast_manager & m, const ackr_info_ref& info);

#endif /* ACKERMANNIZE_MODEL_CONVERTER_H_21501 */
