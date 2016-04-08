/*++
 Copyright (c) 2016 Microsoft Corporation

 Module Name:

  ackermannize_model_converter.cpp

 Abstract:


 Author:

 Mikolas Janota

 Revision History:
--*/
#include"ackr_model_converter.h"
#include"ackermannize_model_converter.h"

model_converter * mk_ackermannize_model_converter(ast_manager & m, const ackr_info_ref& info) {
 return mk_ackr_model_converter(m, info);
}
