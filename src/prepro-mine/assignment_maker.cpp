/*++
 Copyright (c) 2015 Microsoft Corporation

 Module Name:

  assignment_maker.cpp

 Abstract:


 Author:

 Mikolas Janota

 Revision History:
--*/
#include"assignment_maker.h"

void assignment_maker::operator() (/*in*/unsigned count, /*in*/func_decl* const * declarations,/*out*/model_ref& assignment) {
    for (unsigned i = 0; i < count; ++i) {
        func_decl * const declaration = declarations[i];
        expr_ref value(m_m);
        value = m_m.get_some_value(declaration->get_range());
        const unsigned arity = declaration->get_arity();
        if(arity == 0) {
            assignment->register_decl(declaration, value);
        } else {
            func_interp * fi = alloc(func_interp, m_m, arity);
            fi->set_else(value.get());
            assignment->register_decl(declaration, fi);
        }
    }
}
