/*++
 Copyright (c) 2015 Microsoft Corporation

 Module Name:

  assignment_maker.h

 Abstract:


 Author:

 Mikolas Janota

 Revision History:
--*/
#include"ast.h"
#include"model.h"
class assignment_maker {
     public:
         assignment_maker(ast_manager& m) : m_m(m) {}
         void operator() (/*in*/unsigned count, /*in*/func_decl* const * declarations,
             /*out*/model_ref& assignment);
     private:
         ast_manager& m_m;
};

assignment_maker* mk_assignment_maker();
