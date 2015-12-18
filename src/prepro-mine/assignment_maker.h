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
         assignment_maker(ast_manager& m);
         ~assignment_maker();
         void set_polarity(bool polarity);
         void operator() (/*in*/unsigned count, /*in*/func_decl* const * declarations,
             /*out*/model_ref& assignment);
     private:
         struct imp;
         imp* m_imp;
};

assignment_maker* mk_assignment_maker();
