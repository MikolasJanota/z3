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
         enum gen_mode { ONE, ZERO, RANDOM};
         assignment_maker(ast_manager& m);
         virtual ~assignment_maker();
         void set_mode(gen_mode mode);
         void operator() (/*in*/unsigned count, /*in*/func_decl* const * declarations,
             /*out*/model_ref& assignment);
     private:
         struct imp;
         imp* m_imp;
};

assignment_maker* mk_assignment_maker();
