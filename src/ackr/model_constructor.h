 /*++
 Copyright (c) 2015 Microsoft Corporation

 Module Name:

  model_constructor.h

 Abstract:
   Given a propositional abstraction, attempt to construct a model.


 Author:

 Mikolas Janota

 Revision History:
 --*/
#ifndef MODEL_CONSTRUCTOR_H_626
#define MODEL_CONSTRUCTOR_H_626
#include"ast.h"
#include"ackr_info.h"
#include"model.h"
class model_constructor {
    private:
        struct imp;        
    public:
        model_constructor(ast_manager& m, ackr_info_ref info);
        bool check(model_ref& abstr_model);
        vector<std::pair<app*, app*>>& get_conflicts() {
            SASSERT(class_state==CONFLICT);
            return conflicts;
        }
    private:
        enum {CHECKED, CONFLICT, UNKNOWN} class_state;
        vector<std::pair<app*,app*>> conflicts;
        ast_manager& m;
        ackr_info_ref info;
};
#endif /* MODEL_CONSTRUCTOR_H_626 */
