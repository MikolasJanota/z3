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
    public:
        model_constructor(ast_manager& m, const ackr_info& info);
        bool check(model_ref& abstr_model);
        vector<std::pair<app*, app*>>& get_conflicts() {
            SASSERT(state==CONFLICT);
            return conflicts;
        }
    private:
        struct imp;
        enum {CHECKED, CONFLICT, UNKNOWN} state;
        vector<std::pair<app*,app*>> conflicts;
        ast_manager& m;
        const ackr_info& info;
};
#endif /* MODEL_CONSTRUCTOR_H_626 */
