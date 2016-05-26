 /*++
 Copyright (c) 2016 Microsoft Corporation

 Module Name:

  model_constructor.h

 Abstract:


 Author:

 Mikolas Janota (MikolasJanota)

 Revision History:
 --*/
#ifndef MODEL_CONSTRUCTOR_H_
#define MODEL_CONSTRUCTOR_H_
class model_constructor {
    public:
        typedef std::pair<app *, app *>           app_pair;
        typedef vector<app_pair>                  conflict_list;
        virtual bool check(model_ref& abstr_model) = 0;
        virtual const conflict_list& get_conflicts() = 0;
        //virtual void make_model(model_ref& model) = 0;
};
#endif /* MODEL_CONSTRUCTOR_H_ */
