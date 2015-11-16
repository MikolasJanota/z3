/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

lackr_model_converter.h

Abstract:

Author:

Mikolas Janota

Revision History:
--*/
#ifndef LACKR_MODEL_CONVERTER_H_5814
#define LACKR_MODEL_CONVERTER_H_5814
#include"model_converter.h"
#include"model_evaluator.h"
#include"ackr_info.h"

class lackr_model_converter : public model_converter {
public:
    lackr_model_converter(ast_manager & m, const ackr_info& info) 
        : m(m)
        , info(info)
    { }

    virtual ~lackr_model_converter() {
    }

    virtual void operator()(model_ref & md, unsigned goal_idx) {
        SASSERT(goal_idx == 0);
        model * new_model = alloc(model, m);
        convert(md.get(), new_model);
        md = new_model;
    }

    virtual void operator()(model_ref & md) {
        operator()(md, 0);
    }

    //void display(std::ostream & out);

    virtual model_converter * translate(ast_translation & translator) {
        NOT_IMPLEMENTED_YET();
    }

protected:
    ast_manager& m;
    const ackr_info& info;
    void convert(model * source, model * destination);
    void add_entry(model_evaluator & evaluator,
            app* term, expr* value,
            obj_map<func_decl, func_interp*>& interpretations);
    void convert_sorts(model * source, model * destination);
    void convert_constants(model * source, model * destination);
};

model_converter * mk_lackr_model_converter(ast_manager & m, const ackr_info& info);
#endif /* LACKR_MODEL_CONVERTER_H_5814 */
