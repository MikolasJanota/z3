/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

lackr_model_converter.cpp

Abstract:

Author:

Mikolas Janota

Revision History:
--*/
#include"lackr_model_converter.h"
#include"model_evaluator.h"
#include"ast_smt2_pp.h"


void lackr_model_converter::convert(model * source, model * destination) {
    SASSERT(!source->get_num_functions());
    convert_constants(source,destination);
    convert_sorts(source,destination);
}

void lackr_model_converter::convert_constants(model * source, model * destination) {
    TRACE("lackr_model", tout << "converting constants\n";);
    obj_map<func_decl, func_interp*> interpretations;
    model_evaluator evaluator(*source);
    for (unsigned i = 0; i < source->get_num_constants(); i++) {
        func_decl * const c = source->get_constant(i);
        app * const term = info.find_term(c);
        expr * value = source->get_const_interp(c);
        TRACE("lackr_model", tout << "Abstract value"
            << mk_ismt2_pp(term, m, 2)
            << "->"
            << mk_ismt2_pp(term, m, 2);
            );

        if(!term) {
            destination->register_decl(c, value);
        } else {
            add_entry(evaluator, term, value, interpretations);
        }
    }

    obj_map<func_decl, func_interp*>::iterator e = interpretations.end();
    for (obj_map<func_decl, func_interp*>::iterator i = interpretations.begin();
            i!=e; ++i) {
        func_decl* const fd = i->m_key;
        func_interp* const fi = i->get_value();
        destination->register_decl(fd, fi);
    }
}

void lackr_model_converter::add_entry(model_evaluator & evaluator,
        app* term, expr* value,
        obj_map<func_decl, func_interp*>& interpretations) {
    func_interp* fi = 0;
    func_decl * const declaration = term->get_decl();
    const unsigned sz = declaration->get_arity();
    SASSERT(sz == term->get_num_args());
    if (!interpretations.find(declaration, fi))  {
       fi = alloc(func_interp,m,sz);
       interpretations.insert(declaration, fi);
    }
    expr_ref_vector args(m);
    for (unsigned gi = 0; gi < sz; ++gi) {
      expr * const arg = term->get_arg(gi);
      expr_ref arg_value(m);
      evaluator(arg,arg_value);
      args.push_back(arg_value);
    }
    fi->insert_new_entry(args.c_ptr(), value);
}

void lackr_model_converter::convert_sorts(model * source, model * destination) {
    for (unsigned i = 0; i < source->get_num_uninterpreted_sorts(); i++) {
        sort * const s = source->get_uninterpreted_sort(i);
        ptr_vector<expr> u = source->get_universe(s);
        destination->register_usort(s, u.size(), u.c_ptr());
    }
}

model_converter * mk_lackr_model_converter(ast_manager & m, const ackr_info& info) {
    return alloc(lackr_model_converter, m, info);
}
