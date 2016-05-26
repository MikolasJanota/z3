 /*++
 Copyright (c) 2016 Microsoft Corporation

 Module Name:

  lackr_arrays.h

 Abstract:


 Author:

 Mikolas Janota (MikolasJanota)

 Revision History:
 --*/
#ifndef LACKR_ARRAYS_H_
#define LACKR_ARRAYS_H_
#include"lackr.h"
#include"array_decl_plugin.h"
class lackr_arrays : protected lackr  {
    public:
        lackr_arrays(ast_manager& m, params_ref p, lackr_stats& st, expr_ref_vector& formulas, solver * uffree_solver);
        virtual ~lackr_arrays() { }
        virtual void updt_params(params_ref const & _p);
        virtual lbool operator() ();

        //
        // getters
        //
        inline ackr_info_ref get_info() { return lackr::get_info(); }
        inline model_ref get_model() { return lackr::get_model(); }

    protected:
   //     typedef ackr_helper::app_set       app_set;
        array_util            m_ar_util;
        app_set               m_selects;
        app_set               m_stores;
        app_set               m_eqs;
        virtual bool add_term(app* a);
        virtual void build_abstraction_map();
        virtual model_constructor* mk_model_constructor(ast_manager& m, ackr_info_ref& info);
        virtual lbool lazy();
};
#endif /* LACKR_ARRAYS_H_ */
