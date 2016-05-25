 /*++
 Copyright (c) 2016 Microsoft Corporation

 Module Name:

  lackr_arrays_model_constructor.h

 Abstract:


 Author:

 Mikolas Janota (MikolasJanota)

 Revision History:
 --*/
#ifndef LACKR_ARRAYS_MODEL_CONSTRUCTOR_H_
#define LACKR_ARRAYS_MODEL_CONSTRUCTOR_H_
#include"ast.h"
#include"ackr_info.h"
#include"ackr_helper.h"
#include"model.h"
#include"model_constructor.h"

class lackr_arrays_model_constructor : public model_constructor {
    public:
        lackr_arrays_model_constructor(ast_manager& m, ackr_info_ref info);
        virtual ~lackr_arrays_model_constructor();
        virtual bool check(model_ref& abstr_model);

        virtual const expr_ref_vector& get_array_lemmas() {
            SASSERT(m_state == CONFLICT);
            return m_array_lemmas;
        }

        virtual const conflict_list& get_conflicts() {
            SASSERT(m_state == CONFLICT);
            return m_conflicts;
        }
        virtual void make_model(model_ref& model);

        //
        // Reference counting
        //
        void inc_ref() { ++m_ref_count; }
        void dec_ref() {
            --m_ref_count;
            if (m_ref_count == 0) {
                dealloc(this);
            }
        }
    private:
        struct imp;
        imp * m_imp;
        ast_manager &                      m_m;
        enum {CHECKED, CONFLICT, UNKNOWN}  m_state;
        conflict_list                      m_conflicts;
        expr_ref_vector                    m_array_lemmas;
        const ackr_info_ref                m_info;

        unsigned m_ref_count; // reference counting
};

typedef ref<lackr_arrays_model_constructor> lackr_arrays_model_constructor_ref;
#endif /* LACKR_ARRAYS_MODEL_CONSTRUCTOR_H_ */
