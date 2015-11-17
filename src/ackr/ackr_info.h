/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

ackr_info.h

Abstract:

Author:

Mikolas Janota

Revision History:
--*/
#ifndef ACKR_INFO_H_12278
#define ACKR_INFO_H_12278
#include"obj_hashtable.h"
#include"ast.h"
#include"ref.h"
#include"expr_replacer.h"

class ackr_info {
    public:
        ackr_info(ast_manager& m)
        : m_m(m)
        , m_consts(m)
        , m_ref_count(0)
        , m_er(mk_default_expr_replacer(m))
        , m_subst(m_m)
        , m_sealed(false)
        {}

        virtual ~ackr_info() {
            //std::cout << "~ackr_info()" << std::endl;
            m_consts.reset();
        }

        inline app* find_term(func_decl* c)  const {
            app *  rv = 0;
            m_c2t.find(c,rv);
            return rv;
        }

        inline app* get_abstr(app* term)  const {
            app * const rv = m_t2c.find(term);
            SASSERT(rv);
            return rv;
        }

        inline void set_abstr(app* term, app* c) {
            SASSERT(!m_sealed);
            SASSERT(c);
            m_t2c.insert(term,c);
            m_c2t.insert(c->get_decl(),term);
            m_subst.insert(term, c);
            m_consts.push_back(c);
        }

        inline void abstract(expr * e, expr_ref& res) {
            SASSERT(m_sealed);
            (*m_er)(e, res);
        }

        inline void seal() {
            m_sealed=true;
            m_er->set_substitution(&m_subst);
        }

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
        typedef obj_map<app, app*> t2ct;
        typedef obj_map<func_decl, app*> c2tt;
        t2ct m_t2c;
        c2tt m_c2t;
        expr_ref_vector m_consts;
        unsigned m_ref_count;
        ast_manager& m_m;
        scoped_ptr<expr_replacer> m_er;
        expr_substitution m_subst;
        bool m_sealed;
};

typedef ref<ackr_info> ackr_info_ref;
#endif /* ACKR_INFO_H_12278 */
