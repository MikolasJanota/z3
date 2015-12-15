 /*++
 Copyright (c) 2015 Microsoft Corporation

 Module Name:

  lackr.h

 Abstract:


 Author:

 Mikolas Janota

 Revision History:
 --*/
#ifndef LACKR_H_15079
#define LACKR_H_15079
///////////////
#include"inc_sat_solver.h"
#include"qfaufbv_tactic.h"
#include"qfbv_tactic.h"
#include"tactic2solver.h"
#include"ackr_info.h"
#include"tactic_exception.h"
#include"th_rewriter.h"
#include"cooperate.h"

class lackr {
    public:
        lackr(ast_manager& m, params_ref p, expr_ref _f)
            : m_m(m)
            , m_p(p)
            , m_fla(m)
            , m_abstr(m)
            , m_sat(0)
            , m_bvutil(m)
            , m_simp(m)
            , m_ackrs(m)
            , m_cancel(0)
    {
        //simp_wrap _s(m_m);
        //_s(_f, m_fla);
        m_fla = _f;
        updt_params(p);
    }

        lbool operator() ();
        ~lackr() {
            const fun2terms_map::iterator e = m_fun2terms.end();
            for (fun2terms_map::iterator i = m_fun2terms.begin(); i != e; ++i) {
                dealloc(i->get_value());
            }
        }

        ackr_info_ref get_info() { return m_info; }
        model_ref get_model() { return m_model; }

        void updt_params(params_ref const & _p) {
            ackr_params p(_p);
            m_eager = p.eager();
            m_use_sat = p.sat_backend();
        }


        //
        //  timeout mechanisms
        //

        void checkpoint() {
            if (m_cancel)
                throw tactic_exception(TACTIC_CANCELED_MSG);
            cooperate("lackr");
        }

        //virtual void set_cancel(bool f) {
        //    //#pragma omp critical (lackr_cancel)
        //    {
        //        m_cancel = f;
        //        if (m_sat == NULL) return;
        //        if (f) m_sat->cancel();
        //        else m_sat->reset_cancel();
        //    }
        //}
    private:
        typedef obj_hashtable<app>           app_set;
        typedef obj_map<func_decl, app_set*> fun2terms_map;
        ast_manager&                         m_m;
        params_ref                           m_p;
        expr_ref                             m_fla;
        expr_ref                             m_abstr;
        fun2terms_map                        m_fun2terms;
        ackr_info_ref                        m_info;
        scoped_ptr<solver>                   m_sat;
        bv_util                              m_bvutil;
        th_rewriter                          m_simp;
        expr_ref_vector                      m_ackrs;
        model_ref                            m_model;
        volatile bool                        m_cancel;
        bool                                 m_eager;
        bool                                 m_use_sat;

        bool init();
        void setup_sat();
        lbool eager();
        lbool lazy();

        //
        // Introduce ackermann lemma for the two given terms.
        //
        bool ackr(app * const t1, app * const t2);

        //
        // Introduce the ackermann lemma for each pair of terms.
        //
        bool eager_enc();

        bool abstract();

        void add_term(app* a);

        //
        // Collect all uninterpreted terms.
        //
        bool collect_terms();
};
#endif /* LACKR_H_15079 */
