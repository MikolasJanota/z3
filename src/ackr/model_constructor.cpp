/*++
 Copyright (c) 2015 Microsoft Corporation

 Module Name:

  model_constructor.cpp

 Abstract:


 Author:

 Mikolas Janota

 Revision History:
--*/
#include"model_constructor.h"
#include"model_evaluator.h"
#include"ast_smt2_pp.h"
#include"ackr_info.h"
#include"for_each_expr.h"
#include"bv_rewriter.h"
#include"bool_rewriter.h"
struct model_constructor::imp {
    public:
        imp(ast_manager& m,
            const ackr_info& info,
            model_ref& abstr_model,
            vector<std::pair<app*,app*>>& conflicts)
            : m_m(m)
            , m_info(info)
            , m_abstr_model(abstr_model)
            , m_conflicts(conflicts)
            , m_b_rw(m)
            , m_bv_rw(m)
        {}

        //
        // Returns true iff model was successfully constructed.
        //
        bool check() {
            for (unsigned i = 0; i < m_abstr_model->get_num_constants(); i++) {
                func_decl * const c = m_abstr_model->get_constant(i);
                app * const term = m_info.find_term(c);
                SASSERT(term); //TODO a constant invented by the underlying solver, do they occur?
                m_stack.push_back(term);
            }
            return run();
        }
    private:
        ast_manager&                    m_m;
        const ackr_info&                m_info;
        model_ref&                      m_abstr_model;
        vector<std::pair<app*,app*>>&   m_conflicts;
        bool_rewriter                   m_b_rw;
        bv_rewriter                     m_bv_rw;
    private:
        struct val_info { expr * value; app * source_term; };
        typedef obj_map<app, val_info> app2val_t;
        app2val_t        m_app2val;
        ptr_vector<expr> m_stack;

        static inline val_info mk_val_info(expr* value, app* source_term) {
            val_info rv;
            rv.value = value;
            rv.source_term = source_term;
            return rv;
        }

        //
        // Performs congruence check on terms on the stack.
        // (Currently stops upon the first failure).
        // Returns true if and only if congruence check succeeded.
        bool run() {
            expr_mark visited;
            expr *  curr;
            while (!m_stack.empty()) {
                curr = m_stack.back();
                if (visited.is_marked(curr)) {
                    m_stack.pop_back();
                    continue;
                }

                switch (curr->get_kind()) {
                    case AST_VAR:
                        UNREACHABLE();
                        return false;
                    case AST_APP:
                        if (for_each_expr_args(m_stack, visited,
                                    to_app(curr)->get_num_args(), to_app(curr)->get_args())) {
                            visited.mark(curr, true);
                            m_stack.pop_back();
                            if (!mk_value(to_app(curr))) return false;
                        }
                        break;
                    case AST_QUANTIFIER:
                        UNREACHABLE();
                        return false;
                    default:
                        UNREACHABLE();
                        return false;
                }
            }
            return true;
        }

        // 
        // Check and record the value for a given term, given that all arguments are already checked.
        //
        bool mk_value(app * const a) {
            SASSERT(!m_app2val.contains(a));
            family_id fid = a->get_family_id();
            const unsigned num = a->get_num_args();
            expr_ref result(m_m);

            if (num == 0) { //  handle constants
                make_value_constant(a, result);
                m_app2val.insert(a, mk_val_info(result.get(), NULL));
                return true;
            }
            expr_ref_vector values(m_m, num, NULL);
            expr * const * args = a->get_args();
            for (unsigned i = 0; i < num; ++i) { // evaluate arguments
                val_info vi;
                const bool b = m_app2val.find(to_app(args[i]), vi); // TODO: OK conversion?
                SASSERT(b);
                values[i] = vi.value;
            }
            app * const key = m_m.mk_app(a->get_decl(), values.c_ptr());
            if (fid = null_family_id) { // handle uninterpreted
                if (!make_value_uninterpreted_function(a, values, key, result))
                    return false;
            }
            else {// handle interpreted
                make_value_interpreted_function(a, values, result);
            }
            m_app2val.insert(key, mk_val_info(result.get(), a));
            return true;
        }

        // Constants from the abstract model are directly mapped to the concrete one.
        void make_value_constant(app * const a, expr_ref& result) {
            SASSERT(a->get_num_args() == 0);
            func_decl * const fd = a->get_decl();
            expr * val = m_abstr_model->get_const_interp(fd);
            if (val == 0) { // TODO: avoid model completetion?
                sort * s = fd->get_range();
                val = m_abstr_model->get_some_value(s);
            }
            result = val;
        }

        bool make_value_uninterpreted_function(app* a,
                expr_ref_vector& values,
                app* key,
                expr_ref& result) {
            app * const ac = m_info.get_abstr(a); // get ackermann constant
            func_decl * const a_fd = a->get_decl();
            SASSERT(ac->get_num_args() == 0);
            SASSERT(a_fd->get_range() == ac->get_decl()->get_range());
            expr * value = m_abstr_model->get_const_interp(ac->get_decl());
            if (value == 0) { // TODO: avoid model completetion?
                sort * s = a_fd->get_range();
                value = m_abstr_model->get_some_value(s);
            }
            val_info vi;
            if(m_app2val.find(key,vi)) {// already is mapped to a value
                SASSERT(vi.source_term);
                const bool ok =  vi.value == value;
                if(!ok) m_conflicts.push_back(std::make_pair(a,vi.source_term));
                result = vi.value;
                return ok;
            } else {// record value from abstraction
                result = vi.value;
                vi.value = value;
                vi.source_term = a;
                m_app2val.insert(key,vi);
                return true;
            }
            UNREACHABLE();
        }

        void make_value_interpreted_function(app* a,
                expr_ref_vector& values,
                expr_ref& result) {
            const unsigned num = values.size();
            func_decl * const fd = a->get_decl();
            const family_id fid = fd->get_family_id();
            if (fid == m_b_rw.get_fid()) {
                decl_kind k = fd->get_decl_kind();
                if (k == OP_EQ) {
                    // theory dispatch for =
                    SASSERT(num == 2);
                    family_id s_fid = m_m.get_sort(values.get(0))->get_family_id();
                    br_status st = BR_FAILED;
                    if (s_fid == m_bv_rw.get_fid())
                        st = m_bv_rw.mk_eq_core(values.get(0), values.get(1), result);
                    SASSERT(st != BR_FAILED);
                } else {
                    br_status st = m_b_rw.mk_app_core(fd, num, values.c_ptr(), result);
                    SASSERT(st != BR_FAILED);
                }
            } else {
                br_status st = BR_FAILED;
                if (fid == m_bv_rw.get_fid())
                    st = m_bv_rw.mk_app_core(fd, num, values.c_ptr(), result);
                else
                    UNREACHABLE();
                SASSERT(st != BR_FAILED);
            }
        }
};

model_constructor::model_constructor(ast_manager& m, const ackr_info& info)
    :m(m)
,  state(UNKNOWN)
,  info(info)
{}

bool model_constructor::check(model_ref& abstr_model) {
    conflicts.reset();
    model_constructor::imp i(m, info, abstr_model, conflicts);
    const bool rv = i.check();
    state = rv ? CHECKED : CONFLICT;
    return rv;
}