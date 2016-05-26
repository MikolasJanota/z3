/*++
 Copyright (c) 2016 Microsoft Corporation

 Module Name:

  lackr_arrays_model_constructor.cpp

 Abstract:


 Author:

 Mikolas Janota (MikolasJanota)

 Revision History:
--*/
#include"lackr_arrays_model_constructor.h"
#include"model_evaluator.h"
#include"ast_smt2_pp.h"
#include"ackr_info.h"
#include"for_each_expr.h"
#include"bv_rewriter.h"
#include"bool_rewriter.h"
#include"array_decl_plugin.h"

struct lackr_arrays_model_constructor::imp {
    public:
        imp(ast_manager & m,
            ackr_info_ref info,
            model_ref & abstr_model,
            conflict_list & conflicts,
            expr_ref_vector & array_lemmas
            )
            : m_m(m)
            , m_info(info)
            , m_abstr_model(abstr_model)
            , m_conflicts(conflicts)
            , m_array_lemmas(array_lemmas)
            , m_b_rw(m)
            , m_bv_rw(m)
            , m_evaluator(NULL)
            , m_empty_model(m)
            , m_ackr_helper(m)
            , m_ar_util(m)
            , m_qued_dests(m)
            , m_qued_rds(m)
            , m_qued_vals(m)
            , m_qued_reasons(m)
        {}

        ~imp() {
            if (m_evaluator) dealloc(m_evaluator);
            {
                values2val_t::iterator i = m_values2val.begin();
                const values2val_t::iterator e = m_values2val.end();
                for (; i != e; ++i) {
                    m_m.dec_ref(i->m_key);
                    m_m.dec_ref(i->m_value.value);
                    m_m.dec_ref(i->m_value.source_term);
                }
            }
            {
                app2val_t::iterator i = m_app2val.begin();
                const app2val_t::iterator e = m_app2val.end();
                for (; i != e; ++i) {
                    m_m.dec_ref(i->m_value);
                    m_m.dec_ref(i->m_key);
                }
            }
            {
                obj_map<expr, expr2read_info_t *>::iterator i = m_read_vals.begin();
                const obj_map<expr, expr2read_info_t *>::iterator e = m_read_vals.end();
                for (; i != e; ++i) {
                    expr2read_info_t * t = i->get_value();
                    expr2read_info_t::iterator ti = t->begin();
                    const expr2read_info_t::iterator te = t->end();
                    for (; ti != te; ++ti) {
                        const read_info& ri = ti->m_value;
                        m_m.dec_ref(ti->m_key);
                        m_m.dec_ref(ri.reason);
                        m_m.dec_ref(ri.value);
                        m_m.dec_ref(ri.rd);
                    }
                    m_m.dec_ref(i->m_key);
                    dealloc(t);
                    i->m_value = NULL;
                }
            }
        }

        //
        // Returns true iff model was successfully constructed.
        // Conflicts are saved as a side effect.
        //
        bool check() {
            bool retv = true;
            for (unsigned i = 0; i < m_abstr_model->get_num_constants(); i++) {
                func_decl * const c = m_abstr_model->get_constant(i);
                app * const  _term = m_info->find_term(c);
                expr * const term  = _term ? _term : m_m.mk_const(c);
                if (!check_term(term)) retv = false;
            }
            retv = retv && process_read_que();
            return retv;
        }


        void make_model(model_ref& destination) {
            {
                for (unsigned i = 0; i < m_abstr_model->get_num_uninterpreted_sorts(); i++) {
                    sort * const s = m_abstr_model->get_uninterpreted_sort(i);
                    ptr_vector<expr> u = m_abstr_model->get_universe(s);
                    destination->register_usort(s, u.size(), u.c_ptr());
                }
            }
            for (unsigned i = 0; i < m_abstr_model->get_num_functions(); i++) {
                func_decl * const fd = m_abstr_model->get_function(i);
                func_interp * const fi = m_abstr_model->get_func_interp(fd);
                destination->register_decl(fd, fi);
            }

            {
                const app2val_t::iterator e = m_app2val.end();
                app2val_t::iterator i = m_app2val.end();
                for (; i != e; ++i) {
                    app * a = i->m_key;
                    if (a->get_num_args()) continue;
                    destination->register_decl(a->get_decl(), i->m_value);
                }
            }

            obj_map<func_decl, func_interp*> interpretations;
            {
                const values2val_t::iterator e = m_values2val.end();
                values2val_t::iterator i = m_values2val.end();
                for (; i != e; ++i) add_entry(i->m_key, i->m_value.value, interpretations);
            }

            {
                obj_map<func_decl, func_interp*>::iterator ie = interpretations.end();
                obj_map<func_decl, func_interp*>::iterator ii = interpretations.begin();
                for (; ii != ie; ++ii) {
                    func_decl* const fd = ii->m_key;
                    func_interp* const fi = ii->get_value();
                    fi->set_else(m_m.get_some_value(fd->get_range()));
                    destination->register_decl(fd, fi);
                }
            }
        }

        void add_entry(app* term, expr* value,
            obj_map<func_decl, func_interp*>& interpretations) {
            func_interp* fi = 0;
            func_decl * const declaration = term->get_decl();
            const unsigned sz = declaration->get_arity();
            SASSERT(sz == term->get_num_args());
            if (!interpretations.find(declaration, fi)) {
                fi = alloc(func_interp, m_m, sz);
                interpretations.insert(declaration, fi);
            }
            fi->insert_new_entry(term->get_args(), value);
        }
    private:
        ast_manager&                    m_m;
        ackr_info_ref                   m_info;
        model_ref&                      m_abstr_model;
        conflict_list&                  m_conflicts;
        expr_ref_vector&                m_array_lemmas;
        bool_rewriter                   m_b_rw;
        bv_rewriter                     m_bv_rw;
        model_evaluator *               m_evaluator;
        model                           m_empty_model;
        array_util                      m_ar_util;
    private:
        struct val_info { expr * value; app * source_term; };
        struct read_info { expr* rd; expr * value; expr * reason; };
        typedef obj_map<app, expr *> app2val_t;
        typedef obj_map<expr, read_info> expr2read_info_t;
        typedef obj_map<app, val_info> values2val_t;
        values2val_t     m_values2val;
        app2val_t        m_app2val;
        ptr_vector<expr> m_stack;
        ackr_helper      m_ackr_helper;
        expr_mark        m_visited;

        static inline val_info mk_val_info(expr* value, app* source_term) {
            val_info rv;
            rv.value = value;
            rv.source_term = source_term;
            return rv;
        }

        // Performs congruence check on a given term.
        bool check_term(expr * term) {
            m_stack.push_back(term);
            const bool rv = _check_stack();
            m_stack.reset();
            return rv;
        }

        // Performs congruence check on terms on the stack.
        // Stops upon the first failure.
        // Returns true if and only if all congruence checks succeeded.
        bool _check_stack() {
            if (m_evaluator == NULL) m_evaluator = alloc(model_evaluator, m_empty_model);
            expr *  curr;
            while (!m_stack.empty()) {
                curr = m_stack.back();
                if (m_visited.is_marked(curr)) {
                    m_stack.pop_back();
                    continue;
                }

                switch (curr->get_kind()) {
                    case AST_VAR:
                        UNREACHABLE();
                        return false;
                    case AST_APP: {
                            app * a = to_app(curr);
                            if (for_each_expr_args(m_stack, m_visited, a->get_num_args(), a->get_args())) {
                                m_visited.mark(a, true);
                                m_stack.pop_back();
                                if (!mk_value(a)) return false;
                            }
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

        inline bool is_val(expr * e) { return m_m.is_value(e); }

        inline bool eval_cached(expr * a, expr *& val) {
            return eval_cached(to_app(a), val);
        }

        inline bool eval_cached(app * a, expr *& val) {
            if (is_val(a)) { val = a; return true; }
            return m_app2val.find(a, val);
        }

        bool evaluate(app * const a, expr_ref& result) {
            SASSERT(!is_val(a));
            const unsigned num = a->get_num_args();
            if (num == 0) { // handle constants
                make_value_constant(a, result);
                return true;
            }
            expr * const * args = a->get_args();
            if (m_ar_util.is_select(a)) {
                expr* ix_val(NULL);
                const bool b = eval_cached(to_app(args[1]), ix_val); // TODO: OK conversion to_app?
                if (!b) { // bailing out because args eval failed previously
                    return false;
                }
                return mk_value_select(a, ix_val, result);
            }
            // evaluate arguments
            expr_ref_vector values(m_m);
            values.reserve(num);
            for (unsigned i = 0; i < num; ++i) {
                expr * val;
                const bool b = eval_cached(to_app(args[i]), val); // TODO: OK conversion to_app?
                CTRACE("model_constructor", m_conflicts.empty() && !b, tout << "fail arg val(\n" << mk_ismt2_pp(args[i], m_m, 2) << '\n'; );
                if (!b) { // bailing out because args eval failed previously
                    return false;
                }
                TRACE("model_constructor", tout <<
                    "arg val " << i << "(\n" << mk_ismt2_pp(args[i], m_m, 2)
                    << " : " << mk_ismt2_pp(val, m_m, 2) << '\n'; );
                SASSERT(b);
                values[i] = val;
            }
            // handle functions
            if (m_ackr_helper.should_ackermannize(a)) { // handle uninterpreted
                app_ref key(m_m.mk_app(a->get_decl(), values.c_ptr()), m_m);
                if (!make_value_uninterpreted_function(a, values, key.get(), result)) {
                    return false;
                }
            }
            else { // handle interpreted
                make_value_interpreted_function(a, values, result);
            }
            return true;
        }

        //
        // Check and record the value for a given term, given that all arguments are already checked.
        //
        bool mk_value(app * a) {
            if (is_val(a)) return true; // skip numerals
            if (m_ar_util.is_array(a))  return true; // skip array values
            TRACE("model_constructor", tout << "mk_value(\n" << mk_ismt2_pp(a, m_m, 2) << ")\n";);
            SASSERT(!m_app2val.contains(a));
            expr_ref result(m_m);
            if (!evaluate(a, result)) return false;
            SASSERT(is_val(result));
            TRACE("model_constructor",
                tout << "map term(" << mk_ismt2_pp(a, m_m, 2) << "->"
                << mk_ismt2_pp(result.get(), m_m, 2)<< ")\n"; );
            CTRACE("model_constructor",
                !is_val(result.get()),
                tout << "eval fail\n" << mk_ismt2_pp(a, m_m, 2) << mk_ismt2_pp(result, m_m, 2) << "\n";
            );
            SASSERT(is_val(result.get()));
            m_app2val.insert(a, result.get()); // memoize
            m_m.inc_ref(a);
            m_m.inc_ref(result.get());
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
            // get ackermann constant
            app * const ac = m_info->get_abstr(a);
            func_decl * const a_fd = a->get_decl();
            SASSERT(ac->get_num_args() == 0);
            SASSERT(a_fd->get_range() == ac->get_decl()->get_range());
            expr_ref value(m_m);
            value = m_abstr_model->get_const_interp(ac->get_decl());
            // get ackermann constant's interpretation
            if (value.get() == 0) { // TODO: avoid model completion?
                sort * s = a_fd->get_range();
                value = m_abstr_model->get_some_value(s);
            }
            // check congruence
            val_info vi;
            if(m_values2val.find(key,vi)) { // already is mapped to a value
                SASSERT(vi.source_term);
                const bool ok =  vi.value == value;
                if (!ok) {
                    TRACE("model_constructor",
                        tout << "already mapped by(\n" << mk_ismt2_pp(vi.source_term, m_m, 2) << "\n->"
                             << mk_ismt2_pp(vi.value, m_m, 2) << ")\n"; );
                    m_conflicts.push_back(std::make_pair(a, vi.source_term));
                }
                result = vi.value;
                return ok;
            } else {                        // new value
                result = value;
                vi.value = value;
                vi.source_term = a;
                m_values2val.insert(key,vi);
                m_m.inc_ref(vi.source_term);
                m_m.inc_ref(vi.value);
                m_m.inc_ref(key);
                return true;
            }
            UNREACHABLE();
            return true;
        }

        obj_map<expr, expr2read_info_t*> m_read_vals;
        expr_ref_vector   m_qued_dests;
        expr_ref_vector   m_qued_rds;
        expr_ref_vector   m_qued_vals;
        expr_ref_vector   m_qued_reasons;
        inline bool inv() const {
            const unsigned sz = m_qued_dests.size();
            return (sz == m_qued_rds.size())
                && (sz == m_qued_vals.size())
                && (sz == m_qued_reasons.size());
        }

        void que_read(expr* dest, expr* rd, expr_ref& val, expr_ref& reason) {
            SASSERT(m_ar_util.is_array(dest));
            SASSERT(inv());
            m_qued_dests.push_back(dest);
            m_qued_rds.push_back(rd);
            m_qued_vals.push_back(val);
            m_qued_reasons.push_back(reason);
            SASSERT(inv());
        }

        void pop_read(expr_ref& dest, expr_ref& rd, expr_ref& val, expr_ref& reason) {
            SASSERT(m_qued_dests.size());
            SASSERT(inv());
            dest = m_qued_dests.back();
            rd = m_qued_rds.back();
            SASSERT(m_ar_util.is_select(rd) || m_ar_util.is_store(rd));
            val = m_qued_vals.back();
            reason = m_qued_reasons.back();
            m_qued_dests.pop_back();
            m_qued_vals.pop_back();
            m_qued_rds.pop_back();
            m_qued_reasons.pop_back();
            SASSERT(inv());
        }

        void get_abstract(expr* rd, expr_ref& res) {
            SASSERT(m_ar_util.is_select(rd) || m_ar_util.is_store(rd));
            if (m_ar_util.is_select(rd)) m_info->abstract(rd,res);
            else m_info->abstract(to_app(rd)->get_arg(2), res);
        }

        expr * get_ix(expr* rd) {
            SASSERT(m_ar_util.is_select(rd) || m_ar_util.is_store(rd));
            return to_app(rd)->get_arg(1);
        }

        bool get_val(app* rd, expr*& res) {
            SASSERT(m_ar_util.is_select(rd) || m_ar_util.is_store(rd));
            if (m_ar_util.is_select(rd)) {
                const bool rv = eval_cached(to_app(get_ix(rd)), res);
                SASSERT(!rv || is_val(res));
                return rv;
            }
            {
                SASSERT(m_ar_util.is_store(rd));
                const bool rv = eval_cached(to_app(rd->get_arg(2)), res);
                SASSERT(!rv || is_val(res));
                return rv;
            }
        }

        bool get_ix_val(expr* rd, expr*& res) {
            const bool rv = eval_cached(to_app(get_ix(rd)), res);
            SASSERT(!rv || is_val(res));
            return rv;
        }

        bool process_read_que() {
            expr_ref dest(m_m);
            expr_ref rd(m_m);
            expr_ref val(m_m);
            expr_ref reason(m_m);
            while (m_qued_dests.size()) {
                pop_read(dest, rd, val, reason);
                TRACE("model_constructor", tout << "processing read " << mk_ismt2_pp(rd, m_m, 2) << " : " << mk_ismt2_pp(dest, m_m, 2) << "," << mk_ismt2_pp(val.get(), m_m, 2) << ",";
                    if (reason.get()) tout << mk_ismt2_pp(reason.get(), m_m, 2);
                     else tout << "NULL";
                     tout << std::endl;);
                expr2read_info_t * const rvs = get_read_vals(dest);
                expr * ix_val(NULL);
                if (!get_ix_val(rd, ix_val)) return false;
                TRACE("model_constructor", tout << "ix_val: " << mk_ismt2_pp(ix_val, m_m) << std::endl;);
                const expr2read_info_t::iterator i = rvs->find_iterator(ix_val);
                if (i == rvs->end()) {
                    read_info ri;
                    ri.reason = reason.get();
                    ri.value = val.get();
                    ri.rd = rd;
                    m_m.inc_ref(ix_val);
                    m_m.inc_ref(ri.reason);
                    m_m.inc_ref(ri.value);
                    m_m.inc_ref(ri.rd);
                    rvs->insert(ix_val, ri);
                }
                else {
                    if (m_m.are_distinct(i->m_value.value, val)) {
                        mk_arr_lemma(rd, reason, i->m_value);
                        return false;
                    }
                }
                if (!propagate_read(dest, rd, ix_val, val, reason)) {
                    return false;
                }
            }
            return true;
        }

        expr * mk_and_safe(expr * a, expr * b) {
            if (a == NULL) return b;
            if (b == NULL) return a;
            return m_m.mk_and(a, b);
        }

        void mk_arr_lemma(expr_ref& rd, expr_ref& reason, const read_info& ri1) {
            expr * const rd1 = ri1.rd;
            TRACE("model_constructor", tout << "array conflict, with " << mk_ismt2_pp(rd1, m_m) << std::endl;);
            expr_ref rhs(m_m), rd1_a(m_m), rd_a(m_m), ix_a(m_m), ix1_a(m_m), lhs(m_m);
            get_abstract(rd1, rd1_a);
            get_abstract(rd, rd_a);
            m_info->abstract(get_ix(rd), ix_a);
            m_info->abstract(get_ix(rd1), ix1_a);
            lhs = mk_and_safe(mk_and_safe(reason, ri1.reason), m_m.mk_eq(ix_a, ix1_a));
            rhs = m_m.mk_eq(rd_a, rd1_a);
            expr * const lemma = m_m.mk_implies(lhs, rhs);
            m_array_lemmas.push_back(lemma);
            TRACE("model_constructor", tout << "array conflict, with lemma" << mk_ismt2_pp(lemma, m_m) << std::endl;);
        }

        bool propagate_read(expr_ref& dest, expr_ref& rd, expr* ix_val, expr_ref& val, expr_ref& reason) {
            if (m_ar_util.is_select(rd) &&  m_ar_util.is_store(dest)) {
                app* const sel = to_app(rd);
                app* const str = to_app(dest);
                expr* const str_ix = str->get_arg(1);
                expr* str_ix_val(NULL);
                const bool chk = eval_cached(str_ix, str_ix_val);
                if (!chk) return false;
                expr_ref new_reason(m_m), sel_ix_a(m_m), str_ix_a(m_m);
                m_info->abstract(sel->get_arg(1), sel_ix_a);
                m_info->abstract(str_ix, str_ix_a);
                if (m_m.are_distinct(str_ix_val, ix_val)) {
                    new_reason = mk_and_safe(reason, m_m.mk_not(m_m.mk_eq(sel_ix_a, str_ix_a)));
                    que_read(str->get_arg(0), rd, val, new_reason);
                } else {
                    expr* store_val(NULL);
                    if (!get_val(str, store_val)) return false;
                    TRACE("model_constructor", tout << "stored value(\n" << mk_ismt2_pp(store_val, m_m, 2) << ")\n";);
                    new_reason = mk_and_safe(reason, m_m.mk_eq(sel_ix_a, str_ix_a));
                    que_read(dest, dest, expr_ref(store_val, m_m), new_reason);
                }
            }
            return true;
        }

        expr2read_info_t* get_read_vals(expr* a) {
            obj_map<expr, expr2read_info_t *>::iterator i = m_read_vals.find_iterator(a);
            expr2read_info_t *retv(NULL);
            if (i == m_read_vals.end()) {
                retv = alloc(expr2read_info_t);
                m_read_vals.insert(a, retv);
                m_m.inc_ref(a);
            }  else{
                retv = i->get_value();
            }
            return retv;
        }

        bool mk_value_select(app* a,
                expr * ix_val,
                expr_ref& result) {
            SASSERT(m_ar_util.is_select(a));
            // get ackermann constant
            app * const ac = m_info->get_abstr(a);
            func_decl * const a_fd = a->get_decl();
            SASSERT(ac->get_num_args() == 0);
            SASSERT(a_fd->get_range() == ac->get_decl()->get_range());
            result = m_abstr_model->get_const_interp(ac->get_decl());
            if (result.get() == NULL) { // TODO: avoid model completion?
                result = m_abstr_model->get_some_value(a_fd->get_range());
            }
            que_read(a->get_arg(0), a, result, expr_ref(NULL, m_m));
            return true;
        }

        void make_value_interpreted_function(app* a,
                expr_ref_vector& values,
                expr_ref& result) {
            const unsigned num = values.size();
            func_decl * const fd = a->get_decl();
            const family_id fid = fd->get_family_id();
            expr_ref term(m_m);
            term = m_m.mk_app(a->get_decl(), num, values.c_ptr());
            m_evaluator->operator() (term, result);
            TRACE("model_constructor",
                tout << "eval(\n" << mk_ismt2_pp(term.get(), m_m, 2) << "\n->"
                << mk_ismt2_pp(result.get(), m_m, 2) << ")\n"; );
            return;
        }
};

lackr_arrays_model_constructor::lackr_arrays_model_constructor(ast_manager& m, ackr_info_ref info)
    : m_imp(0)
    , m_m(m)
    , m_state(UNKNOWN)
    , m_info(info)
    , m_ref_count(0)
    , m_array_lemmas(m)
{}

lackr_arrays_model_constructor::~lackr_arrays_model_constructor() {
    if (m_imp) dealloc(m_imp);
}

bool lackr_arrays_model_constructor::check(model_ref& abstr_model) {
    m_conflicts.reset();
    if (m_imp) {
        dealloc(m_imp);
        m_imp = 0;
    }
    m_imp = alloc(lackr_arrays_model_constructor::imp, m_m, m_info, abstr_model, m_conflicts, m_array_lemmas);
    const bool rv = m_imp->check();
    m_state = rv ? CHECKED : CONFLICT;
    return rv;
}

void lackr_arrays_model_constructor::make_model(model_ref& model) {
    SASSERT(m_state == CHECKED);
    m_imp->make_model(model);
}
