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
#include"union_find.h"

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
            , m_qued_rds(m)
            , m_qued_vals(m)
            , m_qued_reasons(m)
            , m_uf(m_uf_ctx)
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
                expr2id::iterator i = m_array_ids.begin();
                expr2id::iterator e = m_array_ids.end();
                for (; i != e; ++i) {
                    const unsigned id = i->m_value;
                    expr* const e = i->m_key;
                    const unsigned representative = m_uf.find(id);
                    if (id != representative) continue;
                    expr2read_info_t * t = m_read_vals[id];
                    expr2read_info_t::iterator ti = t->begin();
                    const expr2read_info_t::iterator te = t->end();
                    for (; ti != te; ++ti) {
                        const read_info& ri = ti->m_value;
                        m_m.dec_ref(ti->m_key);
                        m_m.dec_ref(ri.reason);
                        m_m.dec_ref(ri.value);
                        m_m.dec_ref(ri.rd);
                    }
                    dealloc(t);
                }
            }
            {
                expr2id::iterator i = m_array_ids.begin();
                const expr2id::iterator e = m_array_ids.end();
                for (;  i != e; ++i) m_m.dec_ref(i->m_key);
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
                if (_term && m_m.is_eq(_term)) continue;
                expr * const term  = _term ? _term : m_m.mk_const(c);
                if (!check_term(term)) retv = false;
            }

            expr* lhs;
            expr* rhs;
            for (unsigned i = 0; i < m_abstr_model->get_num_constants(); i++) {
                func_decl * const c = m_abstr_model->get_constant(i);
                app * const  term = m_info->find_term(c);
                if (!term) continue;
                if (!m_m.is_eq(term, lhs, rhs)) continue;
                if (!m_m.is_true(m_abstr_model->get_const_interp(c))) continue;
                SASSERT(m_ar_util.is_array(lhs) && m_ar_util.is_array(rhs));
                register_array(lhs);
                register_array(rhs);
                link_arrays(lhs, rhs);
            }

            vector<std::pair<expr*, expr*> >::iterator vsi = m_valued_selects.begin();
            vector<std::pair<expr*, expr*> >::iterator vse = m_valued_selects.begin();
            for ( ; vsi != vse; ++vsi) {
                app * a = to_app(vsi->first);
                SASSERT(m_ar_util.is_select(a));
                expr_ref tmp(vsi->second, m_m);
                que_read(a->get_arg(0), a, tmp, expr_ref(NULL, m_m));
            }

            m_read_vals.resize(m_array_ids.size(), NULL);
            for (unsigned id = 0; id < m_array_ids.size(); ++id) {
                 const unsigned representative = m_uf.find(id);
                 if (m_read_vals[representative] == NULL) {
                    m_read_vals[representative] = alloc(expr2read_info_t);
                 }
                 m_read_vals[id] = m_read_vals[representative];
            }

            expr2id::iterator i = m_array_ids.begin();
            expr2id::iterator e = m_array_ids.end();
            expr_ref null_ref(NULL, m_m);
            expr_ref store_val_ref(NULL, m_m);
            for (; i != e; ++i) {
                expr * const dest = i->m_key;
                if (!m_ar_util.is_store(dest)) continue;
                expr* store_val(NULL);
                if (!get_val(dest, store_val)) continue;
                store_val_ref = store_val;
                TRACE("model_constructor", tout << "stored value(\n" << mk_ismt2_pp(store_val, m_m, 2) << ")\n";);
                que_read(dest, dest, store_val_ref, null_ref);
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
                    TRACE("model_constructor", tout << "entry ("
                            << mk_ismt2_pp(a->get_decl(), m_m, 2)
                            << "->"
                            << mk_ismt2_pp(i->m_value, m_m, 2)
                            << ")\n" ;);
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
            {
                expr2id::iterator i = m_array_ids.begin();
                expr2id::iterator e = m_array_ids.end();
                for (; i != e; ++i) {
                    const unsigned id = i->m_value;
                    expr* const e = i->m_key;
                    if (!is_app(e)) continue;
                    app * const a = to_app(e);
                    if (a->get_num_args() != 0) continue;
                    sort * const  arr_s = a->get_decl()->get_range();
                    SASSERT(get_array_arity(arr_s) == 1);
                    sort * ix_s = get_array_domain(arr_s, 0);
                    sort * const rg_s = get_array_range(arr_s);
                    func_interp * const fi = alloc(func_interp, m_m, 1);
                    expr2read_info_t* const t = m_read_vals[id];
                    expr2read_info_t::iterator ti = t->begin();
                    const expr2read_info_t::iterator te = t->end();
                    expr * args[1];
                    TRACE("model_constructor", tout << "array (\n" << mk_ismt2_pp(a, m_m, 2) << ")\n" ;);
                    for (; ti != te; ++ti) {
                        const read_info& ri = ti->m_value;
                        args[0] = ti->m_key;
                        fi->insert_entry(args, ri.value);
                        TRACE("model_constructor", tout << "entry ("
                                << mk_ismt2_pp(ti->m_key, m_m, 2)
                                << "->"
                                << mk_ismt2_pp(ri.value, m_m, 2)
                                << ")\n" ;);
                    }
                    fi->set_else(m_m.get_some_value(rg_s));
                    sort * dom[1] = { ix_s };
                    func_decl * const fd = m_m.mk_fresh_func_decl(a->get_decl()->get_name(), symbol::null, 1, dom, rg_s);
                    destination->register_decl(fd, fi);
                    parameter p[1] = { parameter(fd) };
                    destination->register_decl(a->get_decl(), m_m.mk_app(m_ar_util.get_family_id(), OP_AS_ARRAY, 1, p));
                }
            }
        }

        void add_entry(app* term, expr* value,
            obj_map<func_decl, func_interp*>& interpretations) {
            if (m_ar_util.is_select(term)) return;
            TRACE("model_constructor", tout << "entry (\n" << mk_ismt2_pp(term, m_m, 2) << '\n' << mk_ismt2_pp(term, m_m, 2)<<'\n'; );
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
        model_ref                       m_abstr_model;
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

        typedef obj_map<expr,unsigned> expr2id;
        expr2id                        m_array_ids;
        vector<expr*>                  m_arrays;
        union_find_default_ctx m_uf_ctx;
        union_find<union_find_default_ctx> m_uf;


        void register_array(expr * a) {
            SASSERT(m_ar_util.is_array(a));
            expr2id::iterator i = m_array_ids.find_iterator(a);
            if (i != m_array_ids.end())  return;
            const unsigned id = m_array_ids.size();
            m_m.inc_ref(a);
            m_array_ids.insert(a, id);
            VERIFY(m_uf.mk_var() == id);
            SASSERT(id == m_arrays.size());
            m_arrays.push_back(a);
            TRACE("model_constructor", tout << "array id(" << mk_ismt2_pp(a, m_m, 2) << "--->"
                    << id << ")\n";);
        }

        //
        // Check and record the value for a given term, given that all arguments are already checked.
        //
        bool mk_value(app * a) {
            if (is_val(a)) return true; // skip numerals
            if (m_ar_util.is_array(a))  {
                register_array(a);
                return true; // skip array values
            }
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

        vector<expr2read_info_t*> m_read_vals;
        vector<unsigned>  m_qued_dests;
        expr_ref_vector   m_qued_rds;
        expr_ref_vector   m_qued_vals;
        expr_ref_vector   m_qued_reasons;
        inline bool inv() const {
            const unsigned sz = m_qued_dests.size();
            return (sz == m_qued_rds.size())
                && (sz == m_qued_vals.size())
                && (sz == m_qued_reasons.size());
        }

        inline unsigned get_representative(expr * e) {
            SASSERT(m_ar_util.is_array(e));
            const unsigned id = m_array_ids.find(e);
            const unsigned rv = m_uf.find(id);
            SASSERT(m_uf.is_root(rv));
            return rv;
        }

        void que_read(expr* dest, expr* rd, expr_ref& val, expr_ref& reason) {
            SASSERT(m_ar_util.is_array(dest));
            SASSERT(inv());
            TRACE("model_constructor", tout << "que_read(\n" << mk_ismt2_pp(dest, m_m, 2)
                    << "," << mk_ismt2_pp(rd, m_m, 2) << "," << mk_ismt2_pp(val, m_m, 2)
                    << "," << ")\n";);
            m_qued_dests.push_back(get_representative(dest));
            m_qued_rds.push_back(rd);
            m_qued_vals.push_back(val);
            m_qued_reasons.push_back(reason);
            SASSERT(inv());
        }

        void pop_read(unsigned& dest, expr_ref& rd, expr_ref& val, expr_ref& reason) {
            SASSERT(m_qued_dests.size());
            SASSERT(inv());
            dest = m_qued_dests.back();
            rd = m_qued_rds.back();
            val = m_qued_vals.back();
            reason = m_qued_reasons.back();
            m_qued_dests.pop_back();
            m_qued_vals.pop_back();
            m_qued_rds.pop_back();
            m_qued_reasons.pop_back();
            TRACE("model_constructor", tout << "pop_read(\n" << dest
                    << "," << mk_ismt2_pp(rd, m_m, 2) << "," << mk_ismt2_pp(val, m_m, 2)
                    << "," << ")\n";);
            SASSERT(inv());
            SASSERT(m_ar_util.is_select(rd) || m_ar_util.is_store(rd));
            SASSERT(m_uf.is_root(dest));
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

        bool get_val(expr* _rd, expr*& res) {
            SASSERT(m_ar_util.is_select(_rd) || m_ar_util.is_store(_rd));
            app * const rd = to_app(_rd);
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

        bool process_read(unsigned dest, expr_ref& rd, expr_ref& val, expr_ref& reason) {
            TRACE("model_constructor",
                    tout << "processing read " << mk_ismt2_pp(rd, m_m, 2) << " : " << dest << "," << mk_ismt2_pp(val.get(), m_m, 2) << ",";
                    if (reason.get()) tout << mk_ismt2_pp(reason.get(), m_m, 2); else tout << "NULL";
                    tout << std::endl;);
            SASSERT(m_uf.is_root(dest));
            unsigned curr = dest;
            expr_ref dest_e(m_m);
            bool rv = record_read(dest, rd, val, reason);
            expr * ix_val(NULL);
            if (!get_ix_val(rd, ix_val)) return false;
            TRACE("model_constructor",tout<<"root " << dest << "\n";);
            do {
                TRACE("model_constructor",tout<<"it " << curr << "\n";);
                dest_e = m_arrays[curr];
                curr = m_uf.next(curr);
                rv = rv & propagate_read(dest_e, rd, ix_val, val, reason);
            } while (curr != dest);
            return rv;
        }

        bool record_read(unsigned dest, expr_ref& rd, expr_ref& val, expr_ref& reason) {
            expr2read_info_t * const rvs = get_read_vals(dest);
            expr * ix_val(NULL);
            if (!get_ix_val(rd, ix_val)) return false;
            TRACE("model_constructor",
                    tout << "record_read("
                    << "rd: " << mk_ismt2_pp(rd, m_m) << std::endl
                    << "ix_val: " << mk_ismt2_pp(ix_val, m_m) << std::endl
                    << "val: " << mk_ismt2_pp(val, m_m) << std::endl;
                    );
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
            return true;
        }

        bool process_read_que() {
            unsigned dest(-1);
            expr_ref rd(m_m);
            expr_ref val(m_m);
            expr_ref reason(m_m);
            bool retv = true;
            while (m_qued_dests.size()) {
                pop_read(dest, rd, val, reason);
                if (!process_read(dest, rd, val, reason)) retv = false;
            }
            return retv;
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

        void link_arrays(expr* a, expr* b) {
            SASSERT(m_ar_util.is_array(a));
            SASSERT(m_ar_util.is_array(b));
            TRACE("model_constructor", tout << "linking arrays(\n" 
                    << mk_ismt2_pp(a, m_m, 2) << "\n"
                    << mk_ismt2_pp(b, m_m, 2) << ")\n";);
            const unsigned id_a = m_array_ids.find(a);
            const unsigned id_b = m_array_ids.find(b);
            m_uf.merge(id_a, id_b);
        }

        inline expr2read_info_t* get_read_vals(unsigned id) {
            return m_read_vals[id];
        }

        vector<std::pair<expr*, expr*> > m_valued_selects;

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
            m_valued_selects.push_back(std::make_pair(a, result.get()));
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
    m_array_lemmas.reset();
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
