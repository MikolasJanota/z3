/*++
 Copyright (c) 2016 Microsoft Corporation

 Module Name:

  bv_ternary_simplifier.cpp

 Abstract:


 Author:

 Mikolas Janota (MikolasJanota)

 Revision History:
--*/
#include"bv_ternary_simplifier.h"
#include"rewriter_params.hpp"
#include"bool_rewriter.h"
#include"bv_rewriter.h"
#include"ast_smt2_pp.h"
#include"cooperate.h"
#include"ast_util.h"
#include"well_sorted.h"
#include"rewriter_def.h"
#include"lbool.h"
#include"ref.h"


class tvec {
public:
    tvec() : m_data(0), m_ref_count(0), m_size(0) {}

    tvec(vector<lbool>::const_iterator b, unsigned size)
        : m_data(0), m_ref_count(0), m_size(size)
    {
        m_data = static_cast<lbool*>(memory::allocate(sizeof(lbool) * size));
        for (unsigned i = 0; i < size; ++i,++b) m_data[i] = *b;
    }

    ~tvec() {
        if (m_data) memory::deallocate(m_data);
    }

    inline unsigned size() const {
        return m_size;
    }

    inline lbool get(unsigned i) const {
        SASSERT(i < m_size);
        return m_data[i];
    }

    inline lbool operator[] (unsigned i) const {
        return get(i);
    }

    void inc_ref() {
        SASSERT(m_ref_count < UINT_MAX);
        m_ref_count++;
    }

    void dec_ref() {
        SASSERT(m_ref_count > 0);
        m_ref_count--;
    }
private:
    lbool *    m_data;
    unsigned   m_ref_count;
    unsigned   m_size;
};


typedef ref<tvec> tvec_ref;

std::ostream & operator<<(std::ostream & target, const tvec_ref& r) {
    target << '[';
    unsigned i = r->size();
    while(i--) {
        switch (r->get(i))
        {
        case l_false: target << '0'; break;
        case l_true: target << '1'; break;
        case l_undef: target << '*'; break;
        default:
            UNREACHABLE();
            break;
        }
    }
    return target << ']';
}

class tvec_maker {
public:
    tvec_maker(ast_manager & m) : m_bv_util(m) {
    }
    virtual ~tvec_maker() {}
    tvec_ref mk_num(app * n);
    tvec_ref mk_num(rational r, unsigned sz);
    tvec_ref mk_undef(unsigned sz);
    tvec_ref mk_concat(func_decl * f, unsigned num, expr * const * args, unsigned depth);
    tvec_ref mk_and(func_decl * f, unsigned num, expr * const * args, unsigned depth);
    tvec_ref mk_or(func_decl * f, unsigned num, expr * const * args, unsigned depth);
    tvec_ref mk_concat(const tvec_ref&  v1, const tvec_ref&  v2);
    tvec_ref mk_extract(unsigned low, unsigned hi, const tvec_ref&  body);
    tvec_ref mk_add(const tvec_ref&  v1, const tvec_ref&  v2);
    tvec_ref mk_mul(const tvec_ref&  v1, const tvec_ref&  v2);
    tvec_ref mk_udiv(const tvec_ref&  v1, const tvec_ref&  v2);
    tvec_ref mk_urem(tvec_ref&  v1, tvec_ref&  v2);
    lbool    is_ule(const tvec_ref&  v1, const tvec_ref&  v2) const;
    lbool    is_sle(const tvec_ref&  v1, const tvec_ref&  v2) const;
    lbool    is_eq(const tvec_ref&  v1, const tvec_ref&  v2) const;

    lbool     check(func_decl * f, unsigned num, expr * const * args);
    tvec_ref  mk_tvec(expr* e, unsigned depth);
    ast_manager& m()  const { return m_bv_util.get_manager(); }
private:
    vector<lbool>                    m_tmp;
    bv_util                          m_bv_util;

    inline void clean() {
        m_tmp.reset();
    }

    inline tvec_ref mk(unsigned sz) {
        SASSERT(sz == m_tmp.size());
        tvec_ref rv(alloc(tvec, m_tmp.begin(), sz));
        clean();
        SASSERT(m_tmp.empty());
        TRACE("bv_ternary", tout << "mk: " << rv << std::endl;);
        return rv;
    }

    template<bool Signed>
    lbool    is_le(const tvec_ref&  v1, const tvec_ref&  v2) const;

    bool find_hi_nz_bit(const tvec_ref& v,
        unsigned& hi_bit_pos,
        lbool& hi_bit_val);
    bool find_hi_bit(const tvec_ref& v, unsigned& hi_bit_pos);

    template<lbool Id_val, lbool Ctrl_val>
    tvec_ref mk_bitwise(func_decl * f, unsigned num, expr * const * args, unsigned depth);
};

bool tvec_maker::find_hi_bit(const tvec_ref& v, unsigned& hi_bit_pos) {
    hi_bit_pos = v->size();
    while (hi_bit_pos--) {
        if (v->get(hi_bit_pos) == l_true) return true;
    }
    return false;
}

bool tvec_maker::find_hi_nz_bit(const tvec_ref& v,
    unsigned& hi_bit_pos,
    lbool& hi_bit_val) {
    hi_bit_pos = v->size();
    while (hi_bit_pos--) {
        hi_bit_val = v->get(hi_bit_pos);
        if (hi_bit_val != l_false) return true;
    }
    return false;
}

template<bool Signed>
lbool tvec_maker::is_le(const tvec_ref&  v1, const tvec_ref&  v2) const {
    SASSERT(v1->size() > 0);
    SASSERT(v1->size() == v2->size());
    const unsigned sz = v1->size();
    if (Signed) {
        const lbool s1 = v1->get(sz - 1);
        const lbool s2 = v2->get(sz - 1);
        if (s1 == l_undef || s2 == l_undef) return l_undef;
        if (s1 == l_true && s2 == l_false) return l_true;
        if (s1 == l_false && s2 == l_true) return l_false;
        SASSERT(s1 == s2 && s1 != l_undef);
    }
    unsigned i = Signed ? sz - 1 : sz;
    bool can_be_t = false;
    bool can_be_f = false;
    while (i--) {
        const lbool b1 = v1->get(i);
        const lbool b2 = v2->get(i);
        if (b1 == l_undef || b2 == l_undef) {
            switch (b1) {
            case l_false: can_be_t = true; break;
            case l_true:  can_be_f = true; break;
            case l_undef:
                switch (b2) {
                case l_false: can_be_f = true; break;
                case l_true:  can_be_t = true; break;
                case l_undef:
                    can_be_t = true;
                    can_be_f = true;
                }
            }
        }
        else {
            if (b1 == l_true  && b2 == l_false) return can_be_t ? l_undef : l_false;
            if (b1 == l_false && b2 == l_true) return can_be_f ? l_undef : l_true;
        }
    }
    return can_be_f ? l_undef : l_true;
}

lbool tvec_maker::is_eq(const tvec_ref&  v1, const tvec_ref&  v2) const {
    SASSERT(v1->size() == v2->size());
    unsigned i = v1->size();
    bool def_true = true;
    while (i--) {
        const lbool b1 = v1->get(i);
        const lbool b2 = v2->get(i);
        if (b1 == l_undef || b2 == l_undef) {
            def_true = false;
        }
        else {
            if (b1 != b2) return l_false;
        }
    }
    return def_true ? l_true : l_undef;
}

lbool tvec_maker::is_ule(const tvec_ref&  v1, const tvec_ref&  v2) const {
    return is_le<false>(v1, v2);
}

lbool tvec_maker::is_sle(const tvec_ref&  v1, const tvec_ref&  v2) const {
    return is_le<true>(v1, v2);
}

tvec_ref tvec_maker::mk_num(app * n) {
    rational val;
    unsigned sz;
    const bool c = m_bv_util.is_numeral(n, val, sz);
    SASSERT(c);
    return mk_num(val, sz);
}

tvec_ref tvec_maker::mk_num(rational val, unsigned sz) {
    TRACE("bv_ternary", tout << "mk_num: " << val << ":" << sz << std::endl;);
    const rational two(2);
    unsigned i = sz;
    while (i--) {
        m_tmp.push_back(val.is_even() ? l_false : l_true);
        val = div(val, two);
    }
    return mk(sz);
}

tvec_ref tvec_maker::mk_undef(unsigned sz) {
    unsigned i = sz;
    while (i--) m_tmp.push_back(l_undef);
    return mk(sz);
}

tvec_ref tvec_maker::mk_extract(unsigned low, unsigned hi, const tvec_ref&  body) {
    const unsigned sz = body->size();
    SASSERT(low <= hi && hi < sz);
    for (unsigned i = low; i <= hi; i++)
        m_tmp.push_back(body->get(i));
    return mk(hi - low + 1);
}

tvec_ref tvec_maker::mk_concat(const tvec_ref&  v1, const tvec_ref&  v2) {
    for (unsigned i = 0; i < v2->size(); i++) m_tmp.push_back(v2->get(i));
    for (unsigned i = 0; i < v1->size(); i++) m_tmp.push_back(v1->get(i));
    return mk(v1->size() + v2->size());
}

template<lbool Id_val, lbool Ctrl_val>
tvec_ref tvec_maker::mk_bitwise(func_decl * f, unsigned num, expr * const * args, unsigned depth) {
    vector<tvec_ref> vs;
    for (unsigned i = 0; i < num; ++i) {
        vs.push_back(mk_tvec(args[i], depth));
        SASSERT(!i || vs[i]->size() == vs[i - 1]->size());
    }

    unsigned sz = num ? vs[0]->size() : m_bv_util.get_bv_size(f->get_range());
    for (unsigned i = 0; i < sz; ++i) {
        lbool val = Id_val;
        for (unsigned j = 0; j < num; ++j) {
            const lbool b = vs[j]->get(i);
            if (val == Id_val && b == Id_val) val = Id_val;
            else if (val == Ctrl_val || b == Ctrl_val) val = Ctrl_val;
            else val = l_undef;
            if (val == Ctrl_val) break;
        }
        m_tmp.push_back(val);
    }
    return mk(sz);
}

tvec_ref tvec_maker::mk_and(func_decl * f, unsigned num, expr * const * args, unsigned depth) {
    SASSERT(f->get_decl_kind() == OP_BAND);
    return mk_bitwise<l_true,l_false>(f, num, args, depth);
}

tvec_ref tvec_maker::mk_or(func_decl * f, unsigned num, expr * const * args, unsigned depth) {
    SASSERT(f->get_decl_kind() == OP_BOR);
    return mk_bitwise<l_false,l_true>(f, num, args, depth);
}

tvec_ref tvec_maker::mk_concat(func_decl * f, unsigned num, expr * const * args, unsigned depth) {
    SASSERT(f->get_decl_kind() == OP_CONCAT);
    unsigned sz = 0;
    vector<tvec_ref> vs;
    for (unsigned i = 0; i < num; ++i) vs.push_back(mk_tvec(args[i], depth));
    unsigned i = num;
    while (i--) {
        const tvec_ref v = vs[i];
        for (unsigned j = 0; j < v->size(); j++) m_tmp.push_back(v->get(j));
        sz += v->size();
    }
    return mk(sz);
}

tvec_ref tvec_maker::mk_mul(const tvec_ref&  v1, const tvec_ref&  v2) {
    SASSERT(v1->size() == v2->size());
    SASSERT(v1->size());
    unsigned hbp1, hbp2;
    lbool    hbv1, hbv2;
    const unsigned sz = v1->size();
    const bool nz1 = find_hi_nz_bit(v1, hbp1, hbv1);
    const bool nz2 = find_hi_nz_bit(v2, hbp2, hbv2);
    if (!nz1 || !nz2) return mk_num(rational::zero(), sz);
    SASSERT(hbv1 != l_false && hbv2 != l_false);
    const unsigned hbp = hbp1 + hbp2;
    if (hbp >= sz) return mk_undef(sz);
    const lbool    hbv = (hbv1 == hbv2) ? hbv1 : l_undef;
    for (unsigned i = 0; i < hbp; ++i) m_tmp.push_back(l_undef);
    m_tmp.push_back(hbv);
    for (unsigned i = hbp + 1; i < sz; ++i) m_tmp.push_back(l_false);
    return mk(sz);
}

tvec_ref tvec_maker::mk_udiv(const tvec_ref&  v1, const tvec_ref&  v2) {
    SASSERT(v1->size() == v2->size());
    SASSERT(v1->size());
    unsigned nzp1, nzp2, hp1, hp2;
    lbool    nzv1, nzv2;
    const unsigned sz = v1->size();
    const bool nz1 = find_hi_nz_bit(v1, nzp1, nzv1);
    const bool nz2 = find_hi_nz_bit(v2, nzp2, nzv2);
    const bool h1 = find_hi_bit(v1, hp1);
    const bool h2 = find_hi_bit(v2, hp2);
    if (!h2) return mk_undef(sz); // TODO Different handling, div0?
    if (!nz1) return mk_num(rational::zero(), sz);
    if (h2 && (nzp1 < hp2)) return mk_num(rational::zero(), sz);
    const bool has1 = h1 && (hp1 >= nzp2);
    for (unsigned i = 0; i < sz; ++i) {
        lbool b;
        if (has1 && i == (hp1 - nzp2)) b = l_true;
        else if (h2 && i > (nzp1 - hp2)) b = l_false;
        else b = l_undef;
        m_tmp.push_back(b);
    }
    const tvec_ref rv = mk(sz);
    TRACE("bv_ternary", tout << "mk_udiv: " << v1 << ":" << v2 << "=" << rv << std::endl;);
    return rv;
}


tvec_ref tvec_maker::mk_urem(tvec_ref&  v1, tvec_ref&  v2) {
    SASSERT(v1->size() == v2->size());
    SASSERT(v1->size());
    unsigned nzp1, nzp2, hp1, hp2;
    lbool    nzv1, nzv2;
    const unsigned sz = v1->size();
    const bool nz1 = find_hi_nz_bit(v1, nzp1, nzv1);
    const bool nz2 = find_hi_nz_bit(v2, nzp2, nzv2);
    const bool h1 = find_hi_bit(v1, hp1);
    const bool h2 = find_hi_bit(v2, hp2);
    if (!h2) return mk_undef(sz); // TODO div 0 Different handling?
    if (!nz1) return mk_num(rational::zero(), sz); // 0 / rhs
    tvec_ref rv;
    if (nzp1 < hp2) {// rhs bigger than lhs, urem has no effect
         rv = v1;
    } else {
         // result at most as big as rhs
         for (unsigned i = 0; i <= nzp2; ++i) m_tmp.push_back(l_undef);
         for (unsigned i = nzp2+1; i < sz; ++i) m_tmp.push_back(l_false);
         rv = mk(sz);
    }
    TRACE("bv_ternary", tout << "mk_urem: " << v1 << ":" << v2 << "=" << rv << std::endl;);
    return rv;
}


tvec_ref tvec_maker::mk_add(const tvec_ref&  v1, const tvec_ref&  v2) {
    SASSERT(v1->size() == v2->size());
    const unsigned sz = v1->size();
    lbool c = l_false;
    for (unsigned i = 0; i < sz; i++) {
        const lbool b1 = v1->get(i);
        const lbool b2 = v2->get(i);
        unsigned t(0);
        unsigned u(0);
        if (c  == l_true) ++t;
        if (b1 == l_true) ++t;
        if (b2 == l_true) ++t;
        if (c  == l_undef) ++u;
        if (b1 == l_undef) ++u;
        if (b2 == l_undef) ++u;
        m_tmp.push_back(u ? l_undef : ((t & 1) ? l_true : l_false));
        const unsigned lo = t;
        const unsigned hi = lo + u;
        if (lo > 1) c = l_true;
        else if (hi <= 1) c = l_false;
        else c = l_undef;
    }
    const tvec_ref rv = mk(sz);
    TRACE("bv_ternary", tout << "mk_add: " << v1 << ":" << v2 << "=" << rv << std::endl;);
    return rv;
}

tvec_ref tvec_maker::mk_tvec(expr* e, unsigned depth) {
    TRACE("bv_ternary", tout << "mk_tvec: " << mk_ismt2_pp(e, m()) << std::endl;);
    const unsigned sz = m_bv_util.get_bv_size(e);
    if (!depth || !is_app(e)) return mk_undef(sz);
    --depth;
    app* a = to_app(e);
    const decl_kind kind = a->get_decl()->get_decl_kind();
    const unsigned num = a->get_num_args();
    //SASSERT(a->get_family_id() == m_bv_util.get_fid());
    if (m_bv_util.is_numeral(a)) {
        tvec_ref nr = mk_num(a);
        TRACE("bv_ternary", tout << "mk_tvec: " << mk_ismt2_pp(e, m()) << ":" << nr << std::endl;);
        return nr;
    }
    if (m_bv_util.is_bv_add(a)) {
        SASSERT(a->get_num_args() > 0);
        tvec_ref rv = mk_tvec(a->get_arg(0), depth);
        for (unsigned i = 1; i < num; ++i) {
            tvec_ref tmp = mk_tvec(a->get_arg(i), depth);
            rv = mk_add(rv, tmp);
        }
        return rv;
    }
    if (m_bv_util.is_bv_mul(a)) {
        SASSERT(a->get_num_args() > 0);
        tvec_ref rv = mk_tvec(a->get_arg(0), depth);
        for (unsigned i = 1; i < num; ++i) {
            tvec_ref tmp = mk_tvec(a->get_arg(i), depth);
            rv = mk_mul(rv, tmp);
        }
        return rv;
    }

    {
        expr* body;
        unsigned low, high;
        if (m_bv_util.is_extract(a, low, high, body)) {
            const tvec_ref b = mk_tvec(body, depth);
            return mk_extract(low, high, b);
        }
    }

    if (m_bv_util.is_bv_and(a)) {
        return mk_and(a->get_decl(), num, a->get_args(), depth);
    }
    if (m_bv_util.is_bv_or(a)) {
        return mk_or(a->get_decl(), num, a->get_args(), depth);
    }

    if (m_bv_util.is_concat(a)) {
        return mk_concat(a->get_decl(), num, a->get_args(), depth);
    }
    if (a->get_family_id() == m_bv_util.get_family_id()) {
        switch (kind)
        {
        case OP_BIT0: return mk_num(rational::zero(), 1);
        case OP_BIT1: return mk_num(rational::one(), 1);
        case OP_BUDIV_I:
            SASSERT(num == 2);
            tvec_ref a0 = mk_tvec(a->get_arg(0), depth);
            tvec_ref a1 = mk_tvec(a->get_arg(1), depth);
            if (kind == OP_BUDIV_I) return mk_udiv(a0, a1);
            if (kind == OP_BUREM_I) return mk_urem(a0, a1);
            break;
        }
    }
    return mk_undef(sz);
}

lbool tvec_maker::check(func_decl * f, unsigned num, expr * const * args) {
    ///SASSERT(a->get_family_id() == m_bv_util.get_family_id());
    const unsigned depth(3);
    if (!num) return l_undef;
    if (m().get_sort(args[0])->get_family_id() != m_bv_util.get_fid()) return l_undef;
    switch (f->get_decl_kind()) {
    case OP_ULEQ: {
        const tvec_ref a0 = mk_tvec(args[0], depth);
        const tvec_ref a1 = mk_tvec(args[1], depth);
        const lbool uler = is_ule(a0, a1);
        TRACE("bv_ternary", tout << "ule: " << a0 << " " << a1  << "=" << uler << std::endl;);
        return uler;
    }
    case OP_SLEQ: {
        const tvec_ref a0 = mk_tvec(args[0], depth);
        const tvec_ref a1 = mk_tvec(args[1], depth);
        const lbool uler = is_sle(a0, a1);
        TRACE("bv_ternary", tout << "sle: " << a0 << " " << a1 << "=" << uler << std::endl;);
        return uler;
    }
    case OP_EQ: {
        const tvec_ref a0 = mk_tvec(args[0], depth);
        const tvec_ref a1 = mk_tvec(args[1], depth);
        const lbool eqr = is_eq(a0, a1);
        TRACE("bv_ternary", tout << "eq: " << a0 << " " << a1 << "=" << eqr << std::endl;);
        return eqr;
    }
    default: return l_undef;
    }
}


struct bv_ternary_simplifier_cfg : public default_rewriter_cfg {
    bool_rewriter       m_b_rw;
    bv_rewriter         m_bv_rw;
    bv_util             m_bv_util;
    unsigned long long  m_max_memory; // in bytes
    unsigned            m_max_steps;
    bool                m_flat;
    bool                m_cache_all;
    bv_ternary_stats&   m_stats;

    ast_manager & m() const { return m_b_rw.m(); }

    void updt_local_params(params_ref const & _p) {
        rewriter_params p(_p);
        m_flat = p.flat();
        m_max_memory = megabytes_to_bytes(p.max_memory());
        m_max_steps = p.max_steps();
        m_cache_all = p.cache_all();
    }

    void updt_params(params_ref const & p) {
        m_b_rw.updt_params(p);
        m_bv_rw.updt_params(p);
        updt_local_params(p);
    }

    bool flat_assoc(func_decl * f) const {
        if (!m_flat) return false;
        family_id fid = f->get_family_id();
        if (fid == null_family_id)
            return false;
        decl_kind k = f->get_decl_kind();
        if (fid == m_b_rw.get_fid())
            return k == OP_AND || k == OP_OR;
        if (fid == m_bv_rw.get_fid())
            return k == OP_BADD || k == OP_BOR || k == OP_BAND || k == OP_BXOR;
        return false;
    }

    bool rewrite_patterns() const { return false; }

    bool cache_all_results() const { return m_cache_all; }

    bool max_steps_exceeded(unsigned num_steps) const {
        cooperate("bv_ternary_simplifier");
        if (memory::get_allocation_size() > m_max_memory)
            throw rewriter_exception(Z3_MAX_MEMORY_MSG);
        return num_steps > m_max_steps;
    }

    br_status reduce_app_core(func_decl * f, unsigned num, expr * const * args, expr_ref & result) {
        family_id fid = f->get_family_id();
        if (fid == null_family_id)
            return BR_FAILED;
        br_status st = BR_FAILED;
        tvec_maker tm(m());
        const lbool r = tm.check(f, num, args);
        if (r != l_undef) (m_stats.m_simps)++;
        switch (r) {
        case l_false:
            result = m().mk_false();
            return BR_DONE;
        case l_true:
            result = m().mk_true();
            return BR_DONE;
        case l_undef:
            return BR_FAILED;
        }
        return BR_FAILED;
    }

    br_status reduce_app(func_decl * f, unsigned num, expr * const * args, expr_ref & result, proof_ref & result_pr) {
        result_pr = 0;
        br_status st = reduce_app_core(f, num, args, result);
        if (st != BR_DONE && st != BR_FAILED) {
            CTRACE("bv_ternary_simplifier_step", st != BR_FAILED,
                tout << f->get_name() << "\n";
            for (unsigned i = 0; i < num; i++) tout << mk_ismt2_pp(args[i], m()) << "\n";
            tout << "---------->\n" << mk_ismt2_pp(result, m()) << "\n";);
            return st;
        }
        CTRACE("bv_ternary_simplifier_step", st != BR_FAILED,
            tout << f->get_name() << "\n";
        for (unsigned i = 0; i < num; i++) tout << mk_ismt2_pp(args[i], m()) << "\n";
        tout << "---------->\n" << mk_ismt2_pp(result, m()) << "\n";);
        return st;
    }


    bv_ternary_simplifier_cfg(ast_manager & m, params_ref const & p, bv_ternary_stats& stats) :
        m_b_rw(m, p),
        m_bv_rw(m, p),
        m_bv_util(m),
        m_stats(stats)
    {
        updt_local_params(p);
    }

};

template class rewriter_tpl<bv_ternary_simplifier_cfg>;

struct bv_ternary_simplifier::imp : public rewriter_tpl<bv_ternary_simplifier_cfg> {
    bv_ternary_simplifier_cfg m_cfg;
    imp(ast_manager & m, params_ref const & p, bv_ternary_stats& stats) :
        rewriter_tpl<bv_ternary_simplifier_cfg>(m, m.proofs_enabled(), m_cfg),
        m_cfg(m, p, stats) {
    }
};

bv_ternary_simplifier::bv_ternary_simplifier(ast_manager & m, params_ref const & p, bv_ternary_stats& stats) :
    m_params(p),
    m_stats(stats)
{
    m_imp = alloc(imp, m, p, m_stats);
}

ast_manager & bv_ternary_simplifier::m() const {
    return m_imp->m();
}

void bv_ternary_simplifier::updt_params(params_ref const & p) {
    m_params = p;
    m_imp->cfg().updt_params(p);
}

void bv_ternary_simplifier::get_param_descrs(param_descrs & r) {
    bool_rewriter::get_param_descrs(r);
    bv_rewriter::get_param_descrs(r);
    rewriter_params::collect_param_descrs(r);
}

bv_ternary_simplifier::~bv_ternary_simplifier() {
    dealloc(m_imp);
}

unsigned bv_ternary_simplifier::get_cache_size() const {
    return m_imp->get_cache_size();
}

unsigned bv_ternary_simplifier::get_num_steps() const {
    return m_imp->get_num_steps();
}

void bv_ternary_simplifier::collect_statistics(statistics & st) const {
   st.update("bv ternary simps", m_stats.m_simps);
}

void bv_ternary_simplifier::reset_statistics() {
    m_stats.m_simps = 0;
}


void bv_ternary_simplifier::cleanup() {
    ast_manager & m = m_imp->m();
    dealloc(m_imp);
    m_imp = alloc(imp, m, m_params, m_stats);
}

void bv_ternary_simplifier::reset() {
    m_imp->reset();
    m_imp->cfg().reset();
}

void bv_ternary_simplifier::operator()(expr_ref & term) {
    expr_ref result(term.get_manager());
    m_imp->operator()(term, result);
    term = result;
}

void bv_ternary_simplifier::operator()(expr * t, expr_ref & result) {
    m_imp->operator()(t, result);
}

void bv_ternary_simplifier::operator()(expr * t, expr_ref & result, proof_ref & result_pr) {
    m_imp->operator()(t, result, result_pr);
}
