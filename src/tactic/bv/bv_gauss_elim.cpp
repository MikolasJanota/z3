/*++
 Copyright (c) 2016 Microsoft Corporation

 Module Name:

  bv_gauss_elim.cpp

 Abstract:


 Author:

 Mikolas Janota

 Revision History:
--*/
#include"bv_gauss_elim_tactic.h"
#include"bv_gauss_elim.h"
#include"bv_decl_plugin.h"
#include"ast_pp.h"

bv_gauss_elim::~bv_gauss_elim() {
    vector<row>::iterator end = m_rows.end();
    for (vector<row>::iterator i = m_rows.begin(); end != i; ++i) {
        dealloc(i->coefs);
        i->coefs = NULL;
    }
}

bool bv_gauss_elim::is_term(expr * e, numeral& coef, app_ref& v) {
    unsigned sz;
    v = NULL;
    if (m_util.is_numeral(e, coef, sz)) return true;
    if (is_var(e)) {
        v = to_app(e);
        coef = numeral::one();
        return true;
    }

    expr * l, * r;
    if (!m_util.is_bv_mul(e, l, r)) return false;

    if (m_util.is_numeral(l, coef, sz) && is_var(r)) {
        v = to_app(r);
        return true;
    }

    if (m_util.is_numeral(r, coef, sz) && is_var(l)) {
        v = to_app(l);
        return true;
    }

    return false;
}

bool bv_gauss_elim::is_term(expr * e) {
    if (m_util.is_numeral(e)) return true;
    if (is_var(e)) return true;
    expr * l, * r;
    if (!m_util.is_bv_mul(e, l, r)) return false;
    return (m_util.is_numeral(l) && is_var(r) || m_util.is_numeral(r) && is_var(l));
}

bool bv_gauss_elim::is_sum(expr * e) {
    if (is_term(e)) return true;
    if (!m_util.is_bv_add(e)) return false;
    app * const a = to_app(e);
    for (unsigned i = 0; i < a->get_num_args(); ++i) {
        if (!is_term(a->get_arg(i))) return false;
    }
    return true;
}

void bv_gauss_elim::add_term(bool lhs, const numeral& coef, const numeral& modulus, app_ref& v, row& r) {
    if (v.get() == NULL) {
        r.coef = mod(lhs ? r.coef - coef : r.coef + coef, modulus);
    }
    else {
        coef_map::obj_map_entry * entry = r.coefs->insert_if_not_there2(v.get(), numeral::zero());
        entry->get_data().m_value = mod(lhs ? entry->get_data().m_value + coef :  entry->get_data().m_value - coef, modulus);
    }
}

void bv_gauss_elim::add_row(expr * e) {
    if (!m_is_consistent) return;
    expr * lhs, * rhs;
    const bool chk1 = m_m.is_eq(e, lhs, rhs);
    SASSERT(chk1);
    row r;
    r.coefs = alloc(coef_map);
    r.original_bit_width = m_util.get_bv_size(lhs);
    r.bit_width = m_util.get_bv_size(lhs);
    r.coef = numeral::zero();
    add_side(lhs, true, r);
    add_side(rhs, false, r);
    normalize_row(r);
    m_rows.push_back(r);
    TRACE("bv_gauss_elim", prn_row(tout << "add_row: ", r) << std::endl;);
}

void bv_gauss_elim::mak_echelon() {
  vector<bool> processed(m_rows.size(), false);
  expr_sparse_mark marked;
  while (m_is_consistent) {
      unsigned max_bw = 0;
      bool found_pivot = false;
      unsigned row_index = m_rows.size();
      for (unsigned i = 0; i < m_rows.size(); ++i)  {
          if (processed[i]) continue;
          const row& r = m_rows[i];
          if (r.coefs->empty()) continue;
          if (r.bit_width > max_bw) {
              row_index = i;
              max_bw = r.bit_width;
          }
      }
      if (row_index == m_rows.size()) break;
      TRACE("bv_gauss_elim", prn_row(tout << "pivot row ", m_rows[row_index]) << std::endl;);
      processed[row_index] = true;
      row& r = m_rows[row_index];
      coef_map::iterator end = r.coefs->end();
      app_ref pivot_var(NULL, m_m);
      numeral pivot_coef;
      for (coef_map::iterator i = r.coefs->begin(); end != i; ++i) {
          pivot_coef = i->get_value();
          if (pivot_coef.is_even()) continue;
          pivot_var = i->m_key;
          break;
      }
      SASSERT(pivot_var.get() != NULL);

      TRACE("bv_gauss_elim", tout << "pivot " << pivot_coef << " " << mk_pp(pivot_var, m_m) << std::endl;);

      numeral inv;
      const bool chk = m_util.mult_inverse(pivot_coef, r.bit_width, inv);
      SASSERT(chk);
      const numeral big_mod = numeral::power_of_two(r.bit_width);
      for (coef_map::iterator i = r.coefs->begin(); end != i; ++i)
          i->m_value = mod(i->m_value * inv, big_mod);
      r.coef = mod(r.coef * inv, big_mod);
      TRACE("bv_gauss_elim", prn_row(tout << "normalize by mul by " << inv << ": ", r) << std::endl;);
      for (unsigned j = 0; j < m_rows.size(); ++j)  {
          if (processed[j]) continue;
          row & r1 = m_rows[j];
          SASSERT(r.bit_width >= r1.bit_width);
          numeral c1;
          if (!r1.coefs->find(pivot_var, c1)) continue;
          const numeral small_mod = numeral::power_of_two(r1.bit_width);
          SASSERT(c1 < small_mod);
          const numeral mul = small_mod - c1;
          coef_map::iterator end1 = r1.coefs->end();
          numeral pval;
          TRACE("bv_gauss_elim", tout << "elim row " << j << " mul " << mul << std::endl;);
          marked.reset();
          for (coef_map::iterator i = r1.coefs->begin(); end1 != i; ++i) {
               app* const v = i->m_key;
               if (!r.coefs->find(v, pval)) continue;
               marked.mark(v);
               i->m_value = mod(i->m_value + mul * pval, small_mod);
               TRACE("bv_gauss_elim", tout << "update var " << mk_pp(v, m_m) << " " << i->m_value << std::endl;);
          }
          for (coef_map::iterator i = r.coefs->begin(); end != i; ++i) {
              if (marked.is_marked(i->m_key)) continue;
              const numeral& nv = mod(i->m_value * mul, small_mod);
              r1.coefs->insert(i->m_key, nv);
          }
          r1.coef = mod(r1.coef + mul * r.coef, small_mod);
          SASSERT(r1.coefs->find(pivot_var).is_zero());
          normalize_row(r1);
      }
  }
}

bool bv_gauss_elim::normalize_row(row& r) {
    ptr_buffer<app> torm;
    numeral tmp;
    unsigned min_rank = r.bit_width;
    coef_map::iterator end = r.coefs->end();
    for (coef_map::iterator i = r.coefs->begin(); end != i; ++i) {
        numeral c = i->get_value();
        if (c.is_zero())  {
            torm.push_back(i->m_key);
        } else {
            min_rank = std::min(min_rank, get_rank(c));
        }
    }
    if (min_rank > 0) {
        numeral divisor = numeral::power_of_two(min_rank);
        for (coef_map::iterator i = r.coefs->begin(); end != i; ++i)
            i->m_value = i->get_value() / divisor;
        if (!r.coef.is_zero() && get_rank(r.coef) < min_rank) {
            m_is_consistent = false;
            return false;
        }
        r.coef = r.coef / divisor;
    }
    r.bit_width -= min_rank;
    for (unsigned i = 0; i < torm.size(); ++i) r.coefs->remove(torm[i]);
    if (r.coefs->empty() && !r.coef.is_zero()) m_is_consistent = false;
    return m_is_consistent;
}

void bv_gauss_elim::output(unsigned  row_index, expr_ref& result) {
    const row& r = m_rows[row_index];
    if (r.coefs->empty()) {
        result = r.coef.is_zero() ? m_m.mk_true() : m_m.mk_false();
        return;
    }
    expr_ref_buffer s(m_m);
    coef_map::iterator end = r.coefs->end();
    for (coef_map::iterator i = r.coefs->begin(); end != i; ++i) {
        const numeral c = i->get_value();
        SASSERT(!c.is_zero());
        const bool iso = c == numeral::one();
        expr * const n = iso ? NULL : m_util.mk_numeral(c, r.bit_width);
        expr * const v = r.original_bit_width == r.bit_width ? i->m_key : m_util.mk_extract(r.bit_width - 1, 0, i->m_key);
        s.push_back(iso ? v : m_util.mk_bv_mul(n, v));
    }
    expr * const lhs = s.size() == 1 ? s[0] : m_m.mk_app(m_util.get_fid(), OP_BADD, s.size(), s.c_ptr());
    result = m_m.mk_eq(lhs, m_util.mk_numeral(r.coef, r.bit_width));
}

unsigned bv_gauss_elim::get_rank(numeral n) {
    SASSERT(!n.is_zero());
    const numeral two(2);
    unsigned rv = 0;
    while (n.is_even()) {
      n = n / two;
      ++rv;
    }
    return rv;
}

void bv_gauss_elim::add_side(expr* e, bool lhs, row& r) {
    numeral coef;
    app_ref v(NULL, m_m);
    numeral modulus = numeral::power_of_two(r.original_bit_width);
    if (is_term(e, coef, v)) {
        add_term(lhs, coef, modulus, v, r);
        return;
    }
    SASSERT(m_util.is_bv_add(e));
    app * const a = to_app(e);
    for (unsigned i = 0; i < a->get_num_args(); ++i) {
        const bool chk = is_term(a->get_arg(i), coef, v);
        SASSERT(chk);
        add_term(lhs, coef, modulus, v, r);
    }
}

bool bv_gauss_elim::is_row(expr * e) {
    if (!m_m.is_eq(e)) return false;
    expr * const lhs = to_app(e)->get_arg(0);
    expr * const rhs = to_app(e)->get_arg(1);
    return m_util.is_bv(lhs) && is_sum(lhs) && is_sum(rhs);
}

std::ostream& bv_gauss_elim::prn_row(std::ostream& o, const row & r) {
    coef_map::iterator end = r.coefs->end();
    o << "(";
    for (coef_map::iterator i = r.coefs->begin(); end != i; ++i) {
        o << "+" << i->get_value() << " " << mk_pp(i->m_key, m_m) << " ";
    }
    return o << " = " << r.coef << " [" << r.bit_width << "])";
}

