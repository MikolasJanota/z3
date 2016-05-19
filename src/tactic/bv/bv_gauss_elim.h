 /*++
 Copyright (c) 2016 Microsoft Corporation

 Module Name:

  bv_gauss_elim.h

 Abstract:


 Author:

 Mikolas Janota

 Revision History:
 --*/
#ifndef BV_GAUSS_ELIM_H_
#define BV_GAUSS_ELIM_H_
#include"ast.h"
#include"bv_decl_plugin.h"
class bv_gauss_elim {
public:
    bv_gauss_elim(ast_manager& m)
        : m_m(m),m_util(m),m_is_consistent(true),m_input_term_count(0),m_output_term_count(0)
    {}

    virtual ~bv_gauss_elim();
    bool is_row(expr * e);
    void add_row(expr * e);
    void elim();
    bool is_consistent () const {return m_is_consistent;}
    unsigned row_count() const { return m_rows.size(); }
    void output(unsigned  row_index, expr_ref& result);
    unsigned input_term_count () const {return m_input_term_count;}
    unsigned output_term_count () const {return m_output_term_count;}
protected:
    typedef rational numeral;
    typedef obj_map<app, numeral> coef_map;
    struct row {
        unsigned bit_width;
        unsigned original_bit_width;
        numeral coef;
        coef_map * coefs;
    };

    struct _row_cmp {
        bool operator() (const row& r1, const row& r2) {
            return r1.bit_width > r2.bit_width;
        }
    } row_cmp;


    ast_manager&  m_m;
    bv_util       m_util;
    vector<row>   m_rows;
    bool          m_is_consistent;
    unsigned      m_input_term_count;
    unsigned      m_output_term_count;

    bool normalize_row(row& r);
    unsigned get_rank(numeral n);
    bool is_term(expr * e);
    bool is_sum(expr * e);
    inline bool is_var(expr * e) { return m_util.is_bv(e) && is_app(e) && to_app(e)->get_num_args() == 0; }
    bool is_term(expr * e, numeral& coef, app_ref& v);
    void add_side(expr* e, bool lhs, row& r);
    void add_term(bool lhs, const numeral& coef, const numeral& modulus, app_ref& v, row& r);

    void elim_defs();
    bool elim_var(const row& r, row& r1, app* pivot_var);
    void make_echelon();

    inline app_ref output_var(app * v, unsigned original_bit_width, unsigned bit_width);

    std::ostream& prn_row(std::ostream& o, const row & r);
};

inline app_ref bv_gauss_elim::output_var(app * v, unsigned original_bit_width, unsigned bit_width) {
    SASSERT(m_util.get_bv_size(v) == original_bit_width);
    SASSERT(bit_width <= original_bit_width);
    const bool changed = original_bit_width != bit_width;
    return app_ref(changed ? m_util.mk_extract(bit_width - 1, 0, v) : v, m_m);
}
#endif /* BV_GAUSS_ELIM_H_ */
