/*++
 Copyright (c) 2016 Microsoft Corporation

 Module Name:

  expr_gen.cpp

 Abstract:


 Author:

 Mikolas Janota (MikolasJanota)

 Revision History:
--*/
#include"expr_gen.h"
#include"bv_rewriter.h"
#include"ast_pp.h"

class expr_gen_imp : public expr_gen {
    public:
        expr_gen_imp(ast_manager& m, unsigned depth, unsigned sz, expr_ref_vector& leafs)
            : m_m(m)
            , m_bv_util(m)
            , m_depth(depth)
            , m_sz(sz)
            , m_leafs(leafs)
            , m_state(0)
            , m_leaf_pos(0)
            , m_cache(NULL, m_m)
        {
            if (m_depth) {
                for (unsigned i = 0; i < 2; ++i)
                    m_subs.push_back(mk_expr_gen(m, depth - 1, sz, leafs));
            }
        }

        virtual ~expr_gen_imp() {
            clean();
        }


        virtual bool gen(expr_ref& out) {
            if (0) {
                out = NULL;
                return false;
            }
            if (m_cache.get() != NULL) {
                out = m_cache;
                return true;
            }

            const bool rv = mk_state(out);
            m_cache = out;
            return rv;
        }

        virtual bool inc(unsigned& budget) {
            bool retv = false;
            bool done = false;
            while (true) {
                //std::cout << "state " << m_state << "@" << m_depth << std::endl;
                unsigned tmp_budget = budget;
                retv |= inc_core(tmp_budget);
                //std::cout << "state' " << m_state << "@" << m_depth << std::endl;
                if (m_state) {
                    expr_ref s0(m_m), s1(m_m);
                    m_subs[0]->gen(s0);
                    m_subs[1]->gen(s1);
                    if (m_state < 3) done = s0->get_id() <= s1->get_id();
                    else done = !m_m.are_equal(s0.get(), s1.get());
                    //if (!done)  std::cout << "skip " << mk_pp(s0.get(), m_m) << ":" << mk_pp(s1.get(), m_m) << std::endl;
                } else {
                    done = true;
                }
                if (done) {
                    budget = tmp_budget;
                    return retv;
                }
            }
        }

        virtual bool inc_core(unsigned& budget) {
            SASSERT(budget);
            bool retv = false;
            bool done = false;
            m_cache = NULL;
            if (budget < (m_subs.size() + 1) || m_depth == 0) m_state = 0;
            switch(m_state) {
                case 0:
                    m_leaf_pos++;
                    if (m_leaf_pos == m_leafs.size()) {
                        m_leaf_pos = 0;
                        ++m_state;
                        if (budget < (m_subs.size() + 1) || m_depth == 0) {
                            m_state = 0;
                            retv = true;
                        } else {
                            budget = budget - m_subs.size() - 1;
                        }
                    } else {
                        --budget;
                    }
                    break;
                case 1:
                case 2:
                case 3:
                    {
                        SASSERT(m_subs.size() == 2);
                        SASSERT(m_depth);
                        unsigned tmp_budget = budget - 1;
                        const bool carry = inc_subs(tmp_budget);
                        if (carry) {
                            m_state++;
                            if (m_state == 4) {
                                retv = true;
                                m_state = 0;
                            }
                            m_leaf_pos = 0;
                        }
                        budget = m_state ? tmp_budget : (budget - 1);
                    }
                    break;
            }
            return retv;
        }


    private:
        ast_manager&          m_m;
        bv_util               m_bv_util;
        unsigned              m_depth;
        unsigned              m_sz;
        expr_ref_vector&      m_leafs;
        unsigned              m_state;
        vector<expr_gen*>     m_subs;
        unsigned              m_leaf_pos;
        expr_ref              m_cache;

        bool inc_subs(unsigned& budget) {
            SASSERT(budget >= m_subs.size());
            bool carry = true;
            expr_ref     tmp(m_m);
            for (unsigned i = 0; carry && i < m_subs.size(); ++i)
                carry = m_subs[i]->inc(budget);
            return carry;
        }

        bool  mk_state(expr_ref& out) {
            expr_ref_vector es(m_m);
            if (m_state) {
                SASSERT(m_subs.size() == 2);
                expr_ref tmp(m_m);
                for (unsigned i = 0; i < m_subs.size(); ++i) {
                    if (!m_subs[tmp]->gen(tmp)) return false;
                    es.push_back(tmp);
                }
            }
            switch(m_state) {
                case 0: out = m_leafs.get(m_leaf_pos); break;
                case 1: out = m_bv_util.mk_bv_add(es.get(0), es.get(1)); break;
                case 2: out = m_bv_util.mk_bv_mul(es.get(0), es.get(1)); break;
                case 3: out = m_bv_util.mk_bv_urem(es.get(0), es.get(1)); break;
                default:
                        UNREACHABLE();
                        out = NULL;
                        return false;
            }
            return true;
        }

        void clean() {
            for (unsigned i=0; i < m_subs.size(); ++i)
                dealloc(m_subs[i]);
        }
};

expr_gen * mk_expr_gen(ast_manager& m, unsigned depth, unsigned sz, expr_ref_vector& leafs) {
    return alloc(expr_gen_imp, m, depth, sz, leafs);
}

void test_expr_gen(ast_manager& m) {
    expr_ref_vector ls(m);
    bv_util  bv_util(m);
    ls.push_back(m.mk_fresh_const("x", bv_util.mk_sort(32)));
    ls.push_back(m.mk_fresh_const("y", bv_util.mk_sort(32)));
    expr_gen* eg = mk_expr_gen(m, 2, 32, ls);
    expr_ref e(m);
    bool done = false;
    const unsigned B = 100;
    while (!done) {
        const bool s = eg->gen(e);
        if (s) std::cout << "gen: " << mk_pp(e.get(), m, 2) << std::endl;
        unsigned budget = B;
        done = (eg->inc(budget));
        if (!done) std::cout << "cost: " << (B - budget) << std::endl;
    };
    dealloc(eg);
}
