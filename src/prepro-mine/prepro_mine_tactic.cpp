/*++
 Copyright (c) 2015 Microsoft Corporation

 Module Name:

  prepro_mine_tactic.cpp

 Abstract:


 Author:

 Mikolas Janota

 Revision History:
--*/
#include"prepro_mine_tactic.h"
class prepro_mine_tactic : public tactic {
    ast_manager&    m_m;
    params_ref      m_params;
public:
    prepro_mine_tactic(ast_manager& m, params_ref const& p)
        : m_m(m)
        , m_params(p)
     {}

    virtual void operator()(/* in */  goal_ref const & in,
                            /* out */ goal_ref_buffer & result,
                            /* out */ model_converter_ref & mc,
                            /* out */ proof_converter_ref & pc,
                            /* out */ expr_dependency_ref & core) {
    }

    virtual tactic* translate(ast_manager& m) {
        return alloc(prepro_mine_tactic, m, m_params);
    }

    virtual void cleanup() { }

    inline void checkpoint() {
        //if (m_m.cancel()) throw tactic_exception(TACTIC_CANCELED_MSG);
    }
};

tactic * mk_prepro_mine_tactic(ast_manager& m, params_ref const & p) {
    return alloc(prepro_mine_tactic, m, p);
}
