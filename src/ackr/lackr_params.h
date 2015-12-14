/*++
 Copyright (c) 2015 Microsoft Corporation

 Module Name:

  lackr_params.h

 Abstract:


 Author:

 Mikolas Janota

 Revision History:
--*/
#ifndef LACKR_PARAMS_H_16537
#define LACKR_PARAMS_H_16537
#include"params.h"


struct lackr_params {
    bool             m_eager;
    bool             m_sat_backend;
public:
    lackr_params(params_ref const & p = params_ref()) :
        m_eager(true),
        m_sat_backend(false)
    {}

    void updt_params(params_ref const & _p);
};
#endif /* LACKR_PARAMS_H_16537 */
