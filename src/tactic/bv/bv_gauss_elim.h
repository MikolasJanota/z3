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
class bv_gauss_elim {
public:
	bv_gauss_elim(ast_manager& m) : m_m(m) {}
protected:
	ast_manager& m_m;
};
#endif /* BV_GAUSS_ELIM_H_ */
