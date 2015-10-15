#include"q2_tactic.h"
#include"qfbv_tactic.h"
#include"expr_substitution.h"
#include"expr_replacer.h"
#include"extension_model_converter.h"
#include"solver.h"
#include"array.h"
#include"tactic2solver.h"
#include"decl_collector.h"
#include"ast_util.h"
#include"quant_hoist.h"
#include"inc_sat_solver.h"
#include"simplifier.h"
#include"bv_simplifier_plugin.h"
#include"nnf_tactic.h"
#include"macro_finder_tactic.h"
#include"ufbv_tactic.h"
#include"model_smt2_pp.h"

using std::cout;
using std::endl;

class q2_tactic : public tactic {
public:
	q2_tactic(ast_manager& m, params_ref const& p)
		: m_m(m)
		, m_p(p)
	{}

	//ptr_vector<decl> cand_decls;
	
	virtual void operator()(goal_ref const & g,
		goal_ref_buffer & result,
		model_converter_ref & mc,
		proof_converter_ref & pc,
		expr_dependency_ref & core) {
		// conjoin goal
		ast_manager& m = g->m();		
		ptr_vector<expr> fmls;
		g->get_formulas(fmls);
		expr_ref const in_f(mk_and(m, fmls.size(), fmls.c_ptr()),m);

		cout << "fla:\n" << mk_ismt2_pp(in_f, m, 0) << endl;

		//get free
		decl_collector dc(m);
		dc.visit(in_f);
		//const func_decl * const * dcs = dc.get_func_decls();
		sort_ref_vector sts1(m);
		expr_ref_vector aux1(m);
		unzip_decl(m,dc.get_func_decls(), dc.get_num_decls(), sts1, aux1);
		unzip_decl(m,dc.get_pred_decls(), dc.get_num_preds(), sts1, aux1);
		// get matrix and forall quant
		quantifier_hoister hoister(m);
		expr_ref matrix(m);		
		bool is_f;
		app_ref_vector aux2(m);
		hoister(in_f,aux2,is_f,matrix);
		SASSERT(is_f||aux2.empty());		
		//
		for (unsigned i = 0; i < aux1.size(); ++i)
			cout << "F " << mk_ismt2_pp(aux1[i].get(), m, 0) << endl;
		for (unsigned i = 0; i < aux2.size(); ++i) 
			cout << "A " << mk_ismt2_pp(aux2[i].get(), m, 0) << endl;

		
		//
		const lbool o = cegar(m,aux1,aux2,matrix);
		goal_ref resg(alloc(goal, *g, true));		
		if (o == l_false) resg->assert_expr(m.mk_false());
		if (o != l_undef) result.push_back(resg.get());
	}

	virtual void cleanup() { }

	virtual tactic* translate(ast_manager& m) {
		return alloc(q2_tactic, m, m_p);
	}

	inline solver* mk_sat_solver(ast_manager& m, params_ref& p) {
		//cout << "ufbv solver" << endl;
		//tactic_ref cext = mk_ufbv_tactic(m, p);
		//solver* rv = mk_tactic2solver(m, cext.get(), m_p);
		//SASSERT(rv);
		//rv->set_produce_models(true);
		//return rv;
		//tactic_ref cext = mk_qfbv_tactic(m, p);
		//scoped_ptr<solver> cex_sat = mk_tactic2solver(m, cext.get(), m_p);
		return  mk_inc_sat_solver(m, p);		
	}

	void unzip_decl(ast_manager& m,
		//const func_decl * const * dcs,
		func_decl * const * dcs,
		unsigned count,
		sort_ref_vector& sts1,
		expr_ref_vector& aux1) {
		for (unsigned i = 0; i < count; ++i) {
			//const 
			func_decl * const fd = dcs[i];
			cout << "decl :" << mk_ismt2_pp(fd, m, 0) << endl;
			cout << fd->get_name() << ":" << mk_ismt2_pp(fd->get_range(), m, 0) << endl;
			SASSERT(fd->get_arity() == 0);
			sort_ref s(fd->get_range(), m);
			expr_ref c(m.mk_const(fd->get_name(), s), m);
			aux1.push_back(c);
			sts1.push_back(s);
			//cand_decls.push_back(fd);
		}
	}



	lbool cegar(
		ast_manager& m,
		expr_ref_vector& aux1,
		app_ref_vector& aux2,
		expr_ref _matrix) {
		//////////////
		simplifier simp(m);
		basic_simplifier_plugin bsp(m);
		bv_simplifier_params bv_par;
		bv_simplifier_plugin bvsp(m, bsp, bv_par);
		simp.register_plugin(&bsp);
		simp.register_plugin(&bvsp);
		simp.enable_ac_support(true);
        //
		expr_ref matrix(m);
		proof_ref dp(m);
		simp(_matrix, matrix, dp);
		//cout << "mx:\n" << mk_ismt2_pp(matrix, m, 0) << endl;
		//
		expr_ref ncmx(m.mk_not(matrix), m);
		scoped_ptr<solver> cex_sat(mk_sat_solver(m, m_p));
		cex_sat->assert_expr(ncmx);
		//////////////
		////////////////
		scoped_ptr<solver> sat(mk_sat_solver(m, m_p));
		expr_substitution cex(m);
		expr_ref_vector ini_cex(m);
		for (unsigned i = 0; i < aux2.size(); ++i) {
			SASSERT(aux2[i]->get_decl()->get_arity() == 0);
			sort * const s = aux2[i]->get_decl()->get_range();
			expr_ref v(m.get_some_value(s), m);
			ini_cex.push_back(v);
			cex.insert(aux2[i].get(), v);
			//cout << "init cex: " << mk_ismt2_pp(aux2[i].get(), m, 0) << " " << mk_ismt2_pp(v, m, 0) << endl;
		}
		scoped_ptr<expr_replacer> rer(mk_default_expr_replacer(m));
		lbool o = l_undef;
		expr_ref_vector cand(m);
		ptr_vector<expr> assum(aux1.size());
        //////////////////
		int count = 0;
		while (1) {
			cout << "it: " << ++count << endl;
			expr_ref ref0(m),ref(m);
			rer->set_substitution(&cex);
			(*rer)(matrix, ref0);//calculate refinement		
			proof_ref dummy(m);
			simp(ref0, ref, dummy);			
			//cout << "ref0: " << mk_ismt2_pp(ref0, m, 2) << endl;
			//cout << "ref: " << mk_ismt2_pp(ref, m, 2) << endl;
			sat->assert_expr(ref);
			////////////
			const lbool sat_res = sat->check_sat(0, NULL); // get cand
														   //////////
			cout << "sat_res: " << sat_res << endl;
			if (sat_res == l_false) { o = l_false; break; }
			////////////
			model_ref sat_m;
			sat->get_model(sat_m);
			cand.reset();
			//cout << "cand\n ";
			//model_smt2_pp(cout, m, *sat_m, 2);
			//cout << endl;
			unsigned fsc = sat_m->get_num_functions();
			SASSERT(!fsc);
			for (unsigned i = 0; i < fsc; ++i) {
				func_decl * const fd = sat_m->get_decl(i);
				func_interp* const fi = sat_m->get_func_interp(fd);
				if (!fi) continue;
				cout << "cand: " << fd->get_name() << ":\n" << mk_ismt2_pp(fi->get_interp(), m, 2) << endl;
			}

			for (unsigned i = 0; i < aux1.size(); ++i) {
				expr_ref val(m);
				sat_m->eval(aux1[i].get(), val, true);
				//cout << "cand " << mk_ismt2_pp(aux1[i].get(), m, 0) << ":\n" << mk_ismt2_pp(val, m, 2) << endl;
				const expr_ref a(m.mk_eq(aux1[i].get(), val), m);
				cand.push_back(a);
				assum[i] = a.get();
			}
			sat_m.reset();
			const lbool cex_res = cex_sat->check_sat(assum.size(), assum.c_ptr()); // get cex
			cout << "cex_res: " << cex_res << endl;
			if (cex_res == l_false) { o = l_true; break; }
			cex.cleanup();
			model_ref cex_m;
			cex_sat->get_model(cex_m);
			for (unsigned i = 0; i < aux2.size(); ++i) {
				expr_ref val(m);
				cex_m->eval(aux2[i].get(), val, true);
				//cout << "cex " << ieq->get_decl_name(i) << ":\n" << mk_ismt2_pp(val, m, 2) << endl;
				cex.insert(aux2[i].get(), val);
			}
		}		
		simp.release_plugins();
		return o;
	}

private:
	ast_manager& m_m;
	params_ref m_p;
};

tactic * mk_q2_tactic(ast_manager & m, params_ref const & p) {
	return and_then(
		//mk_simplify_tactic(m, p),
		mk_macro_finder_tactic(m, p)
		,
		//mk_nnf_tactic(m, p)
		//, 
		alloc(q2_tactic, m, p)
		);
}