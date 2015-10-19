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
#include"model_evaluator.h"

using std::cout;
using std::endl;


inline solver* mk_sat_solver(bool uf, ast_manager& m, params_ref& p);


class q2_tactic : public tactic {
public:
	enum Mode { BV, UFBV };


	q2_tactic(ast_manager& m, params_ref const& p)
		: m_m(m)
		, m_p(p) {}

	
	virtual void operator()(goal_ref const & g,
		goal_ref_buffer & result,
		model_converter_ref & mc,
		proof_converter_ref & pc,
		expr_dependency_ref & core) {
		ast_manager& m(g->m());
		ptr_vector<expr> flas;
		g->get_formulas(flas);
		imp i(m, m_p, q2_tactic::UFBV, flas);
		const lbool o = i();
		goal_ref resg(alloc(goal, *g, true));		
		if (o == l_false) resg->assert_expr(m.mk_false());
		if (o != l_undef) result.push_back(resg.get());
	}

	virtual void cleanup() { }

	virtual tactic* translate(ast_manager& m) {
		return alloc(q2_tactic, m, m_p);
	}
private:
	ast_manager& m_m;
	params_ref m_p;

	struct SimpWrap {
		inline void operator() (expr * s, expr_ref & r) {
			proof_ref dummy(m);
			simp(s, r, dummy);
		}
		SimpWrap(ast_manager& m)
			: m(m)
			, simp(m)
			, bsp(m)
			, bvsp(m, bsp, bv_par) {
			simp.register_plugin(&bsp);
			simp.register_plugin(&bvsp);
			simp.enable_ac_support(true);
		}

		~SimpWrap() {
			simp.release_plugins();
		}

		ast_manager& m;
		simplifier simp;
		basic_simplifier_plugin bsp;
		bv_simplifier_params bv_par;
		bv_simplifier_plugin bvsp;
	};


	class CandWrap {
	public:
		CandWrap(ast_manager& m, params_ref p,
			Mode& mode,
			func_decl_ref_vector& free_decls,
			app_ref_vector& forall_decls,
			expr_ref mx)
			: m(m)
			, free_decls(free_decls)
			, forall_decls(forall_decls)
			, mx(mx)
			, sat(mk_sat_solver(mode == UFBV, m, p))
			, simp(m)
		{  }

		~CandWrap() { }

		const model_ref get_model() const { return cand_model; }

		inline lbool operator() () {
			const lbool retv = sat->check_sat(0, NULL);
			if (retv == l_true) sat->get_model(cand_model);
			return retv;
		}

		void refine(model_ref _cex_m) {
			model cex_m(m);
			//SASSERT(!_cex_m->get_num_functions() || mode==UFBV);
			for (unsigned i = 0; i < forall_decls.size(); ++i) {
				func_decl * const cd = forall_decls[i]->get_decl();
				if (cd->get_arity()) {
					func_interp* ci = _cex_m->get_func_interp(cd);
					if (ci) cex_m.register_decl(cd, ci);
					else /* TODO */ ;
				} else {
					expr* ci = _cex_m->get_const_interp(cd);
					if (!ci) ci = m.get_some_value(cd->get_range());
					cex_m.register_decl(cd, ci);
				}
			}
			model_smt2_pp(cout<<"cex_m\n", m, cex_m, 2);
			expr_ref ref0(m), ref(m);
			model_evaluator me(cex_m);
			me(mx, ref0);//calculate refinement		
			simp(ref0, ref);//simplify refinement
			sat->assert_expr(ref);
			//cout << "mx: " << mk_ismt2_pp(mx, m, 2) << endl;
			//model_smt2_pp(cout << "cex:\n", m, cex_m, 2);
			//cout << "ref0: " << mk_ismt2_pp(ref0, m, 2) << endl;
			cout << "ref: " << mk_ismt2_pp(ref, m, 2) << endl;			
		}
	private:
		ast_manager& m;
		func_decl_ref_vector free_decls;
		app_ref_vector forall_decls;
		expr_ref mx;
		scoped_ptr<solver> sat;
		model_ref cand_model;
		SimpWrap simp;
	};

	class CexWrap {
	public:
		CexWrap(ast_manager&m, params_ref p,
			Mode& mode,
			func_decl_ref_vector& free_decls,			
			app_ref_vector& forall_decls,
			expr_ref nmx)
			: m(m)
			, p(p)
			, free_decls(free_decls)
			, forall_decls(forall_decls)
			, nmx(nmx)
			, cex_sat(mk_sat_solver(mode==UFBV,m,p))
		    ,dummy(m)
		{
			//cex_sat->assert_expr(ncmx);
		}

		const model_ref get_model() const { return model; }

		lbool operator() (model_ref cand) {
			return run_it(cand);
		}

		lbool run_nit(model_ref cand) {
			model_smt2_pp(cout << "cand_m\n", m, *cand, 2);
			scoped_ptr<solver> cex_sat1=mk_sat_solver(true,m,p);
			expr_ref ns(m);
			model_evaluator me(*cand);
			me(nmx, ns);
			cout << "nit ns\n " << mk_ismt2_pp(ns, m, 2) << endl;
			cex_sat1->assert_expr(ns);
			const lbool res = cex_sat1->check_sat(0,NULL);
			if (res == l_true) cex_sat1->get_model(model);
			return res;
		}

		lbool run_it(model_ref cand) {
			assum.reset();
			model.reset();
			dummy.reset();
			model_to_assum(cand, assum, dummy);
			const lbool res = cex_sat->check_sat(assum.size(), assum.c_ptr());		
			assum.reset();
			dummy.reset();
			if(res==l_true) cex_sat->get_model(model);
			return res;
		}
	private:
		ast_manager& m;
		params_ref p;
		func_decl_ref_vector free_decls;
		app_ref_vector forall_decls;
		expr_ref nmx;
		scoped_ptr<solver> cex_sat;
		model_ref model;
		expr_ref_vector dummy;
		ptr_vector<expr> assum;		

		void model_to_assum(const model_ref sat_m, ptr_vector<expr>& assum,
			expr_ref_vector& cand) {
			SASSERT(!sat_m->get_num_functions());
			const unsigned sz = sat_m->get_num_constants();
			for (unsigned i = 0; i < sz; ++i) {
				func_decl * const cd = sat_m->get_constant(i);
				SASSERT(cd->get_arity() == 0);
				expr* ci = sat_m->get_const_interp(cd);
				if (!ci) ci = m.get_some_value(cd->get_range());
				//cout << "cand: " << cd->get_name() << ":\n" << mk_ismt2_pp(ci, m, 2) << endl;
				const expr_ref a(m.mk_eq(m.mk_const(cd), ci), m);
				cand.push_back(a);
				assum.push_back(a.get());
			}
		}
	};



	class imp {
	public:
		imp(ast_manager& m, params_ref p, Mode mode,
			const ptr_vector<expr>& fmls)
			: m(m)
			, p(p)
			, mode(mode)
			, fmls(fmls)
			, free_decls(m)
			, forall_decls(m)
			, simp(m)
			, matrix(m)
		{}

		lbool operator() () {
			init();
			return cegar();
		}
	private:
		ast_manager& m;
		params_ref p;
		Mode mode;
		const ptr_vector<expr>& fmls;

		func_decl_ref_vector free_decls;
		app_ref_vector forall_decls;
		SimpWrap simp;

		expr_ref matrix;

		void init() {
			// conjoin goal			
			expr_ref const in_f(mk_and(m, fmls.size(), fmls.c_ptr()), m);

			//cout << "fla:\n" << mk_ismt2_pp(in_f, m, 0) << endl;

			//get free
			decl_collector dc(m);
			dc.visit(in_f);
			process_free_decls(m, dc.get_func_decls(), dc.get_num_decls());
			process_free_decls(m, dc.get_pred_decls(), dc.get_num_preds());
			// get matrix and forall quant
			quantifier_hoister hoister(m);
			expr_ref _matrix(m);
			bool is_forall;

			hoister(in_f, forall_decls, is_forall, _matrix);
			SASSERT(is_forall || forall_decls.empty()); // TODO: exception?

			cout << "F";
			for (unsigned i = 0; i < free_decls.size(); ++i)
				cout << "\n  " << mk_ismt2_pp(free_decls[i].get(), m, 2);
			cout << endl;
			cout << "A";
			for (unsigned i = 0; i < forall_decls.size(); ++i)
				cout << " " << mk_ismt2_pp(forall_decls[i].get(), m, 0);
			cout << endl;
		
			simp(_matrix, matrix);
			//cout << "mx:\n" << mk_ismt2_pp(matrix, m, 0) << endl;
			//
		}

		lbool cegar() {			
			expr_ref ncmx(m.mk_not(matrix), m);// negate matrix
			CandWrap cands(m, p, mode, free_decls, forall_decls, matrix);
			CexWrap cexs(m, p, mode, free_decls, forall_decls, ncmx);
			//////////////////
			int count = 0;
			lbool retv = l_undef;
			while (1) {
				cout << "it: " << ++count << endl;
				////////////
				const lbool sat_res = cands(); // get cand
				cout << "cand_res: " << sat_res << endl;
				if (sat_res == l_false) { retv = l_false; break; }
				const lbool cex_res = cexs(cands.get_model()); // get cex
				cout << "cex_res: " << cex_res << endl;
				if (cex_res == l_false) { retv = l_true; break; }
				cands.refine(cexs.get_model());
			}
			return retv;
		}


		
		//void mk_ini_cex(expr_substitution& cex) {			
		//	for (unsigned i = 0; i < forall_decls.size(); ++i) {
		//		SASSERT(forall_decls[i]->get_decl()->get_arity() == 0);
		//		sort * const s = forall_decls[i]->get_decl()->get_range();
		//		expr_ref v(m.get_some_value(s), m);
		//		//	ini_cex.push_back(v);
		//		cex.insert(forall_decls[i].get(), v);
		//		//cout << "init cex: " << mk_ismt2_pp(forall_decls[i].get(), m, 0) << " " << mk_ismt2_pp(v, m, 0) << endl;
		//	}
		//}


		void process_free_decls(ast_manager& m,
			func_decl * const * dcs,
			unsigned count) {
			for (unsigned i = 0; i < count; ++i) {
				//const 
				func_decl * const fd = dcs[i];
				free_decls.push_back(fd);
				SASSERT(mode==UFBV || fd->get_arity() == 0);
			}
		}
	};
};

inline solver* mk_sat_solver(bool uf, ast_manager& m, params_ref& p) {
	if (!uf) return  mk_inc_sat_solver(m, p);
	tactic_ref cext = mk_ufbv_tactic(m, p);
	solver* rv = mk_tactic2solver(m, cext.get(), p);
	SASSERT(rv);
	rv->set_produce_models(true);
	return rv;
}

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