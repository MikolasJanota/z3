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
#include"smt_tactic.h"
#include"smt_solver.h"

using std::cout;
using std::endl;


inline solver* mk_sat_solver(bool uf, ast_manager& m, const params_ref& p);


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
		CandWrap(ast_manager& m, params_ref p, Mode& mode)
			: m(m)
			, ex_decls(m)
			, forall_decls(m)
			, mx(m)
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

		void add_forall(const app_ref_vector& fas) {
			forall_decls.append(fas);
		}

		void add_ex(const app_ref_vector& exs) {
			ex_decls.append(exs);
		}

		void set_mx(expr_ref e) { mx = e; }

		void assert(expr *  e) {
			sat->assert_expr(e);
		}

		void refine(
			model_ref cand_m,
			model_ref _cex_m) {
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
			model_smt2_pp(cout << "cex_m\n", m, cex_m, 2);
            ///////////////
			bv_util bu(m);
			expr_substitution subst(m);
			for (unsigned i = 0; i < forall_decls.size(); ++i) {
				app * const a = forall_decls.get(i);
				if (a->get_decl()->get_arity()) continue;
				if (!bu.is_bv_sort(a->get_decl()->get_range())) continue;
				for (unsigned j = 0; j < ex_decls.size(); ++j) {
					app * const b = ex_decls.get(j);
					if (b->get_decl()->get_arity()) continue;
					if (!bu.is_bv_sort(b->get_decl()->get_range())) continue;
					if (cex_m.get_const_interp(a->get_decl()) !=
						cand_m->get_const_interp(b->get_decl())) continue;
					cout << "m:\n" << mk_ismt2_pp(a, m, 0) << "->" << mk_ismt2_pp(b, m, 0) << endl;
					subst.insert(a, b);
					break;
				}
			}
			//calculate refinement		
			expr_ref ref(m);
			expr_ref tmp(m);
			ref = mx;
			scoped_ptr<expr_replacer> er = mk_default_expr_replacer(m);
			er->set_substitution(&subst);
			(*er)(ref.get(), tmp);
			ref = tmp;
			model_evaluator me(cex_m);
 			me(ref, tmp);
			ref = tmp;
			//simplify refinement
			simp(ref, tmp);
			/////
			ref = tmp;
			sat->assert_expr(ref);
			//cout << "mx: " << mk_ismt2_pp(mx, m, 2) << endl;
			//model_smt2_pp(cout << "cex:\n", m, cex_m, 2);
			//cout << "ref0: " << mk_ismt2_pp(ref0, m, 2) << endl;
			cout << "ref: " << mk_ismt2_pp(ref, m, 2) << endl;			
		}
	private:
		ast_manager& m;
		app_ref_vector ex_decls;
		app_ref_vector forall_decls;		
		expr_ref mx;
		scoped_ptr<solver> sat;
		model_ref cand_model;
		SimpWrap simp;
	};

	class CexWrap {
	public:
		CexWrap(ast_manager&m, params_ref p,
			Mode& mode)
			: m(m)
			, p(p)
			, nmx(m)
			, cex_sat(mk_sat_solver(mode==UFBV,m,p))
		    ,dummy(m)
		{
			//cex_sat->assert_expr(ncmx);
		}

		const model_ref get_model() const { return model; }

		void set_nmx(expr_ref e) { nmx = e; }

		lbool operator() (model_ref cand) {
			return run_nit(cand);
		}

		lbool run_nit(model_ref cand) {
			expr_ref ns(m);
			model_evaluator me(*cand);
			me(nmx, ns);
			model_smt2_pp(cout << "cand_m(\n", m, *cand, 2); cout << "\n)\n";
			cout << "nit nmx\n " << mk_ismt2_pp(nmx, m, 2) << endl;
			cout << "nit ns\n " << mk_ismt2_pp(ns, m, 2) << endl;
			scoped_ptr<solver> cex_sat1 = mk_sat_solver(true, m, p);
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
			, ex_decls(m)
			, forall_decls(m)
			, simp(m)
			, matrix(m)
		    , cands(m, p, mode)
		    , cexs(m, p, mode)

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
		app_ref_vector ex_decls;
		app_ref_vector forall_decls;
		SimpWrap simp;

		expr_ref matrix;

		CandWrap cands;
		CexWrap cexs;

		void init() {
			// conjoin goal			
			expr_ref const in_f(mk_and(m, fmls.size(), fmls.c_ptr()), m);

			//cout << "fla:\n" << mk_ismt2_pp(in_f, m, 0) << endl;

			decl_collector dc(m);
			quantifier_hoister hoister(m);
			expr_ref tmp(m);
			app_ref_vector tmp_vs(m);
			expr_ref _matrix(m.mk_true(), m);
			for (unsigned i = 0; i < fmls.size(); ++i) {				
				expr * f = fmls[i];
				cout << "fi:\n" << mk_ismt2_pp(f, m, 2) << endl;
				dc.visit(f);
				process_free_decls(m, dc.get_func_decls(), dc.get_num_decls());
				process_free_decls(m, dc.get_pred_decls(), dc.get_num_preds());
				hoister.pull_exists(f, tmp_vs, tmp);
				if (tmp_vs.size()) {
					f = tmp;
					for (unsigned i = 0; i < tmp_vs.size(); ++i) {
						cout << "E " << mk_ismt2_pp(tmp_vs[i].get(), m, 2) << endl;
					}
					ex_decls.append(tmp_vs);
					cands.add_ex(tmp_vs);
				} 
				unsigned level = 0;
				while (1) {
					bool is_forall;
					tmp_vs.reset();
					hoister(f, tmp_vs, is_forall, tmp);
					for (unsigned i = 0; i < tmp_vs.size(); ++i) {
						cout << (is_forall?'A':'E') << " " << mk_ismt2_pp(tmp_vs[i].get(), m, 2) << endl;
					}
					if (tmp_vs.empty()) break;
					SASSERT(!level || is_forall); // TODO: exception?
					if (level && !is_forall) return;
					if (is_forall) ++level;
					if (level) {
						forall_decls.append(tmp_vs);
						cands.add_forall(tmp_vs);
					}
					else {
						/* TODO */;
					}
					f = tmp;
					cout << "f:\n" << mk_ismt2_pp(f, m, 2) << endl;
				}
				cout << (level ? "quant" : "no quant") << endl;
				if(level) _matrix = m.mk_and(_matrix.get(), f);
				else cands.assert(f);
			}

			////get free
			//decl_collector dc(m);
			//dc.visit(in_f);
			//process_free_decls(m, dc.get_func_decls(), dc.get_num_decls());
			//process_free_decls(m, dc.get_pred_decls(), dc.get_num_preds());
			//// get matrix and forall quant
			//quantifier_hoister hoister(m);
			//expr_ref _matrix(in_f,m);
			//while (1) {
			//	cout << "_mx:\n" << mk_ismt2_pp(_matrix, m, 2) << endl;
			//	expr_ref tmp(m);
			//	app_ref_vector tmp_vs(m);
			//	bool is_forall;
			//	hoister(_matrix, tmp_vs, is_forall, tmp);				
			//	if (tmp_vs.empty()) break;
			//	SASSERT(is_forall); // TODO: exception?
			//	if (!is_forall) return;
			//	forall_decls.append(tmp_vs);
			//	_matrix = tmp;
			//}

			//cout << "F";
			//for (unsigned i = 0; i < free_decls.size(); ++i)
			//	cout << "\n  " << mk_ismt2_pp(free_decls[i].get(), m, 2);
			//cout << endl;
			cout << "A";
			for (unsigned i = 0; i < forall_decls.size(); ++i)
				cout << " " << mk_ismt2_pp(forall_decls[i].get(), m, 0);
			cout << endl;
		
			simp(_matrix, matrix);
			cout << "mx:\n" << mk_ismt2_pp(matrix, m, 0) << endl;
			cands.set_mx(matrix);
			expr_ref nmx(m.mk_not(matrix), m);
			cexs.set_nmx(nmx);
			//
		}

		lbool cegar() {			
			//////////////////
			int count = 0;
			lbool retv = l_undef;
			while (1) {
				cout << "it: " << ++count << endl;
				////////////
				const lbool sat_res = cands(); // get cand
				cout << "cand_res: " << sat_res << endl;
				if (sat_res == l_false) { retv = l_false; break; }
				if (sat_res == l_undef) { retv = l_undef; break; }
				const lbool cex_res = cexs(cands.get_model()); // get cex
				cout << "cex_res: " << cex_res << endl;
				if (cex_res == l_false) { retv = l_true; break; }
				if (sat_res == l_undef) { retv = l_undef; break; }
				cands.refine(cands.get_model(), cexs.get_model());
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

inline solver* mk_sat_solver(bool uf, ast_manager& m, const params_ref& _p) {
	params_ref p;
	p.copy(_p);
	if (!uf) return  mk_inc_sat_solver(m, p);
	return mk_smt_solver(m,p, symbol("UFBV"));
	//p.set_bool("auto_config", true);
	//tactic_ref cext = mk_smt_tactic(p);
	//cext->set_logic(symbol("UFBV"));
	////mk_ufbv_tactic(m, p);
	//solver* rv = mk_tactic2solver(m, cext.get(), p);
	//SASSERT(rv);
	//rv->set_produce_models(true);
	//return rv;
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