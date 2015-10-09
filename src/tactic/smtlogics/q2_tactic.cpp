#include"q2_tactic.h"
#include"inc_sat_solver.h"
#include"qfbv_tactic.h"
#include"expr_substitution.h"
#include"expr_replacer.h"
#include"extension_model_converter.h"
#include"solver.h"
#include"array.h"
#include"tactic2solver.h"
#include"decl_collector.h"
using std::cout;
using std::endl;

class q2_tactic : public tactic {
public:
	q2_tactic(ast_manager& m, params_ref const& p)
		: m_m(m)
		, m_p(p)
	{}

	virtual void operator()(goal_ref const & g,
		goal_ref_buffer & result,
		model_converter_ref & mc,
		proof_converter_ref & pc,
		expr_dependency_ref & core) {
		ast_manager& mng = g->m();
		g->display(cout);
		cout << "sz: " << g->size() << endl;
		SASSERT(g->size() == 1);
		expr_ref f(g->form(0),mng);
		cout << mk_ismt2_pp(f, mng, 0) << endl;
		SASSERT(is_forall(f));
		const quantifier_ref ieq(to_quantifier(f),mng);
		///////////////
		const expr_ref  matrix(ieq->get_expr(), mng);
		cout << "mx: " << endl << mk_ismt2_pp(matrix, mng, 0) << endl;
		expr_ref_vector aux1(mng);
		expr_ref_vector aux2(mng);
		//
		expr_substitution sub(mng);
		for (unsigned i = 0; i < ieq->get_num_decls(); ++i) {
			const unsigned vx = i;
			sort_ref vs(ieq->get_decl_sort(i), mng);
			expr_ref vc(mng.mk_fresh_const(ieq->get_decl_name(i).str().c_str(), vs),mng);
			aux2.push_back(vc);
			sub.insert(mng.mk_var(vx, vs), vc);
		}
		//
		scoped_ptr<expr_replacer> er(mk_default_expr_replacer(mng));
		er->set_substitution(&sub);
		expr_ref cmx(mng);
		(*er)(matrix, cmx);
		cout << "cmx: " << endl << mk_ismt2_pp(cmx, mng, 0) << endl;
		sub.cleanup();
		/////////////
        decl_collector dc(mng);
		dc.visit(f);
		const func_decl * const * dcs = dc.get_func_decls();
		sort_ref_vector sts1(mng);
		for (unsigned i = 0; i < dc.get_num_decls(); ++i) {
			const func_decl * const fd = dcs[i];
			cout << fd->get_name() <<":"<<mk_ismt2_pp(fd->get_range(), mng, 0) << endl;
			sort_ref s(fd->get_range(), mng);
			expr_ref c(mng.mk_const(fd->get_name(), s),mng);
			aux1.push_back(c);
			sts1.push_back(s);
		}
		//////////////
		//tactic_ref cext = mk_qfbv_tactic(mng, m_p);
		//scoped_ptr<solver> cex_sat = mk_tactic2solver(mng, cext.get(), m_p);
		scoped_ptr<solver> cex_sat = mk_inc_sat_solver(mng, m_p);
		expr_ref ncmx(mng.mk_not(cmx), mng);
		cex_sat->assert_expr(ncmx);
		////////////
		//////////////
		//tactic_ref satt = mk_qfbv_tactic(mng, m_p);
		//scoped_ptr<solver> sat = mk_tactic2solver(mng, satt.get(), m_p);
		scoped_ptr<solver> sat = mk_inc_sat_solver(mng, m_p);
		expr_substitution cex(mng);
		expr_ref_vector ini_cex(mng);
		for (unsigned i = 0; i < ieq->get_num_decls(); ++i) {
			expr_ref v(mng.get_some_value(ieq->get_decl_sort(i)),mng);
			ini_cex.push_back(v);
			cex.insert(aux2[i].get(), v);
		}
		scoped_ptr<expr_replacer> rer(mk_default_expr_replacer(mng));
		lbool o = l_undef;
		expr_ref_vector cand(mng);
		ptr_vector<expr> assum(aux1.size());
		while (1) {
			expr_ref ref(mng);
			rer->set_substitution(&cex);
			(*rer)(cmx, ref);
			sat->assert_expr(ref);
			cout << "ref: " << mk_ismt2_pp(ref, mng, 2) << endl;
			////////////
			const lbool sat_res = sat->check_sat(0, NULL);
			////////////
			cout << "sat_res: " << sat_res << endl;
			if (sat_res == l_false) { o = l_false; break; }
			////////////
			model_ref sat_m;
			sat->get_model(sat_m);
			cand.reset();			
			for (unsigned i = 0; i < aux1.size(); ++i) {
				expr_ref val(mng);
				sat_m->eval(aux1[i].get(), val, true);
				cout << "cand " << ":\n" << mk_ismt2_pp(val, mng, 2) << endl;
				const expr_ref a(mng.mk_eq(aux1[i].get(), val), mng);
				cand.push_back(a);
				assum[i] = a.get();
			}
			sat_m.reset();
			const lbool cex_res = cex_sat->check_sat(assum.size(),assum.c_ptr());
			cout << "cex_res: " << cex_res << endl;
			if (cex_res == l_false) { o = l_true; break; }
			cex.cleanup();
			model_ref cex_m;
			cex_sat->get_model(cex_m);
			for (unsigned i = 0; i < aux2.size(); ++i) {
				expr_ref val(mng);
				cex_m->eval(aux2[i].get(), val, true);
				cout << "cex " << ieq->get_decl_name(i) << ":\n" << mk_ismt2_pp(val, mng, 2) << endl;
				cex.insert(aux2[i].get(), val);
			}
		}
		cand.reset();
		
		goal_ref resg(alloc(goal, *g, true));
		//if (o == l_true) resg->assert_expr(mng.mk_true());
		if (o == l_false) resg->assert_expr(mng.mk_false());
		if (o != l_undef) result.push_back(resg.get());
	}

	virtual void cleanup() { }

	virtual tactic* translate(ast_manager& m) {
		return alloc(q2_tactic, m, m_p);
	}
private:
	ast_manager& m_m;
	params_ref m_p;
};

tactic * mk_q2_tactic(ast_manager & m, params_ref const & p) {
	return alloc(q2_tactic, m, p);
}