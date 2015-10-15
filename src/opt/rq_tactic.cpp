#include"rq_tactic.h"
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
#include"for_each_expr.h"

using std::cout;
using std::endl;

class rq_tactic : public tactic {
public:
	rq_tactic(ast_manager& m, params_ref const& p)
		: m_m(m)
		, m_p(p)
	{}

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
		sort_ref_vector sts1(m);
		expr_ref_vector aux1(m);
		unzip_decl(m,dc.get_func_decls(), dc.get_num_decls(), sts1, aux1);
		unzip_decl(m,dc.get_pred_decls(), dc.get_num_preds(), sts1, aux1);

		prn(m,std::cout, in_f);
	}

	virtual void cleanup() { }

	virtual tactic* translate(ast_manager& m) {
		return alloc(rq_tactic, m, m_p);
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
		}
	}

	void prn(ast_manager& m, 
		std::ostream& out, expr_ref f) {
		ptr_vector<expr> stack;
		expr *           curr;
		expr_mark        visited;
		unsigned nid = 0;
		stack.push_back(f.get());
		expr_ref_vector gs(m);
		obj_map<expr, unsigned> e2g;

		while (!stack.empty()) {
			curr = stack.back();

			if (visited.is_marked(curr)) {
				stack.pop_back();
				continue;
			}

			switch (curr->get_kind()) {
			case AST_VAR:
				visited.mark(curr, true);
				stack.pop_back();
				//out<<"("<<to_var(curr)->get_id()<<")";
				break;

			case AST_APP: {
				app *  a = to_app(curr);		
				if (for_each_expr_args(stack, visited, a->get_num_args(), a->get_args())) {
					const unsigned nid = gs.size();
					gs.push_back(a);
					e2g.insert(a, nid);
					out << "g" << nid << "=";
					if (m.is_true(a)) out << "T";
					else if (m.is_false(a)) out << "F";
					else if (m.is_or(a)) out << "OR";
					else if (m.is_and(a)) out << "AND";
					else SASSERT(0);
					for (unsigned i = 0; i < a->get_num_args(); ++i) {
						out << " g";
						out << e2g[(a->get_args())[i]];
					}					
					out << endl;
					visited.mark(curr, true);
					stack.pop_back();
				}							
				break;
			}

			case AST_QUANTIFIER:
				if (!for_each_expr_args(stack, visited, to_quantifier(curr)->get_num_patterns(),
					to_quantifier(curr)->get_patterns())) {
					break;
				}
				if (!for_each_expr_args(stack, visited, to_quantifier(curr)->get_num_no_patterns(),
					to_quantifier(curr)->get_no_patterns())) {
					break;
				}
				if (!visited.is_marked(to_quantifier(curr)->get_expr())) {
					stack.push_back(to_quantifier(curr)->get_expr());
					break;
				}

				stack.pop_back();
				break;
			default:
				UNREACHABLE();
			}
		}
	}


private:
	ast_manager& m_m;
	params_ref m_p;
};

tactic * mk_rq_tactic(ast_manager & m, params_ref const & p) {
	return and_then(
		//mk_simplify_tactic(m, p),
		mk_macro_finder_tactic(m, p)
		,alloc(rq_tactic, m, p)
		);
}
