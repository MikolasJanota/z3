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
#include <strstream>

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
		expr_ref const in_f(mk_and(m, fmls.size(), fmls.c_ptr()), m);
		//cout << "fla:\n" << mk_ismt2_pp(in_f, m, 0) << endl;

		//get free
		decl_collector dc(m);
		dc.visit(in_f);
		ptr_vector<func_decl> decls;
		unzip_decl(m, dc.get_func_decls(), dc.get_num_decls(), decls);
		unzip_decl(m, dc.get_pred_decls(), dc.get_num_preds(), decls);

		prn(decls, m, std::cout, in_f);
	}

	virtual void cleanup() { }

	virtual tactic* translate(ast_manager& m) {
		return alloc(rq_tactic, m, m_p);
	}

	void unzip_decl(ast_manager& m,
		func_decl * const * dcs,
		unsigned count,
		ptr_vector<func_decl>& aux1) {
		for (unsigned i = 0; i < count; ++i) {
			func_decl * const fd = dcs[i];
			//cout << "decl :" << mk_ismt2_pp(fd, m, 0) << endl;
			//cout << fd->get_name() << ":" << mk_ismt2_pp(fd->get_range(), m, 0) << endl;
			SASSERT(fd->get_arity() == 0);
			sort_ref s(fd->get_range(), m);
			//expr_ref c(m.mk_const(fd->get_name(), s), m);			
			aux1.push_back(fd);			
		}
	}

	int prn(const ptr_vector<func_decl>& _decls,
		ast_manager& m,
		std::ostream& out, expr_ref f) {
		vector<int> vnames;
		unsigned gid = 1;
		unsigned vid = 2;
		obj_map<func_decl, int> decls;
		prefix.reset();
		prefix.resize(1);
		prefix[0].qt = "exists";		
		for (unsigned i = 0; i < _decls.size(); ++i) {
			incvid(vid);
			decls.insert(_decls[i], vid);
			prefix[0].vars.push_back(vid);
		}
		//////////////////
		const int o = prn(m, gid, vid, decls, vnames, f);
		prefix[0].b = o;
		//////////////////		
		////////////////// 
		out << "#QCIR-G14" << endl;		
		//////////////////		
		for (unsigned i = 0; i < prefix.size(); ++i) {
			//out << "g" << gid << "=" << (q->is_exists() ? "exists" : "forall") << "(";
			out << prefix[i].qt << "(";
			const vector<int>& vs = prefix[i].vars;
			for (unsigned i = 0; i< vs.size(); ++i) {				
				prn(out<<(i?",":""), vs[i]);
			}
			out << ")" << endl;
			//prn(out << " ; ", bid) << " )";// << endl;
		}

		prn(out << "output(", o) << ")" << endl;

		for (unsigned i = 0; i < gates.size(); ++i) {
			prn(out, gates[i].id) << "=" << gates[i].op << "(";
			const vector<int>& vs = gates[i].ops;
			for (unsigned i = 0; i< vs.size(); ++i) {
				prn(out << (i ? "," : ""), vs[i]);
			}
			out << ")" << endl;
		}
		return o;
	}

	void incgid(unsigned& gid) { SASSERT(gid & 1); gid += 2; }
	void incvid(unsigned& vid) { SASSERT(!(vid & 1)); vid += 2; }

	std::ostream& prn(std::ostream& out, int _id) {
		const bool neg = _id < 0;
		const unsigned id = (neg ? -_id : _id);
		if (neg) out << '-';
		if (id & 1) return out << "g" << id;
		return out << "v" << id;
	}

	//std::ostream& prn(std::ostream& out, obj_map<expr, int>& e2g, expr* e) {
	//	const bool neg = _id < 0;
	//	const unsigned id = (neg ? -_id : _id);
	//	if (neg) out << '-';
	//	if (id & 1) return out << "g" << id;
	//	return out << "v" << id;
	//}



	inline unsigned getvname(unsigned idx, const vector<int>& vnames) const {
		SASSERT(idx < vnames.size());
		return vnames[vnames.size() - idx - 1];
	}

	inline bool is_true(bv_util& bu, const expr * e) {
		return bu.get_manager().is_true(e) || bu.is_allone(e);
	}

	inline bool is_false(bv_util& bu, const expr * e) {
		return bu.get_manager().is_false(e) || bu.is_zero(e);
	}

	struct gate { unsigned id; std::string op; vector<int> ops; };
	struct qgate { std::string qt; vector<int> vars; int b; };

	vector<gate> gates;
	vector<qgate> prefix;

	int prn(ast_manager& m,
		unsigned& gid,
		unsigned& vid,
		const obj_map<func_decl,int>& decls,
		vector<int>& vnames,
		expr_ref f) {
		ptr_vector<expr> stack;
		expr *           curr;
		expr_mark        visited;
		stack.push_back(f.get());
		expr_ref_vector gs(m);
		obj_map<expr, int> e2g;
		bv_util bu(m);
		//out << "// prn vs:" << vnames.size() << endl;
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
				e2g.insert(curr, getvname(to_var(curr)->get_idx(), vnames));
				break;

			case AST_APP: {
				app *  a = to_app(curr);
				if (for_each_expr_args(stack, visited, a->get_num_args(), a->get_args())) {
					bool simp = false;
					if (m.is_eq(a)) {
						SASSERT(a->get_num_args() == 2);
						expr * const l = (a->get_args())[0];
						expr * const r = (a->get_args())[1];
						simp = is_true(bu, l) || is_true(bu, r) || is_false(bu, l) || is_false(bu, r);
						if (simp) {
							int rv = 0;
							if (is_true(bu, l)) rv = e2g[r];
							if (is_true(bu, r)) rv = e2g[l];
							if (is_false(bu, l)) rv = -e2g[r];
							if (is_false(bu, r)) rv = -e2g[l];
							SASSERT(rv);
							e2g.insert(curr, rv);
						}
					}
					else if (m.is_not(a)) {
						SASSERT(a->get_num_args() == 1);
						e2g.insert(curr, -e2g[(a->get_args())[0]]);
						simp = true;
					}
					if (!simp) prn_gate(m, gid, vid, decls, e2g, vnames, a);
					visited.mark(curr, true);
					stack.pop_back();
				}
				break;
			}

			case AST_QUANTIFIER: {
				quantifier * const q = to_quantifier(curr);
				expr_ref b(q->get_expr(), m);
				for (unsigned i = 0; i < q->get_num_decls(); ++i) {
					incvid(vid);
					//out << "// new v " << vid << endl;
					vnames.push_back(vid);
				}

				const unsigned psz = prefix.size();
				prefix.resize(psz + 1);
				prefix[psz].qt = (q->is_exists() ? "exists" : "forall");
				for (unsigned i = q->get_num_decls(); i;) {
					prefix[psz].vars.push_back(getvname(--i, vnames));
				}

				const unsigned oldsz = vnames.size();
				const int bid = prn(m, gid, vid, decls, vnames,b);
				SASSERT(oldsz == vnames.size());
				//incgid(gid);
				//e2g.insert(q, gid);
				e2g.insert(q, bid);
				prefix[psz].b = bid;

				for (unsigned i = 0; i < q->get_num_decls(); ++i) {
					vnames.pop_back();
				}

				visited.mark(curr, true);
				stack.pop_back();
			}
								 break;
			default:
				UNREACHABLE();
			}
		}
		const int retv = e2g[f];
		//out << "// prn retv:" << retv << endl;
		return retv;
	}

	int prn_gate(ast_manager& m,
		unsigned& gid,
		unsigned& vid,
		const obj_map<func_decl, int>& decls,
		obj_map<expr, int>& e2g,
		const vector<int>& vnames,		
		app* a) {
		bv_util bu(m);
		bool neg_fst = false;
		std::string op = "ERROR";
		if (is_true(bu, a)) op = "AND";
		else if (is_false(bu, a)) op = "OR";
		else if (m.is_or(a)) op = "OR";
		else if (m.is_and(a)) op = "AND";
		else if (m.is_ite(a)) op = "ITE";
		else if (m.is_implies(a)) {
			op = "OR";
			neg_fst = true;
		}
		else if (m.is_eq(a)) {
			op = "XOR";
			neg_fst = true;
		}
		else {
			SASSERT(a->get_num_args() == 0);
			const int rv=decls[a->get_decl()];
			e2g.insert(a,rv);
			return rv;
		}
		//////////////////

		incgid(gid);
		e2g.insert(a, gid);
		const unsigned gsz = gates.size();
		gates.resize(gsz + 1);
		gates[gsz].id = gid;
		gates[gsz].op = op;
		for (unsigned i = 0; i < a->get_num_args(); ++i) {
			int av = e2g[(a->get_args())[i]];
			if (!i&&neg_fst) av = -av;
			gates[gsz].ops.push_back(av);
		}		
		return gid;
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
