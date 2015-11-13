/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

q2.cpp

Abstract:

2 level quantification solver a la AReQS.

Author:

Mikolas Janota

Revision History:
--*/
#include"expr_substitution.h"
#include"expr_replacer.h"
#include"solver.h"
#include"tactic2solver.h"
#include"decl_collector.h"
#include"ast_util.h"
#include"quant_hoist.h"
#include"inc_sat_solver.h"
#include"qfaufbv_tactic.h"
#include"model_smt2_pp.h"
#include"model_evaluator.h"
#include"smt_tactic.h"
#include"smt_solver.h"
#include"th_rewriter.h"
#include"tactic.h"
#include"smt2parser.h"
#include"q2.h"
#include <strstream>
#define RUN_EXT 0
using std::endl;

lbool call_external(ast_manager& m, const func_decl_ref_vector& free_decls,
    solver* s, model_ref& model, params_ref p);

/* solver used to solve by the unquantified part. */
inline solver* mk_sat_solver(bool uf, ast_manager& m, const params_ref& p);//TODO: pass factory instead

/* CEGAR-Based approach to two level quantification problems a la AReQS. */

// A wrapper for the solver used to obtain counterexamples,
// i.e. moves for the universal player, given a move for existential.
class CexWrap {
    public:
        CexWrap(ast_manager&m, params_ref p, bool uf)
            : m(m)
            , uf(uf)
            , p(p)
            , nmx(NULL, m)
            , cex_sat(!uf ? mk_sat_solver(false, m, p) : NULL)
            , dummy(m)
            , forall_decls(m)
            { }


        // register forall variables
        void add_forall(const app_ref_vector& fas) {
            forall_decls.append(fas);
        }

        // set the value of the negated matrix
        void set_nmx(expr_ref e) {
            SASSERT(!nmx.get());
            nmx = e;
            if (!uf) cex_sat->assert_expr(nmx);
        }

        // calculate a counter example for a given existential assignment
        // return l_true if such found; return l_false if such does not exist
        lbool operator() (model_ref cand) {
            SASSERT(nmx.get());
            return run_nit(cand);
        }

        const model_ref get_model() const { return model; }

        const app_ref_vector& get_forall() const { return forall_decls; }

        expr_ref get_nmx() const { return nmx; }
    private:
        lbool run_nit(model_ref cand) {// non incremental implementation
            // substitute the candidate into the negated matrix
            expr_ref ns(m);
            model_evaluator me(*cand);
            me(nmx, ns);
            TRACE("q2",
                    model_smt2_pp(tout << "cand_m(\n", m, *cand, 2); tout << ")\n";
                    tout << "nit nmx(\n" << mk_ismt2_pp(nmx, m, 2) << ")\n";
                    tout << "nit ns(\n" << mk_ismt2_pp(ns, m, 2) << ")\n"; );
            // run SAT
            scoped_ptr<solver> cex_sat_tmp = mk_sat_solver(true, m, p);
            cex_sat_tmp->assert_expr(ns);
            const lbool res = cex_sat_tmp->check_sat(0, NULL);
            if (res == l_true) cex_sat_tmp->get_model(model);
            return res;
        }

        lbool run_it(model_ref cand) {// incremental implementation
            //TODO: works?
            assum.reset();
            model.reset();
            dummy.reset();
            model_to_assum(cand, assum, dummy);
            const lbool res = cex_sat->check_sat(assum.size(), assum.c_ptr());
            assum.reset();
            dummy.reset();
            if (res == l_true) cex_sat->get_model(model);
            return res;
        }
    private:
        ast_manager& m;
        bool uf;
        params_ref p;
        expr_ref nmx;
        scoped_ptr<solver> cex_sat;
        model_ref model;
        expr_ref_vector dummy;
        ptr_vector<expr> assum;
        app_ref_vector forall_decls;

        void model_to_assum(const model_ref sat_m, ptr_vector<expr>& assum,
                expr_ref_vector& cand) {
            SASSERT(!sat_m->get_num_functions());
            const unsigned sz = sat_m->get_num_constants();
            for (unsigned i = 0; i < sz; ++i) {
                func_decl * const cd = sat_m->get_constant(i);
                SASSERT(cd->get_arity() == 0);
                expr* ci = sat_m->get_const_interp(cd);
                if (!ci) ci = m.get_some_value(cd->get_range());
                const expr_ref a(m.mk_eq(m.mk_const(cd), ci), m);
                cand.push_back(a);
                assum.push_back(a.get());
            }
        }
};


// A wrapper for the solver used to obtain candidates,
// i.e. moves for the existential player.
class CandWrap {
    public:
        CandWrap(ast_manager& m, params_ref p,
                 bool uf,
                 const func_decl_ref_vector& free_decls)
            : m(m)
            , p(p)
            , free_decls(free_decls)
            , ex_decls(m)
            , sat(mk_sat_solver(uf, m, p))
            , simp(m)
         {}

        ~CandWrap() {
            if(sat) dealloc(sat);
            sat = 0;
        }

        // register an existential variable.
        inline void add_ex(func_decl * ex) {
            ex_decls.push_back(ex);
        }

        // assert an expression that must be always true (used for expressions with no universal variables)
        void assert(expr *  e) {
            sat->assert_expr(e);
        }

        // refine based on a counter example 
        void refine(const CexWrap * cex) {
            SASSERT(cex);
            model_ref cex_m(alloc(model, m));
            expr_substitution subst(m);
            mk_model(cex->get_model().get(), cex->get_forall(), cex_m);
            mk_subs(cex->get_forall(), cex_m, subst);
            expr_ref rf(m.mk_not(cex->get_nmx()), m);
            refine(rf, cex_m.get(), &subst);
        }

        // initial random refinement, i.e. cex has no model
        void init_refine(const CexWrap * cex) {
            SASSERT(cex);
            model_ref cex_m(alloc(model, m));
            mk_model(NULL, cex->get_forall(), cex_m);
            expr_ref rf(m.mk_not(cex->get_nmx()), m);
            refine(rf, cex_m.get(), NULL);
        }

        //TODO: Make sure that only registered variables are in the model.
        const model_ref get_model() const { return cand_model; }

        inline lbool operator() () {
            if (RUN_EXT) {
                return call_external(m, free_decls, sat, cand_model, p);
            }
            else {
                const lbool retv = sat->check_sat(0, NULL);
                if (retv == l_true) sat->get_model(cand_model);
                return retv;
            }
        }

    private:
        params_ref p;

        //Make sure that we have a model that assigns to those and only those 
        //variables that are universally qualified. 
        // If model is NULL, values are guessed. 
        void mk_model(const model *  _cex_m,
                const app_ref_vector& forall_decls,
                /*out*/model_ref cex_m) {
            SASSERT(cex_m.get());
            for (unsigned i = 0; i < forall_decls.size(); ++i) {
                func_decl * const cd = forall_decls[i]->get_decl();
                if (cd->get_arity()) {
                    SASSERT(0);
                    // TODO
                }
                else {
                    expr* ci = _cex_m ? _cex_m->get_const_interp(cd) : NULL;
                    if (!ci) ci = m.get_some_value(cd->get_range());
                    cex_m->register_decl(cd, ci);
                }
            }
            TRACE("q2", model_smt2_pp(tout << "cex_m\n", m, *(cex_m.get()), 2););
        }

        // Try to come up with clever substitutions based on a counter examples and a candidate. 
        // Currently just a hack that looks for identical bv values and maps the corresponding variables. 
        void mk_subs(
                const app_ref_vector& forall_decls,
                model_ref cex_m,
                /*out*/expr_substitution& subst) {
            bv_util bu(m);
            for (unsigned i = 0; i < forall_decls.size(); ++i) {
                app * const ac = forall_decls.get(i);
                func_decl * const a = ac->get_decl();
                if (a->get_arity()) continue;
                if (!bu.is_bv_sort(a->get_range())) continue;
                for (unsigned j = 0; j < ex_decls.size(); ++j) {
                    func_decl * const b = ex_decls.get(j);
                    if (b->get_arity()) continue;
                    if (!bu.is_bv_sort(b->get_range())) continue;
                    if (cex_m->get_const_interp(a) !=
                            cand_model->get_const_interp(b)) continue;
                    TRACE("q2", tout << "m:\n" << mk_ismt2_pp(a, m, 0) << "->" << mk_ismt2_pp(b, m, 0) << endl;);
                    subst.erase(ac);
                    app * const bc = m.mk_const(b);
                    subst.insert(ac, bc);
                    break;
                }
            }
        }


        // Refine based on a model and a substitution. The substitution is applied first. 
        void refine(expr_ref rf, model * cex_m, expr_substitution * subst) {
            //calculate refinement
            expr_ref ref(m);
            expr_ref tmp(m);
            ref = rf;
            TRACE("q2", tout << "ref0: " << mk_ismt2_pp(ref, m, 2) << endl;);
            if (subst) {// apply substitution 
                scoped_ptr<expr_replacer> er = mk_default_expr_replacer(m);
                er->set_substitution(subst);
                (*er)(ref.get(), tmp);
                ref = tmp;
                TRACE("q2", tout << "ref1: " << mk_ismt2_pp(ref, m, 2) << endl;);
            }
            if (cex_m) { // apply counter example 
                model_evaluator me(*cex_m);
                me(ref, tmp);
                ref = tmp;
                TRACE("q2", tout << "ref2: " << mk_ismt2_pp(ref, m, 2) << endl;);
            }
            //simplify refinement
            simp(ref);
            //TRACE("q2",tout << "ref3: " << mk_ismt2_pp(ref, m, 2) << endl;);
            // plug into solver 
            sat->assert_expr(ref);
        }
    private:
        ast_manager& m;
        const func_decl_ref_vector& free_decls;
        func_decl_ref_vector ex_decls;
        solver * sat;
        model_ref cand_model;
        th_rewriter simp;
};


// Implementation of the CEGAR loop.
class q2 : public q2_solver {
    public:
        enum Mode { BV, UFBV }; // pure a bit-vectors or also uninterpreted functions in the matrix. 
        q2(ast_manager& m, params_ref p, Mode mode,
                const ptr_vector<expr>& fmls)
            : m(m)
              , p(p)
              , mode(mode)
              , fmls(fmls)
              , free_decls(m)
              , ex_decls(m)
              , simp(m)
              , cands(m, p, mode==UFBV, free_decls)

    {}

        ~q2() {
            while (cexs.size()) {
                dealloc(cexs.back());
                cexs.pop_back();
            }
        }

        lbool operator() () {
            const bool ok = init();
            if (!ok) return l_undef;
            return cegar();
        }
    private:
        ast_manager& m;
        params_ref p;
        Mode mode;
        const ptr_vector<expr>& fmls;

        func_decl_ref_vector free_decls;
        app_ref_vector ex_decls;
        th_rewriter simp;

        CandWrap cands;
        ptr_vector<CexWrap>  cexs; // Maintain a counter-example generator for each formula (A X. F)

        bool init() {
            decl_collector dc(m);
            quantifier_hoister hoister(m);
            expr_ref tmp(m);
            app_ref_vector tmp_vs(m);
            for (unsigned i = 0; i < fmls.size(); ++i) {
                expr * f = fmls[i];
                TRACE("q2", tout << "fi:\n" << mk_ismt2_pp(f, m, 2) << endl;);
                dc.visit(f);
                // pull initial existential for, which are essentially the same as free 
                hoister.pull_exists(f, tmp_vs, tmp);
                if (tmp_vs.size()) {
                    f = tmp;
                    for (unsigned i = 0; i < tmp_vs.size(); ++i) {
                        app * const v = tmp_vs.get(i);
                        cands.add_ex(v->get_decl());
                        TRACE("q2", tout << "E " << mk_ismt2_pp(v, m, 2) << endl;);
                    }
                    ex_decls.append(tmp_vs);
                }
                unsigned level = 0;
                // pull universals and make sure there are no further existentials
                app_ref_vector forall_decls(m);
                while (1) {
                    bool is_forall;
                    tmp_vs.reset();
                    hoister(f, tmp_vs, is_forall, tmp);
                    for (unsigned i = 0; i < tmp_vs.size(); ++i) {
                        TRACE("q2", tout << (is_forall ? 'A' : 'E') << " " << mk_ismt2_pp(tmp_vs[i].get(), m, 2) << endl;);
                    }
                    if (tmp_vs.empty()) break;
                    SASSERT(!level || is_forall); // TODO: exception?
                    if (level && !is_forall) return false;
                    if (level || is_forall) ++level;
                    if (level) {
                        SASSERT(is_forall);
                        forall_decls.append(tmp_vs);
                    }
                    else {
                        UNREACHABLE(); //TODO OK?
                    }
                    f = tmp;
                    TRACE("q2", tout << "f:\n" << mk_ismt2_pp(f, m, 2) << endl;);
                }
                TRACE("q2", tout << (level ? "quant" : "no quant") << endl;);
                if (level) {// handle quantified formula 
                    CexWrap* const cex = alloc(CexWrap, m, p, mode == UFBV);
                    expr_ref raw_nmx(m.mk_not(f), m);
                    expr_ref nmx(m);
                    simp(raw_nmx, nmx);
                    cex->add_forall(forall_decls);
                    cex->set_nmx(nmx);
                    //cands.init_refine(cexs.back());
                    cexs.push_back(cex);
                }
                else {// assert an unquantified formula
                    expr_ref sf(m);
                    simp(f, sf);
                    TRACE("q2", tout << "sf:\n" << mk_ismt2_pp(sf, m, 2) << endl;);
                    cands.assert(sf);
                }

            }

            process_free_decls(m, dc.get_func_decls(), dc.get_num_decls());
            process_free_decls(m, dc.get_pred_decls(), dc.get_num_preds());

            TRACE("q2",
                    tout << "F\n";
                    for (unsigned i = 0; i < free_decls.size(); ++i)
                    tout << mk_ismt2_pp(free_decls[i].get(), m, 2) << endl;
                 );

            return true;
        }

        lbool cegar() {
            int count = 0;
            while (1) {
                std::cout << "it: " << ++count << endl;
                ////////////
                const lbool sat_res = cands(); // get cand
                TRACE("q2", tout << "cand_res: " << sat_res << endl;);
                if (sat_res == l_false) { return l_false; }
                if (sat_res == l_undef) { return l_undef; }
                // check if there is a counter example 
                bool all_good = true;
                for (unsigned i = 0; i < cexs.size(); ++i) {
                    CexWrap * const s = cexs[i];
                    const lbool cex_res = (*s)(cands.get_model());
                    TRACE("q2", tout << "cex_res[" << i << "]: " << cex_res << endl;);
                    if (cex_res == l_undef) { return l_undef; }
                    if (cex_res == l_false) { continue; }
                    all_good = false;
                    cands.refine(s);
                }
                if (all_good) return l_true;
            }
            UNREACHABLE();
            return l_undef;
        }

        void process_free_decls(ast_manager& m,
                func_decl * const * dcs,
                unsigned count) {
            for (unsigned i = 0; i < count; ++i) {
                //const
                func_decl * const fd = dcs[i];
                free_decls.push_back(fd);
                cands.add_ex(fd);
                SASSERT(mode == UFBV || fd->get_arity() == 0);
            }
        }
};

inline solver* mk_sat_solver(bool uf, ast_manager& m, const params_ref& _p) {
    params_ref p;
    p.copy(_p);
    if (!uf) return mk_inc_sat_solver(m, p);
    //return mk_smt_solver(m, p, symbol());
    tactic_ref t = mk_qfaufbv_tactic(m, p);
    //tactic_ref t = mk_smt_tactic(p);
    solver* rv = mk_tactic2solver(m, t.get(), p);
    rv->set_produce_models(true);
    SASSERT(rv);
    return rv;
}

lbool call_external(ast_manager& m, const func_decl_ref_vector& free_decls,
    solver* s, model_ref& model, params_ref p) {
    const std::string pth = "";// "C:\\Users\\t-mikjan\\git\\z3\\testing\\"; /* C:\\cygwin\\home\\mikolas\\git\\z3\\test\\ */
    const std::string sol = "boolector-207.exe";
    const std::string ifn = "foo.smt2";
    const std::string ifn1 = "foo1.smt2";
    const std::string ofn = "bar.smt2";
    const std::string fifn = pth + ifn;
    const std::string fofn = pth + ofn;
    { std::ofstream out("foo1.smt2"); s->display(out); out.close(); }

    const char * cmd1 = "boolector-211.exe --dump-smt2 -x -rwl 0 foo1.smt2  >foo.smt2";
    std::cerr << "cmd: " << cmd1 << std::endl;
    const int rv1 = system(cmd1);
    if (rv1) return l_undef;
    std::stringstream cms;
    cms << sol
        << " " << "--smt2 -m --smt2-model --dec"
        << " " << fifn
        << " >" << fofn;
    std::string cmdstr(cms.str());
    std::cerr << "cmd: " << cmdstr << std::endl;
    const int rv = system(cmdstr.c_str());
    //int rv = 10;
    if (rv == 10) {
        std::ifstream is(fofn);
        cmd_context ctx(true, &m);
        for (unsigned i = 0; i < free_decls.size(); ++i) 
            ctx.insert(free_decls.get(i));
        const bool mp = parse_smt2_model(ctx, is, false, p, model);
        if (!mp) return l_undef;
        return l_true;
    }
    else if (rv == 20) {
        return l_false;
    }
    std::cerr << "res: " << rv << std::endl;
    return l_undef;
}

q2_solver* mk_q2_solver(ast_manager& m, params_ref p, const ptr_vector<expr>& fmls) {
    return alloc(q2, m, p, q2::UFBV, fmls);
}
