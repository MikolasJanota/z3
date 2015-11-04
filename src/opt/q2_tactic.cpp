/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

q2_tactic.cpp

Abstract:

Tactic for 2 level quantification a la AReQS.

Author:

Mikolas Janota

Revision History:
--*/
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
#include"qfaufbv_tactic.h"
#include"model_smt2_pp.h"
#include"model_evaluator.h"
#include"smt_tactic.h"
#include"smt_solver.h"
#include"array_decl_plugin.h"
#include"simplifier_plugin.h"
#include"basic_simplifier_plugin.h"
#include"array_simplifier_params.h"
#include"array_simplifier_plugin.h"
#include"solve_eqs_tactic.h"
#include"simplify_tactic.h"
#include"propagate_values_tactic.h"
#include"bit_blaster_tactic.h"
#include"elim_uncnstr_tactic.h"
#include"max_bv_sharing_tactic.h"
#include"bv_size_reduction_tactic.h"
#include"ctx_simplify_tactic.h"
#include"th_rewriter.h"
#include"smt2parser.h"
#include <strstream>

using std::endl;

class label_removal {
public:
    label_removal(ast_manager& m)
        : m(m) {}

    void operator () (expr * in, expr_ref& out) {
        ptr_vector<expr> stack;
        expr *           curr;
        expr_mark        visited;
        obj_map<expr, expr*> e2e;
        stack.push_back(in);
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
                e2e.insert(curr, curr);
                break;

            case AST_APP: {
                app *  a = to_app(curr);
                if (for_each_expr_args(stack, visited, a->get_num_args(), a->get_args())) {
                    visited.mark(curr, true);
                    stack.pop_back();
                    buffer<symbol>  names;
                    if (m.is_label_lit(a,names)) {
                        SASSERT(names.size()==1);
                        e2e.insert(curr, m.mk_true());
                    }
                    else if (m.is_label(a)) {
                        e2e.insert(a, e2e[a->get_arg(0)]);
                    }
                    else {
                        ptr_vector<expr> ags;
                        bool c = false;
                        for (unsigned i = 0; i < a->get_num_args(); ++i) {
                            const expr *  const old = a->get_arg(i);
                            expr *  const n = e2e[a->get_arg(i)];
                            if (old != n) c = true;
                            if (n) ags.push_back(n);
                        }
                        if (c) e2e.insert(curr, m.mk_app(a->get_decl(), ags.size(), ags.c_ptr()));
                        else e2e.insert(curr, curr);
                    }
                }
            }
                break;
            case AST_QUANTIFIER: {
                quantifier * const q = to_quantifier(curr);
                if (visited.is_marked(q->get_expr())) {                     
                    e2e.insert(q, m.update_quantifier(q, e2e[q->get_expr()]));
                    visited.mark(curr, true);
                    stack.pop_back();
                }
                else {
                    stack.push_back(q->get_expr());
                }
            }
                break;
            default:
                UNREACHABLE();
            }
        }
        out = e2e[in];
        e2e.reset();
        visited.reset();
    }
protected:
    ast_manager& m;
};

lbool call_external(ast_manager& m, func_decl_ref_vector& free_decls,
    solver* s, model_ref& model, params_ref p);


/* solver used to solve by the unquantified part. */
inline solver* mk_sat_solver(bool uf, ast_manager& m, const params_ref& p);//TODO: pass factory instead

/* CEGAR-Based approach to two level quantification problems a la AReQS. */
class q2_tactic : public tactic {
public:
    enum Mode { BV, UFBV }; // pure a bit-vectors or also uninterpreted functions in the matrix. 
                                //TODO set by params

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
        TRACE("q2", g->display(tout << "Goal:\n"););
        expr_ref_vector flas_refs(m);
        if (0) {
            g->get_formulas(flas);
        }
        else {
            for (unsigned i = 0; i < g->size(); i++) {
                expr_ref sc(m);
                label_removal lr(m);
                lr(g->form(i), sc);
                flas_refs.push_back(sc);
                flas.push_back(sc.get());
                if (sc.get() != g->form(i)) {
                    TRACE("q2",
                        tout << "orig:(\n" << mk_ismt2_pp(g->form(i), m, 2) << ")\n";
                    tout << "no lb:(\n" << mk_ismt2_pp(sc.get(), m, 2) << ")\n";
                    );
                }
            }
        }
        // Running implementation 
        imp i(m, m_p, q2_tactic::UFBV, flas);
        const lbool o = i();
        flas.reset();
        flas_refs.reset();
        // Report result 
        goal_ref resg(alloc(goal, *g, true));
        if (o == l_false) resg->assert_expr(m.mk_false());
        if (o != l_undef) result.push_back(resg.get());
        // TODO Report model 
    }

    virtual void cleanup() { }

    virtual tactic* translate(ast_manager& m) {
        return alloc(q2_tactic, m, m_p);
    }
private:
    ast_manager& m_m;
    params_ref m_p;

    // A wrapper for the solver used to obtain counterexamples,
    // i.e. moves for the universal player, given a move for existential.
    class CexWrap {
    public:
        CexWrap(ast_manager&m, params_ref p, Mode mode)
            : m(m)
            , mode(mode)
            , p(p)
            , nmx(NULL, m)
            , cex_sat(mode == BV ? mk_sat_solver(false, m, p) : NULL)
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
            if (mode == BV) cex_sat->assert_expr(nmx);
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
        Mode mode;
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
        CandWrap(ast_manager& m, params_ref p, Mode& mode)
            : m(m)
            , p(p)
            , free_decls(free_decls)
            , ex_decls(m)
            , sat(mk_sat_solver(mode == UFBV, m, p))
            , simp(m)
        {  }

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
            if (0) {
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
        func_decl_ref_vector free_decls;
        func_decl_ref_vector ex_decls;
        solver * sat;
        model_ref cand_model;
        th_rewriter simp;
    };



    // Implementation of the CEGAR loop.
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
            , simp(m)
            , cands(m, p, mode)

        {}

        ~imp() {
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
                    CexWrap* const cex = alloc(CexWrap, m, p, mode);
                    expr_ref nmx(m);
                    simp(m.mk_not(f), nmx);
                    cex->add_forall(forall_decls);
                    cex->set_nmx(nmx);
                    //cands.init_refine(cexs.back());
                    cexs.push_back(cex);
                }
                else {// assert an unquantified formula 
                    cands.assert(f);
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
                //if (count) return l_undef;
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
};

inline solver* mk_sat_solver(bool uf, ast_manager& m, const params_ref& _p) {
    params_ref p;
    p.copy(_p);
    if (!uf) return mk_inc_sat_solver(m, p);
    //return mk_smt_solver(m,p, symbol("UFBV"));
    //return mk_smt_solver(m, p, symbol());
    tactic_ref t = mk_qfaufbv_tactic(m, p);
    //tactic_ref t = mk_smt_tactic(p);	
    solver* rv = mk_tactic2solver(m, t.get(), p);
    rv->set_produce_models(true);
    SASSERT(rv);
    return rv;
}

lbool call_external(ast_manager& m, func_decl_ref_vector& free_decls,
    solver* s, model_ref& model, params_ref p) {
    //const char * ifn="C:\\cygwin\\home\\mikolas\\git\\z3\\test\\foo.smt2";
    const char * ifn="C:\\cygwin\\home\\mikolas\\git\\z3\\test\\foo.smt2";
    const char * ofn="C:\\cygwin\\home\\mikolas\\git\\z3\\test\\bar.smt2";
    { std::ofstream out(ifn); s->display(out); out.close(); }
    std::stringstream cms;
    cms << "C:\\cygwin\\home\\mikolas\\git\\z3\\test\\boolector.exe"
        << " " << "--smt2 -m --smt2-model --hex"
        << " " << ifn
        << " >" << ofn;
    std::string cmdstr(cms.str());
    std::cerr << "cmd: " << cmdstr << std::endl;
    const int rv = system(cmdstr.c_str());
    //int rv = 10;
    if (rv == 10) {
        std::ifstream is(ofn);
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

tactic * mk_q2_tactic(ast_manager & m, params_ref const & p) {
    return alloc(q2_tactic, m, p);
    params_ref main_p;
    main_p.set_bool("elim_and", true);
    main_p.set_bool("sort_store", true);
    //main_p.set_bool("expand_select_store", true);
    //main_p.set_bool("expand_store_eq", true);

    params_ref simp2_p = p;
    simp2_p.set_bool("som", true);
    simp2_p.set_bool("pull_cheap_ite", true);
    simp2_p.set_bool("push_ite_bv", false);
    simp2_p.set_bool("local_ctx", true);
    simp2_p.set_uint("local_ctx_limit", 10000000);

    params_ref ctx_simp_p;
    ctx_simp_p.set_uint("max_depth", 32);
    ctx_simp_p.set_uint("max_steps", 5000000);

    tactic * const preamble_t = and_then(
        mk_simplify_tactic(m),
        mk_propagate_values_tactic(m),
        //using_params(mk_ctx_simplify_tactic(m), ctx_simp_p),
        mk_solve_eqs_tactic(m),
        mk_elim_uncnstr_tactic(m),
        if_no_proofs(if_no_unsat_cores(mk_bv_size_reduction_tactic(m))),
        using_params(mk_simplify_tactic(m), simp2_p),
        mk_max_bv_sharing_tactic(m),
        mk_macro_finder_tactic(m, p),
        mk_nnf_tactic(m, p)
        );

    return and_then(
        preamble_t,
        alloc(q2_tactic, m, p));
}
