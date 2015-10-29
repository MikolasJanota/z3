/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    nlsat.cpp

Abstract:

    nlsat procedure

Author:

    Leonardo (leonardo) 2012-01-09

Notes:

--*/
#include"nlsat_assignment.h"
#include"nlsat_interval_set.h"
#include"nlsat_evaluator.h"
#include"nlsat_solver.h"
#include"util.h"
#include"nlsat_explain.h"
#include"polynomial_cache.h"

nlsat::interval_set_ref tst_interval(nlsat::interval_set_ref const & s1,
                                     nlsat::interval_set_ref const & s2,
                                     unsigned expected_num_intervals,
                                     bool check_num_intervals = true) {
    nlsat::interval_set_manager & ism = s1.m();
    nlsat::interval_set_ref r(ism);
    std::cout << "s1:            " << s1 << "\n";
    std::cout << "s2:            " << s2 << "\n";
    r = ism.mk_union(s1, s2);
    std::cout << "union(s1, s2): " << r <<  std::endl;
    SASSERT(!check_num_intervals || ism.num_intervals(r) == expected_num_intervals);
    SASSERT(ism.subset(s1, r));
    SASSERT(ism.subset(s2, r));
    if (ism.set_eq(s1, s2)) {
        SASSERT(ism.set_eq(s1, r));
        SASSERT(ism.set_eq(s2, r));
    }
    else {
        SASSERT(ism.subset(s1, s2) || !ism.subset(r, s2));
        SASSERT(ism.subset(s2, s1) || !ism.subset(r, s1));
    }
    nlsat::interval_set_ref r2(ism);
    r2 = ism.mk_union(s2, s1);
    SASSERT(ism.set_eq(r, r2));
    anum zero;
    nlsat::interval_set_ref full(ism);
    nlsat::literal dummy(131, false);
    full = ism.mk(true, true, zero, true, true, zero, dummy);
    SASSERT(ism.set_eq(r, full) == ism.is_full(r));
    return r;
}

static void tst3() {
    enable_trace("nlsat_interval");
    unsynch_mpq_manager         qm;
    anum_manager                am(qm);
    small_object_allocator      allocator;
    nlsat::interval_set_manager ism(am, allocator);

    scoped_anum               sqrt2(am), m_sqrt2(am), two(am), m_two(am), three(am), one(am), zero(am);
    am.set(two, 2);
    am.set(m_two, -2);
    am.set(one, 1);
    am.root(two, 2, sqrt2);
    am.set(m_sqrt2, sqrt2);
    am.neg(m_sqrt2);
    am.set(three, 3);
    
    nlsat::literal p1(1, false);
    nlsat::literal p2(2, false);
    nlsat::literal p3(3, false);
    nlsat::literal p4(4, false);
    nlsat::literal np2(2, true);
    
    nlsat::interval_set_ref s1(ism), s2(ism), s3(ism), s4(ism);
    s1 = ism.mk_empty();
    std::cout << "s1: " << s1 << "\n";
    s2 = ism.mk(true, true, zero, false, false, sqrt2, np2);
    std::cout << "s2: " << s2 << "\n";
    s3 = ism.mk(false, false, zero, false, false, two, p1);
    std::cout << "s3: " << s3 << "\n";
    s4 = ism.mk_union(s2, s3);
    std::cout << "s4: " << s4 << "\n";

    // Case
    //  s1:   [ ... ]
    //  s2:   [ ... ]
    s1 = ism.mk(false, false, zero, false, false, two, p1);
    s2 = ism.mk(false, false, zero, false, false, two, p2);
    tst_interval(s1, s2, 1);

    // Case 
    // s1:   [ ... ]
    // s2: [ ... ]
    s1 = ism.mk(false, false, zero, false, false, two, p1);
    s2 = ism.mk(false, false, m_sqrt2, false, false, one, p2);
    s3 = ism.mk_union(s1, s2);
    tst_interval(s1, s2, 2);

    // Case 
    // s1:   [ ... ]
    // s2:      [ ... ]
    s1 = ism.mk(false, false, m_sqrt2, false, false, one, p1);
    s2 = ism.mk(false, false, zero, false, false, two, p2);
    tst_interval(s1, s2, 2);

    // Case 
    // s1:   [ ... ]
    // s2:            [ ... ]
    s1 = ism.mk(false, false, m_sqrt2, false, false, one, p1);
    s2 = ism.mk(false, false, two, false, false, three, p2);
    tst_interval(s1, s2, 2);

    // Case 
    // s1:   [    ...    ]
    // s2:      [ ... ]
    s1 = ism.mk(false, false, m_sqrt2, false, false, three, p1);
    s2 = ism.mk(false, false, zero, false, false, two, p2);
    tst_interval(s1, s2, 1);

    // Case 
    // s1:   [    ...      ]
    // s2:      [ ... ] [  ...  ]
    s1 = ism.mk(false, false, m_two, false, false, two, p1);
    s2 = ism.mk(false, false, m_sqrt2, false, false, zero, p2);
    s3 = ism.mk(false, false, one, false, false, three, p2);
    s2 = ism.mk_union(s2, s3);
    tst_interval(s1, s2, 2);

    // Case
    // s1:  [ ... ]
    // s2:        [ ... ]
    s1 = ism.mk(false, false, m_two, false, false, two, p1);
    s2 = ism.mk(false, false, two, false, false, three, p2);
    tst_interval(s1, s2, 2);
    s2 = ism.mk(true, false, two, false, false, three, p2);
    tst_interval(s1, s2, 2);
    s2 = ism.mk(true, false, two, false, false, three, p1);
    tst_interval(s1, s2, 1);
    s1 = ism.mk(false, false, m_two, true, false, two, p1);
    tst_interval(s1, s2, 2);
    s1 = ism.mk(false, false, two, false, false, two, p1);
    s2 = ism.mk(false, false, two, false, false, three, p2);
    tst_interval(s1, s2, 1);

    // Case
    // s1:  [ ... ]    [ ...  ]
    // s2: [ .. ]   [ ... ] [ ... ]
    s1 = ism.mk(false, false, m_two, false, false, zero, p1);
    s3 = ism.mk(false, false, one, false, false,   three, p1);
    s1 = ism.mk_union(s1, s3);
    s2 = ism.mk(true, true, zero,  false, false, m_sqrt2, p2);
    tst_interval(s1, s2, 3);
    s3 = ism.mk(false, false, one, false, false, sqrt2, p2);
    s2 = ism.mk_union(s2, s3);
    s3 = ism.mk(false, false, two, true, true, zero, p2);
    s2 = ism.mk_union(s2, s3);
    tst_interval(s1, s2, 4);

    // Case
    s1 = ism.mk(true, true, zero, false, false, one, p1);
    s2 = ism.mk(true, false, one, true, true, zero, p2);
    tst_interval(s1, s2, 2);
    s2 = ism.mk(true, false, one, false, false, two, p2);
    s3 = ism.mk(false, false, two, true, true, zero, p1);
    s2 = ism.mk_union(s2, s3);
    tst_interval(s1, s2, 3);
}

static nlsat::interval_set_ref mk_random(nlsat::interval_set_manager & ism, anum_manager & am, int range, int space, int tries, bool minus_inf, bool plus_inf,
                                       nlsat::literal lit) {
    static random_gen gen;
    SASSERT(range > 0);
    SASSERT(space > 0);
    nlsat::interval_set_ref r(ism), curr(ism);
    scoped_anum lower(am);
    scoped_anum upper(am);
    int prev = -range + (gen() % (space*4));

    if (gen() % 3 == 0 && minus_inf) {
        int  next = prev + (gen() % space);
        bool open = gen() % 2 == 0;
        am.set(upper, next);
        r = ism.mk(true, true, lower, open, false, upper, lit);
        prev = next;
    }

    for (int i = 0; i < tries; i++) {
        int l = prev  + (gen() % space);
        int u = l + (gen() % space);
        bool lower_open = gen() % 2 == 0;
        bool upper_open = gen() % 2 == 0;
        if ((lower_open || upper_open) && l == u)
            u++;
        am.set(lower, l);
        am.set(upper, u);
        curr = ism.mk(lower_open, false, lower, upper_open, false, upper, lit);
        r = ism.mk_union(r, curr);
        prev = u;
    }

    if (gen() % 3 == 0 && plus_inf) {
        int  next = prev + (gen() % space);
        bool open = gen() % 2 == 0;
        am.set(lower, next);
        curr = ism.mk(open, false, lower, true, true, upper, lit);
        r = ism.mk_union(r, curr);
    }
    return r;
}

static void check_subset_result(nlsat::interval_set_ref const & s1, 
                                nlsat::interval_set_ref const & s2,
                                nlsat::interval_set_ref const & r,
                                nlsat::literal l1,
                                nlsat::literal l2) {
    nlsat::interval_set_manager ism(s1.m());
    nlsat::interval_set_ref tmp(ism);
    unsigned num = ism.num_intervals(r);
    nlsat::literal_vector lits;
    ism.get_justifications(r, lits);
    SASSERT(lits.size() <= 2);
    for (unsigned i = 0; i < num; i++) {
        tmp = ism.get_interval(r, i);
        ism.get_justifications(tmp, lits);
        SASSERT(lits.size() == 1);
        if (lits[0] == l1) {
            SASSERT(ism.subset(tmp, s1));
        }
        else {
            SASSERT(lits[0] == l2);
            SASSERT(ism.subset(tmp, s2));
        }
    }
}

static void tst4() {
    enable_trace("nlsat_interval");
    unsynch_mpq_manager         qm;
    anum_manager                am(qm);
    small_object_allocator      allocator;
    nlsat::interval_set_manager ism(am, allocator);
    nlsat::interval_set_ref     s1(ism), s2(ism), r(ism);

    nlsat::literal l1(1, false);
    nlsat::literal l2(2, false);
    
    for (unsigned i = 0; i < 100; i++) {
        s1 = mk_random(ism, am, 20, 3, 10, true, true, l1);
        s2 = mk_random(ism, am, 20, 3, 10, true, true, l2);
        r = tst_interval(s1, s2, 0, false);
        check_subset_result(s1, s2, r, l1, l2);
    }

    for (unsigned i = 0; i < 100; i++) {
        s1 = mk_random(ism, am, 200, 100, 20, true, true, l1);
        s2 = mk_random(ism, am, 200, 100, 20, true, true, l2);
        r = tst_interval(s1, s2, 0, false);
        check_subset_result(s1, s2, r, l1, l2);
    }
}

static void tst5() {
    params_ref      ps;
    reslimit        rlim;
    nlsat::solver s(rlim, ps);
    anum_manager & am = s.am();
    nlsat::pmanager & pm = s.pm();
    nlsat::assignment           as(am);
    small_object_allocator      allocator;
    nlsat::interval_set_manager ism(am, allocator);
    nlsat::evaluator            ev(as, pm, allocator);
    nlsat::var                  x0, x1;
    x0 = pm.mk_var();
    x1 = pm.mk_var();
    nlsat::interval_set_ref i(ism);

    polynomial_ref p(pm);
    polynomial_ref _x0(pm), _x1(pm);
    _x0 = pm.mk_polynomial(x0);
    _x1 = pm.mk_polynomial(x1);
    p = (_x0^2) + (_x1^2) - 2;
    nlsat::poly * _p[1] = { p.get() };
    bool is_even[1] = { false };
    nlsat::bool_var b = s.mk_ineq_atom(nlsat::atom::GT, 1, _p, is_even);
    nlsat::atom * a = s.bool_var2atom(b);
    SASSERT(a != 0);
    scoped_anum zero(am);
    am.set(zero, 0);
    as.set(0, zero);
    i = ev.infeasible_intervals(a, true);
    std::cout << "1) " << i << "\n";
    as.set(1, zero);
    i = ev.infeasible_intervals(a, true);
    std::cout << "2) " << i << "\n";
}



static void project(nlsat::solver& s, nlsat::explain& ex, nlsat::var x, unsigned num, nlsat::literal const* lits) {
    s.display(std::cout, num, lits);
    nlsat::scoped_literal_vector result(s);
    ex.project(x, num, lits, result);
    s.display(std::cout << " ==> ", result.size(), result.c_ptr());
    std::cout << "\n";
}

static nlsat::literal mk_gt(nlsat::solver& s, nlsat::poly* p) {
    nlsat::poly * _p[1] = { p };
    bool is_even[1] = { false };
    return s.mk_ineq_literal(nlsat::atom::GT, 1, _p, is_even);
}

static nlsat::literal mk_eq(nlsat::solver& s, nlsat::poly* p) {
    nlsat::poly * _p[1] = { p };
    bool is_even[1] = { false };
    return s.mk_ineq_literal(nlsat::atom::EQ, 1, _p, is_even);
}

static void tst6() {
    params_ref      ps;
    reslimit        rlim;
    nlsat::solver s(rlim, ps);
    anum_manager & am     = s.am();
    nlsat::pmanager & pm  = s.pm();
    nlsat::assignment as(am);
    nlsat::explain& ex    = s.get_explain();
    nlsat::var x0, x1, x2, a, b, c, d;
    a  = s.mk_var(false);
    b  = s.mk_var(false);
    c  = s.mk_var(false);
    d  = s.mk_var(false);
    x0 = s.mk_var(false);
    x1 = s.mk_var(false);
    x2 = s.mk_var(false);

    polynomial_ref p1(pm), p2(pm), p3(pm), p4(pm), p5(pm);
    polynomial_ref _x0(pm), _x1(pm), _x2(pm);
    polynomial_ref _a(pm), _b(pm), _c(pm), _d(pm);
    _x0 = pm.mk_polynomial(x0);
    _x1 = pm.mk_polynomial(x1);
    _x2 = pm.mk_polynomial(x2);
    _a  = pm.mk_polynomial(a);
    _b  = pm.mk_polynomial(b);
    _c  = pm.mk_polynomial(c);
    _d  = pm.mk_polynomial(d);

    p1 = (_a*(_x0^2)) + _x2 + 2;
    p2 = (_b*_x1) - (2*_x2) - _x0 + 8;
    nlsat::scoped_literal_vector lits(s);
    lits.push_back(mk_gt(s, p1));
    lits.push_back(mk_gt(s, p2));
    lits.push_back(mk_gt(s, (_c*_x0) + _x2 + 1));
    lits.push_back(mk_gt(s, (_d*_x0) - _x1 + 5*_x2));

    scoped_anum zero(am), one(am), two(am);
    am.set(zero, 0);
    am.set(one,  1);
    am.set(two,  2);
    as.set(0, one);
    as.set(1, one);
    as.set(2, two);
    as.set(3, two);
    as.set(4, two);
    as.set(5, one);
    as.set(6, one); 
    s.set_rvalues(as);


    project(s, ex, x0, 2, lits.c_ptr());
    project(s, ex, x1, 3, lits.c_ptr());
    project(s, ex, x2, 3, lits.c_ptr());
    project(s, ex, x2, 2, lits.c_ptr());
    project(s, ex, x2, 4, lits.c_ptr());
    project(s, ex, x2, 3, lits.c_ptr()+1);
    
    
}

static void tst7() {
    params_ref      ps;
    reslimit        rlim;
    nlsat::solver s(rlim, ps);
    anum_manager & am     = s.am();
    nlsat::pmanager & pm  = s.pm();
    nlsat::var x0, x1, x2, a, b, c, d;
    a  = s.mk_var(false);
    b  = s.mk_var(false);
    c  = s.mk_var(false);
    d  = s.mk_var(false);
    x0 = s.mk_var(false);
    x1 = s.mk_var(false);
    x2 = s.mk_var(false);
    polynomial_ref p1(pm), p2(pm), p3(pm), p4(pm), p5(pm);
    polynomial_ref _x0(pm), _x1(pm), _x2(pm);
    polynomial_ref _a(pm), _b(pm), _c(pm), _d(pm);
    _x0 = pm.mk_polynomial(x0);
    _x1 = pm.mk_polynomial(x1);
    _x2 = pm.mk_polynomial(x2);
    _a  = pm.mk_polynomial(a);
    _b  = pm.mk_polynomial(b);
    _c  = pm.mk_polynomial(c);
    _d  = pm.mk_polynomial(d);

    p1 = _x0 + _x1;
    p2 = _x2 - _x0;
    p3 = (-1*_x0) - _x1;
    
    nlsat::scoped_literal_vector lits(s);
    lits.push_back(mk_gt(s, p1));
    lits.push_back(mk_gt(s, p2));
    lits.push_back(mk_gt(s, p3));

    nlsat::literal_vector litsv(lits.size(), lits.c_ptr());
    lbool res = s.check(litsv);
    SASSERT(res == l_false);
    for (unsigned i = 0; i < litsv.size(); ++i) {
        s.display(std::cout, litsv[i]);
        std::cout << " ";
    }
    std::cout << "\n";

    litsv.reset();
    litsv.append(2, lits.c_ptr());
    res = s.check(litsv);
    SASSERT(res == l_true);
    s.display(std::cout);
    s.am().display(std::cout, s.value(x0)); std::cout << "\n";
    s.am().display(std::cout, s.value(x1)); std::cout << "\n";
    s.am().display(std::cout, s.value(x2)); std::cout << "\n";

}

static void tst8() {
    params_ref      ps;
    reslimit        rlim;
    nlsat::solver s(rlim, ps);
    anum_manager & am     = s.am();
    nlsat::pmanager & pm  = s.pm();
    nlsat::assignment as(am);
    nlsat::explain& ex    = s.get_explain();
    nlsat::var x0, x1, x2, a, b, c, d;
    a  = s.mk_var(false);
    b  = s.mk_var(false);
    c  = s.mk_var(false);
    d  = s.mk_var(false);
    x0 = s.mk_var(false);
    x1 = s.mk_var(false);
    x2 = s.mk_var(false);

    polynomial_ref p1(pm), p2(pm), p3(pm), p4(pm), p5(pm);
    polynomial_ref _x0(pm), _x1(pm), _x2(pm);
    polynomial_ref _a(pm), _b(pm), _c(pm), _d(pm);
    _x0 = pm.mk_polynomial(x0);
    _x1 = pm.mk_polynomial(x1);
    _x2 = pm.mk_polynomial(x2);
    _a  = pm.mk_polynomial(a);
    _b  = pm.mk_polynomial(b);
    _c  = pm.mk_polynomial(c);
    _d  = pm.mk_polynomial(d);
    
    scoped_anum zero(am), one(am), two(am), six(am);
    am.set(zero, 0);
    am.set(one,  1);
    am.set(two,  2);
    am.set(six,  6);
    as.set(0, two); // a
    as.set(1, one); // b
    as.set(2, six); // c
    as.set(3, zero); // d
    as.set(4, zero); // x0
    as.set(5, zero); // x1
    as.set(6, two); // x2
    s.set_rvalues(as);

    nlsat::scoped_literal_vector lits(s);
    lits.push_back(mk_eq(s, (_a*_x2*_x2) - (_b*_x2) - _c));
    project(s, ex, x2, 1, lits.c_ptr());
    exit(0);
}

void tst_nlsat() {
    tst8();
    std::cout << "------------------\n";
    tst7();
    std::cout << "------------------\n";
    tst6();
    std::cout << "------------------\n";
    tst5();
    std::cout << "------------------\n";
    tst4();
    std::cout << "------------------\n";
    tst3();
}
