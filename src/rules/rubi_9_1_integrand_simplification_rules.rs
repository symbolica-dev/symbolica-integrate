use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_1(rules);
    push_rules_rule_2(rules);
    push_rules_rule_3(rules);
    push_rules_rule_4(rules);
    push_rules_rule_5(rules);
    push_rules_rule_6(rules);
    push_rules_rule_7(rules);
    push_rules_rule_8(rules);
    push_rules_rule_9(rules);
    push_rules_rule_10(rules);
    push_rules_rule_11(rules);
    push_rules_rule_12(rules);
    push_rules_rule_13(rules);
    push_rules_rule_25(rules);
    push_rules_rule_26(rules);
    push_rules_rule_27(rules);
    push_rules_rule_24(rules);
    push_rules_rule_2009(rules);
    push_rules_rule_2010(rules);
    push_rules_rule_2011(rules);
    push_rules_rule_2012(rules);
    push_rules_rule_2013(rules);
    // The first Rubi 9.1 block 24 row is commented out in the markdown source.

    push_rules_rule_2014(rules);
    push_rules_rule_2015(rules);
    push_rules_rule_2016(rules);
    push_rules_rule_1380(rules);
    push_rules_rule_1384(rules);
    push_rules_rule_1385(rules);
}

fn push_rules_rule_1(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, n_, p_, u__, x_);
    let rule = rubi_rule!(
        order: 1,
        source: "Int[u_.*(a_+b_.*x_^n_.)^p_.,x_Symbol] :=
          Int[u*(b*x^n)^p,x] /;
        FreeQ[{a,b,n,p},x] && EqQ[a,0]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [u__, a__, b__, n_, p_, x_],
        optional: [u__, b__, n_, p_],
        x_free: [n_, p_],
        zero: [a__],
        when: { freeq!([a__, b__, n_, p_], x_) && eqq!(a__, 0) },
        rhs: {
            rubi_rhs_int(&(u__ * (b__ * x_.pow(&n_)).pow(&p_)), x_)
        },
    );
    rules.push(rule.with_algebraic_zero_x_free_additive_part(1));
}

fn push_rules_rule_2(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, n_, p_, u__, x_);
    rules.push(rubi_rule!(
        order: 2,
        source: "Int[u_.*(a_.+b_.*x_^n_.)^p_.,x_Symbol] :=
          Int[u*a^p,x] /;
        FreeQ[{a,b,n,p},x] && EqQ[b,0]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [u__, a__, b__, n_, p_, x_],
        optional: [u__, a__, b__, n_, p_],
        x_free: [n_, p_],
        zero: [b__],
        when: { freeq!([a__, b__, n_, p_], x_) && eqq!(b__, 0) },
        rhs: { rubi_rhs_int(&(u__ * a__.pow(&p_)), x_) },
    ));
}

fn push_rules_rule_3(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, j_, n_, p_, u__, x_);
    let rule = rubi_rule!(
        order: 3,
        source: "Int[u_.*(a_+b_.*x_^n_.+c_.*x_^j_.)^p_.,x_Symbol] :=
          Int[u*(b*x^n+c*x^(2*n))^p,x] /;
        FreeQ[{a,b,c,n,p},x] && EqQ[j,2*n] && EqQ[a,0]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [u__, a__, b__, n_, c__, j_, p_, x_],
        optional: [u__, b__, n_, c__, j_, p_],
        x_free: [n_, p_],
        zero: [a__],
        scaled: [(j_, 2, n_)],
        when: {
            freeq!([a__, b__, c__, n_, p_], x_)
                && eqq!(j_, Atom::num(2) * &n_)
                && eqq!(a__, 0)
        },
        rhs: {
            rubi_rhs_int(&(u__ * (&b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_)).pow(&p_)), x_)
        },
    );
    rules.push(rule.with_algebraic_zero_x_free_additive_part(2));
}

fn push_rules_rule_4(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, j_, n_, p_, u__, x_);
    rules.push(rubi_rule!(
        order: 4,
        source: "Int[u_.*(a_.+b_.*x_^n_.+c_.*x_^j_.)^p_.,x_Symbol] :=
          Int[u*(a+c*x^(2*n))^p,x] /;
        FreeQ[{a,b,c,n,p},x] && EqQ[j,2*n] && EqQ[b,0]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [u__, a__, b__, n_, c__, j_, p_, x_],
        optional: [u__, a__, b__, n_, c__, j_, p_],
        x_free: [n_, p_],
        zero: [b__],
        when: {
            freeq!([a__, b__, c__, n_, p_], x_)
                && eqq!(j_, Atom::num(2) * &n_)
                && eqq!(b__, 0)
        },
        rhs: {
            rubi_rhs_int(&(u__ * (&a__ + &c__ * x_.pow(Atom::num(2) * &n_)).pow(&p_)), x_)
        },
    ));
}

fn push_rules_rule_5(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, j_, n_, p_, u__, x_);
    rules.push(rubi_rule!(
        order: 5,
        source: "Int[u_.*(a_.+b_.*x_^n_.+c_.*x_^j_.)^p_.,x_Symbol] :=
          Int[u*(a+b*x^n)^p,x] /;
        FreeQ[{a,b,c,n,p},x] && EqQ[j,2*n] && EqQ[c,0]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [u__, a__, b__, n_, c__, j_, p_, x_],
        optional: [u__, a__, b__, n_, c__, j_, p_],
        x_free: [n_, p_],
        zero: [c__],
        when: {
            freeq!([a__, b__, c__, n_, p_], x_)
                && eqq!(j_, Atom::num(2) * &n_)
                && eqq!(c__, 0)
        },
        rhs: {
            rubi_rhs_int(&(u__ * (&a__ + &b__ * x_.pow(&n_)).pow(&p_)), x_)
        },
    ));
}

fn push_rules_rule_6(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, fx__, p_, u__, v__);
    rules.push(rubi_rule!(
        order: 6,
        source: "Int[u_.*(v_.+a_.*Fx_+b_.*Fx_)^p_.,x_Symbol] :=
          Int[u*(v+(a+b)*Fx)^p,x] /;
        FreeQ[{a,b},x] && Not[FreeQ[Fx,x]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern: u__ * (v__ + a__ * fx__ + b__ * fx__).pow(p_),
        with: [u__, v__, a__, fx__, b__, p_, x_],
        optional: [u__, v__, a__, b__, p_],
        x_dep: [fx__],
        x_free: [a__, b__],
        when: { freeq!([a__, b__], x_) },
        rhs: {
            rubi_rhs_int(
                &(u__ * (v__ + (a__ + b__) * fx__).pow(&p_)),
                x_,
            )
        },
    ));
}

fn push_rules_rule_7(rules: &mut Vec<RubiRule>) {
    rubi_symb!(p_, px_, u__);
    rules.push(rubi_rule!(
        order: 7,
        source: "Int[u_.*Px_^p_,x_Symbol] :=
          Int[u*Px^Simplify[p],x] /;
        PolyQ[Px,x] && Not[RationalQ[p]] && FreeQ[p,x] && RationalQ[Simplify[p]]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: u__ * px_.pow(p_),
        with: [u__, px_, p_, x_],
        optional: [u__],
        x_free: [p_],
        when: {
            rubi_poly_q(&px_, x_)
                && !rationalq!(p_)
                && freeq!(p_, x_)
                && rationalq!(rubi_simplify(&p_))
        },
        rhs: { rubi_rhs_int(&(u__ * px_.pow(rubi_simplify(&p_))), x_) },
    ));
}

fn push_rules_rule_8(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, m_, p_, u__, x_);
    rules.push(rubi_rule!(
        order: 8,
        source: "Int[u_.*x_^m_.*(a_.*x_)^p_,x_Symbol] :=
          1/a^m \\[Star] Int[u*(a*x)^(m+p),x] /;
        FreeQ[{a,m,p},x] && IntegerQ[m]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern: u__ * x_.pow(m_) * (a__ * x_).pow(p_),
        with: [u__, m_, a__, p_, x_],
        optional: [u__, m_, a__],
        x_free: [a__, m_, p_],
        when: { freeq!([a__, m_, p_], x_) && integerq!(m_) },
        rhs: {
            rubi_star(Atom::num(1) / a__.pow(&m_), rubi_rhs_int(
                &(u__ * (&a__ * x_).pow(&m_ + &p_)),
                x_,
            ))
        },
    ));
}

fn push_rules_rule_9(rules: &mut Vec<RubiRule>) {
    rubi_symb!(e__, m_, p_, px_, u__, x_);
    rules.push(rubi_rule!(
        order: 9,
        source: "Int[u_.*(e_.*x_)^m_.*Px_^p_.,x_Symbol] :=
          With[{r=Expon[Px,x,Min]},
          1/e^(p*r) \\[Star] Int[u*(e*x)^(m+p*r)*ExpandToSum[Px/x^r,x]^p,x] /;
         IGtQ[r,0]] /;
        FreeQ[{e,m},x] && PolyQ[Px,x] && IntegerQ[p] && Not[MonomialQ[Px,x]]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern: u__ * px_.pow(p_) * (e__ * x_).pow(m_),
        with: [u__, px_, p_, e__, m_, x_],
        optional: [u__, p_, e__, m_],
        when: {
            freeq!([e__, m_], x_)
                && rubi_poly_q(&px_, x_)
                && integerq!(p_)
                && !rubi_monomial_q(&px_, x_)
                && rubi_minimum_monomial_exponent(&px_, x_).is_some_and(|r| r > 0)
        },
        rhs: {
            let r = rubi_minimum_monomial_exponent(&px_, x_).rubi_rhs();
            let r_atom = Atom::num(r);
            let shifted_px = rubi_expand_to_sum(&(px_ / x_.pow(r)), x_);
            let transformed_integrand =
                u__ * (&e__ * x_).pow(&m_ + &p_ * &r_atom) * shifted_px.pow(&p_);
            let recursive = rubi_rhs_int(&transformed_integrand, x_);
            rubi_star(Atom::num(1) / e__.pow(&p_ * r_atom), recursive)
        },
    ));
}

fn push_rules_rule_10(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, e__, m_, p_, r_, s_, u__, x_);
    rules.push(rubi_rule!(
        order: 10,
        source: "Int[u_.*(e_.*x_)^m_.*(a_.*x_^r_.+b_.*x_^s_.)^p_.,x_Symbol] :=
          1/e^(p*r) \\[Star] Int[u*(e*x)^(m+p*r)*(a+b*x^(s-r))^p,x] /;
        FreeQ[{a,b,e,m,r,s},x] && IntegerQ[p] && (IntegerQ[p*r] || GtQ[e,0]) && PosQ[s-r]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern: u__
            * (e__ * x_).pow(m_)
            * (a__ * x_.pow(r_) + b__ * x_.pow(s_)).pow(p_),
        with: [u__, e__, m_, a__, r_, b__, s_, p_, x_],
        optional: [u__, e__, m_, a__, r_, b__, s_, p_],
        x_free: [a__, b__, e__, m_, r_, s_],
        when: {
            freeq!([a__, b__, e__, m_, r_, s_], x_)
                && integerq!(p_)
                && (integerq!(&p_ * &r_) || gtq!(e__, 0))
                && posq!(&s_ - &r_)
        },
        rhs: {
            let transformed = u__
                * (&e__ * x_).pow(&m_ + &p_ * &r_)
                * (&a__ + &b__ * x_.pow(&s_ - &r_)).pow(&p_);
            rubi_star(Atom::num(1) / e__.pow(&p_ * &r_), rubi_rhs_int(&transformed, x_))
        },
    ));
}

fn push_rules_rule_11(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, e__, m_, p_, r_, s_, t_, u__, x_);
    rules.push(rubi_rule!(
        order: 11,
        source: "Int[u_.*(e_.*x_)^m_.*(a_.*x_^r_.+b_.*x_^s_.+c_.*x_^t_.)^p_.,x_Symbol] :=
          1/e^(p*r) \\[Star] Int[u*(e*x)^(m+p*r)*(a+b*x^(s-r)+c*x^(t-r))^p,x] /;
        FreeQ[{a,b,c,e,m,r,s,t},x] && IntegerQ[p] && (IntegerQ[p*r] || GtQ[e,0]) && PosQ[s-r] && PosQ[t-r]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern: u__
            * (e__ * x_).pow(m_)
            * (a__ * x_.pow(r_) + b__ * x_.pow(s_) + c__ * x_.pow(t_)).pow(p_),
        with: [u__, e__, m_, a__, r_, b__, s_, c__, t_, p_, x_],
        optional: [u__, e__, m_, a__, r_, b__, s_, c__, t_, p_],
        x_free: [a__, b__, c__, e__, m_, r_, s_, t_],
        when: {
            freeq!([a__, b__, c__, e__, m_, r_, s_, t_], x_)
                && integerq!(p_)
                && (integerq!(&p_ * &r_) || gtq!(e__, 0))
                && posq!(&s_ - &r_)
                && posq!(&t_ - &r_)
        },
        rhs: {
            let transformed = u__
                * (&e__ * x_).pow(&m_ + &p_ * &r_)
                * (&a__
                    + &b__ * x_.pow(&s_ - &r_)
                    + &c__ * x_.pow(&t_ - &r_))
                    .pow(&p_);
            rubi_star(Atom::num(1) / e__.pow(&p_ * &r_), rubi_rhs_int(&transformed, x_))
        },
    ));
}

fn push_rules_rule_12(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, p_, q_, r_, s_, t_, u__, x_);
    rules.push(rubi_rule!(
        order: 12,
        source: "Int[u_.*(e_.*x_)^m_.*(a_.*x_^r_.+b_.*x_^s_.+c_.*x_^t_.+d_.*x_^q_.)^p_.,x_Symbol] :=
          1/e^(p*r) \\[Star] Int[u*(e*x)^(m+p*r)*(a+b*x^(s-r)+c*x^(t-r)+d*x^(q-r))^p,x] /;
        FreeQ[{a,b,c,d,e,m,r,s,t,q},x] && IntegerQ[p] && (IntegerQ[p*r] || GtQ[e,0]) && PosQ[s-r] && PosQ[t-r] && PosQ[q-r]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern: u__
            * (e__ * x_).pow(m_)
            * (a__ * x_.pow(r_)
                + b__ * x_.pow(s_)
                + c__ * x_.pow(t_)
                + d__ * x_.pow(q_))
            .pow(p_),
        with: [u__, e__, m_, a__, r_, b__, s_, c__, t_, d__, q_, p_, x_],
        optional: [u__, e__, m_, a__, r_, b__, s_, c__, t_, d__, q_, p_],
        x_free: [a__, b__, c__, d__, e__, m_, r_, s_, t_, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, r_, s_, t_, q_], x_)
                && integerq!(p_)
                && (integerq!(&p_ * &r_) || gtq!(e__, 0))
                && posq!(&s_ - &r_)
                && posq!(&t_ - &r_)
                && posq!(&q_ - &r_)
        },
        rhs: {
            let transformed = u__
                * (&e__ * x_).pow(&m_ + &p_ * &r_)
                * (&a__
                    + &b__ * x_.pow(&s_ - &r_)
                    + &c__ * x_.pow(&t_ - &r_)
                    + &d__ * x_.pow(&q_ - &r_))
                    .pow(&p_);
            rubi_star(Atom::num(1) / e__.pow(&p_ * &r_), rubi_rhs_int(&transformed, x_))
        },
    ));
}

fn push_rules_rule_13(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, mm_, n_, n2_, p_, u__, v__, x_);
    rules.push(rubi_rule!(
        order: 13,
        source: "Int[u_.*(v_.*(a_+b_.*x_^n_.)^mm_.*(c_+d_.*x_^n2_.)^m_.)^p_,x_Symbol] :=
          Int[u*(v*c^m/a^(2*m)*(a-b*x^n)^m)^p,x] /;
        FreeQ[{a,b,c,d,n,p},x] && EqQ[n2,2*n] && EqQ[b^2*c+a^2*d,0] && IntegersQ[m,mm] && EqQ[m+mm,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern: u__
            * (v__
                * (a__ + b__ * x_.pow(n_)).pow(mm_)
                * (c__ + d__ * x_.pow(n2_)).pow(m_))
            .pow(p_),
        with: [u__, v__, a__, b__, n_, mm_, c__, d__, n2_, m_, p_, x_],
        optional: [u__, v__, b__, n_, mm_, d__, n2_, m_],
        x_free: [a__, b__, c__, d__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, n_, p_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && eqq!(b__.pow(2) * &c__ + a__.pow(2) * &d__, 0)
                && integersq!([m_, mm_])
                && eqq!(&m_ + &mm_, 0)
        },
        rhs: {
            let transformed = u__
                * (v__
                    * c__.pow(&m_)
                    / a__.pow(Atom::num(2) * &m_)
                    * (&a__ - &b__ * x_.pow(&n_)).pow(&m_))
                .pow(&p_);
            rubi_rhs_int(&transformed, x_)
        },
    ));
}

fn push_rules_rule_24(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a_);
    rules.push(rubi_rule!(
        order: 24,
        source: "Int[a_,x_Symbol] :=
           a*x /;
        FreeQ[a,x]",
        desc: "Apply the direct antiderivative formula.",
        refs: ["CRC 1"],
        pattern: Atom::var(a_),
        with: [a_, x_],
        when: { freeq!(a_, x_) },
        rhs: { rubi_simp(&(a_ * x_), x_) },
    ));
}

fn push_rules_rule_25(rules: &mut Vec<RubiRule>) {
    rubi_symb!(fx__);
    rules.push(rubi_rule!(
        order: 25,
        source: "Int[-Fx_,x_Symbol] :=
          Identity[-1] \\[Star] Int[Fx,x]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern: Atom::num(-1) * fx__,
        with: [fx__, x_],
        when: { true },
        rhs: { rubi_star(-(Atom::num(1)), rubi_rhs_int(&fx__, x_)) },
    ));
}

fn push_rules_rule_26(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a_, fx__);
    rules.push(rubi_rule!(
        order: 26,
        source: "Int[Complex[0,a_]*Fx_,x_Symbol] :=
          Complex[Identity[0],a] \\[Star] Int[Fx,x] /;
        FreeQ[a,x] && EqQ[a^2,1]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern: Atom::i() * Atom::var(a_) * fx__,
        with: [a_, fx__, x_],
        x_free: [a_],
        when: { freeq!(a_, x_) && eqq!(a_.pow(2), 1) },
        rhs: { rubi_star(Atom::i() * a_, rubi_rhs_int(&fx__, x_)) },
    ));
}

fn push_rules_rule_27(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, fx__);
    rules.push(rubi_rule!(
        order: 27,
        source: "Int[a_*Fx_,x_Symbol] :=
          a \\[Star] Int[Fx,x] /;
        FreeQ[a,x] && Not[MatchQ[Fx, b_*Gx_ /; FreeQ[b,x]]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern: a__ * fx__,
        with: [a__, fx__, x_],
        x_free: [a__],
        when: { freeq!(a__, x_) && !has_x_free_factor(&fx__, x_) },
        rhs: { rubi_star(a__, rubi_rhs_int(&fx__, x_)) },
    ));
}

fn push_rules_rule_2009(rules: &mut Vec<RubiRule>) {
    rubi_symb!(u_);
    rules.push(rubi_rule!(
        order: 2009,
        source: "Int[u_,x_Symbol] :=
          IntSum[u,x] /;
        SumQ[u]",
        desc: "Integrate the terms of the sum separately.",
        refs: ["G&R 2.02.2, 2.111.1 CRC 2, 4, 23, 27"],
        pattern: Atom::var(u_),
        with: [u_, x_],
        when: { rubi_sum_q(&u_) },
        rhs: { rubi_simp(&rubi_int_sum(&u_, x_).rubi_rhs(), x_) },
    ));
}

fn push_rules_rule_2010(rules: &mut Vec<RubiRule>) {
    rubi_symb!(c__, m_, u__, x_);
    rules.push(rubi_rule!(
        order: 2010,
        source: "Int[(c_.*x_)^m_.*u_,x_Symbol] :=
          Int[ExpandIntegrand[(c*x)^m*u,x],x] /;
        FreeQ[{c,m},x] && SumQ[u] && Not[LinearQ[u,x]] && Not[MatchQ[u,a_+b_.*v_ /; FreeQ[{a,b},x] && InverseFunctionQ[v]]]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (c__ * x_).pow(m_) * u__,
        with: [c__, m_, u__, x_],
        optional: [c__, m_],
        when: {
            freeq!([c__, m_], x_)
                && rubi_sum_q(&u__)
                && !rubi_linear_q(&u__, x_)
                && !rubi_match_affine_inverse_function_q(&u__, x_)
        },
        rhs: {
            let expanded = rubi_expand_integrand(&((&c__ * x_).pow(&m_) * u__), x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_2011(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, u__, v__);
    rules.push(rubi_rule!(
        order: 2011,
        source: "Int[u_.*(a_+b_.*v_)^m_.*(c_+d_.*v_)^n_.,x_Symbol] :=
          (b/d)^m \\[Star] Int[u*(c+d*v)^(m+n),x] /;
        FreeQ[{a,b,c,d,n},x] && EqQ[b*c-a*d,0] && IntegerQ[m] && (Not[IntegerQ[n]] || SimplerQ[c+d*x,a+b*x])",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [u__, a__, b__, v__, m_, c__, d__, n_, x_],
        optional: [u__, b__, m_, d__, n_],
        x_free: [a__, b__, c__, d__, m_, n_],
        proportional_common: [(a__, b__, c__, d__)],
        when: {
            freeq!([a__, b__, c__, d__, n_], x_)
                && eqq!(&b__ * &c__ - &a__ * &d__, 0)
                && integerq!(m_)
                && (!integerq!(n_) || simplerq!(&c__ + &d__ * x_, &a__ + &b__ * x_))
        },
        rhs: { rubi_star((b__ / &d__).pow(&m_), rubi_rhs_int(&(u__ * (c__ + d__ * v__).pow(&m_ + &n_)), x_)) },
    ));
}

fn push_rules_rule_2012(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, u__, v__);
    rules.push(rubi_rule!(
        order: 2012,
        source: "Int[u_.*(a_+b_.*v_)^m_*(c_+d_.*v_)^n_,x_Symbol] :=
          (b/d)^m \\[Star] Int[u*(c+d*v)^(m+n),x] /;
        FreeQ[{a,b,c,d,m,n},x] && EqQ[b*c-a*d,0] && GtQ[b/d,0] && Not[IntegerQ[m] || IntegerQ[n]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [u__, a__, b__, v__, m_, c__, d__, n_, x_],
        optional: [u__, b__, d__],
        x_free: [a__, b__, c__, d__, m_, n_],
        when: {
            freeq!([a__, b__, c__, d__, m_, n_], x_)
                && eqq!(&b__ * &c__ - &a__ * &d__, 0)
                && gtq!(&b__ / &d__, 0)
                && !(integerq!(m_) || integerq!(n_))
        },
        rhs: { rubi_star((b__ / &d__).pow(&m_), rubi_rhs_int(&(u__ * (c__ + d__ * v__).pow(&m_ + &n_)), x_)) },
    ));
}

fn push_rules_rule_2013(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, u__, v__);
    rules.push(rubi_rule!(
        order: 2013,
        source: "Int[u_.*(a_+b_.*v_)^m_*(c_+d_.*v_)^n_,x_Symbol] :=
          (a+b*v)^m/(c+d*v)^m \\[Star] Int[u*(c+d*v)^(m+n),x] /;
        FreeQ[{a,b,c,d,m,n},x] && EqQ[b*c-a*d,0] && Not[IntegerQ[m] || IntegerQ[n] || GtQ[b/d,0]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [u__, a__, b__, v__, m_, c__, d__, n_, x_],
        optional: [u__, b__, d__],
        x_free: [a__, b__, c__, d__, m_, n_],
        when: {
            freeq!([a__, b__, c__, d__, m_, n_], x_)
                && eqq!(&b__ * &c__ - &a__ * &d__, 0)
                && !(integerq!(m_) || integerq!(n_) || gtq!(&b__ / &d__, 0))
        },
        rhs: {
            rubi_star((&a__ + &b__ * &v__).pow(&m_) / (&c__ + &d__ * &v__).pow(&m_), rubi_rhs_int(&(u__ * (c__ + d__ * v__).pow(&m_ + &n_)), x_))
        },
    ));
}

fn push_rules_rule_2014(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        capital_a__,
        capital_b__,
        capital_c__,
        a__,
        b__,
        m_,
        u__,
        v__
    );
    rules.push(rubi_rule!(
        order: 2014,
        source: "Int[u_.*(a_+b_.*v_)^m_*(A_.+B_.*v_+C_.*v_^2),x_Symbol] :=
          1/b^2 \\[Star] Int[u*(a+b*v)^(m+1)*Simp[b*B-a*C+b*C*v,x],x] /;
        FreeQ[{a,b,A,B,C},x] && EqQ[A*b^2-a*b*B+a^2*C,0] && LeQ[m,-1]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: u__ * (a__ + b__ * v__).pow(m_) * (capital_a__ + capital_b__ * v__ + capital_c__ * v__.pow(2)),
        with: [u__, a__, b__, v__, m_, capital_a__, capital_b__, capital_c__, x_],
        optional: [u__, b__, capital_a__, capital_b__, capital_c__],
        when: {
            freeq!([a__, b__, capital_a__, capital_b__, capital_c__], x_)
                && eqq!(&capital_a__ * b__.pow(2) - &a__ * &b__ * &capital_b__ + a__.pow(2) * &capital_c__, 0)
                && leq!(m_, -1)
        },
        rhs: {
            let simp = rubi_simp(&(&b__ * &capital_b__ - &a__ * &capital_c__ + &b__ * &capital_c__ * &v__), x_);
            rubi_star(Atom::num(1) / b__.pow(2), rubi_rhs_int(&(u__ * (a__ + &b__ * v__).pow(&m_ + 1) * simp), x_))
        },
    ));
}

fn push_rules_rule_2015(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, n_, p_, q_, u__, x_);
    rules.push(rubi_rule!(
        order: 2015,
        source: "Int[u_.*(a_+b_.*x_^n_.)^m_.*(c_+d_.*x_^q_.)^p_.,x_Symbol] :=
          (d/a)^p \\[Star] Int[u*(a+b*x^n)^(m+p)/x^(n*p),x] /;
        FreeQ[{a,b,c,d,m,n},x] && EqQ[q,-n] && IntegerQ[p] && EqQ[a*c-b*d,0] && Not[IntegerQ[m] && NegQ[n]]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: u__ * (a__ + b__ * x_.pow(n_)).pow(m_) * (c__ + d__ * x_.pow(q_)).pow(p_),
        with: [u__, a__, b__, n_, m_, c__, d__, q_, p_, x_],
        optional: [u__, b__, n_, d__, q_, p_, m_],
        when: {
            freeq!([a__, b__, c__, d__, m_, n_], x_)
                && eqq!(q_, -&n_)
                && integerq!(p_)
                && eqq!(&a__ * &c__ - &b__ * &d__, 0)
                && !(integerq!(m_) && negq!(n_))
        },
        rhs: {
            rubi_star((d__ / &a__).pow(&p_), rubi_rhs_int(&(u__ * (&a__ + &b__ * x_.pow(&n_)).pow(&m_ + &p_) / x_.pow(&n_ * &p_)), x_))
        },
    ));
}

fn push_rules_rule_2016(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, j_, m_, n_, p_, u__, x_);
    rules.push(rubi_rule!(
        order: 2016,
        source: "Int[u_.*(a_+b_.*x_^n_.)^m_.*(c_+d_.*x_^j_)^p_.,x_Symbol] :=
          (-b^2/d)^m \\[Star] Int[u*(a-b*x^n)^(-m),x] /;
        FreeQ[{a,b,c,d,m,n,p},x] && EqQ[j,2*n] && EqQ[p,-m] && EqQ[b^2*c+a^2*d,0] && GtQ[a,0] && LtQ[d,0] && GtQ[b^2,0]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: u__ * (a__ + b__ * x_.pow(n_)).pow(m_) * (c__ + d__ * x_.pow(j_)).pow(p_),
        with: [u__, a__, b__, n_, m_, c__, d__, j_, p_, x_],
        optional: [u__, b__, n_, d__, m_, p_],
        when: {
            freeq!([a__, b__, c__, d__, m_, n_, p_], x_)
                && eqq!(j_, Atom::num(2) * &n_)
                && eqq!(p_, -&m_)
                && eqq!(b__.pow(2) * &c__ + a__.pow(2) * &d__, 0)
                && gtq!(a__, 0)
                && ltq!(d__, 0)
                && gtq!(b__.pow(2), 0)
        },
        rhs: {
            let recursive = rubi_rhs_int(
                &(u__ * (a__ - &b__ * x_.pow(&n_)).pow(-&m_)),
                x_,
            );
            rubi_star((-b__.pow(2) / d__).pow(&m_), recursive)
        },
    ));
}

fn push_rules_rule_1380(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, n_, n2_, p_, u__, x_);
    rules.push(rubi_rule!(
        order: 1380,
        source: "Int[u_*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_.,x_Symbol] :=
          1/c^p \\[Star] Int[u*(b/2+c*x^n)^(2*p),x] /;
        FreeQ[{a,b,c,n,p},x] && EqQ[n2,2*n] && EqQ[b^2-4*a*c,0] && IntegerQ[p]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [u__, a__, b__, n_, c__, n2_, p_, x_],
        optional: [b__, c__, n2_, p_],
        x_free: [a__, b__, c__, n_, p_],
        scaled: [(n2_, 2, n_)],
        when: {
            freeq!([a__, b__, c__, n_, p_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && eqq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && integerq!(p_)
        },
        rhs: {
            let recursive_integrand =
                &u__ * (&b__ / Atom::num(2) + &c__ * x_.pow(&n_)).pow(Atom::num(2) * &p_);
            rubi_star(Atom::num(1) / c__.pow(&p_), rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1384(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, n_, n2_, p_, u__, x_);
    rules.push(rubi_rule!(
        order: 1384,
        source: "Int[u_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
          (a+b*x^n+c*x^(2*n))^FracPart[p]/(c^IntPart[p]*(b/2+c*x^n)^(2*FracPart[p])) \\[Star] Int[u*(b/2+c*x^n)^(2*p),x] /;
        FreeQ[{a,b,c,n,p},x] && EqQ[n2,2*n] && EqQ[b^2-4*a*c,0] && IntegerQ[p-1/2] && NeQ[u,x^(n-1)] && NeQ[u,x^(2*n-1)] && Not[EqQ[p,1/2] && EqQ[u,x^(-2*n-1)]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [u__, a__, b__, c__, n_, n2_, p_, x_],
        optional: [u__, b__, c__, n2_],
        x_free: [a__, b__, c__, n_, p_],
        when: {
            freeq!([a__, b__, c__, n_, p_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && eqq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && integerq!(&p_ - Atom::num(1) / Atom::num(2))
                && neq!(u__, x_.pow(&n_ - Atom::num(1)))
                && neq!(u__, x_.pow(Atom::num(2) * &n_ - Atom::num(1)))
                && !(eqq!(p_, Atom::num(1) / Atom::num(2))
                    && eqq!(u__, x_.pow(-Atom::num(2) * &n_ - Atom::num(1))))
        },
        rhs: {
            let trinomial =
                &a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_);
            let reduced = &b__ / Atom::num(2) + &c__ * x_.pow(&n_);
            let frac_p = rubi_frac_part(&p_);
            let factor = trinomial.pow(&frac_p)
                / (c__.pow(rubi_int_part(&p_))
                    * reduced.pow(Atom::num(2) * &frac_p));
            let recursive_integrand = &u__ * reduced.pow(Atom::num(2) * &p_);
            rubi_star(factor, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1385(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, n_, n2_, p_, u__, x_);
    rules.push(rubi_rule!(
        order: 1385,
        source: "Int[u_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
          a^IntPart[p]*(a+b*x^n+c*x^(2*n))^FracPart[p]/(1+2*c*x^n/b)^(2*FracPart[p]) \\[Star] Int[u*(1+2*c*x^n/b)^(2*p),x] /;
        FreeQ[{a,b,c,n,p},x] && EqQ[n2,2*n] && EqQ[b^2-4*a*c,0] && Not[IntegerQ[2*p]] && NeQ[u,x^(n-1)] && NeQ[u,x^(2*n-1)]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [u__, a__, b__, c__, n_, n2_, p_, x_],
        optional: [u__, b__, c__, n2_],
        x_free: [a__, b__, c__, n_, p_],
        when: {
            freeq!([a__, b__, c__, n_, p_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && eqq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && !integerq!(Atom::num(2) * &p_)
                && neq!(u__, x_.pow(&n_ - Atom::num(1)))
                && neq!(u__, x_.pow(Atom::num(2) * &n_ - Atom::num(1)))
        },
        rhs: {
            let trinomial =
                &a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_);
            let normalized =
                Atom::num(1) + Atom::num(2) * &c__ * x_.pow(&n_) / &b__;
            let frac_p = rubi_frac_part(&p_);
            let factor = a__.pow(rubi_int_part(&p_)) * trinomial.pow(&frac_p)
                / normalized.pow(Atom::num(2) * &frac_p);
            let recursive_integrand = &u__ * normalized.pow(Atom::num(2) * &p_);
            rubi_star(factor, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

// Generated shared pattern builders.

#[inline(never)]
fn rubi_shared_pattern_0(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let u__ = symbols.u__;
    let v__ = symbols.v__;
    u__ * (a__ + b__ * v__).pow(m_) * (c__ + d__ * v__).pow(n_)
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let u__ = symbols.u__;
    let x_ = symbols.x_;
    u__ * (a__ + b__ * x_.pow(n_)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_2(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let j_ = symbols.j_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let u__ = symbols.u__;
    let x_ = symbols.x_;
    u__ * (a__ + b__ * x_.pow(n_) + c__ * x_.pow(j_)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_3(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let n2_ = symbols.n2_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let u__ = symbols.u__;
    let x_ = symbols.x_;
    u__ * (a__ + b__ * x_.pow(n_) + c__ * x_.pow(n2_)).pow(p_)
}
