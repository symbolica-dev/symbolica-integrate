use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_2491(rules);
    push_rules_rule_2492(rules);
    push_rules_rule_2493(rules);
    push_rules_rule_2494(rules);
    push_rules_rule_2495(rules);
    push_rules_rule_2496(rules);
    push_rules_rule_2497(rules);
    push_rules_rule_2498(rules);
    push_rules_rule_2499(rules);
    push_rules_rule_2504(rules);
    push_rules_rule_2517(rules);
    push_rules_rule_2518(rules);
    push_rules_rule_2482(rules);
    push_rules_rule_2483(rules);
    push_rules_rule_2484(rules);
    push_rules_rule_2485(rules);
    push_rules_rule_2486(rules);
    push_rules_rule_2505(rules);
    push_rules_rule_2506(rules);
    push_rules_rule_2507(rules);
    push_rules_rule_2508(rules);
    push_rules_rule_2500(rules);
    push_rules_rule_2501(rules);
    push_rules_rule_2502(rules);
    push_rules_rule_2503(rules);
    push_rules_rule_2519(rules);
    push_rules_rule_2520(rules);
    push_rules_rule_2521(rules);
    push_rules_rule_2522(rules);
    push_rules_rule_2466(rules);
    push_rules_rule_2523(rules);
    push_rules_rule_2524(rules);
    push_rules_rule_2525(rules);
    push_rules_rule_2526(rules);
    push_rules_rule_2527(rules);
}

fn push_rules_rule_2491(rules: &mut Vec<RubiRule>) {
    rubi_symb!(p_, px_, u__);
    rules.push(rubi_rule!(
        order: 2491,
        source: "Int[u_.*Px_^p_,x_Symbol] :=
          With[{b=Coeff[Px,x,1],c=Coeff[Px,x,2],d=Coeff[Px,x,3],e=Coeff[Px,x,4]},
          Px^FracPart[p]/(x^FracPart[p]*(b+c*x+d*x^2+e*x^3)^FracPart[p]) \\[Star] Int[u*x^p*(b+c*x+d*x^2+e*x^3)^p,x]] /;
        FreeQ[p,x] && PolyQ[Px,x,4] && EqQ[Coeff[Px,x,0],0] && Not[IntegerQ[p]]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: u__ * px_.pow(p_),
        with: [u__, px_, p_, x_],
        optional: [u__],
        x_free: [p_],
        when: {
            freeq!(p_, x_)
                && rubi_poly_q_degree(&px_, x_, 4)
                && rubi_coeff(&px_, x_, 0).is_some_and(|coefficient| eqq!(coefficient, 0))
                && !integerq!(p_)
        },
        rhs: {
            let b = rubi_coeff(&px_, x_, 1).unwrap();
            let c = rubi_coeff(&px_, x_, 2).unwrap();
            let d = rubi_coeff(&px_, x_, 3).unwrap();
            let e = rubi_coeff(&px_, x_, 4).unwrap();
            let frac_p = rubi_frac_part(&p_);
            let cubic = &b + &c * x_ + &d * x_.pow(2) + &e * x_.pow(3);
            let multiplier = px_.pow(&frac_p) / (x_.pow(&frac_p) * cubic.pow(&frac_p));
            let recursive = rubi_rhs_int(&(u__ * x_.pow(&p_) * cubic.pow(&p_)), x_);
            rubi_star(multiplier, recursive)
        },
    ));
}

fn push_rules_rule_2492(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, p_, px__, x_);
    rules.push(rubi_rule!(
        order: 2492,
        source: "Int[Px_.*(a_+b_.*x_+c_.*x_^2+d_.*x_^3+e_.*x_^4)^p_,x_Symbol] :=
          e^p \\[Star] Int[ExpandIntegrand[Px*(b/d+(d+Sqrt[e*(b^2-4*a*c)/a+8*a*d*e/b])/(2*e)*x+x^2)^p*(b/d+(d-Sqrt[e*(b^2-4*a*c)/a+8*a*d*e/b])/(2*e)*x+x^2)^p,x],x] /;
        FreeQ[{a,b,c,d,e},x] && PolyQ[Px,x] && ILtQ[p,0] && EqQ[a*d^2-b^2*e,0]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [px__, a__, b__, c__, d__, e__, p_, x_],
        optional: [px__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && rubi_poly_q(&px__, x_)
                && iltq!(p_, 0)
                && eqq!(&a__ * d__.pow(2) - b__.pow(2) * &e__, 0)
        },
        rhs: {
            let root = (&e__ * (b__.pow(2) - Atom::num(4) * &a__ * &c__) / &a__
                + Atom::num(8) * &a__ * &d__ * &e__ / &b__)
                .sqrt();
            let first = &b__ / &d__ + (&d__ + &root) * x_ / (Atom::num(2) * &e__) + x_.pow(2);
            let second = &b__ / &d__ + (&d__ - root) * x_ / (Atom::num(2) * &e__) + x_.pow(2);
            let expanded = rubi_expand_integrand_or_self(
                &(px__ * first.pow(&p_) * second.pow(&p_)),
                x_,
            );
            rubi_star(e__.pow(&p_), rubi_rhs_int(&expanded, x_))
        },
    ));
}

fn push_rules_rule_2493(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, e__, p_, px__, x_);
    rules.push(rubi_rule!(
        order: 2493,
        source: "Int[Px_.*(a_+b_.*x_+d_.*x_^3+e_.*x_^4)^p_,x_Symbol] :=
          e^p \\[Star] Int[ExpandIntegrand[Px*(b/d+(d+Sqrt[d^2+8*a*d*e/b])/(2*e)*x+x^2)^p*(b/d+(d-Sqrt[d^2+8*a*d*e/b])/(2*e)*x+x^2)^p,x],x] /;
        FreeQ[{a,b,d,e},x] && PolyQ[Px,x] && ILtQ[p,0] && EqQ[a*d^2-b^2*e,0]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [px__, a__, b__, d__, e__, p_, x_],
        optional: [px__, b__, d__, e__],
        when: {
            freeq!([a__, b__, d__, e__], x_)
                && rubi_poly_q(&px__, x_)
                && iltq!(p_, 0)
                && eqq!(&a__ * d__.pow(2) - b__.pow(2) * &e__, 0)
        },
        rhs: {
            let root = (d__.pow(2) + Atom::num(8) * &a__ * &d__ * &e__ / &b__).sqrt();
            let first = &b__ / &d__ + (&d__ + &root) * x_ / (Atom::num(2) * &e__) + x_.pow(2);
            let second = &b__ / &d__ + (&d__ - root) * x_ / (Atom::num(2) * &e__) + x_.pow(2);
            let expanded = rubi_expand_integrand_or_self(
                &(px__ * first.pow(&p_) * second.pow(&p_)),
                x_,
            );
            rubi_star(e__.pow(&p_), rubi_rhs_int(&expanded, x_))
        },
    ));
}

fn push_rules_rule_2494(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, p_, px__, x_);
    rules.push(rubi_rule!(
        order: 2494,
        source: "Int[Px_.*(a_+b_.*x_+c_.*x_^2+d_.*x_^3+e_.*x_^4)^p_,x_Symbol] :=
          With[{S=Root[a*d^2-b^2*e+(b*d^2-4*b*c*e+8*a*d*e)*x+(c*d^2-4*c^2*e+2*b*d*e+16*a*e^2)*x^2+(d^3-4*c*d*e+8*b*e^2)*x^3,3]},
          Subst[Int[ReplaceAll[Px,x->x+S]*ExpandToSum[a+b*(x+S)+c*(x+S)^2+d*(x+S)^3+e*(x+S)^4,x]^p,x],x,x-S] /;
         RationalQ[S]] /;
        FreeQ[{a,b,c,d,e},x] && PolyQ[Px,x] && ILtQ[p,0] && RationalQ[a,b,c,d,e] && NeQ[a*d^2-b^2*e,0]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [px__, a__, b__, c__, d__, e__, p_, x_],
        optional: [px__, b__, c__, d__, e__],
        x_free: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && rubi_poly_q(&px__, x_)
                && iltq!(p_, 0)
                && rationalq!([a__, b__, c__, d__, e__])
                && neq!(&a__ * d__.pow(2) - b__.pow(2) * &e__, 0)
                && {
                    let root_polynomial = &a__ * d__.pow(2) - b__.pow(2) * &e__
                        + (&b__ * d__.pow(2) - Atom::num(4) * &b__ * &c__ * &e__
                            + Atom::num(8) * &a__ * &d__ * &e__)
                            * x_
                        + (&c__ * d__.pow(2) - Atom::num(4) * c__.pow(2) * &e__
                            + Atom::num(2) * &b__ * &d__ * &e__
                            + Atom::num(16) * &a__ * e__.pow(2))
                            * x_.pow(2)
                        + (d__.pow(3) - Atom::num(4) * &c__ * &d__ * &e__
                            + Atom::num(8) * &b__ * e__.pow(2))
                            * x_.pow(3);
                    rubi_rational_root(&root_polynomial, x_, 3).is_some()
                }
        },
        rhs: {
            let root_polynomial = &a__ * d__.pow(2) - b__.pow(2) * &e__
                + (&b__ * d__.pow(2) - Atom::num(4) * &b__ * &c__ * &e__
                    + Atom::num(8) * &a__ * &d__ * &e__)
                    * x_
                + (&c__ * d__.pow(2) - Atom::num(4) * c__.pow(2) * &e__
                    + Atom::num(2) * &b__ * &d__ * &e__
                    + Atom::num(16) * &a__ * e__.pow(2))
                    * x_.pow(2)
                + (d__.pow(3) - Atom::num(4) * &c__ * &d__ * &e__
                    + Atom::num(8) * &b__ * e__.pow(2))
                    * x_.pow(3);
            let s = rubi_rational_root(&root_polynomial, x_, 3).unwrap();
            let shifted_x = x_ + &s;
            let replaced_px = rubi_replace_all(&px__, x_, &shifted_x);
            let shifted_quartic = rubi_expand_to_sum(
                &(&a__
                    + &b__ * &shifted_x
                    + &c__ * shifted_x.pow(2)
                    + &d__ * shifted_x.pow(3)
                    + &e__ * shifted_x.pow(4)),
                x_,
            );
            let primitive = rubi_rhs_int(&(replaced_px * shifted_quartic.pow(&p_)), x_);
            rubi_subst(&primitive, x_, x_ - s)
        },
    ));
}

fn push_rules_rule_2495(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, e__, p_, px__, x_);
    rules.push(rubi_rule!(
        order: 2495,
        source: "Int[Px_.*(a_+b_.*x_+d_.*x_^3+e_.*x_^4)^p_,x_Symbol] :=
          With[{S=Root[a*d^2-b^2*e+(b*d^2+8*a*d*e)*x+(2*b*d*e+16*a*e^2)*x^2+(d^3+8*b*e^2)*x^3,3]},
          Subst[Int[ReplaceAll[Px,x->x+S]*ExpandToSum[a+b*(x+S)+d*(x+S)^3+e*(x+S)^4,x]^p,x],x,x-S] /;
         RationalQ[S]] /;
        FreeQ[{a,b,d,e},x] && PolyQ[Px,x] && ILtQ[p,0] && RationalQ[a,b,d,e] && NeQ[a*d^2-b^2*e,0]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [px__, a__, b__, d__, e__, p_, x_],
        optional: [px__, b__, d__, e__],
        x_free: [a__, b__, d__, e__],
        when: {
            freeq!([a__, b__, d__, e__], x_)
                && rubi_poly_q(&px__, x_)
                && iltq!(p_, 0)
                && rationalq!([a__, b__, d__, e__])
                && neq!(&a__ * d__.pow(2) - b__.pow(2) * &e__, 0)
                && {
                    let root_polynomial = &a__ * d__.pow(2) - b__.pow(2) * &e__
                        + (&b__ * d__.pow(2) + Atom::num(8) * &a__ * &d__ * &e__) * x_
                        + (Atom::num(2) * &b__ * &d__ * &e__
                            + Atom::num(16) * &a__ * e__.pow(2))
                            * x_.pow(2)
                        + (d__.pow(3) + Atom::num(8) * &b__ * e__.pow(2)) * x_.pow(3);
                    rubi_rational_root(&root_polynomial, x_, 3).is_some()
                }
        },
        rhs: {
            let root_polynomial = &a__ * d__.pow(2) - b__.pow(2) * &e__
                + (&b__ * d__.pow(2) + Atom::num(8) * &a__ * &d__ * &e__) * x_
                + (Atom::num(2) * &b__ * &d__ * &e__
                    + Atom::num(16) * &a__ * e__.pow(2))
                    * x_.pow(2)
                + (d__.pow(3) + Atom::num(8) * &b__ * e__.pow(2)) * x_.pow(3);
            let s = rubi_rational_root(&root_polynomial, x_, 3).unwrap();
            let shifted_x = x_ + &s;
            let replaced_px = rubi_replace_all(&px__, x_, &shifted_x);
            let shifted_quartic = rubi_expand_to_sum(
                &(&a__
                    + &b__ * &shifted_x
                    + &d__ * shifted_x.pow(3)
                    + &e__ * shifted_x.pow(4)),
                x_,
            );
            let primitive = rubi_rhs_int(&(replaced_px * shifted_quartic.pow(&p_)), x_);
            rubi_subst(&primitive, x_, x_ - s)
        },
    ));
}

fn push_rules_rule_2496(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, px__, x_);
    rules.push(rubi_rule!(
        order: 2496,
        source: "Int[x_^m_.*Px_.*(a_+b_.*x_+c_.*x_^2+d_.*x_^3+e_.*x_^4)^p_,x_Symbol] :=
          e^p \\[Star] Int[ExpandIntegrand[x^m*Px*(b/d+(d+Sqrt[e*(b^2-4*a*c)/a+8*a*d*e/b])/(2*e)*x+x^2)^p*(b/d+(d-Sqrt[e*(b^2-4*a*c)/a+8*a*d*e/b])/(2*e)*x+x^2)^p,x],x] /;
        FreeQ[{a,b,c,d,e,m},x] && PolyQ[Px,x] && ILtQ[p,0] && EqQ[a*d^2-b^2*e,0]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [m_, px__, a__, b__, c__, d__, e__, p_, x_],
        optional: [m_, px__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_], x_)
                && rubi_poly_q(&px__, x_)
                && iltq!(p_, 0)
                && eqq!(&a__ * d__.pow(2) - b__.pow(2) * &e__, 0)
        },
        rhs: {
            let root = (&e__ * (b__.pow(2) - Atom::num(4) * &a__ * &c__) / &a__
                + Atom::num(8) * &a__ * &d__ * &e__ / &b__)
                .sqrt();
            let first = &b__ / &d__ + (&d__ + &root) * x_ / (Atom::num(2) * &e__) + x_.pow(2);
            let second = &b__ / &d__ + (&d__ - root) * x_ / (Atom::num(2) * &e__) + x_.pow(2);
            let expanded = rubi_expand_integrand_or_self(
                &(x_.pow(&m_) * px__ * first.pow(&p_) * second.pow(&p_)),
                x_,
            );
            rubi_star(e__.pow(&p_), rubi_rhs_int(&expanded, x_))
        },
    ));
}

fn push_rules_rule_2497(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, d__, e__, m_, p_, px__, x_);
    rules.push(rubi_rule!(
        order: 2497,
        source: "Int[x_^m_.*Px_.*(a_+b_.*x_+d_.*x_^3+e_.*x_^4)^p_,x_Symbol] :=
          e^p \\[Star] Int[ExpandIntegrand[x^m*Px*(b/d+(d+Sqrt[d^2+8*a*d*e/b])/(2*e)*x+x^2)^p*(b/d+(d-Sqrt[d^2+8*a*d*e/b])/(2*e)*x+x^2)^p,x],x] /;
        FreeQ[{a,b,d,e,m},x] && PolyQ[Px,x] && ILtQ[p,0] && EqQ[a*d^2-b^2*e,0]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern: x_.pow(m_) * px__ * (a__ + b__ * x_ + d__ * x_.pow(3) + e__ * x_.pow(4)).pow(p_),
        with: [m_, px__, a__, b__, d__, e__, p_, x_],
        optional: [m_, px__, b__, d__, e__],
        when: {
            freeq!([a__, b__, d__, e__, m_], x_)
                && rubi_poly_q(&px__, x_)
                && iltq!(p_, 0)
                && eqq!(&a__ * d__.pow(2) - b__.pow(2) * &e__, 0)
        },
        rhs: {
            let root = (d__.pow(2) + Atom::num(8) * &a__ * &d__ * &e__ / &b__).sqrt();
            let first = &b__ / &d__ + (&d__ + &root) * x_ / (Atom::num(2) * &e__) + x_.pow(2);
            let second = &b__ / &d__ + (&d__ - root) * x_ / (Atom::num(2) * &e__) + x_.pow(2);
            let expanded = rubi_expand_integrand_or_self(
                &(x_.pow(&m_) * px__ * first.pow(&p_) * second.pow(&p_)),
                x_,
            );
            rubi_star(e__.pow(&p_), rubi_rhs_int(&expanded, x_))
        },
    ));
}

fn push_rules_rule_2498(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, p_, px__, x_);
    rules.push(rubi_rule!(
        order: 2498,
        source: "Int[Px_.*(a_+b_.*x_+c_.*x_^2+d_.*x_^3+e_.*x_^4)^p_,x_Symbol] :=
          1/a^(3*p) \\[Star] Int[ExpandIntegrand[Px*(a^5-b^5*x^5)^p/(a-b*x)^p,x],x] /;
        FreeQ[{a,b,c,d,e},x] && PolyQ[Px,x] && ILtQ[p,0] && NeQ[a,0] && EqQ[c,b^2/a] && EqQ[d,b^3/a^2] && EqQ[e,b^4/a^3]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [px__, a__, b__, c__, d__, e__, p_, x_],
        optional: [px__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && rubi_poly_q(&px__, x_)
                && iltq!(p_, 0)
                && neq!(a__, 0)
                && eqq!(c__, b__.pow(2) / &a__)
                && eqq!(d__, b__.pow(3) / a__.pow(2))
                && eqq!(e__, b__.pow(4) / a__.pow(3))
        },
        rhs: {
            let expanded = rubi_expand_integrand_or_self(
                &(px__ * (a__.pow(5) - b__.pow(5) * x_.pow(5)).pow(&p_)
                    / (&a__ - &b__ * x_).pow(&p_)),
                x_,
            );
            rubi_star(Atom::num(1) / a__.pow(Atom::num(3) * &p_), rubi_rhs_int(&expanded, x_))
        },
    ));
}

fn push_rules_rule_2499(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, px__, x_);
    rules.push(rubi_rule!(
        order: 2499,
        source: "Int[x_^m_.*Px_.*(a_+b_.*x_+c_.*x_^2+d_.*x_^3+e_.*x_^4)^p_,x_Symbol] :=
          1/a^(3*p) \\[Star] Int[ExpandIntegrand[x^m*Px*(a^5-b^5*x^5)^p/(a-b*x)^p,x],x] /;
        FreeQ[{a,b,c,d,e,m},x] && PolyQ[Px,x] && ILtQ[p,0] && NeQ[a,0] && EqQ[c,b^2/a] && EqQ[d,b^3/a^2] && EqQ[e,b^4/a^3]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [m_, px__, a__, b__, c__, d__, e__, p_, x_],
        optional: [m_, px__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_], x_)
                && rubi_poly_q(&px__, x_)
                && iltq!(p_, 0)
                && neq!(a__, 0)
                && eqq!(c__, b__.pow(2) / &a__)
                && eqq!(d__, b__.pow(3) / a__.pow(2))
                && eqq!(e__, b__.pow(4) / a__.pow(3))
        },
        rhs: {
            let expanded = rubi_expand_integrand_or_self(
                &(x_.pow(&m_)
                    * px__
                    * (a__.pow(5) - b__.pow(5) * x_.pow(5)).pow(&p_)
                    / (&a__ - &b__ * x_).pow(&p_)),
                x_,
            );
            rubi_star(Atom::num(1) / a__.pow(Atom::num(3) * &p_), rubi_rhs_int(&expanded, x_))
        },
    ));
}

fn push_rules_rule_2504(rules: &mut Vec<RubiRule>) {
    rubi_symb!(p_, p4__);
    rules.push(rubi_rule!(
        order: 2504,
        source: "Int[P4_^p_,x_Symbol] :=
          With[{a=Coeff[P4,x,0],b=Coeff[P4,x,1],c=Coeff[P4,x,2],d=Coeff[P4,x,3],e=Coeff[P4,x,4]},
          -16*a^2 \\[Star] Subst[
            Int[1/(b-4*a*x)^2*(a*(-3*b^4+16*a*b^2*c-64*a^2*b*d+256*a^3*e-32*a^2*(3*b^2-8*a*c)*x^2+256*a^4*x^4)/(b-4*a*x)^4)^p,x],
            x,b/(4*a)+1/x] /;
         NeQ[a,0] && NeQ[b,0] && EqQ[b^3-4*a*b*c+8*a^2*d,0]] /;
        FreeQ[p,x] && PolyQ[P4,x,4] && IntegerQ[2*p] && Not[IGtQ[p,0]]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern: p4__.pow(p_),
        with: [p4__, p_, x_],
        x_free: [p_],
        when: {
            freeq!(p_, x_)
                && rubi_poly_q_degree(&p4__, x_, 4)
                && integerq!(Atom::num(2) * &p_)
                && !igtq!(p_, 0)
                && {
                    let a = rubi_coeff(&p4__, x_, 0).unwrap();
                    let b = rubi_coeff(&p4__, x_, 1).unwrap();
                    let c = rubi_coeff(&p4__, x_, 2).unwrap();
                    let d = rubi_coeff(&p4__, x_, 3).unwrap();
                    neq!(a, 0)
                        && neq!(b, 0)
                        && eqq!(
                            b.pow(3) - Atom::num(4) * &a * &b * &c
                                + Atom::num(8) * a.pow(2) * &d,
                            0
                        )
                }
        },
        rhs: {
            let a = rubi_coeff(&p4__, x_, 0).unwrap();
            let b = rubi_coeff(&p4__, x_, 1).unwrap();
            let c = rubi_coeff(&p4__, x_, 2).unwrap();
            let d = rubi_coeff(&p4__, x_, 3).unwrap();
            let e = rubi_coeff(&p4__, x_, 4).unwrap();
            let denominator = &b - Atom::num(4) * &a * x_;
            let quartic = &a
                * (-Atom::num(3) * b.pow(4)
                    + Atom::num(16) * &a * b.pow(2) * &c
                    - Atom::num(64) * a.pow(2) * &b * &d
                    + Atom::num(256) * a.pow(3) * &e
                    - Atom::num(32)
                        * a.pow(2)
                        * (Atom::num(3) * b.pow(2) - Atom::num(8) * &a * &c)
                        * x_.pow(2)
                    + Atom::num(256) * a.pow(4) * x_.pow(4))
                / denominator.pow(4);
            let primitive = rubi_rhs_int(&(denominator.pow(-2) * quartic.pow(&p_)), x_);
            let substituted = rubi_subst(
                &primitive,
                x_,
                &b / (Atom::num(4) * &a) + x_.pow(-1),
            );
            rubi_star(-Atom::num(16) * a.pow(2), substituted)
        },
    ));
}

fn push_rules_rule_2517(rules: &mut Vec<RubiRule>) {
    rubi_symb!(d__, e__, v_, x_);
    rules.push(rubi_rule!(
        order: 2517,
        source: "Int[Sqrt[v_]/(d_+e_.*x_^4),x_Symbol] :=
          With[{a=Coeff[v,x,0],b=Coeff[v,x,2],c=Coeff[v,x,4]},
          a/d \\[Star] Subst[Int[1/(1-2*b*x^2+(b^2-4*a*c)*x^4),x],x,x/Sqrt[v]] /;
         EqQ[c*d+a*e,0] && PosQ[a*c]] /;
        FreeQ[{d,e},x] && PolyQ[v,x^2,2]",
        desc: "Integration by substitution",
        refs: [],
        pattern: v_.pow(Atom::num(1) / Atom::num(2)) / (d__ + e__ * x_.pow(4)),
        with: [v_, d__, e__, x_],
        optional: [e__],
        when: {
            freeq!([d__, e__], x_)
                && rubi_poly_q_power_degree(&v_, x_, &Atom::num(2), 2)
                && {
                    let a = rubi_coeff(&v_, x_, 0).unwrap();
                    let c = rubi_coeff(&v_, x_, 4).unwrap();
                    eqq!(&c * &d__ + &a * &e__, 0) && posq!(&a * &c)
                }
        },
        rhs: {
            let a = rubi_coeff(&v_, x_, 0).unwrap();
            let b = rubi_coeff(&v_, x_, 2).unwrap();
            let c = rubi_coeff(&v_, x_, 4).unwrap();

            let integrand = Atom::num(1)
                / (Atom::num(1) - Atom::num(2) * &b * x_.pow(2)
                    + (b.pow(2) - Atom::num(4) * &a * &c) * x_.pow(4));
            let transformed = rubi_rhs_int(&integrand, x_);

            rubi_star(a, rubi_subst(&transformed, x_, x_ / v_.sqrt()) / &d__)
        },
    ));
}

fn push_rules_rule_2518(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 2518,
        source: "Int[Sqrt[a_+b_.*x_^2+c_.*x_^4]/(d_+e_.*x_^4),x_Symbol] :=
          With[{q=Sqrt[b^2-4*a*c]},
          -a*Sqrt[b+q]/(2*Sqrt[2]*Rt[-a*c,2]*d)*ArcTan[Sqrt[b+q]*x*(b-q+2*c*x^2)/(2*Sqrt[2]*Rt[-a*c,2]*Sqrt[a+b*x^2+c*x^4])] +
          a*Sqrt[-b+q]/(2*Sqrt[2]*Rt[-a*c,2]*d)*ArcTanh[Sqrt[-b+q]*x*(b+q+2*c*x^2)/(2*Sqrt[2]*Rt[-a*c,2]*Sqrt[a+b*x^2+c*x^4])]] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[c*d+a*e,0] && NegQ[a*c]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: (a__ + b__ * x_.pow(2) + c__ * x_.pow(4)).pow(Atom::num(1) / Atom::num(2))
            / (d__ + e__ * x_.pow(4)),
        with: [a__, b__, c__, d__, e__, x_],
        optional: [b__, c__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(&c__ * &d__ + &a__ * &e__, 0)
                && negq!(&a__ * &c__)
        },
        rhs: {
            let rt = rubi_rt(&(-&a__ * &c__), 2);
            let q = (b__.pow(2) - Atom::num(4) * &a__ * &c__).sqrt();
            let sqrt_two = Atom::num(2).sqrt();
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let quartic_sqrt = quartic.sqrt();
            let common_denominator = Atom::num(2) * &sqrt_two * &rt * &d__;
            let first_sqrt = (&b__ + &q).sqrt();
            let second_sqrt = (-&b__ + &q).sqrt();
            let first_argument = &first_sqrt
                * x_
                * (&b__ - &q + Atom::num(2) * &c__ * x_.pow(2))
                / (Atom::num(2) * &sqrt_two * &rt * &quartic_sqrt);
            let second_argument = &second_sqrt
                * x_
                * (&b__ + &q + Atom::num(2) * &c__ * x_.pow(2))
                / (Atom::num(2) * sqrt_two * rt * quartic_sqrt);

            rubi_simp(
                    &(-&a__ * first_sqrt * first_argument.atan() / &common_denominator),
                    x_,
                ) + rubi_simp(
                    &(a__ * second_sqrt * second_argument.atanh() / common_denominator),
                    x_,
                )
        },
    ));
}

fn push_rules_rule_2482(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, e__, f__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 2482,
        source: "Int[(e_.+f_.*x_)^m_.*(a_+b_.*x_+d_.*x_^3)^p_.,x_Symbol] :=
          1/(3^(3*p)*a^(2*p)) \\[Star] Int[(e+f*x)^m*(3*a-b*x)^p*(3*a+2*b*x)^(2*p),x] /;
        FreeQ[{a,b,d,e,f,m},x] && EqQ[4*b^3+27*a^2*d,0] && IntegerQ[p]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [e__, f__, m_, a__, b__, d__, p_, x_],
        optional: [e__, f__, m_, b__, d__, p_],
        when: {
            freeq!([a__, b__, d__, e__, f__, m_], x_)
                && eqq!(
                    Atom::num(4) * b__.pow(3) + Atom::num(27) * a__.pow(2) * &d__,
                    0
                )
                && integerq!(p_)
        },
        rhs: {
            let integrand = (&e__ + &f__ * x_).pow(&m_)
                * (Atom::num(3) * &a__ - &b__ * x_).pow(&p_)
                * (Atom::num(3) * &a__ + Atom::num(2) * &b__ * x_)
                    .pow(Atom::num(2) * &p_);
            let recursive = rubi_rhs_int(&integrand, x_);

            rubi_star(Atom::num(1) / (Atom::num(3).pow(Atom::num(3) * &p_)
                        * a__.pow(Atom::num(2) * &p_)), recursive)
        },
    ));
}

fn push_rules_rule_2483(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, e__, f__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 2483,
        source: "Int[(e_.+f_.*x_)^m_.*(a_+b_.*x_+d_.*x_^3)^p_,x_Symbol] :=
          (a+b*x+d*x^3)^p/((3*a-b*x)^p*(3*a+2*b*x)^(2*p)) \\[Star] Int[(e+f*x)^m*(3*a-b*x)^p*(3*a+2*b*x)^(2*p),x] /;
        FreeQ[{a,b,d,e,f,m,p},x] && EqQ[4*b^3+27*a^2*d,0] && Not[IntegerQ[p]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [e__, f__, m_, a__, b__, d__, p_, x_],
        optional: [e__, f__, m_, b__, d__],
        when: {
            freeq!([a__, b__, d__, e__, f__, m_, p_], x_)
                && eqq!(
                    Atom::num(4) * b__.pow(3) + Atom::num(27) * a__.pow(2) * &d__,
                    0
                )
                && !integerq!(p_)
        },
        rhs: {
            let cubic = &a__ + &b__ * x_ + &d__ * x_.pow(3);
            let first = Atom::num(3) * &a__ - &b__ * x_;
            let second = Atom::num(3) * &a__ + Atom::num(2) * &b__ * x_;
            let denominator = first.pow(&p_) * second.pow(Atom::num(2) * &p_);
            let integrand = (&e__ + &f__ * x_).pow(&m_)
                * first.pow(&p_)
                * second.pow(Atom::num(2) * &p_);
            let recursive = rubi_rhs_int(&integrand, x_);

            rubi_star(cubic.pow(&p_), recursive / denominator)
        },
    ));
}

fn push_rules_rule_2484(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, e__, f__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 2484,
        source: "Int[(e_.+f_.*x_)^m_.*(a_+b_.*x_+d_.*x_^3)^p_.,x_Symbol] :=
          Int[ExpandIntegrand[(e+f*x)^m*(a+b*x+d*x^3)^p,x],x] /;
        FreeQ[{a,b,d,e,f,m},x] && NeQ[4*b^3+27*a^2*d,0] && IGtQ[p,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [e__, f__, m_, a__, b__, d__, p_, x_],
        optional: [e__, f__, m_, b__, d__, p_],
        when: {
            freeq!([a__, b__, d__, e__, f__, m_], x_)
                && neq!(
                    Atom::num(4) * b__.pow(3) + Atom::num(27) * a__.pow(2) * &d__,
                    0
                )
                && igtq!(p_, 0)
        },
        rhs: {
            let integrand =
                (&e__ + &f__ * x_).pow(&m_) * (&a__ + &b__ * x_ + &d__ * x_.pow(3)).pow(&p_);
            let expanded = rubi_expand_integrand(&integrand, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_2485(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, e__, f__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 2485,
        source: "Int[(e_.+f_.*x_)^m_.*(a_+b_.*x_+d_.*x_^3)^p_,x_Symbol] :=
          With[{r=Rt[-9*a*d^2+Sqrt[3]*d*Sqrt[4*b^3*d+27*a^2*d^2],3]},
          1/d^(2*p) \\[Star] Int[(e+f*x)^m*Simp[18^(1/3)*b*d/(3*r)-r/18^(1/3)+d*x,x]^p*
            Simp[b*d/3+12^(1/3)*b^2*d^2/(3*r^2)+r^2/(3*12^(1/3))-d*(2^(1/3)*b*d/(3^(1/3)*r)-r/18^(1/3))*x+d^2*x^2,x]^p,x]] /;
        FreeQ[{a,b,d,e,f,m},x] && NeQ[4*b^3+27*a^2*d,0] && ILtQ[p,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [e__, f__, m_, a__, b__, d__, p_, x_],
        optional: [e__, f__, m_, b__, d__],
        when: {
            freeq!([a__, b__, d__, e__, f__, m_], x_)
                && neq!(
                    Atom::num(4) * b__.pow(3) + Atom::num(27) * a__.pow(2) * &d__,
                    0
                )
                && iltq!(p_, 0)
        },
        rhs: {
            let sqrt_three = Atom::num(3).sqrt();
            let r = rubi_rt(
                &(-Atom::num(9) * &a__ * d__.pow(2)
                    + &sqrt_three
                        * &d__
                        * (Atom::num(4) * b__.pow(3) * &d__
                            + Atom::num(27) * a__.pow(2) * d__.pow(2))
                        .sqrt()),
                3,
            );
            let rt18 = rubi_rt(&Atom::num(18), 3);
            let rt12 = rubi_rt(&Atom::num(12), 3);
            let rt2 = rubi_rt(&Atom::num(2), 3);
            let rt3 = rubi_rt(&Atom::num(3), 3);
            let simp1 = rubi_simp(
                &(&rt18 * &b__ * &d__ / (Atom::num(3) * &r) - &r / &rt18 + &d__ * x_),
                x_,
            );
            let simp2 = rubi_simp(
                &(&b__ * &d__ / Atom::num(3)
                    + &rt12 * b__.pow(2) * d__.pow(2) / (Atom::num(3) * r.pow(2))
                    + r.pow(2) / (Atom::num(3) * &rt12)
                    - &d__ * (&rt2 * &b__ * &d__ / (&rt3 * &r) - &r / &rt18) * x_
                    + d__.pow(2) * x_.pow(2)),
                x_,
            );
            let integrand = (&e__ + &f__ * x_).pow(&m_) * simp1.pow(&p_) * simp2.pow(&p_);
            let recursive = rubi_rhs_int(&integrand, x_);

            rubi_star(Atom::num(1) / d__.pow(Atom::num(2) * &p_), recursive)
        },
    ));
}

fn push_rules_rule_2486(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, e__, f__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 2486,
        source: "Int[(e_.+f_.*x_)^m_.*(a_+b_.*x_+d_.*x_^3)^p_,x_Symbol] :=
          With[{r=Rt[-9*a*d^2+Sqrt[3]*d*Sqrt[4*b^3*d+27*a^2*d^2],3]},
          (a+b*x+d*x^3)^p/
            (Simp[18^(1/3)*b*d/(3*r)-r/18^(1/3)+d*x,x]^p*
              Simp[b*d/3+12^(1/3)*b^2*d^2/(3*r^2)+r^2/(3*12^(1/3))-d*(2^(1/3)*b*d/(3^(1/3)*r)-r/18^(1/3))*x+d^2*x^2,x]^p) \\[Star]
            Int[(e+f*x)^m*Simp[18^(1/3)*b*d/(3*r)-r/18^(1/3)+d*x,x]^p*
              Simp[b*d/3+12^(1/3)*b^2*d^2/(3*r^2)+r^2/(3*12^(1/3))-d*(2^(1/3)*b*d/(3^(1/3)*r)-r/18^(1/3))*x+d^2*x^2,x]^p,x]] /;
        FreeQ[{a,b,d,e,f,m,p},x] && NeQ[4*b^3+27*a^2*d,0] && Not[IntegerQ[p]]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [e__, f__, m_, a__, b__, d__, p_, x_],
        optional: [e__, f__, m_, b__, d__],
        when: {
            freeq!([a__, b__, d__, e__, f__, m_, p_], x_)
                && neq!(
                    Atom::num(4) * b__.pow(3) + Atom::num(27) * a__.pow(2) * &d__,
                    0
                )
                && !integerq!(p_)
        },
        rhs: {
            let sqrt_three = Atom::num(3).sqrt();
            let r = rubi_rt(
                &(-Atom::num(9) * &a__ * d__.pow(2)
                    + &sqrt_three
                        * &d__
                        * (Atom::num(4) * b__.pow(3) * &d__
                            + Atom::num(27) * a__.pow(2) * d__.pow(2))
                        .sqrt()),
                3,
            );
            let rt18 = rubi_rt(&Atom::num(18), 3);
            let rt12 = rubi_rt(&Atom::num(12), 3);
            let rt2 = rubi_rt(&Atom::num(2), 3);
            let rt3 = rubi_rt(&Atom::num(3), 3);
            let cubic = &a__ + &b__ * x_ + &d__ * x_.pow(3);
            let simp1 = rubi_simp(
                &(&rt18 * &b__ * &d__ / (Atom::num(3) * &r)
                    - &r / &rt18
                    + &d__ * x_),
                x_,
            );
            let simp2 = rubi_simp(
                &(&b__ * &d__ / Atom::num(3)
                    + &rt12 * b__.pow(2) * d__.pow(2) / (Atom::num(3) * r.pow(2))
                    + r.pow(2) / (Atom::num(3) * &rt12)
                    - &d__
                        * (&rt2 * &b__ * &d__ / (&rt3 * &r) - &r / &rt18)
                        * x_
                    + d__.pow(2) * x_.pow(2)),
                x_,
            );
            let denominator = simp1.pow(&p_) * simp2.pow(&p_);
            let integrand = (&e__ + &f__ * x_).pow(&m_) * &denominator;
            let recursive = rubi_rhs_int(&integrand, x_);

            rubi_star(cubic.pow(&p_), recursive / denominator)
        },
    ));
}

fn push_rules_rule_2505(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, e__, x_);
    rules.push(rubi_rule!(
        order: 2505,
        source: "Int[x_/Sqrt[a_+b_.*x_+c_.*x_^2+e_.*x_^4],x_Symbol] :=
          With[{Px=1/320*(33*b^2*c+6*a*c^2+40*a^2*e)-22/5*a*c*e*x^2+22/15*b*c*e*x^3+1/4*e*(5*c^2+4*a*e)*x^4+
            4/3*b*e^2*x^5+2*c*e^2*x^6+e^3*x^8},
          1/(8*Rt[e,2])*Log[Px + (1/(8*Rt[e,2]*x) \\[Star] D[Px,x])*Sqrt[a+b*x+c*x^2+e*x^4]]] /;
        FreeQ[{a,b,c,e},x] && EqQ[71*c^2+100*a*e,0] && EqQ[1152*c^3-125*b^2*e,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: ["Bronstein"],
        pattern: x_ / (a__ + b__ * x_ + c__ * x_.pow(2) + e__ * x_.pow(4)).sqrt(),
        with: [a__, b__, c__, e__, x_],
        optional: [b__, c__, e__],
        when: {
            freeq!([a__, b__, c__, e__], x_)
                && eqq!(
                    Atom::num(71) * c__.pow(2) + Atom::num(100) * &a__ * &e__,
                    0
                )
                && eqq!(
                    Atom::num(1152) * c__.pow(3) - Atom::num(125) * b__.pow(2) * &e__,
                    0
                )
        },
        rhs: {
            let rt_e = rubi_rt(&e__, 2);
            let rt_denominator = Atom::num(8) * &rt_e;
            let dist_denominator = &rt_denominator * x_;

            let px = (Atom::num(1) / Atom::num(320))
                * (Atom::num(33) * b__.pow(2) * &c__
                    + Atom::num(6) * &a__ * c__.pow(2)
                    + Atom::num(40) * a__.pow(2) * &e__)
                - Atom::num(22) * &a__ * &c__ * &e__ * x_.pow(2) / Atom::num(5)
                + Atom::num(22) * &b__ * &c__ * &e__ * x_.pow(3) / Atom::num(15)
                + &e__ * (Atom::num(5) * c__.pow(2) + Atom::num(4) * &a__ * &e__)
                    * x_.pow(4)
                    / Atom::num(4)
                + Atom::num(4) * &b__ * e__.pow(2) * x_.pow(5) / Atom::num(3)
                + Atom::num(2) * &c__ * e__.pow(2) * x_.pow(6)
                + e__.pow(3) * x_.pow(8);
            let quartic = &a__ + &b__ * x_ + &c__ * x_.pow(2) + &e__ * x_.pow(4);
            let derivative_term =
                rubi_star(Atom::num(1) / dist_denominator, px.derivative(x_));

            rubi_simp(
                &((&px + derivative_term * quartic.sqrt()).log() / rt_denominator),
                x_,
            )
        },
    ));
}

fn push_rules_rule_2506(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_a__, capital_b__, a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 2506,
        source: "Int[(A_+B_.*x_)/Sqrt[a_+b_.*x_+c_.*x_^2+d_.*x_^3+e_.*x_^4],x_Symbol] :=
          B \\[Star] Subst[Int[x/Sqrt[(-3*d^4+16*c*d^2*e-64*b*d*e^2+256*a*e^3)/(256*e^3)+(d^3-4*c*d*e+8*b*e^2)*x/(8*e^2)-
            (3*d^2-8*c*e)*x^2/(8*e)+e*x^4],x],x,d/(4*e)+x] /;
        FreeQ[{a,b,c,d,e,A,B},x] && EqQ[B*d-4*A*e,0] &&
          EqQ[d*(141*d^3-752*c*d*e-400*b*e^2)+16*e^2*(71*c^2+100*a*e),0] &&
          EqQ[144*(3*d^2-8*c*e)^3+125*(d^3-4*c*d*e+8*b*e^2)^2,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (capital_a__ + capital_b__ * x_)
            / (a__ + b__ * x_ + c__ * x_.pow(2) + d__ * x_.pow(3) + e__ * x_.pow(4)).sqrt(),
        with: [capital_a__, capital_b__, a__, b__, c__, d__, e__, x_],
        optional: [capital_b__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__, capital_a__, capital_b__], x_)
                && eqq!(&capital_b__ * &d__ - Atom::num(4) * &capital_a__ * &e__, 0)
                && eqq!(
                    &d__ * (Atom::num(141) * d__.pow(3)
                        - Atom::num(752) * &c__ * &d__ * &e__
                        - Atom::num(400) * &b__ * e__.pow(2))
                        + Atom::num(16)
                            * e__.pow(2)
                            * (Atom::num(71) * c__.pow(2) + Atom::num(100) * &a__ * &e__),
                    0
                )
                && eqq!(
                    Atom::num(144)
                        * (Atom::num(3) * d__.pow(2) - Atom::num(8) * &c__ * &e__).pow(3)
                        + Atom::num(125)
                            * (d__.pow(3) - Atom::num(4) * &c__ * &d__ * &e__
                                + Atom::num(8) * &b__ * e__.pow(2))
                            .pow(2),
                    0
                )
        },
        rhs: {
            let shifted_quartic = (-Atom::num(3) * d__.pow(4)
                + Atom::num(16) * &c__ * d__.pow(2) * &e__
                - Atom::num(64) * &b__ * &d__ * e__.pow(2)
                + Atom::num(256) * &a__ * e__.pow(3))
                / (Atom::num(256) * e__.pow(3))
                + (d__.pow(3) - Atom::num(4) * &c__ * &d__ * &e__
                    + Atom::num(8) * &b__ * e__.pow(2))
                    * x_
                    / (Atom::num(8) * e__.pow(2))
                - (Atom::num(3) * d__.pow(2) - Atom::num(8) * &c__ * &e__) * x_.pow(2)
                    / (Atom::num(8) * &e__)
                + &e__ * x_.pow(4);
            let transformed = rubi_rhs_int(&(x_ / shifted_quartic.sqrt()), x_);

            rubi_star(capital_b__, rubi_subst(
                        &transformed,
                        x_,
                        &d__ / (Atom::num(4) * &e__) + x_,
                    ))
        },
    ));
}

fn push_rules_rule_2507(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, x_);
    rules.push(rubi_rule!(
        order: 2507,
        source: "Int[(f_+g_.*x_^2)/((d_+e_.*x_+d_.*x_^2)*Sqrt[a_+b_.*x_+c_.*x_^2+b_.*x_^3+a_.*x_^4]),x_Symbol] :=
          a*f/(d*Rt[a^2*(2*a-c),2])*ArcTan[(a*b+(4*a^2+b^2-2*a*c)*x+a*b*x^2)/(2*Rt[a^2*(2*a-c),2]*Sqrt[a+b*x+c*x^2+b*x^3+a*x^4])] /;
        FreeQ[{a,b,c,d,e,f,g},x] && EqQ[b*d-a*e,0] && EqQ[f+g,0] && PosQ[a^2*(2*a-c)]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [f__, g__, d__, e__, a__, b__, c__, x_],
        optional: [g__, d__, e__, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__], x_)
                && eqq!(&b__ * &d__ - &a__ * &e__, 0)
                && eqq!(&f__ + &g__, 0)
                && posq!(a__.pow(2) * (Atom::num(2) * &a__ - &c__))
        },
        rhs: {
            let rt = rubi_rt(&(a__.pow(2) * (Atom::num(2) * &a__ - &c__)), 2);
            let quartic =
                &a__ + &b__ * x_ + &c__ * x_.pow(2) + &b__ * x_.pow(3) + &a__ * x_.pow(4);
            let atan_denominator = Atom::num(2) * &rt * quartic.sqrt();
            let coefficient_denominator = &d__ * &rt;

            let atan_argument = (&a__ * &b__
                + (Atom::num(4) * a__.pow(2) + b__.pow(2) - Atom::num(2) * &a__ * &c__) * x_
                + &a__ * &b__ * x_.pow(2))
                / atan_denominator;

            rubi_simp(
                &(&a__ * &f__ * atan_argument.atan() / coefficient_denominator),
                x_,
            )
        },
    ));
}

fn push_rules_rule_2508(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, x_);
    rules.push(rubi_rule!(
        order: 2508,
        source: "Int[(f_+g_.*x_^2)/((d_+e_.*x_+d_.*x_^2)*Sqrt[a_+b_.*x_+c_.*x_^2+b_.*x_^3+a_.*x_^4]),x_Symbol] :=
          -a*f/(d*Rt[-a^2*(2*a-c),2])*ArcTanh[(a*b+(4*a^2+b^2-2*a*c)*x+a*b*x^2)/(2*Rt[-a^2*(2*a-c),2]*Sqrt[a+b*x+c*x^2+b*x^3+a*x^4])] /;
        FreeQ[{a,b,c,d,e,f,g},x] && EqQ[b*d-a*e,0] && EqQ[f+g,0] && NegQ[a^2*(2*a-c)]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [f__, g__, d__, e__, a__, b__, c__, x_],
        optional: [g__, d__, e__, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__], x_)
                && eqq!(&b__ * &d__ - &a__ * &e__, 0)
                && eqq!(&f__ + &g__, 0)
                && negq!(a__.pow(2) * (Atom::num(2) * &a__ - &c__))
        },
        rhs: {
            let rt = rubi_rt(&(-a__.pow(2) * (Atom::num(2) * &a__ - &c__)), 2);
            let quartic =
                &a__ + &b__ * x_ + &c__ * x_.pow(2) + &b__ * x_.pow(3) + &a__ * x_.pow(4);
            let atanh_denominator = Atom::num(2) * &rt * quartic.sqrt();
            let coefficient_denominator = &d__ * &rt;

            let atanh_argument = (&a__ * &b__
                + (Atom::num(4) * a__.pow(2) + b__.pow(2) - Atom::num(2) * &a__ * &c__) * x_
                + &a__ * &b__ * x_.pow(2))
                / atanh_denominator;

            rubi_simp(
                &(-&a__ * &f__ * atanh_argument.atanh() / coefficient_denominator),
                x_,
            )
        },
    ));
}

fn push_rules_rule_2500(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_a__,
        capital_b__,
        capital_c__,
        a__,
        b__,
        c__,
        d__,
        e__,
        x_
    );
    rules.push(rubi_rule!(
        order: 2500,
        source: "Int[(A_.+B_.*x_+C_.*x_^2)/(a_+b_.*x_+c_.*x_^2+d_.*x_^3+e_.*x_^4),x_Symbol] :=
          With[{q=Rt[C*(2*e*(B*d-4*A*e)+C*(d^2-4*c*e)),2]},
          -2*C^2/q*ArcTanh[(C*d-B*e+2*C*e*x)/q] +
          2*C^2/q*ArcTanh[C*(4*B*c*C-3*B^2*d-4*A*C*d+12*A*B*e+4*C*(2*c*C-B*d+2*A*e)*x+4*C*(2*C*d-B*e)*x^2+8*C^2*e*x^3)/(q*(B^2-4*A*C))]] /;
        FreeQ[{a,b,c,d,e,A,B,C},x] && EqQ[B^2*d+2*C*(b*C+A*d)-2*B*(c*C+2*A*e),0] &&
          EqQ[2*B^2*c*C-8*a*C^3-B^3*d-4*A*B*C*d+4*A*(B^2+2*A*C)*e,0] && PosQ[C*(2*e*(B*d-4*A*e)+C*(d^2-4*c*e))]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [capital_a__, capital_b__, capital_c__, a__, b__, c__, d__, e__, x_],
        optional: [capital_a__, capital_b__, capital_c__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__, capital_a__, capital_b__, capital_c__], x_)
                && eqq!(
                    capital_b__.pow(2) * &d__
                        + Atom::num(2) * &capital_c__ * (&b__ * &capital_c__ + &capital_a__ * &d__)
                        - Atom::num(2)
                            * &capital_b__
                            * (&c__ * &capital_c__ + Atom::num(2) * &capital_a__ * &e__),
                    0
                )
                && eqq!(
                    Atom::num(2) * capital_b__.pow(2) * &c__ * &capital_c__
                        - Atom::num(8) * &a__ * capital_c__.pow(3)
                        - capital_b__.pow(3) * &d__
                        - Atom::num(4) * &capital_a__ * &capital_b__ * &capital_c__ * &d__
                        + Atom::num(4)
                            * &capital_a__
                            * (capital_b__.pow(2) + Atom::num(2) * &capital_a__ * &capital_c__)
                            * &e__,
                    0
                )
                && posq!(
                    &capital_c__
                        * (Atom::num(2)
                            * &e__
                            * (&capital_b__ * &d__ - Atom::num(4) * &capital_a__ * &e__)
                            + &capital_c__ * (d__.pow(2) - Atom::num(4) * &c__ * &e__))
                )
        },
        rhs: {
            let q = rubi_rt(
                &(&capital_c__
                    * (Atom::num(2)
                        * &e__
                        * (&capital_b__ * &d__ - Atom::num(4) * &capital_a__ * &e__)
                        + &capital_c__ * (d__.pow(2) - Atom::num(4) * &c__ * &e__))),
                2,
            );
            let second_denominator =
                &q * (capital_b__.pow(2) - Atom::num(4) * &capital_a__ * &capital_c__);

            let first_argument = (&capital_c__ * &d__ - &capital_b__ * &e__
                + Atom::num(2) * &capital_c__ * &e__ * x_)
                / &q;
            let second_argument = &capital_c__
                * (Atom::num(4) * &capital_b__ * &c__ * &capital_c__
                    - Atom::num(3) * capital_b__.pow(2) * &d__
                    - Atom::num(4) * &capital_a__ * &capital_c__ * &d__
                    + Atom::num(12) * &capital_a__ * &capital_b__ * &e__
                    + Atom::num(4)
                        * &capital_c__
                        * (Atom::num(2) * &c__ * &capital_c__ - &capital_b__ * &d__
                            + Atom::num(2) * &capital_a__ * &e__)
                        * x_
                    + Atom::num(4)
                        * &capital_c__
                        * (Atom::num(2) * &capital_c__ * &d__ - &capital_b__ * &e__)
                        * x_.pow(2)
                    + Atom::num(8) * capital_c__.pow(2) * &e__ * x_.pow(3))
                / second_denominator;

            rubi_simp(
                    &(-Atom::num(2) * capital_c__.pow(2) * first_argument.atanh() / &q),
                    x_,
                ) + rubi_simp(
                    &(Atom::num(2) * capital_c__.pow(2) * second_argument.atanh() / q),
                    x_,
                )
        },
    ));
}

fn push_rules_rule_2501(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_a__, capital_c__, a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 2501,
        source: "Int[(A_.+C_.*x_^2)/(a_+b_.*x_+c_.*x_^2+d_.*x_^3+e_.*x_^4),x_Symbol] :=
          With[{q=Rt[C*(-8*A*e^2+C*(d^2-4*c*e)),2]},
          -2*C^2/q*ArcTanh[C*(d+2*e*x)/q] + 2*C^2/q*ArcTanh[C*(A*d-2*(c*C+A*e)*x-2*C*d*x^2-2*C*e*x^3)/(A*q)]] /;
        FreeQ[{a,b,c,d,e,A,C},x] && EqQ[b*C+A*d,0] && EqQ[a*C^2-A^2*e,0] && PosQ[C*(-8*A*e^2+C*(d^2-4*c*e))]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [capital_a__, capital_c__, a__, b__, c__, d__, e__, x_],
        optional: [capital_a__, capital_c__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__, capital_a__, capital_c__], x_)
                && eqq!(&b__ * &capital_c__ + &capital_a__ * &d__, 0)
                && eqq!(&a__ * capital_c__.pow(2) - capital_a__.pow(2) * &e__, 0)
                && posq!(
                    &capital_c__
                        * (-Atom::num(8) * &capital_a__ * e__.pow(2)
                            + &capital_c__ * (d__.pow(2) - Atom::num(4) * &c__ * &e__))
                )
        },
        rhs: {
            let q = rubi_rt(
                &(&capital_c__
                    * (-Atom::num(8) * &capital_a__ * e__.pow(2)
                        + &capital_c__ * (d__.pow(2) - Atom::num(4) * &c__ * &e__))),
                2,
            );
            let second_denominator = &capital_a__ * &q;

            let first_argument =
                &capital_c__ * (&d__ + Atom::num(2) * &e__ * x_) / &q;
            let second_argument = &capital_c__
                * (&capital_a__ * &d__
                    - Atom::num(2) * (&c__ * &capital_c__ + &capital_a__ * &e__) * x_
                    - Atom::num(2) * &capital_c__ * &d__ * x_.pow(2)
                    - Atom::num(2) * &capital_c__ * &e__ * x_.pow(3))
                / second_denominator;

            rubi_simp(
                    &(-Atom::num(2) * capital_c__.pow(2) * first_argument.atanh() / &q),
                    x_,
                ) + rubi_simp(
                    &(Atom::num(2) * capital_c__.pow(2) * second_argument.atanh() / q),
                    x_,
                )
        },
    ));
}

fn push_rules_rule_2502(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_a__,
        capital_b__,
        capital_c__,
        a__,
        b__,
        c__,
        d__,
        e__,
        x_
    );
    rules.push(rubi_rule!(
        order: 2502,
        source: "Int[(A_.+B_.*x_+C_.*x_^2)/(a_+b_.*x_+c_.*x_^2+d_.*x_^3+e_.*x_^4),x_Symbol] :=
          With[{q=Rt[-C*(2*e*(B*d-4*A*e)+C*(d^2-4*c*e)),2]},
          2*C^2/q*ArcTan[(C*d-B*e+2*C*e*x)/q] -
          2*C^2/q*ArcTan[C*(4*B*c*C-3*B^2*d-4*A*C*d+12*A*B*e+4*C*(2*c*C-B*d+2*A*e)*x+4*C*(2*C*d-B*e)*x^2+8*C^2*e*x^3)/(q*(B^2-4*A*C))]] /;
        FreeQ[{a,b,c,d,e,A,B,C},x] && EqQ[B^2*d+2*C*(b*C+A*d)-2*B*(c*C+2*A*e),0] &&
          EqQ[2*B^2*c*C-8*a*C^3-B^3*d-4*A*B*C*d+4*A*(B^2+2*A*C)*e,0] && NegQ[C*(2*e*(B*d-4*A*e)+C*(d^2-4*c*e))]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [capital_a__, capital_b__, capital_c__, a__, b__, c__, d__, e__, x_],
        optional: [capital_a__, capital_b__, capital_c__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__, capital_a__, capital_b__, capital_c__], x_)
                && eqq!(
                    capital_b__.pow(2) * &d__
                        + Atom::num(2) * &capital_c__ * (&b__ * &capital_c__ + &capital_a__ * &d__)
                        - Atom::num(2)
                            * &capital_b__
                            * (&c__ * &capital_c__ + Atom::num(2) * &capital_a__ * &e__),
                    0
                )
                && eqq!(
                    Atom::num(2) * capital_b__.pow(2) * &c__ * &capital_c__
                        - Atom::num(8) * &a__ * capital_c__.pow(3)
                        - capital_b__.pow(3) * &d__
                        - Atom::num(4) * &capital_a__ * &capital_b__ * &capital_c__ * &d__
                        + Atom::num(4)
                            * &capital_a__
                            * (capital_b__.pow(2) + Atom::num(2) * &capital_a__ * &capital_c__)
                            * &e__,
                    0
                )
                && negq!(
                    &capital_c__
                        * (Atom::num(2)
                            * &e__
                            * (&capital_b__ * &d__ - Atom::num(4) * &capital_a__ * &e__)
                            + &capital_c__ * (d__.pow(2) - Atom::num(4) * &c__ * &e__))
                )
        },
        rhs: {
            let q = rubi_rt(
                &(-&capital_c__
                    * (Atom::num(2)
                        * &e__
                        * (&capital_b__ * &d__ - Atom::num(4) * &capital_a__ * &e__)
                        + &capital_c__ * (d__.pow(2) - Atom::num(4) * &c__ * &e__))),
                2,
            );
            let second_denominator =
                &q * (capital_b__.pow(2) - Atom::num(4) * &capital_a__ * &capital_c__);

            let first_argument = (&capital_c__ * &d__ - &capital_b__ * &e__
                + Atom::num(2) * &capital_c__ * &e__ * x_)
                / &q;
            let second_argument = &capital_c__
                * (Atom::num(4) * &capital_b__ * &c__ * &capital_c__
                    - Atom::num(3) * capital_b__.pow(2) * &d__
                    - Atom::num(4) * &capital_a__ * &capital_c__ * &d__
                    + Atom::num(12) * &capital_a__ * &capital_b__ * &e__
                    + Atom::num(4)
                        * &capital_c__
                        * (Atom::num(2) * &c__ * &capital_c__ - &capital_b__ * &d__
                            + Atom::num(2) * &capital_a__ * &e__)
                        * x_
                    + Atom::num(4)
                        * &capital_c__
                        * (Atom::num(2) * &capital_c__ * &d__ - &capital_b__ * &e__)
                        * x_.pow(2)
                    + Atom::num(8) * capital_c__.pow(2) * &e__ * x_.pow(3))
                / second_denominator;

            rubi_simp(
                    &(Atom::num(2) * capital_c__.pow(2) * first_argument.atan() / &q),
                    x_,
                ) - rubi_simp(
                    &(Atom::num(2) * capital_c__.pow(2) * second_argument.atan() / q),
                    x_,
                )
        },
    ));
}

fn push_rules_rule_2503(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_a__, capital_c__, a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 2503,
        source: "Int[(A_.+C_.*x_^2)/(a_+b_.*x_+c_.*x_^2+d_.*x_^3+e_.*x_^4),x_Symbol] :=
          With[{q=Rt[-C*(-8*A*e^2+C*(d^2-4*c*e)),2]},
          2*C^2/q*ArcTan[(C*d+2*C*e*x)/q] - 2*C^2/q*ArcTan[-C*(-A*d+2*(c*C+A*e)*x+2*C*d*x^2+2*C*e*x^3)/(A*q)]] /;
        FreeQ[{a,b,c,d,e,A,C},x] && EqQ[b*C+A*d,0] && EqQ[a*C^2-A^2*e,0] && NegQ[C*(-8*A*e^2+C*(d^2-4*c*e))]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [capital_a__, capital_c__, a__, b__, c__, d__, e__, x_],
        optional: [capital_a__, capital_c__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__, capital_a__, capital_c__], x_)
                && eqq!(&b__ * &capital_c__ + &capital_a__ * &d__, 0)
                && eqq!(&a__ * capital_c__.pow(2) - capital_a__.pow(2) * &e__, 0)
                && negq!(
                    &capital_c__
                        * (-Atom::num(8) * &capital_a__ * e__.pow(2)
                            + &capital_c__ * (d__.pow(2) - Atom::num(4) * &c__ * &e__))
                )
        },
        rhs: {
            let q = rubi_rt(
                &(-&capital_c__
                    * (-Atom::num(8) * &capital_a__ * e__.pow(2)
                        + &capital_c__ * (d__.pow(2) - Atom::num(4) * &c__ * &e__))),
                2,
            );
            let second_denominator = &capital_a__ * &q;

            let first_argument =
                (&capital_c__ * &d__ + Atom::num(2) * &capital_c__ * &e__ * x_) / &q;
            let second_argument = -&capital_c__
                * (-&capital_a__ * &d__
                    + Atom::num(2) * (&c__ * &capital_c__ + &capital_a__ * &e__) * x_
                    + Atom::num(2) * &capital_c__ * &d__ * x_.pow(2)
                    + Atom::num(2) * &capital_c__ * &e__ * x_.pow(3))
                / second_denominator;

            rubi_simp(
                    &(Atom::num(2) * capital_c__.pow(2) * first_argument.atan() / &q),
                    x_,
                ) - rubi_simp(
                    &(Atom::num(2) * capital_c__.pow(2) * second_argument.atan() / q),
                    x_,
                )
        },
    ));
}

fn push_rules_rule_2519(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_a__, capital_b__, a__, b__, c__, d__, n_, n2_, x_);
    rules.push(rubi_rule!(
        order: 2519,
        source: "Int[(A_+B_.*x_^n_)/(a_+b_.*x_^2+c_.*x_^n_+d_.*x_^n2_), x_Symbol] :=
          A^2*(n-1) \\[Star] Subst[Int[1/(a+A^2*b*(n-1)^2*x^2),x],x,x/(A*(n-1)-B*x^n)] /;
        FreeQ[{a,b,c,d,A,B,n},x] && EqQ[n2,2*n] && NeQ[n,2] && EqQ[a*B^2-A^2*d*(n-1)^2,0] && EqQ[B*c+2*A*d*(n-1),0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (capital_a__ + capital_b__ * x_.pow(n_))
            / (a__ + b__ * x_.pow(2) + c__ * x_.pow(n_) + d__ * x_.pow(n2_)),
        with: [capital_a__, capital_b__, n_, a__, b__, c__, d__, n2_, x_],
        optional: [capital_b__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, capital_a__, capital_b__, n_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && neq!(n_, 2)
                && eqq!(
                    &a__ * capital_b__.pow(2)
                        - capital_a__.pow(2) * &d__ * (&n_ - Atom::num(1)).pow(2),
                    0
                )
                && eqq!(
                    &capital_b__ * &c__
                        + Atom::num(2) * &capital_a__ * &d__ * (&n_ - Atom::num(1)),
                    0
                )
        },
        rhs: {
            let substitution_denominator =
                &capital_a__ * (&n_ - Atom::num(1)) - &capital_b__ * x_.pow(&n_);

            let inner_integrand = Atom::num(1)
                / (&a__
                    + capital_a__.pow(2)
                        * &b__
                        * (&n_ - Atom::num(1)).pow(2)
                        * x_.pow(2));
            let transformed = rubi_rhs_int(&inner_integrand, x_);

            rubi_star(capital_a__.pow(2) * (&n_ - Atom::num(1)), rubi_subst(&transformed, x_, x_ / substitution_denominator))
        },
    ));
}

fn push_rules_rule_2520(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        capital_a__,
        capital_b__,
        a__,
        b__,
        c__,
        d__,
        k_,
        m_,
        n_,
        n2_,
        x_
    );
    rules.push(rubi_rule!(
        order: 2520,
        source: "Int[x_^m_.*(A_+B_.*x_^n_.)/(a_+b_.*x_^k_.+c_.*x_^n_.+d_.*x_^n2_), x_Symbol] :=
          A^2*(m-n+1)/(m+1) \\[Star] Subst[Int[1/(a+A^2*b*(m-n+1)^2*x^2),x],x,x^(m+1)/(A*(m-n+1)+B*(m+1)*x^n)] /;
        FreeQ[{a,b,c,d,A,B,m,n},x] && EqQ[n2,2*n] && EqQ[k,2*(m+1)] && EqQ[a*B^2*(m+1)^2-A^2*d*(m-n+1)^2,0] && EqQ[B*c*(m+1)-2*A*d*(m-n+1),0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: x_.pow(m_) * (capital_a__ + capital_b__ * x_.pow(n_))
            / (a__ + b__ * x_.pow(k_) + c__ * x_.pow(n_) + d__ * x_.pow(n2_)),
        with: [m_, capital_a__, capital_b__, n_, a__, b__, k_, c__, d__, n2_, x_],
        optional: [m_, capital_b__, n_, b__, k_, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, capital_a__, capital_b__, m_, n_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && eqq!(k_, Atom::num(2) * (&m_ + Atom::num(1)))
                && eqq!(
                    &a__ * capital_b__.pow(2) * (&m_ + Atom::num(1)).pow(2)
                        - capital_a__.pow(2) * &d__ * (&m_ - &n_ + Atom::num(1)).pow(2),
                    0
                )
                && eqq!(
                    &capital_b__ * &c__ * (&m_ + Atom::num(1))
                        - Atom::num(2) * &capital_a__ * &d__ * (&m_ - &n_ + Atom::num(1)),
                    0
                )
        },
        rhs: {
            let m_plus_1 = &m_ + Atom::num(1);
            let m_minus_n_plus_1 = &m_ - &n_ + Atom::num(1);
            let coefficient_denominator = &m_plus_1;
            let substitution_denominator = &capital_a__ * &m_minus_n_plus_1
                + &capital_b__ * &m_plus_1 * x_.pow(&n_);

            let inner_integrand = Atom::num(1)
                / (&a__
                    + capital_a__.pow(2)
                        * &b__
                        * m_minus_n_plus_1.pow(2)
                        * x_.pow(2));
            let transformed = rubi_rhs_int(&inner_integrand, x_);

            rubi_star(capital_a__.pow(2) * m_minus_n_plus_1 / coefficient_denominator, rubi_subst(
                        &transformed,
                        x_,
                        x_.pow(m_plus_1) / substitution_denominator,
                    ))
        },
    ));
}

fn push_rules_rule_2521(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, x_);
    rules.push(rubi_rule!(
        order: 2521,
        source: "Int[(a_+b_.*x_^2+c_.*x_^4)/(d_+e_.*x_^2+f_.*x_^4+g_.*x_^6),x_Symbol] :=
          With[{q=Rt[(-a*c*f^2+12*a^2*g^2+f*(3*c^2*d-2*a*b*g))/(c*g*(3*c*d-a*f)),2],
                r=Rt[(a*c*f^2+4*g*(b*c*d+a^2*g)-f*(3*c^2*d+2*a*b*g))/(c*g*(3*c*d-a*f)),2]},
          c/(g*q)*ArcTan[(r+2*x)/q] -
          c/(g*q)*ArcTan[(r-2*x)/q] -
          c/(g*q)*ArcTan[(3*c*d-a*f)*x/(g*q*(b*c*d-2*a^2*g)*(b*c*d-a*b*f+4*a^2*g))*
            (b*c^2*d*f-a*b^2*f*g-2*a^2*c*f*g+6*a^2*b*g^2+c*(3*c^2*d*f-a*c*f^2-b*c*d*g+2*a^2*g^2)*x^2+c^2*g*(3*c*d-a*f)*x^4)]] /;
        FreeQ[{a,b,c,d,e,f,g},x] && EqQ[9*c^3*d^2-c*(b^2+6*a*c)*d*f+a^2*c*f^2+2*a*b*(3*c*d+a*f)*g-12*a^3*g^2,0] &&
          EqQ[3*c^4*d^2*e-3*a^2*c^2*d*f*g+a^3*c*f^2*g+2*a^3*g^2*(b*f-6*a*g)-c^3*d*(2*b*d*f+a*e*f-12*a*d*g),0] &&
          NeQ[3*c*d-a*f,0] && NeQ[b*c*d-2*a^2*g,0] && NeQ[b*c*d-a*b*f+4*a^2*g,0] &&
          PosQ[(-a*c*f^2+12*a^2*g^2+f*(3*c^2*d-2*a*b*g))/(c*g*(3*c*d-a*f))]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: (a__ + b__ * x_.pow(2) + c__ * x_.pow(4))
            / (d__ + e__ * x_.pow(2) + f__ * x_.pow(4) + g__ * x_.pow(6)),
        with: [a__, b__, c__, d__, e__, f__, g__, x_],
        optional: [b__, c__, e__, f__, g__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__], x_)
                && eqq!(
                    Atom::num(9) * c__.pow(3) * d__.pow(2)
                        - &c__ * (b__.pow(2) + Atom::num(6) * &a__ * &c__) * &d__ * &f__
                        + a__.pow(2) * &c__ * f__.pow(2)
                        + Atom::num(2)
                            * &a__
                            * &b__
                            * (Atom::num(3) * &c__ * &d__ + &a__ * &f__)
                            * &g__
                        - Atom::num(12) * a__.pow(3) * g__.pow(2),
                    0
                )
                && eqq!(
                    Atom::num(3) * c__.pow(4) * d__.pow(2) * &e__
                        - Atom::num(3) * a__.pow(2) * c__.pow(2) * &d__ * &f__ * &g__
                        + a__.pow(3) * &c__ * f__.pow(2) * &g__
                        + Atom::num(2) * a__.pow(3) * g__.pow(2) * (&b__ * &f__ - Atom::num(6) * &a__ * &g__)
                        - c__.pow(3)
                            * &d__
                            * (Atom::num(2) * &b__ * &d__ * &f__ + &a__ * &e__ * &f__
                                - Atom::num(12) * &a__ * &d__ * &g__),
                    0
                )
                && neq!(Atom::num(3) * &c__ * &d__ - &a__ * &f__, 0)
                && neq!(&b__ * &c__ * &d__ - Atom::num(2) * a__.pow(2) * &g__, 0)
                && neq!(
                    &b__ * &c__ * &d__ - &a__ * &b__ * &f__ + Atom::num(4) * a__.pow(2) * &g__,
                    0
                )
                && posq!(
                    (-&a__ * &c__ * f__.pow(2)
                        + Atom::num(12) * a__.pow(2) * g__.pow(2)
                        + &f__ * (Atom::num(3) * c__.pow(2) * &d__ - Atom::num(2) * &a__ * &b__ * &g__))
                        / (&c__
                            * &g__
                            * (Atom::num(3) * &c__ * &d__ - &a__ * &f__))
                )
        },
        rhs: {
            let rt_denominator = &c__ * &g__ * (Atom::num(3) * &c__ * &d__ - &a__ * &f__);
            let q = rubi_rt(
                &((-&a__ * &c__ * f__.pow(2)
                    + Atom::num(12) * a__.pow(2) * g__.pow(2)
                    + &f__ * (Atom::num(3) * c__.pow(2) * &d__ - Atom::num(2) * &a__ * &b__ * &g__))
                    / &rt_denominator),
                2,
            );
            let r = rubi_rt(
                &((&a__ * &c__ * f__.pow(2)
                    + Atom::num(4) * &g__ * (&b__ * &c__ * &d__ + a__.pow(2) * &g__)
                    - &f__ * (Atom::num(3) * c__.pow(2) * &d__ + Atom::num(2) * &a__ * &b__ * &g__))
                    / rt_denominator),
                2,
            );
            let coefficient_denominator = &g__ * &q;
            let third_argument_denominator = &g__
                * &q
                * (&b__ * &c__ * &d__ - Atom::num(2) * a__.pow(2) * &g__)
                * (&b__ * &c__ * &d__ - &a__ * &b__ * &f__ + Atom::num(4) * a__.pow(2) * &g__);

            let first_argument = (&r + Atom::num(2) * x_) / &q;
            let second_argument = (&r - Atom::num(2) * x_) / &q;
            let third_argument = (Atom::num(3) * &c__ * &d__ - &a__ * &f__)
                * x_
                / third_argument_denominator
                * (&b__ * c__.pow(2) * &d__ * &f__
                    - &a__ * b__.pow(2) * &f__ * &g__
                    - Atom::num(2) * a__.pow(2) * &c__ * &f__ * &g__
                    + Atom::num(6) * a__.pow(2) * &b__ * g__.pow(2)
                    + &c__
                        * (Atom::num(3) * c__.pow(2) * &d__ * &f__
                            - &a__ * &c__ * f__.pow(2)
                            - &b__ * &c__ * &d__ * &g__
                            + Atom::num(2) * a__.pow(2) * g__.pow(2))
                        * x_.pow(2)
                    + c__.pow(2) * &g__ * (Atom::num(3) * &c__ * &d__ - &a__ * &f__) * x_.pow(4));

            rubi_simp(
                    &(&c__ * first_argument.atan() / &coefficient_denominator),
                    x_,
                ) - rubi_simp(
                    &(&c__ * second_argument.atan() / &coefficient_denominator),
                    x_,
                ) - rubi_simp(
                    &(c__ * third_argument.atan() / coefficient_denominator),
                    x_,
                )
        },
    ));
}

fn push_rules_rule_2522(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, c__, d__, e__, f__, g__, x_);
    rules.push(rubi_rule!(
        order: 2522,
        source: "Int[(a_+c_.*x_^4)/(d_+e_.*x_^2+f_.*x_^4+g_.*x_^6),x_Symbol] :=
          With[{q=Rt[(-a*c*f^2+12*a^2*g^2+3*f*c^2*d)/(c*g*(3*c*d-a*f)),2],
                r=Rt[(a*c*f^2+4*a^2*g^2-3*c^2*d*f)/(c*g*(3*c*d-a*f)),2]},
          c/(g*q)*ArcTan[(r+2*x)/q] -
          c/(g*q)*ArcTan[(r-2*x)/q] -
          c/(g*q)*ArcTan[(c*(3*c*d-a*f)*x*(2*a^2*f*g-(3*c^2*d*f-a*c*f^2+2*a^2*g^2)*x^2-c*(3*c*d-a*f)*g*x^4))/(8*a^4*g^3*q)]] /;
        FreeQ[{a,c,d,e,f,g},x] && EqQ[9*c^3*d^2-6*a*c^2*d*f+a^2*c*f^2-12*a^3*g^2,0] &&
          EqQ[3*c^4*d^2*e-3*a^2*c^2*d*f*g+a^3*c*f^2*g-12*a^4*g^3-a*c^3*d*(e*f-12*d*g),0] &&
          NeQ[3*c*d-a*f,0] && PosQ[(-a*c*f^2+12*a^2*g^2+3*c^2*d*f)/(c*g*(3*c*d-a*f))]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: (a__ + c__ * x_.pow(4))
            / (d__ + e__ * x_.pow(2) + f__ * x_.pow(4) + g__ * x_.pow(6)),
        with: [a__, c__, d__, e__, f__, g__, x_],
        optional: [c__, e__, f__, g__],
        when: {
            freeq!([a__, c__, d__, e__, f__, g__], x_)
                && eqq!(
                    Atom::num(9) * c__.pow(3) * d__.pow(2)
                        - Atom::num(6) * &a__ * c__.pow(2) * &d__ * &f__
                        + a__.pow(2) * &c__ * f__.pow(2)
                        - Atom::num(12) * a__.pow(3) * g__.pow(2),
                    0
                )
                && eqq!(
                    Atom::num(3) * c__.pow(4) * d__.pow(2) * &e__
                        - Atom::num(3) * a__.pow(2) * c__.pow(2) * &d__ * &f__ * &g__
                        + a__.pow(3) * &c__ * f__.pow(2) * &g__
                        - Atom::num(12) * a__.pow(4) * g__.pow(3)
                        - &a__
                            * c__.pow(3)
                            * &d__
                            * (&e__ * &f__ - Atom::num(12) * &d__ * &g__),
                    0
                )
                && neq!(Atom::num(3) * &c__ * &d__ - &a__ * &f__, 0)
                && posq!(
                    (-&a__ * &c__ * f__.pow(2)
                        + Atom::num(12) * a__.pow(2) * g__.pow(2)
                        + Atom::num(3) * &f__ * c__.pow(2) * &d__)
                        / (&c__
                            * &g__
                            * (Atom::num(3) * &c__ * &d__ - &a__ * &f__))
                )
        },
        rhs: {
            let rt_denominator = &c__ * &g__ * (Atom::num(3) * &c__ * &d__ - &a__ * &f__);
            let q = rubi_rt(
                &((-&a__ * &c__ * f__.pow(2)
                    + Atom::num(12) * a__.pow(2) * g__.pow(2)
                    + Atom::num(3) * &f__ * c__.pow(2) * &d__)
                    / &rt_denominator),
                2,
            );
            let r = rubi_rt(
                &((&a__ * &c__ * f__.pow(2) + Atom::num(4) * a__.pow(2) * g__.pow(2)
                    - Atom::num(3) * c__.pow(2) * &d__ * &f__)
                    / rt_denominator),
                2,
            );
            let coefficient_denominator = &g__ * &q;
            let third_argument_denominator = Atom::num(8) * a__.pow(4) * g__.pow(3) * &q;

            let first_argument = (&r + Atom::num(2) * x_) / &q;
            let second_argument = (&r - Atom::num(2) * x_) / &q;
            let third_argument = &c__
                * (Atom::num(3) * &c__ * &d__ - &a__ * &f__)
                * x_
                * (Atom::num(2) * a__.pow(2) * &f__ * &g__
                    - (Atom::num(3) * c__.pow(2) * &d__ * &f__
                        - &a__ * &c__ * f__.pow(2)
                        + Atom::num(2) * a__.pow(2) * g__.pow(2))
                        * x_.pow(2)
                    - &c__ * (Atom::num(3) * &c__ * &d__ - &a__ * &f__) * &g__ * x_.pow(4))
                / third_argument_denominator;

            rubi_simp(
                    &(&c__ * first_argument.atan() / &coefficient_denominator),
                    x_,
                ) - rubi_simp(
                    &(&c__ * second_argument.atan() / &coefficient_denominator),
                    x_,
                ) - rubi_simp(
                    &(c__ * third_argument.atan() / coefficient_denominator),
                    x_,
                )
        },
    ));
}

fn push_rules_rule_2466(rules: &mut Vec<RubiRule>) {
    rubi_symb!(p_, q6_, u__);
    rules.push(rubi_rule!(
        order: 2466,
        source: "Int[u_.*Q6_^p_,x_Symbol] :=
          With[{a=Coeff[Q6,x,0],b=Coeff[Q6,x,2],c=Coeff[Q6,x,3],d=Coeff[Q6,x,4],e=Coeff[Q6,x,6]},
          1/(3^(3*p)*a^(2*p)) \\[Star] Int[ExpandIntegrand[u*
            (3*a+3*Rt[a,3]^2*Rt[c,3]*x+b*x^2)^p*
            (3*a-3*(-1)^(1/3)*Rt[a,3]^2*Rt[c,3]*x+b*x^2)^p*
            (3*a+3*(-1)^(2/3)*Rt[a,3]^2*Rt[c,3]*x+b*x^2)^p,x],x] /;
         EqQ[b^2-3*a*d,0] && EqQ[b^3-27*a^2*e,0]] /;
        ILtQ[p,0] && PolyQ[Q6,x,6] && EqQ[Coeff[Q6,x,1],0] && EqQ[Coeff[Q6,x,5],0] && RationalFunctionQ[u,x]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern: u__ * q6_.pow(p_),
        with: [u__, q6_, p_, x_],
        optional: [u__],
        when: {
            iltq!(p_, 0)
                && rubi_poly_q_degree(&q6_, x_, 6)
                && eqq!(rubi_coeff(&q6_, x_, 1).unwrap(), 0)
                && eqq!(rubi_coeff(&q6_, x_, 5).unwrap(), 0)
                && rubi_rational_function_q(&u__, x_)
                && {
                    let a = rubi_coeff(&q6_, x_, 0).unwrap();
                    let b = rubi_coeff(&q6_, x_, 2).unwrap();
                    let d = rubi_coeff(&q6_, x_, 4).unwrap();
                    let e = rubi_coeff(&q6_, x_, 6).unwrap();
                    eqq!(b.pow(2) - Atom::num(3) * &a * &d, 0)
                        && eqq!(b.pow(3) - Atom::num(27) * a.pow(2) * &e, 0)
                }
        },
        rhs: {
            let a = rubi_coeff(&q6_, x_, 0).unwrap();
            let b = rubi_coeff(&q6_, x_, 2).unwrap();
            let c = rubi_coeff(&q6_, x_, 3).unwrap();
            let rt_a = rubi_rt(&a, 3);
            let rt_c = rubi_rt(&c, 3);
            let minus_one_one_third = Atom::num(-1).pow(Atom::num(1) / Atom::num(3));
            let minus_one_two_thirds = Atom::num(-1).pow(Atom::num(2) / Atom::num(3));
            let common = Atom::num(3) * rt_a.pow(2) * rt_c;
            let expanded_integrand = rubi_expand_integrand(
                &(&u__
                    * (Atom::num(3) * &a + &common * x_ + &b * x_.pow(2)).pow(&p_)
                    * (Atom::num(3) * &a - &minus_one_one_third * &common * x_
                        + &b * x_.pow(2))
                    .pow(&p_)
                    * (Atom::num(3) * &a
                        + &minus_one_two_thirds * &common * x_
                        + &b * x_.pow(2))
                    .pow(&p_)),
                x_,
            );
            rubi_star(Atom::num(1) / (Atom::num(3).pow(Atom::num(3) * &p_)
                        * a.pow(Atom::num(2) * &p_)), rubi_rhs_int(&expanded_integrand, x_))
        },
    ));
}

fn push_rules_rule_2523(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; pm_, qn_);
    rules.push(rubi_rule!(
        order: 2523,
        source: "Int[Pm_/Qn_,x_Symbol] :=
          With[{m=Expon[Pm,x],n=Expon[Qn,x]},
          Coeff[Pm,x,m]*Log[Qn]/(n*Coeff[Qn,x,n]) + Simplify[Pm-Coeff[Pm,x,m]*D[Qn,x]/(n*Coeff[Qn,x,n])] \\[Star] Int[1/Qn,x]/;
         EqQ[m,n-1] && EqQ[D[Simplify[Pm-Coeff[Pm,x,m]/(n*Coeff[Qn,x,n])*D[Qn,x]],x],0]] /;
        PolyQ[Pm,x] && PolyQ[Qn,x]",
        desc: "Algebraic expansion and reciprocal integration rule",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [pm_, qn_, x_],
        when: {
            poly_q(&pm_, x_)
                && poly_q(&qn_, x_)
                && {
                    let m = rubi_expon(&pm_, x_).unwrap();
                    let n = rubi_expon(&qn_, x_).unwrap();
                    m == n - 1
                        && {
                            let pm_m = rubi_coeff(&pm_, x_, m).unwrap();
                            let qn_n = rubi_coeff(&qn_, x_, n).unwrap();
                            let denominator = Atom::num(n) * &qn_n;
                            eqq!(
                                rubi_simplify(
                                    &(&pm_ - &pm_m * qn_.derivative(x_) / denominator),
                                )
                                .derivative(x_),
                                0
                            )
                        }
                }
        },
        rhs: {
            let m = rubi_expon(&pm_, x_).unwrap();
            let n = rubi_expon(&qn_, x_).unwrap();
            let pm_m = rubi_coeff(&pm_, x_, m).unwrap();
            let qn_n = rubi_coeff(&qn_, x_, n).unwrap();
            let denominator = Atom::num(n) * &qn_n;
            let reduction = rubi_simplify(&(&pm_ - &pm_m * qn_.derivative(x_) / &denominator));

            rubi_simp(&(&pm_m * qn_.log() / &denominator), x_)
                    + rubi_star(reduction, rubi_rhs_int(&(Atom::num(1) / qn_), x_))
        },
    ));
}

fn push_rules_rule_2524(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; p_, pm_, qn_);
    rules.push(rubi_rule!(
        order: 2524,
        source: "Int[Pm_*Qn_^p_,x_Symbol] :=
          With[{m=Expon[Pm,x],n=Expon[Qn,x]},
          Coeff[Pm,x,m]*Qn^(p+1)/(n*(p+1)*Coeff[Qn,x,n]) + Simplify[Pm-Coeff[Pm,x,m]*D[Qn,x]/(n*Coeff[Qn,x,n])] \\[Star] Int[Qn^p,x]/;
         EqQ[m,n-1] && EqQ[D[Simplify[Pm-Coeff[Pm,x,m]/(n*Coeff[Qn,x,n])*D[Qn,x]],x],0]] /;
        FreeQ[p,x] && PolyQ[Pm,x] && PolyQ[Qn,x] && NeQ[p,-1]",
        desc: "Integrate by parts and recursively integrate the remainder.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [pm_, qn_, p_, x_],
        when: {
            freeq!(p_, x_)
                && poly_q(&pm_, x_)
                && poly_q(&qn_, x_)
                && neq!(p_, -1)
                && {
                    let m = rubi_expon(&pm_, x_).unwrap();
                    let n = rubi_expon(&qn_, x_).unwrap();
                    m == n - 1
                        && {
                            let pm_m = rubi_coeff(&pm_, x_, m).unwrap();
                            let qn_n = rubi_coeff(&qn_, x_, n).unwrap();
                            let denominator = Atom::num(n) * &qn_n;
                            eqq!(
                                rubi_simplify(
                                    &(&pm_ - &pm_m * qn_.derivative(x_) / denominator),
                                )
                                .derivative(x_),
                                0
                            )
                        }
                }
        },
        rhs: {
            let m = rubi_expon(&pm_, x_).unwrap();
            let n = rubi_expon(&qn_, x_).unwrap();
            let pm_m = rubi_coeff(&pm_, x_, m).unwrap();
            let qn_n = rubi_coeff(&qn_, x_, n).unwrap();
            let denominator = Atom::num(n) * (&p_ + Atom::num(1)) * &qn_n;
            let reduction_denominator = Atom::num(n) * &qn_n;
            let reduction =
                rubi_simplify(&(&pm_ - &pm_m * qn_.derivative(x_) / &reduction_denominator));

            rubi_simp(
                    &(&pm_m * qn_.pow(&p_ + Atom::num(1)) / denominator),
                    x_,
                ) + rubi_star(reduction, rubi_rhs_int(&qn_.pow(&p_), x_))
        },
    ));
}

fn push_rules_rule_2525(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; pm_, qn_);
    rules.push(rubi_rule!(
        order: 2525,
        source: "Int[Pm_/Qn_,x_Symbol] :=
          With[{m=Expon[Pm,x],n=Expon[Qn,x]},
          Coeff[Pm,x,m]*Log[Qn]/(n*Coeff[Qn,x,n]) +
          1/(n*Coeff[Qn,x,n]) \\[Star] Int[ExpandToSum[n*Coeff[Qn,x,n]*Pm-Coeff[Pm,x,m]*D[Qn,x],x]/Qn,x]/;
         EqQ[m,n-1]] /;
        PolyQ[Pm,x] && PolyQ[Qn,x]",
        desc: "Algebraic expansion and reciprocal integration rule",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [pm_, qn_, x_],
        when: {
            poly_q(&pm_, x_)
                && poly_q(&qn_, x_)
                && rubi_expon(&pm_, x_).unwrap() == rubi_expon(&qn_, x_).unwrap() - 1
        },
        rhs: {
            let m = rubi_expon(&pm_, x_).unwrap();
            let n = rubi_expon(&qn_, x_).unwrap();
            let pm_m = rubi_coeff(&pm_, x_, m).unwrap();
            let qn_n = rubi_coeff(&qn_, x_, n).unwrap();
            let denominator = Atom::num(n) * &qn_n;
            let expand_to_sum = rubi_expand_to_sum(
                &(Atom::num(n) * &qn_n * &pm_ - &pm_m * qn_.derivative(x_)),
                x_,
            );

            rubi_simp(&(&pm_m * qn_.log() / &denominator), x_)
                    + rubi_star(Atom::num(1) / denominator, rubi_rhs_int(&(expand_to_sum / qn_), x_))
        },
    ));
}

fn push_rules_rule_2526(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; p_, pm_, qn_);
    rules.push(rubi_rule!(
        order: 2526,
        source: "Int[Pm_*Qn_^p_,x_Symbol] :=
          With[{m=Expon[Pm,x],n=Expon[Qn,x]},
          Coeff[Pm,x,m]*Qn^(p+1)/(n*(p+1)*Coeff[Qn,x,n]) +
          1/(n*Coeff[Qn,x,n]) \\[Star] Int[ExpandToSum[n*Coeff[Qn,x,n]*Pm-Coeff[Pm,x,m]*D[Qn,x],x]*Qn^p,x]/;
         EqQ[m,n-1]] /;
        FreeQ[p,x] && PolyQ[Pm,x] && PolyQ[Qn,x] && NeQ[p,-1]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [pm_, qn_, p_, x_],
        when: {
            freeq!(p_, x_)
                && poly_q(&pm_, x_)
                && poly_q(&qn_, x_)
                && neq!(p_, -1)
                && rubi_expon(&pm_, x_).unwrap() == rubi_expon(&qn_, x_).unwrap() - 1
        },
        rhs: {
            let m = rubi_expon(&pm_, x_).unwrap();
            let n = rubi_expon(&qn_, x_).unwrap();
            let pm_m = rubi_coeff(&pm_, x_, m).unwrap();
            let qn_n = rubi_coeff(&qn_, x_, n).unwrap();
            let denominator = Atom::num(n) * (&p_ + Atom::num(1)) * &qn_n;
            let reduction_denominator = Atom::num(n) * &qn_n;
            let expand_to_sum = rubi_expand_to_sum(
                &(Atom::num(n) * &qn_n * &pm_ - &pm_m * qn_.derivative(x_)),
                x_,
            );

            rubi_simp(
                    &(&pm_m * qn_.pow(&p_ + Atom::num(1)) / denominator),
                    x_,
                ) + rubi_star(Atom::num(1) / reduction_denominator, rubi_rhs_int(&(expand_to_sum * qn_.pow(&p_)), x_))
        },
    ));
}

fn push_rules_rule_2527(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; p_, pm_, qn_);
    rules.push(rubi_rule!(
        order: 2527,
        source: "Int[Pm_*Qn_^p_.,x_Symbol] :=
          With[{m=Expon[Pm,x],n=Expon[Qn,x]},
          Coeff[Pm,x,m]*x^(m-n+1)*Qn^(p+1)/((m+n*p+1)*Coeff[Qn,x,n]) +
          1/((m+n*p+1)*Coeff[Qn,x,n]) \\[Star]
            Int[ExpandToSum[(m+n*p+1)*Coeff[Qn,x,n]*Pm-Coeff[Pm,x,m]*x^(m-n)*((m-n+1)*Qn+(p+1)*x*D[Qn,x]),x]*Qn^p,x] /;
         LtQ[1,n,m+1] && m+n*p+1<0] /;
        FreeQ[p,x] && PolyQ[Pm,x] && PolyQ[Qn,x] && LtQ[p,-1]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: ["G&R 2.104"],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [pm_, qn_, p_, x_],
        optional: [p_],
        when: {
            freeq!(p_, x_)
                && poly_q(&pm_, x_)
                && poly_q(&qn_, x_)
                && ltq!(p_, -1)
                && {
                    let m = rubi_expon(&pm_, x_).unwrap();
                    let n = rubi_expon(&qn_, x_).unwrap();
                    ltq!(Atom::num(1), Atom::num(n))
                        && ltq!(Atom::num(n), Atom::num(m + 1))
                        && ltq!(Atom::num(m) + Atom::num(n) * &p_ + Atom::num(1), 0)
                }
        },
        rhs: {
            let m = rubi_expon(&pm_, x_).unwrap();
            let n = rubi_expon(&qn_, x_).unwrap();
            let pm_m = rubi_coeff(&pm_, x_, m).unwrap();
            let qn_n = rubi_coeff(&qn_, x_, n).unwrap();
            let denominator = (Atom::num(m) + Atom::num(n) * &p_ + Atom::num(1)) * &qn_n;

            let expand_to_sum = rubi_expand_to_sum(
                &((Atom::num(m) + Atom::num(n) * &p_ + Atom::num(1)) * &qn_n * &pm_
                    - &pm_m
                        * x_.pow(m - n)
                        * ((Atom::num(m - n + 1)) * &qn_
                            + (&p_ + Atom::num(1)) * x_ * qn_.derivative(x_))),
                x_,
            );

            rubi_simp(
                    &(&pm_m * x_.pow(m - n + 1) * qn_.pow(&p_ + Atom::num(1))
                        / &denominator),
                    x_,
                ) + rubi_star(
                    Atom::num(1) / denominator,
                    rubi_rhs_int(&(expand_to_sum * qn_.pow(&p_)), x_),
                )
        },
    ));
}

// Generated shared pattern builders.

#[inline(never)]
fn rubi_shared_pattern_0(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let capital_a__ = symbols.capital_a__;
    let capital_b__ = symbols.capital_b__;
    let capital_c__ = symbols.capital_c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let x_ = symbols.x_;
    (capital_a__ + capital_b__ * x_ + capital_c__ * x_.pow(2))
        / (a__ + b__ * x_ + c__ * x_.pow(2) + d__ * x_.pow(3) + e__ * x_.pow(4))
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let capital_a__ = symbols.capital_a__;
    let capital_c__ = symbols.capital_c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let x_ = symbols.x_;
    (capital_a__ + capital_c__ * x_.pow(2))
        / (a__ + b__ * x_ + c__ * x_.pow(2) + d__ * x_.pow(3) + e__ * x_.pow(4))
}

#[inline(never)]
fn rubi_shared_pattern_2(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (e__ + f__ * x_).pow(m_) * (a__ + b__ * x_ + d__ * x_.pow(3)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_3(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let g__ = symbols.g__;
    let x_ = symbols.x_;
    (f__ + g__ * x_.pow(2))
        / ((d__ + e__ * x_ + d__ * x_.pow(2))
            * (a__ + b__ * x_ + c__ * x_.pow(2) + b__ * x_.pow(3) + a__ * x_.pow(4)).sqrt())
}

#[inline(never)]
fn rubi_shared_pattern_4(symbols: &RubiSymbols) -> Atom {
    let p_ = symbols.p_;
    let pm_ = symbols.pm_;
    let qn_ = symbols.qn_;
    pm_ * qn_.pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_5(symbols: &RubiSymbols) -> Atom {
    let pm_ = symbols.pm_;
    let qn_ = symbols.qn_;
    pm_ / qn_
}

#[inline(never)]
fn rubi_shared_pattern_6(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let p_ = symbols.p_;
    let px__ = symbols.px__;
    let x_ = symbols.x_;
    px__ * (a__ + b__ * x_ + c__ * x_.pow(2) + d__ * x_.pow(3) + e__ * x_.pow(4)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_7(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let p_ = symbols.p_;
    let px__ = symbols.px__;
    let x_ = symbols.x_;
    px__ * (a__ + b__ * x_ + d__ * x_.pow(3) + e__ * x_.pow(4)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_8(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let m_ = symbols.m_;
    let p_ = symbols.p_;
    let px__ = symbols.px__;
    let x_ = symbols.x_;
    x_.pow(m_)
        * px__
        * (a__ + b__ * x_ + c__ * x_.pow(2) + d__ * x_.pow(3) + e__ * x_.pow(4)).pow(p_)
}
