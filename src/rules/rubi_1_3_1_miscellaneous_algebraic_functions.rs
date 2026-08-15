use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_2471(rules);
    push_rules_rule_2472(rules);
    push_rules_rule_2473(rules);
    push_rules_rule_2474(rules);
    push_rules_rule_2475(rules);
    push_rules_rule_2476(rules);
    push_rules_rule_2477(rules);
    push_rules_rule_2478(rules);
    push_rules_rule_2479(rules);
    push_rules_rule_2480(rules);
    push_rules_rule_2481(rules);
    push_rules_rule_2487(rules);
    push_rules_rule_2488(rules);
    push_rules_rule_2489(rules);
    push_rules_rule_2490(rules);
}

fn push_rules_rule_2471(rules: &mut Vec<RubiRule>) {
    rubi_symb!(p_, px_, u__);
    rules.push(rubi_rule!(
        order: 2471,
        source: "Int[u_.*Px_^p_,x_Symbol] :=
          With[{b=Coeff[Px,x,1],c=Coeff[Px,x,2],d=Coeff[Px,x,3]},
          Px^FracPart[p]/(x^FracPart[p]*(b+c*x+d*x^2)^FracPart[p]) \\[Star] Int[u*x^p*(b+c*x+d*x^2)^p,x]] /;
        FreeQ[p,x] && PolyQ[Px,x,3] && EqQ[Coeff[Px,x,0],0] && Not[IntegerQ[p]]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: u__ * px_.pow(p_),
        with: [u__, px_, p_, x_],
        optional: [u__],
        x_free: [p_],
        when: {
            freeq!(p_, x_)
                && rubi_poly_q_degree(&px_, x_, 3)
                && rubi_coeff(&px_, x_, 0).is_some_and(|coefficient| eqq!(coefficient, 0))
                && !integerq!(p_)
        },
        rhs: {
            let b = rubi_coeff(&px_, x_, 1).unwrap();
            let c = rubi_coeff(&px_, x_, 2).unwrap();
            let d = rubi_coeff(&px_, x_, 3).unwrap();
            let frac_p = rubi_frac_part(&p_);
            let quadratic = &b + &c * x_ + &d * x_.pow(2);
            let multiplier = px_.pow(&frac_p)
                / (x_.pow(&frac_p) * quadratic.pow(&frac_p));
            let recursive = rubi_rhs_int(
                &(u__ * x_.pow(&p_) * quadratic.pow(&p_)),
                x_,
            );
            rubi_star(multiplier, recursive)
        },
    ));
}

fn push_rules_rule_2476(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; p_, px_);
    rules.push(rubi_rule!(
        order: 2476,
        source: "Int[Px_^p_,x_Symbol] :=
          With[{a=Coeff[Px,x,0],b=Coeff[Px,x,1],c=Coeff[Px,x,2],d=Coeff[Px,x,3]},
          1/d^p \\[Star] Int[(c+d*x)^p*(b+d*x^2)^p,x] /;
         EqQ[b*c-a*d,0]] /;
        PolyQ[Px,x,3] && IntegerQ[p]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [px_, p_, x_],
        when: {
            rubi_poly_q_degree(&px_, x_, 3)
                && integerq!(p_)
                && {
                    let a = rubi_coeff(&px_, x_, 0).unwrap();
                    let b = rubi_coeff(&px_, x_, 1).unwrap();
                    let c = rubi_coeff(&px_, x_, 2).unwrap();
                    let d = rubi_coeff(&px_, x_, 3).unwrap();
                    eqq!(&b * &c - &a * &d, 0)
                }
        },
        rhs: {
            let b = rubi_coeff(&px_, x_, 1).unwrap();
            let c = rubi_coeff(&px_, x_, 2).unwrap();
            let d = rubi_coeff(&px_, x_, 3).unwrap();
            let recursive = rubi_rhs_int(
                &((&c + &d * x_).pow(&p_)
                    * (&b + &d * x_.pow(2)).pow(&p_)),
                x_,
            );
            rubi_star(Atom::num(1) / d.pow(&p_), recursive)
        },
    ));
}

fn push_rules_rule_2477(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; p_, px_);
    rules.push(rubi_rule!(
        order: 2477,
        source: "Int[Px_^p_,x_Symbol] :=
          With[{a=Coeff[Px,x,0],b=Coeff[Px,x,1],c=Coeff[Px,x,2],d=Coeff[Px,x,3]},
          Px^p/((c+d*x)^p*(b+d*x^2)^p) \\[Star] Int[(c+d*x)^p*(b+d*x^2)^p,x] /;
         EqQ[b*c-a*d,0]] /;
        FreeQ[p,x] && PolyQ[Px,x,3] && Not[IntegerQ[p]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [px_, p_, x_],
        x_free: [p_],
        when: {
            freeq!(p_, x_)
                && rubi_poly_q_degree(&px_, x_, 3)
                && !integerq!(p_)
                && {
                    let a = rubi_coeff(&px_, x_, 0).unwrap();
                    let b = rubi_coeff(&px_, x_, 1).unwrap();
                    let c = rubi_coeff(&px_, x_, 2).unwrap();
                    let d = rubi_coeff(&px_, x_, 3).unwrap();
                    eqq!(&b * &c - &a * &d, 0)
                }
        },
        rhs: {
            let b = rubi_coeff(&px_, x_, 1).unwrap();
            let c = rubi_coeff(&px_, x_, 2).unwrap();
            let d = rubi_coeff(&px_, x_, 3).unwrap();
            let first = (&c + &d * x_).pow(&p_);
            let second = (&b + &d * x_.pow(2)).pow(&p_);
            let recursive = rubi_rhs_int(&(&first * &second), x_);
            rubi_star(px_.pow(&p_) / (first * second), recursive)
        },
    ));
}

fn push_rules_rule_2478(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; p_, px_);
    rules.push(rubi_rule!(
        order: 2478,
        source: "Int[Px_^p_,x_Symbol] :=
          With[{a=Coeff[Px,x,0],b=Coeff[Px,x,1],c=Coeff[Px,x,2],d=Coeff[Px,x,3]},
          Subst[Int[Simp[a-b^2/(3*c)+d*x^3,x]^p,x],x,c/(3*d)+x] /;
         EqQ[c^2-3*b*d,0]] /;
        FreeQ[p,x] && PolyQ[Px,x,3]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [px_, p_, x_],
        x_free: [p_],
        when: {
            freeq!(p_, x_)
                && rubi_poly_q_degree(&px_, x_, 3)
                && {
                    let b = rubi_coeff(&px_, x_, 1).unwrap();
                    let c = rubi_coeff(&px_, x_, 2).unwrap();
                    let d = rubi_coeff(&px_, x_, 3).unwrap();
                    eqq!(c.pow(2) - Atom::num(3) * b * d, 0)
                }
        },
        rhs: {
            let a = rubi_coeff(&px_, x_, 0).unwrap();
            let b = rubi_coeff(&px_, x_, 1).unwrap();
            let c = rubi_coeff(&px_, x_, 2).unwrap();
            let d = rubi_coeff(&px_, x_, 3).unwrap();
            let depressed = rubi_simp(
                &(&a - b.pow(2) / (Atom::num(3) * &c) + &d * x_.pow(3)),
                x_,
            );
            let primitive = rubi_rhs_int(&depressed.pow(&p_), x_);
            rubi_subst(
                &primitive,
                x_,
                c / (Atom::num(3) * d) + x_,
            )
        },
    ));
}

fn push_rules_rule_2479(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; p_, px_);
    rules.push(rubi_rule!(
        order: 2479,
        source: "Int[Px_^p_,x_Symbol] :=
          With[{a=Coeff[Px,x,0],b=Coeff[Px,x,1],c=Coeff[Px,x,2],d=Coeff[Px,x,3]},
          1/(4^p*(c^2-3*b*d)^(3*p)) \\[Star] Int[(c^3-4*b*c*d+9*a*d^2+d*(c^2-3*b*d)*x)^p*(b*c-9*a*d+2*(c^2-3*b*d)*x)^(2*p),x] /;
         EqQ[b^2*c^2-4*a*c^3-4*b^3*d+18*a*b*c*d-27*a^2*d^2,0] && NeQ[c^2-3*b*d,0]] /;
        FreeQ[p,x] && PolyQ[Px,x,3] && IntegerQ[p]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [px_, p_, x_],
        x_free: [p_],
        when: {
            freeq!(p_, x_)
                && rubi_poly_q_degree(&px_, x_, 3)
                && integerq!(p_)
                && {
                    let a = rubi_coeff(&px_, x_, 0).unwrap();
                    let b = rubi_coeff(&px_, x_, 1).unwrap();
                    let c = rubi_coeff(&px_, x_, 2).unwrap();
                    let d = rubi_coeff(&px_, x_, 3).unwrap();
                    let delta = c.pow(2) - Atom::num(3) * &b * &d;
                    let discriminant = b.pow(2) * c.pow(2)
                        - Atom::num(4) * &a * c.pow(3)
                        - Atom::num(4) * b.pow(3) * &d
                        + Atom::num(18) * &a * &b * &c * &d
                        - Atom::num(27) * a.pow(2) * d.pow(2);
                    eqq!(discriminant, 0) && neq!(delta, 0)
                }
        },
        rhs: {
            let a = rubi_coeff(&px_, x_, 0).unwrap();
            let b = rubi_coeff(&px_, x_, 1).unwrap();
            let c = rubi_coeff(&px_, x_, 2).unwrap();
            let d = rubi_coeff(&px_, x_, 3).unwrap();
            let delta = c.pow(2) - Atom::num(3) * &b * &d;
            let first = (c.pow(3) - Atom::num(4) * &b * &c * &d
                + Atom::num(9) * &a * d.pow(2)
                + &d * &delta * x_)
                .pow(&p_);
            let second = (&b * &c - Atom::num(9) * &a * &d
                + Atom::num(2) * &delta * x_)
                .pow(Atom::num(2) * &p_);
            let recursive = rubi_rhs_int(&(&first * &second), x_);
            rubi_star(Atom::num(1) / (Atom::num(4).pow(&p_) * delta.pow(Atom::num(3) * &p_)), recursive)
        },
    ));
}

fn push_rules_rule_2480(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; p_, px_);
    rules.push(rubi_rule!(
        order: 2480,
        source: "Int[Px_^p_,x_Symbol] :=
          With[{a=Coeff[Px,x,0],b=Coeff[Px,x,1],c=Coeff[Px,x,2],d=Coeff[Px,x,3]},
          Px^p/((c^3-4*b*c*d+9*a*d^2+d*(c^2-3*b*d)*x)^p*(b*c-9*a*d+2*(c^2-3*b*d)*x)^(2*p)) \\[Star]
            Int[(c^3-4*b*c*d+9*a*d^2+d*(c^2-3*b*d)*x)^p*(b*c-9*a*d+2*(c^2-3*b*d)*x)^(2*p),x] /;
         EqQ[b^2*c^2-4*a*c^3-4*b^3*d+18*a*b*c*d-27*a^2*d^2,0] && NeQ[c^2-3*b*d,0]] /;
        FreeQ[p,x] && PolyQ[Px,x,3] && Not[IntegerQ[p]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [px_, p_, x_],
        x_free: [p_],
        when: {
            freeq!(p_, x_)
                && rubi_poly_q_degree(&px_, x_, 3)
                && !integerq!(p_)
                && {
                    let a = rubi_coeff(&px_, x_, 0).unwrap();
                    let b = rubi_coeff(&px_, x_, 1).unwrap();
                    let c = rubi_coeff(&px_, x_, 2).unwrap();
                    let d = rubi_coeff(&px_, x_, 3).unwrap();
                    let delta = c.pow(2) - Atom::num(3) * &b * &d;
                    let discriminant = b.pow(2) * c.pow(2)
                        - Atom::num(4) * &a * c.pow(3)
                        - Atom::num(4) * b.pow(3) * &d
                        + Atom::num(18) * &a * &b * &c * &d
                        - Atom::num(27) * a.pow(2) * d.pow(2);
                    eqq!(discriminant, 0) && neq!(delta, 0)
                }
        },
        rhs: {
            let a = rubi_coeff(&px_, x_, 0).unwrap();
            let b = rubi_coeff(&px_, x_, 1).unwrap();
            let c = rubi_coeff(&px_, x_, 2).unwrap();
            let d = rubi_coeff(&px_, x_, 3).unwrap();
            let delta = c.pow(2) - Atom::num(3) * &b * &d;
            let first = (c.pow(3) - Atom::num(4) * &b * &c * &d
                + Atom::num(9) * &a * d.pow(2)
                + &d * &delta * x_)
                .pow(&p_);
            let second = (&b * &c - Atom::num(9) * &a * &d
                + Atom::num(2) * &delta * x_)
                .pow(Atom::num(2) * &p_);
            let recursive = rubi_rhs_int(&(&first * &second), x_);
            rubi_star(px_.pow(&p_) / (first * second), recursive)
        },
    ));
}

fn push_rules_rule_2481(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; p_, px_);
    rules.push(rubi_rule!(
        order: 2481,
        source: "Int[Px_^p_,x_Symbol] :=
          With[{a=Coeff[Px,x,0],b=Coeff[Px,x,1],c=Coeff[Px,x,2],d=Coeff[Px,x,3]},
          Subst[Int[Simp[(2*c^3-9*b*c*d+27*a*d^2)/(27*d^2)-(c^2-3*b*d)*x/(3*d)+d*x^3,x]^p,x],x,c/(3*d)+x]] /;
        FreeQ[p,x] && PolyQ[Px,x,3]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [px_, p_, x_],
        x_free: [p_],
        when: { freeq!(p_, x_) && rubi_poly_q_degree(&px_, x_, 3) },
        rhs: {
            let a = rubi_coeff(&px_, x_, 0).unwrap();
            let b = rubi_coeff(&px_, x_, 1).unwrap();
            let c = rubi_coeff(&px_, x_, 2).unwrap();
            let d = rubi_coeff(&px_, x_, 3).unwrap();
            let depressed = rubi_simp(
                &((Atom::num(2) * c.pow(3) - Atom::num(9) * &b * &c * &d
                    + Atom::num(27) * &a * d.pow(2))
                    / (Atom::num(27) * d.pow(2))
                    - (c.pow(2) - Atom::num(3) * &b * &d) * x_
                        / (Atom::num(3) * &d)
                    + &d * x_.pow(3)),
                x_,
            );
            let primitive = rubi_rhs_int(&depressed.pow(&p_), x_);
            rubi_subst(
                &primitive,
                x_,
                c / (Atom::num(3) * d) + x_,
            )
        },
    ));
}

fn push_rules_rule_2487(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 2487,
        source: "Int[(e_.+f_.*x_)^m_.*(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
          Subst[Int[((3*d*e-c*f)/(3*d)+f*x)^m*Simp[a-b^2/(3*c)+d*x^3,x]^p,x],x,x+c/(3*d)] /;
        FreeQ[{a,b,c,d,e,f,m,p},x] && EqQ[c^2-3*b*d,0]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [e__, f__, m_, a__, b__, c__, d__, p_, x_],
        optional: [e__, f__, m_, a__, b__, c__, d__],
        x_free: [a__, b__, c__, d__, e__, f__, m_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, p_], x_)
                && eqq!(c__.pow(2) - Atom::num(3) * &b__ * &d__, 0)
        },
        rhs: {
            let linear = (Atom::num(3) * &d__ * &e__ - &c__ * &f__)
                / (Atom::num(3) * &d__)
                + &f__ * x_;
            let depressed = rubi_simp(
                &(&a__ - b__.pow(2) / (Atom::num(3) * &c__)
                    + &d__ * x_.pow(3)),
                x_,
            );
            let primitive = rubi_rhs_int(&(linear.pow(&m_) * depressed.pow(&p_)), x_);
            rubi_subst(
                &primitive,
                x_,
                x_ + &c__ / (Atom::num(3) * &d__),
            )
        },
    ));
}

fn push_rules_rule_2488(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 2488,
        source: "Int[(e_.+f_.*x_)^m_.*(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
          1/(4^p*(c^2-3*b*d)^(3*p)) \\[Star] Int[(e+f*x)^m*(c^3-4*b*c*d+9*a*d^2+d*(c^2-3*b*d)*x)^p*(b*c-9*a*d+2*(c^2-3*b*d)*x)^(2*p),x] /;
        FreeQ[{a,b,c,d,e,f,m,p},x] && NeQ[c^2-3*b*d,0] && EqQ[b^2*c^2-4*a*c^3-4*b^3*d+18*a*b*c*d-27*a^2*d^2,0] && ILtQ[p,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [e__, f__, m_, a__, b__, c__, d__, p_, x_],
        optional: [e__, f__, m_, a__, b__, c__, d__],
        x_free: [a__, b__, c__, d__, e__, f__, m_, p_],
        when: {
            let delta = c__.pow(2) - Atom::num(3) * &b__ * &d__;
            let discriminant = b__.pow(2) * c__.pow(2)
                - Atom::num(4) * &a__ * c__.pow(3)
                - Atom::num(4) * b__.pow(3) * &d__
                + Atom::num(18) * &a__ * &b__ * &c__ * &d__
                - Atom::num(27) * a__.pow(2) * d__.pow(2);
            freeq!([a__, b__, c__, d__, e__, f__, m_, p_], x_)
                && neq!(delta, 0)
                && eqq!(discriminant, 0)
                && iltq!(p_, 0)
        },
        rhs: {
            let delta = c__.pow(2) - Atom::num(3) * &b__ * &d__;
            let first = (c__.pow(3) - Atom::num(4) * &b__ * &c__ * &d__
                + Atom::num(9) * &a__ * d__.pow(2)
                + &d__ * &delta * x_)
                .pow(&p_);
            let second = (&b__ * &c__ - Atom::num(9) * &a__ * &d__
                + Atom::num(2) * &delta * x_)
                .pow(Atom::num(2) * &p_);
            let recursive = rubi_rhs_int(
                &((&e__ + &f__ * x_).pow(&m_) * first * second),
                x_,
            );
            rubi_star(Atom::num(1) / (Atom::num(4).pow(&p_) * delta.pow(Atom::num(3) * &p_)), recursive)
        },
    ));
}

fn push_rules_rule_2489(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 2489,
        source: "Int[(e_.+f_.*x_)^m_.*(a_.+b_.*x_+c_.*x_^2+d_.*x_^3)^p_,x_Symbol] :=
          (a+b*x+c*x^2+d*x^3)^p/((c^3-4*b*c*d+9*a*d^2+d*(c^2-3*b*d)*x)^p*(b*c-9*a*d+2*(c^2-3*b*d)*x)^(2*p)) \\[Star]
            Int[(e+f*x)^m*(c^3-4*b*c*d+9*a*d^2+d*(c^2-3*b*d)*x)^p*(b*c-9*a*d+2*(c^2-3*b*d)*x)^(2*p),x] /;
        FreeQ[{a,b,c,d,e,f,m,p},x] && NeQ[c^2-3*b*d,0] && EqQ[b^2*c^2-4*a*c^3-4*b^3*d+18*a*b*c*d-27*a^2*d^2,0] && Not[IntegerQ[p]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [e__, f__, m_, a__, b__, c__, d__, p_, x_],
        optional: [e__, f__, m_, a__, b__, c__, d__],
        x_free: [a__, b__, c__, d__, e__, f__, m_, p_],
        when: {
            let delta = c__.pow(2) - Atom::num(3) * &b__ * &d__;
            let discriminant = b__.pow(2) * c__.pow(2)
                - Atom::num(4) * &a__ * c__.pow(3)
                - Atom::num(4) * b__.pow(3) * &d__
                + Atom::num(18) * &a__ * &b__ * &c__ * &d__
                - Atom::num(27) * a__.pow(2) * d__.pow(2);
            freeq!([a__, b__, c__, d__, e__, f__, m_, p_], x_)
                && neq!(delta, 0)
                && eqq!(discriminant, 0)
                && !integerq!(p_)
        },
        rhs: {
            let delta = c__.pow(2) - Atom::num(3) * &b__ * &d__;
            let cubic = (&a__
                + &b__ * x_
                + &c__ * x_.pow(2)
                + &d__ * x_.pow(3))
                .pow(&p_);
            let first = (c__.pow(3) - Atom::num(4) * &b__ * &c__ * &d__
                + Atom::num(9) * &a__ * d__.pow(2)
                + &d__ * &delta * x_)
                .pow(&p_);
            let second = (&b__ * &c__ - Atom::num(9) * &a__ * &d__
                + Atom::num(2) * &delta * x_)
                .pow(Atom::num(2) * &p_);
            let recursive = rubi_rhs_int(
                &((&e__ + &f__ * x_).pow(&m_) * &first * &second),
                x_,
            );
            rubi_star(cubic / (first * second), recursive)
        },
    ));
}

fn push_rules_rule_2472(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, p_, x_);
    rules.push(rubi_rule!(
        order: 2472,
        source: "Int[(a_.+b_.*x_+d_.*x_^3)^p_,x_Symbol] :=
          1/(3^(3*p)*a^(2*p)) \\[Star] Int[(3*a-b*x)^p*(3*a+2*b*x)^(2*p),x] /;
        FreeQ[{a,b,d},x] && EqQ[4*b^3+27*a^2*d,0] && IntegerQ[p]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, d__, p_, x_],
        optional: [a__, b__, d__],
        when: {
            freeq!([a__, b__, d__], x_)
                && eqq!(
                    Atom::num(4) * b__.pow(3) + Atom::num(27) * a__.pow(2) * &d__,
                    0
                )
                && integerq!(p_)
        },
        rhs: {
            let integrand = (Atom::num(3) * &a__ - &b__ * x_).pow(&p_)
                * (Atom::num(3) * &a__ + Atom::num(2) * &b__ * x_).pow(Atom::num(2) * &p_);
            let recursive = rubi_rhs_int(&integrand, x_);

            rubi_star(Atom::num(1) / (Atom::num(3).pow(Atom::num(3) * &p_)
                        * a__.pow(Atom::num(2) * &p_)), recursive)
        },
    ));
}

fn push_rules_rule_2473(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, p_, x_);
    rules.push(rubi_rule!(
        order: 2473,
        source: "Int[(a_.+b_.*x_+d_.*x_^3)^p_,x_Symbol] :=
          (a+b*x+d*x^3)^p/((3*a-b*x)^p*(3*a+2*b*x)^(2*p)) \\[Star] Int[(3*a-b*x)^p*(3*a+2*b*x)^(2*p),x] /;
        FreeQ[{a,b,d,p},x] && EqQ[4*b^3+27*a^2*d,0] && Not[IntegerQ[p]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, d__, p_, x_],
        optional: [a__, b__, d__],
        when: {
            freeq!([a__, b__, d__, p_], x_)
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
            let integrand = first.pow(&p_) * second.pow(Atom::num(2) * &p_);
            let recursive = rubi_rhs_int(&integrand, x_);
            rubi_star(cubic.pow(&p_), recursive / denominator)
        },
    ));
}

fn push_rules_rule_2474(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, p_, x_);
    rules.push(rubi_rule!(
        order: 2474,
        source: "Int[(a_.+b_.*x_+d_.*x_^3)^p_,x_Symbol] :=
          With[{r=Rt[-9*a*d^2+Sqrt[3]*d*Sqrt[4*b^3*d+27*a^2*d^2],3]},
          1/d^(2*p) \\[Star] Int[Simp[18^(1/3)*b*d/(3*r)-r/18^(1/3)+d*x,x]^p*
            Simp[b*d/3+12^(1/3)*b^2*d^2/(3*r^2)+r^2/(3*12^(1/3))-d*(2^(1/3)*b*d/(3^(1/3)*r)-r/18^(1/3))*x+d^2*x^2,x]^p,x]] /;
        FreeQ[{a,b,d},x] && NeQ[4*b^3+27*a^2*d,0] && IntegerQ[p]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, d__, p_, x_],
        optional: [a__, b__, d__],
        when: {
            freeq!([a__, b__, d__], x_)
                && neq!(
                    Atom::num(4) * b__.pow(3) + Atom::num(27) * a__.pow(2) * &d__,
                    0
                )
                && integerq!(p_)
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
            let integrand = simp1.pow(&p_) * simp2.pow(&p_);
            let recursive = rubi_rhs_int(&integrand, x_);

            rubi_star(Atom::num(1) / d__.pow(Atom::num(2) * &p_), recursive)
        },
    ));
}

fn push_rules_rule_2475(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, p_, x_);
    rules.push(rubi_rule!(
        order: 2475,
        source: "Int[(a_.+b_.*x_+d_.*x_^3)^p_,x_Symbol] :=
          With[{r=Rt[-9*a*d^2+Sqrt[3]*d*Sqrt[4*b^3*d+27*a^2*d^2],3]},
          (a+b*x+d*x^3)^p/
            (Simp[18^(1/3)*b*d/(3*r)-r/18^(1/3)+d*x,x]^p*
              Simp[b*d/3+12^(1/3)*b^2*d^2/(3*r^2)+r^2/(3*12^(1/3))-d*(2^(1/3)*b*d/(3^(1/3)*r)-r/18^(1/3))*x+d^2*x^2,x]^p) \\[Star]
            Int[Simp[18^(1/3)*b*d/(3*r)-r/18^(1/3)+d*x,x]^p*
              Simp[b*d/3+12^(1/3)*b^2*d^2/(3*r^2)+r^2/(3*12^(1/3))-d*(2^(1/3)*b*d/(3^(1/3)*r)-r/18^(1/3))*x+d^2*x^2,x]^p,x]] /;
        FreeQ[{a,b,d,p},x] && NeQ[4*b^3+27*a^2*d,0] && Not[IntegerQ[p]]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, d__, p_, x_],
        optional: [a__, b__, d__],
        when: {
            freeq!([a__, b__, d__, p_], x_)
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
            let denominator = simp1.pow(&p_) * simp2.pow(&p_);
            let integrand = simp1.pow(&p_) * simp2.pow(&p_);
            let recursive = rubi_rhs_int(&integrand, x_);
            rubi_star(cubic.pow(&p_), recursive / denominator)
        },
    ));
}

fn push_rules_rule_2490(rules: &mut Vec<RubiRule>) {
    rubi_symb!(e__, f__, m_, p_, p3__, x_);
    rules.push(rubi_rule!(
        order: 2490,
        source: "Int[(e_.+f_.*x_)^m_.*P3_^p_.,x_Symbol] :=
          With[{a=Coeff[P3,x,0],b=Coeff[P3,x,1],c=Coeff[P3,x,2],d=Coeff[P3,x,3]},
          Subst[Int[((3*d*e-c*f)/(3*d)+f*x)^m*Simp[(2*c^3-9*b*c*d+27*a*d^2)/(27*d^2)-(c^2-3*b*d)*x/(3*d)+d*x^3,x]^p,x],x,x+c/(3*d)] /;
         NeQ[c,0]] /;
        FreeQ[{e,f,m,p},x] && PolyQ[P3,x,3]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (e__ + f__ * x_).pow(m_) * p3__.pow(p_),
        with: [e__, f__, m_, p3__, p_, x_],
        optional: [e__, f__, m_, p_],
        when: {
            freeq!([e__, f__, m_, p_], x_)
                && rubi_poly_q_degree(&p3__, x_, 3)
                && neq!(rubi_coeff(&p3__, x_, 2).unwrap(), 0)
        },
        rhs: {
            let a = rubi_coeff(&p3__, x_, 0).unwrap();
            let b = rubi_coeff(&p3__, x_, 1).unwrap();
            let c = rubi_coeff(&p3__, x_, 2).unwrap();
            let d = rubi_coeff(&p3__, x_, 3).unwrap();

            let linear = ((Atom::num(3) * &d * &e__ - &c * &f__) / (Atom::num(3) * &d)
                + &f__ * x_)
                .pow(&m_);
            let simp = rubi_simp(
                &((Atom::num(2) * c.pow(3)
                    - Atom::num(9) * &b * &c * &d
                    + Atom::num(27) * &a * d.pow(2))
                    / (Atom::num(27) * d.pow(2))
                    - (c.pow(2) - Atom::num(3) * &b * &d) * x_ / (Atom::num(3) * &d)
                    + &d * x_.pow(3)),
                x_,
            );
            let transformed = rubi_rhs_int(&(linear * simp.pow(&p_)), x_);

            rubi_subst(
                &transformed,
                x_,
                x_ + &c / (Atom::num(3) * &d),
            )
        },
    ));
}

// Generated shared pattern builders.

#[inline(never)]
fn rubi_shared_pattern_0(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let d__ = symbols.d__;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (a__ + b__ * x_ + d__ * x_.pow(3)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (e__ + f__ * x_).pow(m_) * (a__ + b__ * x_ + c__ * x_.pow(2) + d__ * x_.pow(3)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_2(symbols: &RubiSymbols) -> Atom {
    let p_ = symbols.p_;
    let px_ = symbols.px_;
    px_.pow(p_)
}
