use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_2262(rules);
    push_rules_rule_2263(rules);
    push_rules_rule_2264(rules);
    push_rules_rule_2265(rules);
    push_rules_rule_2266(rules);
    push_rules_rule_2267(rules);
    push_rules_rule_2268(rules);
    push_rules_rule_2269(rules);
    push_rules_rule_2270(rules);
    push_rules_rule_2271(rules);
    push_rules_rule_2272(rules);
    push_rules_rule_2273(rules);
    push_rules_rule_2274(rules);
    push_rules_rule_2275(rules);
    push_rules_rule_2276(rules);
    push_rules_rule_2277(rules);
    push_rules_rule_2278(rules);
    push_rules_rule_2279(rules);
    push_rules_rule_2280(rules);
    push_rules_rule_2281(rules);
    push_rules_rule_2282(rules);
}

fn push_rules_rule_2262(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 2262,
        source: "Int[1/((d_+e_.*x_)*Sqrt[a_+b_.*x_^2+c_.*x_^4]),x_Symbol] :=
          d \\[Star] Int[1/((d^2-e^2*x^2)*Sqrt[a+b*x^2+c*x^4]),x] - e \\[Star] Int[x/((d^2-e^2*x^2)*Sqrt[a+b*x^2+c*x^4]),x] /;
        FreeQ[{a,b,c,d,e},x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: Atom::num(1) / ((d__ + e__ * x_) * (a__ + b__ * x_.pow(2) + c__ * x_.pow(4)).sqrt()),
        with: [d__, e__, a__, b__, c__, x_],
        optional: [e__, b__, c__],
        when: { freeq!([a__, b__, c__, d__, e__], x_) },
        rhs: {
            let denominator = d__.pow(2) - e__.pow(2) * x_.pow(2);
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let first = rubi_rhs_int(&(Atom::num(1) / (&denominator * quartic.sqrt())), x_);
            let second = rubi_rhs_int(&(x_ / (denominator * quartic.sqrt())), x_);

            rubi_star(d__, first) - rubi_star(e__, second)
        },
    ));
}

fn push_rules_rule_2263(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 2263,
        source: "Int[1/((d_+e_.*x_)*Sqrt[a_+c_.*x_^4]),x_Symbol] :=
          d \\[Star] Int[1/((d^2-e^2*x^2)*Sqrt[a+c*x^4]),x] - e \\[Star] Int[x/((d^2-e^2*x^2)*Sqrt[a+c*x^4]),x] /;
        FreeQ[{a,c,d,e},x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: Atom::num(1) / ((d__ + e__ * x_) * (a__ + c__ * x_.pow(4)).sqrt()),
        with: [d__, e__, a__, c__, x_],
        optional: [e__, c__],
        when: { freeq!([a__, c__, d__, e__], x_) },
        rhs: {
            let denominator = d__.pow(2) - e__.pow(2) * x_.pow(2);
            let quartic = &a__ + &c__ * x_.pow(4);
            let first = rubi_rhs_int(&(Atom::num(1) / (&denominator * quartic.sqrt())), x_);
            let second = rubi_rhs_int(&(x_ / (denominator * quartic.sqrt())), x_);

            rubi_star(d__, first) - rubi_star(e__, second)
        },
    ));
}

fn push_rules_rule_2264(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, q_, x_);
    rules.push(rubi_rule!(
        order: 2264,
        source: "Int[(d_+e_.*x_)^q_/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
          e^3*(d+e*x)^(q+1)*Sqrt[a+b*x^2+c*x^4]/((q+1)*(c*d^4+b*d^2*e^2+a*e^4)) +
          1/((q+1)*(c*d^4+b*d^2*e^2+a*e^4)) \\[Star]
            Int[(d+e*x)^(q+1)/Sqrt[a+b*x^2+c*x^4]*
              Simp[d*(q+1)*(c*d^2+b*e^2)-e*(c*d^2*(q+1)+b*e^2*(q+2))*x+c*d*e^2*(q+1)*x^2-c*e^3*(q+3)*x^3,x],x] /;
        FreeQ[{a,b,c,d,e},x] && NeQ[c*d^4+b*d^2*e^2+a*e^4,0] && ILtQ[q,-1]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (d__ + e__ * x_).pow(q_) / (a__ + b__ * x_.pow(2) + c__ * x_.pow(4)).sqrt(),
        with: [d__, e__, q_, a__, b__, c__, x_],
        optional: [e__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && neq!(&c__ * d__.pow(4) + &b__ * d__.pow(2) * e__.pow(2) + &a__ * e__.pow(4), 0)
                && iltq!(q_, -1)
        },
        rhs: {
            let affine = &d__ + &e__ * x_;
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let invariant = &c__ * d__.pow(4) + &b__ * d__.pow(2) * e__.pow(2) + &a__ * e__.pow(4);
            let q1 = &q_ + Atom::num(1);
            let denominator = &q1 * &invariant;

            let direct = e__.pow(3) * affine.pow(&q1) * quartic.sqrt() / &denominator;
            let simp = rubi_simp(
                &(&d__ * &q1 * (&c__ * d__.pow(2) + &b__ * e__.pow(2))
                    - &e__
                        * (&c__ * d__.pow(2) * &q1 + &b__ * e__.pow(2) * (&q_ + Atom::num(2)))
                        * x_
                    + &c__ * &d__ * e__.pow(2) * &q1 * x_.pow(2)
                    - &c__ * e__.pow(3) * (&q_ + Atom::num(3)) * x_.pow(3)),
                x_,
            );
            let recursive_integrand = affine.pow(q1) * simp / quartic.sqrt();
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_2265(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, c__, d__, e__, q_, x_);
    rules.push(rubi_rule!(
        order: 2265,
        source: "Int[(d_+e_.*x_)^q_/Sqrt[a_+c_.*x_^4],x_Symbol] :=
          e^3*(d+e*x)^(q+1)*Sqrt[a+c*x^4]/((q+1)*(c*d^4+a*e^4)) +
          c/((q+1)*(c*d^4+a*e^4)) \\[Star]
            Int[(d+e*x)^(q+1)/Sqrt[a+c*x^4]*Simp[d^3*(q+1)-d^2*e*(q+1)*x+d*e^2*(q+1)*x^2-e^3*(q+3)*x^3,x],x] /;
        FreeQ[{a,c,d,e},x] && NeQ[c*d^4+a*e^4,0] && ILtQ[q,-1]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (d__ + e__ * x_).pow(q_) / (a__ + c__ * x_.pow(4)).sqrt(),
        with: [d__, e__, q_, a__, c__, x_],
        optional: [e__, c__],
        when: {
            freeq!([a__, c__, d__, e__], x_)
                && neq!(&c__ * d__.pow(4) + &a__ * e__.pow(4), 0)
                && iltq!(q_, -1)
        },
        rhs: {
            let affine = &d__ + &e__ * x_;
            let quartic = &a__ + &c__ * x_.pow(4);
            let invariant = &c__ * d__.pow(4) + &a__ * e__.pow(4);
            let q1 = &q_ + Atom::num(1);
            let denominator = &q1 * &invariant;

            let direct = e__.pow(3) * affine.pow(&q1) * quartic.sqrt() / &denominator;
            let simp = rubi_simp(
                &(&d__.pow(3) * &q1
                    - d__.pow(2) * &e__ * &q1 * x_
                    + &d__ * e__.pow(2) * &q1 * x_.pow(2)
                    - e__.pow(3) * (&q_ + Atom::num(3)) * x_.pow(3)),
                x_,
            );
            let recursive_integrand = affine.pow(q1) * simp / quartic.sqrt();
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) + rubi_star(c__, recursive / denominator)
        },
    ));
}

fn push_rules_rule_2266(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, p_, x_);
    rules.push(rubi_rule!(
        order: 2266,
        source: "Int[(a_+b_.*x_^2+c_.*x_^4)^p_./(d_+e_.*x_),x_Symbol] :=
          d \\[Star] Int[(a+b*x^2+c*x^4)^p/(d^2-e^2*x^2),x] - e \\[Star] Int[x*(a+b*x^2+c*x^4)^p/(d^2-e^2*x^2),x] /;
        FreeQ[{a,b,c,d,e},x] && IntegerQ[p+1/2]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (a__ + b__ * x_.pow(2) + c__ * x_.pow(4)).pow(p_) / (d__ + e__ * x_),
        with: [a__, b__, c__, p_, d__, e__, x_],
        optional: [b__, c__, p_, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && integerq!(&p_ + Atom::num(1) / Atom::num(2))
        },
        rhs: {
            let denominator = d__.pow(2) - e__.pow(2) * x_.pow(2);
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let first = rubi_rhs_int(&(quartic.pow(&p_) / &denominator), x_);
            let second = rubi_rhs_int(&(x_ * quartic.pow(&p_) / denominator), x_);

            rubi_star(d__, first) - rubi_star(e__, second)
        },
    ));
}

fn push_rules_rule_2267(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, c__, d__, e__, p_, x_);
    rules.push(rubi_rule!(
        order: 2267,
        source: "Int[(a_+c_.*x_^4)^p_./(d_+e_.*x_),x_Symbol] :=
          d \\[Star] Int[(a+c*x^4)^p/(d^2-e^2*x^2),x] - e \\[Star] Int[x*(a+c*x^4)^p/(d^2-e^2*x^2),x] /;
        FreeQ[{a,c,d,e},x] && IntegerQ[p+1/2]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (a__ + c__ * x_.pow(4)).pow(p_) / (d__ + e__ * x_),
        with: [a__, c__, p_, d__, e__, x_],
        optional: [c__, p_, e__],
        when: {
            freeq!([a__, c__, d__, e__], x_)
                && integerq!(&p_ + Atom::num(1) / Atom::num(2))
        },
        rhs: {
            let denominator = d__.pow(2) - e__.pow(2) * x_.pow(2);
            let quartic = &a__ + &c__ * x_.pow(4);
            let first = rubi_rhs_int(&(quartic.pow(&p_) / &denominator), x_);
            let second = rubi_rhs_int(&(x_ * quartic.pow(&p_) / denominator), x_);

            rubi_star(d__, first) - rubi_star(e__, second)
        },
    ));
}

fn push_rules_rule_2268(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, p_, px__, q_, x_);
    rules.push(rubi_rule!(
        order: 2268,
        source: "Int[Px_*(d_+e_.*x_)^q_.*(a_+b_.*x_^2+c_.*x_^4)^p_.,x_Symbol] :=
          Int[PolynomialQuotient[Px,d+e*x,x]*(d+e*x)^(q+1)*(a+b*x^2+c*x^4)^p,x] /;
        FreeQ[{a,b,c,d,e,p,q},x] && PolyQ[Px,x] && EqQ[PolynomialRemainder[Px,d+e*x,x],0]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [px__, d__, e__, q_, a__, b__, c__, p_, x_],
        optional: [e__, q_, b__, c__, p_],
        when: {
            let divisor = &d__ + &e__ * x_;
            freeq!([a__, b__, c__, d__, e__, p_, q_], x_)
                && rubi_poly_q(&px__, x_)
                && rubi_polynomial_remainder(&px__, &divisor, x_)
                    .is_some_and(|remainder| eqq!(remainder, 0))
        },
        rhs: {
            let affine = &d__ + &e__ * x_;
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let quotient = rubi_polynomial_quotient(&px__, &affine, x_).rubi_rhs();
            let recursive_integrand = quotient * affine.pow(&q_ + Atom::num(1)) * quartic.pow(&p_);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_2269(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, p_, px__, q_, x_);
    rules.push(rubi_rule!(
        order: 2269,
        source: "Int[Px_*(d_+e_.*x_)^q_.*(a_+c_.*x_^4)^p_.,x_Symbol] :=
          Int[PolynomialQuotient[Px,d+e*x,x]*(d+e*x)^(q+1)*(a+c*x^4)^p,x] /;
        FreeQ[{a,c,d,e,p,q},x] && PolyQ[Px,x] && EqQ[PolynomialRemainder[Px,d+e*x,x],0]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [px__, d__, e__, q_, a__, c__, p_, x_],
        optional: [e__, q_, c__, p_],
        when: {
            let divisor = &d__ + &e__ * x_;
            freeq!([a__, c__, d__, e__, p_, q_], x_)
                && rubi_poly_q(&px__, x_)
                && rubi_polynomial_remainder(&px__, &divisor, x_)
                    .is_some_and(|remainder| eqq!(remainder, 0))
        },
        rhs: {
            let affine = &d__ + &e__ * x_;
            let quartic = &a__ + &c__ * x_.pow(4);
            let quotient = rubi_polynomial_quotient(&px__, &affine, x_).rubi_rhs();
            let recursive_integrand = quotient * affine.pow(&q_ + Atom::num(1)) * quartic.pow(&p_);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_2270(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, p_, px__, q_, x_);
    rules.push(rubi_rule!(
        order: 2270,
        source: "Int[Px_*(d_+e_.*x_)^q_.*(a_+b_.*x_^2+c_.*x_^4)^p_.,x_Symbol] :=
          Int[PolynomialQuotient[Px,a+b*x^2+c*x^4,x]*(d+e*x)^q*(a+b*x^2+c*x^4)^(p+1),x] /;
        FreeQ[{a,b,c,d,e,p,q},x] && PolyQ[Px,x] && EqQ[PolynomialRemainder[Px,a+b*x^2+c*x^4,x],0]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [px__, d__, e__, q_, a__, b__, c__, p_, x_],
        optional: [e__, q_, b__, c__, p_],
        when: {
            let divisor = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            freeq!([a__, b__, c__, d__, e__, p_, q_], x_)
                && rubi_poly_q(&px__, x_)
                && rubi_polynomial_remainder(&px__, &divisor, x_)
                    .is_some_and(|remainder| eqq!(remainder, 0))
        },
        rhs: {
            let affine = &d__ + &e__ * x_;
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let quotient = rubi_polynomial_quotient(&px__, &quartic, x_).rubi_rhs();
            let recursive_integrand = quotient * affine.pow(&q_) * quartic.pow(&p_ + Atom::num(1));

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_2271(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, p_, px__, q_, x_);
    rules.push(rubi_rule!(
        order: 2271,
        source: "Int[Px_*(d_+e_.*x_)^q_.*(a_+c_.*x_^4)^p_.,x_Symbol] :=
          Int[PolynomialQuotient[Px,a+c*x^4,x]*(d+e*x)^q*(a+c*x^4)^(p+1),x] /;
        FreeQ[{a,c,d,e,p,q},x] && PolyQ[Px,x] && EqQ[PolynomialRemainder[Px,a+c*x^4,x],0]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [px__, d__, e__, q_, a__, c__, p_, x_],
        optional: [e__, q_, c__, p_],
        when: {
            let divisor = &a__ + &c__ * x_.pow(4);
            freeq!([a__, c__, d__, e__, p_, q_], x_)
                && rubi_poly_q(&px__, x_)
                && rubi_polynomial_remainder(&px__, &divisor, x_)
                    .is_some_and(|remainder| eqq!(remainder, 0))
        },
        rhs: {
            let affine = &d__ + &e__ * x_;
            let quartic = &a__ + &c__ * x_.pow(4);
            let quotient = rubi_polynomial_quotient(&px__, &quartic, x_).rubi_rhs();
            let recursive_integrand = quotient * affine.pow(&q_) * quartic.pow(&p_ + Atom::num(1));

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_2272(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, px__, q_, x_);
    rules.push(rubi_rule!(
        order: 2272,
        source: "Int[Px_*(d_+e_.*x_)^q_/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
          With[{A=Coeff[Px,x,0],B=Coeff[Px,x,1],C=Coeff[Px,x,2],D=Coeff[Px,x,3]},
          Int[(d+e*x)^(q-1)*(A*d+(B*d+A*e)*x+(C*d+B*e)*x^2+C*e*x^3)/Sqrt[a+b*x^2+c*x^4],x]] /;
        FreeQ[{a,b,c,d,e},x] && PolyQ[Px,x] && LeQ[Expon[Px,x],2] && NeQ[c*d^4+b*d^2*e^2+a*e^4,0] && GtQ[q,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [px__, d__, e__, q_, a__, b__, c__, x_],
        optional: [e__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && rubi_poly_q(&px__, x_)
                && rubi_expon(&px__, x_).is_some_and(|exponent| leq!(Atom::num(exponent), 2))
                && neq!(&c__ * d__.pow(4) + &b__ * d__.pow(2) * e__.pow(2) + &a__ * e__.pow(4), 0)
                && gtq!(q_, 0)
        },
        rhs: {
            let A = rubi_coeff(&px__, x_, 0).rubi_rhs();
            let B = rubi_coeff(&px__, x_, 1).rubi_rhs();
            let C = rubi_coeff(&px__, x_, 2).rubi_rhs();
            let affine = &d__ + &e__ * x_;
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let payload = &A * &d__
                + (&B * &d__ + &A * &e__) * x_
                + (&C * &d__ + &B * &e__) * x_.pow(2)
                + &C * &e__ * x_.pow(3);
            let recursive_integrand = affine.pow(&q_ - Atom::num(1)) * payload / quartic.sqrt();

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_2273(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, px__, q_, x_);
    rules.push(rubi_rule!(
        order: 2273,
        source: "Int[Px_*(d_+e_.*x_)^q_/Sqrt[a_+c_.*x_^4],x_Symbol] :=
          With[{A=Coeff[Px,x,0],B=Coeff[Px,x,1],C=Coeff[Px,x,2],D=Coeff[Px,x,3]},
          Int[(d+e*x)^(q-1)*(A*d+(B*d+A*e)*x+(C*d+B*e)*x^2+C*e*x^3)/Sqrt[a+c*x^4],x]] /;
        FreeQ[{a,c,d,e},x] && PolyQ[Px,x] && LeQ[Expon[Px,x],2] && NeQ[c*d^4+a*e^4,0] && GtQ[q,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [px__, d__, e__, q_, a__, c__, x_],
        optional: [e__, c__],
        when: {
            freeq!([a__, c__, d__, e__], x_)
                && rubi_poly_q(&px__, x_)
                && rubi_expon(&px__, x_).is_some_and(|exponent| leq!(Atom::num(exponent), 2))
                && neq!(&c__ * d__.pow(4) + &a__ * e__.pow(4), 0)
                && gtq!(q_, 0)
        },
        rhs: {
            let A = rubi_coeff(&px__, x_, 0).rubi_rhs();
            let B = rubi_coeff(&px__, x_, 1).rubi_rhs();
            let C = rubi_coeff(&px__, x_, 2).rubi_rhs();
            let affine = &d__ + &e__ * x_;
            let quartic = &a__ + &c__ * x_.pow(4);
            let payload = &A * &d__
                + (&B * &d__ + &A * &e__) * x_
                + (&C * &d__ + &B * &e__) * x_.pow(2)
                + &C * &e__ * x_.pow(3);
            let recursive_integrand = affine.pow(&q_ - Atom::num(1)) * payload / quartic.sqrt();

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_2274(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, px__, q_, x_);
    rules.push(rubi_rule!(
        order: 2274,
        source: "Int[Px_*(d_+e_.*x_)^q_/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
          With[{A=Coeff[Px,x,0],B=Coeff[Px,x,1],C=Coeff[Px,x,2],D=Coeff[Px,x,3]},
          D*(d+e*x)^q*Sqrt[a+b*x^2+c*x^4]/(c*(q+2)) -
          1/(c*(q+2)) \\[Star] Int[(d+e*x)^(q-1)/Sqrt[a+b*x^2+c*x^4]*
            Simp[a*D*e*q-A*c*d*(q+2)+(b*d*D-B*c*d*(q+2)-A*c*e*(q+2))*x+
              (b*D*e*(q+1)-c*(C*d+B*e)*(q+2))*x^2-c*(d*D*q+C*e*(q+2))*x^3,x],x]] /;
        FreeQ[{a,b,c,d,e},x] && PolyQ[Px,x,3] && NeQ[c*d^4+b*d^2*e^2+a*e^4,0] && GtQ[q,0]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [px__, d__, e__, q_, a__, b__, c__, x_],
        optional: [e__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && rubi_poly_q_degree(&px__, x_, 3)
                && neq!(&c__ * d__.pow(4) + &b__ * d__.pow(2) * e__.pow(2) + &a__ * e__.pow(4), 0)
                && gtq!(q_, 0)
        },
        rhs: {
            let A = rubi_coeff(&px__, x_, 0).rubi_rhs();
            let B = rubi_coeff(&px__, x_, 1).rubi_rhs();
            let C = rubi_coeff(&px__, x_, 2).rubi_rhs();
            let D = rubi_coeff(&px__, x_, 3).rubi_rhs();
            let affine = &d__ + &e__ * x_;
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let denominator = &c__ * (&q_ + Atom::num(2));
            let direct = &D * affine.pow(&q_) * quartic.sqrt() / &denominator;
            let simp = rubi_simp(
                &(&a__ * &D * &e__ * &q_ - &A * &c__ * &d__ * (&q_ + Atom::num(2))
                    + (&b__ * &d__ * &D
                        - &B * &c__ * &d__ * (&q_ + Atom::num(2))
                        - &A * &c__ * &e__ * (&q_ + Atom::num(2)))
                        * x_
                    + (&b__ * &D * &e__ * (&q_ + Atom::num(1))
                        - &c__ * (&C * &d__ + &B * &e__) * (&q_ + Atom::num(2)))
                        * x_.pow(2)
                    - &c__ * (&d__ * &D * &q_ + &C * &e__ * (&q_ + Atom::num(2)))
                        * x_.pow(3)),
                x_,
            );
            let recursive_integrand = affine.pow(&q_ - Atom::num(1)) * simp / quartic.sqrt();
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) - rubi_star(Atom::num(1) / &denominator, recursive)
        },
    ));
}

fn push_rules_rule_2275(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, px__, q_, x_);
    rules.push(rubi_rule!(
        order: 2275,
        source: "Int[Px_*(d_+e_.*x_)^q_/Sqrt[a_+c_.*x_^4],x_Symbol] :=
          With[{A=Coeff[Px,x,0],B=Coeff[Px,x,1],C=Coeff[Px,x,2],D=Coeff[Px,x,3]},
          D*(d+e*x)^q*Sqrt[a+c*x^4]/(c*(q+2)) -
          1/(c*(q+2)) \\[Star] Int[(d+e*x)^(q-1)/Sqrt[a+c*x^4]*
            Simp[a*D*e*q-A*c*d*(q+2)-c*(B*d*(q+2)+A*e*(q+2))*x-c*(C*d+B*e)*(q+2)*x^2-c*(d*D*q+C*e*(q+2))*x^3,x],x]] /;
        FreeQ[{a,c,d,e},x] && PolyQ[Px,x,3] && NeQ[c*d^4+a*e^4,0] && GtQ[q,0]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [px__, d__, e__, q_, a__, c__, x_],
        optional: [e__, c__],
        when: {
            freeq!([a__, c__, d__, e__], x_)
                && rubi_poly_q_degree(&px__, x_, 3)
                && neq!(&c__ * d__.pow(4) + &a__ * e__.pow(4), 0)
                && gtq!(q_, 0)
        },
        rhs: {
            let A = rubi_coeff(&px__, x_, 0).rubi_rhs();
            let B = rubi_coeff(&px__, x_, 1).rubi_rhs();
            let C = rubi_coeff(&px__, x_, 2).rubi_rhs();
            let D = rubi_coeff(&px__, x_, 3).rubi_rhs();
            let affine = &d__ + &e__ * x_;
            let quartic = &a__ + &c__ * x_.pow(4);
            let denominator = &c__ * (&q_ + Atom::num(2));
            let direct = &D * affine.pow(&q_) * quartic.sqrt() / &denominator;
            let simp = rubi_simp(
                &(&a__ * &D * &e__ * &q_
                    - &A * &c__ * &d__ * (&q_ + Atom::num(2))
                    - &c__ * (&B * &d__ * (&q_ + Atom::num(2)) + &A * &e__ * (&q_ + Atom::num(2)))
                        * x_
                    - &c__ * (&C * &d__ + &B * &e__) * (&q_ + Atom::num(2)) * x_.pow(2)
                    - &c__ * (&d__ * &D * &q_ + &C * &e__ * (&q_ + Atom::num(2)))
                        * x_.pow(3)),
                x_,
            );
            let recursive_integrand = affine.pow(&q_ - Atom::num(1)) * simp / quartic.sqrt();
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) - rubi_star(Atom::num(1) / &denominator, recursive)
        },
    ));
}

fn push_rules_rule_2276(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, px__, q_, x_);
    rules.push(rubi_rule!(
        order: 2276,
        source: "Int[Px_*(d_+e_.*x_)^q_/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
          With[{A=Coeff[Px,x,0],B=Coeff[Px,x,1],C=Coeff[Px,x,2],D=Coeff[Px,x,3]},
          -(d^3*D-C*d^2*e+B*d*e^2-A*e^3)*(d+e*x)^(q+1)*Sqrt[a+b*x^2+c*x^4]/((q+1)*(c*d^4+b*d^2*e^2+a*e^4)) +
          1/((q+1)*(c*d^4+b*d^2*e^2+a*e^4)) \\[Star]
            Int[((d+e*x)^(q+1)/Sqrt[a+b*x^2+c*x^4])*
              Simp[(q+1)*(a*e*(d^2*D-C*d*e+B*e^2)+A*d*(c*d^2+b*e^2)) -
                (e*(q+1)*(A*c*d^2+a*e*(d*D-C*e))-B*d*(c*d^2*(q+1)+b*e^2*(q+2))-b*(d^3*D-C*d^2*e-A*e^3*(q+2)))*x +
                (q+1)*(D*e*(b*d^2+a*e^2)+c*d*(C*d^2-e*(B*d-A*e)))*x^2 +
                c*(q+3)*(d^3*D-C*d^2*e+B*d*e^2-A*e^3)*x^3,x],x]] /;
        FreeQ[{a,b,c,d,e},x] && PolyQ[Px,x] && LeQ[Expon[Px,x],3] && NeQ[c*d^4+b*d^2*e^2+a*e^4,0] && LtQ[q,-1]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [px__, d__, e__, q_, a__, b__, c__, x_],
        optional: [e__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && rubi_poly_q(&px__, x_)
                && rubi_expon(&px__, x_).is_some_and(|exponent| leq!(Atom::num(exponent), 3))
                && neq!(&c__ * d__.pow(4) + &b__ * d__.pow(2) * e__.pow(2) + &a__ * e__.pow(4), 0)
                && ltq!(q_, -1)
        },
        rhs: {
            let A = rubi_coeff(&px__, x_, 0).rubi_rhs();
            let B = rubi_coeff(&px__, x_, 1).rubi_rhs();
            let C = rubi_coeff(&px__, x_, 2).rubi_rhs();
            let D = rubi_coeff(&px__, x_, 3).rubi_rhs();
            let affine = &d__ + &e__ * x_;
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let invariant = &c__ * d__.pow(4) + &b__ * d__.pow(2) * e__.pow(2) + &a__ * e__.pow(4);
            let q1 = &q_ + Atom::num(1);
            let denominator = &q1 * &invariant;
            let leading =
                d__.pow(3) * &D - &C * d__.pow(2) * &e__ + &B * &d__ * e__.pow(2) - &A * e__.pow(3);
            let direct = -&leading * affine.pow(&q1) * quartic.sqrt() / &denominator;
            let simp = rubi_simp(
                &(&q1
                    * (&a__ * &e__ * (d__.pow(2) * &D - &C * &d__ * &e__ + &B * e__.pow(2))
                        + &A * &d__ * (&c__ * d__.pow(2) + &b__ * e__.pow(2)))
                    - (&e__
                        * &q1
                        * (&A * &c__ * d__.pow(2) + &a__ * &e__ * (&d__ * &D - &C * &e__))
                        - &B
                            * &d__
                            * (&c__ * d__.pow(2) * &q1
                                + &b__ * e__.pow(2) * (&q_ + Atom::num(2)))
                        - &b__
                            * (d__.pow(3) * &D
                                - &C * d__.pow(2) * &e__
                                - &A * e__.pow(3) * (&q_ + Atom::num(2))))
                        * x_
                    + &q1
                        * (&D * &e__ * (&b__ * d__.pow(2) + &a__ * e__.pow(2))
                            + &c__
                                * &d__
                                * (&C * d__.pow(2) - &e__ * (&B * &d__ - &A * &e__)))
                        * x_.pow(2)
                    + &c__ * (&q_ + Atom::num(3)) * &leading * x_.pow(3)),
                x_,
            );
            let recursive_integrand = affine.pow(q1) * simp / quartic.sqrt();
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / &denominator, recursive)
        },
    ));
}

fn push_rules_rule_2277(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, px__, q_, x_);
    rules.push(rubi_rule!(
        order: 2277,
        source: "Int[Px_*(d_+e_.*x_)^q_/Sqrt[a_+c_.*x_^4],x_Symbol] :=
          With[{A=Coeff[Px,x,0],B=Coeff[Px,x,1],C=Coeff[Px,x,2],D=Coeff[Px,x,3]},
          -(d^3*D-C*d^2*e+B*d*e^2-A*e^3)*(d+e*x)^(q+1)*Sqrt[a+c*x^4]/((q+1)*(c*d^4+a*e^4)) +
          1/((q+1)*(c*d^4+a*e^4)) \\[Star]
            Int[((d+e*x)^(q+1)/Sqrt[a+c*x^4])*
              Simp[(q+1)*(a*e*(d^2*D-C*d*e+B*e^2)+A*d*(c*d^2)) -
                (e*(q+1)*(A*c*d^2+a*e*(d*D-C*e))-B*d*(c*d^2*(q+1)))*x +
                (q+1)*(D*e*(a*e^2)+c*d*(C*d^2-e*(B*d-A*e)))*x^2 +
                c*(q+3)*(d^3*D-C*d^2*e+B*d*e^2-A*e^3)*x^3,x],x]] /;
        FreeQ[{a,c,d,e},x] && PolyQ[Px,x] && LeQ[Expon[Px,x],3] && NeQ[c*d^4+a*e^4,0] && LtQ[q,-1]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [px__, d__, e__, q_, a__, c__, x_],
        optional: [e__, c__],
        when: {
            freeq!([a__, c__, d__, e__], x_)
                && rubi_poly_q(&px__, x_)
                && rubi_expon(&px__, x_).is_some_and(|exponent| leq!(Atom::num(exponent), 3))
                && neq!(&c__ * d__.pow(4) + &a__ * e__.pow(4), 0)
                && ltq!(q_, -1)
        },
        rhs: {
            let A = rubi_coeff(&px__, x_, 0).rubi_rhs();
            let B = rubi_coeff(&px__, x_, 1).rubi_rhs();
            let C = rubi_coeff(&px__, x_, 2).rubi_rhs();
            let D = rubi_coeff(&px__, x_, 3).rubi_rhs();
            let affine = &d__ + &e__ * x_;
            let quartic = &a__ + &c__ * x_.pow(4);
            let invariant = &c__ * d__.pow(4) + &a__ * e__.pow(4);
            let q1 = &q_ + Atom::num(1);
            let denominator = &q1 * &invariant;
            let leading =
                d__.pow(3) * &D - &C * d__.pow(2) * &e__ + &B * &d__ * e__.pow(2) - &A * e__.pow(3);
            let direct = -&leading * affine.pow(&q1) * quartic.sqrt() / &denominator;
            let simp = rubi_simp(
                &(&q1
                    * (&a__ * &e__ * (d__.pow(2) * &D - &C * &d__ * &e__ + &B * e__.pow(2))
                        + &A * &d__ * (&c__ * d__.pow(2)))
                    - (&e__
                        * &q1
                        * (&A * &c__ * d__.pow(2) + &a__ * &e__ * (&d__ * &D - &C * &e__))
                        - &B * &d__ * (&c__ * d__.pow(2) * &q1))
                        * x_
                    + &q1
                        * (&D * &e__ * (&a__ * e__.pow(2))
                            + &c__
                                * &d__
                                * (&C * d__.pow(2) - &e__ * (&B * &d__ - &A * &e__)))
                        * x_.pow(2)
                    + &c__ * (&q_ + Atom::num(3)) * &leading * x_.pow(3)),
                x_,
            );
            let recursive_integrand = affine.pow(q1) * simp / quartic.sqrt();
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / &denominator, recursive)
        },
    ));
}

fn push_rules_rule_2278(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_a__, capital_b__, a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 2278,
        source: "Int[(A_+B_.*x_)/((d_+e_.*x_)*Sqrt[a_+b_.*x_^2+c_.*x_^4]),x_Symbol] :=
          -A^2*(B*d+A*e)/e \\[Star] Subst[Int[1/(6*A^3*B*d+3*A^4*e-a*e*x^2),x],x,(A+B*x)^2/Sqrt[a+b*x^2+c*x^4]] /;
        FreeQ[{a,b,c,d,e,A,B},x] && NeQ[B*d-A*e,0] && EqQ[c^2*d^6+a*e^4*(13*c*d^2+b*e^2),0] &&
          EqQ[b^2*e^4-12*c*d^2*(c*d^2-b*e^2),0] && EqQ[4*A*c*d*e+B*(2*c*d^2-b*e^2),0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (capital_a__ + capital_b__ * x_)
            / ((d__ + e__ * x_) * (a__ + b__ * x_.pow(2) + c__ * x_.pow(4)).sqrt()),
        with: [capital_a__, capital_b__, d__, e__, a__, b__, c__, x_],
        optional: [capital_b__, e__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__, capital_a__, capital_b__], x_)
                && neq!(&capital_b__ * &d__ - &capital_a__ * &e__, 0)
                && eqq!(
                    c__.pow(2) * d__.pow(6)
                        + &a__ * e__.pow(4) * (Atom::num(13) * &c__ * d__.pow(2) + &b__ * e__.pow(2)),
                    0
                )
                && eqq!(
                    b__.pow(2) * e__.pow(4)
                        - Atom::num(12) * &c__ * d__.pow(2) * (&c__ * d__.pow(2) - &b__ * e__.pow(2)),
                    0
                )
                && eqq!(
                    Atom::num(4) * &capital_a__ * &c__ * &d__ * &e__
                        + &capital_b__ * (Atom::num(2) * &c__ * d__.pow(2) - &b__ * e__.pow(2)),
                    0
                )
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let sub_atom = Atom::var(sub);
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let inner_integrand = Atom::num(1)
                / (Atom::num(6) * capital_a__.pow(3) * &capital_b__ * &d__
                    + Atom::num(3) * capital_a__.pow(4) * &e__
                    - &a__ * &e__ * sub_atom.pow(2));
            let inner = rubi_rhs_int(&inner_integrand, sub);
            let substitution = (&capital_a__ + &capital_b__ * x_).pow(2) / quartic.sqrt();

            rubi_star(-capital_a__.pow(2) * (&capital_b__ * &d__ + &capital_a__ * &e__) / &e__, rubi_subst(&inner, sub, substitution))
        },
    ));
}

fn push_rules_rule_2279(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, px_, x_);
    rules.push(rubi_rule!(
        order: 2279,
        source: "Int[Px_/((d_+e_.*x_)*Sqrt[a_+b_.*x_^2+c_.*x_^4]),x_Symbol] :=
          With[{A=Coeff[Px,x,0],B=Coeff[Px,x,1],C=Coeff[Px,x,2],D=Coeff[Px,x,3]},
          Int[(x*(B*d-A*e+(d*D-C*e)*x^2))/((d^2-e^2*x^2)*Sqrt[a+b*x^2+c*x^4]),x] +
          Int[(A*d+(C*d-B*e)*x^2-D*e*x^4)/((d^2-e^2*x^2)*Sqrt[a+b*x^2+c*x^4]),x]] /;
        FreeQ[{a,b,c,d,e},x] && PolyQ[Px,x] && LeQ[Expon[Px,x],3] && NeQ[c*d^4+b*d^2*e^2+a*e^4,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: px_ / ((d__ + e__ * x_) * (a__ + b__ * x_.pow(2) + c__ * x_.pow(4)).sqrt()),
        with: [px_, d__, e__, a__, b__, c__, x_],
        optional: [e__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && rubi_poly_q(&px_, x_)
                && rubi_expon(&px_, x_).is_some_and(|exponent| leq!(Atom::num(exponent), 3))
                && neq!(&c__ * d__.pow(4) + &b__ * d__.pow(2) * e__.pow(2) + &a__ * e__.pow(4), 0)
        },
        rhs: {
            let A = rubi_coeff(&px_, x_, 0).rubi_rhs();
            let B = rubi_coeff(&px_, x_, 1).rubi_rhs();
            let C = rubi_coeff(&px_, x_, 2).rubi_rhs();
            let D = rubi_coeff(&px_, x_, 3).rubi_rhs();
            let denominator = d__.pow(2) - e__.pow(2) * x_.pow(2);
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let first_integrand = x_
                * (&B * &d__ - &A * &e__ + (&d__ * &D - &C * &e__) * x_.pow(2))
                / (&denominator * quartic.sqrt());
            let second_integrand = (&A * &d__ + (&C * &d__ - &B * &e__) * x_.pow(2)
                - &D * &e__ * x_.pow(4))
                / (denominator * quartic.sqrt());
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            first + second
        },
    ));
}

fn push_rules_rule_2280(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, c__, d__, e__, px_, x_);
    rules.push(rubi_rule!(
        order: 2280,
        source: "Int[Px_/((d_+e_.*x_)*Sqrt[a_+c_.*x_^4]),x_Symbol] :=
          With[{A=Coeff[Px,x,0],B=Coeff[Px,x,1],C=Coeff[Px,x,2],D=Coeff[Px,x,3]},
          Int[(x*(B*d-A*e+(d*D-C*e)*x^2))/((d^2-e^2*x^2)*Sqrt[a+c*x^4]),x] +
          Int[(A*d+(C*d-B*e)*x^2-D*e*x^4)/((d^2-e^2*x^2)*Sqrt[a+c*x^4]),x]] /;
        FreeQ[{a,c,d,e},x] && PolyQ[Px,x] && LeQ[Expon[Px,x],3] && NeQ[c*d^4+a*e^4,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: px_ / ((d__ + e__ * x_) * (a__ + c__ * x_.pow(4)).sqrt()),
        with: [px_, d__, e__, a__, c__, x_],
        optional: [e__, c__],
        when: {
            freeq!([a__, c__, d__, e__], x_)
                && rubi_poly_q(&px_, x_)
                && rubi_expon(&px_, x_).is_some_and(|exponent| leq!(Atom::num(exponent), 3))
                && neq!(&c__ * d__.pow(4) + &a__ * e__.pow(4), 0)
        },
        rhs: {
            let A = rubi_coeff(&px_, x_, 0).rubi_rhs();
            let B = rubi_coeff(&px_, x_, 1).rubi_rhs();
            let C = rubi_coeff(&px_, x_, 2).rubi_rhs();
            let D = rubi_coeff(&px_, x_, 3).rubi_rhs();
            let denominator = d__.pow(2) - e__.pow(2) * x_.pow(2);
            let quartic = &a__ + &c__ * x_.pow(4);
            let first_integrand = x_
                * (&B * &d__ - &A * &e__ + (&d__ * &D - &C * &e__) * x_.pow(2))
                / (&denominator * quartic.sqrt());
            let second_integrand = (&A * &d__ + (&C * &d__ - &B * &e__) * x_.pow(2)
                - &D * &e__ * x_.pow(4))
                / (denominator * quartic.sqrt());
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            first + second
        },
    ));
}

fn push_rules_rule_2281(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, p_, px_, x_);
    rules.push(rubi_rule!(
        order: 2281,
        source: "Int[Px_*(a_+b_.*x_^2+c_.*x_^4)^p_./(d_+e_.*x_),x_Symbol] :=
          d \\[Star] Int[Px*(a+b*x^2+c*x^4)^p/(d^2-e^2*x^2),x] - e \\[Star] Int[x*Px*(a+b*x^2+c*x^4)^p/(d^2-e^2*x^2),x] /;
        FreeQ[{a,b,c,d,e},x] && PolyQ[Px,x] && IntegerQ[p+1/2]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: px_ * (a__ + b__ * x_.pow(2) + c__ * x_.pow(4)).pow(p_) / (d__ + e__ * x_),
        with: [px_, a__, b__, c__, p_, d__, e__, x_],
        optional: [b__, c__, p_, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__, p_], x_)
                && rubi_poly_q(&px_, x_)
                && integerq!(&p_ + Atom::num(1) / Atom::num(2))
        },
        rhs: {
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let denominator = d__.pow(2) - e__.pow(2) * x_.pow(2);
            let first =
                rubi_rhs_int(&(&px_ * quartic.pow(&p_) / &denominator), x_);
            let second =
                rubi_rhs_int(&(x_ * &px_ * quartic.pow(p_) / denominator), x_);

            rubi_star(d__, first) - rubi_star(e__, second)
        },
    ));
}

fn push_rules_rule_2282(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, c__, d__, e__, p_, px_, x_);
    rules.push(rubi_rule!(
        order: 2282,
        source: "Int[Px_*(a_+c_.*x_^4)^p_./(d_+e_.*x_),x_Symbol] :=
          d \\[Star] Int[Px*(a+c*x^4)^p/(d^2-e^2*x^2),x] - e \\[Star] Int[x*Px*(a+c*x^4)^p/(d^2-e^2*x^2),x] /;
        FreeQ[{a,c,d,e},x] && PolyQ[Px,x] && IntegerQ[p+1/2]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: px_ * (a__ + c__ * x_.pow(4)).pow(p_) / (d__ + e__ * x_),
        with: [px_, a__, c__, p_, d__, e__, x_],
        optional: [c__, p_, e__],
        when: {
            freeq!([a__, c__, d__, e__, p_], x_)
                && rubi_poly_q(&px_, x_)
                && integerq!(&p_ + Atom::num(1) / Atom::num(2))
        },
        rhs: {
            let quartic = &a__ + &c__ * x_.pow(4);
            let denominator = d__.pow(2) - e__.pow(2) * x_.pow(2);
            let first =
                rubi_rhs_int(&(&px_ * quartic.pow(&p_) / &denominator), x_);
            let second =
                rubi_rhs_int(&(x_ * &px_ * quartic.pow(p_) / denominator), x_);

            rubi_star(d__, first) - rubi_star(e__, second)
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
    let e__ = symbols.e__;
    let p_ = symbols.p_;
    let px__ = symbols.px__;
    let q_ = symbols.q_;
    let x_ = symbols.x_;
    px__ * (d__ + e__ * x_).pow(q_) * (a__ + b__ * x_.pow(2) + c__ * x_.pow(4)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let p_ = symbols.p_;
    let px__ = symbols.px__;
    let q_ = symbols.q_;
    let x_ = symbols.x_;
    px__ * (d__ + e__ * x_).pow(q_) * (a__ + c__ * x_.pow(4)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_2(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let px__ = symbols.px__;
    let q_ = symbols.q_;
    let x_ = symbols.x_;
    px__ * (d__ + e__ * x_).pow(q_) / (a__ + b__ * x_.pow(2) + c__ * x_.pow(4)).sqrt()
}

#[inline(never)]
fn rubi_shared_pattern_3(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let px__ = symbols.px__;
    let q_ = symbols.q_;
    let x_ = symbols.x_;
    px__ * (d__ + e__ * x_).pow(q_) / (a__ + c__ * x_.pow(4)).sqrt()
}
