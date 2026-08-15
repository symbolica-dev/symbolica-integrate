use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_2141(rules);
    push_rules_rule_2155(rules);
    push_rules_rule_2156(rules);
    push_rules_rule_2157(rules);
    push_rules_rule_2158(rules);
    push_rules_rule_2159(rules);
    push_rules_rule_2160(rules);
    push_rules_rule_2161(rules);
    push_rules_rule_2162(rules);
    push_rules_rule_2163(rules);
    push_rules_rule_2164(rules);
    push_rules_rule_2165(rules);
    push_rules_rule_2166(rules);
    push_rules_rule_2167(rules);
    push_rules_rule_2168(rules);
    push_rules_rule_2169(rules);
    push_rules_rule_2170(rules);
    push_rules_rule_2171(rules);
    push_rules_rule_2172(rules);
    push_rules_rule_2173(rules);
    push_rules_rule_2174(rules);
    push_rules_rule_2175(rules);
    push_rules_rule_2176(rules);
    push_rules_rule_2177(rules);
    push_rules_rule_2178(rules);
    push_rules_rule_2179(rules);
    push_rules_rule_2180(rules);
    push_rules_rule_2181(rules);
    push_rules_rule_2182(rules);
    push_rules_rule_2183(rules);
    push_rules_rule_2184(rules);
    push_rules_rule_2185(rules);
    push_rules_rule_2186(rules);
    push_rules_rule_2187(rules);
}

fn push_rules_rule_2141(rules: &mut Vec<RubiRule>) {
    rubi_symb!(px_, a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 2141,
        source: "Int[Px_/((a_+b_.*x_+c_.*x_^2)*(d_+e_.*x_+f_.*x_^2)),x_Symbol] :=
          With[{A=Coeff[Px,x,0],B=Coeff[Px,x,1],C=Coeff[Px,x,2],q=c^2*d^2-b*c*d*e+a*c*e^2+b^2*d*f-2*a*c*d*f-a*b*e*f+a^2*f^2},
          1/q \\[Star] Int[(A*c^2*d-a*c*C*d-A*b*c*e+a*B*c*e+A*b^2*f-a*b*B*f-a*A*c*f+a^2*C*f+
            c*(B*c*d-b*C*d-A*c*e+a*C*e+A*b*f-a*B*f)*x)/(a+b*x+c*x^2),x] +
          1/q \\[Star] Int[(c*C*d^2-B*c*d*e+A*c*e^2+b*B*d*f-A*c*d*f-a*C*d*f-A*b*e*f+a*A*f^2-
            f*(B*c*d-b*C*d-A*c*e+a*C*e+A*b*f-a*B*f)*x)/(d+e*x+f*x^2),x] /;
         NeQ[q,0]] /;
        FreeQ[{a,b,c,d,e,f},x] && PolyQ[Px,x,2]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern: px_
            / ((a__ + b__ * x_ + c__ * x_.pow(2))
                * (d__ + e__ * x_ + f__ * x_.pow(2))),
        with: [px_, a__, b__, c__, d__, e__, f__, x_],
        optional: [b__, c__, e__, f__],
        x_free: [a__, b__, c__, d__, e__, f__],
        when: {
            let q = c__.pow(2) * d__.pow(2)
                - &b__ * &c__ * &d__ * &e__
                + &a__ * &c__ * e__.pow(2)
                + b__.pow(2) * &d__ * &f__
                - Atom::num(2) * &a__ * &c__ * &d__ * &f__
                - &a__ * &b__ * &e__ * &f__
                + a__.pow(2) * f__.pow(2);
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && rubi_poly_q_degree(&px_, x_, 2)
                && neq!(q, 0)
        },
        rhs: {
            let capital_a = rubi_coeff(&px_, x_, 0).rubi_rhs();
            let capital_b = rubi_coeff(&px_, x_, 1).rubi_rhs();
            let capital_c = rubi_coeff(&px_, x_, 2).rubi_rhs();
            let q = c__.pow(2) * d__.pow(2)
                - &b__ * &c__ * &d__ * &e__
                + &a__ * &c__ * e__.pow(2)
                + b__.pow(2) * &d__ * &f__
                - Atom::num(2) * &a__ * &c__ * &d__ * &f__
                - &a__ * &b__ * &e__ * &f__
                + a__.pow(2) * f__.pow(2);

            let shared_linear = &capital_b * &c__ * &d__
                - &b__ * &capital_c * &d__
                - &capital_a * &c__ * &e__
                + &a__ * &capital_c * &e__
                + &capital_a * &b__ * &f__
                - &a__ * &capital_b * &f__;
            let first_numerator = &capital_a * c__.pow(2) * &d__
                - &a__ * &c__ * &capital_c * &d__
                - &capital_a * &b__ * &c__ * &e__
                + &a__ * &capital_b * &c__ * &e__
                + &capital_a * b__.pow(2) * &f__
                - &a__ * &b__ * &capital_b * &f__
                - &a__ * &capital_a * &c__ * &f__
                + a__.pow(2) * &capital_c * &f__
                + &c__ * &shared_linear * x_;
            let second_numerator = &c__ * &capital_c * d__.pow(2)
                - &capital_b * &c__ * &d__ * &e__
                + &capital_a * &c__ * e__.pow(2)
                + &b__ * &capital_b * &d__ * &f__
                - &capital_a * &c__ * &d__ * &f__
                - &a__ * &capital_c * &d__ * &f__
                - &capital_a * &b__ * &e__ * &f__
                + &a__ * &capital_a * f__.pow(2)
                - &f__ * shared_linear * x_;
            let first_integrand = first_numerator
                / (&a__ + &b__ * x_ + &c__ * x_.pow(2));
            let second_integrand = second_numerator
                / (&d__ + &e__ * x_ + &f__ * x_.pow(2));

            rubi_star(Atom::num(1) / &q, rubi_rhs_int(&first_integrand, x_)) + rubi_star(Atom::num(1) / q, rubi_rhs_int(&second_integrand, x_))
        },
    ));
}

fn push_rules_rule_2155(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2155,
        source: "Int[(d_.+e_.*x_)^m_.*Pq_*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
          Int[(d+e*x)^(m+1)*PolynomialQuotient[Pq,d+e*x,x]*(a+b*x+c*x^2)^p,x] /;
        FreeQ[{a,b,c,d,e,m,p},x] && PolyQ[Pq,x] && EqQ[PolynomialRemainder[Pq,d+e*x,x],0]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [d__, e__, pq__, a__, b__, c__, m_, p_, x_],
        optional: [d__, e__, m_, a__, b__, c__, p_],
        when: {
            let affine = &d__ + &e__ * x_;
            freeq!([a__, b__, c__, d__, e__, m_, p_], x_)
                && poly_q(&pq__, x_)
                && rubi_polynomial_remainder(&pq__, &affine, x_)
                    .is_some_and(|remainder| eqq!(remainder, 0))
        },
        rhs: {
            let affine = &d__ + &e__ * x_;
            let quotient = rubi_polynomial_quotient(&pq__, &affine, x_).rubi_rhs();
            let integrand = affine.pow(&m_ + Atom::num(1)) * quotient * (&a__ + &b__ * x_ + &c__ * x_.pow(2)).pow(&p_);

            rubi_rhs_int(&integrand, x_)
        },
    ));
}

fn push_rules_rule_2156(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, e__, m_, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2156,
        source: "Int[(d_+e_.*x_)^m_.*Pq_*(a_+b_.*x_^2)^p_.,x_Symbol] :=
          Int[(d+e*x)^(m+1)*PolynomialQuotient[Pq,d+e*x,x]*(a+b*x^2)^p,x] /;
        FreeQ[{a,b,d,e,m,p},x] && PolyQ[Pq,x] && EqQ[PolynomialRemainder[Pq,d+e*x,x],0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [d__, e__, pq__, a__, b__, m_, p_, x_],
        optional: [e__, m_, b__, p_],
        when: {
            let affine = &d__ + &e__ * x_;
            freeq!([a__, b__, d__, e__, m_, p_], x_)
                && poly_q(&pq__, x_)
                && rubi_polynomial_remainder(&pq__, &affine, x_)
                    .is_some_and(|remainder| eqq!(remainder, 0))
        },
        rhs: {
            let affine = &d__ + &e__ * x_;
            let quotient = rubi_polynomial_quotient(&pq__, &affine, x_).rubi_rhs();
            let integrand = affine.pow(&m_ + Atom::num(1)) * quotient * (&a__ + &b__ * x_.pow(2)).pow(&p_);

            rubi_rhs_int(&integrand, x_)
        },
    ));
}

fn push_rules_rule_2157(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, p_, p2__, x_);
    rules.push(rubi_rule!(
        order: 2157,
        source: "Int[(d_.+e_.*x_)^m_.*P2_*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
          With[{f=Coeff[P2,x,0],g=Coeff[P2,x,1],h=Coeff[P2,x,2]},
          h*(d+e*x)^(m+1)*(a+b*x+c*x^2)^(p+1)/(c*e*(m+2*p+3)) /;
         EqQ[b*e*h*(m+p+2)+2*c*d*h*(p+1)-c*e*g*(m+2*p+3),0] && EqQ[b*d*h*(p+1)+a*e*h*(m+1)-c*e*f*(m+2*p+3),0]] /;
        FreeQ[{a,b,c,d,e,m,p},x] && PolyQ[P2,x,2] && NeQ[m+2*p+3,0]",
        desc: "Special case of one step of the Ostrogradskiy-Hermite integration method",
        refs: [],
        pattern: (d__ + e__ * x_).pow(m_) * p2__ * (a__ + b__ * x_ + c__ * x_.pow(2)).pow(p_),
        with: [d__, e__, p2__, a__, b__, c__, m_, p_, x_],
        optional: [d__, e__, m_, a__, b__, c__, p_],
        when: {
            let f = polynomial_coefficient(&p2__, x_, 0);
            let g = polynomial_coefficient(&p2__, x_, 1);
            let h = polynomial_coefficient(&p2__, x_, 2);
            freeq!([a__, b__, c__, d__, e__, m_, p_], x_)
                && rubi_poly_q_degree(&p2__, x_, 2)
                && neq!(&m_ + Atom::num(2) * &p_ + Atom::num(3), 0)
                && f.zip(g).zip(h).is_some_and(|((f, g), h)| {
                    eqq!(
                        &b__ * &e__ * &h * (&m_ + &p_ + Atom::num(2))
                            + Atom::num(2) * &c__ * &d__ * &h * (&p_ + Atom::num(1))
                            - &c__ * &e__ * &g * (&m_ + Atom::num(2) * &p_ + Atom::num(3)),
                        0
                    ) && eqq!(
                        &b__ * &d__ * &h * (&p_ + Atom::num(1)) + &a__ * &e__ * &h * (&m_ + Atom::num(1))
                            - &c__ * &e__ * &f * (&m_ + Atom::num(2) * &p_ + Atom::num(3)),
                        0
                    )
                })
        },
        rhs: {
            let denominator = &c__ * &e__ * (&m_ + Atom::num(2) * &p_ + Atom::num(3));
            let h = polynomial_coefficient(&p2__, x_, 2).rubi_rhs();
            let result =
                h * (&d__ + &e__ * x_).pow(&m_ + Atom::num(1))
                    * (&a__ + &b__ * x_ + &c__ * x_.pow(2)).pow(&p_ + Atom::num(1))
                    / denominator;
            rubi_simp(&result, x_)
        },
    ));
}

fn push_rules_rule_2158(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, d__, e__, m_, p_, p2__, x_);
    rules.push(rubi_rule!(
        order: 2158,
        source: "Int[(d_+e_.*x_)^m_.*P2_*(a_+b_.*x_^2)^p_.,x_Symbol] :=
          With[{f=Coeff[P2,x,0],g=Coeff[P2,x,1],h=Coeff[P2,x,2]},
          h*(d+e*x)^(m+1)*(a+b*x^2)^(p+1)/(b*e*(m+2*p+3)) /;
         EqQ[2*d*h*(p+1)-e*g*(m+2*p+3),0] && EqQ[a*h*(m+1)-b*f*(m+2*p+3),0]] /;
        FreeQ[{a,b,d,e,m,p},x] && PolyQ[P2,x,2] && NeQ[m+2*p+3,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: (d__ + e__ * x_).pow(m_) * p2__ * (a__ + b__ * x_.pow(2)).pow(p_),
        with: [d__, e__, p2__, a__, b__, m_, p_, x_],
        optional: [e__, m_, b__, p_],
        when: {
            let f = polynomial_coefficient(&p2__, x_, 0);
            let g = polynomial_coefficient(&p2__, x_, 1);
            let h = polynomial_coefficient(&p2__, x_, 2);
            freeq!([a__, b__, d__, e__, m_, p_], x_)
                && rubi_poly_q_degree(&p2__, x_, 2)
                && neq!(&m_ + Atom::num(2) * &p_ + Atom::num(3), 0)
                && f.zip(g).zip(h).is_some_and(|((f, g), h)| {
                    eqq!(
                        Atom::num(2) * &d__ * &h * (&p_ + Atom::num(1)) - &e__ * &g * (&m_ + Atom::num(2) * &p_ + Atom::num(3)),
                        0
                    ) && eqq!(
                        &a__ * &h * (&m_ + Atom::num(1)) - &b__ * &f * (&m_ + Atom::num(2) * &p_ + Atom::num(3)),
                        0
                    )
                })
        },
        rhs: {
            let denominator = &b__ * &e__ * (&m_ + Atom::num(2) * &p_ + Atom::num(3));
            let h = polynomial_coefficient(&p2__, x_, 2).rubi_rhs();
            let result = h
                * (&d__ + &e__ * x_).pow(&m_ + Atom::num(1))
                * (&a__ + &b__ * x_.pow(2)).pow(&p_ + Atom::num(1))
                / denominator;
            rubi_simp(&result, x_)
        },
    ));
}

fn push_rules_rule_2159(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2159,
        source: "Int[(d_.+e_.*x_)^m_.*Pq_*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
          Int[ExpandIntegrand[(d+e*x)^m*Pq*(a+b*x+c*x^2)^p,x],x] /;
        FreeQ[{a,b,c,d,e,m},x] && PolyQ[Pq,x] && IGtQ[p,-2]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [d__, e__, pq__, a__, b__, c__, m_, p_, x_],
        optional: [d__, e__, m_, a__, b__, c__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_], x_)
                && poly_q(&pq__, x_)
                && igtq!(p_, -2)
        },
        rhs: {
            let integrand = (&d__ + &e__ * x_).pow(&m_) * &pq__ * (&a__ + &b__ * x_ + &c__ * x_.pow(2)).pow(&p_);
            let expanded = rubi_expand_integrand(&integrand, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_2160(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, e__, m_, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2160,
        source: "Int[(d_+e_.*x_)^m_.*Pq_*(a_+b_.*x_^2)^p_.,x_Symbol] :=
          Int[ExpandIntegrand[(d+e*x)^m*Pq*(a+b*x^2)^p,x],x] /;
        FreeQ[{a,b,d,e,m},x] && PolyQ[Pq,x] && IGtQ[p,-2]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [d__, e__, pq__, a__, b__, m_, p_, x_],
        optional: [e__, m_, b__, p_],
        when: {
            freeq!([a__, b__, d__, e__, m_], x_)
                && poly_q(&pq__, x_)
                && igtq!(p_, -2)
        },
        rhs: {
            let integrand = (&d__ + &e__ * x_).pow(&m_) * &pq__ * (&a__ + &b__ * x_.pow(2)).pow(&p_);
            let expanded = rubi_expand_integrand(&integrand, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_2161(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2161,
        source: "Int[(d_.+e_.*x_)^m_.*Pq_*(a_+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          (a+b*x+c*x^2)^FracPart[p]/((4*c)^IntPart[p]*(b+2*c*x)^(2*FracPart[p])) \\[Star] Int[(d+e*x)^m*Pq*(b+2*c*x)^(2*p),x] /;
        FreeQ[{a,b,c,d,e,m,p},x] && PolyQ[Pq,x] && EqQ[b^2-4*a*c,0]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [d__, e__, pq__, a__, b__, c__, m_, p_, x_],
        optional: [d__, e__, m_, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, p_], x_)
                && poly_q(&pq__, x_)
                && !c__.expand().is_zero()
                && eqq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
        },
        rhs: {
            if c__.expand().is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let frac_p = rubi_frac_part(&p_);
            let linear = &b__ + Atom::num(2) * &c__ * x_;
            let denominator = (Atom::num(4) * &c__).pow(rubi_int_part(&p_)) * linear.pow(Atom::num(2) * &frac_p);
            if denominator.expand().is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let trinomial = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let recursive_integrand = (&d__ + &e__ * x_).pow(&m_) * &pq__ * linear.pow(Atom::num(2) * &p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(trinomial.pow(&frac_p), recursive / denominator)
        },
    ));
}

fn push_rules_rule_2162(rules: &mut Vec<RubiRule>) {
    rubi_symb!(b__, c__, e__, m_, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2162,
        source: "Int[(e_.*x_)^m_.*Pq_*(b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
          e \\[Star] Int[(e*x)^(m-1)*PolynomialQuotient[Pq,b+c*x,x]*(b*x+c*x^2)^(p+1),x] /;
        FreeQ[{b,c,e,m,p},x] && PolyQ[Pq,x] && EqQ[PolynomialRemainder[Pq,b+c*x,x],0]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: (e__ * x_).pow(m_) * pq__ * (b__ * x_ + c__ * x_.pow(2)).pow(p_),
        with: [e__, pq__, b__, c__, m_, p_, x_],
        optional: [e__, m_, b__, c__, p_],
        when: {
            let divisor = &b__ + &c__ * x_;
            freeq!([b__, c__, e__, m_, p_], x_)
                && poly_q(&pq__, x_)
                && rubi_polynomial_remainder(&pq__, &divisor, x_)
                    .is_some_and(|remainder| eqq!(remainder, 0))
        },
        rhs: {
            let divisor = &b__ + &c__ * x_;
            let quotient = rubi_polynomial_quotient(&pq__, &divisor, x_).rubi_rhs();
            let integrand = (&e__ * x_).pow(&m_ - Atom::num(1)) * quotient * (&b__ * x_ + &c__ * x_.pow(2)).pow(&p_ + Atom::num(1));

            rubi_star(e__, rubi_rhs_int(&integrand, x_))
        },
    ));
}

fn push_rules_rule_2163(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2163,
        source: "Int[(d_+e_.*x_)^m_.*Pq_*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
          d*e \\[Star] Int[(d+e*x)^(m-1)*PolynomialQuotient[Pq,a*e+c*d*x,x]*(a+b*x+c*x^2)^(p+1),x] /;
        FreeQ[{a,b,c,d,e,m,p},x] && PolyQ[Pq,x] && NeQ[b^2-4*a*c,0] && EqQ[c*d^2-b*d*e+a*e^2,0] && EqQ[PolynomialRemainder[Pq,a*e+c*d*x,x],0]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [d__, e__, pq__, a__, b__, c__, m_, p_, x_],
        optional: [e__, m_, a__, b__, c__, p_],
        when: {
            let divisor = &a__ * &e__ + &c__ * &d__ * x_;
            freeq!([a__, b__, c__, d__, e__, m_, p_], x_)
                && poly_q(&pq__, x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && eqq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && rubi_polynomial_remainder(&pq__, &divisor, x_)
                    .is_some_and(|remainder| eqq!(remainder, 0))
        },
        rhs: {
            let divisor = &a__ * &e__ + &c__ * &d__ * x_;
            let quotient = rubi_polynomial_quotient(&pq__, &divisor, x_).rubi_rhs();
            let integrand = (&d__ + &e__ * x_).pow(&m_ - Atom::num(1)) * quotient * (&a__ + &b__ * x_ + &c__ * x_.pow(2)).pow(&p_ + Atom::num(1));

            rubi_star(&d__ * &e__, rubi_rhs_int(&integrand, x_))
        },
    ));
}

fn push_rules_rule_2164(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, e__, m_, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2164,
        source: "Int[(d_+e_.*x_)^m_.*Pq_*(a_+b_.*x_^2)^p_.,x_Symbol] :=
          d*e \\[Star] Int[(d+e*x)^(m-1)*PolynomialQuotient[Pq,a*e+b*d*x,x]*(a+b*x^2)^(p+1),x] /;
        FreeQ[{a,b,d,e,m,p},x] && PolyQ[Pq,x] && EqQ[b*d^2+a*e^2,0] && EqQ[PolynomialRemainder[Pq,a*e+b*d*x,x],0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [d__, e__, pq__, a__, b__, m_, p_, x_],
        optional: [e__, m_, b__, p_],
        when: {
            let divisor = &a__ * &e__ + &b__ * &d__ * x_;
            freeq!([a__, b__, d__, e__, m_, p_], x_)
                && poly_q(&pq__, x_)
                && eqq!(&b__ * d__.pow(2) + &a__ * e__.pow(2), 0)
                && rubi_polynomial_remainder(&pq__, &divisor, x_)
                    .is_some_and(|remainder| eqq!(remainder, 0))
        },
        rhs: {
            let divisor = &a__ * &e__ + &b__ * &d__ * x_;
            let quotient = rubi_polynomial_quotient(&pq__, &divisor, x_).rubi_rhs();
            let integrand = (&d__ + &e__ * x_).pow(&m_ - Atom::num(1)) * quotient * (&a__ + &b__ * x_.pow(2)).pow(&p_ + Atom::num(1));

            rubi_star(&d__ * &e__, rubi_rhs_int(&integrand, x_))
        },
    ));
}

fn push_rules_rule_2165(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2165,
        source: "Int[(d_.+e_.*x_)^m_.*Pq_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          With[{Qx=PolynomialQuotient[Pq,a*e+c*d*x,x], R=PolynomialRemainder[Pq,a*e+c*d*x,x]},
          R*(2*c*d-b*e)*(d+e*x)^m*(a+b*x+c*x^2)^(p+1)/(e*(p+1)*(b^2-4*a*c)) +
          1/((p+1)*(b^2-4*a*c)) \\[Star] Int[(d+e*x)^(m-1)*(a+b*x+c*x^2)^(p+1)*
            ExpandToSum[d*e*(p+1)*(b^2-4*a*c)*Qx-R*(2*c*d-b*e)*(m+2*p+2),x],x]] /;
        FreeQ[{a,b,c,d,e},x] && PolyQ[Pq,x] && NeQ[b^2-4*a*c,0] && EqQ[c*d^2-b*d*e+a*e^2,0] && ILtQ[p+1/2,0] && GtQ[m,0]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [d__, e__, pq__, a__, b__, c__, m_, p_, x_],
        optional: [d__, e__, m_, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && poly_q(&pq__, x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && eqq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && iltq!(&p_ + Atom::num(1) / Atom::num(2), 0)
                && gtq!(m_, 0)
        },
        rhs: {
            let discriminant = b__.pow(2) - Atom::num(4) * &a__ * &c__;
            let raised_p = &p_ + Atom::num(1);
            let direct_denominator = &e__ * &raised_p * &discriminant;
            let recursive_denominator = &raised_p * &discriminant;
            if direct_denominator.expand().is_zero() || recursive_denominator.expand().is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let divisor = &a__ * &e__ + &c__ * &d__ * x_;
            let (capital_q, f) = polynomial_quotient_remainder(&pq__, &divisor, x_).rubi_rhs();
            let affine = &d__ + &e__ * x_;
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let balance = Atom::num(2) * &c__ * &d__ - &b__ * &e__;
            let direct = &f * &balance * affine.pow(&m_) * quadratic.pow(&raised_p) / &direct_denominator;
            let expand_to_sum = rubi_expand_to_sum(
                &(&d__ * &e__ * &raised_p * &discriminant * capital_q
                    - &f * &balance * (&m_ + Atom::num(2) * &p_ + Atom::num(2))),
                x_,
            );
            let recursive = rubi_rhs_int(
                &(affine.pow(&m_ - Atom::num(1))
                    * quadratic.pow(raised_p)
                    * expand_to_sum),
                x_,
            );

            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / recursive_denominator, recursive)
        },
    ));
}

fn push_rules_rule_2166(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, e__, m_, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2166,
        source: "Int[(d_+e_.*x_)^m_.*Pq_*(a_+b_.*x_^2)^p_,x_Symbol] :=
          With[{Qx=PolynomialQuotient[Pq,a*e+b*d*x,x], R=PolynomialRemainder[Pq,a*e+b*d*x,x]},
          -d*R*(d+e*x)^m*(a+b*x^2)^(p+1)/(2*a*e*(p+1)) +
          d/(2*a*(p+1)) \\[Star] Int[(d+e*x)^(m-1)*(a+b*x^2)^(p+1)*ExpandToSum[2*a*e*(p+1)*Qx+R*(m+2*p+2),x],x]] /;
        FreeQ[{a,b,d,e},x] && PolyQ[Pq,x] && EqQ[b*d^2+a*e^2,0] && ILtQ[p+1/2,0] && GtQ[m,0]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [d__, e__, pq__, a__, b__, m_, p_, x_],
        optional: [e__, m_, b__],
        when: {
            freeq!([a__, b__, d__, e__], x_)
                && poly_q(&pq__, x_)
                && eqq!(&b__ * d__.pow(2) + &a__ * e__.pow(2), 0)
                && iltq!(&p_ + Atom::num(1) / Atom::num(2), 0)
                && gtq!(m_, 0)
        },
        rhs: {
            let raised_p = &p_ + Atom::num(1);
            let direct_denominator = Atom::num(2) * &a__ * &e__ * &raised_p;
            let recursive_denominator = Atom::num(2) * &a__ * &raised_p;
            if direct_denominator.expand().is_zero() || recursive_denominator.expand().is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let divisor = &a__ * &e__ + &b__ * &d__ * x_;
            let (capital_q, f) = polynomial_quotient_remainder(&pq__, &divisor, x_).rubi_rhs();
            let affine = &d__ + &e__ * x_;
            let quadratic = &a__ + &b__ * x_.pow(2);
            let direct = -&d__ * &f * affine.pow(&m_) * quadratic.pow(&raised_p) / &direct_denominator;
            let expand_to_sum = rubi_expand_to_sum(
                &(Atom::num(2) * &a__ * &e__ * &raised_p * capital_q
                    + &f * (&m_ + Atom::num(2) * &p_ + Atom::num(2))),
                x_,
            );
            let recursive = rubi_rhs_int(
                &(affine.pow(&m_ - Atom::num(1))
                    * quadratic.pow(raised_p)
                    * expand_to_sum),
                x_,
            );

            rubi_simp(&(direct), x_) + rubi_star(d__, recursive / recursive_denominator)
        },
    ));
}

fn push_rules_rule_2167(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2167,
        source: "Int[(d_.+e_.*x_)^m_*Pq_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          Int[ExpandIntegrand[(a+b*x+c*x^2)^p,(d+e*x)^m*Pq,x],x] /;
        FreeQ[{a,b,c,d,e},x] && PolyQ[Pq,x] && NeQ[b^2-4*a*c,0] && EqQ[c*d^2-b*d*e+a*e^2,0] && EqQ[m+Expon[Pq,x]+2*p+1,0] && ILtQ[m,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [d__, e__, pq__, a__, b__, c__, m_, p_, x_],
        optional: [d__, e__, a__, b__, c__],
        when: {
            let q = polynomial_degree(&pq__, x_);
            freeq!([a__, b__, c__, d__, e__], x_)
                && poly_q(&pq__, x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && eqq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && q.is_some_and(|q| eqq!(&m_ + Atom::num(q) + Atom::num(2) * &p_ + Atom::num(1), 0))
                && iltq!(m_, 0)
        },
        rhs: {
            let u = (&a__ + &b__ * x_ + &c__ * x_.pow(2)).pow(&p_);
            let v_expr = (&d__ + &e__ * x_).pow(&m_) * &pq__;
            let expanded = rubi_expand_integrand_product(&u, &v_expr, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_2168(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, e__, m_, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2168,
        source: "Int[(d_+e_.*x_)^m_*Pq_*(a_+b_.*x_^2)^p_,x_Symbol] :=
          Int[ExpandIntegrand[(a+b*x^2)^p,(d+e*x)^m*Pq,x],x] /;
        FreeQ[{a,b,d,e},x] && PolyQ[Pq,x] && EqQ[b*d^2+a*e^2,0] && EqQ[m+Expon[Pq,x]+2*p+1,0] && ILtQ[m,0]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [d__, e__, pq__, a__, b__, m_, p_, x_],
        optional: [e__, b__],
        when: {
            let q = polynomial_degree(&pq__, x_);
            freeq!([a__, b__, d__, e__], x_)
                && poly_q(&pq__, x_)
                && eqq!(&b__ * d__.pow(2) + &a__ * e__.pow(2), 0)
                && q.is_some_and(|q| eqq!(&m_ + Atom::num(q) + Atom::num(2) * &p_ + Atom::num(1), 0))
                && iltq!(m_, 0)
        },
        rhs: {
            let u = (&a__ + &b__ * x_.pow(2)).pow(&p_);
            let v_expr = (&d__ + &e__ * x_).pow(&m_) * &pq__;
            let expanded = rubi_expand_integrand_product(&u, &v_expr, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_2169(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2169,
        source: "Int[(d_.+e_.*x_)^m_.*Pq_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          With[{q=Expon[Pq,x],f=Coeff[Pq,x,Expon[Pq,x]]},
          f*(d+e*x)^(m+q-1)*(a+b*x+c*x^2)^(p+1)/(c*e^(q-1)*(m+q+2*p+1)) +
          1/(c*e^q*(m+q+2*p+1)) \\[Star] Int[(d+e*x)^m*(a+b*x+c*x^2)^p*
            ExpandToSum[c*e^q*(m+q+2*p+1)*Pq-c*f*(m+q+2*p+1)*(d+e*x)^q+e*f*(m+p+q)*(d+e*x)^(q-2)*(b*d-2*a*e+(2*c*d-b*e)*x),x],x] /;
         NeQ[m+q+2*p+1,0]] /;
        FreeQ[{a,b,c,d,e,m,p},x] && PolyQ[Pq,x] && NeQ[b^2-4*a*c,0] && EqQ[c*d^2-b*d*e+a*e^2,0]",
        desc: "Algebraic expansion and quadratic recurrence 3a with A=d, B=e and m=m-1",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [d__, e__, pq__, a__, b__, c__, m_, p_, x_],
        optional: [d__, e__, a__, b__, c__, m_],
        when: {
            let q = polynomial_degree(&pq__, x_);
            freeq!([a__, b__, c__, d__, e__, m_, p_], x_)
                && poly_q(&pq__, x_)
                && !c__.expand().is_zero()
                && !e__.expand().is_zero()
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && eqq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && q.is_some_and(|q| neq!(&m_ + Atom::num(q) + Atom::num(2) * &p_ + Atom::num(1), 0))
        },
        rhs: {
            if c__.expand().is_zero() || e__.expand().is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let (q, f) = polynomial_leading_term(&pq__, x_).rubi_rhs();
            let q_atom = Atom::num(q);
            let balance = &m_ + &q_atom + Atom::num(2) * &p_ + Atom::num(1);
            let direct_denominator = &c__ * e__.pow(q - 1) * &balance;
            let recursive_denominator = &c__ * e__.pow(q) * &balance;
            if direct_denominator.expand().is_zero() || recursive_denominator.expand().is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let affine = &d__ + &e__ * x_;
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let direct = &f * affine.pow(&m_ + &q_atom - Atom::num(1)) * quadratic.pow(&p_ + Atom::num(1)) / &direct_denominator;
            let expand_to_sum = (&c__ * e__.pow(q) * &balance * &pq__ - &c__ * &f * &balance * affine.pow(q)
                + &e__ * &f * (&m_ + &p_ + &q_atom) * affine.pow(q - 2) * (&b__ * &d__ - Atom::num(2) * &a__ * &e__ + (Atom::num(2) * &c__ * &d__ - &b__ * &e__) * x_))
                .expand();
            let recursive = rubi_rhs_int(&(affine.pow(&m_) * quadratic.pow(&p_) * expand_to_sum), x_);

            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / recursive_denominator, recursive)
        },
    ));
}

fn push_rules_rule_2170(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, e__, m_, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2170,
        source: "Int[(d_+e_.*x_)^m_.*Pq_*(a_+b_.*x_^2)^p_,x_Symbol] :=
          With[{q=Expon[Pq,x],f=Coeff[Pq,x,Expon[Pq,x]]},
          f*(d+e*x)^(m+q-1)*(a+b*x^2)^(p+1)/(b*e^(q-1)*(m+q+2*p+1)) +
          1/(b*e^q*(m+q+2*p+1)) \\[Star] Int[(d+e*x)^m*(a+b*x^2)^p*
            ExpandToSum[b*e^q*(m+q+2*p+1)*Pq-b*f*(m+q+2*p+1)*(d+e*x)^q-2*e*f*(m+p+q)*(d+e*x)^(q-2)*(a*e-b*d*x),x],x] /;
         NeQ[m+q+2*p+1,0]] /;
        FreeQ[{a,b,d,e,m,p},x] && PolyQ[Pq,x] && EqQ[b*d^2+a*e^2,0] && Not[IGtQ[m,0]]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [d__, e__, pq__, a__, b__, m_, p_, x_],
        optional: [e__, b__, m_],
        when: {
            let q = polynomial_degree(&pq__, x_);
            freeq!([a__, b__, d__, e__, m_, p_], x_)
                && poly_q(&pq__, x_)
                && !b__.expand().is_zero()
                && !e__.expand().is_zero()
                && eqq!(&b__ * d__.pow(2) + &a__ * e__.pow(2), 0)
                && !igtq!(m_, 0)
                && q.is_some_and(|q| neq!(&m_ + Atom::num(q) + Atom::num(2) * &p_ + Atom::num(1), 0))
        },
        rhs: {
            if b__.expand().is_zero() || e__.expand().is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let (q, f) = polynomial_leading_term(&pq__, x_).rubi_rhs();
            let q_atom = Atom::num(q);
            let balance = &m_ + &q_atom + Atom::num(2) * &p_ + Atom::num(1);
            let direct_denominator = &b__ * e__.pow(q - 1) * &balance;
            let recursive_denominator = &b__ * e__.pow(q) * &balance;
            if direct_denominator.expand().is_zero() || recursive_denominator.expand().is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let affine = &d__ + &e__ * x_;
            let quadratic = &a__ + &b__ * x_.pow(2);
            let direct = &f * affine.pow(&m_ + &q_atom - Atom::num(1)) * quadratic.pow(&p_ + Atom::num(1)) / &direct_denominator;
            let expand_to_sum = (&b__ * e__.pow(q) * &balance * &pq__
                - &b__ * &f * &balance * affine.pow(q)
                - Atom::num(2) * &e__ * &f * (&m_ + &p_ + &q_atom) * affine.pow(q - 2) * (&a__ * &e__ - &b__ * &d__ * x_))
                .expand();
            let recursive = rubi_rhs_int(&(affine.pow(&m_) * quadratic.pow(&p_) * expand_to_sum), x_);

            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / recursive_denominator, recursive)
        },
    ));
}

fn push_rules_rule_2171(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2171,
        source: "Int[(d_.+e_.*x_)^m_.*Pq_*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
          Int[(d+e*x)^(m+p)*(a/d+c/e*x)^p*Pq,x] /;
        FreeQ[{a,b,c,d,e,m},x] && PolyQ[Pq,x] && NeQ[b^2-4*a*c,0] && EqQ[c*d^2-b*d*e+a*e^2,0] && IntegerQ[p]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [d__, e__, pq__, a__, b__, c__, m_, p_, x_],
        optional: [d__, e__, a__, b__, c__, p_, m_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_], x_)
                && poly_q(&pq__, x_)
                && !d__.expand().is_zero()
                && !e__.expand().is_zero()
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && eqq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && integerq!(p_)
        },
        rhs: {
            if d__.expand().is_zero() || e__.expand().is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let transformed = (&d__ + &e__ * x_).pow(&m_ + &p_) * (&a__ / &d__ + &c__ / &e__ * x_).pow(&p_) * &pq__;

            rubi_rhs_int(&transformed, x_)
        },
    ));
}

fn push_rules_rule_2172(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, e__, m_, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2172,
        source: "Int[(d_+e_.*x_)^m_.*Pq_*(a_+b_.*x_^2)^p_.,x_Symbol] :=
          Int[(d+e*x)^(m+p)*(a/d+b/e*x)^p*Pq,x] /;
        FreeQ[{a,b,d,e,m},x] && PolyQ[Pq,x] && EqQ[b*d^2+a*e^2,0] && IntegerQ[p]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [d__, e__, pq__, a__, b__, m_, p_, x_],
        optional: [e__, b__, p_, m_],
        when: {
            freeq!([a__, b__, d__, e__, m_], x_)
                && poly_q(&pq__, x_)
                && !d__.expand().is_zero()
                && !e__.expand().is_zero()
                && eqq!(&b__ * d__.pow(2) + &a__ * e__.pow(2), 0)
                && integerq!(p_)
        },
        rhs: {
            if d__.expand().is_zero() || e__.expand().is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let transformed = (&d__ + &e__ * x_).pow(&m_ + &p_) * (&a__ / &d__ + &b__ / &e__ * x_).pow(&p_) * &pq__;

            rubi_rhs_int(&transformed, x_)
        },
    ));
}

fn push_rules_rule_2173(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2173,
        source: "Int[(d_.+e_.*x_)^m_.*Pq_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          (a+b*x+c*x^2)^FracPart[p]/((d+e*x)^FracPart[p]*(a/d+(c*x)/e)^FracPart[p]) \\[Star] Int[(d+e*x)^(m+p)*(a/d+c/e*x)^p*Pq,x] /;
        FreeQ[{a,b,c,d,e,m,p},x] && PolyQ[Pq,x] && NeQ[b^2-4*a*c,0] && EqQ[c*d^2-b*d*e+a*e^2,0] && Not[IntegerQ[p]] && Not[IGtQ[m,0]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [d__, e__, pq__, a__, b__, c__, m_, p_, x_],
        optional: [d__, e__, a__, b__, c__, m_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, p_], x_)
                && poly_q(&pq__, x_)
                && !d__.expand().is_zero()
                && !e__.expand().is_zero()
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && eqq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && !integerq!(p_)
                && !igtq!(m_, 0)
        },
        rhs: {
            if d__.expand().is_zero() || e__.expand().is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let frac_p = rubi_frac_part(&p_);
            let affine = &d__ + &e__ * x_;
            let transformed_linear = &a__ / &d__ + &c__ / &e__ * x_;
            let denominator = affine.pow(&frac_p) * transformed_linear.pow(&frac_p);
            if denominator.expand().is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let recursive_integrand = affine.pow(&m_ + &p_) * transformed_linear.pow(&p_) * &pq__;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(quadratic.pow(&frac_p), recursive / denominator)
        },
    ));
}

fn push_rules_rule_2174(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, e__, m_, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2174,
        source: "Int[(d_+e_.*x_)^m_.*Pq_*(a_+b_.*x_^2)^p_,x_Symbol] :=
          (a+b*x^2)^FracPart[p]/((d+e*x)^FracPart[p]*(a/d+(b*x)/e)^FracPart[p]) \\[Star] Int[(d+e*x)^(m+p)*(a/d+b/e*x)^p*Pq,x] /;
        FreeQ[{a,b,d,e,m,p},x] && PolyQ[Pq,x] && EqQ[b*d^2+a*e^2,0] && Not[IntegerQ[p]] && Not[IGtQ[m,0]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [d__, e__, pq__, a__, b__, m_, p_, x_],
        optional: [e__, b__, m_],
        when: {
            freeq!([a__, b__, d__, e__, m_, p_], x_)
                && poly_q(&pq__, x_)
                && !d__.expand().is_zero()
                && !e__.expand().is_zero()
                && eqq!(&b__ * d__.pow(2) + &a__ * e__.pow(2), 0)
                && !integerq!(p_)
                && !igtq!(m_, 0)
        },
        rhs: {
            if d__.expand().is_zero() || e__.expand().is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let frac_p = rubi_frac_part(&p_);
            let affine = &d__ + &e__ * x_;
            let transformed_linear = &a__ / &d__ + &b__ / &e__ * x_;
            let denominator = affine.pow(&frac_p) * transformed_linear.pow(&frac_p);
            if denominator.expand().is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let quadratic = &a__ + &b__ * x_.pow(2);
            let recursive_integrand = affine.pow(&m_ + &p_) * transformed_linear.pow(&p_) * &pq__;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(quadratic.pow(&frac_p), recursive / denominator)
        },
    ));
}

fn push_rules_rule_2175(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2175,
        source: "Int[(d_.+e_.*x_)^m_.*Pq_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          With[{Qx=PolynomialQuotient[Pq,a+b*x+c*x^2,x],
                R=Coeff[PolynomialRemainder[Pq,a+b*x+c*x^2,x],x,0],
                S=Coeff[PolynomialRemainder[Pq,a+b*x+c*x^2,x],x,1]},
          (d+e*x)^m*(a+b*x+c*x^2)^(p+1)*(R*b-2*a*S+(2*c*R-b*S)*x)/((p+1)*(b^2-4*a*c)) +
          1/((p+1)*(b^2-4*a*c)) \\[Star] Int[(d+e*x)^(m-1)*(a+b*x+c*x^2)^(p+1)*
            ExpandToSum[(p+1)*(b^2-4*a*c)*(d+e*x)*Qx+S*(2*a*e*m+b*d*(2*p+3))-R*(b*e*m+2*c*d*(2*p+3))-e*(2*c*R-b*S)*(m+2*p+3)*x,x],x]] /;
        FreeQ[{a,b,c,d,e},x] && PolyQ[Pq,x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && LtQ[p,-1] && GtQ[m,0] &&
          (IntegerQ[p] || Not[IntegerQ[m]] || Not[RationalQ[a,b,c,d,e]]) &&
          Not[IGtQ[m,0] && RationalQ[a,b,c,d,e] && (IntegerQ[p] || ILtQ[p+1/2,0])]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [d__, e__, pq__, a__, b__, c__, m_, p_, x_],
        optional: [d__, e__, a__, b__, c__, m_],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && poly_q(&pq__, x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && neq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && ltq!(p_, -1)
                && gtq!(m_, 0)
                && (integerq!(p_) || !integerq!(m_) || !rationalq!([a__, b__, c__, d__, e__]))
                && !(igtq!(m_, 0)
                    && rationalq!([a__, b__, c__, d__, e__])
                    && (integerq!(p_) || iltq!(&p_ + Atom::num(1) / Atom::num(2), 0)))
        },
        rhs: {
            let affine = &d__ + &e__ * x_;
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let discriminant = b__.pow(2) - Atom::num(4) * &a__ * &c__;
            let raised_p = &p_ + Atom::num(1);
            let denominator = &raised_p * &discriminant;
            if denominator.expand().is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let (capital_q, capital_r) = polynomial_quotient_remainder(&pq__, &quadratic, x_).rubi_rhs();
            let f = polynomial_coefficient(&capital_r, x_, 0).rubi_rhs();
            let g = polynomial_coefficient(&capital_r, x_, 1).rubi_rhs();
            let linear = &f * &b__ - Atom::num(2) * &a__ * &g + (Atom::num(2) * &c__ * &f - &b__ * &g) * x_;
            let direct = affine.pow(&m_) * quadratic.pow(&raised_p) * linear / &denominator;
            let expand_to_sum = (&raised_p * &discriminant * &affine * capital_q
                + &g * (Atom::num(2) * &a__ * &e__ * &m_ + &b__ * &d__ * (Atom::num(2) * &p_ + Atom::num(3)))
                - &f * (&b__ * &e__ * &m_ + Atom::num(2) * &c__ * &d__ * (Atom::num(2) * &p_ + Atom::num(3)))
                - &e__ * (Atom::num(2) * &c__ * &f - &b__ * &g) * (&m_ + Atom::num(2) * &p_ + Atom::num(3)) * x_)
                .expand();
            let recursive = rubi_rhs_int(&(affine.pow(&m_ - Atom::num(1)) * quadratic.pow(raised_p) * expand_to_sum), x_);

            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_2176(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, e__, m_, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2176,
        source: "Int[(d_+e_.*x_)^m_.*Pq_*(a_+b_.*x_^2)^p_,x_Symbol] :=
          With[{Qx=PolynomialQuotient[Pq,a+b*x^2,x],
                R=Coeff[PolynomialRemainder[Pq,a+b*x^2,x],x,0],
                S=Coeff[PolynomialRemainder[Pq,a+b*x^2,x],x,1]},
          (d+e*x)^m*(a+b*x^2)^(p+1)*(a*S-b*R*x)/(2*a*b*(p+1)) +
          1/(2*a*b*(p+1)) \\[Star] Int[(d+e*x)^(m-1)*(a+b*x^2)^(p+1)*
            ExpandToSum[2*a*b*(p+1)*(d+e*x)*Qx-a*e*S*m+b*d*R*(2*p+3)+b*e*R*(m+2*p+3)*x,x],x]] /;
        FreeQ[{a,b,d,e},x] && PolyQ[Pq,x] && NeQ[b*d^2+a*e^2,0] && LtQ[p,-1] && GtQ[m,0] &&
          Not[IGtQ[m,0] && RationalQ[a,b,d,e] && (IntegerQ[p] || ILtQ[p+1/2,0])]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [d__, e__, pq__, a__, b__, m_, p_, x_],
        optional: [e__, b__, m_],
        when: {
            freeq!([a__, b__, d__, e__], x_)
                && poly_q(&pq__, x_)
                && neq!(&b__ * d__.pow(2) + &a__ * e__.pow(2), 0)
                && ltq!(p_, -1)
                && gtq!(m_, 0)
                && !(igtq!(m_, 0) && rationalq!([a__, b__, d__, e__]) && (integerq!(p_) || iltq!(&p_ + Atom::num(1) / Atom::num(2), 0)))
        },
        rhs: {
            let affine = &d__ + &e__ * x_;
            let quadratic = &a__ + &b__ * x_.pow(2);
            let raised_p = &p_ + Atom::num(1);
            let denominator = Atom::num(2) * &a__ * &b__ * &raised_p;
            if denominator.expand().is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let (capital_q, capital_r) = polynomial_quotient_remainder(&pq__, &quadratic, x_).rubi_rhs();
            let f = polynomial_coefficient(&capital_r, x_, 0).rubi_rhs();
            let g = polynomial_coefficient(&capital_r, x_, 1).rubi_rhs();
            let direct = affine.pow(&m_) * quadratic.pow(&raised_p) * (&a__ * &g - &b__ * &f * x_) / &denominator;
            let expand_to_sum = (Atom::num(2) * &a__ * &b__ * &raised_p * &affine * capital_q
                - &a__ * &e__ * &g * &m_
                + &b__ * &d__ * &f * (Atom::num(2) * &p_ + Atom::num(3))
                + &b__ * &e__ * &f * (&m_ + Atom::num(2) * &p_ + Atom::num(3)) * x_)
                .expand();
            let recursive = rubi_rhs_int(&(affine.pow(&m_ - Atom::num(1)) * quadratic.pow(raised_p) * expand_to_sum), x_);

            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_2177(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2177,
        source: "Int[(d_.+e_.*x_)^m_.*Pq_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          With[{Qx=PolynomialQuotient[(d+e*x)^m*Pq,a+b*x+c*x^2,x],
                R=Coeff[PolynomialRemainder[(d+e*x)^m*Pq,a+b*x+c*x^2,x],x,0],
                S=Coeff[PolynomialRemainder[(d+e*x)^m*Pq,a+b*x+c*x^2,x],x,1]},
          (b*R-2*a*S+(2*c*R-b*S)*x)*(a+b*x+c*x^2)^(p+1)/((p+1)*(b^2-4*a*c)) +
          1/((p+1)*(b^2-4*a*c)) \\[Star] Int[(d+e*x)^m*(a+b*x+c*x^2)^(p+1)*
            ExpandToSum[(p+1)*(b^2-4*a*c)*(d+e*x)^(-m)*Qx-(2*p+3)*(2*c*R-b*S)*(d+e*x)^(-m),x],x]] /;
        FreeQ[{a,b,c,d,e},x] && PolyQ[Pq,x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && LtQ[p,-1] && ILtQ[m,0]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [d__, e__, pq__, a__, b__, c__, m_, p_, x_],
        optional: [d__, e__, a__, b__, c__, m_],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && poly_q(&pq__, x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && neq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && ltq!(p_, -1)
                && iltq!(m_, 0)
        },
        rhs: {
            let m_i = integer_i64(&m_).rubi_rhs();
            let affine = &d__ + &e__ * x_;
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let discriminant = b__.pow(2) - Atom::num(4) * &a__ * &c__;
            let raised_p = &p_ + Atom::num(1);
            let denominator = &raised_p * &discriminant;
            if denominator.expand().is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let affine_power = affine.pow(-m_i);
            let (capital_q, capital_r) = polynomial_quotient_remainder_rational_dividend(
                &pq__,
                &affine_power,
                &quadratic,
                x_,
            ).rubi_rhs();
            let f = polynomial_coefficient(&capital_r, x_, 0).rubi_rhs();
            let g = polynomial_coefficient(&capital_r, x_, 1).rubi_rhs();
            let direct = rubi_simp(
                &((&b__ * &f
                    - Atom::num(2) * &a__ * &g
                    + (Atom::num(2) * &c__ * &f - &b__ * &g) * x_)
                    * quadratic.pow(&raised_p)
                    / &denominator),
                x_,
            );
            let expand_to_sum = rubi_expand_to_sum(
                &(&raised_p * &discriminant * &affine_power * capital_q
                    - (Atom::num(2) * &p_ + Atom::num(3))
                        * (Atom::num(2) * &c__ * &f - &b__ * &g)
                        * affine_power),
                x_,
            );
            let recursive = rubi_rhs_int(
                &(affine.pow(&m_) * quadratic.pow(raised_p) * expand_to_sum),
                x_,
            );

            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_2178(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, e__, m_, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2178,
        source: "Int[(d_+e_.*x_)^m_.*Pq_*(a_+b_.*x_^2)^p_,x_Symbol] :=
          With[{Qx=PolynomialQuotient[(d+e*x)^m*Pq,a+b*x^2,x],
                R=Coeff[PolynomialRemainder[(d+e*x)^m*Pq,a+b*x^2,x],x,0],
                S=Coeff[PolynomialRemainder[(d+e*x)^m*Pq,a+b*x^2,x],x,1]},
          (a*S-b*R*x)*(a+b*x^2)^(p+1)/(2*a*b*(p+1)) +
          1/(2*a*b*(p+1)) \\[Star] Int[(d+e*x)^m*(a+b*x^2)^(p+1)*
            ExpandToSum[2*a*b*(p+1)*(d+e*x)^(-m)*Qx+b*R*(2*p+3)*(d+e*x)^(-m),x],x]] /;
        FreeQ[{a,b,d,e},x] && PolyQ[Pq,x] && NeQ[b*d^2+a*e^2,0] && LtQ[p,-1] && ILtQ[m,0]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [d__, e__, pq__, a__, b__, m_, p_, x_],
        optional: [e__, b__, m_],
        when: {
            freeq!([a__, b__, d__, e__], x_)
                && poly_q(&pq__, x_)
                && neq!(&b__ * d__.pow(2) + &a__ * e__.pow(2), 0)
                && ltq!(p_, -1)
                && iltq!(m_, 0)
        },
        rhs: {
            let m_i = integer_i64(&m_).rubi_rhs();
            let affine = &d__ + &e__ * x_;
            let quadratic = &a__ + &b__ * x_.pow(2);
            let raised_p = &p_ + Atom::num(1);
            let denominator = Atom::num(2) * &a__ * &b__ * &raised_p;
            if denominator.expand().is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let affine_power = affine.pow(-m_i);
            let (capital_q, capital_r) = polynomial_quotient_remainder_rational_dividend(
                &pq__,
                &affine_power,
                &quadratic,
                x_,
            ).rubi_rhs();
            let f = polynomial_coefficient(&capital_r, x_, 0).rubi_rhs();
            let g = polynomial_coefficient(&capital_r, x_, 1).rubi_rhs();
            let direct = rubi_simp(
                &((&a__ * &g - &b__ * &f * x_) * quadratic.pow(&raised_p)
                    / &denominator),
                x_,
            );
            let expand_to_sum = rubi_expand_to_sum(
                &(Atom::num(2) * &a__ * &b__ * &raised_p * &affine_power * capital_q
                    + &b__
                        * &f
                        * (Atom::num(2) * &p_ + Atom::num(3))
                        * affine_power),
                x_,
            );
            let recursive = rubi_rhs_int(
                &(affine.pow(&m_) * quadratic.pow(raised_p) * expand_to_sum),
                x_,
            );

            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_2179(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2179,
        source: "Int[(d_.+e_.*x_)^m_.*Pq_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          With[{Qx=PolynomialQuotient[Pq,a+b*x+c*x^2,x],
                R=Coeff[PolynomialRemainder[Pq,a+b*x+c*x^2,x],x,0],
                S=Coeff[PolynomialRemainder[Pq,a+b*x+c*x^2,x],x,1]},
          (d+e*x)^(m+1)*(a+b*x+c*x^2)^(p+1)*(R*(b*c*d-b^2*e+2*a*c*e)-a*S*(2*c*d-b*e)+c*(R*(2*c*d-b*e)-S*(b*d-2*a*e))*x)/
            ((p+1)*(b^2-4*a*c)*(c*d^2-b*d*e+a*e^2)) +
          1/((p+1)*(b^2-4*a*c)*(c*d^2-b*d*e+a*e^2)) \\[Star] Int[(d+e*x)^m*(a+b*x+c*x^2)^(p+1)*
           ExpandToSum[(p+1)*(b^2-4*a*c)*(c*d^2-b*d*e+a*e^2)*Qx+
              R*(b*c*d*e*(2*p-m+2)+b^2*e^2*(p+m+2)-2*c^2*d^2*(2*p+3)-2*a*c*e^2*(m+2*p+3))-
              S*(a*e*(b*e-2*c*d*m+b*e*m)-b*d*(3*c*d-b*e+2*c*d*p-b*e*p))+
              c*e*(S*(b*d-2*a*e)-R*(2*c*d-b*e))*(m+2*p+4)*x,x],x]] /;
        FreeQ[{a,b,c,d,e,m},x] && PolyQ[Pq,x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && LtQ[p,-1] &&
          Not[IGtQ[m,0] && RationalQ[a,b,c,d,e] && (IntegerQ[p] || ILtQ[p+1/2,0])]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [d__, e__, pq__, a__, b__, c__, m_, p_, x_],
        optional: [d__, e__, a__, b__, c__, m_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_], x_)
                && poly_q(&pq__, x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && neq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && ltq!(p_, -1)
                && !(igtq!(m_, 0)
                    && rationalq!([a__, b__, c__, d__, e__])
                    && (integerq!(p_) || iltq!(&p_ + Atom::num(1) / Atom::num(2), 0)))
        },
        rhs: {
            let affine = &d__ + &e__ * x_;
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let raised_p = &p_ + Atom::num(1);
            let discriminant = b__.pow(2) - Atom::num(4) * &a__ * &c__;
            let invariant = &c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2);
            let denominator = &raised_p * &discriminant * &invariant;
            if denominator.expand().is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let (capital_q, capital_r) = polynomial_quotient_remainder(&pq__, &quadratic, x_).rubi_rhs();
            let f = polynomial_coefficient(&capital_r, x_, 0).rubi_rhs();
            let g = polynomial_coefficient(&capital_r, x_, 1).rubi_rhs();
            let direct_numerator = &f * (&b__ * &c__ * &d__ - b__.pow(2) * &e__ + Atom::num(2) * &a__ * &c__ * &e__)
                - &a__ * &g * (Atom::num(2) * &c__ * &d__ - &b__ * &e__)
                + &c__ * (&f * (Atom::num(2) * &c__ * &d__ - &b__ * &e__) - &g * (&b__ * &d__ - Atom::num(2) * &a__ * &e__)) * x_;
            let direct = affine.pow(&m_ + Atom::num(1)) * quadratic.pow(&raised_p) * direct_numerator / &denominator;
            let expand_to_sum = (&raised_p * &discriminant * &invariant * capital_q
                + &f
                    * (&b__ * &c__ * &d__ * &e__ * (Atom::num(2) * &p_ - &m_ + Atom::num(2))
                        + b__.pow(2) * e__.pow(2) * (&p_ + &m_ + Atom::num(2))
                        - Atom::num(2) * c__.pow(2) * d__.pow(2) * (Atom::num(2) * &p_ + Atom::num(3))
                        - Atom::num(2) * &a__ * &c__ * e__.pow(2) * (&m_ + Atom::num(2) * &p_ + Atom::num(3)))
                - &g
                    * (&a__ * &e__ * (&b__ * &e__ - Atom::num(2) * &c__ * &d__ * &m_ + &b__ * &e__ * &m_)
                        - &b__ * &d__ * (Atom::num(3) * &c__ * &d__ - &b__ * &e__ + Atom::num(2) * &c__ * &d__ * &p_ - &b__ * &e__ * &p_))
                + &c__ * &e__ * (&g * (&b__ * &d__ - Atom::num(2) * &a__ * &e__) - &f * (Atom::num(2) * &c__ * &d__ - &b__ * &e__))
                    * (&m_ + Atom::num(2) * &p_ + Atom::num(4))
                    * x_)
                .expand();
            let recursive = rubi_rhs_int(&(affine.pow(&m_) * quadratic.pow(raised_p) * expand_to_sum), x_);

            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_2180(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, e__, m_, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2180,
        source: "Int[(d_+e_.*x_)^m_.*Pq_*(a_+b_.*x_^2)^p_,x_Symbol] :=
          With[{Qx=PolynomialQuotient[Pq,a+b*x^2,x],
                R=Coeff[PolynomialRemainder[Pq,a+b*x^2,x],x,0],
                S=Coeff[PolynomialRemainder[Pq,a+b*x^2,x],x,1]},
          -(d+e*x)^(m+1)*(a+b*x^2)^(p+1)*(a*(e*R-d*S)+(b*d*R+a*e*S)*x)/(2*a*(p+1)*(b*d^2+a*e^2)) +
          1/(2*a*(p+1)*(b*d^2+a*e^2)) \\[Star] Int[(d+e*x)^m*(a+b*x^2)^(p+1)*
           ExpandToSum[2*a*(p+1)*(b*d^2+a*e^2)*Qx+b*d^2*R*(2*p+3)-a*e*(d*S*m-e*R*(m+2*p+3))+e*(b*d*R+a*e*S)*(m+2*p+4)*x,x],x]] /;
        FreeQ[{a,b,d,e,m},x] && PolyQ[Pq,x] && NeQ[b*d^2+a*e^2,0] && LtQ[p,-1] &&
          Not[IGtQ[m,0] && RationalQ[a,b,d,e] && (IntegerQ[p] || ILtQ[p+1/2,0])]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [d__, e__, pq__, a__, b__, m_, p_, x_],
        optional: [e__, b__, m_],
        when: {
            freeq!([a__, b__, d__, e__, m_], x_)
                && poly_q(&pq__, x_)
                && neq!(&b__ * d__.pow(2) + &a__ * e__.pow(2), 0)
                && ltq!(p_, -1)
                && !(igtq!(m_, 0) && rationalq!([a__, b__, d__, e__]) && (integerq!(p_) || iltq!(&p_ + Atom::num(1) / Atom::num(2), 0)))
        },
        rhs: {
            let affine = &d__ + &e__ * x_;
            let quadratic = &a__ + &b__ * x_.pow(2);
            let raised_p = &p_ + Atom::num(1);
            let invariant = &b__ * d__.pow(2) + &a__ * e__.pow(2);
            let denominator = Atom::num(2) * &a__ * &raised_p * &invariant;
            if denominator.expand().is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let (capital_q, capital_r) = polynomial_quotient_remainder(&pq__, &quadratic, x_).rubi_rhs();
            let f = polynomial_coefficient(&capital_r, x_, 0).rubi_rhs();
            let g = polynomial_coefficient(&capital_r, x_, 1).rubi_rhs();
            let direct_numerator = &a__ * (&e__ * &f - &d__ * &g) + (&b__ * &d__ * &f + &a__ * &e__ * &g) * x_;
            let direct = -affine.pow(&m_ + Atom::num(1)) * quadratic.pow(&raised_p) * direct_numerator / &denominator;
            let expand_to_sum = (Atom::num(2) * &a__ * &raised_p * &invariant * capital_q
                + &b__ * d__.pow(2) * &f * (Atom::num(2) * &p_ + Atom::num(3))
                - &a__ * &e__ * (&d__ * &g * &m_ - &e__ * &f * (&m_ + Atom::num(2) * &p_ + Atom::num(3)))
                + &e__ * (&b__ * &d__ * &f + &a__ * &e__ * &g) * (&m_ + Atom::num(2) * &p_ + Atom::num(4)) * x_)
                .expand();
            let recursive = rubi_rhs_int(&(affine.pow(&m_) * quadratic.pow(raised_p) * expand_to_sum), x_);

            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_2181(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2181,
        source: "Int[(d_.+e_.*x_)^m_*Pq_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          With[{Qx=PolynomialQuotient[Pq,d+e*x,x], R=PolynomialRemainder[Pq,d+e*x,x]},
          (e*R*(d+e*x)^(m+1)*(a+b*x+c*x^2)^(p+1))/((m+1)*(c*d^2-b*d*e+a*e^2)) +
          1/((m+1)*(c*d^2-b*d*e+a*e^2)) \\[Star] Int[(d+e*x)^(m+1)*(a+b*x+c*x^2)^p*
             ExpandToSum[(m+1)*(c*d^2-b*d*e+a*e^2)*Qx+c*d*R*(m+1)-b*e*R*(m+p+2)-c*e*R*(m+2*p+3)*x,x],x]] /;
        FreeQ[{a,b,c,d,e,p},x] && PolyQ[Pq,x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && LtQ[m,-1]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [d__, e__, pq__, a__, b__, c__, m_, p_, x_],
        optional: [d__, e__, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__, p_], x_)
                && poly_q(&pq__, x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && neq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && ltq!(m_, -1)
        },
        rhs: {
            let affine = &d__ + &e__ * x_;
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let invariant = &c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2);
            let denominator = (&m_ + Atom::num(1)) * &invariant;
            if denominator.expand().is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let (capital_q, capital_r) = polynomial_quotient_remainder(&pq__, &affine, x_).rubi_rhs();
            let direct = rubi_simp(
                &(&e__
                    * &capital_r
                    * affine.pow(&m_ + Atom::num(1))
                    * quadratic.pow(&p_ + Atom::num(1))
                    / &denominator),
                x_,
            );
            let expand_to_sum = rubi_expand_to_sum(
                &((&m_ + Atom::num(1)) * &invariant * capital_q
                    + &c__ * &d__ * &capital_r * (&m_ + Atom::num(1))
                    - &b__ * &e__ * &capital_r * (&m_ + &p_ + Atom::num(2))
                    - &c__
                        * &e__
                        * &capital_r
                        * (&m_ + Atom::num(2) * &p_ + Atom::num(3))
                        * x_),
                x_,
            );
            let recursive = rubi_rhs_int(
                &(affine.pow(&m_ + Atom::num(1))
                    * quadratic.pow(&p_)
                    * expand_to_sum),
                x_,
            );

            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_2182(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, e__, m_, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2182,
        source: "Int[(d_+e_.*x_)^m_*Pq_*(a_+b_.*x_^2)^p_,x_Symbol] :=
          With[{Qx=PolynomialQuotient[Pq,d+e*x,x], R=PolynomialRemainder[Pq,d+e*x,x]},
          e*R*(d+e*x)^(m+1)*(a+b*x^2)^(p+1)/((m+1)*(b*d^2+a*e^2)) +
          1/((m+1)*(b*d^2+a*e^2)) \\[Star] Int[(d+e*x)^(m+1)*(a+b*x^2)^p*
             ExpandToSum[(m+1)*(b*d^2+a*e^2)*Qx+b*d*R*(m+1)-b*e*R*(m+2*p+3)*x,x],x]] /;
        FreeQ[{a,b,d,e,p},x] && PolyQ[Pq,x] && NeQ[b*d^2+a*e^2,0] && LtQ[m,-1]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [d__, e__, pq__, a__, b__, m_, p_, x_],
        optional: [e__, b__],
        when: {
            freeq!([a__, b__, d__, e__, p_], x_)
                && poly_q(&pq__, x_)
                && neq!(&b__ * d__.pow(2) + &a__ * e__.pow(2), 0)
                && ltq!(m_, -1)
        },
        rhs: {
            let affine = &d__ + &e__ * x_;
            let quadratic = &a__ + &b__ * x_.pow(2);
            let invariant = &b__ * d__.pow(2) + &a__ * e__.pow(2);
            let denominator = (&m_ + Atom::num(1)) * &invariant;
            if denominator.expand().is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let (capital_q, capital_r) = polynomial_quotient_remainder(&pq__, &affine, x_).rubi_rhs();
            let direct = rubi_simp(
                &(&e__
                    * &capital_r
                    * affine.pow(&m_ + Atom::num(1))
                    * quadratic.pow(&p_ + Atom::num(1))
                    / &denominator),
                x_,
            );
            let expand_to_sum = rubi_expand_to_sum(
                &((&m_ + Atom::num(1)) * &invariant * capital_q
                    + &b__ * &d__ * &capital_r * (&m_ + Atom::num(1))
                    - &b__
                        * &e__
                        * &capital_r
                        * (&m_ + Atom::num(2) * &p_ + Atom::num(3))
                        * x_),
                x_,
            );
            let recursive = rubi_rhs_int(
                &(affine.pow(&m_ + Atom::num(1))
                    * quadratic.pow(&p_)
                    * expand_to_sum),
                x_,
            );

            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_2183(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, m_, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2183,
        source: "Int[x_^m_.*Pq_*(a_+b_.*x_^2)^p_,x_Symbol] :=
          Module[{q=Expon[Pq,x],k},
          Int[x^m*Sum[Coeff[Pq,x,2*k]*x^(2*k),{k,0,q/2}]*(a+b*x^2)^p,x] +
          Int[x^(m+1)*Sum[Coeff[Pq,x,2*k+1]*x^(2*k),{k,0,(q-1)/2}]*(a+b*x^2)^p,x]] /;
        FreeQ[{a,b,p},x] && PolyQ[Pq,x] && Not[PolyQ[Pq,x^2]] && IGtQ[m,-2] && Not[IntegerQ[2*p]]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: x_.pow(m_) * pq__ * (a__ + b__ * x_.pow(2)).pow(p_),
        with: [m_, pq__, a__, b__, p_, x_],
        optional: [m_, b__],
        when: {
            freeq!([a__, b__, p_], x_)
                && poly_q(&pq__, x_)
                && !rubi_poly_q_power(&pq__, x_, &Atom::num(2))
                && igtq!(m_, -2)
                && !integerq!(Atom::num(2) * &p_)
        },
        rhs: {
            let terms = collect_polynomial_terms(&pq__, x_).rubi_rhs();
            let quadratic = &a__ + &b__ * x_.pow(2);
            let mut even_sum = Atom::num(0);
            let mut odd_sum = Atom::num(0);
            for (degree, coefficient) in terms {
                if degree % 2 == 0 {
                    even_sum += coefficient * x_.pow(degree);
                } else {
                    odd_sum += coefficient * x_.pow(degree - 1);
                }
            }

            let first = rubi_rhs_int(&(x_.pow(&m_) * even_sum * quadratic.pow(&p_)), x_);
            let second = rubi_rhs_int(
                &(x_.pow(&m_ + Atom::num(1)) * odd_sum * quadratic.pow(p_)),
                x_,
            );

            first + second
        },
    ));
}

fn push_rules_rule_2184(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2184,
        source: "Int[(d_.+e_.*x_)^m_.*Pq_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          With[{q=Expon[Pq,x],f=Coeff[Pq,x,Expon[Pq,x]]},
          f*(d+e*x)^(m+q-1)*(a+b*x+c*x^2)^(p+1)/(c*e^(q-1)*(m+q+2*p+1)) +
          1/(c*e^q*(m+q+2*p+1)) \\[Star] Int[(d+e*x)^m*(a+b*x+c*x^2)^p*ExpandToSum[c*e^q*(m+q+2*p+1)*Pq-c*f*(m+q+2*p+1)*(d+e*x)^q-
            f*(d+e*x)^(q-2)*(b*d*e*(p+1)+a*e^2*(m+q-1)-c*d^2*(m+q+2*p+1)-e*(2*c*d-b*e)*(m+q+p)*x),x],x] /;
         GtQ[q,1] && NeQ[m+q+2*p+1,0]] /;
        FreeQ[{a,b,c,d,e,m,p},x] && PolyQ[Pq,x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] &&
          Not[IGtQ[m,0] && RationalQ[a,b,c,d,e] && (IntegerQ[p] || ILtQ[p+1/2,0])]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [d__, e__, pq__, a__, b__, c__, m_, p_, x_],
        optional: [d__, e__, a__, b__, c__, m_],
        when: {
            let q = polynomial_degree(&pq__, x_);
            freeq!([a__, b__, c__, d__, e__, m_, p_], x_)
                && poly_q(&pq__, x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && neq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && !(igtq!(m_, 0)
                    && rationalq!([a__, b__, c__, d__, e__])
                    && (integerq!(p_) || iltq!(&p_ + Atom::num(1) / Atom::num(2), 0)))
                && q.is_some_and(|q| q > 1 && neq!(&m_ + Atom::num(q) + Atom::num(2) * &p_ + Atom::num(1), 0))
        },
        rhs: {
            let (q, f) = polynomial_leading_term(&pq__, x_).rubi_rhs();
            if q <= 1 {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let q_atom = Atom::num(q);
            let balance = &m_ + &q_atom + Atom::num(2) * &p_ + Atom::num(1);
            let direct_denominator = &c__ * e__.pow(q - 1) * &balance;
            let recursive_denominator = &c__ * e__.pow(q) * &balance;

            let affine = &d__ + &e__ * x_;
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let direct = rubi_simp(
                &(&f
                    * affine.pow(&m_ + &q_atom - Atom::num(1))
                    * quadratic.pow(&p_ + Atom::num(1))
                    / &direct_denominator),
                x_,
            );
            let expand_to_sum = rubi_expand_to_sum(&(&c__ * e__.pow(q) * &balance * &pq__
                - &c__ * &f * &balance * affine.pow(q)
                - &f
                    * affine.pow(q - 2)
                    * (&b__ * &d__ * &e__ * (&p_ + Atom::num(1))
                        + &a__ * e__.pow(2) * (&m_ + &q_atom - Atom::num(1))
                        - &c__ * d__.pow(2) * &balance
                        - &e__ * (Atom::num(2) * &c__ * &d__ - &b__ * &e__) * (&m_ + &q_atom + &p_) * x_)), x_);
            let recursive = rubi_rhs_int(&(affine.pow(&m_) * quadratic.pow(&p_) * expand_to_sum), x_);

            rubi_simp(&(direct), x_)
                    + rubi_star(Atom::num(1) / recursive_denominator, recursive)
        },
    ));
}

fn push_rules_rule_2185(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, e__, m_, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2185,
        source: "Int[(d_+e_.*x_)^m_.*Pq_*(a_+b_.*x_^2)^p_,x_Symbol] :=
          With[{q=Expon[Pq,x],f=Coeff[Pq,x,Expon[Pq,x]]},
          f*(d+e*x)^(m+q-1)*(a+b*x^2)^(p+1)/(b*e^(q-1)*(m+q+2*p+1)) +
          1/(b*e^q*(m+q+2*p+1)) \\[Star] Int[(d+e*x)^m*(a+b*x^2)^p*
            ExpandToSum[b*e^q*(m+q+2*p+1)*Pq-b*f*(m+q+2*p+1)*(d+e*x)^q-f*(d+e*x)^(q-2)*(a*e^2*(m+q-1)-b*d^2*(m+q+2*p+1)-2*b*d*e*(m+q+p)*x),x],x] /;
         GtQ[q,1] && NeQ[m+q+2*p+1,0]] /;
        FreeQ[{a,b,d,e,m,p},x] && PolyQ[Pq,x] && NeQ[b*d^2+a*e^2,0] && Not[EqQ[d,0] && True] &&
          Not[IGtQ[m,0] && RationalQ[a,b,d,e] && (IntegerQ[p] || ILtQ[p+1/2,0])]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [d__, e__, pq__, a__, b__, m_, p_, x_],
        optional: [e__, b__, m_],
        when: {
            let q = polynomial_degree(&pq__, x_);
            freeq!([a__, b__, d__, e__, m_, p_], x_)
                && poly_q(&pq__, x_)
                && neq!(&b__ * d__.pow(2) + &a__ * e__.pow(2), 0)
                && neq!(d__, 0)
                && !(igtq!(m_, 0) && rationalq!([a__, b__, d__, e__]) && (integerq!(p_) || iltq!(&p_ + Atom::num(1) / Atom::num(2), 0)))
                && q.is_some_and(|q| q > 1 && neq!(&m_ + Atom::num(q) + Atom::num(2) * &p_ + Atom::num(1), 0))
        },
        rhs: {
            let (q, f) = polynomial_leading_term(&pq__, x_).rubi_rhs();
            if q <= 1 {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let q_atom = Atom::num(q);
            let balance = &m_ + &q_atom + Atom::num(2) * &p_ + Atom::num(1);
            let direct_denominator = &b__ * e__.pow(q - 1) * &balance;
            let recursive_denominator = &b__ * e__.pow(q) * &balance;

            let affine = &d__ + &e__ * x_;
            let quadratic = &a__ + &b__ * x_.pow(2);
            let direct = rubi_simp(
                &(&f
                    * affine.pow(&m_ + &q_atom - Atom::num(1))
                    * quadratic.pow(&p_ + Atom::num(1))
                    / &direct_denominator),
                x_,
            );
            let expand_to_sum = rubi_expand_to_sum(&(&b__ * e__.pow(q) * &balance * &pq__
                - &b__ * &f * &balance * affine.pow(q)
                - &f
                    * affine.pow(q - 2)
                    * (&a__ * e__.pow(2) * (&m_ + &q_atom - Atom::num(1))
                        - &b__ * d__.pow(2) * &balance
                        - Atom::num(2) * &b__ * &d__ * &e__ * (&m_ + &q_atom + &p_) * x_)), x_);
            let recursive = rubi_rhs_int(&(affine.pow(&m_) * quadratic.pow(&p_) * expand_to_sum), x_);

            rubi_simp(&(direct), x_)
                    + rubi_star(Atom::num(1) / recursive_denominator, recursive)
        },
    ));
}

fn push_rules_rule_2186(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2186,
        source: "Int[(d_.+e_.*x_)^m_.*Pq_*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
          With[{q=Expon[Pq,x]},
          Coeff[Pq,x,q]/e^q \\[Star] Int[(d+e*x)^(m+q)*(a+b*x+c*x^2)^p,x] +
          1/e^q \\[Star] Int[(d+e*x)^m*(a+b*x+c*x^2)^p*ExpandToSum[e^q*Pq-Coeff[Pq,x,q]*(d+e*x)^q,x],x]] /;
        FreeQ[{a,b,c,d,e,m,p},x] && PolyQ[Pq,x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] &&
          Not[IGtQ[m,0] && RationalQ[a,b,c,d,e] && (IntegerQ[p] || ILtQ[p+1/2,0])]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [d__, e__, pq__, a__, b__, c__, m_, p_, x_],
        optional: [d__, e__, a__, b__, c__, p_, m_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, p_], x_)
                && poly_q(&pq__, x_)
                && !e__.expand().is_zero()
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && neq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && !(igtq!(m_, 0)
                    && rationalq!([a__, b__, c__, d__, e__])
                    && (integerq!(p_) || iltq!(&p_ + Atom::num(1) / Atom::num(2), 0)))
        },
        rhs: {
            if e__.expand().is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let (q, coefficient) = polynomial_leading_term(&pq__, x_).rubi_rhs();
            let denominator = e__.pow(q);
            if denominator.expand().is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let affine = &d__ + &e__ * x_;
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let first = &coefficient * rubi_rhs_int(&(affine.pow(&m_ + Atom::num(q)) * quadratic.pow(&p_)), x_) / &denominator;
            let expand_to_sum = (&denominator * &pq__ - &coefficient * affine.pow(q)).expand();
            let second = rubi_rhs_int(&(affine.pow(&m_) * quadratic.pow(&p_) * expand_to_sum), x_) / denominator;

            rubi_star(Atom::num(1), first) + rubi_star(Atom::num(1), second)
        },
    ));
}

fn push_rules_rule_2187(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, e__, m_, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2187,
        source: "Int[(d_+e_.*x_)^m_.*Pq_*(a_+b_.*x_^2)^p_.,x_Symbol] :=
          With[{q=Expon[Pq,x]},
          Coeff[Pq,x,q]/e^q \\[Star] Int[(d+e*x)^(m+q)*(a+b*x^2)^p,x] +
          1/e^q \\[Star] Int[(d+e*x)^m*(a+b*x^2)^p*ExpandToSum[e^q*Pq-Coeff[Pq,x,q]*(d+e*x)^q,x],x]] /;
        FreeQ[{a,b,d,e,m,p},x] && PolyQ[Pq,x] && NeQ[b*d^2+a*e^2,0] &&
          Not[IGtQ[m,0] && RationalQ[a,b,d,e] && (IntegerQ[p] || ILtQ[p+1/2,0])]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [d__, e__, pq__, a__, b__, m_, p_, x_],
        optional: [e__, b__, p_, m_],
        when: {
            freeq!([a__, b__, d__, e__, m_, p_], x_)
                && poly_q(&pq__, x_)
                && !e__.expand().is_zero()
                && neq!(&b__ * d__.pow(2) + &a__ * e__.pow(2), 0)
                && !(igtq!(m_, 0) && rationalq!([a__, b__, d__, e__]) && (integerq!(p_) || iltq!(&p_ + Atom::num(1) / Atom::num(2), 0)))
        },
        rhs: {
            if e__.expand().is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let (q, coefficient) = polynomial_leading_term(&pq__, x_).rubi_rhs();
            let denominator = e__.pow(q);
            if denominator.expand().is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let affine = &d__ + &e__ * x_;
            let quadratic = &a__ + &b__ * x_.pow(2);
            let first = &coefficient * rubi_rhs_int(&(affine.pow(&m_ + Atom::num(q)) * quadratic.pow(&p_)), x_) / &denominator;
            let expand_to_sum = (&denominator * &pq__ - &coefficient * affine.pow(q)).expand();
            let second = rubi_rhs_int(&(affine.pow(&m_) * quadratic.pow(&p_) * expand_to_sum), x_) / denominator;

            rubi_star(Atom::num(1), first) + rubi_star(Atom::num(1), second)
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
    let m_ = symbols.m_;
    let p_ = symbols.p_;
    let pq__ = symbols.pq__;
    let x_ = symbols.x_;
    (d__ + e__ * x_).pow(m_) * pq__ * (a__ + b__ * x_ + c__ * x_.pow(2)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let m_ = symbols.m_;
    let p_ = symbols.p_;
    let pq__ = symbols.pq__;
    let x_ = symbols.x_;
    (d__ + e__ * x_).pow(m_) * pq__ * (a__ + b__ * x_.pow(2)).pow(p_)
}
