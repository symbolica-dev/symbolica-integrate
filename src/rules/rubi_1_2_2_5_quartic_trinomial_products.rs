use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_2200(rules);
    push_rules_rule_2201(rules);
    push_rules_rule_2202(rules);
    push_rules_rule_2203(rules);
    push_rules_rule_2204(rules);
    push_rules_rule_2205(rules);
    push_rules_rule_2206(rules);
    push_rules_rule_2207(rules);
}

fn push_rules_rule_2200(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, p_, px__, x_);
    rules.push(rubi_rule!(
        order: 2200,
        source: "Int[Px_*(a_+b_.*x_^2+c_.*x_^4)^p_.,x_Symbol] :=
          Int[ExpandIntegrand[Px*(a+b*x^2+c*x^4)^p,x],x] /;
        FreeQ[{a,b,c},x] && PolyQ[Px,x] && IGtQ[p,0]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [px__, a__, b__, c__, p_, x_],
        optional: [b__, c__, p_],
        when: { freeq!([a__, b__, c__], x_) && rubi_poly_q(&px__, x_) && igtq!(p_, 0) },
        rhs: {
            let integrand = &px__ * (&a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4)).pow(&p_);
            let expanded = rubi_expand_integrand(&integrand, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_2201(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, p_, px__, x_);
    rules.push(rubi_rule!(
        order: 2201,
        source: "Int[Px_*(a_+b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
          With[{m=Expon[Px,x,Min]},
          Int[x^m*ExpandToSum[Px/x^m,x]*(a+b*x^2+c*x^4)^p,x] /;
         GtQ[m,0] && Not[MatchQ[Px,x^m*u_.]]] /;
        FreeQ[{a,b,c,p},x] && PolyQ[Px,x]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [px__, a__, b__, c__, p_, x_],
        optional: [b__, c__],
        when: {
            freeq!([a__, b__, c__, p_], x_)
                && rubi_poly_q(&px__, x_)
                && rubi_minimum_monomial_exponent(&px__, x_)
                    .is_some_and(|m| gtq!(Atom::num(m), 0))
                && !visible_integer_power_of_variable_factor(&px__, x_)
        },
        rhs: {
            let m = rubi_minimum_monomial_exponent(&px__, x_).rubi_rhs();
            let quotient = rubi_expand_to_sum(&(&px__ / x_.pow(m)), x_);
            let integrand = x_.pow(m)
                * quotient
                * (&a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4)).pow(&p_);
            rubi_rhs_int(&integrand, x_)
        },
    ));
}

fn push_rules_rule_2202(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, p_, pn__, x_);
    rules.push(rubi_rule!(
        order: 2202,
        source: "Int[Pn_*(a_+b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
          Module[{n=Expon[Pn,x],k},
          Int[Sum[Coeff[Pn,x,2*k]*x^(2*k),{k,0,n/2}]*(a+b*x^2+c*x^4)^p,x] +
          Int[x*Sum[Coeff[Pn,x,2*k+1]*x^(2*k),{k,0,(n-1)/2}]*(a+b*x^2+c*x^4)^p,x]] /;
        FreeQ[{a,b,c,p},x] && PolyQ[Pn,x] && Not[PolyQ[Pn,x^2]]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern: pn__ * (a__ + b__ * x_.pow(2) + c__ * x_.pow(4)).pow(p_),
        with: [pn__, a__, b__, c__, p_, x_],
        optional: [b__, c__],
        when: {
            freeq!([a__, b__, c__, p_], x_)
                && rubi_poly_q(&pn__, x_)
                && !rubi_poly_q_power(&pn__, x_, &Atom::num(2))
        },
        rhs: {
            let q = rubi_expon(&pn__, x_).rubi_rhs();
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);

            let mut even_sum = Atom::num(0);
            for k in 0..=(q / 2) {
                even_sum += rubi_coeff(&pn__, x_, 2 * k).rubi_rhs() * x_.pow(2 * k);
            }

            let mut odd_sum = Atom::num(0);
            if q >= 1 {
                for k in 0..=((q - 1) / 2) {
                    odd_sum += rubi_coeff(&pn__, x_, 2 * k + 1).rubi_rhs() * x_.pow(2 * k);
                }
            }

            let first = rubi_rhs_int(&(even_sum * quartic.pow(&p_)), x_);
            let second = rubi_rhs_int(&(x_ * odd_sum * quartic.pow(&p_)), x_);

            first + second
        },
    ));
}

fn push_rules_rule_2203(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, p_, px__, x_);
    rules.push(rubi_rule!(
        order: 2203,
        source: "Int[Px_*(a_+b_.*x_^2+c_.*x_^4)^p_.,x_Symbol] :=
          With[{d=Coeff[Px,x,0],e=Coeff[Px,x,2],f=Coeff[Px,x,4]},
          d*x*(a+b*x^2+c*x^4)^(p+1)/a /;
         EqQ[a*e-b*d*(2*p+3),0] && EqQ[a*f-c*d*(4*p+5),0]] /;
        FreeQ[{a,b,c,p},x] && PolyQ[Px,x^2] && EqQ[Expon[Px,x],4]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [px__, a__, b__, c__, p_, x_],
        optional: [b__, c__, p_],
        when: {
            if let (Some(d), Some(e), Some(f)) = (
                rubi_coeff(&px__, x_, 0),
                rubi_coeff(&px__, x_, 2),
                rubi_coeff(&px__, x_, 4),
            ) {
                freeq!([a__, b__, c__, p_], x_)
                    && rubi_poly_q_power(&px__, x_, &Atom::num(2))
                    && rubi_expon(&px__, x_).is_some_and(|q| eqq!(Atom::num(q), 4))
                    && eqq!(&a__ * &e - &b__ * &d * (Atom::num(2) * &p_ + Atom::num(3)), 0)
                    && eqq!(&a__ * &f - &c__ * &d * (Atom::num(4) * &p_ + Atom::num(5)), 0)
            } else {
                false
            }
        },
        rhs: {
            let d = rubi_coeff(&px__, x_, 0).rubi_rhs();
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);

            d * x_ * quartic.pow(&p_ + Atom::num(1)) / &a__
        },
    ));
}

fn push_rules_rule_2204(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, p_, px__, x_);
    rules.push(rubi_rule!(
        order: 2204,
        source: "Int[Px_*(a_+b_.*x_^2+c_.*x_^4)^p_.,x_Symbol] :=
          With[{d=Coeff[Px,x,0],e=Coeff[Px,x,2],f=Coeff[Px,x,4],g=Coeff[Px,x,6]},
          x*(3*a*d+(a*e-b*d*(2*p+3))*x^2)*(a+b*x^2+c*x^4)^(p+1)/(3*a^2) /;
         EqQ[3*a^2*g-c*(4*p+7)*(a*e-b*d*(2*p+3)),0] && EqQ[3*a^2*f-3*a*c*d*(4*p+5)-b*(2*p+5)*(a*e-b*d*(2*p+3)),0]] /;
        FreeQ[{a,b,c,p},x] && PolyQ[Px,x^2] && EqQ[Expon[Px,x],6]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [px__, a__, b__, c__, p_, x_],
        optional: [b__, c__, p_],
        when: {
            if let (Some(d), Some(e), Some(f), Some(g)) = (
                rubi_coeff(&px__, x_, 0),
                rubi_coeff(&px__, x_, 2),
                rubi_coeff(&px__, x_, 4),
                rubi_coeff(&px__, x_, 6),
            ) {
                freeq!([a__, b__, c__, p_], x_)
                    && rubi_poly_q_power(&px__, x_, &Atom::num(2))
                    && rubi_expon(&px__, x_).is_some_and(|q| eqq!(Atom::num(q), 6))
                    && eqq!(
                        Atom::num(3) * a__.pow(2) * &g
                            - &c__
                                * (Atom::num(4) * &p_ + Atom::num(7))
                                * (&a__ * &e - &b__ * &d * (Atom::num(2) * &p_ + Atom::num(3))),
                        0
                    )
                    && eqq!(
                        Atom::num(3) * a__.pow(2) * &f
                            - Atom::num(3)
                                * &a__
                                * &c__
                                * &d
                                * (Atom::num(4) * &p_ + Atom::num(5))
                            - &b__
                                * (Atom::num(2) * &p_ + Atom::num(5))
                                * (&a__ * &e - &b__ * &d * (Atom::num(2) * &p_ + Atom::num(3))),
                        0
                    )
            } else {
                false
            }
        },
        rhs: {
            let d = rubi_coeff(&px__, x_, 0).rubi_rhs();
            let e = rubi_coeff(&px__, x_, 2).rubi_rhs();
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);

            x_
                    * (Atom::num(3) * &a__ * &d
                        + (&a__ * &e - &b__ * &d * (Atom::num(2) * &p_ + Atom::num(3)))
                            * x_.pow(2))
                    * quartic.pow(&p_ + Atom::num(1))
                    / (Atom::num(3) * a__.pow(2))
        },
    ));
}

fn push_rules_rule_2205(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, px__, x_);
    rules.push(rubi_rule!(
        order: 2205,
        source: "Int[Px_/(a_+b_.*x_^2+c_.*x_^4),x_Symbol] :=
          Int[ExpandIntegrand[Px/(a+b*x^2+c*x^4),x],x] /;
        FreeQ[{a,b,c},x] && PolyQ[Px,x^2] && Expon[Px,x^2]>1",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern: px__ / (a__ + b__ * x_.pow(2) + c__ * x_.pow(4)),
        with: [px__, a__, b__, c__, x_],
        optional: [b__, c__],
        when: {
            freeq!([a__, b__, c__], x_)
                && rubi_poly_q_power(&px__, x_, &Atom::num(2))
                && rubi_expon_power(&px__, x_, &Atom::num(2)).is_some_and(|q| q > 1)
        },
        rhs: {
            let integrand = &px__ / (&a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4));
            let expanded = rubi_expand_integrand(&integrand, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_2206(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, p_, px__, x_);
    rules.push(rubi_rule!(
        order: 2206,
        source: "Int[Px_*(a_+b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
          With[{d=Coeff[PolynomialRemainder[Px,a+b*x^2+c*x^4,x],x,0],
                e=Coeff[PolynomialRemainder[Px,a+b*x^2+c*x^4,x],x,2]},
          x*(a+b*x^2+c*x^4)^(p+1)*(a*b*e-d*(b^2-2*a*c)-c*(b*d-2*a*e)*x^2)/(2*a*(p+1)*(b^2-4*a*c)) +
          1/(2*a*(p+1)*(b^2-4*a*c)) \\[Star] Int[(a+b*x^2+c*x^4)^(p+1)*
            ExpandToSum[2*a*(p+1)*(b^2-4*a*c)*PolynomialQuotient[Px,a+b*x^2+c*x^4,x]+
              b^2*d*(2*p+3)-2*a*c*d*(4*p+5)-a*b*e+c*(4*p+7)*(b*d-2*a*e)*x^2,x],x]] /;
        FreeQ[{a,b,c},x] && PolyQ[Px,x^2] && Expon[Px,x^2]>1 && NeQ[b^2-4*a*c,0] && LtQ[p,-1]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [px__, a__, b__, c__, p_, x_],
        optional: [b__, c__],
        when: {
            freeq!([a__, b__, c__], x_)
                && rubi_poly_q_power(&px__, x_, &Atom::num(2))
                && rubi_expon_power(&px__, x_, &Atom::num(2)).is_some_and(|q| q > 1)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && ltq!(p_, -1)
        },
        rhs: {
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let polynomial_remainder = rubi_polynomial_remainder(&px__, &quartic, x_).rubi_rhs();
            let d = rubi_coeff(&polynomial_remainder, x_, 0).rubi_rhs();
            let e = rubi_coeff(&polynomial_remainder, x_, 2).rubi_rhs();
            let polynomial_quotient = rubi_polynomial_quotient(&px__, &quartic, x_).rubi_rhs();
            let discriminant = b__.pow(2) - Atom::num(4) * &a__ * &c__;
            let denominator = Atom::num(2) * &a__ * (&p_ + Atom::num(1)) * &discriminant;

            let direct = x_
                * quartic.pow(&p_ + Atom::num(1))
                * (&a__ * &b__ * &e
                    - &d * (b__.pow(2) - Atom::num(2) * &a__ * &c__)
                    - &c__ * (&b__ * &d - Atom::num(2) * &a__ * &e) * x_.pow(2))
                / &denominator;

            let expand_to_sum = rubi_expand_to_sum(
                &(Atom::num(2)
                    * &a__
                    * (&p_ + Atom::num(1))
                    * &discriminant
                    * polynomial_quotient
                    + b__.pow(2) * &d * (Atom::num(2) * &p_ + Atom::num(3))
                    - Atom::num(2) * &a__ * &c__ * &d * (Atom::num(4) * &p_ + Atom::num(5))
                    - &a__ * &b__ * &e
                    + &c__
                        * (Atom::num(4) * &p_ + Atom::num(7))
                        * (&b__ * &d - Atom::num(2) * &a__ * &e)
                        * x_.pow(2)),
                x_,
            );
            let recursive_integrand = quartic.pow(&p_ + Atom::num(1)) * expand_to_sum;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_)
                    + rubi_star(Atom::num(1) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_2207(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, p_, px__, x_);
    rules.push(rubi_rule!(
        order: 2207,
        source: "Int[Px_*(a_+b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
          With[{n=Expon[Px,x^2],e=Coeff[Px,x^2,Expon[Px,x^2]]},
          e*x^(2*n-3)*(a+b*x^2+c*x^4)^(p+1)/(c*(2*n+4*p+1)) +
          1/(c*(2*n+4*p+1)) \\[Star] Int[(a+b*x^2+c*x^4)^p*
            ExpandToSum[c*(2*n+4*p+1)*Px-a*e*(2*n-3)*x^(2*n-4)-b*e*(2*n+2*p-1)*x^(2*n-2)-c*e*(2*n+4*p+1)*x^(2*n),x],x]] /;
        FreeQ[{a,b,c,p},x] && PolyQ[Px,x^2] && Expon[Px,x^2]>1 && NeQ[b^2-4*a*c,0] && Not[LtQ[p,-1]]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [px__, a__, b__, c__, p_, x_],
        optional: [b__, c__],
        when: {
            freeq!([a__, b__, c__, p_], x_)
                && rubi_poly_q_power(&px__, x_, &Atom::num(2))
                && rubi_expon_power(&px__, x_, &Atom::num(2)).is_some_and(|q| q > 1)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && !ltq!(p_, -1)
        },
        rhs: {
            let q = rubi_expon_power(&px__, x_, &Atom::num(2)).rubi_rhs();
            let e = rubi_coeff_power(&px__, x_, &Atom::num(2), q).rubi_rhs();
            let q_atom = Atom::num(q);
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let denominator = &c__ * (Atom::num(2) * &q_atom + Atom::num(4) * &p_ + Atom::num(1));

            let direct = &e
                * x_.pow(Atom::num(2) * &q_atom - Atom::num(3))
                * quartic.pow(&p_ + Atom::num(1))
                / &denominator;

            let expand_to_sum = rubi_expand_to_sum(
                &(&c__ * (Atom::num(2) * &q_atom + Atom::num(4) * &p_ + Atom::num(1)) * &px__
                    - &a__
                        * &e
                        * (Atom::num(2) * &q_atom - Atom::num(3))
                        * x_.pow(Atom::num(2) * &q_atom - Atom::num(4))
                    - &b__
                        * &e
                        * (Atom::num(2) * &q_atom + Atom::num(2) * &p_ - Atom::num(1))
                        * x_.pow(Atom::num(2) * &q_atom - Atom::num(2))
                    - &c__
                        * &e
                        * (Atom::num(2) * &q_atom + Atom::num(4) * &p_ + Atom::num(1))
                        * x_.pow(Atom::num(2) * &q_atom)),
                x_,
            );
            let recursive_integrand = quartic.pow(&p_) * expand_to_sum;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_)
                    + rubi_star(Atom::num(1) / denominator, recursive)
        },
    ));
}

// Generated shared pattern builders.

#[inline(never)]
fn rubi_shared_pattern_0(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let p_ = symbols.p_;
    let px__ = symbols.px__;
    let x_ = symbols.x_;
    px__ * (a__ + b__ * x_.pow(2) + c__ * x_.pow(4)).pow(p_)
}
