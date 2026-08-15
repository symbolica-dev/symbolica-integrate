use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_2193(rules);
    push_rules_rule_2194(rules);
    push_rules_rule_2195(rules);
    push_rules_rule_2196(rules);
    push_rules_rule_2197(rules);
    push_rules_rule_2198(rules);
    push_rules_rule_2199(rules);
}

fn push_rules_rule_2193(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2193,
        source: "Int[Pq_*(d_.*x_)^m_.*(a_+b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
          Module[{q=Expon[Pq,x],k},
          Int[Sum[Coeff[Pq,x,2*k]*x^(2*k),{k,0,q/2+1}]*(d*x)^m*(a+b*x^2+c*x^4)^p,x] +
          1/d \\[Star] Int[Sum[Coeff[Pq,x,2*k+1]*x^(2*k),{k,0,(q+1)/2}]*(d*x)^(m+1)*(a+b*x^2+c*x^4)^p,x]] /;
        FreeQ[{a,b,c,d,m,p},x] && PolyQ[Pq,x] && Not[PolyQ[Pq,x^2]]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [d__, m_, pq__, a__, b__, c__, p_, x_],
        optional: [d__, m_, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, m_, p_], x_)
                && rubi_poly_q(&pq__, x_)
                && !rubi_poly_q_power(&pq__, x_, &Atom::num(2))
        },
        rhs: {
            let q = rubi_expon(&pq__, x_).rubi_rhs();
            let dx = &d__ * x_;
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);

            let mut even_sum = Atom::num(0);
            for k in 0..=(q / 2 + 1) {
                even_sum += rubi_coeff(&pq__, x_, 2 * k).rubi_rhs() * x_.pow(2 * k);
            }

            let mut odd_sum = Atom::num(0);
            for k in 0..=((q - 1) / 2 + 1) {
                odd_sum += rubi_coeff(&pq__, x_, 2 * k + 1).rubi_rhs() * x_.pow(2 * k);
            }

            let first = rubi_rhs_int(&(dx.pow(&m_) * even_sum * quartic.pow(&p_)), x_);
            let second = rubi_rhs_int(
                &(dx.pow(&m_ + Atom::num(1)) * odd_sum * quartic.pow(&p_)),
                x_,
            );

            first + rubi_star(Atom::num(1) / &d__, second)
        },
    ));
}

fn push_rules_rule_2194(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2194,
        source: "Int[x_^m_.*Pq_*(a_+b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
          1/2 \\[Star] Subst[Int[x^((m-1)/2)*SubstFor[x^2,Pq,x]*(a+b*x+c*x^2)^p,x],x,x^2] /;
        FreeQ[{a,b,c,p},x] && PolyQ[Pq,x^2] && IntegerQ[(m-1)/2]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [m_, pq__, a__, b__, c__, p_, x_],
        optional: [m_, b__, c__],
        when: {
            freeq!([a__, b__, c__, p_], x_)
                && rubi_poly_q_power(&pq__, x_, &Atom::num(2))
                && integerq!((&m_ - 1) / 2)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let sub_atom = Atom::var(sub);
            let subst_for = rubi_subst_for_power(&pq__, x_, &Atom::num(2), sub).rubi_rhs();
            let transformed_integrand = sub_atom.pow((&m_ - 1) / 2)
                * subst_for
                * (&a__ + &b__ * &sub_atom + &c__ * sub_atom.pow(2)).pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);
            let substituted = rubi_subst(&transformed, sub, x_.pow(2));

            rubi_star(Atom::num(1) / 2, substituted)
        },
    ));
}

fn push_rules_rule_2195(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2195,
        source: "Int[(d_.*x_)^m_.*Pq_*(a_+b_.*x_^2+c_.*x_^4)^p_.,x_Symbol] :=
          Int[ExpandIntegrand[(d*x)^m*Pq*(a+b*x^2+c*x^4)^p,x],x] /;
        FreeQ[{a,b,c,d,m},x] && PolyQ[Pq,x^2] && IGtQ[p,-2]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [d__, m_, pq__, a__, b__, c__, p_, x_],
        optional: [d__, m_, b__, c__, p_],
        when: {
            freeq!([a__, b__, c__, d__, m_], x_)
                && rubi_poly_q_power(&pq__, x_, &Atom::num(2))
                && igtq!(p_, -2)
        },
        rhs: {
            let integrand = (&d__ * x_).pow(&m_)
                * &pq__
                * (&a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4)).pow(&p_);
            let expanded = rubi_expand_integrand(&integrand, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_2196(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2196,
        source: "Int[(d_.*x_)^m_.*Pq_*(a_+b_.*x_^2+c_.*x_^4)^p_.,x_Symbol] :=
          With[{e=Coeff[Pq,x,0],f=Coeff[Pq,x,2],g=Coeff[Pq,x,4]},
          e*(d*x)^(m+1)*(a+b*x^2+c*x^4)^(p+1)/(a*d*(m+1)) /;
         EqQ[a*f*(m+1)-b*e*(m+2*p+3),0] && EqQ[a*g*(m+1)-c*e*(m+4*p+5),0] && NeQ[m,-1]] /;
        FreeQ[{a,b,c,d,m,p},x] && PolyQ[Pq,x^2] && EqQ[Expon[Pq,x],4]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [d__, m_, pq__, a__, b__, c__, p_, x_],
        optional: [d__, m_, b__, c__, p_],
        when: {
            if let (Some(e), Some(f), Some(g)) = (
                rubi_coeff(&pq__, x_, 0),
                rubi_coeff(&pq__, x_, 2),
                rubi_coeff(&pq__, x_, 4),
            ) {
                freeq!([a__, b__, c__, d__, m_, p_], x_)
                    && rubi_poly_q_power(&pq__, x_, &Atom::num(2))
                    && rubi_expon(&pq__, x_).is_some_and(|q| eqq!(Atom::num(q), 4))
                    && eqq!(
                        &a__ * &f * (&m_ + Atom::num(1))
                            - &b__ * &e * (&m_ + Atom::num(2) * &p_ + Atom::num(3)),
                        0
                    )
                    && eqq!(
                        &a__ * &g * (&m_ + Atom::num(1))
                            - &c__ * &e * (&m_ + Atom::num(4) * &p_ + Atom::num(5)),
                        0
                    )
                    && neq!(m_, -1)
            } else {
                false
            }
        },
        rhs: {
            let e = rubi_coeff(&pq__, x_, 0).rubi_rhs();
            let dx = &d__ * x_;
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);

            e * dx.pow(&m_ + Atom::num(1)) * quartic.pow(&p_ + Atom::num(1))
                    / (&a__ * &d__ * (&m_ + Atom::num(1)))
        },
    ));
}

fn push_rules_rule_2197(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2197,
        source: "Int[x_^m_*Pq_*(a_+b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
          With[{Qx=PolynomialQuotient[x^m*Pq,a+b*x^2+c*x^4,x],
                d=Coeff[PolynomialRemainder[x^m*Pq,a+b*x^2+c*x^4,x],x,0],
                e=Coeff[PolynomialRemainder[x^m*Pq,a+b*x^2+c*x^4,x],x,2]},
          x*(a+b*x^2+c*x^4)^(p+1)*(a*b*e-d*(b^2-2*a*c)-c*(b*d-2*a*e)*x^2)/(2*a*(p+1)*(b^2-4*a*c)) +
          1/(2*a*(p+1)*(b^2-4*a*c)) \\[Star] Int[(a+b*x^2+c*x^4)^(p+1)*
            ExpandToSum[2*a*(p+1)*(b^2-4*a*c)*Qx+b^2*d*(2*p+3)-2*a*c*d*(4*p+5)-a*b*e+c*(4*p+7)*(b*d-2*a*e)*x^2,x],x]] /;
        FreeQ[{a,b,c},x] && PolyQ[Pq,x^2] && GtQ[Expon[Pq,x^2],1] && NeQ[b^2-4*a*c,0] && LtQ[p,-1] && IGtQ[m/2,0]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [m_, pq__, a__, b__, c__, p_, x_],
        optional: [b__, c__],
        when: {
            freeq!([a__, b__, c__], x_)
                && rubi_poly_q_power(&pq__, x_, &Atom::num(2))
                && rubi_expon_power(&pq__, x_, &Atom::num(2)).is_some_and(|q| gtq!(Atom::num(q), 1))
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && ltq!(p_, -1)
                && igtq!(&m_ / Atom::num(2), 0)
        },
        rhs: {
            let xm_pq = x_.pow(&m_) * &pq__;
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let polynomial_remainder = rubi_polynomial_remainder(&xm_pq, &quartic, x_).rubi_rhs();
            let d = rubi_coeff(&polynomial_remainder, x_, 0).rubi_rhs();
            let e = rubi_coeff(&polynomial_remainder, x_, 2).rubi_rhs();
            let polynomial_quotient = rubi_polynomial_quotient(&xm_pq, &quartic, x_).rubi_rhs();
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

fn push_rules_rule_2198(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2198,
        source: "Int[x_^m_*Pq_*(a_+b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
          With[{Qx=PolynomialQuotient[x^m*Pq,a+b*x^2+c*x^4,x],
                d=Coeff[PolynomialRemainder[x^m*Pq,a+b*x^2+c*x^4,x],x,0],
                e=Coeff[PolynomialRemainder[x^m*Pq,a+b*x^2+c*x^4,x],x,2]},
          x*(a+b*x^2+c*x^4)^(p+1)*(a*b*e-d*(b^2-2*a*c)-c*(b*d-2*a*e)*x^2)/(2*a*(p+1)*(b^2-4*a*c)) +
          1/(2*a*(p+1)*(b^2-4*a*c)) \\[Star] Int[x^m*(a+b*x^2+c*x^4)^(p+1)*
            ExpandToSum[2*a*(p+1)*(b^2-4*a*c)*x^(-m)*Qx+(b^2*d*(2*p+3)-2*a*c*d*(4*p+5)-a*b*e)*x^(-m)+c*(4*p+7)*(b*d-2*a*e)*x^(2-m),x],x]] /;
        FreeQ[{a,b,c},x] && PolyQ[Pq,x^2] && GtQ[Expon[Pq,x^2],1] && NeQ[b^2-4*a*c,0] && LtQ[p,-1] && ILtQ[m/2,0]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [m_, pq__, a__, b__, c__, p_, x_],
        optional: [b__, c__],
        when: {
            freeq!([a__, b__, c__], x_)
                && rubi_poly_q_power(&pq__, x_, &Atom::num(2))
                && rubi_expon_power(&pq__, x_, &Atom::num(2)).is_some_and(|q| gtq!(Atom::num(q), 1))
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && ltq!(p_, -1)
                && iltq!(&m_ / Atom::num(2), 0)
        },
        rhs: {
            let xm_pq = x_.pow(&m_) * &pq__;
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let polynomial_remainder = rubi_polynomial_remainder(&xm_pq, &quartic, x_).rubi_rhs();
            let d = rubi_coeff(&polynomial_remainder, x_, 0).rubi_rhs();
            let e = rubi_coeff(&polynomial_remainder, x_, 2).rubi_rhs();
            let polynomial_quotient = rubi_polynomial_quotient(&xm_pq, &quartic, x_).rubi_rhs();
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
                    * x_.pow(-&m_)
                    * polynomial_quotient
                    + (b__.pow(2) * &d * (Atom::num(2) * &p_ + Atom::num(3))
                        - Atom::num(2) * &a__ * &c__ * &d * (Atom::num(4) * &p_ + Atom::num(5))
                        - &a__ * &b__ * &e)
                        * x_.pow(-&m_)
                    + &c__
                        * (Atom::num(4) * &p_ + Atom::num(7))
                        * (&b__ * &d - Atom::num(2) * &a__ * &e)
                        * x_.pow(Atom::num(2) - &m_)),
                x_,
            );
            let recursive_integrand =
                x_.pow(&m_) * quartic.pow(&p_ + Atom::num(1)) * expand_to_sum;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_)
                    + rubi_star(Atom::num(1) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_2199(rules: &mut Vec<RubiRule>) {
    rubi_symb!(px__, a__, b__, c__, d__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 2199,
        source: "Int[Px_*(d_.*x_)^m_.*(a_+b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
          With[{q=Expon[Px,x^2]},
          Coeff[Px,x^2,q]*(d*x)^(m+2*q-3)*(a+b*x^2+c*x^4)^(p+1)/(c*d^(2*q-3)*(m+4*p+2*q+1)) +
          Int[(d*x)^m*(a+b*x^2+c*x^4)^p*
            ExpandToSum[Px-Coeff[Px,x^2,q]*x^(2*q)-Coeff[Px,x^2,q]*(a*(m+2*q-3)*x^(2*(q-2))+b*(m+2*p+2*q-1)*x^(2*(q-1)))/(c*(m+4*p+2*q+1)),x],x] /;
         GtQ[q,1] && NeQ[m+4*p+2*q+1,0]] /;
        FreeQ[{a,b,c,d,m,p},x] && PolyQ[Px,x^2] && NeQ[b^2-4*a*c,0]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern: px__
            * (d__ * x_).pow(m_)
            * (a__ + b__ * x_.pow(2) + c__ * x_.pow(4)).pow(p_),
        with: [px__, d__, m_, a__, b__, c__, p_, x_],
        optional: [d__, m_, b__, c__],
        x_free: [a__, b__, c__, d__, m_, p_],
        when: {
            rubi_poly_q_power(&px__, x_, &Atom::num(2))
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && rubi_expon_power(&px__, x_, &Atom::num(2)).is_some_and(|q_i| {
                    let q = Atom::num(q_i);
                    gtq!(&q, 1)
                        && neq!(&m_ + Atom::num(4) * &p_ + Atom::num(2) * &q + 1, 0)
                })
        },
        rhs: {
            let q_i = rubi_expon_power(&px__, x_, &Atom::num(2)).rubi_rhs();
            let q = Atom::num(q_i);
            let coefficient = rubi_coeff_power(&px__, x_, &Atom::num(2), q_i).rubi_rhs();
            let dx = &d__ * x_;
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let denominator_factor = &m_ + Atom::num(4) * &p_ + Atom::num(2) * &q + 1;
            let d_exponent = Atom::num(2) * &q - 3;
            let direct = &coefficient
                * dx.pow(&m_ + Atom::num(2) * &q - 3)
                * quartic.pow(&p_ + 1)
                / (&c__ * d__.pow(&d_exponent) * &denominator_factor);
            let payload = &px__
                - &coefficient * x_.pow(Atom::num(2) * &q)
                - &coefficient
                    * (&a__
                        * (&m_ + Atom::num(2) * &q - 3)
                        * x_.pow(Atom::num(2) * (&q - 2))
                        + &b__
                            * (&m_ + Atom::num(2) * &p_ + Atom::num(2) * &q - 1)
                            * x_.pow(Atom::num(2) * (&q - 1)))
                    / (&c__ * &denominator_factor);
            let expanded = rubi_expand_to_sum(&payload, x_);
            let recursive = rubi_rhs_int(
                &(dx.pow(&m_) * quartic.pow(&p_) * expanded),
                x_,
            );

            rubi_simp(&(direct), x_) + recursive
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
    let p_ = symbols.p_;
    let pq__ = symbols.pq__;
    let x_ = symbols.x_;
    (d__ * x_).pow(m_) * pq__ * (a__ + b__ * x_.pow(2) + c__ * x_.pow(4)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let m_ = symbols.m_;
    let p_ = symbols.p_;
    let pq__ = symbols.pq__;
    let x_ = symbols.x_;
    x_.pow(m_) * pq__ * (a__ + b__ * x_.pow(2) + c__ * x_.pow(4)).pow(p_)
}
