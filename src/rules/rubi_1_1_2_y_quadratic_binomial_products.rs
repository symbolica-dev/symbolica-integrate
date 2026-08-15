use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_2331(rules);
    push_rules_rule_2332(rules);
    push_rules_rule_2333(rules);
    push_rules_rule_2334(rules);
    push_rules_rule_2335(rules);
    push_rules_rule_2336(rules);
    push_rules_rule_2337(rules);
    push_rules_rule_2338(rules);
    push_rules_rule_2339(rules);
    push_rules_rule_2340(rules);
}

fn push_rules_rule_2331(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2331,
        source: "Int[x_^m_.*Pq_*(a_+b_.*x_^2)^p_.,x_Symbol] :=
          1/2 \\[Star] Subst[Int[x^((m-1)/2)*SubstFor[x^2,Pq,x]*(a+b*x)^p,x],x,x^2] /;
        FreeQ[{a,b,p},x] && PolyQ[Pq,x^2] && IntegerQ[(m-1)/2]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [pq__, a__, b__, m_, p_, x_],
        optional: [b__, m_, p_],
        when: {
            freeq!([a__, b__, p_], x_)
                && rubi_poly_q_power(&pq__, x_, &Atom::num(2))
                && integerq!((&m_ - 1) / 2)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let x_squared = x_.pow(2);
            let substituted_pq = rubi_subst_for(&pq__, &x_squared, sub);
            let transformed_integrand = sub_atom.pow((&m_ - 1) / 2)
                * substituted_pq
                * (&a__ + &b__ * &sub_atom).pow(&p_);
            let primitive = rubi_rhs_int(&transformed_integrand, sub);
            let substituted = rubi_subst(&primitive, sub, x_squared);

            rubi_star(Atom::num(1) / 2, substituted)
        },
    ));
}

fn push_rules_rule_2332(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, m_, p_, p2__, x_);
    rules.push(rubi_rule!(
        order: 2332,
        source: "Int[(c_.*x_)^m_.*P2_*(a_+b_.*x_^2)^p_.,x_Symbol] :=
          With[{f=Coeff[P2,x,0],g=Coeff[P2,x,1],h=Coeff[P2,x,2]},
          h*(c*x)^(m+1)*(a+b*x^2)^(p+1)/(b*c*(m+2*p+3)) /;
         EqQ[g,0] && EqQ[a*h*(m+1)-b*f*(m+2*p+3),0]] /;
        FreeQ[{a,b,c,m,p},x] && PolyQ[P2,x,2] && NeQ[m,-1]",
        desc: "Special case of one step of the Ostrogradskiy-Hermite integration method",
        refs: [],
        pattern: (c__ * x_).pow(m_) * p2__ * (a__ + b__ * x_.pow(2)).pow(p_),
        with: [p2__, a__, b__, c__, m_, p_, x_],
        optional: [b__, c__, m_, p_],
        when: {
            let f = rubi_coeff(&p2__, x_, 0);
            let g = rubi_coeff(&p2__, x_, 1);
            let h = rubi_coeff(&p2__, x_, 2);
            freeq!([a__, b__, c__, m_, p_], x_)
                && rubi_poly_q_degree(&p2__, x_, 2)
                && neq!(m_, -1)
                && f.zip(g).zip(h).is_some_and(|((f, g), h)| {
                    eqq!(g, 0)
                        && eqq!(
                            &a__ * &h * (&m_ + 1)
                                - &b__ * &f * (&m_ + Atom::num(2) * &p_ + 3),
                            0
                        )
                })
        },
        rhs: {
            let h = rubi_coeff(&p2__, x_, 2).rubi_rhs();
            let result = h
                * (&c__ * x_).pow(&m_ + 1)
                * (&a__ + &b__ * x_.pow(2)).pow(&p_ + 1)
                / (&b__ * &c__ * (&m_ + Atom::num(2) * &p_ + 3));
            rubi_simp(&result, x_)
        },
    ));
}

fn push_rules_rule_2333(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2333,
        source: "Int[(c_.*x_)^m_.*Pq_*(a_+b_.*x_^2)^p_.,x_Symbol] :=
          Int[ExpandIntegrand[(c*x)^m*Pq*(a+b*x^2)^p,x],x] /;
        FreeQ[{a,b,c,m},x] && PolyQ[Pq,x] && IGtQ[p,-2]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [pq__, a__, b__, c__, m_, p_, x_],
        optional: [b__, c__, m_, p_],
        when: {
            freeq!([a__, b__, c__, m_], x_)
                && poly_q(&pq__, x_)
                && igtq!(p_, -2)
        },
        rhs: {
            let integrand = (&c__ * x_).pow(&m_)
                * &pq__
                * (&a__ + &b__ * x_.pow(2)).pow(&p_);
            let expanded = rubi_expand_integrand(&integrand, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_2334(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2334,
        source: "Int[x_^m_*Pq_*(a_+b_.*x_^2)^p_,x_Symbol] :=
          With[{A=Coeff[Pq,x,0],Q=PolynomialQuotient[Pq-Coeff[Pq,x,0],x^2,x]},
          A*x^(m+1)*(a+b*x^2)^(p+1)/(a*(m+1)) +
          1/(a*(m+1)) \\[Star] Int[x^(m+2)*(a+b*x^2)^p*(a*(m+1)*Q-A*b*(m+2*(p+1)+1)),x]] /;
        FreeQ[{a,b},x] && PolyQ[Pq,x^2] && IntegerQ[m/2] && ILtQ[(m+1)/2+p,0] && LtQ[m+Expon[Pq,x]+2*p+1,0]",
        desc: "Algebraic expansion and binomial recurrence 3b",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [pq__, a__, b__, m_, p_, x_],
        optional: [b__],
        when: {
            freeq!([a__, b__], x_)
                && rubi_poly_q_power(&pq__, x_, &Atom::num(2))
                && integerq!(&m_ / 2)
                && iltq!((&m_ + 1) / 2 + &p_, 0)
                && rubi_expon(&pq__, x_).is_some_and(|q| {
                    ltq!(&m_ + Atom::num(q) + Atom::num(2) * &p_ + 1, 0)
                })
        },
        rhs: {
            let capital_a = rubi_coeff(&pq__, x_, 0).rubi_rhs();
            let q = rubi_polynomial_quotient(
                &(&pq__ - &capital_a),
                x_.pow(2),
                x_,
            ).rubi_rhs();
            let quadratic = &a__ + &b__ * x_.pow(2);
            let denominator = &a__ * (&m_ + 1);
            let direct = rubi_simp(
                &(&capital_a
                    * x_.pow(&m_ + 1)
                    * quadratic.pow(&p_ + 1)
                    / &denominator),
                x_,
            );
            let payload = &a__ * (&m_ + 1) * q
                - &capital_a * &b__ * (&m_ + Atom::num(2) * (&p_ + 1) + 1);
            let recursive_integrand =
                x_.pow(&m_ + 2) * quadratic.pow(&p_) * payload;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_)
                    + rubi_star(Atom::num(1) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_2335(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2335,
        source: "Int[(c_.*x_)^m_.*Pq_*(a_+b_.*x_^2)^p_,x_Symbol] :=
          With[{Q=PolynomialQuotient[Pq,a+b*x^2,x],
                f=Coeff[PolynomialRemainder[Pq,a+b*x^2,x],x,0],
                g=Coeff[PolynomialRemainder[Pq,a+b*x^2,x],x,1]},
          (c*x)^m*(a+b*x^2)^(p+1)*(a*g-b*f*x)/(2*a*b*(p+1)) +
          c/(2*a*b*(p+1)) \\[Star] Int[(c*x)^(m-1)*(a+b*x^2)^(p+1)*ExpandToSum[2*a*b*(p+1)*x*Q-a*g*m+b*f*(m+2*p+3)*x,x],x]] /;
        FreeQ[{a,b,c},x] && PolyQ[Pq,x] && LtQ[p,-1] && GtQ[m,0]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [pq__, a__, b__, c__, m_, p_, x_],
        optional: [b__, c__, m_],
        when: {
            freeq!([a__, b__, c__], x_)
                && poly_q(&pq__, x_)
                && ltq!(p_, -1)
                && gtq!(m_, 0)
        },
        rhs: {
            let quadratic = &a__ + &b__ * x_.pow(2);
            let q = rubi_polynomial_quotient(&pq__, &quadratic, x_).rubi_rhs();
            let remainder = rubi_polynomial_remainder(&pq__, &quadratic, x_).rubi_rhs();
            let f = rubi_coeff(&remainder, x_, 0).rubi_rhs();
            let g = rubi_coeff(&remainder, x_, 1).rubi_rhs();
            let denominator = Atom::num(2) * &a__ * &b__ * (&p_ + 1);
            let direct = rubi_simp(
                &((&c__ * x_).pow(&m_)
                    * quadratic.pow(&p_ + 1)
                    * ((&a__ * &g - &b__ * &f * x_) / &denominator)),
                x_,
            );
            let payload = rubi_expand_to_sum(
                &(Atom::num(2) * &a__ * &b__ * (&p_ + 1) * x_ * q
                    - &a__ * g * &m_
                    + &b__ * f * (&m_ + Atom::num(2) * &p_ + 3) * x_),
                x_,
            );
            let recursive_integrand = (&c__ * x_).pow(&m_ - 1)
                * quadratic.pow(&p_ + 1)
                * payload;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_)
                    + rubi_star(&c__ / denominator, recursive)
        },
    ));
}

fn push_rules_rule_2336(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2336,
        source: "Int[(c_.*x_)^m_.*Pq_*(a_+b_.*x_^2)^p_,x_Symbol] :=
          With[{Q=PolynomialQuotient[(c*x)^m*Pq,a+b*x^2,x],
                f=Coeff[PolynomialRemainder[(c*x)^m*Pq,a+b*x^2,x],x,0],
                g=Coeff[PolynomialRemainder[(c*x)^m*Pq,a+b*x^2,x],x,1]},
          (a*g-b*f*x)*(a+b*x^2)^(p+1)/(2*a*b*(p+1)) +
          1/(2*a*(p+1)) \\[Star] Int[(c*x)^m*(a+b*x^2)^(p+1)*ExpandToSum[2*a*(p+1)*(c*x)^(-m)*Q+f*(2*p+3)*(c*x)^(-m),x],x]] /;
        FreeQ[{a,b,c},x] && PolyQ[Pq,x] && LtQ[p,-1] && ILtQ[m,0]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [pq__, a__, b__, c__, m_, p_, x_],
        optional: [b__, c__, m_],
        when: {
            freeq!([a__, b__, c__], x_)
                && poly_q(&pq__, x_)
                && ltq!(p_, -1)
                && iltq!(m_, 0)
        },
        rhs: {
            let quadratic = &a__ + &b__ * x_.pow(2);
            let monomial = (&c__ * x_).pow(&m_);
            let scaled_pq = &monomial * &pq__;
            let q = rubi_polynomial_quotient(&scaled_pq, &quadratic, x_).rubi_rhs();
            let remainder = rubi_polynomial_remainder(&scaled_pq, &quadratic, x_).rubi_rhs();
            let f = rubi_coeff(&remainder, x_, 0).rubi_rhs();
            let g = rubi_coeff(&remainder, x_, 1).rubi_rhs();
            let direct = rubi_simp(
                &((&a__ * &g - &b__ * &f * x_)
                    * quadratic.pow(&p_ + 1)
                    / (Atom::num(2) * &a__ * &b__ * (&p_ + 1))),
                x_,
            );
            let payload = rubi_expand_to_sum(
                &((Atom::num(2) * &a__ * (&p_ + 1) * q) / &monomial
                    + (&f * (Atom::num(2) * &p_ + 3)) / &monomial),
                x_,
            );
            let recursive_integrand =
                monomial * quadratic.pow(&p_ + 1) * payload;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_)
                    + rubi_star(Atom::num(1) / (Atom::num(2) * &a__ * (&p_ + 1)), recursive)
        },
    ));
}

fn push_rules_rule_2337(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2337,
        source: "Int[(c_.*x_)^m_.*Pq_*(a_+b_.*x_^2)^p_,x_Symbol] :=
          With[{Q=PolynomialQuotient[Pq,a+b*x^2,x],
                f=Coeff[PolynomialRemainder[Pq,a+b*x^2,x],x,0],
                g=Coeff[PolynomialRemainder[Pq,a+b*x^2,x],x,1]},
          -(c*x)^(m+1)*(f+g*x)*(a+b*x^2)^(p+1)/(2*a*c*(p+1)) +
          1/(2*a*(p+1)) \\[Star] Int[(c*x)^m*(a+b*x^2)^(p+1)*ExpandToSum[2*a*(p+1)*Q+f*(m+2*p+3)+g*(m+2*p+4)*x,x],x]] /;
        FreeQ[{a,b,c,m},x] && PolyQ[Pq,x] && LtQ[p,-1] && Not[GtQ[m,0]]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [pq__, a__, b__, c__, m_, p_, x_],
        optional: [b__, c__, m_],
        when: {
            freeq!([a__, b__, c__, m_], x_)
                && poly_q(&pq__, x_)
                && ltq!(p_, -1)
                && !gtq!(m_, 0)
        },
        rhs: {
            let quadratic = &a__ + &b__ * x_.pow(2);
            let q = rubi_polynomial_quotient(&pq__, &quadratic, x_).rubi_rhs();
            let remainder = rubi_polynomial_remainder(&pq__, &quadratic, x_).rubi_rhs();
            let f = rubi_coeff(&remainder, x_, 0).rubi_rhs();
            let g = rubi_coeff(&remainder, x_, 1).rubi_rhs();
            let direct = rubi_simp(
                &(-(&c__ * x_).pow(&m_ + 1)
                    * (&f + &g * x_)
                    * quadratic.pow(&p_ + 1)
                    / (Atom::num(2) * &a__ * &c__ * (&p_ + 1))),
                x_,
            );
            let payload = rubi_expand_to_sum(
                &(Atom::num(2) * &a__ * (&p_ + 1) * q
                    + &f * (&m_ + Atom::num(2) * &p_ + 3)
                    + &g * (&m_ + Atom::num(2) * &p_ + 4) * x_),
                x_,
            );
            let recursive_integrand = (&c__ * x_).pow(&m_)
                * quadratic.pow(&p_ + 1)
                * payload;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_)
                    + rubi_star(Atom::num(1) / (Atom::num(2) * &a__ * (&p_ + 1)), recursive)
        },
    ));
}

fn push_rules_rule_2338(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2338,
        source: "Int[(c_.*x_)^m_*Pq_*(a_+b_.*x_^2)^p_,x_Symbol] :=
          With[{Q=PolynomialQuotient[Pq,c*x,x], R=PolynomialRemainder[Pq,c*x,x]},
          R*(c*x)^(m+1)*(a+b*x^2)^(p+1)/(a*c*(m+1)) +
          1/(a*c*(m+1)) \\[Star] Int[(c*x)^(m+1)*(a+b*x^2)^p*ExpandToSum[a*c*(m+1)*Q-b*R*(m+2*p+3)*x,x],x]] /;
        FreeQ[{a,b,c,p},x] && PolyQ[Pq,x] && LtQ[m,-1] && (IntegerQ[2*p] || NeQ[Expon[Pq,x],1])",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [pq__, a__, b__, c__, m_, p_, x_],
        optional: [b__, c__],
        when: {
            freeq!([a__, b__, c__, p_], x_)
                && poly_q(&pq__, x_)
                && ltq!(m_, -1)
                && (integerq!(Atom::num(2) * &p_)
                    || rubi_expon(&pq__, x_).is_some_and(|q| neq!(Atom::num(q), 1)))
        },
        rhs: {
            let monomial = &c__ * x_;
            let q = rubi_polynomial_quotient(&pq__, &monomial, x_).rubi_rhs();
            let r = rubi_polynomial_remainder(&pq__, &monomial, x_).rubi_rhs();
            let denominator = &a__ * &c__ * (&m_ + 1);
            let quadratic = &a__ + &b__ * x_.pow(2);
            let direct = rubi_simp(
                &(&r
                    * monomial.pow(&m_ + 1)
                    * quadratic.pow(&p_ + 1)
                    / &denominator),
                x_,
            );
            let payload = rubi_expand_to_sum(
                &(&a__ * &c__ * (&m_ + 1) * q
                    - &b__ * &r * (&m_ + Atom::num(2) * &p_ + 3) * x_),
                x_,
            );
            let recursive_integrand =
                monomial.pow(&m_ + 1) * quadratic.pow(&p_) * payload;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_)
                    + rubi_star(Atom::num(1) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_2339(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2339,
        source: "Int[(c_.*x_)^m_.*Pq_*(a_+b_.*x_^2)^p_.,x_Symbol] :=
          With[{q=Expon[Pq,x]},
          Coeff[Pq,x,q]/c^q \\[Star] Int[(c*x)^(m+q)*(a+b*x^2)^p,x] +
          1/c^q \\[Star] Int[(c*x)^m*(a+b*x^2)^p*ExpandToSum[c^q*Pq-Coeff[Pq,x,q]*(c*x)^q,x],x] /;
         EqQ[q,1] || EqQ[m+q+2*p+1,0]] /;
        FreeQ[{a,b,c,m,p},x] && PolyQ[Pq,x] && Not[IGtQ[m,0] && ILtQ[p+1/2,0]]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [pq__, a__, b__, c__, m_, p_, x_],
        optional: [b__, c__, m_, p_],
        when: {
            freeq!([a__, b__, c__, m_, p_], x_)
                && poly_q(&pq__, x_)
                && !(igtq!(m_, 0) && iltq!(&p_ + Atom::num(1) / 2, 0))
                && rubi_expon(&pq__, x_).is_some_and(|q| {
                    eqq!(Atom::num(q), 1)
                        || eqq!(&m_ + Atom::num(q) + Atom::num(2) * &p_ + 1, 0)
            })
        },
        rhs: {
            let q = rubi_expon(&pq__, x_).rubi_rhs();
            let f = rubi_coeff(&pq__, x_, q).rubi_rhs();
            let quadratic = &a__ + &b__ * x_.pow(2);
            let monomial = &c__ * x_;
            let leading_integrand = monomial.pow(&m_ + q) * quadratic.pow(&p_);
            let leading = rubi_rhs_int(&leading_integrand, x_);
            let direct = rubi_star(&f / c__.pow(q), leading);
            let payload = rubi_expand_to_sum(
                &(c__.pow(q) * &pq__ - &f * monomial.pow(q)),
                x_,
            );
            let remainder_integrand =
                monomial.pow(&m_) * quadratic.pow(&p_) * payload;
            let remainder = rubi_rhs_int(&remainder_integrand, x_);

            direct + rubi_star(Atom::num(1) / c__.pow(q), remainder)
        },
    ));
}

fn push_rules_rule_2340(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2340,
        source: "Int[(c_.*x_)^m_.*Pq_*(a_+b_.*x_^2)^p_,x_Symbol] :=
          With[{q=Expon[Pq,x],f=Coeff[Pq,x,Expon[Pq,x]]},
          f*(c*x)^(m+q-1)*(a+b*x^2)^(p+1)/(b*c^(q-1)*(m+q+2*p+1)) +
          1/(b*(m+q+2*p+1)) \\[Star] Int[(c*x)^m*(a+b*x^2)^p*ExpandToSum[b*(m+q+2*p+1)*Pq-b*f*(m+q+2*p+1)*x^q-a*f*(m+q-1)*x^(q-2),x],x] /;
         GtQ[q,1] && NeQ[m+q+2*p+1,0]] /;
        FreeQ[{a,b,c,m,p},x] && PolyQ[Pq,x] && (Not[IGtQ[m,0]] || IGtQ[p+1/2,-1])",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [pq__, a__, b__, c__, m_, p_, x_],
        optional: [b__, c__, m_],
        when: {
            freeq!([a__, b__, c__, m_, p_], x_)
                && poly_q(&pq__, x_)
                && (!igtq!(m_, 0) || igtq!(&p_ + Atom::num(1) / 2, -1))
                && rubi_expon(&pq__, x_).is_some_and(|q| {
                    gtq!(Atom::num(q), 1)
                        && neq!(&m_ + Atom::num(q) + Atom::num(2) * &p_ + 1, 0)
                })
        },
        rhs: {
            let q = rubi_expon(&pq__, x_).rubi_rhs();
            let f = rubi_coeff(&pq__, x_, q).rubi_rhs();
            let balance = &m_ + Atom::num(q) + Atom::num(2) * &p_ + 1;
            let quadratic = &a__ + &b__ * x_.pow(2);
            let direct = rubi_simp(
                &(&f
                    * (&c__ * x_).pow(&m_ + q - 1)
                    * quadratic.pow(&p_ + 1)
                    / (&b__ * c__.pow(q - 1) * &balance)),
                x_,
            );
            let payload = rubi_expand_to_sum(
                &(&b__ * &balance * &pq__
                    - &b__ * &f * &balance * x_.pow(q)
                    - &a__ * &f * (&m_ + q - 1) * x_.pow(q - 2)),
                x_,
            );
            let recursive_integrand =
                (&c__ * x_).pow(&m_) * quadratic.pow(&p_) * payload;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_)
                    + rubi_star(Atom::num(1) / (&b__ * &balance), recursive)
        },
    ));
}

// Generated shared pattern builders.

#[inline(never)]
fn rubi_shared_pattern_0(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let m_ = symbols.m_;
    let p_ = symbols.p_;
    let pq__ = symbols.pq__;
    let x_ = symbols.x_;
    (c__ * x_).pow(m_) * pq__ * (a__ + b__ * x_.pow(2)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let m_ = symbols.m_;
    let p_ = symbols.p_;
    let pq__ = symbols.pq__;
    let x_ = symbols.x_;
    x_.pow(m_) * pq__ * (a__ + b__ * x_.pow(2)).pow(p_)
}
