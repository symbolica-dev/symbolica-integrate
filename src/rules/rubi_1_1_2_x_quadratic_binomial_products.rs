use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_2341(rules);
    push_rules_rule_2342(rules);
    push_rules_rule_2343(rules);
    push_rules_rule_2344(rules);
    push_rules_rule_2345(rules);
    push_rules_rule_2346(rules);
}

fn push_rules_rule_2341(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2341,
        source: "Int[Pq_*(a_+b_.*x_^2)^p_.,x_Symbol] :=
          Int[ExpandIntegrand[Pq*(a+b*x^2)^p,x],x] /;
        FreeQ[{a,b},x] && PolyQ[Pq,x] && IGtQ[p,-2]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [pq__, a__, b__, p_, x_],
        optional: [b__, p_],
        when: {
            freeq!([a__, b__], x_) && poly_q(&pq__, x_) && igtq!(p_, -2)
        },
        rhs: {
            let integrand = &pq__ * (&a__ + &b__ * x_.pow(2)).pow(&p_);
            let expanded = rubi_expand_integrand(&integrand, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_2342(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2342,
        source: "Int[Pq_*(a_+b_.*x_^2)^p_,x_Symbol] :=
          Int[x*PolynomialQuotient[Pq,x,x]*(a+b*x^2)^p,x] /;
        FreeQ[{a,b,p},x] && PolyQ[Pq,x] && EqQ[Coeff[Pq,x,0],0] && Not[MatchQ[Pq,x^m_.*u_. /; IntegerQ[m]]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [pq__, a__, b__, p_, x_],
        optional: [b__],
        when: {
            freeq!([a__, b__, p_], x_)
                && poly_q(&pq__, x_)
                && rubi_coeff(&pq__, x_, 0).is_some_and(|coeff| eqq!(coeff, 0))
                && !visible_integer_power_of_variable_factor(&pq__, x_)
        },
        rhs: {
            let quotient = rubi_polynomial_quotient(&pq__, x_, x_).rubi_rhs();
            let transformed = x_ * quotient * (&a__ + &b__ * x_.pow(2)).pow(p_);

            rubi_rhs_int(&transformed, x_)
        },
    ));
}

fn push_rules_rule_2343(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, p_, px__, x_);
    rules.push(rubi_rule!(
        order: 2343,
        source: "Int[Px_*(a_+b_.*x_^2)^p_.,x_Symbol] :=
          Int[PolynomialQuotient[Px,a+b*x^2,x]*(a+b*x^2)^(p+1),x] /;
        FreeQ[{a,b,p},x] && PolyQ[Px,x] && EqQ[PolynomialRemainder[Px,a+b*x^2,x],0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: px__ * (a__ + b__ * x_.pow(2)).pow(p_),
        with: [px__, a__, b__, p_, x_],
        optional: [b__, p_],
        when: {
            let denominator = &a__ + &b__ * x_.pow(2);
            freeq!([a__, b__, p_], x_)
                && rubi_poly_q(&px__, x_)
                && rubi_polynomial_remainder(&px__, &denominator, x_)
                    .is_some_and(|remainder| eqq!(remainder, 0))
        },
        rhs: {
            let denominator = &a__ + &b__ * x_.pow(2);
            let quotient = rubi_polynomial_quotient(&px__, &denominator, x_).rubi_rhs();
            let transformed = quotient * denominator.pow(&p_ + 1);

            rubi_rhs_int(&transformed, x_)
        },
    ));
}

fn push_rules_rule_2344(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2344,
        source: "Int[Pq_*(a_+b_.*x_^2)^p_,x_Symbol] :=
          With[{A=Coeff[Pq,x,0],Q=PolynomialQuotient[Pq-Coeff[Pq,x,0],x^2,x]},
          A*x*(a+b*x^2)^(p+1)/a + 1/a \\[Star] Int[x^2*(a+b*x^2)^p*(a*Q-A*b*(2*p+3)),x]] /;
        FreeQ[{a,b},x] && PolyQ[Pq,x^2] && ILtQ[p+1/2,0] && LtQ[Expon[Pq,x]+2*p+1,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [pq__, a__, b__, p_, x_],
        optional: [b__],
        when: {
            freeq!([a__, b__], x_)
                && rubi_poly_q_power(&pq__, x_, &Atom::num(2))
                && iltq!(&p_ + Atom::num(1) / Atom::num(2), 0)
                && rubi_expon(&pq__, x_)
                    .is_some_and(|q| ltq!(Atom::num(q) + Atom::num(2) * &p_ + 1, 0))
        },
        rhs: {
            let quadratic = &a__ + &b__ * x_.pow(2);
            let capital_a = rubi_coeff(&pq__, x_, 0).rubi_rhs();
            let numerator = &pq__ - &capital_a;
            let capital_q =
                rubi_polynomial_quotient(&numerator, x_.pow(2), x_).rubi_rhs();
            let direct = rubi_simp(
                &(&capital_a * x_ * quadratic.pow(&p_ + 1) / &a__),
                x_,
            );
            let recursive_integrand = x_.pow(2)
                * quadratic.pow(&p_)
                * (&a__ * capital_q
                    - &capital_a * &b__ * (Atom::num(2) * &p_ + 3));
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_)
                    + rubi_star(Atom::num(1) / &a__, recursive)
        },
    ));
}

fn push_rules_rule_2345(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2345,
        source: "Int[Pq_*(a_+b_.*x_^2)^p_,x_Symbol] :=
          With[{Q=PolynomialQuotient[Pq,a+b*x^2,x],
                f=Coeff[PolynomialRemainder[Pq,a+b*x^2,x],x,0],
                g=Coeff[PolynomialRemainder[Pq,a+b*x^2,x],x,1]},
          (a*g-b*f*x)*(a+b*x^2)^(p+1)/(2*a*b*(p+1)) +
          1/(2*a*(p+1)) \\[Star] Int[(a+b*x^2)^(p+1)*ExpandToSum[2*a*(p+1)*Q+f*(2*p+3),x],x]] /;
        FreeQ[{a,b},x] && PolyQ[Pq,x] && LtQ[p,-1]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [pq__, a__, b__, p_, x_],
        optional: [b__],
        when: {
            freeq!([a__, b__], x_)
                && poly_q(&pq__, x_)
                && ltq!(p_, -1)
        },
        rhs: {
            let quadratic = &a__ + &b__ * x_.pow(2);
            let q = rubi_polynomial_quotient(&pq__, &quadratic, x_).rubi_rhs();
            let remainder = rubi_polynomial_remainder(&pq__, &quadratic, x_).rubi_rhs();
            let f = rubi_coeff(&remainder, x_, 0).rubi_rhs();
            let g = rubi_coeff(&remainder, x_, 1).rubi_rhs();
            let raised_p = &p_ + 1;
            let recurrence_payload = rubi_expand_to_sum(
                &(Atom::num(2) * &a__ * &raised_p * q
                    + &f * (Atom::num(2) * &p_ + 3)),
                x_,
            );
            let recursive = rubi_rhs_int(
                &(quadratic.pow(&raised_p) * recurrence_payload),
                x_,
            );
            let direct = rubi_simp(
                &((&a__ * &g - &b__ * &f * x_)
                    * quadratic.pow(&raised_p)
                    / (Atom::num(2) * &a__ * &b__ * &raised_p)),
                x_,
            );

            rubi_simp(&(direct), x_)
                    + rubi_star(Atom::num(1) / (Atom::num(2) * &a__ * raised_p), recursive)
        },
    ));
}

fn push_rules_rule_2346(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2346,
        source: "Int[Pq_*(a_+b_.*x_^2)^p_,x_Symbol] :=
          With[{q=Expon[Pq,x],e=Coeff[Pq,x,Expon[Pq,x]]},
          e*x^(q-1)*(a+b*x^2)^(p+1)/(b*(q+2*p+1)) +
          1/(b*(q+2*p+1)) \\[Star] Int[(a+b*x^2)^p*ExpandToSum[b*(q+2*p+1)*Pq-a*e*(q-1)*x^(q-2)-b*e*(q+2*p+1)*x^q,x],x]] /;
        FreeQ[{a,b,p},x] && PolyQ[Pq,x] && Not[LeQ[p,-1]]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [pq__, a__, b__, p_, x_],
        optional: [b__],
        when: {
            freeq!([a__, b__, p_], x_)
                && poly_q(&pq__, x_)
                && !leq!(p_, -1)
        },
        rhs: {
            let q = rubi_expon(&pq__, x_).rubi_rhs();
            let e = rubi_coeff(&pq__, x_, q).rubi_rhs();
            let q_atom = Atom::num(q);
            let denominator_factor = &q_atom + Atom::num(2) * &p_ + 1;
            let quadratic = &a__ + &b__ * x_.pow(2);
            let direct = rubi_simp(
                &(&e * x_.pow(q - 1) * quadratic.pow(&p_ + 1)
                    / (&b__ * &denominator_factor)),
                x_,
            );
            let payload = rubi_expand_to_sum(
                &(&b__ * &denominator_factor * &pq__
                    - &a__ * &e * (&q_atom - 1) * x_.pow(q - 2)
                    - &b__ * &e * &denominator_factor * x_.pow(q)),
                x_,
            );
            let recursive = rubi_rhs_int(&(quadratic.pow(&p_) * payload), x_);

            rubi_simp(&(direct), x_)
                    + rubi_star(Atom::num(1) / (&b__ * denominator_factor), recursive)
        },
    ));
}

// Generated shared pattern builders.

#[inline(never)]
fn rubi_shared_pattern_0(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let p_ = symbols.p_;
    let pq__ = symbols.pq__;
    let x_ = symbols.x_;
    pq__ * (a__ + b__ * x_.pow(2)).pow(p_)
}
