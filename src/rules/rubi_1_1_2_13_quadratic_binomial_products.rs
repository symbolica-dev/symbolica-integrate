use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_2350(rules);
    push_rules_rule_2351(rules);
    push_rules_rule_2352(rules);
    push_rules_rule_2353(rules);
    push_rules_rule_2354(rules);
    push_rules_rule_2355(rules);
}

fn push_rules_rule_2350(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, px__, x_);
    rules.push(rubi_rule!(
        order: 2350,
        source: "Int[Px_*(e_.*x_)^m_.*(c_+d_.*x_)^n_.*(a_+b_.*x_^2)^p_.,x_Symbol] :=
          Int[PolynomialQuotient[Px,c+d*x,x]*(e*x)^m*(c+d*x)^(n+1)*(a+b*x^2)^p,x] /;
        FreeQ[{a,b,c,d,e,m,n,p},x] && PolynomialQ[Px,x] && EqQ[PolynomialRemainder[Px,c+d*x,x],0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [px__, e__, m_, c__, d__, n_, a__, b__, p_, x_],
        optional: [e__, m_, d__, n_, b__, p_],
        when: {
            let linear = &c__ + &d__ * x_;
            freeq!([a__, b__, c__, d__, e__, m_, n_, p_], x_)
                && rubi_polynomial_q(&px__, x_)
                && rubi_polynomial_remainder(&px__, &linear, x_)
                    .is_some_and(|remainder| eqq!(remainder, 0))
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let quotient = rubi_polynomial_quotient(&px__, &linear, x_).rubi_rhs();
            let transformed = quotient
                * (&e__ * x_).pow(&m_)
                * linear.pow(&n_ + 1)
                * (&a__ + &b__ * x_.pow(2)).pow(&p_);

            rubi_rhs_int(&transformed, x_)
        },
    ));
}

fn push_rules_rule_2351(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, n_, p_, px__, x_);
    rules.push(rubi_rule!(
        order: 2351,
        source: "Int[Px_*(c_+d_.*x_)^n_.*(a_+b_.*x_^2)^p_./x_,x_Symbol] :=
          Int[PolynomialQuotient[Px,x,x]*(c+d*x)^n*(a+b*x^2)^p,x] +
          PolynomialRemainder[Px,x,x] \\[Star] Int[(c+d*x)^n*(a+b*x^2)^p/x,x]/;
        FreeQ[{a,b,c,d,n,p},x] && PolynomialQ[Px,x]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern: px__ * (c__ + d__ * x_).pow(n_)
            * (a__ + b__ * x_.pow(2)).pow(p_)
            / x_,
        with: [px__, c__, d__, n_, a__, b__, p_, x_],
        optional: [d__, n_, b__, p_],
        when: {
            freeq!([a__, b__, c__, d__, n_, p_], x_)
                && rubi_polynomial_q(&px__, x_)
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let quadratic = &a__ + &b__ * x_.pow(2);
            let quotient = rubi_polynomial_quotient(&px__, x_, x_).rubi_rhs();
            let remainder = rubi_polynomial_remainder(&px__, x_, x_).rubi_rhs();
            let first = rubi_rhs_int(
                &(quotient * linear.pow(&n_) * quadratic.pow(&p_)),
                x_,
            );
            let second = rubi_rhs_int(
                &(linear.pow(&n_) * quadratic.pow(&p_) / x_),
                x_,
            );

            first + rubi_star(remainder, second)
        },
    ));
}

fn push_rules_rule_2352(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, px__, x_);
    rules.push(rubi_rule!(
        order: 2352,
        source: "Int[(e_.*x_)^m_*Px_/(Sqrt[c_+d_.*x_]*Sqrt[a_+b_.*x_^2]),x_Symbol] :=
          With[{Px0=Coefficient[Px,x,0]},
          Px0*(e*x)^(m+1)*Sqrt[c+d*x]*Sqrt[a+b*x^2]/(a*c*e*(m+1)) +
          1/(2*a*c*e*(m+1)) \\[Star] Int[(e*x)^(m+1)/(Sqrt[c+d*x]*Sqrt[a+b*x^2])*
            ExpandToSum[2*a*c*(m+1)*((Px-Px0)/x)-Px0*(a*d*(2*m+3)+2*b*c*(m+2)*x+b*d*(2*m+5)*x^2),x],x]]/;
        FreeQ[{a,b,c,d,e},x] && PolynomialQ[Px,x] && LtQ[m,-1]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern: (e__ * x_).pow(m_) * px__
            / ((c__ + d__ * x_).sqrt() * (a__ + b__ * x_.pow(2)).sqrt()),
        with: [e__, m_, px__, c__, d__, a__, b__, x_],
        optional: [e__, d__, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && rubi_polynomial_q(&px__, x_)
                && ltq!(m_, -1)
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let quadratic = &a__ + &b__ * x_.pow(2);
            let px0 = rubi_coefficient(&px__, x_, 0).rubi_rhs();
            let direct = rubi_simp(
                &(&px0
                    * (&e__ * x_).pow(&m_ + 1)
                    * linear.sqrt()
                    * quadratic.sqrt()
                    / (&a__ * &c__ * &e__ * (&m_ + 1))),
                x_,
            );
            let payload = rubi_expand_to_sum(
                &(Atom::num(2) * &a__ * &c__ * (&m_ + 1) * ((&px__ - &px0) / x_)
                    - &px0
                        * (&a__ * &d__ * (Atom::num(2) * &m_ + 3)
                            + Atom::num(2) * &b__ * &c__ * (&m_ + 2) * x_
                            + &b__ * &d__ * (Atom::num(2) * &m_ + 5) * x_.pow(2))),
                x_,
            );
            let recursive = rubi_rhs_int(
                &((&e__ * x_).pow(&m_ + 1) * payload
                    / (linear.sqrt() * quadratic.sqrt())),
                x_,
            );

            rubi_simp(&(direct), x_)
                    + rubi_star(Atom::num(1)
                            / (Atom::num(2) * &a__ * &c__ * &e__ * (&m_ + 1)), recursive)
        },
    ));
}

fn push_rules_rule_2353(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, px__, x_);
    rules.push(rubi_rule!(
        order: 2353,
        source: "Int[Px_*(e_.*x_)^m_.*(c_+d_.*x_)^n_*(a_+b_.*x_^2)^p_,x_Symbol] :=
          Int[ExpandIntegrand[Px*(e*x)^m*(c+d*x)^n*(a+b*x^2)^p,x],x] /;
        FreeQ[{a,b,c,d,e,m,n,p},x] && PolyQ[Px,x] && (IntegerQ[p] || IntegerQ[2*p] && IntegerQ[m] && ILtQ[n,0])",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [px__, e__, m_, c__, d__, n_, a__, b__, p_, x_],
        optional: [e__, m_, d__, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_, p_], x_)
                && poly_q(&px__, x_)
                && (integerq!(p_)
                    || integerq!(Atom::num(2) * &p_)
                        && integerq!(m_)
                        && iltq!(n_, 0))
        },
        rhs: {
            let integrand = &px__
                * (&e__ * x_).pow(&m_)
                * (&c__ + &d__ * x_).pow(&n_)
                * (&a__ + &b__ * x_.pow(2)).pow(&p_);
            let expanded = rubi_expand_integrand(&integrand, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_2354(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, px__, x_);
    rules.push(rubi_rule!(
        order: 2354,
        source: "Int[Px_*(e_.*x_)^m_*(c_+d_.*x_)^n_.*(a_+b_.*x_^2)^p_.,x_Symbol] :=
          With[{k=Denominator[m]},
          k/e \\[Star] Subst[Int[ReplaceAll[Px,x->x^k/e]*x^(k*(m+1)-1)*(c+d*x^k/e)^n*(a+b*x^(2*k)/e^2)^p,x],x,(e*x)^(1/k)]] /;
        FreeQ[{a,b,c,d,e,n,p},x] && PolyQ[Px,x] && FractionQ[m]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [px__, e__, m_, c__, d__, n_, a__, b__, p_, x_],
        optional: [e__, d__, n_, b__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, n_, p_], x_)
                && poly_q(&px__, x_)
                && fractionq!(m_)
        },
        rhs: {
            let k = denominator!(m_);
            let k_atom = Atom::num(k);
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let replaced_px = substitute_symbol(
                &px__,
                x_,
                sub_atom.pow(&k_atom) / &e__,
            );
            let transformed = replaced_px
                * sub_atom.pow(&k_atom * (&m_ + 1) - 1)
                * (&c__ + &d__ * sub_atom.pow(&k_atom) / &e__).pow(&n_)
                * (&a__ + &b__ * sub_atom.pow(Atom::num(2) * &k_atom) / e__.pow(2))
                    .pow(&p_);
            let primitive = rubi_rhs_int(&transformed, sub);
            let substitution =
                (&e__ * x_).pow(Atom::num(1) / &k_atom);
            let substituted = rubi_subst(&primitive, sub, substitution);

            rubi_star(&k_atom / &e__, substituted)
        },
    ));
}

fn push_rules_rule_2355(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, px__, x_);
    rules.push(rubi_rule!(
        order: 2355,
        source: "Int[Px_*(e_.*x_)^m_.*(c_+d_.*x_)^n_*(a_+b_.*x_^2)^p_.,x_Symbol] :=
          Int[PolynomialQuotient[Px,c+d*x,x]*(e*x)^m*(c+d*x)^(n+1)*(a+b*x^2)^p,x] +
          PolynomialRemainder[Px,c+d*x,x] \\[Star] Int[(e*x)^m*(c+d*x)^n*(a+b*x^2)^p,x]/;
        FreeQ[{a,b,c,d,e,m,p},x] && PolynomialQ[Px,x] && LtQ[n,0]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [px__, e__, m_, c__, d__, n_, a__, b__, p_, x_],
        optional: [e__, m_, d__, b__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, p_], x_)
                && rubi_polynomial_q(&px__, x_)
                && ltq!(n_, 0)
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let monomial = (&e__ * x_).pow(&m_);
            let quadratic = (&a__ + &b__ * x_.pow(2)).pow(&p_);
            let quotient = rubi_polynomial_quotient(&px__, &linear, x_).rubi_rhs();
            let remainder = rubi_polynomial_remainder(&px__, &linear, x_).rubi_rhs();
            let first = rubi_rhs_int(
                &(quotient * &monomial * linear.pow(&n_ + 1) * &quadratic),
                x_,
            );
            let second = rubi_rhs_int(
                &(monomial * linear.pow(&n_) * quadratic),
                x_,
            );

            first + rubi_star(remainder, second)
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
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let px__ = symbols.px__;
    let x_ = symbols.x_;
    px__ * (e__ * x_).pow(m_) * (c__ + d__ * x_).pow(n_) * (a__ + b__ * x_.pow(2)).pow(p_)
}
