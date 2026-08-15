use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_2347(rules);
    push_rules_rule_2348(rules);
    push_rules_rule_2349(rules);
}

fn push_rules_rule_2347(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, p_, px__, x_);
    rules.push(rubi_rule!(
        order: 2347,
        source: "Int[Px_*(c_+d_.*x_)^m_.*(e_+f_.*x_)^n_.*(a_.+b_.*x_^2)^p_.,x_Symbol] :=
          Int[PolynomialQuotient[Px,c+d*x,x]*(c+d*x)^(m+1)*(e+f*x)^n*(a+b*x^2)^p,x] /;
        FreeQ[{a,b,c,d,e,f,m,n,p},x] && PolynomialQ[Px,x] && EqQ[PolynomialRemainder[Px,c+d*x,x],0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [px__, c__, d__, m_, e__, f__, n_, a__, b__, p_, x_],
        optional: [d__, m_, f__, n_, a__, b__, p_],
        x_free: [a__, b__, c__, d__, e__, f__, m_, n_, p_],
        when: {
            let first_linear = &c__ + &d__ * x_;
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_, p_], x_)
                && rubi_polynomial_q(&px__, x_)
                && rubi_polynomial_remainder(&px__, &first_linear, x_)
                    .is_some_and(|remainder| eqq!(remainder, 0))
        },
        rhs: {
            let first_linear = &c__ + &d__ * x_;
            let quotient = rubi_polynomial_quotient(&px__, &first_linear, x_).rubi_rhs();
            let integrand = quotient
                    * first_linear.pow(&m_ + 1)
                    * (&e__ + &f__ * x_).pow(&n_)
                    * (&a__ + &b__ * x_.pow(2)).pow(&p_);
            rubi_rhs_int(&integrand, x_)
        },
    ));
}

fn push_rules_rule_2348(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, p_, px__, x_);
    rules.push(rubi_rule!(
        order: 2348,
        source: "Int[Px_*(c_+d_.*x_)^m_.*(e_+f_.*x_)^n_.*(a_.+b_.*x_^2)^p_.,x_Symbol] :=
          Int[ExpandIntegrand[Px*(c+d*x)^m*(e+f*x)^n*(a+b*x^2)^p,x],x] /;
        FreeQ[{a,b,c,d,e,f,m,n,p},x] && PolyQ[Px,x] && (IntegerQ[p] || IntegerQ[2*p] && IntegerQ[m] && ILtQ[n,0]) && Not[IGtQ[m,0] && IGtQ[n,0]]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [px__, c__, d__, m_, e__, f__, n_, a__, b__, p_, x_],
        optional: [d__, m_, f__, n_, a__, b__, p_],
        x_free: [a__, b__, c__, d__, e__, f__, m_, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_, p_], x_)
                && rubi_poly_q(&px__, x_)
                && (integerq!(p_)
                    || integerq!(Atom::num(2) * &p_) && integerq!(m_) && iltq!(n_, 0))
                && !(igtq!(m_, 0) && igtq!(n_, 0))
        },
        rhs: {
            let integrand = px__
                * (&c__ + &d__ * x_).pow(&m_)
                * (&e__ + &f__ * x_).pow(&n_)
                * (&a__ + &b__ * x_.pow(2)).pow(&p_);
            let expanded = rubi_expand_integrand(&integrand, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_2349(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, p_, px__, x_);
    rules.push(rubi_rule!(
        order: 2349,
        source: "Int[Px_*(c_+d_.*x_)^m_.*(e_+f_.*x_)^n_.*(a_.+b_.*x_^2)^p_.,x_Symbol] :=
          Int[PolynomialQuotient[Px,c+d*x,x]*(c+d*x)^(m+1)*(e+f*x)^n*(a+b*x^2)^p,x] +
          PolynomialRemainder[Px,c+d*x,x] \\[Star] Int[(c+d*x)^m*(e+f*x)^n*(a+b*x^2)^p,x]/;
        FreeQ[{a,b,c,d,e,f,n,p},x] && PolynomialQ[Px,x] && LtQ[m,0] && Not[IntegerQ[n]] && IntegersQ[2*m,2*n,2*p]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [px__, c__, d__, m_, e__, f__, n_, a__, b__, p_, x_],
        optional: [d__, m_, f__, n_, a__, b__, p_],
        x_free: [a__, b__, c__, d__, e__, f__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, n_, p_], x_)
                && rubi_polynomial_q(&px__, x_)
                && ltq!(m_, 0)
                && !integerq!(n_)
                && integersq!([
                    Atom::num(2) * &m_,
                    Atom::num(2) * &n_,
                    Atom::num(2) * &p_,
                ])
        },
        rhs: {
            let first_linear = &c__ + &d__ * x_;
            let second_linear = &e__ + &f__ * x_;
            let quadratic = &a__ + &b__ * x_.pow(2);
            let quotient = rubi_polynomial_quotient(&px__, &first_linear, x_).rubi_rhs();
            let remainder = rubi_polynomial_remainder(&px__, &first_linear, x_).rubi_rhs();
            let quotient_integrand = quotient
                    * first_linear.pow(&m_ + 1)
                    * second_linear.pow(&n_)
                    * quadratic.pow(&p_);
            let quotient_integral = rubi_rhs_int(&quotient_integrand, x_);
            let base_integrand = first_linear.pow(&m_)
                    * second_linear.pow(&n_)
                    * quadratic.pow(&p_);
            let base_integral = rubi_rhs_int(&base_integrand, x_);
            quotient_integral + rubi_star(remainder, base_integral)
        },
    ));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn downvalue_2348_expands_the_tangent_substitution_payload() {
        let x = symbol!("x");
        let payload = parse!("(A+B*x+C*x^2)/((1+x^2)*(a+b*x)^(1/2)*(c+d*x)^(1/2))");
        let expanded = rubi_expand_integrand(&payload, x);
        let x_atom = Atom::var(x);
        let i = Atom::i();
        let a = Atom::var(symbol!("a"));
        let b = Atom::var(symbol!("b"));
        let c = Atom::var(symbol!("c"));
        let d = Atom::var(symbol!("d"));
        let coefficient_a = Atom::var(symbol!("A"));
        let coefficient_b = Atom::var(symbol!("B"));
        let coefficient_c = Atom::var(symbol!("C"));
        let radical = (a + b * &x_atom).sqrt() * (c + d * &x_atom).sqrt();
        let expected = &coefficient_c / &radical
            + (-&coefficient_b + &i * (&coefficient_a - &coefficient_c))
                / (2 * (&i - &x_atom) * &radical)
            + (&coefficient_b + &i * (coefficient_a - coefficient_c))
                / (2 * (i + x_atom) * radical);

        assert!(
            eqq!(expanded, expected),
            "Rubi ExpandIntegrand should reproduce Mathematica's linear-pole split: {expanded}"
        );
        assert!(
            (expanded - payload).together().is_zero(),
            "expanded payload must remain algebraically equivalent"
        );
    }

    #[test]
    fn downvalue_2348_matches_its_source_factorization() {
        let x = symbol!("x");
        let integrand = parse!("x*(1+x)/((2+x)*(3+x^2))");
        let rule = rubi_rules()
            .iter()
            .find(|rule| rule.downvalue_order == Some(2348))
            .expect("Rubi DownValue 2348 should be registered");

        assert!(
            matcher_rule(&integrand, x, rule).is_some(),
            "DownValue 2348 should match its source factorization: {}",
            rule.replacement.pat
        );
    }
}

// Generated shared pattern builders.

#[inline(never)]
fn rubi_shared_pattern_0(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let px__ = symbols.px__;
    let x_ = symbols.x_;
    px__ * (c__ + d__ * x_).pow(m_) * (e__ + f__ * x_).pow(n_) * (a__ + b__ * x_.pow(2)).pow(p_)
}
