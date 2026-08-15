use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_2152(rules);
    push_rules_rule_2153(rules);
    push_rules_rule_2154(rules);
}

fn push_rules_rule_2152(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, px__, x_);
    rules.push(rubi_rule!(
        order: 2152,
        source: "Int[Px_*(d_.+e_.*x_)^m_.*(f_.+g_.*x_)^n_.*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
          Int[PolynomialQuotient[Px,d+e*x,x]*(d+e*x)^(m+1)*(f+g*x)^n*(a+b*x+c*x^2)^p,x] /;
        FreeQ[{a,b,c,d,e,f,g,m,n,p},x] && PolynomialQ[Px,x] && EqQ[PolynomialRemainder[Px,d+e*x,x],0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [px__, d__, e__, m_, f__, g__, n_, a__, b__, c__, p_, x_],
        optional: [d__, e__, m_, f__, g__, n_, a__, b__, c__, p_],
        when: {
            let first_linear = &d__ + &e__ * x_;
            freeq!([a__, b__, c__, d__, e__, f__, g__, m_, n_, p_], x_)
                && rubi_polynomial_q(&px__, x_)
                && rubi_polynomial_remainder(&px__, &first_linear, x_)
                    .is_some_and(|remainder| eqq!(remainder, 0))
        },
        rhs: {
            let first_linear = &d__ + &e__ * x_;
            let quotient = rubi_polynomial_quotient(&px__, &first_linear, x_).rubi_rhs();
            let transformed = quotient
                * first_linear.pow(&m_ + 1)
                * (&f__ + &g__ * x_).pow(&n_)
                * (&a__ + &b__ * x_ + &c__ * x_.pow(2)).pow(&p_);

            rubi_rhs_int(&transformed, x_)
        },
    ));
}

fn push_rules_rule_2153(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, px__, x_);
    rules.push(rubi_rule!(
        order: 2153,
        source: "Int[Px_*(d_.+e_.*x_)^m_.*(f_.+g_.*x_)^n_.*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
          Int[ExpandIntegrand[Px*(d+e*x)^m*(f+g*x)^n*(a+b*x+c*x^2)^p,x],x] /;
        FreeQ[{a,b,c,d,e,f,g,m,n,p},x] && PolyQ[Px,x] && (IntegerQ[p] || IntegerQ[2*p] && IntegerQ[m] && ILtQ[n,0]) && Not[IGtQ[m,0] && IGtQ[n,0]]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [px__, d__, e__, m_, f__, g__, n_, a__, b__, c__, p_, x_],
        optional: [d__, e__, m_, f__, g__, n_, a__, b__, c__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, m_, n_, p_], x_)
                && poly_q(&px__, x_)
                && (integerq!(p_)
                    || integerq!(Atom::num(2) * &p_)
                        && integerq!(m_)
                        && iltq!(n_, 0))
                && !(igtq!(m_, 0) && igtq!(n_, 0))
        },
        rhs: {
            let integrand = &px__
                * (&d__ + &e__ * x_).pow(&m_)
                * (&f__ + &g__ * x_).pow(&n_)
                * (&a__ + &b__ * x_ + &c__ * x_.pow(2)).pow(&p_);
            let expanded = rubi_expand_integrand(&integrand, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_2154(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, px__, x_);
    rules.push(rubi_rule!(
        order: 2154,
        source: "Int[Px_*(d_.+e_.*x_)^m_.*(f_.+g_.*x_)^n_.*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
          Int[PolynomialQuotient[Px,d+e*x,x]*(d+e*x)^(m+1)*(f+g*x)^n*(a+b*x+c*x^2)^p,x] +
          PolynomialRemainder[Px,d+e*x,x] \\[Star] Int[(d+e*x)^m*(f+g*x)^n*(a+b*x+c*x^2)^p,x]/;
        FreeQ[{a,b,c,d,e,f,g,n,p},x] && PolynomialQ[Px,x] && LtQ[m,0] && Not[IntegerQ[n]] && IntegersQ[2*m,2*n,2*p]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [px__, d__, e__, m_, f__, g__, n_, a__, b__, c__, p_, x_],
        optional: [d__, e__, m_, f__, g__, n_, a__, b__, c__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, n_, p_], x_)
                && rubi_polynomial_q(&px__, x_)
                && ltq!(m_, 0)
                && !integerq!(n_)
                && integersq!([
                    Atom::num(2) * &m_,
                    Atom::num(2) * &n_,
                    Atom::num(2) * &p_
                ])
        },
        rhs: {
            let first_linear = &d__ + &e__ * x_;
            let second_linear = &f__ + &g__ * x_;
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let quotient = rubi_polynomial_quotient(&px__, &first_linear, x_).rubi_rhs();
            let remainder = rubi_polynomial_remainder(&px__, &first_linear, x_).rubi_rhs();
            let first = rubi_rhs_int(
                &(quotient
                    * first_linear.pow(&m_ + 1)
                    * second_linear.pow(&n_)
                    * quadratic.pow(&p_)),
                x_,
            );
            let second = rubi_rhs_int(
                &(first_linear.pow(&m_)
                    * second_linear.pow(&n_)
                    * quadratic.pow(&p_)),
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
    let f__ = symbols.f__;
    let g__ = symbols.g__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let px__ = symbols.px__;
    let x_ = symbols.x_;
    px__ * (d__ + e__ * x_).pow(m_)
        * (f__ + g__ * x_).pow(n_)
        * (a__ + b__ * x_ + c__ * x_.pow(2)).pow(p_)
}
