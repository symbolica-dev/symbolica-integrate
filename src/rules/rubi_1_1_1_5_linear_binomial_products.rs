use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_2119(rules);
    push_rules_rule_2120(rules);
    push_rules_rule_2121(rules);
    push_rules_rule_2122(rules);
    push_rules_rule_2123(rules);
    push_rules_rule_2124(rules);
    push_rules_rule_2125(rules);
}

fn push_rules_rule_2119(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, px__, x_);
    rules.push(rubi_rule!(
        order: 2119,
        source: "Int[Px_*(a_.+b_.*x_)^m_.*(c_.+d_.*x_)^n_.,x_Symbol] :=
          Int[Px*(a*c+b*d*x^2)^m,x] /;
        FreeQ[{a,b,c,d,m,n},x] && PolyQ[Px,x] && EqQ[b*c+a*d,0] && EqQ[m,n] && (IntegerQ[m] || GtQ[a,0] && GtQ[c,0])",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [px__, a__, b__, c__, d__, m_, n_, x_],
        optional: [a__, b__, c__, d__, m_, n_],
        x_free: [a__, b__, c__, d__, m_, n_],
        when: {
            freeq!([a__, b__, c__, d__, m_, n_], x_)
                && poly_q(&px__, x_)
                && eqq!(&b__ * &c__ + &a__ * &d__, Atom::num(0))
                && eqq!(m_, n_)
                && (integerq!(m_) || gtq!(a__, 0) && gtq!(c__, 0))
        },
        rhs: {
            let transformed_integrand =
                &px__ * (&a__ * &c__ + &b__ * &d__ * x_.pow(2)).pow(&m_);
            rubi_rhs_int(&transformed_integrand, x_)
        },
    ));
}

fn push_rules_rule_2120(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, px__, x_);
    rules.push(rubi_rule!(
        order: 2120,
        source: "Int[Px_*(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_,x_Symbol] :=
          (a+b*x)^FracPart[m]*(c+d*x)^FracPart[m]/(a*c+b*d*x^2)^FracPart[m] \\[Star] Int[Px*(a*c+b*d*x^2)^m,x] /;
        FreeQ[{a,b,c,d,m,n},x] && PolyQ[Px,x] && EqQ[b*c+a*d,0] && EqQ[m,n] && Not[IntegerQ[m]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [px__, a__, b__, c__, d__, m_, n_, x_],
        optional: [a__, b__, c__, d__],
        x_free: [a__, b__, c__, d__, m_, n_],
        when: {
            freeq!([a__, b__, c__, d__, m_, n_], x_)
                && poly_q(&px__, x_)
                && eqq!(&b__ * &c__ + &a__ * &d__, Atom::num(0))
                && eqq!(m_, n_)
                && !integerq!(m_)
        },
        rhs: {
            let first = &a__ + &b__ * x_;
            let second = &c__ + &d__ * x_;
            let quadratic = &a__ * &c__ + &b__ * &d__ * x_.pow(2);
            let fractional_part = rubi_frac_part(&m_);
            let multiplier = first.pow(&fractional_part) * second.pow(&fractional_part)
                / quadratic.pow(fractional_part);
            let primitive = rubi_rhs_int(&(&px__ * quadratic.pow(&m_)), x_);
            rubi_star(multiplier, primitive)
        },
    ));
}

fn push_rules_rule_2121(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, px__, x_);
    rules.push(rubi_rule!(
        order: 2121,
        source: "Int[Px_*(a_.+b_.*x_)^m_.*(c_.+d_.*x_)^n_.,x_Symbol] :=
          Int[PolynomialQuotient[Px,a+b*x,x]*(a+b*x)^(m+1)*(c+d*x)^n,x] /;
        FreeQ[{a,b,c,d,m,n},x] && PolyQ[Px,x] && EqQ[PolynomialRemainder[Px,a+b*x,x],0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [px__, a__, b__, c__, d__, m_, n_, x_],
        optional: [a__, b__, c__, d__, m_, n_],
        x_free: [a__, b__, c__, d__, m_, n_],
        when: {
            freeq!([a__, b__, c__, d__, m_, n_], x_)
                && poly_q(&px__, x_)
                && rubi_polynomial_remainder(&px__, &(&a__ + &b__ * x_), x_)
                    .is_some_and(|remainder| remainder.is_zero())
        },
        rhs: {
            let first = &a__ + &b__ * x_;
            let second = &c__ + &d__ * x_;
            let quotient = rubi_polynomial_quotient(&px__, &first, x_).rubi_rhs();
            rubi_rhs_int(
                &(quotient * first.pow(&m_ + Atom::num(1)) * second.pow(&n_)),
                x_,
            )
        },
    ));
}

fn push_rules_rule_2122(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, n_, px__, x_);
    rules.push(rubi_rule!(
        order: 2122,
        source: "Int[Px_*(c_.+d_.*x_)^n_/(a_.+b_.*x_),x_Symbol] :=
          Int[ExpandIntegrand[1/Sqrt[c+d*x],Px*(c+d*x)^(n+1/2)/(a+b*x),x],x] /;
        FreeQ[{a,b,c,d,n},x] && PolyQ[Px,x] && ILtQ[n+1/2,0]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern: px__ * (c__ + d__ * x_).pow(n_) / (a__ + b__ * x_),
        with: [px__, a__, b__, c__, d__, n_, x_],
        optional: [a__, b__, c__, d__],
        x_free: [a__, b__, c__, d__, n_],
        when: {
            freeq!([a__, b__, c__, d__, n_], x_)
                && poly_q(&px__, x_)
                && iltq!(&n_ + Atom::num(1) / Atom::num(2), 0)
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let u = Atom::num(1) / &linear.sqrt();
            let v = &px__ * linear.pow(&n_ + Atom::num(1) / Atom::num(2))
                / (&a__ + &b__ * x_);
            let expanded = rubi_expand_integrand_product(&u, &v, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_2123(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, px__, x_);
    rules.push(rubi_rule!(
        order: 2123,
        source: "Int[Px_*(a_.+b_.*x_)^m_.*(c_.+d_.*x_)^n_.,x_Symbol] :=
          Int[ExpandIntegrand[Px*(a+b*x)^m*(c+d*x)^n,x],x] /;
        FreeQ[{a,b,c,d,m,n},x] && PolyQ[Px,x] && (IntegersQ[m,n] || IGtQ[m,-2])",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [px__, a__, b__, c__, d__, m_, n_, x_],
        optional: [a__, b__, c__, d__, m_, n_],
        x_free: [a__, b__, c__, d__, m_, n_],
        when: {
            freeq!([a__, b__, c__, d__, m_, n_], x_)
                && poly_q(&px__, x_)
                && (integersq!([m_, n_]) || igtq!(m_, -2))
        },
        rhs: {
            let integrand = &px__
                * (&a__ + &b__ * x_).pow(&m_)
                * (&c__ + &d__ * x_).pow(&n_);
            let expanded = rubi_expand_integrand(&integrand, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_2124(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, px__, x_);
    rules.push(rubi_rule!(
        order: 2124,
        source: "Int[Px_*(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_.,x_Symbol] :=
          With[{Qx=PolynomialQuotient[Px,a+b*x,x], R=PolynomialRemainder[Px,a+b*x,x]},
          R*(a+b*x)^(m+1)*(c+d*x)^(n+1)/((m+1)*(b*c-a*d)) +
          1/((m+1)*(b*c-a*d)) \\[Star] Int[(a+b*x)^(m+1)*(c+d*x)^n*ExpandToSum[(m+1)*(b*c-a*d)*Qx-d*R*(m+n+2),x],x]] /;
        FreeQ[{a,b,c,d,n},x] && PolyQ[Px,x] && LtQ[m,-1] && (IntegerQ[m] || Not[ILtQ[n,-1]])",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [px__, a__, b__, c__, d__, m_, n_, x_],
        optional: [a__, b__, c__, d__, n_],
        x_free: [a__, b__, c__, d__, n_],
        when: {
            freeq!([a__, b__, c__, d__, n_], x_)
                && poly_q(&px__, x_)
                && ltq!(m_, -1)
                && (integerq!(m_) || !iltq!(n_, -1))
        },
        rhs: {
            let first = &a__ + &b__ * x_;
            let second = &c__ + &d__ * x_;
            let qx = rubi_polynomial_quotient(&px__, &first, x_).rubi_rhs();
            let r = rubi_polynomial_remainder(&px__, &first, x_).rubi_rhs();
            let m1 = &m_ + Atom::num(1);
            let determinant = &b__ * &c__ - &a__ * &d__;
            let denominator = &m1 * &determinant;
            let direct = &r
                * first.pow(&m1)
                * second.pow(&n_ + Atom::num(1))
                / &denominator;
            let payload = rubi_expand_to_sum(
                &(&m1 * &determinant * qx - &d__ * &r * (&m_ + &n_ + Atom::num(2))),
                x_,
            );
            let recursive = rubi_rhs_int(
                &(first.pow(m1) * second.pow(n_) * payload),
                x_,
            );
            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_2125(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, px__, x_);
    rules.push(rubi_rule!(
        order: 2125,
        source: "Int[Px_*(a_.+b_.*x_)^m_.*(c_.+d_.*x_)^n_.,x_Symbol] :=
          With[{q=Expon[Px,x],k=Coeff[Px,x,Expon[Px,x]]},
          k*(a+b*x)^(m+q)*(c+d*x)^(n+1)/(d*b^q*(m+n+q+1)) +
          1/(d*b^q*(m+n+q+1)) \\[Star] Int[(a+b*x)^m*(c+d*x)^n*
            ExpandToSum[d*b^q*(m+n+q+1)*Px-d*k*(m+n+q+1)*(a+b*x)^q-k*(b*c-a*d)*(m+q)*(a+b*x)^(q-1),x],x] /;
          NeQ[m+n+q+1,0]] /;
        FreeQ[{a,b,c,d,m,n},x] && PolyQ[Px,x]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [px__, a__, b__, c__, d__, m_, n_, x_],
        optional: [a__, b__, c__, d__, m_, n_],
        x_free: [a__, b__, c__, d__, m_, n_],
        when: {
            freeq!([a__, b__, c__, d__, m_, n_], x_)
                && poly_q(&px__, x_)
                && rubi_expon(&px__, x_)
                    .is_some_and(|q| neq!(&m_ + &n_ + Atom::num(q + 1), 0))
        },
        rhs: {
            let q = rubi_expon(&px__, x_).rubi_rhs();
            let k = rubi_coeff(&px__, x_, q).rubi_rhs();
            let q_atom = Atom::num(q);
            let first = &a__ + &b__ * x_;
            let second = &c__ + &d__ * x_;
            let exponent_sum = &m_ + &n_ + &q_atom + Atom::num(1);
            let denominator = &d__ * b__.pow(&q_atom) * &exponent_sum;
            let direct = &k
                * first.pow(&m_ + &q_atom)
                * second.pow(&n_ + Atom::num(1))
                / &denominator;
            let payload = rubi_expand_to_sum(
                &(&d__ * b__.pow(&q_atom) * &exponent_sum * &px__
                    - &d__ * &k * &exponent_sum * first.pow(&q_atom)
                    - &k
                        * (&b__ * &c__ - &a__ * &d__)
                        * (&m_ + &q_atom)
                        * first.pow(q - 1)),
                x_,
            );
            let recursive = rubi_rhs_int(
                &(first.pow(m_) * second.pow(n_) * payload),
                x_,
            );
            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / denominator, recursive)
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
    let n_ = symbols.n_;
    let px__ = symbols.px__;
    let x_ = symbols.x_;
    px__ * (a__ + b__ * x_).pow(m_) * (c__ + d__ * x_).pow(n_)
}
