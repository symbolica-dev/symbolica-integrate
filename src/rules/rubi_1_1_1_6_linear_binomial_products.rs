use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_2112(rules);
    push_rules_rule_2113(rules);
    push_rules_rule_2114(rules);
    push_rules_rule_2115(rules);
    push_rules_rule_2116(rules);
    push_rules_rule_2117(rules);
    push_rules_rule_2118(rules);
}

fn push_rules_rule_2112(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, px__, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 2112,
        source: "Int[Px_*(a_.+b_.*x_)^m_.*(c_.+d_.*x_)^n_.*(e_.+f_.*x_)^p_.,x_Symbol] :=
          Int[Px*(a*c+b*d*x^2)^m*(e+f*x)^p,x] /;
        FreeQ[{a,b,c,d,e,f,m,n,p},x] && PolyQ[Px,x] && EqQ[b*c+a*d,0] && EqQ[m,n] && (IntegerQ[m] || GtQ[a,0] && GtQ[c,0])",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [px__, a__, b__, c__, d__, e__, f__, m_, n_, p_, x_],
        optional: [a__, b__, c__, d__, e__, f__, m_, n_, p_],
        x_free: [a__, b__, c__, d__, e__, f__, m_, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_, p_], x_)
                && poly_q(&px__, x_)
                && eqq!(&b__ * &c__ + &a__ * &d__, Atom::num(0))
                && eqq!(m_, n_)
                && (integerq!(m_) || gtq!(a__, 0) && gtq!(c__, 0))
        },
        rhs: {
            let quadratic = &a__ * &c__ + &b__ * &d__ * x_.pow(2);
            let third = e__ + f__ * x_;
            let recursive_integrand = px__ * quadratic.pow(m_) * third.pow(p_);
            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_2113(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, px__, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 2113,
        source: "Int[Px_*(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_*(e_.+f_.*x_)^p_.,x_Symbol] :=
          (a+b*x)^FracPart[m]*(c+d*x)^FracPart[m]/(a*c+b*d*x^2)^FracPart[m] \\[Star] Int[Px*(a*c+b*d*x^2)^m*(e+f*x)^p,x] /;
        FreeQ[{a,b,c,d,e,f,m,n,p},x] && PolyQ[Px,x] && EqQ[b*c+a*d,0] && EqQ[m,n] && Not[IntegerQ[m]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [px__, a__, b__, c__, d__, e__, f__, m_, n_, p_, x_],
        optional: [a__, b__, c__, d__, e__, f__, p_],
        x_free: [a__, b__, c__, d__, e__, f__, m_, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_, p_], x_)
                && poly_q(&px__, x_)
                && eqq!(&b__ * &c__ + &a__ * &d__, Atom::num(0))
                && eqq!(m_, n_)
                && !integerq!(m_)
        },
        rhs: {
            let first = &a__ + &b__ * x_;
            let second = &c__ + &d__ * x_;
            let quadratic = &a__ * &c__ + &b__ * &d__ * x_.pow(2);
            let third = &e__ + &f__ * x_;
            let primitive = rubi_rhs_int(
                &(&px__ * quadratic.pow(&m_) * third.pow(&p_)),
                x_,
            );
            let frac = rubi_frac_part(&m_);
            let multiplier = first.pow(&frac) * second.pow(&frac) / quadratic.pow(frac);
            rubi_star(multiplier, primitive)
        },
    ));
}

fn push_rules_rule_2114(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, px__, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 2114,
        source: "Int[Px_*(a_.+b_.*x_)^m_.*(c_.+d_.*x_)^n_.*(e_.+f_.*x_)^p_.,x_Symbol] :=
          Int[PolynomialQuotient[Px,a+b*x,x]*(a+b*x)^(m+1)*(c+d*x)^n*(e+f*x)^p,x] /;
        FreeQ[{a,b,c,d,e,f,m,n,p},x] && PolyQ[Px,x] && EqQ[PolynomialRemainder[Px,a+b*x,x],0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [px__, a__, b__, c__, d__, e__, f__, m_, n_, p_, x_],
        optional: [a__, b__, c__, d__, e__, f__, m_, n_, p_],
        x_free: [a__, b__, c__, d__, e__, f__, m_, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_, p_], x_)
                && poly_q(&px__, x_)
                && rubi_polynomial_remainder(&px__, &(&a__ + &b__ * x_), x_)
                    .is_some_and(|remainder| remainder.is_zero())
        },
        rhs: {
            let first = &a__ + &b__ * x_;
            let second = c__ + d__ * x_;
            let third = e__ + f__ * x_;
            let qx = rubi_polynomial_quotient(&px__, &first, x_).rubi_rhs();
            rubi_rhs_int(
                &(qx * first.pow(&m_ + 1) * second.pow(n_) * third.pow(p_)),
                x_,
            )
        },
    ));
}

fn push_rules_rule_2115(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, px__, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 2115,
        source: "Int[Px_*(a_.+b_.*x_)^m_.*(c_.+d_.*x_)^n_.*(e_.+f_.*x_)^p_.,x_Symbol] :=
          Int[ExpandIntegrand[Px*(a+b*x)^m*(c+d*x)^n*(e+f*x)^p,x],x] /;
        FreeQ[{a,b,c,d,e,f,m,n,p},x] && PolyQ[Px,x] && IntegersQ[m,n]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [px__, a__, b__, c__, d__, e__, f__, m_, n_, p_, x_],
        optional: [a__, b__, c__, d__, e__, f__, m_, n_, p_],
        x_free: [a__, b__, c__, d__, e__, f__, m_, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_, p_], x_)
                && poly_q(&px__, x_)
                && integersq!([m_, n_])
        },
        rhs: {
            let first = a__ + b__ * x_;
            let second = c__ + d__ * x_;
            let third = e__ + f__ * x_;
            let integrand = px__ * first.pow(m_) * second.pow(n_) * third.pow(p_);
            let expanded = rubi_expand_integrand(&integrand, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_2116(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, px__, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 2116,
        source: "Int[Px_*(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_.*(e_.+f_.*x_)^p_.,x_Symbol] :=
          With[{Qx=PolynomialQuotient[Px,a+b*x,x], R=PolynomialRemainder[Px,a+b*x,x]},
          b*R*(a+b*x)^(m+1)*(c+d*x)^(n+1)*(e+f*x)^(p+1)/((m+1)*(b*c-a*d)*(b*e-a*f)) +
          1/((m+1)*(b*c-a*d)*(b*e-a*f)) \\[Star] Int[(a+b*x)^(m+1)*(c+d*x)^n*(e+f*x)^p*
            ExpandToSum[(m+1)*(b*c-a*d)*(b*e-a*f)*Qx+a*d*f*R*(m+1)-b*R*(d*e*(m+n+2)+c*f*(m+p+2))-b*d*f*R*(m+n+p+3)*x,x],x]] /;
        FreeQ[{a,b,c,d,e,f,n,p},x] && PolyQ[Px,x] && ILtQ[m,-1]",
        desc: "Algebraic expansion and nondegenerate trilinear recurrence 3",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [px__, a__, b__, c__, d__, e__, f__, m_, n_, p_, x_],
        optional: [a__, b__, c__, d__, e__, f__, n_, p_],
        x_free: [a__, b__, c__, d__, e__, f__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, n_, p_], x_)
                && poly_q(&px__, x_)
                && iltq!(m_, -1)
        },
        rhs: {
            let first = &a__ + &b__ * x_;
            let second = &c__ + &d__ * x_;
            let third = &e__ + &f__ * x_;
            let qx = rubi_polynomial_quotient(&px__, &first, x_).rubi_rhs();
            let r = rubi_polynomial_remainder(&px__, &first, x_).rubi_rhs();
            let m1 = &m_ + 1;
            let bc_ad = &b__ * &c__ - &a__ * &d__;
            let be_af = &b__ * &e__ - &a__ * &f__;
            let denominator = &m1 * &bc_ad * &be_af;
            let payload = rubi_expand_to_sum(
                &(&m1 * &bc_ad * &be_af * qx
                    + &a__ * &d__ * &f__ * &r * &m1
                    - &b__
                        * &r
                        * (&d__ * &e__ * (&m_ + &n_ + 2) + &c__ * &f__ * (&m_ + &p_ + 2))
                    - &b__ * &d__ * &f__ * &r * (&m_ + &n_ + &p_ + 3) * x_),
                x_
            );
            let direct = &b__
                * &r
                * first.pow(&m1)
                * second.pow(&n_ + 1)
                * third.pow(&p_ + 1)
                / &denominator;
            let recursive_integrand = first.pow(m1) * second.pow(n_) * third.pow(p_) * payload;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_2117(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, px__, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 2117,
        source: "Int[Px_*(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_.*(e_.+f_.*x_)^p_.,x_Symbol] :=
          With[{Qx=PolynomialQuotient[Px,a+b*x,x], R=PolynomialRemainder[Px,a+b*x,x]},
          b*R*(a+b*x)^(m+1)*(c+d*x)^(n+1)*(e+f*x)^(p+1)/((m+1)*(b*c-a*d)*(b*e-a*f)) +
          1/((m+1)*(b*c-a*d)*(b*e-a*f)) \\[Star] Int[(a+b*x)^(m+1)*(c+d*x)^n*(e+f*x)^p*
            ExpandToSum[(m+1)*(b*c-a*d)*(b*e-a*f)*Qx+a*d*f*R*(m+1)-b*R*(d*e*(m+n+2)+c*f*(m+p+2))-b*d*f*R*(m+n+p+3)*x,x],x]] /;
        FreeQ[{a,b,c,d,e,f,n,p},x] && PolyQ[Px,x] && LtQ[m,-1] && IntegersQ[2*m,2*n,2*p]",
        desc: "Algebraic expansion and nondegenerate trilinear recurrence 3",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [px__, a__, b__, c__, d__, e__, f__, m_, n_, p_, x_],
        optional: [a__, b__, c__, d__, e__, f__, n_, p_],
        x_free: [a__, b__, c__, d__, e__, f__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, n_, p_], x_)
                && poly_q(&px__, x_)
                && ltq!(m_, -1)
                && integersq!([Atom::num(2) * &m_, Atom::num(2) * &n_, Atom::num(2) * &p_])
        },
        rhs: {
            let first = &a__ + &b__ * x_;
            let second = &c__ + &d__ * x_;
            let third = &e__ + &f__ * x_;
            let qx = rubi_polynomial_quotient(&px__, &first, x_).rubi_rhs();
            let r = rubi_polynomial_remainder(&px__, &first, x_).rubi_rhs();
            let m1 = &m_ + 1;
            let bc_ad = &b__ * &c__ - &a__ * &d__;
            let be_af = &b__ * &e__ - &a__ * &f__;
            let denominator = &m1 * &bc_ad * &be_af;
            let payload = rubi_expand_to_sum(
                &(&m1 * &bc_ad * &be_af * qx
                    + &a__ * &d__ * &f__ * &r * &m1
                    - &b__
                        * &r
                        * (&d__ * &e__ * (&m_ + &n_ + 2) + &c__ * &f__ * (&m_ + &p_ + 2))
                    - &b__ * &d__ * &f__ * &r * (&m_ + &n_ + &p_ + 3) * x_),
                x_
            );
            let direct = &b__
                * &r
                * first.pow(&m1)
                * second.pow(&n_ + 1)
                * third.pow(&p_ + 1)
                / &denominator;
            let recursive_integrand = first.pow(m1) * second.pow(n_) * third.pow(p_) * payload;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_2118(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, px__, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 2118,
        source: "Int[Px_*(a_.+b_.*x_)^m_.*(c_.+d_.*x_)^n_.*(e_.+f_.*x_)^p_.,x_Symbol] :=
          With[{q=Expon[Px,x],k=Coeff[Px,x,Expon[Px,x]]},
          k*(a+b*x)^(m+q-1)*(c+d*x)^(n+1)*(e+f*x)^(p+1)/(d*f*b^(q-1)*(m+n+p+q+1)) +
          1/(d*f*b^q*(m+n+p+q+1)) \\[Star] Int[(a+b*x)^m*(c+d*x)^n*(e+f*x)^p*
            ExpandToSum[d*f*b^q*(m+n+p+q+1)*Px-d*f*k*(m+n+p+q+1)*(a+b*x)^q +
              k*(a+b*x)^(q-2)*(a^2*d*f*(m+n+p+q+1)-b*(b*c*e*(m+q-1)+a*(d*e*(n+1)+c*f*(p+1)))+
                b*(a*d*f*(2*(m+q)+n+p)-b*(d*e*(m+q+n)+c*f*(m+q+p)))*x),x],x] /;
          NeQ[m+n+p+q+1,0]] /;
        FreeQ[{a,b,c,d,e,f,m,n,p},x] && PolyQ[Px,x]",
        desc: "Algebraic expansion and nondegenerate trilinear recurrence 2",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [px__, a__, b__, c__, d__, e__, f__, m_, n_, p_, x_],
        optional: [a__, b__, c__, d__, e__, f__, m_, n_, p_],
        x_free: [a__, b__, c__, d__, e__, f__, m_, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_, p_], x_)
                && poly_q(&px__, x_)
                && rubi_expon(&px__, x_).is_some_and(|q| {
                    neq!(&m_ + &n_ + &p_ + Atom::num(q + 1), Atom::num(0))
                })
        },
        rhs: {
            let q = rubi_expon(&px__, x_).rubi_rhs();
            let k = rubi_coeff(&px__, x_, q).rubi_rhs();
            let q_atom = Atom::num(q);
            let first = &a__ + &b__ * x_;
            let second = &c__ + &d__ * x_;
            let third = &e__ + &f__ * x_;
            let exponent_sum = &m_ + &n_ + &p_ + &q_atom + 1;
            let b_q = b__.pow(&q_atom);
            let direct_denominator = &d__ * &f__ * b__.pow(q - 1) * &exponent_sum;
            let recursive_denominator = &d__ * &f__ * &b_q * &exponent_sum;
            let direct = &k
                * first.pow(&m_ + &q_atom - 1)
                * second.pow(&n_ + 1)
                * third.pow(&p_ + 1)
                / &direct_denominator;
            let payload = rubi_expand_to_sum(
                &(&d__ * &f__ * &b_q * &exponent_sum * &px__
                    - &d__ * &f__ * &k * &exponent_sum * first.pow(&q_atom)
                    + &k
                        * first.pow(q - 2)
                        * (&a__ * &a__ * &d__ * &f__ * &exponent_sum
                            - &b__
                                * (&b__ * &c__ * &e__ * (&m_ + &q_atom - 1)
                                    + &a__
                                        * (&d__ * &e__ * (&n_ + 1)
                                            + &c__ * &f__ * (&p_ + 1)))
                            + &b__
                                * (&a__
                                    * &d__
                                    * &f__
                                    * (Atom::num(2) * (&m_ + &q_atom) + &n_ + &p_)
                                    - &b__
                                        * (&d__ * &e__ * (&m_ + &q_atom + &n_)
                                            + &c__ * &f__ * (&m_ + &q_atom + &p_)))
                                * x_)),
                x_,
            );
            let recursive_integrand = first.pow(m_) * second.pow(n_) * third.pow(p_) * payload;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            rubi_simp(&(direct), x_)
                    + rubi_star(Atom::num(1) / recursive_denominator, recursive)
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
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let px__ = symbols.px__;
    let x_ = symbols.x_;
    px__ * (a__ + b__ * x_).pow(m_) * (c__ + d__ * x_).pow(n_) * (e__ + f__ * x_).pow(p_)
}
