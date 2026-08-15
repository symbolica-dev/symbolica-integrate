use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_2017(rules);
    push_rules_rule_2018(rules);
    push_rules_rule_2019(rules);
    push_rules_rule_2020(rules);
    push_rules_rule_2021(rules);
    push_rules_rule_2022(rules);
    push_rules_rule_2023(rules);
    push_rules_rule_2024(rules);
    push_rules_rule_2025(rules);
    push_rules_rule_2097(rules);
    push_rules_rule_2098(rules);
    push_rules_rule_2099(rules);
    push_rules_rule_2100(rules);
    push_rules_rule_2101(rules);
    push_rules_rule_2102(rules);
    push_rules_rule_2103(rules);
    push_rules_rule_2104(rules);
    push_rules_rule_2105(rules);
    push_rules_rule_2106(rules);
    push_rules_rule_2107(rules);
    push_rules_rule_2108(rules);
    push_rules_rule_2109(rules);
    push_rules_rule_2110(rules);
    push_rules_rule_2111(rules);
}

fn push_rules_rule_2017(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, n_, p_, px__, x_);
    rules.push(rubi_rule!(
        order: 2017,
        source: "Int[Px_*(a_+b_.*x_^n_)^p_,x_Symbol] :=
          Coeff[Px,x,n-1]*(a+b*x^n)^(p+1)/(b*n*(p+1)) +
          Int[(Px-Coeff[Px,x,n-1]*x^(n-1))*(a+b*x^n)^p,x] /;
        FreeQ[{a,b},x] && PolyQ[Px,x] && IGtQ[p,1] && IGtQ[n,1] && NeQ[Coeff[Px,x,n-1],0] && NeQ[Px,Coeff[Px,x,n-1]*x^(n-1)] &&
          Not[MatchQ[Px,Qx_.*(c_+d_.*x^m_)^q_ /;
            FreeQ[{c,d},x] && PolyQ[Qx,x] && IGtQ[q,1] && IGtQ[m,1] && NeQ[Coeff[Qx*(a+b*x^n)^p,x,m-1],0] && GtQ[m*q,n*p]]]",
        desc: "Algebraic expansion and power rule for integration",
        refs: [],
        pattern: px__ * (a__ + b__ * x_.pow(n_)).pow(p_),
        with: [px__, a__, b__, n_, p_, x_],
        optional: [b__],
        x_free: [a__, b__],
        when: {
            match integer_i64(&n_) {
                Some(n_integer) => {
                    let coefficient = rubi_coefficient(&px__, x_, n_integer - 1);
                    freeq!([a__, b__], x_)
                        && poly_q(&px__, x_)
                        && igtq!(p_, 1)
                        && igtq!(n_, 1)
                        && coefficient
                            .as_ref()
                            .is_some_and(|coefficient_value| neq!(&coefficient_value, 0))
                        && coefficient.as_ref().is_some_and(|coefficient_value| {
                            neq!(
                                px__,
                                coefficient_value * x_.pow(n_integer - 1)
                            )
                        })
                        && !rubi_conditional_match_q(
                            &px__,
                            Atom::var(rubi_symbols().qx__)
                                * (Atom::var(rubi_symbols().c__)
                                    + Atom::var(rubi_symbols().d__)
                                        * x_.pow(Atom::var(rubi_symbols().m_)))
                                .pow(Atom::var(rubi_symbols().q_)),
                            &[rubi_symbols().qx__, rubi_symbols().d__],
                            |matches| {
                                    rubi_symb!(qx__, c__, d__, m_, q_);
                                    let Some(qx) = wildcard_atom(matches, qx__) else {
                                        return false;
                                    };
                                    let Some(c) = wildcard_atom(matches, c__) else {
                                        return false;
                                    };
                                    let Some(d) = wildcard_atom(matches, d__) else {
                                        return false;
                                    };
                                    let Some(m) = wildcard_atom(matches, m_) else {
                                        return false;
                                    };
                                    let Some(q) = wildcard_atom(matches, q_) else {
                                        return false;
                                    };
                                    let Some(m_integer) = integer_i64(&m) else {
                                        return false;
                                    };
                                    let coefficient_source = &qx
                                        * (&a__
                                            + &b__ * x_.pow(&n_))
                                        .pow(&p_);

                                    freeq!([c, d], x_)
                                        && poly_q(&qx, x_)
                                        && igtq!(q, 1)
                                        && igtq!(m, 1)
                                        && rubi_coefficient(
                                            &coefficient_source,
                                            x_,
                                            m_integer - 1,
                                        )
                                        .is_some_and(|nested_coefficient| {
                                            neq!(nested_coefficient, 0)
                                        })
                                        && gtq!(&m * &q, &n_ * &p_)
                            },
                        )
                }
                None => false,
            }
        },
        rhs: {
            let p_integer = integer_i64(&p_).rubi_rhs();
            let n_integer = integer_i64(&n_).rubi_rhs();
            let coefficient = rubi_coefficient(&px__, x_, n_integer - 1).rubi_rhs();
            let coefficient_term = &coefficient * x_.pow(n_integer - 1);
            let remainder = &px__ - coefficient_term;
            let base = a__ + &b__ * x_.pow(n_integer);
            let direct = coefficient * base.pow(p_integer + 1)
                / (&b__ * n_integer * (p_integer + 1));
            let recursive_integrand = remainder * base.pow(p_integer);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            rubi_simp(&(direct), x_) + recursive
        },
    ));
}

fn push_rules_rule_2018(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, m_, n_, p_, px__, x_);
    rules.push(rubi_rule!(
        order: 2018,
        source: "Int[Px_*x_^m_.*(a_+b_.*x_^n_.)^p_,x_Symbol] :=
          Coeff[Px,x,n-m-1]*(a+b*x^n)^(p+1)/(b*n*(p+1)) +
          Int[(Px-Coeff[Px,x,n-m-1]*x^(n-m-1))*x^m*(a+b*x^n)^p,x] /;
        FreeQ[{a,b,m,n},x] && PolyQ[Px,x] && IGtQ[p,1] && IGtQ[n-m,0] && NeQ[Coeff[Px,x,n-m-1],0]",
        desc: "Algebraic expansion and power rule for integration",
        refs: [],
        pattern: px__ * x_.pow(m_) * (a__ + b__ * x_.pow(n_)).pow(p_),
        with: [px__, a__, b__, m_, n_, p_, x_],
        optional: [b__, m_, n_],
        x_free: [a__, b__, m_, n_],
        when: {
            match integer_i64(&(&n_ - &m_)) {
                Some(delta) => {
                    let coefficient = rubi_coefficient(&px__, x_, delta - 1);
                    freeq!([a__, b__, m_, n_], x_)
                        && poly_q(&px__, x_)
                        && igtq!(p_, 1)
                        && igtq!(&n_ - &m_, 0)
                        && coefficient
                            .as_ref()
                            .is_some_and(|coefficient_value| neq!(&coefficient_value, 0))
                }
                None => false,
            }
        },
        rhs: {
            let p_integer = integer_i64(&p_).rubi_rhs();
            let n_integer = integer_i64(&n_).rubi_rhs();
            let m_integer = integer_i64(&m_).rubi_rhs();
            let coefficient_degree = n_integer - m_integer - 1;
            if coefficient_degree < 0 {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }
            let coefficient = rubi_coefficient(&px__, x_, coefficient_degree).rubi_rhs();
            let coefficient_term = &coefficient * x_.pow(coefficient_degree);
            let remainder = &px__ - coefficient_term;
            let base = a__ + &b__ * x_.pow(n_integer);
            let direct = coefficient * base.pow(p_integer + 1)
                / (&b__ * n_integer * (p_integer + 1));
            let recursive_integrand =
                remainder * x_.pow(m_integer) * base.pow(p_integer);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            rubi_simp(&(direct), x_) + recursive
        },
    ));
}

fn push_rules_rule_2019(rules: &mut Vec<RubiRule>) {
    rubi_symb!(p_, px_, q_, u__, qx_);
    rules.push(rubi_rule!(
        order: 2019,
        source: "Int[u_.*Px_^p_.*Qx_^q_.,x_Symbol] :=
          Int[u*PolynomialQuotient[Px,Qx,x]^p*Qx^(p+q),x] /;
        FreeQ[q,x] && PolyQ[Px,x] && PolyQ[Qx,x] && EqQ[PolynomialRemainder[Px,Qx,x],0] && IntegerQ[p] && LtQ[p*q,0]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: u__ * px_.pow(p_) * qx_.pow(q_),
        with: [u__, px_, qx_, p_, q_, x_],
        optional: [u__, p_, q_],
        x_free: [q_],
        integer: [p_],
        when: {
            freeq!(q_, x_)
                && poly_q(&px_, x_)
                && poly_q(&qx_, x_)
                && rubi_polynomial_remainder(&px_, &qx_, x_)
                    .is_some_and(|remainder| eqq!(remainder, 0))
                && integerq!(p_)
                && ltq!(&p_ * &q_, 0)
        },
        rhs: {
            let quotient = rubi_polynomial_quotient(&px_, &qx_, x_).rubi_rhs();
            let transformed_integrand =
                u__ * quotient.pow(&p_) * qx_.pow(&p_ + &q_);
            rubi_rhs_int(&transformed_integrand, x_)
        },
    ));
}

fn push_rules_rule_2020(rules: &mut Vec<RubiRule>) {
    rubi_symb!(pp__, qq_);
    rules.push(rubi_rule!(
        order: 2020,
        source: "Int[Pp_/Qq_,x_Symbol] :=
          With[{p=Expon[Pp,x],q=Expon[Qq,x]},
          Coeff[Pp,x,p]*Log[RemoveContent[Qq,x]]/(q*Coeff[Qq,x,q])/;
         EqQ[p,q-1] && EqQ[Pp,Simplify[Coeff[Pp,x,p]/(q*Coeff[Qq,x,q])*D[Qq,x]]]] /;
        PolyQ[Pp,x] && PolyQ[Qq,x]",
        desc: "Reciprocal integration rule",
        refs: [],
        pattern: pp__ / qq_,
        with: [pp__, qq_, x_],
        when: {
            if poly_q(&pp__, x_) && poly_q(&qq_, x_) {
                match (rubi_expon(&pp__, x_), rubi_expon(&qq_, x_)) {
                    (Some(p), Some(q)) => {
                        if eqq!(Atom::num(p), Atom::num(q) - 1) {
                            let numerator_leading = rubi_coefficient(&pp__, x_, p);
                            let denominator_leading = rubi_coefficient(&qq_, x_, q);
                            match (numerator_leading, denominator_leading) {
                                (Some(p_coeff), Some(q_coeff)) => {
                                    let expected = rubi_simplify(
                                        &(&p_coeff * rubi_d(&qq_, x_)
                                            / (Atom::num(q) * &q_coeff)),
                                    );
                                    eqq!(pp__, expected)
                                }
                                _ => false,
                            }
                        } else {
                            false
                        }
                    }
                    _ => false,
                }
            } else {
                false
            }
        },
        rhs: {
            let p = rubi_expon(&pp__, x_).rubi_rhs();
            let q = rubi_expon(&qq_, x_).rubi_rhs();
            let p_coeff = rubi_coefficient(&pp__, x_, p).rubi_rhs();
            let q_coeff = rubi_coefficient(&qq_, x_, q).rubi_rhs();
            p_coeff * rubi_remove_content(&qq_, x_).log()
                    / (Atom::num(q) * q_coeff)
        },
    ));
}

fn push_rules_rule_2021(rules: &mut Vec<RubiRule>) {
    rubi_symb!(m_, pp__, qq_);
    rules.push(rubi_rule!(
        order: 2021,
        source: "Int[Pp_*Qq_^m_.,x_Symbol] :=
          With[{p=Expon[Pp,x],q=Expon[Qq,x]},
          Coeff[Pp,x,p]*x^(p-q+1)*Qq^(m+1)/((p+m*q+1)*Coeff[Qq,x,q]) /;
         NeQ[p+m*q+1,0] && EqQ[(p+m*q+1)*Coeff[Qq,x,q]*Pp,Coeff[Pp,x,p]*x^(p-q)*((p-q+1)*Qq+(m+1)*x*D[Qq,x])]] /;
        FreeQ[m,x] && PolyQ[Pp,x] && PolyQ[Qq,x] && NeQ[m,-1]",
        desc: "Derivative divides",
        refs: [],
        pattern: pp__ * qq_.pow(m_),
        with: [pp__, qq_, m_, x_],
        optional: [m_],
        x_free: [m_],
        when: {
            if freeq!(m_, x_)
                && poly_q(&pp__, x_)
                && poly_q(&qq_, x_)
                && neq!(m_, -1)
            {
                match (rubi_expon(&pp__, x_), rubi_expon(&qq_, x_)) {
                    (Some(p), Some(q)) => {
                        let p_coeff = rubi_coefficient(&pp__, x_, p);
                        let q_coeff = rubi_coefficient(&qq_, x_, q);
                        match (p_coeff, q_coeff) {
                            (Some(p_coeff), Some(q_coeff)) => {
                                let denominator_factor =
                                    (Atom::num(p) + &m_ * Atom::num(q) + 1).expand();
                                let expected = (&p_coeff
                                    * x_.pow(p - q)
                                    * (Atom::num(p - q + 1) * &qq_
                                        + (&m_ + 1) * x_ * rubi_d(&qq_, x_)))
                                .expand();
                                let scaled =
                                    (&denominator_factor * &q_coeff * &pp__).expand();
                                neq!(denominator_factor, 0) && eqq!(scaled, expected)
                            }
                            _ => false,
                        }
                    }
                    _ => false,
                }
            } else {
                false
            }
        },
        rhs: {
            let p = rubi_expon(&pp__, x_).rubi_rhs();
            let q = rubi_expon(&qq_, x_).rubi_rhs();
            let p_coeff = rubi_coefficient(&pp__, x_, p).rubi_rhs();
            let q_coeff = rubi_coefficient(&qq_, x_, q).rubi_rhs();
            let denominator_factor =
                (Atom::num(p) + &m_ * Atom::num(q) + 1).expand();
            p_coeff
                    * x_.pow(p - q + 1)
                    * qq_.pow(&m_ + 1)
                    / (denominator_factor * q_coeff)
        },
    ));
}

fn push_rules_rule_2022(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a1__, b1__, a2__, b2__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 2022,
        source: "Int[x_^m_.*(a1_+b1_.*x_^n_.)^p_*(a2_+b2_.*x_^n_.)^p_,x_Symbol] :=
          (a1+b1*x^n)^(p+1)*(a2+b2*x^n)^(p+1)/(2*b1*b2*n*(p+1)) /;
        FreeQ[{a1,b1,a2,b2,m,n,p},x] && EqQ[a2*b1+a1*b2,0] && EqQ[m-2*n+1,0] && NeQ[p,-1]",
        desc: "Derivative divides",
        refs: [],
        pattern: x_.pow(m_)
            * (a1__ + b1__ * x_.pow(n_)).pow(p_)
            * (a2__ + b2__ * x_.pow(n_)).pow(p_),
        with: [a1__, b1__, a2__, b2__, m_, n_, p_, x_],
        optional: [b1__, b2__, m_, n_],
        x_free: [a1__, b1__, a2__, b2__, m_, n_, p_],
        when: {
            freeq!([a1__, b1__, a2__, b2__, m_, n_, p_], x_)
                && eqq!(&a2__ * &b1__ + &a1__ * &b2__, Atom::num(0))
                && eqq!(&m_ - Atom::num(2) * &n_ + Atom::num(1), Atom::num(0))
                && neq!(p_, -Atom::num(1))
        },
        rhs: {
            let first = a1__ + &b1__ * x_.pow(&n_);
            let second = a2__ + &b2__ * x_.pow(&n_);
            let denominator = Atom::num(2) * b1__ * b2__ * n_ * (&p_ + 1);
            rubi_simp(&(first.pow(&p_ + 1) * second.pow(&p_ + 1) / denominator), x_)
        },
    ));
}

fn push_rules_rule_2023(rules: &mut Vec<RubiRule>) {
    rubi_symb!(m_, n_, pp__, qq_, rr_);
    rules.push(rubi_rule!(
        order: 2023,
        source: "Int[Pp_*Qq_^m_.*Rr_^n_.,x_Symbol] :=
          With[{p=Expon[Pp,x],q=Expon[Qq,x],r=Expon[Rr,x]},
          Coeff[Pp,x,p]*x^(p-q-r+1)*Qq^(m+1)*Rr^(n+1)/((p+m*q+n*r+1)*Coeff[Qq,x,q]*Coeff[Rr,x,r]) /;
         NeQ[p+m*q+n*r+1,0] &&
         EqQ[(p+m*q+n*r+1)*Coeff[Qq,x,q]*Coeff[Rr,x,r]*Pp,Coeff[Pp,x,p]*x^(p-q-r)*((p-q-r+1)*Qq*Rr+(m+1)*x*Rr*D[Qq,x]+(n+1)*x*Qq*D[Rr,x])]] /;
        FreeQ[{m,n},x] && PolyQ[Pp,x] && PolyQ[Qq,x] && PolyQ[Rr,x] && NeQ[m,-1] && NeQ[n,-1]",
        desc: "Derivative divides",
        refs: [],
        pattern: pp__ * qq_.pow(m_) * rr_.pow(n_),
        with: [pp__, qq_, rr_, m_, n_, x_],
        optional: [m_, n_],
        x_free: [m_, n_],
        when: {
            if freeq!([m_, n_], x_)
                && poly_q(&pp__, x_)
                && poly_q(&qq_, x_)
                && poly_q(&rr_, x_)
                && neq!(m_, -1)
                && neq!(n_, -1)
            {
                match (
                    rubi_expon(&pp__, x_),
                    rubi_expon(&qq_, x_),
                    rubi_expon(&rr_, x_),
                ) {
                    (Some(p), Some(q), Some(r)) => {
                        let p_coeff = rubi_coefficient(&pp__, x_, p);
                        let q_coeff = rubi_coefficient(&qq_, x_, q);
                        let r_coeff = rubi_coefficient(&rr_, x_, r);
                        match (p_coeff, q_coeff, r_coeff) {
                            (Some(p_coeff), Some(q_coeff), Some(r_coeff)) => {
                                let denominator_factor = (Atom::num(p)
                                    + &m_ * Atom::num(q)
                                    + &n_ * Atom::num(r)
                                    + 1)
                                .expand();
                                let expected = (&p_coeff
                                    * x_.pow(p - q - r)
                                    * (Atom::num(p - q - r + 1)
                                        * &qq_
                                        * &rr_
                                        + (&m_ + 1) * x_ * &rr_ * rubi_d(&qq_, x_)
                                        + (&n_ + 1) * x_ * &qq_ * rubi_d(&rr_, x_)))
                                .expand();
                                let scaled =
                                    (&denominator_factor * &q_coeff * &r_coeff * &pp__)
                                        .expand();
                                neq!(denominator_factor, 0) && eqq!(scaled, expected)
                            }
                            _ => false,
                        }
                    }
                    _ => false,
                }
            } else {
                false
            }
        },
        rhs: {
            let p = rubi_expon(&pp__, x_).rubi_rhs();
            let q = rubi_expon(&qq_, x_).rubi_rhs();
            let r = rubi_expon(&rr_, x_).rubi_rhs();
            let p_coeff = rubi_coefficient(&pp__, x_, p).rubi_rhs();
            let q_coeff = rubi_coefficient(&qq_, x_, q).rubi_rhs();
            let r_coeff = rubi_coefficient(&rr_, x_, r).rubi_rhs();
            let denominator_factor = (Atom::num(p)
                + &m_ * Atom::num(q)
                + &n_ * Atom::num(r)
                + 1)
            .expand();
            p_coeff
                    * x_.pow(p - q - r + 1)
                    * qq_.pow(&m_ + 1)
                    * rr_.pow(&n_ + 1)
                    / (denominator_factor * q_coeff * r_coeff)
        },
    ));
}

fn push_rules_rule_2024(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, n_, p_, qr__, pq_);
    rules.push(rubi_rule!(
        order: 2024,
        source: "Int[Qr_*(a_.+b_.*Pq_^n_.)^p_.,x_Symbol] :=
          With[{q=Expon[Pq,x],r=Expon[Qr,x]},
          Coeff[Qr,x,r]/(q*Coeff[Pq,x,q]) \\[Star] Subst[Int[(a+b*x^n)^p,x],x,Pq] /;
         EqQ[r,q-1] && EqQ[Coeff[Qr,x,r]*D[Pq,x],q*Coeff[Pq,x,q]*Qr]] /;
        FreeQ[{a,b,n,p},x] && PolyQ[Pq,x] && PolyQ[Qr,x]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern: qr__ * (a__ + b__ * pq_.pow(n_)).pow(p_),
        with: [qr__, a__, b__, pq_, n_, p_, x_],
        optional: [a__, b__, n_, p_],
        x_free: [a__, b__, n_, p_],
        derivative_pair: [(pq_, qr__)],
        when: {
            freeq!([a__, b__, n_, p_], x_)
                && rubi_polynomial_derivative_pair_q(&pq_, &qr__, x_)
        },
        rhs: {
            let q = rubi_expon(&pq_, x_).rubi_rhs();
            let r = rubi_expon(&qr__, x_).rubi_rhs();
            let q_coeff = rubi_coefficient(&pq_, x_, q).rubi_rhs();
            let r_coeff = rubi_coefficient(&qr__, x_, r).rubi_rhs();
            let multiplier = r_coeff / (Atom::num(q) * q_coeff);

            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = (a__ + b__ * sub_atom.pow(n_)).pow(p_);
            let primitive = rubi_rhs_int(&transformed_integrand, sub);
            let substituted = rubi_subst(&primitive, sub, pq_);
            rubi_star(multiplier, substituted)
        },
    ));
}

fn push_rules_rule_2025(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, n_, p_, n2_, qr__, pq_);
    rules.push(rubi_rule!(
        order: 2025,
        source: "Int[Qr_*(a_.+b_.*Pq_^n_.+c_.*Pq_^n2_.)^p_.,x_Symbol] :=
          Module[{q=Expon[Pq,x],r=Expon[Qr,x]},
          Coeff[Qr,x,r]/(q*Coeff[Pq,x,q]) \\[Star] Subst[Int[(a+b*x^n+c*x^(2*n))^p,x],x,Pq] /;
         EqQ[r,q-1] && EqQ[Coeff[Qr,x,r]*D[Pq,x],q*Coeff[Pq,x,q]*Qr]] /;
        FreeQ[{a,b,c,n,p},x] && EqQ[n2,2*n] && PolyQ[Pq,x] && PolyQ[Qr,x]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern: qr__ * (a__ + b__ * pq_.pow(n_) + c__ * pq_.pow(n2_)).pow(p_),
        with: [qr__, a__, b__, c__, pq_, n_, n2_, p_, x_],
        optional: [a__, b__, c__, n_, n2_, p_],
        x_free: [a__, b__, c__, n_, n2_, p_],
        derivative_pair: [(pq_, qr__)],
        when: {
            freeq!([a__, b__, c__, n_, p_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && rubi_polynomial_derivative_pair_q(&pq_, &qr__, x_)
        },
        rhs: {
            let q = rubi_expon(&pq_, x_).rubi_rhs();
            let r = rubi_expon(&qr__, x_).rubi_rhs();
            let q_coeff = rubi_coefficient(&pq_, x_, q).rubi_rhs();
            let r_coeff = rubi_coefficient(&qr__, x_, r).rubi_rhs();
            let multiplier = r_coeff / (Atom::num(q) * q_coeff);

            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand =
                (a__ + b__ * sub_atom.pow(&n_) + c__ * sub_atom.pow(Atom::num(2) * n_))
                    .pow(p_);
            let primitive = rubi_rhs_int(&transformed_integrand, sub);
            let substituted = rubi_subst(&primitive, sub, pq_);
            rubi_star(multiplier, substituted)
        },
    ));
}

fn push_rules_rule_2098(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_a__,
        capital_b__,
        a__,
        b__,
        c__,
        d__,
        x_,
        e__,
        f__,
        g__,
        h__
    );
    rules.push(rubi_rule!(
                order: 2098,
                source: "Int[Sqrt[a_.+b_.*x_]*(A_.+B_.*x_)/(Sqrt[c_.+d_.*x_]*Sqrt[e_.+f_.*x_]*Sqrt[g_.+h_.*x_]),x_Symbol] :=
                  b*B*Sqrt[c+d*x]*Sqrt[e+f*x]*Sqrt[g+h*x]/(d*f*h*Sqrt[a+b*x]) -
                  B*(b*g-a*h)/(2*f*h) \\[Star] Int[Sqrt[e+f*x]/(Sqrt[a+b*x]*Sqrt[c+d*x]*Sqrt[g+h*x]),x] +
                  B*(b*e-a*f)*(b*g-a*h)/(2*d*f*h) \\[Star] Int[Sqrt[c+d*x]/((a+b*x)^(3/2)*Sqrt[e+f*x]*Sqrt[g+h*x]),x] /;
                FreeQ[{a,b,c,d,e,f,g,h,A,B},x] && EqQ[2*A*d*f-B*(d*e+c*f),0]",
                desc: "Decompose the integrand into a sum of simpler integrals.",
                refs: [],
                pattern:  rubi_shared_pattern_3(symbols),
                with: [capital_a__, capital_b__, a__, b__, c__, d__, e__, f__, g__, h__, x_],
                optional: [capital_a__, capital_b__, a__, b__, c__, d__, e__, f__, g__, h__],
                x_free: [capital_a__, capital_b__, a__, b__, c__, d__, e__, f__, g__, h__],
                when: {
                    freeq!([a__, b__, c__, d__, e__, f__, g__, h__, capital_a__, capital_b__], x_)
                        && eqq!(
                            Atom::num(2) * &capital_a__ * &d__ * &f__
                                - &capital_b__ * (&d__ * &e__ + &c__ * &f__),
                            Atom::num(0)
                        )
                },
                rhs: {
                    let first = &a__ + &b__ * x_;
                    let second = &c__ + &d__ * x_;
                    let third = &e__ + &f__ * x_;
                    let fourth = &g__ + &h__ * x_;
                    let direct = &b__
                        * &capital_b__
                        * second.sqrt()
                        * third.sqrt()
                        * fourth.sqrt()
                        / (&d__ * &f__ * &h__ * first.sqrt());
                    let first_coefficient =
                        -&capital_b__ * (&b__ * &g__ - &a__ * &h__) / (Atom::num(2) * &f__ * &h__);
                    let first_integrand =
                        third.sqrt() / (first.sqrt() * second.sqrt() * fourth.sqrt());
                    let second_coefficient = &capital_b__
                        * (&b__ * &e__ - &a__ * &f__)
                        * (&b__ * &g__ - &a__ * &h__)
                        / (Atom::num(2) * &d__ * &f__ * &h__);
                    let second_integrand = second.sqrt()
                        / (first.pow(half_integer_atom(3)) * third.sqrt() * fourth.sqrt());

                    rubi_simp(&(direct), x_)
                            + rubi_star(first_coefficient, rubi_rhs_int(&first_integrand, x_))
                            + rubi_star(second_coefficient, rubi_rhs_int(&second_integrand, x_))
                },
            ));
}

fn push_rules_rule_2099(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_a__,
        capital_b__,
        a__,
        b__,
        c__,
        d__,
        x_,
        e__,
        f__,
        g__,
        h__
    );
    rules.push(rubi_rule!(
                order: 2099,
                source: "Int[Sqrt[a_.+b_.*x_]*(A_.+B_.*x_)/(Sqrt[c_.+d_.*x_]*Sqrt[e_.+f_.*x_]*Sqrt[g_.+h_.*x_]),x_Symbol] :=
                  B*Sqrt[a+b*x]*Sqrt[e+f*x]*Sqrt[g+h*x]/(f*h*Sqrt[c+d*x]) +
                  B*(d*e-c*f)*(d*g-c*h)/(2*d*f*h) \\[Star] Int[Sqrt[a+b*x]/((c+d*x)^(3/2)*Sqrt[e+f*x]*Sqrt[g+h*x]),x] -
                  B*(b*e-a*f)*(b*g-a*h)/(2*b*f*h) \\[Star] Int[1/(Sqrt[a+b*x]*Sqrt[c+d*x]*Sqrt[e+f*x]*Sqrt[g+h*x]),x] +
                  (2*A*b*d*f*h+B*(a*d*f*h-b*(d*f*g+d*e*h+c*f*h)))/(2*b*d*f*h) \\[Star] Int[Sqrt[a+b*x]/(Sqrt[c+d*x]*Sqrt[e+f*x]*Sqrt[g+h*x]),x] /;
                FreeQ[{a,b,c,d,e,f,g,h,A,B},x] && NeQ[2*A*d*f-B*(d*e+c*f),0]",
                desc: "Decompose the integrand into a sum of simpler integrals.",
                refs: [],
                pattern:  rubi_shared_pattern_3(symbols),
                with: [capital_a__, capital_b__, a__, b__, c__, d__, e__, f__, g__, h__, x_],
                optional: [capital_a__, capital_b__, a__, b__, c__, d__, e__, f__, g__, h__],
                x_free: [capital_a__, capital_b__, a__, b__, c__, d__, e__, f__, g__, h__],
                when: {
                    freeq!([a__, b__, c__, d__, e__, f__, g__, h__, capital_a__, capital_b__], x_)
                        && neq!(
                            Atom::num(2) * &capital_a__ * &d__ * &f__
                                - &capital_b__ * (&d__ * &e__ + &c__ * &f__),
                            Atom::num(0)
                        )
                },
                rhs: {
                    let first = &a__ + &b__ * x_;
                    let second = &c__ + &d__ * x_;
                    let third = &e__ + &f__ * x_;
                    let fourth = &g__ + &h__ * x_;
                    let direct = &capital_b__
                        * first.sqrt()
                        * third.sqrt()
                        * fourth.sqrt()
                        / (&f__ * &h__ * second.sqrt());
                    let first_coefficient = &capital_b__
                        * (&d__ * &e__ - &c__ * &f__)
                        * (&d__ * &g__ - &c__ * &h__)
                        / (Atom::num(2) * &d__ * &f__ * &h__);
                    let first_integrand = first.sqrt()
                        / (second.pow(half_integer_atom(3)) * third.sqrt() * fourth.sqrt());
                    let second_coefficient = -&capital_b__
                        * (&b__ * &e__ - &a__ * &f__)
                        * (&b__ * &g__ - &a__ * &h__)
                        / (Atom::num(2) * &b__ * &f__ * &h__);
                    let second_integrand = Atom::num(1)
                        / (first.sqrt() * second.sqrt() * third.sqrt() * fourth.sqrt());
                    let third_coefficient = (Atom::num(2)
                        * &capital_a__
                        * &b__
                        * &d__
                        * &f__
                        * &h__
                        + &capital_b__
                            * (&a__ * &d__ * &f__ * &h__
                                - &b__ * (&d__ * &f__ * &g__ + &d__ * &e__ * &h__ + &c__ * &f__ * &h__)))
                        / (Atom::num(2) * &b__ * &d__ * &f__ * &h__);
                    let third_integrand =
                        first.sqrt() / (second.sqrt() * third.sqrt() * fourth.sqrt());

                    rubi_simp(&(direct), x_)
                            + rubi_star(first_coefficient, rubi_rhs_int(&first_integrand, x_))
                            + rubi_star(second_coefficient, rubi_rhs_int(&second_integrand, x_))
                            + rubi_star(third_coefficient, rubi_rhs_int(&third_integrand, x_))
                },
            ));
}

fn push_rules_rule_2100(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_a__,
        capital_b__,
        a__,
        b__,
        c__,
        d__,
        m_,
        x_,
        e__,
        f__,
        g__,
        h__
    );
    rules.push(rubi_rule!(
                order: 2100,
                source: "Int[(a_.+b_.*x_)^m_*(A_.+B_.*x_)/(Sqrt[c_.+d_.*x_]*Sqrt[e_.+f_.*x_]*Sqrt[g_.+h_.*x_]),x_Symbol] :=
                  2*b*B*(a+b*x)^(m-1)*Sqrt[c+d*x]*Sqrt[e+f*x]*Sqrt[g+h*x]/(d*f*h*(2*m+1)) +
                  1/(d*f*h*(2*m+1)) \\[Star]
                    Int[(a+b*x)^(m-2)/(Sqrt[c+d*x]*Sqrt[e+f*x]*Sqrt[g+h*x])*
                      Simp[-b*B*(a*(d*e*g+c*f*g+c*e*h)+2*b*c*e*g*(m-1))+a^2*A*d*f*h*(2*m+1)+
                        (2*a*A*b*d*f*h*(2*m+1)-B*(2*a*b*(d*f*g+d*e*h+c*f*h)+b^2*(d*e*g+c*f*g+c*e*h)*(2*m-1)-
                        a^2*d*f*h*(2*m+1)))*x+b*(A*b*d*f*h*(2*m+1)-B*(2*b*(d*f*g+d*e*h+c*f*h)*m-a*d*f*h*(4*m-1)))*x^2,x],x] /;
                FreeQ[{a,b,c,d,e,f,g,h,A,B},x] && IntegerQ[2*m] && GtQ[m,1]",
                desc: "Simplify the integrand and continue with the simpler form.",
                refs: [],
                pattern:  rubi_shared_pattern_0(symbols),
                with: [capital_a__, capital_b__, a__, b__, c__, d__, e__, f__, g__, h__, m_, x_],
                optional: [capital_a__, capital_b__, a__, b__, c__, d__, e__, f__, g__, h__],
                x_free: [capital_a__, capital_b__, a__, b__, c__, d__, e__, f__, g__, h__],
                when: {
                    freeq!([a__, b__, c__, d__, e__, f__, g__, h__, capital_a__, capital_b__], x_)
                        && integerq!(Atom::num(2) * &m_)
                        && gtq!(m_, 1)
                },
                rhs: {
                    let first = &a__ + &b__ * x_;
                    let second = &c__ + &d__ * x_;
                    let third = &e__ + &f__ * x_;
                    let fourth = &g__ + &h__ * x_;
                    let two_m_1 = Atom::num(2) * &m_ + 1;
                    let s1 = &d__ * &e__ * &g__ + &c__ * &f__ * &g__ + &c__ * &e__ * &h__;
                    let s2 = &d__ * &f__ * &g__ + &d__ * &e__ * &h__ + &c__ * &f__ * &h__;
                    let denominator = &d__ * &f__ * &h__ * &two_m_1;
                    let direct = Atom::num(2)
                        * &b__
                        * &capital_b__
                        * first.pow(&m_ - 1)
                        * second.sqrt()
                        * third.sqrt()
                        * fourth.sqrt()
                        / &denominator;
                    let payload = simp!(
                        -&b__
                            * &capital_b__
                            * (&a__ * &s1
                                + Atom::num(2) * &b__ * &c__ * &e__ * &g__ * (&m_ - 1))
                            + a__.pow(2)
                                * &capital_a__
                                * &d__
                                * &f__
                                * &h__
                                * &two_m_1
                            + (Atom::num(2)
                                * &a__
                                * &capital_a__
                                * &b__
                                * &d__
                                * &f__
                                * &h__
                                * &two_m_1
                                - &capital_b__
                                    * (Atom::num(2) * &a__ * &b__ * &s2
                                        + b__.pow(2) * &s1 * (Atom::num(2) * &m_ - 1)
                                        - a__.pow(2) * &d__ * &f__ * &h__ * &two_m_1))
                                * x_
                            + &b__
                                * (&capital_a__ * &b__ * &d__ * &f__ * &h__ * &two_m_1
                                    - &capital_b__
                                        * (Atom::num(2) * &b__ * &s2 * &m_
                                            - &a__ * &d__ * &f__ * &h__ * (Atom::num(4) * &m_ - 1)))
                                * x_.pow(2),
                        x_
                    );
                    let recursive_integrand = first.pow(&m_ - 2) * payload
                        / (second.sqrt() * third.sqrt() * fourth.sqrt());
                    let recursive = rubi_rhs_int(&recursive_integrand, x_);
                    rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / denominator, recursive)
                },
            ));
}

fn push_rules_rule_2101(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        capital_a__,
        capital_b__,
        a__,
        b__,
        c__,
        d__,
        x_,
        e__,
        f__,
        g__,
        h__
    );
    rules.push(rubi_rule!(
        order: 2101,
        source: "Int[(A_.+B_.*x_)/(Sqrt[a_.+b_.*x_]*Sqrt[c_.+d_.*x_]*Sqrt[e_.+f_.*x_]*Sqrt[g_.+h_.*x_]),x_Symbol] :=
          (A*b-a*B)/b \\[Star] Int[1/(Sqrt[a+b*x]*Sqrt[c+d*x]*Sqrt[e+f*x]*Sqrt[g+h*x]),x] +
          B/b \\[Star] Int[Sqrt[a+b*x]/(Sqrt[c+d*x]*Sqrt[e+f*x]*Sqrt[g+h*x]),x] /;
        FreeQ[{a,b,c,d,e,f,g,h,A,B},x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (capital_a__ + capital_b__ * x_)
            / ((a__ + b__ * x_).sqrt()
                * (c__ + d__ * x_).sqrt()
                * (e__ + f__ * x_).sqrt()
                * (g__ + h__ * x_).sqrt()),
        with: [capital_a__, capital_b__, a__, b__, c__, d__, e__, f__, g__, h__, x_],
        optional: [capital_a__, capital_b__, a__, b__, c__, d__, e__, f__, g__, h__],
        x_free: [capital_a__, capital_b__, a__, b__, c__, d__, e__, f__, g__, h__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__, capital_a__, capital_b__], x_)
        },
        rhs: {
            let first = &a__ + &b__ * x_;
            let second = &c__ + &d__ * x_;
            let third = &e__ + &f__ * x_;
            let fourth = &g__ + &h__ * x_;
            let first_coefficient = (&capital_a__ * &b__ - &a__ * &capital_b__) / &b__;
            let second_coefficient = capital_b__ / &b__;
            let first_integrand =
                Atom::num(1) / (first.sqrt() * second.sqrt() * third.sqrt() * fourth.sqrt());
            let second_integrand =
                first.sqrt() / (second.sqrt() * third.sqrt() * fourth.sqrt());

            rubi_star(first_coefficient, rubi_rhs_int(&first_integrand, x_))
                    + rubi_star(second_coefficient, rubi_rhs_int(&second_integrand, x_))
        },
    ));
}

fn push_rules_rule_2102(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_a__,
        capital_b__,
        a__,
        b__,
        c__,
        d__,
        m_,
        x_,
        e__,
        f__,
        g__,
        h__
    );
    rules.push(rubi_rule!(
        order: 2102,
        source: "Int[(a_.+b_.*x_)^m_*(A_.+B_.*x_)/(Sqrt[c_.+d_.*x_]*Sqrt[e_.+f_.*x_]*Sqrt[g_.+h_.*x_]),x_Symbol] :=
          (A*b^2-a*b*B)*(a+b*x)^(m+1)*Sqrt[c+d*x]*Sqrt[e+f*x]*Sqrt[g+h*x]/((m+1)*(b*c-a*d)*(b*e-a*f)*(b*g-a*h)) -
          1/(2*(m+1)*(b*c-a*d)*(b*e-a*f)*(b*g-a*h)) \\[Star] Int[((a+b*x)^(m+1)/(Sqrt[c+d*x]*Sqrt[e+f*x]*Sqrt[g+h*x]))*
            Simp[A*(2*a^2*d*f*h*(m+1)-2*a*b*(m+1)*(d*f*g+d*e*h+c*f*h)+b^2*(2*m+3)*(d*e*g+c*f*g+c*e*h)) -
              b*B*(a*(d*e*g+c*f*g+c*e*h)+2*b*c*e*g*(m+1)) -
              2*((A*b-a*B)*(a*d*f*h*(m+1)-b*(m+2)*(d*f*g+d*e*h+c*f*h)))*x +
              d*f*h*(2*m+5)*(A*b^2-a*b*B)*x^2,x],x] /;
        FreeQ[{a,b,c,d,e,f,g,h,A,B},x] && IntegerQ[2*m] && LtQ[m,-1]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [capital_a__, capital_b__, a__, b__, c__, d__, e__, f__, g__, h__, m_, x_],
        optional: [capital_a__, capital_b__, a__, b__, c__, d__, e__, f__, g__, h__],
        x_free: [capital_a__, capital_b__, a__, b__, c__, d__, e__, f__, g__, h__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__, capital_a__, capital_b__], x_)
                && integerq!(Atom::num(2) * &m_)
                && ltq!(m_, -1)
        },
        rhs: {
            let first = &a__ + &b__ * x_;
            let second = &c__ + &d__ * x_;
            let third = &e__ + &f__ * x_;
            let fourth = &g__ + &h__ * x_;
            let m1 = (&m_ + 1).expand();
            let m2 = (&m_ + 2).expand();
            let two_m_3 = Atom::num(2) * &m_ + 3;
            let two_m_5 = Atom::num(2) * &m_ + 5;
            let bc_ad = (&b__ * &c__ - &a__ * &d__).expand();
            let be_af = (&b__ * &e__ - &a__ * &f__).expand();
            let bg_ah = (&b__ * &g__ - &a__ * &h__).expand();
            let leading = (&capital_a__ * b__.pow(2) - &a__ * &b__ * &capital_b__).expand();
            let denominator = (&m1 * &bc_ad * &be_af * &bg_ah).expand();
            let direct =
                &leading * first.pow(&m1) * second.sqrt() * third.sqrt() * fourth.sqrt()
                    / &denominator;
            let quadratic = simp!(
                &capital_a__
                    * (Atom::num(2) * a__.pow(2) * &d__ * &f__ * &h__ * &m1
                        - Atom::num(2)
                            * &a__
                            * &b__
                            * &m1
                            * (&d__ * &f__ * &g__ + &d__ * &e__ * &h__ + &c__ * &f__ * &h__)
                        + b__.pow(2)
                            * &two_m_3
                            * (&d__ * &e__ * &g__ + &c__ * &f__ * &g__ + &c__ * &e__ * &h__))
                    - &b__
                        * &capital_b__
                        * (&a__ * (&d__ * &e__ * &g__ + &c__ * &f__ * &g__ + &c__ * &e__ * &h__)
                            + Atom::num(2) * &b__ * &c__ * &e__ * &g__ * &m1)
                    - Atom::num(2)
                        * (&capital_a__ * &b__ - &a__ * &capital_b__)
                        * (&a__ * &d__ * &f__ * &h__ * &m1
                            - &b__
                                * &m2
                                * (&d__ * &f__ * &g__ + &d__ * &e__ * &h__ + &c__ * &f__ * &h__))
                        * x_
                    + &d__ * &f__ * &h__ * &two_m_5 * &leading * x_.pow(2),
                x_
            );
            let radical_product = second.sqrt() * third.sqrt() * fourth.sqrt();
            let recursive_integrand = first.pow(&m1) * &quadratic / radical_product;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) - rubi_star(Atom::num(1) / (Atom::num(2) * denominator), recursive)
        },
    ));
}

fn push_rules_rule_2103(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_a__,
        capital_b__,
        capital_c__,
        a__,
        b__,
        c__,
        d__,
        m_,
        x_,
        e__,
        f__,
        g__,
        h__
    );
    rules.push(rubi_rule!(
        order: 2103,
        source: "Int[(a_.+b_.*x_)^m_.*(A_.+B_.*x_+C_.*x_^2)/(Sqrt[c_.+d_.*x_]*Sqrt[e_.+f_.*x_]*Sqrt[g_.+h_.*x_]),x_Symbol] :=
          2*C*(a+b*x)^m*Sqrt[c+d*x]*Sqrt[e+f*x]*Sqrt[g+h*x]/(d*f*h*(2*m+3)) +
          1/(d*f*h*(2*m+3)) \\[Star] Int[((a+b*x)^(m-1)/(Sqrt[c+d*x]*Sqrt[e+f*x]*Sqrt[g+h*x]))*
            Simp[a*A*d*f*h*(2*m+3)-C*(a*(d*e*g+c*f*g+c*e*h)+2*b*c*e*g*m) +
              ((A*b+a*B)*d*f*h*(2*m+3)-C*(2*a*(d*f*g+d*e*h+c*f*h)+b*(2*m+1)*(d*e*g+c*f*g+c*e*h)))*x +
              (b*B*d*f*h*(2*m+3)+2*C*(a*d*f*h*m-b*(m+1)*(d*f*g+d*e*h+c*f*h)))*x^2,x],x] /;
        FreeQ[{a,b,c,d,e,f,g,h,A,B,C},x] && IntegerQ[2*m] && GtQ[m,0]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [capital_a__, capital_b__, capital_c__, a__, b__, c__, d__, e__, f__, g__, h__, m_, x_],
        optional: [capital_a__, capital_b__, capital_c__, a__, b__, c__, d__, e__, f__, g__, h__, m_],
        x_free: [capital_a__, capital_b__, capital_c__, a__, b__, c__, d__, e__, f__, g__, h__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__, capital_a__, capital_b__, capital_c__], x_)
                && integerq!(Atom::num(2) * &m_)
                && gtq!(m_, 0)
        },
        rhs: {
            let first = &a__ + &b__ * x_;
            let second = &c__ + &d__ * x_;
            let third = &e__ + &f__ * x_;
            let fourth = &g__ + &h__ * x_;
            let two_m_3 = Atom::num(2) * &m_ + 3;
            let two_m_1 = Atom::num(2) * &m_ + 1;
            let m1 = (&m_ + 1).expand();
            let denominator = (&d__ * &f__ * &h__ * &two_m_3).expand();
            let radical_product = second.sqrt() * third.sqrt() * fourth.sqrt();
            let direct = Atom::num(2)
                * &capital_c__
                * first.pow(&m_)
                * &radical_product
                / &denominator;
            let quadratic = simp!(
                &a__ * &capital_a__ * &d__ * &f__ * &h__ * &two_m_3
                    - &capital_c__
                        * (&a__ * (&d__ * &e__ * &g__ + &c__ * &f__ * &g__ + &c__ * &e__ * &h__)
                            + Atom::num(2) * &b__ * &c__ * &e__ * &g__ * &m_)
                    + ((&capital_a__ * &b__ + &a__ * &capital_b__) * &d__ * &f__ * &h__ * &two_m_3
                        - &capital_c__
                            * (Atom::num(2)
                                * &a__
                                * (&d__ * &f__ * &g__ + &d__ * &e__ * &h__ + &c__ * &f__ * &h__)
                                + &b__
                                    * &two_m_1
                                    * (&d__ * &e__ * &g__ + &c__ * &f__ * &g__ + &c__ * &e__ * &h__)))
                        * x_
                    + (&b__ * &capital_b__ * &d__ * &f__ * &h__ * &two_m_3
                        + Atom::num(2)
                            * &capital_c__
                            * (&a__ * &d__ * &f__ * &h__ * &m_
                                - &b__
                                    * &m1
                                    * (&d__ * &f__ * &g__ + &d__ * &e__ * &h__ + &c__ * &f__ * &h__)))
                        * x_.pow(2),
                x_
            );
            let recursive_integrand = first.pow((&m_ - 1).expand()) * &quadratic / radical_product;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_2104(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_a__,
        capital_c__,
        a__,
        b__,
        c__,
        d__,
        m_,
        x_,
        e__,
        f__,
        g__,
        h__
    );
    rules.push(rubi_rule!(
        order: 2104,
        source: "Int[(a_.+b_.*x_)^m_.*(A_.+C_.*x_^2)/(Sqrt[c_.+d_.*x_]*Sqrt[e_.+f_.*x_]*Sqrt[g_.+h_.*x_]),x_Symbol] :=
          2*C*(a+b*x)^m*Sqrt[c+d*x]*Sqrt[e+f*x]*Sqrt[g+h*x]/(d*f*h*(2*m+3)) +
          1/(d*f*h*(2*m+3)) \\[Star] Int[((a+b*x)^(m-1)/(Sqrt[c+d*x]*Sqrt[e+f*x]*Sqrt[g+h*x]))*
            Simp[a*A*d*f*h*(2*m+3)-C*(a*(d*e*g+c*f*g+c*e*h)+2*b*c*e*g*m) +
              (A*b*d*f*h*(2*m+3)-C*(2*a*(d*f*g+d*e*h+c*f*h)+b*(2*m+1)*(d*e*g+c*f*g+c*e*h)))*x +
              2*C*(a*d*f*h*m-b*(m+1)*(d*f*g+d*e*h+c*f*h))*x^2,x],x] /;
        FreeQ[{a,b,c,d,e,f,g,h,A,C},x] && IntegerQ[2*m] && GtQ[m,0]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [capital_a__, capital_c__, a__, b__, c__, d__, e__, f__, g__, h__, m_, x_],
        optional: [capital_a__, capital_c__, a__, b__, c__, d__, e__, f__, g__, h__, m_],
        x_free: [capital_a__, capital_c__, a__, b__, c__, d__, e__, f__, g__, h__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__, capital_a__, capital_c__], x_)
                && integerq!(Atom::num(2) * &m_)
                && gtq!(m_, 0)
        },
        rhs: {
            let first = &a__ + &b__ * x_;
            let second = &c__ + &d__ * x_;
            let third = &e__ + &f__ * x_;
            let fourth = &g__ + &h__ * x_;
            let two_m_3 = Atom::num(2) * &m_ + 3;
            let two_m_1 = Atom::num(2) * &m_ + 1;
            let m1 = (&m_ + 1).expand();
            let denominator = (&d__ * &f__ * &h__ * &two_m_3).expand();
            let radical_product = second.sqrt() * third.sqrt() * fourth.sqrt();
            let direct = Atom::num(2)
                * &capital_c__
                * first.pow(&m_)
                * &radical_product
                / &denominator;
            let quadratic = simp!(
                &a__ * &capital_a__ * &d__ * &f__ * &h__ * &two_m_3
                    - &capital_c__
                        * (&a__ * (&d__ * &e__ * &g__ + &c__ * &f__ * &g__ + &c__ * &e__ * &h__)
                            + Atom::num(2) * &b__ * &c__ * &e__ * &g__ * &m_)
                    + (&capital_a__ * &b__ * &d__ * &f__ * &h__ * &two_m_3
                        - &capital_c__
                            * (Atom::num(2)
                                * &a__
                                * (&d__ * &f__ * &g__ + &d__ * &e__ * &h__ + &c__ * &f__ * &h__)
                                + &b__
                                    * &two_m_1
                                    * (&d__ * &e__ * &g__ + &c__ * &f__ * &g__ + &c__ * &e__ * &h__)))
                        * x_
                    + Atom::num(2)
                        * &capital_c__
                        * (&a__ * &d__ * &f__ * &h__ * &m_
                            - &b__ * &m1 * (&d__ * &f__ * &g__ + &d__ * &e__ * &h__ + &c__ * &f__ * &h__))
                        * x_.pow(2),
                x_
            );
            let recursive_integrand = first.pow((&m_ - 1).expand()) * &quadratic / radical_product;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_2105(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        capital_a__,
        capital_b__,
        capital_c__,
        a__,
        b__,
        c__,
        d__,
        x_,
        e__,
        f__,
        g__,
        h__
    );
    rules.push(rubi_rule!(
        order: 2105,
        source: "Int[(A_.+B_.*x_+C_.*x_^2)/(Sqrt[a_.+b_.*x_]*Sqrt[c_.+d_.*x_]*Sqrt[e_.+f_.*x_]*Sqrt[g_.+h_.*x_]),x_Symbol] :=
          C*Sqrt[a+b*x]*Sqrt[e+f*x]*Sqrt[g+h*x]/(b*f*h*Sqrt[c+d*x]) +
          C*(d*e-c*f)*(d*g-c*h)/(2*b*d*f*h) \\[Star] Int[Sqrt[a+b*x]/((c+d*x)^(3/2)*Sqrt[e+f*x]*Sqrt[g+h*x]),x] +
          1/(2*b*d*f*h) \\[Star] Int[1/(Sqrt[a+b*x]*Sqrt[c+d*x]*Sqrt[e+f*x]*Sqrt[g+h*x])*
            Simp[2*A*b*d*f*h-C*(b*d*e*g+a*c*f*h)+(2*b*B*d*f*h-C*(a*d*f*h+b*(d*f*g+d*e*h+c*f*h)))*x,x],x] /;
        FreeQ[{a,b,c,d,e,f,g,h,A,B,C},x]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern: (capital_a__ + capital_b__ * x_ + capital_c__ * x_.pow(2))
            / ((a__ + b__ * x_).sqrt()
                * (c__ + d__ * x_).sqrt()
                * (e__ + f__ * x_).sqrt()
                * (g__ + h__ * x_).sqrt()),
        with: [capital_a__, capital_b__, capital_c__, a__, b__, c__, d__, e__, f__, g__, h__, x_],
        optional: [capital_a__, capital_b__, capital_c__, a__, b__, c__, d__, e__, f__, g__, h__],
        x_free: [capital_a__, capital_b__, capital_c__, a__, b__, c__, d__, e__, f__, g__, h__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__, capital_a__, capital_b__, capital_c__], x_)
        },
        rhs: {
            let first = &a__ + &b__ * x_;
            let second = &c__ + &d__ * x_;
            let third = &e__ + &f__ * x_;
            let fourth = &g__ + &h__ * x_;
            let denominator = (&b__ * &d__ * &f__ * &h__).expand();
            let direct = &capital_c__ * first.sqrt() * third.sqrt() * fourth.sqrt()
                / (&b__ * &f__ * &h__ * second.sqrt());
            let second_coefficient = (&capital_c__
                * (&d__ * &e__ - &c__ * &f__)
                * (&d__ * &g__ - &c__ * &h__)
                / (Atom::num(2) * &denominator))
                .expand();
            let second_integrand = first.sqrt()
                / (second.pow(Atom::num(3) / Atom::num(2)) * third.sqrt() * fourth.sqrt());
            let constant_payload = Atom::num(2) * &capital_a__ * &b__ * &d__ * &f__ * &h__
                - &capital_c__ * (&b__ * &d__ * &e__ * &g__ + &a__ * &c__ * &f__ * &h__);
            let linear_payload = Atom::num(2) * &b__ * &capital_b__ * &d__ * &f__ * &h__
                - &capital_c__
                    * (&a__ * &d__ * &f__ * &h__
                        + &b__
                            * (&d__ * &f__ * &g__ + &d__ * &e__ * &h__ + &c__ * &f__ * &h__));
            let payload = simp!(&constant_payload + &linear_payload * x_, x_);
            let third_integrand =
                &payload / (first.sqrt() * second.sqrt() * third.sqrt() * fourth.sqrt());
            let third_recursive = rubi_rhs_int(&third_integrand, x_);

            rubi_simp(&(direct), x_)
                    + rubi_star(second_coefficient, rubi_rhs_int(&second_integrand, x_))
                    + rubi_star(Atom::num(1) / (Atom::num(2) * denominator), third_recursive)
        },
    ));
}

fn push_rules_rule_2106(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        capital_a__,
        capital_c__,
        a__,
        b__,
        c__,
        d__,
        x_,
        e__,
        f__,
        g__,
        h__
    );
    rules.push(rubi_rule!(
        order: 2106,
        source: "Int[(A_.+C_.*x_^2)/(Sqrt[a_.+b_.*x_]*Sqrt[c_.+d_.*x_]*Sqrt[e_.+f_.*x_]*Sqrt[g_.+h_.*x_]),x_Symbol] :=
          C*Sqrt[a+b*x]*Sqrt[e+f*x]*Sqrt[g+h*x]/(b*f*h*Sqrt[c+d*x]) +
          C*(d*e-c*f)*(d*g-c*h)/(2*b*d*f*h) \\[Star] Int[Sqrt[a+b*x]/((c+d*x)^(3/2)*Sqrt[e+f*x]*Sqrt[g+h*x]),x] +
          1/(2*b*d*f*h) \\[Star] Int[1/(Sqrt[a+b*x]*Sqrt[c+d*x]*Sqrt[e+f*x]*Sqrt[g+h*x])*
            Simp[2*A*b*d*f*h-C*(b*d*e*g+a*c*f*h)-C*(a*d*f*h+b*(d*f*g+d*e*h+c*f*h))*x,x],x] /;
        FreeQ[{a,b,c,d,e,f,g,h,A,C},x]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern: (capital_a__ + capital_c__ * x_.pow(2))
            / ((a__ + b__ * x_).sqrt()
                * (c__ + d__ * x_).sqrt()
                * (e__ + f__ * x_).sqrt()
                * (g__ + h__ * x_).sqrt()),
        with: [capital_a__, capital_c__, a__, b__, c__, d__, e__, f__, g__, h__, x_],
        optional: [capital_a__, capital_c__, a__, b__, c__, d__, e__, f__, g__, h__],
        x_free: [capital_a__, capital_c__, a__, b__, c__, d__, e__, f__, g__, h__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__, capital_a__, capital_c__], x_)
        },
        rhs: {
            let first = &a__ + &b__ * x_;
            let second = &c__ + &d__ * x_;
            let third = &e__ + &f__ * x_;
            let fourth = &g__ + &h__ * x_;
            let denominator = (&b__ * &d__ * &f__ * &h__).expand();
            let direct = &capital_c__ * first.sqrt() * third.sqrt() * fourth.sqrt()
                / (&b__ * &f__ * &h__ * second.sqrt());
            let second_coefficient = (&capital_c__
                * (&d__ * &e__ - &c__ * &f__)
                * (&d__ * &g__ - &c__ * &h__)
                / (Atom::num(2) * &denominator))
                .expand();
            let second_integrand = first.sqrt()
                / (second.pow(Atom::num(3) / Atom::num(2)) * third.sqrt() * fourth.sqrt());
            let constant_payload = (Atom::num(2) * &capital_a__ * &b__ * &d__ * &f__ * &h__
                - &capital_c__ * (&b__ * &d__ * &e__ * &g__ + &a__ * &c__ * &f__ * &h__))
                .expand();
            let linear_payload = (-&capital_c__
                * (&a__ * &d__ * &f__ * &h__
                    + &b__ * (&d__ * &f__ * &g__ + &d__ * &e__ * &h__ + &c__ * &f__ * &h__)))
                .expand();
            let payload = simp!(&constant_payload + &linear_payload * x_, x_);
            let third_integrand =
                &payload / (first.sqrt() * second.sqrt() * third.sqrt() * fourth.sqrt());
            let third_recursive = rubi_rhs_int(&third_integrand, x_);

            rubi_simp(&(direct), x_)
                    + rubi_star(second_coefficient, rubi_rhs_int(&second_integrand, x_))
                    + rubi_star(Atom::num(1) / (Atom::num(2) * denominator), third_recursive)
        },
    ));
}

fn push_rules_rule_2107(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_a__,
        capital_b__,
        capital_c__,
        a__,
        b__,
        c__,
        d__,
        m_,
        x_,
        e__,
        f__,
        g__,
        h__
    );
    rules.push(rubi_rule!(
        order: 2107,
        source: "Int[(a_.+b_.*x_)^m_*(A_.+B_.*x_+C_.*x_^2)/(Sqrt[c_.+d_.*x_]*Sqrt[e_.+f_.*x_]*Sqrt[g_.+h_.*x_]),x_Symbol] :=
          (A*b^2-a*b*B+a^2*C)*(a+b*x)^(m+1)*Sqrt[c+d*x]*Sqrt[e+f*x]*Sqrt[g+h*x]/((m+1)*(b*c-a*d)*(b*e-a*f)*(b*g-a*h)) -
          1/(2*(m+1)*(b*c-a*d)*(b*e-a*f)*(b*g-a*h)) \\[Star] Int[((a+b*x)^(m+1)/(Sqrt[c+d*x]*Sqrt[e+f*x]*Sqrt[g+h*x]))*
            Simp[A*(2*a^2*d*f*h*(m+1)-2*a*b*(m+1)*(d*f*g+d*e*h+c*f*h)+b^2*(2*m+3)*(d*e*g+c*f*g+c*e*h)) -
              (b*B-a*C)*(a*(d*e*g+c*f*g+c*e*h)+2*b*c*e*g*(m+1)) -
              2*((A*b-a*B)*(a*d*f*h*(m+1)-b*(m+2)*(d*f*g+d*e*h+c*f*h))-C*(a^2*(d*f*g+d*e*h+c*f*h)-b^2*c*e*g*(m+1)+a*b*(m+1)*(d*e*g+c*f*g+c*e*h)))*x +
              d*f*h*(2*m+5)*(A*b^2-a*b*B+a^2*C)*x^2,x],x] /;
        FreeQ[{a,b,c,d,e,f,g,h,A,B,C},x] && IntegerQ[2*m] && LtQ[m,-1]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [capital_a__, capital_b__, capital_c__, a__, b__, c__, d__, e__, f__, g__, h__, m_, x_],
        optional: [capital_a__, capital_b__, capital_c__, a__, b__, c__, d__, e__, f__, g__, h__],
        x_free: [capital_a__, capital_b__, capital_c__, a__, b__, c__, d__, e__, f__, g__, h__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__, capital_a__, capital_b__, capital_c__], x_)
                && integerq!(Atom::num(2) * &m_)
                && ltq!(m_, -1)
        },
        rhs: {
            let first = &a__ + &b__ * x_;
            let second = &c__ + &d__ * x_;
            let third = &e__ + &f__ * x_;
            let fourth = &g__ + &h__ * x_;
            let m1 = (&m_ + 1).expand();
            let m2 = (&m_ + 2).expand();
            let two_m_3 = Atom::num(2) * &m_ + 3;
            let two_m_5 = Atom::num(2) * &m_ + 5;
            let bc_ad = (&b__ * &c__ - &a__ * &d__).expand();
            let be_af = (&b__ * &e__ - &a__ * &f__).expand();
            let bg_ah = (&b__ * &g__ - &a__ * &h__).expand();
            let leading =
                (&capital_a__ * b__.pow(2) - &a__ * &b__ * &capital_b__ + a__.pow(2) * &capital_c__)
                    .expand();
            let denominator = (&m1 * &bc_ad * &be_af * &bg_ah).expand();
            let s2 = &d__ * &f__ * &g__ + &d__ * &e__ * &h__ + &c__ * &f__ * &h__;
            let s1 = &d__ * &e__ * &g__ + &c__ * &f__ * &g__ + &c__ * &e__ * &h__;
            let direct =
                &leading * first.pow(&m1) * second.sqrt() * third.sqrt() * fourth.sqrt()
                    / &denominator;
            let quadratic = simp!(
                &capital_a__
                    * (Atom::num(2) * a__.pow(2) * &d__ * &f__ * &h__ * &m1
                        - Atom::num(2) * &a__ * &b__ * &m1 * &s2
                        + b__.pow(2) * &two_m_3 * &s1)
                    - (&b__ * &capital_b__ - &a__ * &capital_c__)
                        * (&a__ * &s1 + Atom::num(2) * &b__ * &c__ * &e__ * &g__ * &m1)
                    - Atom::num(2)
                        * ((&capital_a__ * &b__ - &a__ * &capital_b__)
                            * (&a__ * &d__ * &f__ * &h__ * &m1 - &b__ * &m2 * &s2)
                            - &capital_c__
                                * (a__.pow(2) * &s2
                                    - b__.pow(2) * &c__ * &e__ * &g__ * &m1
                                    + &a__ * &b__ * &m1 * &s1))
                        * x_
                    + &d__ * &f__ * &h__ * &two_m_5 * &leading * x_.pow(2),
                x_
            );
            let radical_product = second.sqrt() * third.sqrt() * fourth.sqrt();
            let recursive_integrand = first.pow(&m1) * &quadratic / radical_product;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) - rubi_star(Atom::num(1) / (Atom::num(2) * denominator), recursive)
        },
    ));
}

fn push_rules_rule_2108(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_a__,
        capital_c__,
        a__,
        b__,
        c__,
        d__,
        m_,
        x_,
        e__,
        f__,
        g__,
        h__
    );
    rules.push(rubi_rule!(
        order: 2108,
        source: "Int[(a_.+b_.*x_)^m_*(A_.+C_.*x_^2)/(Sqrt[c_.+d_.*x_]*Sqrt[e_.+f_.*x_]*Sqrt[g_.+h_.*x_]),x_Symbol] :=
          (A*b^2+a^2*C)*(a+b*x)^(m+1)*Sqrt[c+d*x]*Sqrt[e+f*x]*Sqrt[g+h*x]/((m+1)*(b*c-a*d)*(b*e-a*f)*(b*g-a*h)) -
          1/(2*(m+1)*(b*c-a*d)*(b*e-a*f)*(b*g-a*h)) \\[Star] Int[((a+b*x)^(m+1)/(Sqrt[c+d*x]*Sqrt[e+f*x]*Sqrt[g+h*x]))*
            Simp[A*(2*a^2*d*f*h*(m+1)-2*a*b*(m+1)*(d*f*g+d*e*h+c*f*h)+b^2*(2*m+3)*(d*e*g+c*f*g+c*e*h)) +
              a*C*(a*(d*e*g+c*f*g+c*e*h)+2*b*c*e*g*(m+1)) -
              2*(A*b*(a*d*f*h*(m+1)-b*(m+2)*(d*f*g+d*e*h+c*f*h))-C*(a^2*(d*f*g+d*e*h+c*f*h)-b^2*c*e*g*(m+1)+a*b*(m+1)*(d*e*g+c*f*g+c*e*h)))*x +
              d*f*h*(2*m+5)*(A*b^2+a^2*C)*x^2,x],x] /;
        FreeQ[{a,b,c,d,e,f,g,h,A,C},x] && IntegerQ[2*m] && LtQ[m,-1]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [capital_a__, capital_c__, a__, b__, c__, d__, e__, f__, g__, h__, m_, x_],
        optional: [capital_a__, capital_c__, a__, b__, c__, d__, e__, f__, g__, h__],
        x_free: [capital_a__, capital_c__, a__, b__, c__, d__, e__, f__, g__, h__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__, capital_a__, capital_c__], x_)
                && integerq!(Atom::num(2) * &m_)
                && ltq!(m_, -1)
        },
        rhs: {
            let first = &a__ + &b__ * x_;
            let second = &c__ + &d__ * x_;
            let third = &e__ + &f__ * x_;
            let fourth = &g__ + &h__ * x_;
            let m1 = (&m_ + 1).expand();
            let m2 = (&m_ + 2).expand();
            let two_m_3 = Atom::num(2) * &m_ + 3;
            let two_m_5 = Atom::num(2) * &m_ + 5;
            let bc_ad = (&b__ * &c__ - &a__ * &d__).expand();
            let be_af = (&b__ * &e__ - &a__ * &f__).expand();
            let bg_ah = (&b__ * &g__ - &a__ * &h__).expand();
            let leading = (&capital_a__ * b__.pow(2) + a__.pow(2) * &capital_c__).expand();
            let denominator = (&m1 * &bc_ad * &be_af * &bg_ah).expand();
            let s2 = &d__ * &f__ * &g__ + &d__ * &e__ * &h__ + &c__ * &f__ * &h__;
            let s1 = &d__ * &e__ * &g__ + &c__ * &f__ * &g__ + &c__ * &e__ * &h__;
            let direct =
                &leading * first.pow(&m1) * second.sqrt() * third.sqrt() * fourth.sqrt()
                    / &denominator;
            let quadratic = simp!(
                &capital_a__
                    * (Atom::num(2) * a__.pow(2) * &d__ * &f__ * &h__ * &m1
                        - Atom::num(2) * &a__ * &b__ * &m1 * &s2
                        + b__.pow(2) * &two_m_3 * &s1)
                    + &a__
                        * &capital_c__
                        * (&a__ * &s1 + Atom::num(2) * &b__ * &c__ * &e__ * &g__ * &m1)
                    - Atom::num(2)
                        * (&capital_a__ * &b__ * (&a__ * &d__ * &f__ * &h__ * &m1 - &b__ * &m2 * &s2)
                            - &capital_c__
                                * (a__.pow(2) * &s2
                                    - b__.pow(2) * &c__ * &e__ * &g__ * &m1
                                    + &a__ * &b__ * &m1 * &s1))
                        * x_
                    + &d__ * &f__ * &h__ * &two_m_5 * &leading * x_.pow(2),
                x_
            );
            let radical_product = second.sqrt() * third.sqrt() * fourth.sqrt();
            let recursive_integrand = first.pow(&m1) * &quadratic / radical_product;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) - rubi_star(Atom::num(1) / (Atom::num(2) * denominator), recursive)
        },
    ));
}

fn push_rules_rule_2109(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        a__, b__, c__, d__, m_, n_, p_, px__, q_, x_, e__, f__, g__, h__
    );
    rules.push(rubi_rule!(
        order: 2109,
        source: "Int[Px_*(a_.+b_.*x_)^m_.*(c_.+d_.*x_)^n_.*(e_.+f_.*x_)^p_.*(g_.+h_.*x_)^q_.,x_Symbol] :=
          Int[ExpandIntegrand[Px*(a+b*x)^m*(c+d*x)^n*(e+f*x)^p*(g+h*x)^q,x],x] /;
        FreeQ[{a,b,c,d,e,f,g,h,m,n,p,q},x] && PolyQ[Px,x] && IntegersQ[m,n]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [px__, a__, b__, c__, d__, e__, f__, g__, h__, m_, n_, p_, q_, x_],
        optional: [a__, b__, c__, d__, e__, f__, g__, h__, m_, n_, p_, q_],
        x_free: [a__, b__, c__, d__, e__, f__, g__, h__, m_, n_, p_, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__, m_, n_, p_, q_], x_)
                && poly_q(&px__, x_)
                && integersq!([m_, n_])
        },
        rhs: {
            let integrand = &px__
                * (&a__ + &b__ * x_).pow(m_)
                * (&c__ + &d__ * x_).pow(n_)
                * (&e__ + &f__ * x_).pow(&p_)
                * (&g__ + &h__ * x_).pow(&q_);
            let expanded = rubi_expand_integrand(&integrand, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_2110(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        a__, b__, c__, d__, m_, n_, p_, px__, q_, x_, e__, f__, g__, h__
    );
    rules.push(rubi_rule!(
        order: 2110,
        source: "Int[Px_*(a_.+b_.*x_)^m_.*(c_.+d_.*x_)^n_.*(e_.+f_.*x_)^p_.*(g_.+h_.*x_)^q_.,x_Symbol] :=
          PolynomialRemainder[Px,a+b*x,x] \\[Star] Int[(a+b*x)^m*(c+d*x)^n*(e+f*x)^p*(g+h*x)^q,x] +
          Int[PolynomialQuotient[Px,a+b*x,x]*(a+b*x)^(m+1)*(c+d*x)^n*(e+f*x)^p*(g+h*x)^q,x] /;
        FreeQ[{a,b,c,d,e,f,g,h,m,n,p,q},x] && PolyQ[Px,x] && EqQ[m,-1]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [px__, a__, b__, c__, d__, e__, f__, g__, h__, m_, n_, p_, q_, x_],
        optional: [a__, b__, c__, d__, e__, f__, g__, h__, m_, n_, p_, q_],
        x_free: [a__, b__, c__, d__, e__, f__, g__, h__, m_, n_, p_, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__, m_, n_, p_, q_], x_)
                && poly_q(&px__, x_)
                && eqq!(m_, -1)
        },
        rhs: {
            let first = &a__ + &b__ * x_;
            let second = &c__ + &d__ * x_;
            let third = &e__ + &f__ * x_;
            let fourth = &g__ + &h__ * x_;
            let remainder = rubi_polynomial_remainder(&px__, &first, x_).rubi_rhs();
            let base = second.pow(&n_) * third.pow(&p_) * fourth.pow(&q_);
            let first_recursive = rubi_rhs_int(&(first.pow(&m_) * &base), x_);
            let quotient = rubi_polynomial_quotient(&px__, &first, x_).rubi_rhs();
            let second_recursive = rubi_rhs_int(
                &(quotient * first.pow(&m_ + 1) * base),
                x_,
            );
            rubi_star(remainder, first_recursive) + second_recursive
        },
    ));
}

fn push_rules_rule_2111(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        a__, b__, c__, d__, m_, n_, p_, px__, q_, x_, e__, f__, g__, h__
    );
    rules.push(rubi_rule!(
        order: 2111,
        source: "Int[Px_*(a_.+b_.*x_)^m_.*(c_.+d_.*x_)^n_.*(e_.+f_.*x_)^p_.*(g_.+h_.*x_)^q_.,x_Symbol] :=
          PolynomialRemainder[Px,a+b*x,x] \\[Star] Int[(a+b*x)^m*(c+d*x)^n*(e+f*x)^p*(g+h*x)^q,x] +
          Int[PolynomialQuotient[Px,a+b*x,x]*(a+b*x)^(m+1)*(c+d*x)^n*(e+f*x)^p*(g+h*x)^q,x] /;
        FreeQ[{a,b,c,d,e,f,g,h,m,n,p,q},x] && PolyQ[Px,x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [px__, a__, b__, c__, d__, e__, f__, g__, h__, m_, n_, p_, q_, x_],
        optional: [a__, b__, c__, d__, e__, f__, g__, h__, m_, n_, p_, q_],
        x_free: [a__, b__, c__, d__, e__, f__, g__, h__, m_, n_, p_, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__, m_, n_, p_, q_], x_)
                && poly_q(&px__, x_)
        },
        rhs: {
            let first = &a__ + &b__ * x_;
            let second = &c__ + &d__ * x_;
            let third = &e__ + &f__ * x_;
            let fourth = &g__ + &h__ * x_;
            let remainder = rubi_polynomial_remainder(&px__, &first, x_).rubi_rhs();
            let base = second.pow(&n_) * third.pow(&p_) * fourth.pow(&q_);
            let first_recursive = rubi_rhs_int(&(first.pow(&m_) * &base), x_);
            let quotient = rubi_polynomial_quotient(&px__, &first, x_).rubi_rhs();
            let second_recursive = rubi_rhs_int(
                &(quotient * first.pow(&m_ + 1) * base),
                x_,
            );
            rubi_star(remainder, first_recursive) + second_recursive
        },
    ));
}

fn push_rules_rule_2097(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        capital_a__,
        capital_b__,
        a__,
        b__,
        c__,
        d__,
        e__,
        f__,
        g__,
        h__,
        x_
    );
    rules.push(rubi_rule!(
        order: 2097,
        source: "Int[(a_.+b_.*x_)*(A_.+B_.*x_)/(Sqrt[c_.+d_.*x_]*Sqrt[e_.+f_.*x_]*Sqrt[g_.+h_.*x_]),x_Symbol] :=
          2*b*B*Sqrt[c+d*x]*Sqrt[e+f*x]*Sqrt[g+h*x]/(3*d*f*h) +
          1/(3*d*f*h) \\[Star]
            Int[1/(Sqrt[c+d*x]*Sqrt[e+f*x]*Sqrt[g+h*x])*
              Simp[3*a*A*d*f*h-b*B*(d*e*g+c*f*g+c*e*h)+(3*A*b*d*f*h+B*(3*a*d*f*h-2*b*(d*f*g+d*e*h+c*f*h)))*x,x],x] /;
        FreeQ[{a,b,c,d,e,f,g,h,A,B},x]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern: (a__ + b__ * x_) * (capital_a__ + capital_b__ * x_)
            / ((c__ + d__ * x_).sqrt()
                * (e__ + f__ * x_).sqrt()
                * (g__ + h__ * x_).sqrt()),
        with: [a__, b__, capital_a__, capital_b__, c__, d__, e__, f__, g__, h__, x_],
        optional: [a__, b__, capital_a__, capital_b__, c__, d__, e__, f__, g__, h__],
        x_free: [a__, b__, capital_a__, capital_b__, c__, d__, e__, f__, g__, h__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__, capital_a__, capital_b__], x_)
        },
        rhs: {
            let second = &c__ + &d__ * x_;
            let third = &e__ + &f__ * x_;
            let fourth = &g__ + &h__ * x_;
            let denominator = Atom::num(3) * &d__ * &f__ * &h__;
            let direct = Atom::num(2)
                * &b__
                * &capital_b__
                * second.sqrt()
                * third.sqrt()
                * fourth.sqrt()
                / &denominator;
            let payload = simp!(
                Atom::num(3) * &a__ * &capital_a__ * &d__ * &f__ * &h__
                    - &b__
                        * &capital_b__
                        * (&d__ * &e__ * &g__ + &c__ * &f__ * &g__ + &c__ * &e__ * &h__)
                    + (Atom::num(3) * &capital_a__ * &b__ * &d__ * &f__ * &h__
                        + &capital_b__
                            * (Atom::num(3) * &a__ * &d__ * &f__ * &h__
                                - Atom::num(2)
                                    * &b__
                                    * (&d__ * &f__ * &g__
                                        + &d__ * &e__ * &h__
                                        + &c__ * &f__ * &h__)))
                        * x_,
                x_
            );
            let recursive_integrand = payload / (second.sqrt() * third.sqrt() * fourth.sqrt());
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
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
    let capital_a__ = symbols.capital_a__;
    let capital_b__ = symbols.capital_b__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let g__ = symbols.g__;
    let h__ = symbols.h__;
    let m_ = symbols.m_;
    let x_ = symbols.x_;
    (a__ + b__ * x_).pow(m_) * (capital_a__ + capital_b__ * x_)
        / ((c__ + d__ * x_).sqrt() * (e__ + f__ * x_).sqrt() * (g__ + h__ * x_).sqrt())
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let capital_a__ = symbols.capital_a__;
    let capital_b__ = symbols.capital_b__;
    let capital_c__ = symbols.capital_c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let g__ = symbols.g__;
    let h__ = symbols.h__;
    let m_ = symbols.m_;
    let x_ = symbols.x_;
    (a__ + b__ * x_).pow(m_) * (capital_a__ + capital_b__ * x_ + capital_c__ * x_.pow(2))
        / ((c__ + d__ * x_).sqrt() * (e__ + f__ * x_).sqrt() * (g__ + h__ * x_).sqrt())
}

#[inline(never)]
fn rubi_shared_pattern_2(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let capital_a__ = symbols.capital_a__;
    let capital_c__ = symbols.capital_c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let g__ = symbols.g__;
    let h__ = symbols.h__;
    let m_ = symbols.m_;
    let x_ = symbols.x_;
    (a__ + b__ * x_).pow(m_) * (capital_a__ + capital_c__ * x_.pow(2))
        / ((c__ + d__ * x_).sqrt() * (e__ + f__ * x_).sqrt() * (g__ + h__ * x_).sqrt())
}

#[inline(never)]
fn rubi_shared_pattern_3(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let capital_a__ = symbols.capital_a__;
    let capital_b__ = symbols.capital_b__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let g__ = symbols.g__;
    let h__ = symbols.h__;
    let x_ = symbols.x_;
    (a__ + b__ * x_).sqrt() * (capital_a__ + capital_b__ * x_)
        / ((c__ + d__ * x_).sqrt() * (e__ + f__ * x_).sqrt() * (g__ + h__ * x_).sqrt())
}

#[inline(never)]
fn rubi_shared_pattern_4(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let g__ = symbols.g__;
    let h__ = symbols.h__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let px__ = symbols.px__;
    let q_ = symbols.q_;
    let x_ = symbols.x_;
    px__ * (a__ + b__ * x_).pow(m_)
        * (c__ + d__ * x_).pow(n_)
        * (e__ + f__ * x_).pow(p_)
        * (g__ + h__ * x_).pow(q_)
}
