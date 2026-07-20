use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    let symbols = rubi_symbols();
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let g__ = symbols.g__;
    let h__ = symbols.h__;
    let j_ = symbols.j_;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let n1_ = symbols.n1_;
    let n2_ = symbols.n2_;
    let p_ = symbols.p_;
    let px__ = symbols.px__;
    let q_ = symbols.q_;
    let u_ = symbols.u_;
    let u__ = symbols.u__;
    let v_ = symbols.v_;
    let v__ = symbols.v__;
    let x_ = symbols.x_;
    let capital_a__ = symbols.capital_a__;
    let capital_b__ = symbols.capital_b__;
    let capital_f_ = symbols.capital_f_;
    let capital_g_ = symbols.capital_g_;
    let head = symbols.rubi_expand_integrand;

    rules.push(rubi_helper_row!(
        order: 3,
        source: "ExpandIntegrand[u_^p_.,x_Symbol]",
        pattern: u_.pow(p_),
        head: head,
        with: [u_, p_, x_],
        optional: [p_],
        when: { rubi_sum_q(&u_) && igtq!(p_, 0) },
        rhs: {
            let expanded = if eqq!(p_, 1) {
                u_.to_owned()
            } else {
                rubi_mathematica_expand(&u_.pow(p_), Some(x_))
            };
            rubi_expand_cleanup(&expanded, x_)
        },
    ));

    rules.push(rubi_helper_row!(
        order: 4,
        source: "ExpandIntegrand[(a_+b_.*x_^n_)^p_.,x_Symbol]",
        pattern: (a__ + b__ * x_.pow(n_)).pow(p_),
        head: head,
        with: [a__, b__, n_, p_, x_],
        optional: [b__, p_],
        when: { integerq!(p_) && iltq!(n_, 0) },
        rhs: {
            rubi_expand_integrand_or_self(
                &(x_.pow(&n_ * &p_) * (&b__ + &a__ * x_.pow(-&n_)).pow(&p_)),
                x_,
            )
        },
    ));

    rules.push(rubi_helper_row!(
        order: 5,
        source: "ExpandIntegrand[x_^m_.*(a_+b_.*x_^n_)^p_.,x_Symbol]",
        pattern: x_.pow(m_) * (a__ + b__ * x_.pow(n_)).pow(p_),
        head: head,
        with: [m_, a__, b__, n_, p_, x_],
        optional: [m_, b__, p_],
        when: { integerq!(p_) && iltq!(n_, 0) },
        rhs: {
            rubi_expand_integrand_or_self(
                &(x_.pow(&m_ + &n_ * &p_) * (&b__ + &a__ * x_.pow(-&n_)).pow(&p_)),
                x_,
            )
        },
    ));

    rules.push(rubi_helper_row!(
        order: 6,
        source: "ExpandIntegrand[Px_.*x_^m_*(b_.*x_^n_.+c_.*x_^n1_)^p_.,x_Symbol]",
        pattern: px__ * x_.pow(m_)
            * (b__ * x_.pow(n_) + c__ * x_.pow(n1_)).pow(p_),
        head: head,
        with: [px__, m_, b__, n_, c__, n1_, p_, x_],
        optional: [px__, b__, n_, c__],
        when: {
            freeq!([b__, c__, m_], x_)
                && poly_q(&px__, x_)
                && igtq!(n_, 0)
                && eqq!(n1_, &n_ + 1)
                && integerq!(p_)
        },
        rhs: {
            rubi_expand_integrand_or_self(
                &(&px__ * x_.pow(&m_ + &n_ * &p_) * (&b__ + &c__ * x_).pow(&p_)),
                x_,
            )
        },
    ));

    rules.push(rubi_helper_row!(
        order: 7,
        source: "ExpandIntegrand[Px_.*(b_.*x_^n_.+c_.*x_^n1_)^p_.,x_Symbol]",
        pattern: px__ * (b__ * x_.pow(n_) + c__ * x_.pow(n1_)).pow(p_),
        head: head,
        with: [px__, b__, n_, c__, n1_, p_, x_],
        optional: [px__, b__, n_, c__],
        when: {
            freeq!([b__, c__], x_)
                && poly_q(&px__, x_)
                && igtq!(n_, 0)
                && eqq!(n1_, &n_ + 1)
                && integerq!(p_)
        },
        rhs: {
            rubi_expand_integrand_or_self(
                &(&px__ * x_.pow(&n_ * &p_) * (&b__ + &c__ * x_).pow(&p_)),
                x_,
            )
        },
    ));

    rules.push(
        rubi_helper_row!(
            order: 8,
            source: "ExpandIntegrand[(a_.+b_.*F_^u_)^p_.*(c_.+d_.*F_^v_)^q_.,x_Symbol]",
            pattern: (a__ + b__ * capital_f_.pow(u_)).pow(p_)
                * (c__ + d__ * capital_f_.pow(v_)).pow(q_),
            head: head,
            with: [a__, b__, capital_f_, u_, p_, c__, d__, v_, q_, x_],
            optional: [a__, b__, p_, c__, d__, q_],
            x_dep: [],
            x_free: [capital_f_, a__, b__, c__, d__],
            when: {
                freeq!([capital_f_, a__, b__, c__, d__], x_)
                    && integersq!([p_, q_])
                    && rationalq!(rubi_simplify(&(&u_ / &v_)))
            },
            rhs: {
                let k = rubi_simplify(&(&u_ / &v_));
                let numerator = rubi_numerator(&k);
                let denominator = rubi_denominator_atom(&k);
                let expanded = rubi_expand_integrand_or_self(
                    &((&a__ + &b__ * x_.pow(numerator)).pow(&p_)
                        * (&c__ + &d__ * x_.pow(&denominator)).pow(&q_)),
                    x_,
                );
                rubi_replace_all(
                    &expanded,
                    x_,
                    capital_f_.pow(&v_ / denominator),
                )
            },
        )
        .with_x_dependent_exponent_for_x_dependent_candidate(),
    );

    rules.push(rubi_helper_row!(
        order: 9,
        source: "ExpandIntegrand[(a_.+b_.*x_)^m_.*F_^(e_.*(c_.+d_.*x_)^n_.)/(g_.+h_.*x_),x_Symbol]",
        pattern: (a__ + b__ * x_).pow(m_)
            * capital_f_.pow(e__ * (c__ + d__ * x_).pow(n_))
            * (g__ + h__ * x_).pow(-1),
        head: head,
        with: [a__, b__, m_, capital_f_, e__, c__, d__, n_, g__, h__, x_],
        optional: [a__, b__, e__, c__, d__, n_, g__, h__],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__, g__, h__], x_)
                && igtq!(m_, 0)
                && eqq!(&b__ * &c__ - &a__ * &d__, 0)
        },
        rhs: {
            let m = integer_i64(&m_)?;
            let tmp = &a__ * &h__ - &b__ * &g__;
            let exponential = capital_f_.pow(&e__ * (&c__ + &d__ * x_).pow(&n_));
            let mut result = rubi_simplify_term(
                &(tmp.pow(&m_) / h__.pow(&m_)),
                x_,
            ) * &exponential / (&g__ + &h__ * x_);
            for k in 1..=m {
                result += rubi_simplify_term(
                    &(&b__ * tmp.pow(k - 1) / h__.pow(k)),
                    x_,
                ) * &exponential
                    * (&a__ + &b__ * x_).pow(m - k);
            }
            result
        },
    ));

    rules.push(rubi_helper_row!(
        order: 10,
        source: "ExpandIntegrand[x_^m_.*(e_+f_.*x_)^p_.*F_^(b_.*(c_.+d_.*x_)^n_.),x_Symbol]",
        pattern: x_.pow(m_)
            * (e__ + f__ * x_).pow(p_)
            * capital_f_.pow(b__ * (c__ + d__ * x_).pow(n_)),
        head: head,
        with: [m_, e__, f__, p_, capital_f_, b__, c__, d__, n_, x_],
        optional: [f__, b__, c__, d__, n_],
        when: {
            freeq!([capital_f_, b__, c__, d__, e__, f__, m_, n_, p_], x_)
        },
        rhs: {
            let linear = &e__ + &f__ * x_;
            let exponential = capital_f_.pow(&b__ * (&c__ + &d__ * x_).pow(&n_));
            if igtq!(m_, 0)
                && igtq!(p_, 0)
                && leq!(m_, p_)
                && (eqq!(n_, 1) || eqq!(&d__ * &e__ - &c__ * &f__, 0))
            {
                rubi_expand_linear_product(
                    &(linear.pow(&p_) * &exponential),
                    x_.pow(&m_),
                    &e__,
                    &f__,
                    x_,
                )?
            } else if igtq!(p_, 0) {
                let expanded = rubi_mathematica_expand(&linear.pow(&p_), Some(x_));
                map_sum_terms(&expanded, |term| x_.pow(&m_) * &exponential * term)
            } else {
                let multiplier = x_.pow(&m_) * linear.pow(&p_);
                rubi_expand_integrand_product(&exponential, &multiplier, x_)
            }
        },
    ));

    rules.push(rubi_helper_row!(
        order: 11,
        source: "ExpandIntegrand[x_^m_.*(e_+f_.*x_)^p_.*F_^(a_.+b_.*(c_.+d_.*x_)^n_.),x_Symbol]",
        pattern: x_.pow(m_)
            * (e__ + f__ * x_).pow(p_)
            * capital_f_.pow(a__ + b__ * (c__ + d__ * x_).pow(n_)),
        head: head,
        with: [m_, e__, f__, p_, capital_f_, a__, b__, c__, d__, n_, x_],
        optional: [f__, a__, b__, c__, d__, n_],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__, f__, m_, n_, p_], x_)
        },
        rhs: {
            let linear = &e__ + &f__ * x_;
            let exponential =
                capital_f_.pow(&a__ + &b__ * (&c__ + &d__ * x_).pow(&n_));
            if igtq!(m_, 0)
                && igtq!(p_, 0)
                && leq!(m_, p_)
                && (eqq!(n_, 1) || eqq!(&d__ * &e__ - &c__ * &f__, 0))
            {
                rubi_expand_linear_product(
                    &(linear.pow(&p_) * &exponential),
                    x_.pow(&m_),
                    &e__,
                    &f__,
                    x_,
                )?
            } else if igtq!(p_, 0) {
                let expanded = rubi_mathematica_expand(&linear.pow(&p_), Some(x_));
                map_sum_terms(&expanded, |term| x_.pow(&m_) * &exponential * term)
            } else {
                let multiplier = x_.pow(&m_) * linear.pow(&p_);
                rubi_expand_integrand_product(&exponential, &multiplier, x_)
            }
        },
    ));

    rules.push(rubi_helper_row!(
        order: 12,
        source: "ExpandIntegrand[u_.*(a_+b_.*F_^v_)^m_.*(c_+d_.*F_^v_)^n_,x_Symbol]",
        pattern: u__ * (a__ + b__ * capital_f_.pow(v_)).pow(m_)
            * (c__ + d__ * capital_f_.pow(v_)).pow(n_),
        head: head,
        with: [u__, a__, b__, capital_f_, v_, m_, c__, d__, n_, x_],
        optional: [u__, b__, d__],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__], x_)
                && integersq!([m_, n_])
                && ltq!(n_, 0)
        },
        rhs: {
            let expanded = rubi_expand_integrand_or_self(
                &((&a__ + &b__ * x_).pow(&m_) * (&c__ + &d__ * x_).pow(&n_)),
                x_,
            );
            let replaced = rubi_replace_all(&expanded, x_, capital_f_.pow(&v_));
            rubi_sum_q(&replaced).then(|| map_sum_terms(&replaced, |term| &u__ * term))?
        },
    ));

    rules.push(rubi_helper_row!(
        order: 13,
        source: "ExpandIntegrand[u_*(a_.+b_.*x_)^m_.*F_^(e_.*(c_.+d_.*x_)^n_.),x_Symbol]",
        pattern: u__ * (a__ + b__ * x_).pow(m_)
            * capital_f_.pow(e__ * (c__ + d__ * x_).pow(n_)),
        head: head,
        with: [u__, a__, b__, m_, capital_f_, e__, c__, d__, n_, x_],
        optional: [a__, b__, e__, c__, d__, n_],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__, m_, n_], x_)
                && rubi_polynomial_q(&u__, x_)
        },
        rhs: {
            let expanded = rubi_expand_integrand_or_self(
                &(&u__ * (&a__ + &b__ * x_).pow(&m_)),
                x_,
            );
            if !rubi_sum_q(&expanded) {
                return None;
            }
            let exponential = capital_f_.pow(&e__ * (&c__ + &d__ * x_).pow(&n_));
            map_sum_terms(&expanded, |term| &exponential * term)
        },
    ));

    rules.push(rubi_helper_row!(
        order: 14,
        source: "ExpandIntegrand[u_*(a_.+b_.*x_)^m_.*Log[c_.*(d_.+e_.*x_^n_.)^p_.],x_Symbol]",
        pattern: u__ * (a__ + b__ * x_).pow(m_)
            * (c__ * (d__ + e__ * x_.pow(n_)).pow(p_)).log(),
        head: head,
        with: [u__, a__, b__, m_, c__, d__, e__, n_, p_, x_],
        optional: [a__, b__, m_, c__, d__, e__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_, p_], x_)
                && rubi_polynomial_q(&u__, x_)
        },
        rhs: {
            let logarithm = (&c__ * (&d__ + &e__ * x_.pow(&n_)).pow(&p_)).log();
            let multiplier = &u__ * (&a__ + &b__ * x_).pow(&m_);
            rubi_expand_integrand_product(&logarithm, &multiplier, x_)
        },
    ));

    rules.push(rubi_helper_row!(
        order: 15,
        source: "ExpandIntegrand[u_*F_^(e_.*(c_.+d_.*x_)^n_.),x_Symbol]",
        pattern: u__ * capital_f_.pow(e__ * (c__ + d__ * x_).pow(n_)),
        head: head,
        with: [u__, capital_f_, e__, c__, d__, n_, x_],
        optional: [e__, c__, d__, n_],
        when: {
            freeq!([capital_f_, c__, d__, e__, n_], x_)
                && rubi_polynomial_q(&u__, x_)
        },
        rhs: {
            let exponential = capital_f_.pow(&e__ * (&c__ + &d__ * x_).pow(&n_));
            if eqq!(n_, 1) {
                rubi_expand_integrand_product(&exponential, &u__, x_)
            } else {
                rubi_expand_linear_product(&exponential, &u__, &c__, &d__, x_)?
            }
        },
    ));

    rules.push(rubi_helper_row!(
        order: 16,
        source: "ExpandIntegrand[F_[u_]^m_.*(a_+b_.*G_[u_])^n_.,x_Symbol]",
        pattern: capital_f_.call(u_).pow(m_)
            * (a__ + b__ * capital_g_.call(u_)).pow(n_),
        head: head,
        with: [capital_f_, u_, m_, a__, b__, capital_g_, n_, x_],
        optional: [m_, b__, n_],
        when: {
            let f_call = rubi_function_head_symbol(&capital_f_).unwrap().call(&u_);
            let g_call = rubi_function_head_symbol(&capital_g_).unwrap().call(&u_);
            freeq!([a__, b__], x_)
                && integersq!([m_, n_])
                && f_call * g_call == Atom::num(1)
        },
        rhs: {
            let expanded = rubi_expand_integrand_or_self(
                &((&a__ + &b__ * x_).pow(&n_) / x_.pow(&m_)),
                x_,
            );
            rubi_replace_all(
                &expanded,
                x_,
                rubi_function_head_symbol(&capital_g_).unwrap().call(u_),
            )
        },
    ));

    rules.push(rubi_helper_row!(
        order: 17,
        source: "ExpandIntegrand[u_*(a_.+b_.*Log[c_.*(d_.*(e_.+f_.*x_)^p_.)^q_.])^n_,x_Symbol]",
        pattern: u__
            * (a__
                + b__ * (c__ * (d__ * (e__ + f__ * x_).pow(p_)).pow(q_)).log())
                .pow(n_),
        head: head,
        with: [u__, a__, b__, c__, d__, e__, f__, p_, q_, n_, x_],
        optional: [a__, b__, c__, d__, e__, f__, p_, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, n_, p_, q_], x_)
                && rubi_polynomial_q(&u__, x_)
        },
        rhs: {
            let logarithmic = (&a__
                + &b__
                    * (&c__ * (&d__ * (&e__ + &f__ * x_).pow(&p_)).pow(&q_)).log())
            .pow(&n_);
            rubi_expand_linear_product(&logarithmic, &u__, &e__, &f__, x_)?
        },
    ));

    rules.push(rubi_helper_row!(
        order: 18,
        source: "ExpandIntegrand[u_*(a_.+b_.*F_[c_.+d_.*x_])^n_,x_Symbol]",
        pattern: u__
            * (a__ + b__ * capital_f_.call(c__ + d__ * x_)).pow(n_),
        head: head,
        with: [u__, a__, b__, capital_f_, c__, d__, n_, x_],
        optional: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, n_], x_)
                && rubi_polynomial_q(&u__, x_)
                && rubi_function_head_symbol(&capital_f_).is_some_and(|function| {
                    function == symbol!("asin")
                        || function == symbol!("acos")
                        || function == symbol!("asinh")
                        || function == symbol!("acosh")
                })
        },
        rhs: {
            let inverse = rubi_function_head_symbol(&capital_f_)
                .unwrap()
                .call(&c__ + &d__ * x_);
            let powered = (&a__ + &b__ * inverse).pow(&n_);
            rubi_expand_linear_product(&powered, &u__, &c__, &d__, x_)?
        },
    ));

    rules.push(rubi_helper_row!(
        order: 19,
        source: "ExpandIntegrand[u_./(a_.*x_^n_+b_.*Sqrt[c_+d_.*x_^j_]),x_Symbol]",
        pattern: u__ * (a__ * x_.pow(n_) + b__ * (c__ + d__ * x_.pow(j_)).sqrt()).pow(-1),
        head: head,
        with: [u__, a__, n_, b__, c__, d__, j_, x_],
        optional: [u__, a__, b__, d__],
        when: {
            freeq!([a__, b__, c__, d__, n_], x_)
                && eqq!(j_, Atom::num(2) * &n_)
        },
        rhs: {
            rubi_expand_integrand(
                &(&u__
                    * (&a__ * x_.pow(&n_)
                        - &b__ * (&c__ + &d__ * x_.pow(Atom::num(2) * &n_)).sqrt())
                    / (-b__.pow(2) * &c__ + (a__.pow(2) - b__.pow(2) * &d__) * x_.pow(Atom::num(2) * &n_))),
                x_,
            )
        },
    ));

    rules.push(
        rubi_helper_row!(
            order: 20,
            source: "ExpandIntegrand[(a_+b_.*x_)^m_/(c_+d_.*x_),x_Symbol]",
            pattern: (a__ + b__ * x_).pow(m_) * (c__ + d__ * x_).pow(-1),
            head: head,
            with: [a__, b__, m_, c__, d__, x_],
            optional: [b__, d__],
            x_dep: [],
            x_free: [a__, b__, c__, d__],
            when: {
                freeq!([a__, b__, c__, d__], x_) && igtq!(m_, 0)
            },
            rhs: {
                let linear = &a__ + &b__ * x_;
                let denominator = &c__ + &d__ * x_;
                if rationalq!([a__, b__, c__, d__]) {
                    rubi_expand_expression(&(linear.pow(&m_) / denominator), x_)
                } else {
                    let m = integer_i64(&m_)?;
                    let tmp = &a__ * &d__ - &b__ * &c__;
                    let mut result = rubi_simplify_term(
                        &(tmp.pow(m) / d__.pow(m)),
                        x_,
                    ) / (&c__ + &d__ * x_);
                    for k in 1..=m {
                        result += rubi_simplify_term(
                            &(&b__ * tmp.pow(k - 1) / d__.pow(k)),
                            x_,
                        ) * (&a__ + &b__ * x_).pow(m - k);
                    }
                    result
                }
            },
        )
        .with_positive_integer_affine_power(),
    );

    rules.push(
        rubi_helper_row!(
            order: 21,
            source: "ExpandIntegrand[(a_+b_.*x_)^m_.*(A_+B_.*x_)/(c_+d_.*x_),x_Symbol]",
            pattern: (a__ + b__ * x_).pow(m_)
                * (capital_a__ + capital_b__ * x_)
                * (c__ + d__ * x_).pow(-1),
            head: head,
            with: [a__, b__, m_, capital_a__, capital_b__, c__, d__, x_],
            optional: [b__, capital_b__, d__],
            x_dep: [],
            x_free: [a__, b__, c__, d__, capital_a__, capital_b__],
            when: {
                freeq!([a__, b__, c__, d__, capital_a__, capital_b__], x_)
                    && igtq!(m_, 0)
            },
            rhs: {
                let linear = &a__ + &b__ * x_;
                let numerator_linear = &capital_a__ + &capital_b__ * x_;
                let denominator = &c__ + &d__ * x_;
                if rationalq!([a__, b__, c__, d__, capital_a__, capital_b__]) {
                    rubi_expand_expression(
                        &(linear.pow(&m_) * numerator_linear / denominator),
                        x_,
                    )
                } else {
                    let tmp1 = (&capital_a__ * &d__ - &capital_b__ * &c__) / &d__;
                    let tmp2 = rubi_expand_integrand_or_self(
                        &(linear.pow(&m_) / (&c__ + &d__ * x_)),
                        x_,
                    );
                    let tmp2 = if rubi_sum_q(&tmp2) {
                        map_sum_terms(&tmp2, |term| {
                            rubi_simplify_term(&(&tmp1 * term), x_)
                        })
                    } else {
                        rubi_simplify_term(&(&tmp1 * tmp2), x_)
                    };
                    rubi_simplify_term(&(&capital_b__ / &d__), x_) * linear.pow(&m_)
                        + tmp2
                }
            },
        )
        .with_positive_integer_affine_power(),
    );

    rules.push(rubi_helper_row!(
        order: 22,
        source: "ExpandIntegrand[u_*(a_+b_.*x_)^m_.*(c_+d_.*x_)^n_.,x_Symbol]",
        pattern: u__ * (a__ + b__ * x_).pow(m_) * (c__ + d__ * x_).pow(n_),
        head: head,
        with: [u__, a__, b__, m_, c__, d__, n_, x_],
        optional: [b__, m_, d__, n_],
        x_dep: [],
        x_free: [a__, b__, c__, d__, m_, n_],
        noninteger_affine_power_difference: true,
        when: {
            freeq!([a__, b__, c__, d__, m_, n_], x_)
                && poly_q(&u__, x_)
                && !integerq!(m_)
                && igtq!(&n_ - &m_, 0)
        },
        rhs: {
            rubi_expand_integrand_product(
                &(c__ + d__ * x_).pow(n_),
                &(u__ * (a__ + b__ * x_).pow(m_)),
                x_,
            )
        },
    ));

    rules.push(
        rubi_helper_row!(
            order: 23,
            source: "ExpandIntegrand[u_*(a_+b_.*x_)^m_.,x_Symbol]",
            pattern: u__ * (a__ + b__ * x_).pow(m_),
            head: head,
            with: [u__, a__, b__, m_, x_],
            optional: [b__, m_],
            x_dep: [],
            x_free: [a__, b__, m_],
            when: {
                freeq!([a__, b__, m_], x_)
                    && poly_q(&u__, x_)
                    && !(igtq!(m_, 0)
                        && rubi_match_polynomial_times_larger_linear_power_q(&u__, &m_, x_))
            },
            rhs: {
                let linear = &a__ + &b__ * x_;
                let sum1 = rubi_expand_linear_product(&linear.pow(&m_), &u__, &a__, &b__, x_)?;
                if !integerq!(m_) || gtq!(m_, 2) && rubi_linear_q(&u__, x_) {
                    sum1
                } else {
                    let sum2 = rubi_expand_expression(&(&u__ * linear.pow(&m_)), x_);
                    if rubi_sum_q(&sum2) {
                        if gtq!(m_, 0) {
                            let exponent = rubi_expon(&u__, x_).unwrap_or(0);
                            if rubi_length(&sum2) <= (exponent + 2).max(0) as usize
                                || 3 * rubi_leaf_count(&sum2)
                                    <= 2 * rubi_leaf_count(&sum1)
                            {
                                sum2
                            } else {
                                sum1
                            }
                        } else if rubi_leaf_count(&sum2)
                            <= rubi_leaf_count(&sum1) + 2
                        {
                            sum2
                        } else {
                            sum1
                        }
                    } else {
                        sum1
                    }
                }
            },
        )
        .with_polynomial_complement_of_affine_power(),
    );

    rules.push(
        rubi_helper_row!(
            order: 24,
            source: "ExpandIntegrand[u_*v_^n_*(a_+b_.*x_)^m_,x_Symbol]",
            pattern: u__ * v_.pow(n_) * (a__ + b__ * x_).pow(m_),
            head: head,
            with: [u__, v_, n_, a__, b__, m_, x_],
            optional: [b__, m_],
            x_dep: [],
            x_free: [a__, b__, m_],
            when: {
                let degrees = rubi_expon(&u__, x_).zip(rubi_expon(&v_, x_));
                freeq!([a__, b__, m_], x_)
                    && iltq!(n_, 0)
                    && !integerq!(m_)
                    && rubi_polynomial_q(&u__, x_)
                    && rubi_polynomial_q(&v_, x_)
                    && rationalq!(m_)
                    && ltq!(m_, -1)
                    && degrees.is_some_and(|(u_degree, v_degree)| {
                        let minimum_degree =
                            -(&n_ + rubi_int_part(&m_)) * Atom::num(v_degree);
                        geq!(Atom::num(u_degree), minimum_degree)
                    })
            },
            rhs: {
                let linear = &a__ + &b__ * x_;
                let divisor = v_.pow(-&n_) * linear.pow(-rubi_int_part(&m_));
                let (quotient, remainder) =
                    polynomial_quotient_remainder(&u__, &divisor, x_)?;
                let first = quotient * linear.pow(rubi_frac_part(&m_));
                let second = remainder * v_.pow(&n_) * linear.pow(&m_);
                rubi_expand_integrand_or_self(&first, x_)
                        + rubi_expand_integrand_or_self(&second, x_)
            },
        )
        .with_rational_noninteger_affine_power_below_negative_one(),
    );

    rules.push(rubi_helper_row!(
        order: 25,
        source: "ExpandIntegrand[u_*v_^n_*(a_+b_.*x_)^m_,x_Symbol]",
        pattern: u__ * v_.pow(n_) * (a__ + b__ * x_).pow(m_),
        head: head,
        with: [u__, v_, n_, a__, b__, m_, x_],
        optional: [b__, m_],
        x_dep: [],
        x_free: [a__, b__, m_],
        when: {
            let degrees = rubi_expon(&u__, x_).zip(rubi_expon(&v_, x_));
            freeq!([a__, b__, m_], x_)
                && iltq!(n_, 0)
                && !integerq!(m_)
                && rubi_polynomial_q(&u__, x_)
                && rubi_polynomial_q(&v_, x_)
                && degrees.is_some_and(|(u_degree, v_degree)| {
                    let minimum_degree = -&n_ * Atom::num(v_degree);
                    geq!(Atom::num(u_degree), minimum_degree)
                })
        },
        rhs: {
            let linear = &a__ + &b__ * x_;
            let divisor = v_.pow(-&n_);
            let (quotient, remainder) =
                polynomial_quotient_remainder(&u__, &divisor, x_)?;
            let first = quotient * linear.pow(&m_);
            let second = remainder * v_.pow(&n_) * linear.pow(&m_);
            rubi_expand_integrand_or_self(&first, x_)
                    + rubi_expand_integrand_or_self(&second, x_)
        },
    ));

    rules.push(rubi_helper_row!(
        order: 26,
        source: "ExpandIntegrand[1/(a_+b_.*u_^n_),x_Symbol]",
        pattern: (a__ + b__ * u__.pow(n_)).pow(-1),
        head: head,
        with: [a__, b__, u__, n_, x_],
        optional: [b__],
        when: {
            let half_n = (&n_ / Atom::num(2)).expand();
            freeq!([a__, b__], x_) && igtq!(half_n, 0)
        },
        rhs: {
            let half_n = (&n_ / Atom::num(2)).expand();
            let rt = rubi_rt(&(-&a__ / &b__), 2);
            let r = rubi_numerator(&rt);
            let s = rubi_denominator_atom(&rt);
            let u_power = u__.pow(half_n);

            &r / (Atom::num(2) * &a__ * (&r - &s * &u_power))
                    + &r / (Atom::num(2) * &a__ * (&r + &s * u_power))
        },
    ));

    rules.push(rubi_helper_row!(
        order: 27,
        source: "ExpandIntegrand[(c_+d_.*u_^n_)/(a_+b_.*u_^n2_),x_Symbol]",
        pattern: (c__ + d__ * u_.pow(n_)) * (a__ + b__ * u_.pow(n2_)).pow(-1),
        head: head,
        with: [c__, d__, u_, n_, a__, b__, n2_, x_],
        optional: [d__, b__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && igtq!(n_, 0)
                && eqq!(n2_, Atom::num(2) * &n_)
        },
        rhs: {
            let rt = rubi_rt(&(-&a__ / &b__), 2);
            let r = rubi_numerator(&rt);
            let s = rubi_denominator_atom(&rt);
            let u_power = u_.pow(n_);

            -&s * (&d__ * &r + &c__ * &s)
                    / (Atom::num(2) * &b__ * &r * (&r - &s * &u_power))
                    + &s * (&d__ * &r - &c__ * &s)
                        / (Atom::num(2) * &b__ * &r * (&r + &s * u_power))
        },
    ));

    rules.push(rubi_helper_row!(
        order: 27,
        source: "ExpandIntegrand[(c_+d_.*u_^n_)/(a_+b_.*u_^n2_),x_Symbol]",
        pattern: d__ * u__.pow(n_) * (a__ + b__ * u__.pow(n2_)).pow(-1),
        head: head,
        with: [d__, u__, n_, a__, b__, n2_, x_],
        optional: [d__, b__],
        when: {
            freeq!([a__, b__, d__], x_)
                && igtq!(n_, 0)
                && eqq!(n2_, Atom::num(2) * &n_)
        },
        rhs: {
            let rt = rubi_rt(&(-&a__ / &b__), 2);
            let r = rubi_numerator(&rt);
            let s = rubi_denominator_atom(&rt);
            let u_power = u__.pow(n_);

            -&s * &d__ * &r / (Atom::num(2) * &b__ * &r * (&r - &s * &u_power))
                    + &s * &d__ * &r
                        / (Atom::num(2) * &b__ * &r * (&r + &s * u_power))
        },
    ));

    rules.push(rubi_helper_row!(
        order: 27,
        source: "ExpandIntegrand[(c_+d_.*u_^n_)/(a_+b_.*u_^n2_),x_Symbol]",
        pattern: d__ * u__ * (a__ + b__ * u__.pow(n2_)).pow(-1),
        head: head,
        with: [d__, u__, a__, b__, n2_, x_],
        optional: [d__, b__],
        when: {
            freeq!([a__, b__, d__], x_)
                && eqq!(n2_, Atom::num(2))
        },
        rhs: {
            let rt = rubi_rt(&(-&a__ / &b__), 2);
            let r = rubi_numerator(&rt);
            let s = rubi_denominator_atom(&rt);

            -&s * &d__ * &r / (Atom::num(2) * &b__ * &r * (&r - &s * &u__))
                    + &s * &d__ * &r / (Atom::num(2) * &b__ * &r * (&r + &s * u__))
        },
    ));

    rules.push(rubi_helper_row!(
        order: 28,
        source: "ExpandIntegrand[(a_+b_.*u_)^m_*(c_.+d_.*u_),x_Symbol]",
        pattern: (a__ + b__ * u__).pow(m_) * (c__ + d__ * u__),
        head: head,
        with: [a__, b__, u__, m_, c__, d__, x_],
        optional: [b__, c__, d__],
        x_dep: [],
        x_free: [a__, b__, c__, d__],
        when: { freeq!([a__, b__, c__, d__], x_) && iltq!(m_, 0) },
        rhs: {
            &d__ / &b__ * (&a__ + &b__ * &u__).pow(&m_ + 1)
                    + (&b__ * &c__ - &a__ * &d__) / &b__
                        * (&a__ + &b__ * u__).pow(m_)
        },
    ));

    rules.push(rubi_helper_row!(
        order: 29,
        source: "ExpandIntegrand[1/(a_+b_.*u_^n_),x_Symbol]",
        pattern: (a__ + b__ * u__.pow(n_)).pow(-1),
        head: head,
        with: [a__, b__, u__, n_, x_],
        optional: [b__],
        when: { freeq!([a__, b__], x_) && igtq!(n_, 1) },
        rhs: {
            let n_integer = integer_i64(&n_)?;
            let rt = rubi_rt(&(-&a__ / &b__), n_integer);
            let r = rubi_numerator(&rt);
            let s = rubi_denominator_atom(&rt);
            let mut sum = Atom::num(0);
            for k in 1..=n_integer {
                let phase = Atom::num(-1).pow(Atom::num(2 * k) / &n_);
                sum += &r / (&a__ * &n_ * (&r - phase * &s * &u__));
            }
            sum
        },
    ));

    rules.push(rubi_helper_row!(
        order: 30,
        source: "ExpandIntegrand[(c_+d_.*u_^m_.)/(a_+b_.*u_^n_),x_Symbol]",
        pattern: (c__ + d__ * u__.pow(m_)) * (a__ + b__ * u__.pow(n_)).pow(-1),
        head: head,
        with: [c__, d__, u__, m_, a__, b__, n_, x_],
        optional: [d__, m_, b__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && integersq!([m_, n_])
                && gtq!(m_, 0)
                && ltq!(m_, n_)
        },
        rhs: {
            let n_integer = integer_i64(&n_)?;
            let rt = rubi_rt(&(-&a__ / &b__), n_integer);
            let r = rubi_numerator(&rt);
            let s = rubi_denominator_atom(&rt);
            let rs_m = (&r / &s).pow(&m_);
            let mut sum = Atom::num(0);
            for k in 1..=n_integer {
                let numerator_phase = Atom::num(-1).pow(Atom::num(-2 * k) * &m_ / &n_);
                let denominator_phase = Atom::num(-1).pow(Atom::num(2 * k) / &n_);
                sum += (&r * &c__ + &r * &d__ * &rs_m * numerator_phase)
                    / (&a__ * &n_ * (&r - denominator_phase * &s * &u__));
            }
            sum
        },
    ));

    rules.push(rubi_helper_row!(
        order: 31,
        source: "ExpandIntegrand[(c_.+d_.*u_^m_.+e_.*u_^p_)/(a_+b_.*u_^n_),x_Symbol]",
        pattern: (c__ + d__ * u__.pow(m_) + e__ * u__.pow(p_))
            * (a__ + b__ * u__.pow(n_)).pow(-1),
        head: head,
        with: [c__, d__, u__, m_, e__, p_, a__, b__, n_, x_],
        optional: [c__, d__, m_, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && integersq!([m_, n_, p_])
                && gtq!(m_, 0)
                && ltq!(m_, p_)
                && ltq!(p_, n_)
        },
        rhs: {
            let n_integer = integer_i64(&n_)?;
            let rt = rubi_rt(&(-&a__ / &b__), n_integer);
            let r = rubi_numerator(&rt);
            let s = rubi_denominator_atom(&rt);
            let rs_m = (&r / &s).pow(&m_);
            let rs_p = (&r / &s).pow(&p_);
            let mut sum = Atom::num(0);
            for k in 1..=n_integer {
                let m_phase = Atom::num(-1).pow(Atom::num(-2 * k) * &m_ / &n_);
                let p_phase = Atom::num(-1).pow(Atom::num(-2 * k) * &p_ / &n_);
                let denominator_phase = Atom::num(-1).pow(Atom::num(2 * k) / &n_);
                sum += (&r * &c__
                    + &r * &d__ * &rs_m * m_phase
                    + &r * &e__ * &rs_p * p_phase)
                    / (&a__ * &n_ * (&r - denominator_phase * &s * &u__));
            }
            sum
        },
    ));

    rules.push(rubi_helper_row!(
        order: 32,
        source: "ExpandIntegrand[(c_.+d_.*u_^m_.+e_.*u_^p_+f_.*u_^q_)/(a_+b_.*u_^n_),x_Symbol]",
        pattern: (c__ + d__ * u__.pow(m_) + e__ * u__.pow(p_) + f__ * u__.pow(q_))
            * (a__ + b__ * u__.pow(n_)).pow(-1),
        head: head,
        with: [c__, d__, u__, m_, e__, p_, f__, q_, a__, b__, n_, x_],
        optional: [c__, d__, m_, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && integersq!([m_, n_, p_, q_])
                && gtq!(m_, 0)
                && ltq!(m_, p_)
                && ltq!(p_, q_)
                && ltq!(q_, n_)
        },
        rhs: {
            let n_integer = integer_i64(&n_)?;
            let rt = rubi_rt(&(-&a__ / &b__), n_integer);
            let r = rubi_numerator(&rt);
            let s = rubi_denominator_atom(&rt);
            let rs_m = (&r / &s).pow(&m_);
            let rs_p = (&r / &s).pow(&p_);
            let rs_q = (&r / &s).pow(&q_);
            let mut sum = Atom::num(0);
            for k in 1..=n_integer {
                let m_phase = Atom::num(-1).pow(Atom::num(-2 * k) * &m_ / &n_);
                let p_phase = Atom::num(-1).pow(Atom::num(-2 * k) * &p_ / &n_);
                let q_phase = Atom::num(-1).pow(Atom::num(-2 * k) * &q_ / &n_);
                let denominator_phase = Atom::num(-1).pow(Atom::num(2 * k) / &n_);
                sum += (&r * &c__
                    + &r * &d__ * &rs_m * m_phase
                    + &r * &e__ * &rs_p * p_phase
                    + &r * &f__ * &rs_q * q_phase)
                    / (&a__ * &n_ * (&r - denominator_phase * &s * &u__));
            }
            sum
        },
    ));

    rules.push(rubi_helper_row!(
        order: 33,
        source: "ExpandIntegrand[(a_+c_.*u_^n_)^p_,x_Symbol]",
        pattern: (a__ + c__ * u__.pow(n_)).pow(p_),
        head: head,
        with: [a__, c__, u__, n_, p_, x_],
        optional: [c__],
        when: {
            let half_n = (&n_ / Atom::num(2)).expand();
            freeq!([a__, c__], x_) && integerq!(half_n) && iltq!(p_, 0)
        },
        rhs: {
            let half_n = (&n_ / Atom::num(2)).expand();
            let temporary_q = Symbol::parse("ExpandIntegrandQ", "ruby").ok()?;
            let temporary_x = Symbol::parse("ExpandIntegrandX", "ruby").ok()?;
            let q_atom = Atom::var(temporary_q);
            let temporary_x_atom = Atom::var(temporary_x);
            let coefficient = Atom::num(1) / c__.pow(&p_);
            let factors = rubi_hold_power(&(-&q_atom + &c__ * &temporary_x_atom), &p_)
                * rubi_hold_power(&(&q_atom + &c__ * temporary_x_atom), &p_);
            let expanded = rubi_expand_integrand_product(&coefficient, &factors, temporary_x);
            let expanded = rubi_replace_all(
                &expanded,
                temporary_q,
                rubi_rt(&(-&a__ * &c__), 2),
            );
            rubi_replace_all(
                &expanded,
                temporary_x,
                u__.pow(half_n),
            )
        },
    ));

    rules.push(rubi_helper_row!(
        order: 34,
        source: "ExpandIntegrand[u_^m_.*(a_.+c_.*u_^n_)^p_,x_Symbol]",
        pattern: u__.pow(m_) * (a__ + c__ * u__.pow(n_)).pow(p_),
        head: head,
        with: [u__, m_, a__, c__, n_, p_, x_],
        optional: [m_, a__, c__],
        when: {
            let half_n = (&n_ / Atom::num(2)).expand();
            freeq!([a__, c__], x_)
                && integersq!([m_, half_n])
                && iltq!(p_, 0)
                && gtq!(m_, 0)
                && ltq!(m_, n_)
                && neq!(m_, half_n)
        },
        rhs: {
            let half_n = (&n_ / Atom::num(2)).expand();
            let q_ = rubi_rt(&(-&a__ * &c__), 2);
            let z = u__.pow(&half_n);
            let first = Atom::num(1) / c__.pow(&p_);
            let second = u__.pow(&m_)
                * (-&q_ + &c__ * &z).pow(&p_)
                * (&q_ + &c__ * z).pow(&p_);
            rubi_expand_integrand_product(&first, &second, x_)
        },
    ));

    rules.push(rubi_helper_row!(
        order: 35,
        source: "ExpandIntegrand[(a_+b_.*x_^n_)^p_,x_Symbol]",
        pattern: (a__ + b__ * u__.pow(n_)).pow(p_),
        head: head,
        with: [a__, b__, u__, n_, p_, x_],
        optional: [b__],
        when: {
            u__ == x_
                && freeq!([a__, b__], x_)
                && igtq!(n_, 1)
                && iltq!(p_, -1)
        },
        rhs: {
            let n_integer = integer_i64(&n_)?;
            let q = rubi_rt(&(-&a__ / &b__), n_integer);
            let factors = (1..=n_integer).fold(Atom::num(1), |product, ii| {
                let phase = Atom::num(-1).pow(Atom::num(2 * ii) / &n_);
                product * (&q - phase * x_).pow(&p_)
            });

            rubi_expand_integrand_product(&(-&b__).pow(&p_), &factors, x_)
        },
    ));

    rules.push(rubi_helper_row!(
        order: 36,
        source: "ExpandIntegrand[(a_.+b_.*u_^n_.+c_.*u_^n2_.)^p_,x_Symbol]",
        pattern: (a__ + b__ * u__.pow(n_) + c__ * u__.pow(n2_)).pow(p_),
        head: head,
        with: [a__, b__, u__, n_, c__, n2_, p_, x_],
        optional: [a__, b__, n_, c__, n2_],
        when: {
            freeq!([a__, b__, c__], x_)
                && integerq!(n_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && iltq!(p_, 0)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
        },
        rhs: {
            let q_ = rubi_rt(&(b__.pow(2) - Atom::num(4) * &a__ * &c__), 2);
            let z = u__.pow(&n_);
            let first = Atom::num(1) / (Atom::num(4).pow(&p_) * c__.pow(&p_));
            let second = (&b__ - &q_ + Atom::num(2) * &c__ * &z).pow(&p_)
                * (&b__ + &q_ + Atom::num(2) * &c__ * z).pow(&p_);
            rubi_expand_integrand_product(&first, &second, x_)
        },
    ));

    rules.push(rubi_helper_row!(
        order: 37,
        source: "ExpandIntegrand[u_^m_.*(a_.+b_.*u_^n_.+c_.*u_^n2_.)^p_,x_Symbol]",
        pattern: u__.pow(m_) * (a__ + b__ * u__.pow(n_) + c__ * u__.pow(n2_)).pow(p_),
        head: head,
        with: [u__, m_, a__, b__, n_, c__, n2_, p_, x_],
        optional: [m_, a__, b__, n_, c__, n2_],
        when: {
            freeq!([a__, b__, c__], x_)
                && integersq!([m_, n_, n2_])
                && eqq!(n2_, Atom::num(2) * &n_)
                && iltq!(p_, 0)
                && gtq!(m_, 0)
                && ltq!(m_, Atom::num(2) * &n_)
                && !(eqq!(m_, n_) && eqq!(p_, -1))
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
        },
        rhs: {
            let q_ = rubi_rt(&(b__.pow(2) - Atom::num(4) * &a__ * &c__), 2);
            let z = u__.pow(&n_);
            let first = Atom::num(1) / (Atom::num(4).pow(&p_) * c__.pow(&p_));
            let second = u__.pow(&m_)
                * (&b__ - &q_ + Atom::num(2) * &c__ * &z).pow(&p_)
                * (&b__ + &q_ + Atom::num(2) * &c__ * z).pow(&p_);
            rubi_expand_integrand_product(&first, &second, x_)
        },
    ));

    rules.push(rubi_helper_row!(
        order: 38,
        source: "ExpandIntegrand[(c_+d_.*u_^n_.)/(a_+b_.*u_^n2_.),x_Symbol]",
        pattern: (c__ + d__ * u_.pow(n_)) * (a__ + b__ * u_.pow(n2_)).pow(-1),
        head: head,
        with: [c__, d__, u_, n_, a__, b__, n2_, x_],
        optional: [d__, n_, b__, n2_],
        x_dep: [],
        x_free: [a__, b__, c__, d__, n_, n2_],
        when: {
            freeq!([a__, b__, c__, d__, n_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
        },
        rhs: {
            let q_ = rubi_rt(&(-&a__ / &b__), 2);
            let u_power = u_.pow(n_);
            -(&c__ - &d__ * &q_) / (Atom::num(2) * &b__ * &q_ * (&q_ + &u_power))
                    - (&c__ + &d__ * &q_)
                        / (Atom::num(2) * &b__ * &q_ * (&q_ - u_power))
        },
    ));

    rules.push(rubi_helper_row!(
        order: 39,
        source: "ExpandIntegrand[(d_.+e_.*(f_.+g_.*u_^n_.))/(a_.+b_.*u_^n_.+c_.*u_^n2_.),x_Symbol]",
        pattern: (f__ + u_) * (Atom::num(1) + u_ + u_.pow(2)).pow(-1),
        head: head,
        with: [f__, u_, x_],
        when: { freeq!(f__, x_) },
        rhs: {
            let q_ = rubi_rt(&-Atom::num(3), 2);
            let r = rubi_together_simplify(&((Atom::num(2) * &f__ - Atom::num(1)) / &q_));
            (Atom::num(1) + &r) / (Atom::num(1) - &q_ + Atom::num(2) * &u_)
                    + (Atom::num(1) - r) / (Atom::num(1) + q_ + Atom::num(2) * u_)
        },
    ));

    rules.push(rubi_helper_row!(
        order: 39,
        source: "ExpandIntegrand[(d_.+e_.*(f_.+g_.*u_^n_.))/(a_.+b_.*u_^n_.+c_.*u_^n2_.),x_Symbol]",
        pattern: (f__ + g__ * u_) * (Atom::num(1) + u_ + u_.pow(2)).pow(-1),
        head: head,
        with: [f__, g__, u_, x_],
        when: { freeq!([f__, g__], x_) },
        rhs: {
            let q_ = rubi_rt(&-Atom::num(3), 2);
            let r = rubi_together_simplify(&((Atom::num(2) * &f__ - &g__) / &q_));
            (&g__ + &r) / (Atom::num(1) - &q_ + Atom::num(2) * &u_)
                    + (&g__ - r) / (Atom::num(1) + q_ + Atom::num(2) * u_)
        },
    ));

    rules.push(rubi_helper_row!(
        order: 39,
        source: "ExpandIntegrand[(d_.+e_.*(f_.+g_.*u_^n_.))/(a_.+b_.*u_^n_.+c_.*u_^n2_.),x_Symbol]",
        pattern: (d__ + e__ * u_.pow(n_))
            * (a__ + b__ * u_.pow(n_) + c__ * u_.pow(n2_)).pow(-1),
        head: head,
        with: [d__, e__, u_, n_, a__, b__, c__, n2_, x_],
        optional: [d__, e__, n_, a__, b__, c__, n2_],
        when: {
            freeq!([a__, b__, c__, d__, e__, n_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
        },
        rhs: {
            let q_ = rubi_rt(&(b__.pow(2) - Atom::num(4) * &a__ * &c__), 2);
            let r = rubi_together_simplify(
                &((Atom::num(2) * &c__ * &d__ - &b__ * &e__) / &q_),
            );
            let u_power = u_.pow(n_);
            (&e__ + &r) / (&b__ - &q_ + Atom::num(2) * &c__ * &u_power)
                    + (&e__ - r)
                        / (&b__ + q_ + Atom::num(2) * &c__ * u_power)
        },
    ));

    rules.push(rubi_helper_row!(
        order: 39,
        source: "ExpandIntegrand[(d_.+e_.*(f_.+g_.*u_^n_.))/(a_.+b_.*u_^n_.+c_.*u_^n2_.),x_Symbol]",
        pattern: (d__ + e__ * (f__ + g__ * u_.pow(n_)))
            * (a__ + b__ * u_.pow(n_) + c__ * u_.pow(n2_)).pow(-1),
        head: head,
        with: [d__, e__, f__, g__, u_, n_, a__, b__, c__, n2_, x_],
        optional: [d__, e__, f__, g__, n_, a__, b__, c__, n2_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, n_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
        },
        rhs: {
            let q_ = rubi_rt(&(b__.pow(2) - Atom::num(4) * &a__ * &c__), 2);
            let r = rubi_together_simplify(
                &((Atom::num(2) * &c__ * (&d__ + &e__ * &f__) - &b__ * &e__ * &g__) / &q_),
            );
            let u_power = u_.pow(n_);
            (&e__ * &g__ + &r) / (&b__ - &q_ + Atom::num(2) * &c__ * &u_power)
                    + (&e__ * &g__ - r)
                        / (&b__ + q_ + Atom::num(2) * &c__ * u_power)
        },
    ));

    rules.push(rubi_helper_row!(
        order: 40,
        source: "ExpandIntegrand[u_/v_,x_Symbol]",
        pattern: u__ * v__.pow(-1),
        head: head,
        with: [u__, v__, x_],
        when: {
            let degrees = rubi_expon(&u__, x_).zip(rubi_expon(&v__, x_));
            rubi_polynomial_q(&u__, x_)
                && rubi_polynomial_q(&v__, x_)
                && degrees.is_some_and(|(u_degree, v_degree)| u_degree >= v_degree)
        },
        rhs: { rubi_polynomial_divide(&u__, &v__, x_)? },
    ));

    rules.push(rubi_helper_row!(
        order: 41,
        source: "ExpandIntegrand[u_*(a_.*x_)^p_,x_Symbol]",
        pattern: u__ * (a__ * x_).pow(p_),
        head: head,
        with: [u__, a__, p_, x_],
        optional: [a__],
        when: {
            !integerq!(p_) && rubi_polynomial_q(&u__, x_)
        },
        rhs: {
            let power = (&a__ * x_).pow(&p_);
            rubi_expand_to_sum_product(&power, &u__, x_)
        },
    ));

    rules.push(rubi_helper_row!(
        order: 42,
        source: "ExpandIntegrand[u_.*v_^p_,x_Symbol]",
        pattern: u__ * v_.pow(p_),
        head: head,
        with: [u__, v_, p_, x_],
        optional: [u__],
        when: { !integerq!(p_) },
        rhs: {
            let normalized_power = rubi_normalize_integrand(&v_.pow(&p_), x_);
            rubi_expand_integrand_product(&normalized_power, &u__, x_)
        },
    ));

    rules.push(rubi_helper_row!(
        order: 43,
        source: "ExpandIntegrand[u_,x_Symbol]",
        pattern: Atom::var(u_),
        head: head,
        with: [u_, x_],
        when: { rubi_sum_q(&rubi_expand_expression(&u_, x_)) },
        rhs: { rubi_expand_expression(&u_, x_) },
    ));

    rules.push(rubi_helper_row!(
        order: 44,
        source: "ExpandIntegrand[u_^m_./(a_+b_.*u_^n_),x_Symbol]",
        pattern: u_.pow(m_) * (a__ + b__ * u_.pow(n_)).pow(-1),
        head: head,
        with: [u_, m_, a__, b__, n_, x_],
        optional: [m_, b__],
        when: {
            freeq!([a__, b__], x_)
                && integersq!([m_, n_])
                && gtq!(m_, 0)
                && ltq!(m_, n_)
        },
        rhs: { rubi_expand_binomial(&a__, &b__, &m_, &n_, &u_, x_)? },
    ));

    rules.push(rubi_helper_row!(
        order: 45,
        source: "ExpandIntegrand[u_,x_Symbol]",
        pattern: Atom::var(u_),
        head: head,
        with: [u_, x_],
        when: { true },
        rhs: { u_ },
    ));
}

fn rubi_expand_binomial(
    a: &Atom,
    b: &Atom,
    m: &Atom,
    n: &Atom,
    u: &Atom,
    _x: Symbol,
) -> Option<Atom> {
    let m = integer_i64(m)?;
    let n = integer_i64(n)?;
    if m <= 0 || n <= m {
        return None;
    }

    let g = integer_gcd(m, n);
    let reduced_n = n / g;
    let positive_root = reduced_n % 2 != 0 && rubi_pos_q(&(a / b));
    let root_argument = if positive_root { a / b } else { -a / b };
    let root = rubi_rt(&root_argument, reduced_n);
    let r = rubi_numerator(&root);
    let s = rubi_denominator_atom(&root);

    if !positive_root && reduced_n == 2 {
        let u_power = u.pow(g);
        return Some(
            &s / (Atom::num(2) * b * (&r + &s * &u_power))
                - &s / (Atom::num(2) * b * (&r - &s * u_power)),
        );
    }

    let coprime = integer_gcd(m + g, n) == 1;
    let ratio_power = if positive_root {
        (-&r / &s).pow(m / g)
    } else {
        (&r / &s).pow(m / g)
    };
    let u_power = u.pow(g);
    let mut sum = Atom::num(0);
    for k in 1..=reduced_n {
        let denominator_phase = Atom::num(-1).pow(Atom::num(2 * k * g) / n);
        let (numerator_phase, denominator) = if coprime {
            (
                Atom::num(-1).pow(Atom::num(-2 * k * m) / n),
                if positive_root {
                    &r + denominator_phase * &s * &u_power
                } else {
                    &r - denominator_phase * &s * &u_power
                },
            )
        } else {
            (
                Atom::num(-1).pow(Atom::num(2 * k * (m + g)) / n),
                if positive_root {
                    denominator_phase * &r + &s * &u_power
                } else {
                    denominator_phase * &r - &s * &u_power
                },
            )
        };
        sum += &r * &ratio_power * numerator_phase / (a * n * denominator);
    }
    Some(sum)
}
