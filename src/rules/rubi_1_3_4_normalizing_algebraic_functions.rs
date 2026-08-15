use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_2003(rules);
    push_rules_rule_2004(rules);
    push_rules_rule_2005(rules);
    push_rules_rule_2006(rules);
    push_rules_rule_2007(rules);
    push_rules_rule_2008(rules);
    push_rules_rule_2026(rules);
    push_rules_rule_2028(rules);
    push_rules_rule_2029(rules);
    push_rules_rule_2030(rules);
    push_rules_rule_2031(rules);
    push_rules_rule_2032(rules);
    push_rules_rule_2033(rules);
    push_rules_rule_2034(rules);
    push_rules_rule_2035(rules);
    push_rules_rule_2042(rules);
    push_rules_rule_2043(rules);
    push_rules_rule_2044(rules);
    push_rules_rule_2045(rules);
    push_rules_rule_2046(rules);
    push_rules_rule_2047(rules);
    push_rules_rule_2048(rules);
    push_rules_rule_2049(rules);
    push_rules_rule_2050(rules);
    push_rules_rule_2051(rules);
    push_rules_rule_2052(rules);
    push_rules_rule_2053(rules);
    push_rules_rule_2054(rules);
    push_rules_rule_2055(rules);
    push_rules_rule_2056(rules);
    push_rules_rule_2057(rules);
    push_rules_rule_2058(rules);
    push_rules_rule_2059(rules);
    push_rules_rule_2060(rules);
    push_rules_rule_2061(rules);
    push_rules_rule_2062(rules);
    push_rules_rule_2063(rules);
    push_rules_rule_2064(rules);
    push_rules_rule_2065(rules);
    push_rules_rule_2066(rules);
    push_rules_rule_2067(rules);
    push_rules_rule_2068(rules);
    push_rules_rule_2069(rules);
    push_rules_rule_2070(rules);
    push_rules_rule_2071(rules);
    push_rules_rule_203(rules);
    push_rules_rule_204(rules);
    push_rules_rule_205(rules);
    push_rules_rule_206(rules);
    push_rules_rule_2072(rules);
    push_rules_rule_2073(rules);
    push_rules_rule_2074(rules);
    push_rules_rule_2075(rules);
    push_rules_rule_2076(rules);
    push_rules_rule_2077(rules);
    push_rules_rule_2451(rules);
    push_rules_rule_2078(rules);
    push_rules_rule_2079(rules);
    push_rules_rule_2080(rules);
    push_rules_rule_2081(rules);
    push_rules_rule_2082(rules);
    push_rules_rule_2083(rules);
    push_rules_rule_2084(rules);
    push_rules_rule_2452(rules);
    push_rules_rule_2453(rules);
    push_rules_rule_2085(rules);
    push_rules_rule_2086(rules);
    push_rules_rule_2087(rules);
    push_rules_rule_2088(rules);
    push_rules_rule_2089(rules);
    push_rules_rule_2090(rules);
    push_rules_rule_2091(rules);
    push_rules_rule_2092(rules);
    push_rules_rule_2454(rules);
    push_rules_rule_2455(rules);
    push_rules_rule_2093(rules);
    push_rules_rule_2094(rules);
    push_rules_rule_2095(rules);
    push_rules_rule_2096(rules);
}

fn push_rules_rule_2003(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, n_, p_, u__, x_);
    rules.push(rubi_rule!(
        order: 2003,
        source: "Int[u_*(c_+d_.*x_)^n_.*(a_+b_.*x_^2)^p_.,x_Symbol] :=
          Int[u*(c+d*x)^(n+p)*(a/c+b/d*x)^p,x] /;
        FreeQ[{a,b,c,d,n,p},x] && EqQ[b*c^2+a*d^2,0] && (IntegerQ[p] || GtQ[a,0] && GtQ[c,0] && Not[IntegerQ[n]])",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern: u__ * (c__ + d__ * x_).pow(n_) * (a__ + b__ * x_.pow(2)).pow(p_),
        with: [u__, c__, d__, n_, a__, b__, p_, x_],
        optional: [d__, n_, b__, p_],
        x_free: [a__, b__, c__, d__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, n_, p_], x_)
                && eqq!(&b__ * c__.pow(2) + &a__ * d__.pow(2), 0)
                && (integerq!(p_)
                    || gtq!(a__, 0) && gtq!(c__, 0) && !integerq!(n_))
        },
        rhs: {
            rubi_rhs_int(
                &(u__
                    * (&c__ + &d__ * x_).pow(&n_ + &p_)
                    * (&a__ / &c__ + &b__ / &d__ * x_).pow(p_)),
                x_,
            )
        },
    ));
}

fn push_rules_rule_2004(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, p_, q_, u__, x_);
    rules.push(rubi_rule!(
        order: 2004,
        source: "Int[u_*(d_+e_.*x_)^q_.*(a_+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
          Int[u*(d+e*x)^(p+q)*(a/d+c/e*x)^p,x] /;
        FreeQ[{a,b,c,d,e,q},x] && EqQ[c*d^2-b*d*e+a*e^2,0] && IntegerQ[p]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern: u__ * (d__ + e__ * x_).pow(q_)
            * (a__ + b__ * x_ + c__ * x_.pow(2)).pow(p_),
        with: [u__, d__, e__, q_, a__, b__, c__, p_, x_],
        optional: [e__, q_, b__, c__, p_],
        x_free: [a__, b__, c__, d__, e__, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__, q_], x_)
                && eqq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && integerq!(p_)
        },
        rhs: {
            rubi_rhs_int(
                &(u__
                    * (&d__ + &e__ * x_).pow(&p_ + &q_)
                    * (&a__ / &d__ + &c__ / &e__ * x_).pow(p_)),
                x_,
            )
        },
    ));
}

fn push_rules_rule_2005(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, fx__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 2005,
        source: "Int[x_^m_.*(a_+b_.*x_^n_)^p_.*Fx_,x_Symbol] :=
          Int[x^(m+n*p)*(b+a*x^(-n))^p*Fx,x] /;
        FreeQ[{a,b,m,n},x] && IntegerQ[p] && NegQ[n]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern: x_.pow(m_) * (a__ + b__ * x_.pow(n_)).pow(p_) * fx__,
        with: [m_, a__, b__, n_, p_, fx__, x_],
        optional: [m_, b__, p_],
        x_free: [a__, b__, m_, n_],
        when: {
            freeq!([a__, b__, m_, n_], x_) && integerq!(p_) && negq!(n_)
        },
        rhs: {
            rubi_rhs_int(
                &(x_.pow(&m_ + &n_ * &p_)
                    * (&b__ + &a__ * x_.pow(-&n_)).pow(p_)
                    * fx__),
                x_,
            )
        },
    ));
}

fn push_rules_rule_2006(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; px_, u__);
    rules.push(rubi_rule!(
        order: 2006,
        source: "Int[u_.*Px_,x_Symbol] :=
          With[{a=Rt[Coeff[Px,x,0],Expon[Px,x]],b=Rt[Coeff[Px,x,Expon[Px,x]],Expon[Px,x]]},
          Int[u*(a+b*x)^Expon[Px,x],x] /;
         EqQ[Px,(a+b*x)^Expon[Px,x]]] /;
        PolyQ[Px,x] && GtQ[Expon[Px,x],1] && NeQ[Coeff[Px,x,0],0] && Not[MatchQ[Px,a_.*v_^Expon[Px,x] /; FreeQ[a,x] && LinearQ[v,x]]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_12(symbols),
        with: [u__, px_, x_],
        optional: [u__],
        when: {
            rubi_perfect_affine_power(&px_, x_).is_some_and(|parts| {
                !rubi_int_term_linear_power(&px_, x_).is_some_and(
                    |(coefficient, _, exponent)| {
                        is_free_of(&coefficient, x_) && eqq!(exponent, parts.degree)
                    },
                )
            })
        },
        rhs: {
            let parts = rubi_perfect_affine_power(&px_, x_)
                .expect("Rubi DownValue 2006 condition validates the affine power");
            rubi_rhs_int(&(u__ * parts.power), x_)
        },
    ));
}

fn push_rules_rule_2007(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; p_, px_, u__);
    rules.push(rubi_rule!(
        order: 2007,
        source: "Int[u_.*Px_^p_,x_Symbol] :=
          With[{a=Rt[Coeff[Px,x,0],Expon[Px,x]],b=Rt[Coeff[Px,x,Expon[Px,x]],Expon[Px,x]]},
          Int[u*(a+b*x)^(Expon[Px,x]*p),x] /;
         EqQ[Px,(a+b*x)^Expon[Px,x]]] /;
        IntegerQ[p] && PolyQ[Px,x] && GtQ[Expon[Px,x],1] && NeQ[Coeff[Px,x,0],0]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_13(symbols),
        with: [u__, px_, p_, x_],
        optional: [u__],
        x_free: [p_],
        when: {
            integerq!(p_)
                && rubi_perfect_affine_power(&px_, x_).is_some()
        },
        rhs: {
            let parts = rubi_perfect_affine_power(&px_, x_)
                .expect("Rubi DownValue 2007 condition validates the affine power");
            rubi_rhs_int(
                &(u__ * (&parts.a + &parts.b * x_).pow(Atom::num(parts.degree) * p_)),
                x_,
            )
        },
    ));
}

fn push_rules_rule_2008(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; p_, px_, u__);
    rules.push(rubi_rule!(
        order: 2008,
        source: "Int[u_.*Px_^p_,x_Symbol] :=
          With[{a=Rt[Coeff[Px,x,0],Expon[Px,x]],b=Rt[Coeff[Px,x,Expon[Px,x]],Expon[Px,x]]},
          ((a+b*x)^Expon[Px,x])^p/(a+b*x)^(Expon[Px,x]*p) \\[Star] Int[u*(a+b*x)^(Expon[Px,x]*p),x] /;
         EqQ[Px,(a+b*x)^Expon[Px,x]]] /;
        Not[IntegerQ[p]] && PolyQ[Px,x] && GtQ[Expon[Px,x],1] && NeQ[Coeff[Px,x,0],0]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_13(symbols),
        with: [u__, px_, p_, x_],
        optional: [u__],
        x_free: [p_],
        when: {
            !integerq!(p_)
                && rubi_perfect_affine_power(&px_, x_).is_some()
        },
        rhs: {
            let parts = rubi_perfect_affine_power(&px_, x_)
                .expect("Rubi DownValue 2008 condition validates the affine power");
            let affine = &parts.a + &parts.b * x_;
            let recursive = rubi_rhs_int(
                &(u__ * affine.pow(Atom::num(parts.degree) * &p_)),
                x_,
            );
            rubi_star(
                parts.power.pow(&p_)
                    / (&parts.a + &parts.b * x_).pow(Atom::num(parts.degree) * p_),
                recursive,
            )
        },
    ));
}

fn push_rules_rule_2026(rules: &mut Vec<RubiRule>) {
    rubi_symb!(fx__, p_, px_);
    rules.push(rubi_rule!(
        order: 2026,
        source: "Int[Px_^p_.*Fx_.,x_Symbol] :=
          With[{r=Expon[Px,x,Min]},
          Int[x^(p*r)*ExpandToSum[Px/x^r,x]^p*Fx,x] /;
         IGtQ[r,0]] /;
        PolyQ[Px,x] && IntegerQ[p] && Not[MonomialQ[Px,x]] && (ILtQ[p,0] || Not[PolyQ[u,x]])",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern: px_.pow(p_) * fx__,
        with: [px_, p_, fx__, x_],
        optional: [p_, fx__],
        x_free: [p_],
        when: {
            rubi_poly_q(&px_, x_)
                && integerq!(p_)
                && !rubi_monomial_q(&px_, x_)
                && (iltq!(p_, 0) || !rubi_poly_q(&Atom::var(symbol!("u")), x_))
                && rubi_polynomial_terms(&px_, x_)
                    .and_then(|terms| terms.keys().next().copied())
                    .is_some_and(|r| r > 0)
        },
        rhs: {
            let r = rubi_polynomial_terms(&px_, x_)
                .rubi_rhs()
                .keys()
                .next()
                .copied()
                .rubi_rhs();
            rubi_rhs_int(
                &(x_.pow(&p_ * r)
                    * rubi_expand_to_sum(&(&px_ / x_.pow(r)), x_).pow(p_)
                    * fx__),
                x_,
            )
        },
    ));
}

fn push_rules_rule_2028(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, fx__, p_, r_, s_, t_, x_);
    rules.push(rubi_rule!(
        order: 2028,
        source: "Int[(a_.*x_^r_.+b_.*x_^s_.+c_.*x_^t_.)^p_.*Fx_.,x_Symbol] :=
          Int[x^(p*r)*(a+b*x^(s-r)+c*x^(t-r))^p*Fx,x] /;
        FreeQ[{a,b,c,r,s,t},x] && IntegerQ[p] && PosQ[s-r] && PosQ[t-r] && Not[EqQ[p,1] && EqQ[u,1]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern: (a__ * x_.pow(r_) + b__ * x_.pow(s_) + c__ * x_.pow(t_)).pow(p_) * fx__,
        with: [a__, r_, b__, s_, c__, t_, p_, fx__, x_],
        optional: [a__, r_, b__, s_, c__, t_, p_, fx__],
        x_free: [a__, b__, c__, r_, s_, t_],
        when: {
            freeq!([a__, b__, c__, r_, s_, t_], x_)
                && integerq!(p_)
                && posq!(&s_ - &r_)
                && posq!(&t_ - &r_)
        },
        rhs: {
            rubi_rhs_int(
                &(x_.pow(&p_ * &r_)
                    * (&a__
                        + &b__ * x_.pow(&s_ - &r_)
                        + &c__ * x_.pow(&t_ - &r_))
                        .pow(p_)
                    * fx__),
                x_,
            )
        },
    ));
}

fn push_rules_rule_2029(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, fx__, p_, q_, r_, s_, t_, x_);
    rules.push(rubi_rule!(
        order: 2029,
        source: "Int[(a_.*x_^r_.+b_.*x_^s_.+c_.*x_^t_.+d_.*x_^q_.)^p_.*Fx_.,x_Symbol] :=
          Int[x^(p*r)*(a+b*x^(s-r)+c*x^(t-r)+d*x^(q-r))^p*Fx,x] /;
        FreeQ[{a,b,c,d,r,s,t,q},x] && IntegerQ[p] && PosQ[s-r] && PosQ[t-r] && PosQ[q-r] && Not[EqQ[p,1] && EqQ[u,1]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern: (a__ * x_.pow(r_) + b__ * x_.pow(s_) + c__ * x_.pow(t_) + d__ * x_.pow(q_)).pow(p_) * fx__,
        with: [a__, r_, b__, s_, c__, t_, d__, q_, p_, fx__, x_],
        optional: [a__, r_, b__, s_, c__, t_, d__, q_, p_, fx__],
        x_free: [a__, b__, c__, d__, r_, s_, t_, q_],
        when: {
            freeq!([a__, b__, c__, d__, r_, s_, t_, q_], x_)
                && integerq!(p_)
                && posq!(&s_ - &r_)
                && posq!(&t_ - &r_)
                && posq!(&q_ - &r_)
        },
        rhs: {
            rubi_rhs_int(
                &(x_.pow(&p_ * &r_)
                    * (&a__
                        + &b__ * x_.pow(&s_ - &r_)
                        + &c__ * x_.pow(&t_ - &r_)
                        + &d__ * x_.pow(&q_ - &r_))
                        .pow(p_)
                    * fx__),
                x_,
            )
        },
    ));
}

fn push_rules_rule_2030(rules: &mut Vec<RubiRule>) {
    rubi_symb!(b__, fx__, m_, n_, v__);
    rules.push(rubi_rule!(
        order: 2030,
        source: "Int[v_^m_.*(b_*v_)^n_*Fx_.,x_Symbol] :=
          1/b^m \\[Star] Int[(b*v)^(m+n)*Fx,x] /;
        FreeQ[{b,n},x] && IntegerQ[m]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern: v__.pow(m_) * (b__ * v__).pow(n_) * fx__,
        with: [v__, m_, b__, n_, fx__, x_],
        optional: [m_, fx__],
        x_free: [b__, n_],
        when: { freeq!([b__, n_], x_) && integerq!(m_) },
        rhs: {
            rubi_star(Atom::num(1) / b__.pow(&m_), rubi_rhs_int(&((&b__ * &v__).pow(&m_ + &n_) * fx__), x_))
        },
    ));
}

fn push_rules_rule_2035(rules: &mut Vec<RubiRule>) {
    rubi_symb!(fx__, m_, x_);
    rules.push(rubi_rule!(
        order: 2035,
        source: "Int[x_^m_*Fx_,x_Symbol] :=
          With[{k=Denominator[m]},
          k \\[Star] Subst[Int[x^(k*(m+1)-1)*SubstPower[Fx,x,k],x],x,x^(1/k)]] /;
        FractionQ[m] && AlgebraicFunctionQ[Fx,x]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern: x_.pow(m_) * fx__,
        with: [m_, fx__, x_],
        x_free: [m_],
        when: { fractionq!(m_) && rubi_algebraic_function_q(&fx__, x_, false) },
        rhs: {
            let k = rational_number(&m_).rubi_rhs().1;
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let transformed_fx = rubi_replace_all(
                &rubi_subst_power(&fx__, x_, k),
                x_,
                Atom::var(sub),
            );
            let transformed = Atom::var(sub)
                .pow(Atom::num(k) * (&m_ + Atom::num(1)) - Atom::num(1))
                * transformed_fx;
            let substituted = rubi_subst(
                &rubi_rhs_int(&transformed, sub),
                sub,
                x_.pow(Atom::num(1) / Atom::num(k)),
            );
            rubi_star(Atom::num(k), substituted)
        },
    ));
}

fn push_rules_rule_2031(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, fx__, m_, n_, v__);
    rules.push(rubi_rule!(
        order: 2031,
        source: "Int[(a_.*v_)^m_*(b_.*v_)^n_*Fx_.,x_Symbol] :=
          a^(m+1/2)*b^(n-1/2)*Sqrt[b*v]/Sqrt[a*v] \\[Star] Int[v^(m+n)*Fx,x] /;
        FreeQ[{a,b,m},x] && Not[IntegerQ[m]] && IGtQ[n+1/2,0] && IntegerQ[m+n]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [fx__, a__, v__, m_, b__, n_, x_],
        optional: [fx__, a__, b__],
        noninteger_power_factors: 1,
        when: {
            freeq!([a__, b__, m_], x_)
                && !integerq!(m_)
                && igtq!(&n_ + Atom::num(1) / 2, 0)
                && integerq!(&m_ + &n_)
        },
        rhs: {
            let recursive_integrand = v__.pow(&m_ + &n_) * &fx__;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let multiplier = a__.pow(&m_ + Atom::num(1) / 2)
                * b__.pow(&n_ - Atom::num(1) / 2)
                * (&b__ * &v__).sqrt()
                / (&a__ * &v__).sqrt();

            rubi_star(multiplier, recursive)
        },
    ));
}

fn push_rules_rule_2032(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, fx__, m_, n_, v__);
    rules.push(rubi_rule!(
        order: 2032,
        source: "Int[(a_.*v_)^m_*(b_.*v_)^n_*Fx_.,x_Symbol] :=
          a^(m-1/2)*b^(n+1/2)*Sqrt[a*v]/Sqrt[b*v] \\[Star] Int[v^(m+n)*Fx,x] /;
        FreeQ[{a,b,m},x] && Not[IntegerQ[m]] && ILtQ[n-1/2,0] && IntegerQ[m+n]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [fx__, a__, v__, m_, b__, n_, x_],
        optional: [fx__, a__, b__],
        noninteger_power_factors: 1,
        when: {
            freeq!([a__, b__, m_], x_)
                && !integerq!(m_)
                && iltq!(&n_ - Atom::num(1) / 2, 0)
                && integerq!(&m_ + &n_)
        },
        rhs: {
            let recursive_integrand = v__.pow(&m_ + &n_) * &fx__;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let multiplier = a__.pow(&m_ - Atom::num(1) / 2)
                * b__.pow(&n_ + Atom::num(1) / 2)
                * (&a__ * &v__).sqrt()
                / (&b__ * &v__).sqrt();

            rubi_star(multiplier, recursive)
        },
    ));
}

fn push_rules_rule_2033(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, fx__, m_, n_, v__);
    rules.push(rubi_rule!(
        order: 2033,
        source: "Int[(a_.*v_)^m_*(b_.*v_)^n_*Fx_.,x_Symbol] :=
          a^(m+n)*(b*v)^n/(a*v)^n \\[Star] Int[v^(m+n)*Fx,x] /;
        FreeQ[{a,b,m,n},x] && Not[IntegerQ[m]] && Not[IntegerQ[n]] && IntegerQ[m+n]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [fx__, a__, v__, m_, b__, n_, x_],
        optional: [fx__, a__, b__],
        noninteger_power_factors: 2,
        when: {
            freeq!([a__, b__, m_, n_], x_)
                && !integerq!(m_)
                && !integerq!(n_)
                && integerq!(&m_ + &n_)
        },
        rhs: {
            let recursive_integrand = v__.pow(&m_ + &n_) * &fx__;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let multiplier = a__.pow(&m_ + &n_) * (&b__ * &v__).pow(&n_)
                / (&a__ * &v__).pow(&n_);

            rubi_star(multiplier, recursive)
        },
    ));
}

fn push_rules_rule_2034(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, fx__, m_, n_, v__);
    rules.push(rubi_rule!(
        order: 2034,
        source: "Int[(a_.*v_)^m_*(b_.*v_)^n_*Fx_.,x_Symbol] :=
          b^IntPart[n]*(b*v)^FracPart[n]/(a^IntPart[n]*(a*v)^FracPart[n]) \\[Star] Int[(a*v)^(m+n)*Fx,x] /;
        FreeQ[{a,b,m,n},x] && Not[IntegerQ[m]] && Not[IntegerQ[n]] && Not[IntegerQ[m+n]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [fx__, a__, v__, m_, b__, n_, x_],
        optional: [fx__, a__, b__],
        noninteger_power_factors: 2,
        when: {
            freeq!([a__, b__, m_, n_], x_)
                && !integerq!(m_)
                && !integerq!(n_)
                && !integerq!(&m_ + &n_)
        },
        rhs: {
            let int_n = rubi_int_part(&n_);
            let frac_n = rubi_frac_part(&n_);
            let recursive_integrand = (&a__ * &v__).pow(&m_ + &n_) * &fx__;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let multiplier = b__.pow(&int_n) * (&b__ * &v__).pow(&frac_n)
                / (a__.pow(&int_n) * (&a__ * &v__).pow(&frac_n));

            rubi_star(multiplier, recursive)
        },
    ));
}

fn push_rules_rule_2042(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d_, p_, q_, u__, x_);
    rules.push(rubi_rule!(
        order: 2042,
        source: "Int[u_.*(c_.*(d_*(a_.+b_.* x_))^q_)^p_,x_Symbol] :=
          (c*(d*(a+b*x))^q)^p/(a+b*x)^(p*q) \\[Star] Int[u*(a+b*x)^(p*q),x] /;
        FreeQ[{a,b,c,d,q,p},x] && Not[IntegerQ[q]] && Not[IntegerQ[p]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: u__ * (c__ * (d_ * (a__ + b__ * x_)).pow(q_)).pow(p_),
        with: [u__, c__, d_, a__, b__, q_, p_, x_],
        optional: [u__, c__, a__, b__],
        when: {
            freeq!([a__, b__, c__, d_, q_, p_], x_) && !integerq!(q_) && !integerq!(p_)
        },
        rhs: {
            let affine = &a__ + &b__ * x_;
            let denominator = affine.pow(&p_ * &q_);
            if denominator.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let coefficient = (&c__ * (&d_ * &affine).pow(&q_)).pow(&p_) / denominator;
            let recursive_integrand = &u__ * affine.pow(&p_ * &q_);

            rubi_star(coefficient, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_2043(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, n_, p_, q_, u__, x_);
    rules.push(rubi_rule!(
        order: 2043,
        source: "Int[u_.*(c_.*(d_.*(a_.+b_.* x_)^n_)^q_)^p_,x_Symbol] :=
          (c*(d*(a+b*x)^n)^q)^p/(a+b*x)^(n*p*q) \\[Star] Int[u*(a+b*x)^(n*p*q),x] /;
        FreeQ[{a,b,c,d,n,q,p},x] && Not[IntegerQ[q]] && Not[IntegerQ[p]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: u__ * (c__ * (d__ * (a__ + b__ * x_).pow(n_)).pow(q_)).pow(p_),
        with: [u__, c__, d__, a__, b__, n_, q_, p_, x_],
        optional: [u__, c__, d__, a__, b__],
        when: {
            freeq!([a__, b__, c__, d__, n_, q_, p_], x_) && !integerq!(q_) && !integerq!(p_)
        },
        rhs: {
            let affine = &a__ + &b__ * x_;
            let denominator = affine.pow(&n_ * &p_ * &q_);
            if denominator.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let coefficient = (&c__ * (&d__ * affine.pow(&n_)).pow(&q_)).pow(&p_) / denominator;
            let recursive_integrand = &u__ * affine.pow(&n_ * &p_ * &q_);

            rubi_star(coefficient, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_2044(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, n_, p_, q_, u__, x_);
    rules.push(rubi_rule!(
        order: 2044,
        source: "Int[u_.*(c_.*(a_.+b_.*x_^n_.)^q_)^p_,x_Symbol] :=
          Simp[(c*(a+b*x^n)^q)^p/(a+b*x^n)^(p*q)] \\[Star] Int[u*(a+b*x^n)^(p*q),x] /;
        FreeQ[{a,b,c,n,p,q},x] && GeQ[a,0]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: u__ * (c__ * (a__ + b__ * x_.pow(n_)).pow(q_)).pow(p_),
        with: [u__, c__, a__, b__, n_, q_, p_, x_],
        optional: [u__, c__, a__, b__, n_],
        x_free: [a__, b__, c__, n_, p_, q_],
        when: { freeq!([a__, b__, c__, n_, p_, q_], x_) && geq!(a__, 0) },
        rhs: {
            let base = &a__ + &b__ * x_.pow(&n_);
            let denominator = base.pow(&p_ * &q_);
            if denominator.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let coefficient = rubi_simp(&((&c__ * base.pow(&q_)).pow(&p_) / denominator), x_);
            let recursive_integrand = &u__ * base.pow(&p_ * &q_);

            rubi_star(coefficient, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_2045(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a_, b__, c__, n_, p_, q_, u__, x_);
    rules.push(rubi_rule!(
        order: 2045,
        source: "Int[u_.*(c_.*(a_+b_.*x_^n_.)^q_)^p_,x_Symbol] :=
          Simp[(c*(a+b*x^n)^q)^p/(1+b*x^n/a)^(p*q)] \\[Star] Int[u*(1+b*x^n/a)^(p*q),x] /;
        FreeQ[{a,b,c,n,p,q},x] && Not[GeQ[a,0]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: u__ * (c__ * (a_ + b__ * x_.pow(n_)).pow(q_)).pow(p_),
        with: [u__, c__, a_, b__, n_, q_, p_, x_],
        optional: [u__, c__, b__, n_],
        when: { freeq!([a_, b__, c__, n_, p_, q_], x_) && !geq!(a_, 0) },
        rhs: {
            if a_.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let normalized = Atom::num(1) + &b__ * x_.pow(&n_) / &a_;
            let denominator = normalized.pow(&p_ * &q_);
            if denominator.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let coefficient =
                rubi_simp(&((&c__ * (&a_ + &b__ * x_.pow(&n_)).pow(&q_)).pow(&p_) / denominator), x_);
            let recursive_integrand = &u__ * normalized.pow(&p_ * &q_);

            rubi_star(coefficient, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_2046(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c_, d__, e__, n_, p_, q_, u__, x_);
    rules.push(rubi_rule!(
        order: 2046,
        source: "Int[u_.*(e_.*(a_.+b_.*x_^n_.)^q_.*(c_+d_.*x_^n_.)^q_.)^p_,x_Symbol] :=
          Int[u*(e*(d/b)^q*(a+b*x^n)^(2*q))^p,x] /;
        FreeQ[{a,b,c,d,e,n,p},x] && IntegerQ[q] && EqQ[b*c-a*d,0]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_10(symbols),
        with: [u__, e__, a__, b__, n_, q_, c_, d__, p_, x_],
        optional: [u__, e__, a__, b__, n_, q_, d__],
        when: {
            freeq!([a__, b__, c_, d__, e__, n_, p_], x_)
                && integerq!(q_)
                && eqq!(&b__ * &c_ - &a__ * &d__, 0)
        },
        rhs: {
            if b__.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let recursive_integrand =
                &u__ * (&e__ * (&d__ / &b__).pow(&q_) * (&a__ + &b__ * x_.pow(&n_)).pow(Atom::num(2) * &q_)).pow(&p_);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_2047(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c_, d__, e__, n_, p_, q_, u__, x_);
    rules.push(rubi_rule!(
        order: 2047,
        source: "Int[u_.*(e_.*(a_.+b_.*x_^n_.)^q_*(c_+d_.*x_^n_.)^q_)^p_,x_Symbol] :=
          Int[u*(e*(-a^2*d/b+b*d*x^(2*n))^q)^p,x] /;
        FreeQ[{a,b,c,d,e,n,p},x] && IntegerQ[q] && EqQ[b*c+a*d,0]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_10(symbols),
        with: [u__, e__, a__, b__, n_, q_, c_, d__, p_, x_],
        optional: [u__, e__, a__, b__, n_, d__],
        when: {
            freeq!([a__, b__, c_, d__, e__, n_, p_], x_)
                && integerq!(q_)
                && eqq!(&b__ * &c_ + &a__ * &d__, 0)
        },
        rhs: {
            if b__.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let recursive_integrand = &u__
                * (&e__ * (-a__.pow(2) * &d__ / &b__ + &b__ * &d__ * x_.pow(Atom::num(2) * &n_)).pow(&q_)).pow(&p_);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_2048(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c_, d__, e__, n_, p_, u__, x_);
    rules.push(rubi_rule!(
        order: 2048,
        source: "Int[u_.*(e_.*(a_.+b_.*x_^n_.)*(c_+d_.*x_^n_.))^p_,x_Symbol] :=
          Int[u*(a*c*e+(b*c+a*d)*e*x^n+b*d*e*x^(2*n))^p,x] /;
        FreeQ[{a,b,c,d,e,n,p},x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: u__ * (e__ * (a__ + b__ * x_.pow(n_)) * (c_ + d__ * x_.pow(n_))).pow(p_),
        with: [u__, e__, a__, b__, n_, c_, d__, p_, x_],
        optional: [u__, e__, a__, b__, n_, d__],
        when: { freeq!([a__, b__, c_, d__, e__, n_, p_], x_) },
        rhs: {
            let normalized = &a__ * &c_ * &e__
                + (&b__ * &c_ + &a__ * &d__) * &e__ * x_.pow(&n_)
                + &b__ * &d__ * &e__ * x_.pow(Atom::num(2) * &n_);
            let recursive_integrand = &u__ * normalized.pow(&p_);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_2049(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c_, d__, e__, n_, p_, u__, x_);
    rules.push(rubi_rule!(
        order: 2049,
        source: "Int[u_.*(e_.*(a_.+b_.*x_^n_.)/(c_+d_.*x_^n_.))^p_,x_Symbol] :=
          (b*e/d)^p \\[Star] Int[u,x] /;
        FreeQ[{a,b,c,d,e,n,p},x] && EqQ[b*c-a*d,0]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_11(symbols),
        with: [u__, e__, a__, b__, n_, c_, d__, p_, x_],
        optional: [u__, e__, a__, b__, n_, d__],
        when: {
            freeq!([a__, b__, c_, d__, e__, n_, p_], x_)
                && eqq!(&b__ * &c_ - &a__ * &d__, 0)
        },
        rhs: {
            if d__.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            rubi_star((&b__ * &e__ / &d__).pow(&p_), rubi_rhs_int(&u__, x_))
        },
    ));
}

fn push_rules_rule_2050(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c_, d__, e__, n_, p_, u__, x_);
    rules.push(rubi_rule!(
        order: 2050,
        source: "Int[u_.*(e_.*(a_.+b_.*x_^n_.)/(c_+d_.*x_^n_.))^p_,x_Symbol] :=
          Int[u*(a*e+b*e*x^n)^p/(c+d*x^n)^p,x] /;
        FreeQ[{a,b,c,d,e,n,p},x] && GtQ[b*d*e,0] && GtQ[c-a*d/b,0]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_11(symbols),
        with: [u__, e__, a__, b__, n_, c_, d__, p_, x_],
        optional: [u__, e__, a__, b__, n_, d__],
        when: {
            freeq!([a__, b__, c_, d__, e__, n_, p_], x_)
                && !b__.is_zero()
                && gtq!(&b__ * &d__ * &e__, 0)
                && gtq!(&c_ - &a__ * &d__ / &b__, 0)
        },
        rhs: {
            let recursive_integrand =
                &u__ * (&a__ * &e__ + &b__ * &e__ * x_.pow(&n_)).pow(&p_) / (&c_ + &d__ * x_.pow(&n_)).pow(&p_);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_2051(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 2051,
        source: "Int[(e_.*(a_.+b_.*x_^n_.)/(c_+d_.*x_^n_.))^p_,x_Symbol] :=
          With[{q=Denominator[p]},
          q*e*(b*c-a*d)/n \\[Star] Subst[
            Int[x^(q*(p+1)-1)*(-a*e+c*x^q)^(1/n-1)/(b*e-d*x^q)^(1/n+1),x],x,(e*(a+b*x^n)/(c+d*x^n))^(1/q)]] /;
        FreeQ[{a,b,c,d,e},x] && FractionQ[p] && IntegerQ[1/n]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern: (e__ * (a__ + b__ * x_.pow(n_)) / (c__ + d__ * x_.pow(n_))).pow(p_),
        with: [e__, a__, b__, n_, c__, d__, p_, x_],
        optional: [e__, a__, b__, n_, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && fractionq!(p_)
                && !n_.is_zero()
                && integerq!(Atom::num(1) / &n_)
        },
        rhs: {
            if n_.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let q_i = rubi_denominator(&p_).rubi_rhs();
            let q = Atom::num(q_i);
            if q.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_denominator = &b__ * &e__ - &d__ * sub_atom.pow(&q);
            if transformed_denominator.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let transformed_integrand = sub_atom.pow(&q * (&p_ + 1) - 1)
                * (-&a__ * &e__ + &c__ * sub_atom.pow(&q)).pow(Atom::num(1) / &n_ - 1)
                / transformed_denominator.pow(Atom::num(1) / &n_ + 1);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);

            let replacement_denominator = &c__ + &d__ * x_.pow(&n_);
            if replacement_denominator.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let replacement =
                (&e__ * (&a__ + &b__ * x_.pow(&n_)) / replacement_denominator).pow(Atom::num(1) / &q);

            rubi_star(&q * &e__ * (&b__ * &c__ - &a__ * &d__) / &n_, rubi_subst(&transformed, sub, replacement))
        },
    ));
}

fn push_rules_rule_2052(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 2052,
        source: "Int[x_^m_.*(e_.*(a_.+b_.*x_)/(c_+d_.*x_))^p_,x_Symbol] :=
          With[{q=Denominator[p]},
          q*e*(b*c-a*d) \\[Star] Subst[Int[x^(q*(p+1)-1)*(-a*e+c*x^q)^m/(b*e-d*x^q)^(m+2),x],x,(e*(a+b*x)/(c+d*x))^(1/q)]] /;
        FreeQ[{a,b,c,d,e,m},x] && FractionQ[p] && IntegerQ[m]",
        desc: "Integration by substitution",
        refs: [],
        pattern: x_.pow(m_) * (e__ * (a__ + b__ * x_) / (c__ + d__ * x_)).pow(p_),
        with: [m_, e__, a__, b__, c__, d__, p_, x_],
        optional: [e__, a__, b__, d__, m_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_], x_)
                && fractionq!(p_)
                && integerq!(m_)
        },
        rhs: {
            let q_i = rubi_denominator(&p_).rubi_rhs();
            let q = Atom::num(q_i);
            if q.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_denominator = &b__ * &e__ - &d__ * sub_atom.pow(&q);
            if transformed_denominator.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let transformed_integrand = sub_atom.pow(&q * (&p_ + 1) - 1)
                * (-&a__ * &e__ + &c__ * sub_atom.pow(&q)).pow(&m_)
                / transformed_denominator.pow(&m_ + 2);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);

            let replacement_denominator = &c__ + &d__ * x_;
            if replacement_denominator.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let replacement = (&e__ * (&a__ + &b__ * x_) / replacement_denominator).pow(Atom::num(1) / &q);

            rubi_star(&q * &e__ * (&b__ * &c__ - &a__ * &d__), rubi_subst(&transformed, sub, replacement))
        },
    ));
}

fn push_rules_rule_2053(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 2053,
        source: "Int[x_^m_.*(e_.*(a_.+b_.*x_^n_.)/(c_+d_.*x_^n_.))^p_,x_Symbol] :=
          1/n \\[Star] Subst[Int[x^(Simplify[(m+1)/n]-1)*(e*(a+b*x)/(c+d*x))^p,x],x,x^n] /;
        FreeQ[{a,b,c,d,e,m,n,p},x] && IntegerQ[Simplify[(m+1)/n]]",
        desc: "Integration by substitution",
        refs: [],
        pattern: x_.pow(m_) * (e__ * (a__ + b__ * x_.pow(n_)) / (c__ + d__ * x_.pow(n_))).pow(p_),
        with: [m_, e__, a__, b__, n_, c__, d__, p_, x_],
        optional: [e__, a__, b__, n_, d__, m_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_, p_], x_)
                && !n_.is_zero()
                && integerq!(rubi_simplify(&((&m_ + 1) / &n_)))
        },
        rhs: {
            if n_.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_denominator = &c__ + &d__ * &sub_atom;
            if transformed_denominator.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let transformed_integrand = sub_atom.pow(rubi_simplify(&((&m_ + 1) / &n_)) - 1)
                * (&e__ * (&a__ + &b__ * &sub_atom) / transformed_denominator).pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);

            rubi_star(Atom::num(1) / &n_, rubi_subst(&transformed, sub, x_.pow(&n_)))
        },
    ));
}

fn push_rules_rule_2054(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 2054,
        source: "Int[(f_*x_)^m_*(e_.*(a_.+b_.*x_^n_.)/(c_+d_.*x_^n_.))^p_,x_Symbol] :=
          Simp[(c*x)^m/x^m] \\[Star] Int[x^m*(e*(a+b*x^n)/(c+d*x^n))^p,x] /;
        FreeQ[{a,b,c,d,e,f,m,n,p},x] && IntegerQ[Simplify[(m+1)/n]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: (f__ * x_).pow(m_) * (e__ * (a__ + b__ * x_.pow(n_)) / (c__ + d__ * x_.pow(n_))).pow(p_),
        with: [f__, m_, e__, a__, b__, n_, c__, d__, p_, x_],
        optional: [e__, a__, b__, n_, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_, p_], x_)
                && !n_.is_zero()
                && integerq!(rubi_simplify(&((&m_ + 1) / &n_)))
        },
        rhs: {
            let recursive_denominator = &c__ + &d__ * x_.pow(&n_);
            if recursive_denominator.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let coefficient = rubi_simp(&(((&c__ * x_).pow(&m_)) / x_.pow(&m_)), x_);
            let recursive_integrand =
                x_.pow(&m_) * (&e__ * (&a__ + &b__ * x_.pow(&n_)) / recursive_denominator).pow(&p_);

            rubi_star(coefficient, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_2055(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, n_, p_, r_, u_, x_);
    rules.push(rubi_rule!(
        order: 2055,
        source: "Int[u_^r_.*(e_.*(a_.+b_.*x_^n_.)/(c_+d_.*x_^n_.))^p_,x_Symbol] :=
          With[{q=Denominator[p]},
          q*e*(b*c-a*d)/n \\[Star] Subst[Int[SimplifyIntegrand[x^(q*(p+1)-1)*(-a*e+c*x^q)^(1/n-1)/(b*e-d*x^q)^(1/n+1)*
            ReplaceAll[u,x->(-a*e+c*x^q)^(1/n)/(b*e-d*x^q)^(1/n)]^r,x],x],x,(e*(a+b*x^n)/(c+d*x^n))^(1/q)]] /;
        FreeQ[{a,b,c,d,e},x] && PolynomialQ[u,x] && FractionQ[p] && IntegerQ[1/n] && IntegerQ[r]",
        desc: "Integration by substitution",
        refs: [],
        pattern: u_.pow(r_) * (e__ * (a__ + b__ * x_.pow(n_)) / (c__ + d__ * x_.pow(n_))).pow(p_),
        with: [u_, r_, e__, a__, b__, n_, c__, d__, p_, x_],
        optional: [r_, e__, a__, b__, n_, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && rubi_polynomial_q(&u_, x_)
                && fractionq!(p_)
                && !n_.is_zero()
                && integerq!(Atom::num(1) / &n_)
                && integerq!(r_)
        },
        rhs: {
            if n_.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let q_i = rubi_denominator(&p_).rubi_rhs();
            let q = Atom::num(q_i);
            if q.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_denominator = &b__ * &e__ - &d__ * sub_atom.pow(&q);
            if transformed_denominator.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let replacement = (-&a__ * &e__ + &c__ * sub_atom.pow(&q)).pow(Atom::num(1) / &n_)
                / (&b__ * &e__ - &d__ * sub_atom.pow(&q)).pow(Atom::num(1) / &n_);
            let transformed_integrand = rubi_simplify_integrand(
                &(sub_atom.pow(&q * (&p_ + 1) - 1)
                    * (-&a__ * &e__ + &c__ * sub_atom.pow(&q)).pow(Atom::num(1) / &n_ - 1)
                    / transformed_denominator.pow(Atom::num(1) / &n_ + 1)
                    * rubi_replace_all(&u_, x_, replacement).pow(&r_)),
                sub,
            );
            let transformed = rubi_rhs_int(&transformed_integrand, sub);

            let replacement_denominator = &c__ + &d__ * x_.pow(&n_);
            if replacement_denominator.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let outer_replacement =
                (&e__ * (&a__ + &b__ * x_.pow(&n_)) / replacement_denominator).pow(Atom::num(1) / &q);

            rubi_star(&q * &e__ * (&b__ * &c__ - &a__ * &d__) / &n_, rubi_subst(&transformed, sub, outer_replacement))
        },
    ));
}

fn push_rules_rule_2056(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, n_, p_, r_, u_, x_);
    rules.push(rubi_rule!(
        order: 2056,
        source: "Int[x_^m_.*u_^r_.*(e_.*(a_.+b_.*x_^n_.)/(c_+d_.*x_^n_.))^p_,x_Symbol] :=
          With[{q=Denominator[p]},
          q*e*(b*c-a*d)/n \\[Star] Subst[Int[SimplifyIntegrand[x^(q*(p+1)-1)*(-a*e+c*x^q)^((m+1)/n-1)/(b*e-d*x^q)^((m+1)/n+1)*
            ReplaceAll[u,x->(-a*e+c*x^q)^(1/n)/(b*e-d*x^q)^(1/n)]^r,x],x],x,(e*(a+b*x^n)/(c+d*x^n))^(1/q)]] /;
        FreeQ[{a,b,c,d,e},x] && PolynomialQ[u,x] && FractionQ[p] && IntegerQ[1/n] && IntegersQ[m,r]",
        desc: "Integration by substitution",
        refs: [],
        pattern: x_.pow(m_) * u_.pow(r_) * (e__ * (a__ + b__ * x_.pow(n_)) / (c__ + d__ * x_.pow(n_))).pow(p_),
        with: [m_, u_, r_, e__, a__, b__, n_, c__, d__, p_, x_],
        optional: [r_, e__, a__, b__, n_, d__, m_],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && rubi_polynomial_q(&u_, x_)
                && fractionq!(p_)
                && !n_.is_zero()
                && integerq!(Atom::num(1) / &n_)
                && integersq!([m_, r_])
        },
        rhs: {
            if n_.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let q_i = rubi_denominator(&p_).rubi_rhs();
            let q = Atom::num(q_i);
            if q.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_denominator = &b__ * &e__ - &d__ * sub_atom.pow(&q);
            if transformed_denominator.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let replacement = (-&a__ * &e__ + &c__ * sub_atom.pow(&q)).pow(Atom::num(1) / &n_)
                / (&b__ * &e__ - &d__ * sub_atom.pow(&q)).pow(Atom::num(1) / &n_);
            let transformed_integrand = rubi_simplify_integrand(
                &(sub_atom.pow(&q * (&p_ + 1) - 1)
                    * (-&a__ * &e__ + &c__ * sub_atom.pow(&q)).pow((&m_ + 1) / &n_ - 1)
                    / transformed_denominator.pow((&m_ + 1) / &n_ + 1)
                    * rubi_replace_all(&u_, x_, replacement).pow(&r_)),
                sub,
            );
            let transformed = rubi_rhs_int(&transformed_integrand, sub);

            let replacement_denominator = &c__ + &d__ * x_.pow(&n_);
            if replacement_denominator.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let outer_replacement =
                (&e__ * (&a__ + &b__ * x_.pow(&n_)) / replacement_denominator).pow(Atom::num(1) / &q);

            rubi_star(&q * &e__ * (&b__ * &c__ - &a__ * &d__) / &n_, rubi_subst(&transformed, sub, outer_replacement))
        },
    ));
}

fn push_rules_rule_2057(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, n_, p_, u__, x_);
    rules.push(rubi_rule!(
        order: 2057,
        source: "Int[u_.*(a_+b_./(c_+d_.*x_^n_))^p_,x_Symbol] :=
          Int[u*((b+a*c+a*d*x^n)/(c+d*x^n))^p,x] /;
        FreeQ[{a,b,c,d,n,p},x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: u__ * (a__ + b__ / (c__ + d__ * x_.pow(n_))).pow(p_),
        with: [u__, a__, b__, c__, d__, n_, p_, x_],
        optional: [u__, b__, d__],
        when: { freeq!([a__, b__, c__, d__, n_, p_], x_) },
        rhs: {
            let denominator = &c__ + &d__ * x_.pow(&n_);
            if denominator.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let recursive_integrand = &u__ * ((&b__ + &a__ * &c__ + &a__ * &d__ * x_.pow(&n_)) / denominator).pow(&p_);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_2058(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, n_, p_, q_, r_, u__, x_);
    rules.push(rubi_rule!(
        order: 2058,
        source: "Int[u_.*(e_.*(a_.+b_.*x_^n_.)^q_.*(c_+d_.*x_^n_)^r_.)^p_,x_Symbol] :=
          Simp[(e*(a+b*x^n)^q*(c+d*x^n)^r)^p/((a+b*x^n)^(p*q)*(c+d*x^n)^(p*r))] \\[Star]
            Int[u*(a+b*x^n)^(p*q)*(c+d*x^n)^(p*r),x] /;
        FreeQ[{a,b,c,d,e,n,p,q,r},x]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: u__ * (e__ * (a__ + b__ * x_.pow(n_)).pow(q_) * (c__ + d__ * x_.pow(n_)).pow(r_)).pow(p_),
        with: [u__, e__, a__, b__, n_, q_, c__, d__, r_, p_, x_],
        optional: [u__, e__, a__, b__, n_, q_, d__, r_],
        when: { freeq!([a__, b__, c__, d__, e__, n_, p_, q_, r_], x_) },
        rhs: {
            let denominator =
                (&a__ + &b__ * x_.pow(&n_)).pow(&p_ * &q_) * (&c__ + &d__ * x_.pow(&n_)).pow(&p_ * &r_);
            if denominator.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let coefficient = rubi_simp(
                &((&e__
                    * (&a__ + &b__ * x_.pow(&n_)).pow(&q_)
                    * (&c__ + &d__ * x_.pow(&n_)).pow(&r_))
                .pow(&p_)
                    / denominator),
                x_,
            );
            let recursive_integrand =
                &u__ * (&a__ + &b__ * x_.pow(&n_)).pow(&p_ * &q_) * (&c__ + &d__ * x_.pow(&n_)).pow(&p_ * &r_);

            rubi_star(coefficient, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_2059(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 2059,
        source: "Int[(a_.+b_.*(c_./x_)^n_)^p_,x_Symbol] :=
          -c \\[Star] Subst[Int[(a+b*x^n)^p/x^2,x],x,c/x] /;
        FreeQ[{a,b,c,n,p},x]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (a__ + b__ * (c__ / x_).pow(n_)).pow(p_),
        with: [a__, b__, c__, n_, p_, x_],
        optional: [a__, b__, c__],
        when: { freeq!([a__, b__, c__, n_, p_], x_) },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = (&a__ + &b__ * sub_atom.pow(&n_)).pow(&p_) / sub_atom.pow(2);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);

            rubi_star(-&c__, rubi_subst(&transformed, sub, &c__ / x_))
        },
    ));
}

fn push_rules_rule_2060(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 2060,
        source: "Int[x_^m_.*(a_.+b_.*(c_./x_)^n_)^p_,x_Symbol] :=
          -c^(m+1) \\[Star] Subst[Int[(a+b*x^n)^p/x^(m+2),x],x,c/x] /;
        FreeQ[{a,b,c,n,p},x] && IntegerQ[m]",
        desc: "Integration by substitution",
        refs: [],
        pattern: x_.pow(m_) * (a__ + b__ * (c__ / x_).pow(n_)).pow(p_),
        with: [m_, a__, b__, c__, n_, p_, x_],
        optional: [a__, b__, c__, m_],
        when: { freeq!([a__, b__, c__, n_, p_], x_) && integerq!(m_) },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = (&a__ + &b__ * sub_atom.pow(&n_)).pow(&p_) / sub_atom.pow(&m_ + 2);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);

            rubi_star(-c__.pow(&m_ + 1), rubi_subst(&transformed, sub, &c__ / x_))
        },
    ));
}

fn push_rules_rule_2061(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 2061,
        source: "Int[(d_.*x_)^m_*(a_.+b_.*(c_./x_)^n_)^p_,x_Symbol] :=
          -c*(d*x)^m*(c/x)^m \\[Star] Subst[Int[(a+b*x^n)^p/x^(m+2),x],x,c/x] /;
        FreeQ[{a,b,c,d,m,n,p},x] && Not[IntegerQ[m]]",
        desc: "Piecewise constant extraction and integration by substitution",
        refs: [],
        pattern: (d__ * x_).pow(m_) * (a__ + b__ * (c__ / x_).pow(n_)).pow(p_),
        with: [d__, m_, a__, b__, c__, n_, p_, x_],
        optional: [d__, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, m_, n_, p_], x_) && !integerq!(m_)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = (&a__ + &b__ * sub_atom.pow(&n_)).pow(&p_) / sub_atom.pow(&m_ + 2);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);
            rubi_star(-&c__ * (&d__ * x_).pow(&m_) * (&c__ / x_).pow(&m_), rubi_subst(&transformed, sub, &c__ / x_))
        },
    ));
}

fn push_rules_rule_2062(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 2062,
        source: "Int[(a_.+b_.*(d_./x_)^n_+c_.*(d_./x_)^n2_.)^p_,x_Symbol] :=
          -d \\[Star] Subst[Int[(a+b*x^n+c*x^(2*n))^p/x^2,x],x,d/x] /;
        FreeQ[{a,b,c,d,n,p},x] && EqQ[n2,2*n]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (a__ + b__ * (d__ / x_).pow(n_) + c__ * (d__ / x_).pow(n2_)).pow(p_),
        with: [a__, b__, d__, n_, c__, n2_, p_, x_],
        optional: [a__, b__, d__, c__, n2_],
        when: {
            freeq!([a__, b__, c__, d__, n_, p_], x_) && eqq!(n2_, Atom::num(2) * &n_)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand =
                (&a__ + &b__ * sub_atom.pow(&n_) + &c__ * sub_atom.pow(Atom::num(2) * &n_)).pow(&p_) / sub_atom.pow(2);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);

            rubi_star(-&d__, rubi_subst(&transformed, sub, &d__ / x_))
        },
    ));
}

fn push_rules_rule_2063(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a_, b__, c__, d__, m_, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 2063,
        source: "Int[x_^m_.*(a_+b_.*(d_./x_)^n_+c_.*(d_./x_)^n2_.)^p_,x_Symbol] :=
          -d^(m+1) \\[Star] Subst[Int[(a+b*x^n+c*x^(2*n))^p/x^(m+2),x],x,d/x] /;
        FreeQ[{a,b,c,d,n,p},x] && EqQ[n2,2*n] && IntegerQ[m]",
        desc: "Integration by substitution",
        refs: [],
        pattern: x_.pow(m_) * (a_ + b__ * (d__ / x_).pow(n_) + c__ * (d__ / x_).pow(n2_)).pow(p_),
        with: [m_, a_, b__, d__, n_, c__, n2_, p_, x_],
        optional: [b__, d__, c__, n2_, m_],
        when: {
            freeq!([a_, b__, c__, d__, n_, p_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && integerq!(m_)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand =
                (&a_ + &b__ * sub_atom.pow(&n_) + &c__ * sub_atom.pow(Atom::num(2) * &n_)).pow(&p_) / sub_atom.pow(&m_ + 2);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);

            rubi_star(-d__.pow(&m_ + 1), rubi_subst(&transformed, sub, &d__ / x_))
        },
    ));
}

fn push_rules_rule_2064(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a_, b__, c__, d__, e__, m_, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 2064,
        source: "Int[(e_.*x_)^m_*(a_+b_.*(d_./x_)^n_+c_.*(d_./x_)^n2_.)^p_,x_Symbol] :=
          -d*(e*x)^m*(d/x)^m \\[Star] Subst[Int[(a+b*x^n+c*x^(2*n))^p/x^(m+2),x],x,d/x] /;
        FreeQ[{a,b,c,d,e,m,n,p},x] && EqQ[n2,2*n] && Not[IntegerQ[m]]",
        desc: "Piecewise constant extraction and integration by substitution",
        refs: [],
        pattern: (e__ * x_).pow(m_) * (a_ + b__ * (d__ / x_).pow(n_) + c__ * (d__ / x_).pow(n2_)).pow(p_),
        with: [e__, m_, a_, b__, d__, n_, c__, n2_, p_, x_],
        optional: [e__, b__, d__, c__, n2_],
        when: {
            freeq!([a_, b__, c__, d__, e__, m_, n_, p_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && !integerq!(m_)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand =
                (&a_ + &b__ * sub_atom.pow(&n_) + &c__ * sub_atom.pow(Atom::num(2) * &n_)).pow(&p_) / sub_atom.pow(&m_ + 2);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);
            rubi_star(-&d__ * (&e__ * x_).pow(&m_) * (&d__ / x_).pow(&m_), rubi_subst(&transformed, sub, &d__ / x_))
        },
    ));
}

fn push_rules_rule_2065(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 2065,
        source: "Int[(a_.+b_.*(d_./x_)^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
          -d \\[Star] Subst[Int[(a+b*x^n+c/d^(2*n)*x^(2*n))^p/x^2,x],x,d/x] /;
        FreeQ[{a,b,c,d,n,p},x] && EqQ[n2,-2*n] && IntegerQ[2*n]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (a__ + b__ * (d__ / x_).pow(n_) + c__ * x_.pow(n2_)).pow(p_),
        with: [a__, b__, d__, n_, c__, n2_, p_, x_],
        optional: [a__, b__, d__, c__, n2_],
        when: {
            freeq!([a__, b__, c__, d__, n_, p_], x_)
                && eqq!(n2_, -Atom::num(2) * &n_)
                && integerq!(Atom::num(2) * &n_)
        },
        rhs: {
            let d_power = d__.pow(Atom::num(2) * &n_);
            if d_power.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand =
                (&a__ + &b__ * sub_atom.pow(&n_) + &c__ / d_power * sub_atom.pow(Atom::num(2) * &n_)).pow(&p_)
                    / sub_atom.pow(2);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);

            rubi_star(-&d__, rubi_subst(&transformed, sub, &d__ / x_))
        },
    ));
}

fn push_rules_rule_2066(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a_, b__, c__, d__, m_, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 2066,
        source: "Int[x_^m_.*(a_+b_.*(d_./x_)^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
          -d^(m+1) \\[Star] Subst[Int[(a+b*x^n+c/d^(2*n)*x^(2*n))^p/x^(m+2),x],x,d/x] /;
        FreeQ[{a,b,c,d,n,p},x] && EqQ[n2,-2*n] && IntegerQ[2*n] && IntegerQ[m]",
        desc: "Integration by substitution",
        refs: [],
        pattern: x_.pow(m_) * (a_ + b__ * (d__ / x_).pow(n_) + c__ * x_.pow(n2_)).pow(p_),
        with: [m_, a_, b__, d__, n_, c__, n2_, p_, x_],
        optional: [b__, d__, c__, n2_, m_],
        when: {
            freeq!([a_, b__, c__, d__, n_, p_], x_)
                && eqq!(n2_, -Atom::num(2) * &n_)
                && integerq!(Atom::num(2) * &n_)
                && integerq!(m_)
        },
        rhs: {
            let d_power = d__.pow(Atom::num(2) * &n_);
            if d_power.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand =
                (&a_ + &b__ * sub_atom.pow(&n_) + &c__ / d_power * sub_atom.pow(Atom::num(2) * &n_)).pow(&p_)
                    / sub_atom.pow(&m_ + 2);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);

            rubi_star(-d__.pow(&m_ + 1), rubi_subst(&transformed, sub, &d__ / x_))
        },
    ));
}

fn push_rules_rule_2067(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a_, b__, c__, d__, e__, m_, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 2067,
        source: "Int[(e_.*x_)^m_*(a_+b_.*(d_./x_)^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
          -d*(e*x)^m*(d/x)^m \\[Star] Subst[Int[(a+b*x^n+c/d^(2*n)*x^(2*n))^p/x^(m+2),x],x,d/x] /;
        FreeQ[{a,b,c,d,e,n,p},x] && EqQ[n2,-2*n] && Not[IntegerQ[m]] && IntegerQ[2*n]",
        desc: "Piecewise constant extraction and integration by substitution",
        refs: [],
        pattern: (e__ * x_).pow(m_) * (a_ + b__ * (d__ / x_).pow(n_) + c__ * x_.pow(n2_)).pow(p_),
        with: [e__, m_, a_, b__, d__, n_, c__, n2_, p_, x_],
        optional: [e__, b__, d__, c__, n2_],
        when: {
            freeq!([a_, b__, c__, d__, e__, n_, p_], x_)
                && eqq!(n2_, -Atom::num(2) * &n_)
                && !integerq!(m_)
                && integerq!(Atom::num(2) * &n_)
        },
        rhs: {
            let d_power = d__.pow(Atom::num(2) * &n_);
            if d_power.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand =
                (&a_ + &b__ * sub_atom.pow(&n_) + &c__ / d_power * sub_atom.pow(Atom::num(2) * &n_)).pow(&p_)
                    / sub_atom.pow(&m_ + 2);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);
            rubi_star(-&d__ * (&e__ * x_).pow(&m_) * (&d__ / x_).pow(&m_), rubi_subst(&transformed, sub, &d__ / x_))
        },
    ));
}

fn push_rules_rule_2068(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a_, b__, c_, d__, e__, f__, n_, p_, q_, r_, s_, u__, x_);
    rules.push(rubi_rule!(
        order: 2068,
        source: "Int[u_.*(e_.*(a_+b_.*x_^n_.)^r_.)^p_*(f_.*(c_+d_.*x_^n_.)^s_)^q_,x_Symbol] :=
          (e*(a+b*x^n)^r)^p*(f*(c+d*x^n)^s)^q/((a+b*x^n)^(p*r)*(c+d*x^n)^(q*s)) \\[Star]
            Int[u*(a+b*x^n)^(p*r)*(c+d*x^n)^(q*s),x] /;
        FreeQ[{a,b,c,d,e,f,n,p,q,r,s},x]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: u__ * (e__ * (a_ + b__ * x_.pow(n_)).pow(r_)).pow(p_) * (f__ * (c_ + d__ * x_.pow(n_)).pow(s_)).pow(q_),
        with: [u__, e__, a_, b__, n_, r_, p_, f__, c_, d__, s_, q_, x_],
        optional: [u__, e__, b__, n_, r_, f__, d__],
        when: { freeq!([a_, b__, c_, d__, e__, f__, n_, p_, q_, r_, s_], x_) },
        rhs: {
            let denominator =
                (&a_ + &b__ * x_.pow(&n_)).pow(&p_ * &r_) * (&c_ + &d__ * x_.pow(&n_)).pow(&q_ * &s_);
            if denominator.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let coefficient = (&e__ * (&a_ + &b__ * x_.pow(&n_)).pow(&r_)).pow(&p_)
                * (&f__ * (&c_ + &d__ * x_.pow(&n_)).pow(&s_)).pow(&q_)
                / denominator;
            let recursive_integrand =
                &u__ * (&a_ + &b__ * x_.pow(&n_)).pow(&p_ * &r_) * (&c_ + &d__ * x_.pow(&n_)).pow(&q_ * &s_);

            rubi_star(coefficient, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_2069(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; px_, u__);
    rules.push(rubi_rule!(
        order: 2069,
        source: "Int[u_.*Px_,x_Symbol] :=
          With[{a=Rt[Coeff[Px,x^2,0],Expon[Px,x^2]],b=Rt[Coeff[Px,x^2,Expon[Px,x^2]],Expon[Px,x^2]]},
          Int[u*(a+b*x^2)^Expon[Px,x^2],x] /;
         EqQ[Px,(a+b*x^2)^Expon[Px,x^2]]] /;
        PolyQ[Px,x^2] && GtQ[Expon[Px,x^2],1] && NeQ[Coeff[Px,x^2,0],0] && Not[MatchQ[Px,a_.*v_^Expon[Px,x^2] /; FreeQ[a,x] && BinomialQ[v,x,2]]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_12(symbols),
        with: [u__, px_, x_],
        optional: [u__],
        when: {
            rubi_perfect_binomial_power(&px_, x_, 2).is_some_and(|parts| {
                let matches_source_shape = rubi_split_product(
                    |factor| {
                        if factor.get_atom_type() != AtomType::Pow {
                            return false;
                        }
                        let (base, exponent) = rubi_factor_base_exponent(factor);
                        eqq!(exponent, parts.degree)
                            && rubi_binomial_degree(&base, x_).is_some_and(|n| eqq!(n, 2))
                    },
                    &px_,
                )
                .is_some_and(|(_, coefficient)| is_free_of(&coefficient, x_));

                !matches_source_shape
            })
        },
        rhs: {
            let parts = rubi_perfect_binomial_power(&px_, x_, 2)
                .expect("Rubi DownValue 2069 condition validates the binomial power");
            rubi_rhs_int(&(u__ * parts.power), x_)
        },
    ));
}

fn push_rules_rule_2070(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; p_, px_, u__);
    rules.push(rubi_rule!(
        order: 2070,
        source: "Int[u_.*Px_^p_,x_Symbol] :=
          With[{a=Rt[Coeff[Px,x^2,0],Expon[Px,x^2]],b=Rt[Coeff[Px,x^2,Expon[Px,x^2]],Expon[Px,x^2]]},
          Int[u*(a+b*x^2)^(Expon[Px,x^2]*p),x] /;
         EqQ[Px,(a+b*x^2)^Expon[Px,x^2]]] /;
        IntegerQ[p] && PolyQ[Px,x^2] && GtQ[Expon[Px,x^2],1] && NeQ[Coeff[Px,x^2,0],0]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_13(symbols),
        with: [u__, px_, p_, x_],
        optional: [u__],
        x_free: [p_],
        when: {
            integerq!(p_)
                && rubi_perfect_binomial_power(&px_, x_, 2).is_some()
        },
        rhs: {
            let x_squared = x_.pow(2);
            let parts = rubi_perfect_binomial_power(&px_, x_, 2)
                .expect("Rubi DownValue 2070 condition validates the binomial power");
            rubi_rhs_int(
                &(u__
                    * (&parts.a + &parts.b * &x_squared)
                        .pow(Atom::num(parts.degree) * p_)),
                x_,
            )
        },
    ));
}

fn push_rules_rule_2071(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; p_, px_, u__);
    rules.push(rubi_rule!(
        order: 2071,
        source: "Int[u_.*Px_^p_,x_Symbol] :=
          With[{a=Rt[Coeff[Px,x^2,0],Expon[Px,x^2]],b=Rt[Coeff[Px,x^2,Expon[Px,x^2]],Expon[Px,x^2]]},
          ((a+b*x^2)^Expon[Px,x^2])^p/(a+b*x^2)^(Expon[Px,x^2]*p) \\[Star] Int[u*(a+b*x^2)^(Expon[Px,x^2]*p),x] /;
         EqQ[Px,(a+b*x^2)^Expon[Px,x^2]]] /;
        Not[IntegerQ[p]] && PolyQ[Px,x^2] && GtQ[Expon[Px,x^2],1] && NeQ[Coeff[Px,x^2,0],0]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_13(symbols),
        with: [u__, px_, p_, x_],
        optional: [u__],
        x_free: [p_],
        when: {
            !integerq!(p_)
                && rubi_perfect_binomial_power(&px_, x_, 2).is_some()
        },
        rhs: {
            let x_squared = x_.pow(2);
            let parts = rubi_perfect_binomial_power(&px_, x_, 2)
                .expect("Rubi DownValue 2071 condition validates the binomial power");
            let binomial = &parts.a + &parts.b * &x_squared;
            let recursive = rubi_rhs_int(
                &(u__ * binomial.pow(Atom::num(parts.degree) * &p_)),
                x_,
            );
            rubi_star(
                parts.power.pow(&p_)
                    / (&parts.a + &parts.b * &x_squared)
                        .pow(Atom::num(parts.degree) * p_),
                recursive,
            )
        },
    ));
}

fn push_rules_rule_203(rules: &mut Vec<RubiRule>) {
    rubi_symb!(m_, u_);
    rules.push(rubi_rule!(
        order: 203,
        source: "Int[u_^m_,x_Symbol] :=
          Int[ExpandToSum[u,x]^m,x] /;
        FreeQ[m,x] && LinearQ[u,x] && Not[LinearMatchQ[u,x]]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: u_.pow(m_),
        with: [u_, m_, x_],
        when: { freeq!(m_, x_) && rubi_linear_q(&u_, x_) && !rubi_linear_match_q(&u_, x_) },
        rhs: {
            let recursive_integrand = rubi_expand_to_sum(&u_, x_).pow(&m_);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_204(rules: &mut Vec<RubiRule>) {
    rubi_symb!(m_, n_, u_, v_);
    rules.push(rubi_rule!(
        order: 204,
        source: "Int[u_^m_.*v_^n_.,x_Symbol] :=
          Int[ExpandToSum[u,x]^m*ExpandToSum[v,x]^n,x] /;
        FreeQ[{m,n},x] && LinearQ[{u,v},x] && Not[LinearMatchQ[{u,v},x]]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: u_.pow(m_) * v_.pow(n_),
        with: [u_, m_, v_, n_, x_],
        optional: [m_, n_],
        when: {
            freeq!([m_, n_], x_)
                && rubi_linear_q_list(&[&u_, &v_], x_)
                && !rubi_linear_match_q_list(&[&u_, &v_], x_)
        },
        rhs: {
            let recursive_integrand = rubi_expand_to_sum(&u_, x_).pow(&m_) * rubi_expand_to_sum(&v_, x_).pow(&n_);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_205(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; m_, n_, p_, u_, v_, w_);
    rules.push(rubi_rule!(
        order: 205,
        source: "Int[u_^m_.*v_^n_.*w_^p_.,x_Symbol] :=
          Int[ExpandToSum[u,x]^m*ExpandToSum[v,x]^n*ExpandToSum[w,x]^p,x] /;
        FreeQ[{m,n,p},x] && LinearQ[{u,v,w},x] && Not[LinearMatchQ[{u,v,w},x]]",
        desc: "Algebraic normalization",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [u_, m_, v_, n_, w_, p_, x_],
        optional: [m_, n_, p_],
        when: {
            freeq!([m_, n_, p_], x_)
                && rubi_linear_q_list(&[&u_, &v_, &w_], x_)
                && !rubi_linear_match_q_list(&[&u_, &v_, &w_], x_)
        },
        rhs: {
            let recursive_integrand = rubi_expand_to_sum(&u_, x_).pow(&m_)
                * rubi_expand_to_sum(&v_, x_).pow(&n_)
                * rubi_expand_to_sum(&w_, x_).pow(&p_);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_206(rules: &mut Vec<RubiRule>) {
    rubi_symb!(m_, n_, p_, q_, u_, v_, w_, z_);
    rules.push(rubi_rule!(
        order: 206,
        source: "Int[u_^m_.*v_^n_.*w_^p_.*z_^q_.,x_Symbol] :=
          Int[ExpandToSum[u,x]^m*ExpandToSum[v,x]^n*ExpandToSum[w,x]^p*ExpandToSum[z,x]^q,x] /;
        FreeQ[{m,n,p,q},x] && LinearQ[{u,v,w,z},x] && Not[LinearMatchQ[{u,v,w,z},x]]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: u_.pow(m_) * v_.pow(n_) * w_.pow(p_) * z_.pow(q_),
        with: [u_, m_, v_, n_, w_, p_, z_, q_, x_],
        optional: [m_, n_, p_, q_],
        when: {
            freeq!([m_, n_, p_, q_], x_)
                && rubi_linear_q_list(&[&u_, &v_, &w_, &z_], x_)
                && !rubi_linear_match_q_list(&[&u_, &v_, &w_, &z_], x_)
        },
        rhs: {
            let recursive_integrand = rubi_expand_to_sum(&u_, x_).pow(&m_)
                * rubi_expand_to_sum(&v_, x_).pow(&n_)
                * rubi_expand_to_sum(&w_, x_).pow(&p_)
                * rubi_expand_to_sum(&z_, x_).pow(&q_);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_2072(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; p_, u_);
    rules.push(rubi_rule!(
        order: 2072,
        source: "Int[u_^p_,x_Symbol] :=
          Int[ExpandToSum[u,x]^p,x] /;
        FreeQ[p,x] && BinomialQ[u,x] && Not[BinomialMatchQ[u,x]]",
        desc: "Algebraic normalization",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [u_, p_, x_],
        when: { freeq!(p_, x_) && rubi_binomial_q(&u_, x_) && !rubi_binomial_match_q(&u_, x_) },
        rhs: {
            let recursive_integrand = rubi_expand_to_sum(&u_, x_).pow(&p_);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_2073(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; c__, m_, p_, u_, x_);
    rules.push(rubi_rule!(
        order: 2073,
        source: "Int[(c_.*x_)^m_.*u_^p_.,x_Symbol] :=
          Int[(c*x)^m*ExpandToSum[u,x]^p,x] /;
        FreeQ[{c,m,p},x] && BinomialQ[u,x] && Not[BinomialMatchQ[u,x]]",
        desc: "Algebraic normalization",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [c__, m_, u_, p_, x_],
        optional: [c__, m_, p_],
        when: {
            freeq!([c__, m_, p_], x_)
                && rubi_binomial_q(&u_, x_)
                && !rubi_binomial_match_q(&u_, x_)
        },
        rhs: {
            let recursive_integrand = (&c__ * x_).pow(&m_) * rubi_expand_to_sum(&u_, x_).pow(&p_);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_2074(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; p_, q_, u_, v_);
    rules.push(rubi_rule!(
        order: 2074,
        source: "Int[u_^p_.*v_^q_.,x_Symbol] :=
          Int[ExpandToSum[u,x]^p*ExpandToSum[v,x]^q,x] /;
        FreeQ[{p,q},x] && BinomialQ[{u,v},x] && EqQ[BinomialDegree[u,x]-BinomialDegree[v,x],0] && Not[BinomialMatchQ[{u,v},x]]",
        desc: "Algebraic normalization",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [u_, p_, v_, q_, x_],
        optional: [p_, q_],
        when: {
            freeq!([p_, q_], x_)
                && rubi_binomial_q_list(&[&u_, &v_], x_)
                && rubi_binomial_degree(&u_, x_)
                    .zip(rubi_binomial_degree(&v_, x_))
                    .is_some_and(|(u_degree, v_degree)| eqq!(u_degree - v_degree, 0))
                && !rubi_binomial_match_q_list(&[&u_, &v_], x_)
        },
        rhs: {
            let recursive_integrand = rubi_expand_to_sum(&u_, x_).pow(&p_) * rubi_expand_to_sum(&v_, x_).pow(&q_);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_2075(rules: &mut Vec<RubiRule>) {
    rubi_symb!(e__, m_, p_, q_, u_, v_, x_);
    rules.push(rubi_rule!(
        order: 2075,
        source: "Int[(e_.*x_)^m_.*u_^p_.*v_^q_.,x_Symbol] :=
          Int[(e*x)^m*ExpandToSum[u,x]^p*ExpandToSum[v,x]^q,x] /;
        FreeQ[{e,m,p,q},x] && BinomialQ[{u,v},x] && EqQ[BinomialDegree[u,x]-BinomialDegree[v,x],0] && Not[BinomialMatchQ[{u,v},x]]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: (e__ * x_).pow(m_) * u_.pow(p_) * v_.pow(q_),
        with: [e__, m_, u_, p_, v_, q_, x_],
        optional: [e__, m_, p_, q_],
        when: {
            freeq!([e__, m_, p_, q_], x_)
                && rubi_binomial_q_list(&[&u_, &v_], x_)
                && rubi_binomial_degree(&u_, x_)
                    .zip(rubi_binomial_degree(&v_, x_))
                    .is_some_and(|(u_degree, v_degree)| eqq!(u_degree - v_degree, 0))
                && !rubi_binomial_match_q_list(&[&u_, &v_], x_)
        },
        rhs: {
            let recursive_integrand =
                (&e__ * x_).pow(&m_) * rubi_expand_to_sum(&u_, x_).pow(&p_) * rubi_expand_to_sum(&v_, x_).pow(&q_);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_2076(rules: &mut Vec<RubiRule>) {
    rubi_symb!(m_, p_, q_, u_, v_, w_);
    rules.push(rubi_rule!(
        order: 2076,
        source: "Int[u_^m_.*v_^p_.*w_^q_.,x_Symbol] :=
          Int[ExpandToSum[u,x]^m*ExpandToSum[v,x]^p*ExpandToSum[w,x]^q,x] /;
        FreeQ[{m,p,q},x] && BinomialQ[{u,v,w},x] && EqQ[BinomialDegree[u,x]-BinomialDegree[v,x],0] &&
          EqQ[BinomialDegree[u,x]-BinomialDegree[w,x],0] && Not[BinomialMatchQ[{u,v,w},x]]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: u_.pow(m_) * v_.pow(p_) * w_.pow(q_),
        with: [u_, m_, v_, p_, w_, q_, x_],
        optional: [m_, p_, q_],
        when: {
            freeq!([m_, p_, q_], x_)
                && rubi_binomial_q_list(&[&u_, &v_, &w_], x_)
                && rubi_binomial_degree(&u_, x_)
                    .zip(rubi_binomial_degree(&v_, x_))
                    .is_some_and(|(u_degree, v_degree)| eqq!(u_degree - v_degree, 0))
                && rubi_binomial_degree(&u_, x_)
                    .zip(rubi_binomial_degree(&w_, x_))
                    .is_some_and(|(u_degree, w_degree)| eqq!(u_degree - w_degree, 0))
                && !rubi_binomial_match_q_list(&[&u_, &v_, &w_], x_)
        },
        rhs: {
            let recursive_integrand = rubi_expand_to_sum(&u_, x_).pow(&m_)
                * rubi_expand_to_sum(&v_, x_).pow(&p_)
                * rubi_expand_to_sum(&w_, x_).pow(&q_);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_2077(rules: &mut Vec<RubiRule>) {
    rubi_symb!(g__, m_, p_, q_, r_, u_, v_, x_, z_);
    rules.push(rubi_rule!(
        order: 2077,
        source: "Int[(g_.*x_)^m_.*u_^p_.*v_^q_.*z_^r_.,x_Symbol] :=
          Int[(g*x)^m*ExpandToSum[u,x]^p*ExpandToSum[v,x]^q*ExpandToSum[z,x]^r,x] /;
        FreeQ[{g,m,p,q,r},x] && BinomialQ[{u,v,z},x] && EqQ[BinomialDegree[u,x]-BinomialDegree[v,x],0] &&
          EqQ[BinomialDegree[u,x]-BinomialDegree[z,x],0] && Not[BinomialMatchQ[{u,v,z},x]]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: (g__ * x_).pow(m_) * u_.pow(p_) * v_.pow(q_) * z_.pow(r_),
        with: [g__, m_, u_, p_, v_, q_, z_, r_, x_],
        optional: [g__, m_, p_, q_, r_],
        when: {
            freeq!([g__, m_, p_, q_, r_], x_)
                && rubi_binomial_q_list(&[&u_, &v_, &z_], x_)
                && rubi_binomial_degree(&u_, x_)
                    .zip(rubi_binomial_degree(&v_, x_))
                    .is_some_and(|(u_degree, v_degree)| eqq!(u_degree - v_degree, 0))
                && rubi_binomial_degree(&u_, x_)
                    .zip(rubi_binomial_degree(&z_, x_))
                    .is_some_and(|(u_degree, z_degree)| eqq!(u_degree - z_degree, 0))
                && !rubi_binomial_match_q_list(&[&u_, &v_, &z_], x_)
        },
        rhs: {
            let recursive_integrand = (&g__ * x_).pow(&m_)
                * rubi_expand_to_sum(&u_, x_).pow(&p_)
                * rubi_expand_to_sum(&v_, x_).pow(&q_)
                * rubi_expand_to_sum(&z_, x_).pow(&r_);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_2451(rules: &mut Vec<RubiRule>) {
    rubi_symb!(c__, m_, p_, pq__, u_, x_);
    rules.push(rubi_rule!(
        order: 2451,
        source: "Int[(c_.*x_)^m_.*Pq_*u_^p_.,x_Symbol] :=
          Int[(c*x)^m*Pq*ExpandToSum[u,x]^p,x] /;
        FreeQ[{c,m,p},x] && PolyQ[Pq,x] && BinomialQ[u,x] && Not[BinomialMatchQ[u,x]]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: (c__ * x_).pow(m_) * pq__ * u_.pow(p_),
        with: [c__, m_, pq__, u_, p_, x_],
        optional: [c__, m_, p_],
        when: {
            freeq!([c__, m_, p_], x_)
                && rubi_poly_q(&pq__, x_)
                && rubi_binomial_q(&u_, x_)
                && !rubi_binomial_match_q(&u_, x_)
        },
        rhs: {
            let recursive_integrand = (&c__ * x_).pow(&m_) * &pq__ * rubi_expand_to_sum(&u_, x_).pow(&p_);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_2078(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; p_, u_);
    rules.push(rubi_rule!(
        order: 2078,
        source: "Int[u_^p_,x_Symbol] :=
          Int[ExpandToSum[u,x]^p,x] /;
        FreeQ[p,x] && GeneralizedBinomialQ[u,x] && Not[GeneralizedBinomialMatchQ[u,x]]",
        desc: "Algebraic normalization",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [u_, p_, x_],
        when: {
            freeq!(p_, x_) && rubi_generalized_binomial_q(&u_, x_) && !rubi_generalized_binomial_match_q(&u_, x_)
        },
        rhs: {
            let recursive_integrand = rubi_expand_to_sum(&u_, x_).pow(&p_);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_2079(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; c__, m_, p_, u_, x_);
    rules.push(rubi_rule!(
        order: 2079,
        source: "Int[(c_.*x_)^m_.*u_^p_.,x_Symbol] :=
          Int[(c*x)^m*ExpandToSum[u,x]^p,x] /;
        FreeQ[{c,m,p},x] && GeneralizedBinomialQ[u,x] && Not[GeneralizedBinomialMatchQ[u,x]]",
        desc: "Algebraic normalization",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [c__, m_, u_, p_, x_],
        optional: [c__, m_, p_],
        when: {
            freeq!([c__, m_, p_], x_)
                && rubi_generalized_binomial_q(&u_, x_)
                && !rubi_generalized_binomial_match_q(&u_, x_)
        },
        rhs: {
            let recursive_integrand = (&c__ * x_).pow(&m_) * rubi_expand_to_sum(&u_, x_).pow(&p_);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_2080(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; p_, u_);
    rules.push(rubi_rule!(
        order: 2080,
        source: "Int[u_^p_,x_Symbol] :=
          Int[ExpandToSum[u,x]^p,x] /;
        FreeQ[p,x] && QuadraticQ[u,x] && Not[QuadraticMatchQ[u,x]]",
        desc: "Algebraic normalization",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [u_, p_, x_],
        when: { freeq!(p_, x_) && rubi_quadratic_q(&u_, x_) && !rubi_quadratic_match_q(&u_, x_) },
        rhs: {
            let recursive_integrand = rubi_expand_to_sum(&u_, x_).pow(&p_);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_2081(rules: &mut Vec<RubiRule>) {
    rubi_symb!(m_, p_, u_, v_);
    rules.push(rubi_rule!(
        order: 2081,
        source: "Int[u_^m_.*v_^p_.,x_Symbol] :=
          Int[ExpandToSum[u,x]^m*ExpandToSum[v,x]^p,x] /;
        FreeQ[{m,p},x] && LinearQ[u,x] && QuadraticQ[v,x] && Not[LinearMatchQ[u,x] && QuadraticMatchQ[v,x]]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: u_.pow(m_) * v_.pow(p_),
        with: [u_, m_, v_, p_, x_],
        optional: [m_, p_],
        when: {
            freeq!([m_, p_], x_)
                && rubi_linear_q(&u_, x_)
                && rubi_quadratic_q(&v_, x_)
                && !(rubi_linear_match_q(&u_, x_) && rubi_quadratic_match_q(&v_, x_))
        },
        rhs: {
            let recursive_integrand = rubi_expand_to_sum(&u_, x_).pow(&m_) * rubi_expand_to_sum(&v_, x_).pow(&p_);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_2082(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; m_, n_, p_, u_, v_, w_);
    rules.push(rubi_rule!(
        order: 2082,
        source: "Int[u_^m_.*v_^n_.*w_^p_.,x_Symbol] :=
          Int[ExpandToSum[u,x]^m*ExpandToSum[v,x]^n*ExpandToSum[w,x]^p,x] /;
        FreeQ[{m,n,p},x] && LinearQ[{u,v},x] && QuadraticQ[w,x] && Not[LinearMatchQ[{u,v},x] && QuadraticMatchQ[w,x]]",
        desc: "Algebraic normalization",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [u_, m_, v_, n_, w_, p_, x_],
        optional: [m_, n_, p_],
        when: {
            freeq!([m_, n_, p_], x_)
                && rubi_linear_q_list(&[&u_, &v_], x_)
                && rubi_quadratic_q(&w_, x_)
                && !(rubi_linear_match_q_list(&[&u_, &v_], x_) && rubi_quadratic_match_q(&w_, x_))
        },
        rhs: {
            let recursive_integrand = rubi_expand_to_sum(&u_, x_).pow(&m_)
                * rubi_expand_to_sum(&v_, x_).pow(&n_)
                * rubi_expand_to_sum(&w_, x_).pow(&p_);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_2083(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; p_, q_, u_, v_);
    rules.push(rubi_rule!(
        order: 2083,
        source: "Int[u_^p_.*v_^q_.,x_Symbol] :=
          Int[ExpandToSum[u,x]^p*ExpandToSum[v,x]^q,x] /;
        FreeQ[{p,q},x] && QuadraticQ[{u,v},x] && Not[QuadraticMatchQ[{u,v},x]]",
        desc: "Algebraic normalization",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [u_, p_, v_, q_, x_],
        optional: [p_, q_],
        when: {
            freeq!([p_, q_], x_)
                && rubi_quadratic_q_list(&[&u_, &v_], x_)
                && !rubi_quadratic_match_q_list(&[&u_, &v_], x_)
        },
        rhs: {
            let recursive_integrand = rubi_expand_to_sum(&u_, x_).pow(&p_) * rubi_expand_to_sum(&v_, x_).pow(&q_);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_2084(rules: &mut Vec<RubiRule>) {
    rubi_symb!(m_, p_, q_, u_, v_, z_);
    rules.push(rubi_rule!(
        order: 2084,
        source: "Int[z_^m_.*u_^p_.*v_^q_.,x_Symbol] :=
          Int[ExpandToSum[z,x]^m*ExpandToSum[u,x]^p*ExpandToSum[v,x]^q,x] /;
        FreeQ[{m,p,q},x] && LinearQ[z,x] && QuadraticQ[{u,v},x] && Not[LinearMatchQ[z,x] && QuadraticMatchQ[{u,v},x]] &&
          Not[MatchQ[z^m*u^p*v^q, (d_.+e_.*x)^m*(f_.+g_.*x)^2*(a_.+b_.*x+c_.*x^2)^t_. /; FreeQ[{a,b,c,d,e,f,g,t},x]]] &&
          Not[MatchQ[z^m*u^p*v^q, (d_.+e_.*x)^m*(f_.+g_.*x)^2*(a_.+c_.*x^2)^t_. /; FreeQ[{a,c,d,e,f,g,t},x]]]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: z_.pow(m_) * u_.pow(p_) * v_.pow(q_),
        with: [z_, m_, u_, p_, v_, q_, x_],
        optional: [m_, p_, q_],
        when: {
            freeq!([m_, p_, q_], x_)
                && rubi_linear_q(&z_, x_)
                && rubi_quadratic_q_list(&[&u_, &v_], x_)
                && !(rubi_linear_match_q(&z_, x_) && rubi_quadratic_match_q_list(&[&u_, &v_], x_))
        },
        rhs: {
            let recursive_integrand = rubi_expand_to_sum(&z_, x_).pow(&m_)
                * rubi_expand_to_sum(&u_, x_).pow(&p_)
                * rubi_expand_to_sum(&v_, x_).pow(&q_);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_2452(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; p_, pq__, u_);
    rules.push(rubi_rule!(
        order: 2452,
        source: "Int[Pq_*u_^p_.,x_Symbol] :=
          Int[Pq*ExpandToSum[u,x]^p,x] /;
        FreeQ[p,x] && PolyQ[Pq,x] && QuadraticQ[u,x] && Not[QuadraticMatchQ[u,x]]",
        desc: "Algebraic normalization",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [pq__, u_, p_, x_],
        optional: [p_],
        when: {
            freeq!(p_, x_)
                && rubi_poly_q(&pq__, x_)
                && rubi_quadratic_q(&u_, x_)
                && !rubi_quadratic_match_q(&u_, x_)
        },
        rhs: {
            let recursive_integrand = &pq__ * rubi_expand_to_sum(&u_, x_).pow(&p_);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_2453(rules: &mut Vec<RubiRule>) {
    rubi_symb!(m_, p_, pq__, u_, v_);
    rules.push(rubi_rule!(
        order: 2453,
        source: "Int[u_^m_.*Pq_*v_^p_.,x_Symbol] :=
          Int[ExpandToSum[u,x]^m*Pq*ExpandToSum[v,x]^p,x] /;
        FreeQ[{m,p},x] && PolyQ[Pq,x] && LinearQ[u,x] && QuadraticQ[v,x] && Not[LinearMatchQ[u,x] && QuadraticMatchQ[v,x]]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: u_.pow(m_) * pq__ * v_.pow(p_),
        with: [u_, m_, pq__, v_, p_, x_],
        optional: [m_, p_],
        when: {
            freeq!([m_, p_], x_)
                && rubi_poly_q(&pq__, x_)
                && rubi_linear_q(&u_, x_)
                && rubi_quadratic_q(&v_, x_)
                && !(rubi_linear_match_q(&u_, x_) && rubi_quadratic_match_q(&v_, x_))
        },
        rhs: {
            let recursive_integrand = rubi_expand_to_sum(&u_, x_).pow(&m_) * &pq__ * rubi_expand_to_sum(&v_, x_).pow(&p_);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_2085(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; p_, u_);
    rules.push(rubi_rule!(
        order: 2085,
        source: "Int[u_^p_,x_Symbol] :=
          Int[ExpandToSum[u,x]^p,x] /;
        FreeQ[p,x] && TrinomialQ[u,x] && Not[TrinomialMatchQ[u,x]]",
        desc: "Algebraic normalization",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [u_, p_, x_],
        when: { freeq!(p_, x_) && rubi_trinomial_q(&u_, x_) && !rubi_trinomial_match_q(&u_, x_) },
        rhs: {
            let recursive_integrand = rubi_expand_to_sum(&u_, x_).pow(&p_);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_2086(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; d__, m_, p_, u_, x_);
    rules.push(rubi_rule!(
        order: 2086,
        source: "Int[(d_.*x_)^m_.*u_^p_.,x_Symbol] :=
          Int[(d*x)^m*ExpandToSum[u,x]^p,x] /;
        FreeQ[{d,m,p},x] && TrinomialQ[u,x] && Not[TrinomialMatchQ[u,x]]",
        desc: "Algebraic normalization",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [d__, m_, u_, p_, x_],
        optional: [d__, m_, p_],
        when: {
            freeq!([d__, m_, p_], x_)
                && rubi_trinomial_q(&u_, x_)
                && !rubi_trinomial_match_q(&u_, x_)
        },
        rhs: {
            let recursive_integrand = (&d__ * x_).pow(&m_) * rubi_expand_to_sum(&u_, x_).pow(&p_);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_2087(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; p_, q_, u_, v_);
    rules.push(rubi_rule!(
        order: 2087,
        source: "Int[u_^q_.*v_^p_.,x_Symbol] :=
          Int[ExpandToSum[u,x]^q*ExpandToSum[v,x]^p,x] /;
        FreeQ[{p,q},x] && BinomialQ[u,x] && TrinomialQ[v,x] && Not[BinomialMatchQ[u,x] && TrinomialMatchQ[v,x]]",
        desc: "Algebraic normalization",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [u_, q_, v_, p_, x_],
        optional: [q_, p_],
        when: {
            freeq!([p_, q_], x_)
                && rubi_binomial_q(&u_, x_)
                && rubi_trinomial_q(&v_, x_)
                && !(rubi_binomial_match_q(&u_, x_) && rubi_trinomial_match_q(&v_, x_))
        },
        rhs: {
            let recursive_integrand = rubi_expand_to_sum(&u_, x_).pow(&q_) * rubi_expand_to_sum(&v_, x_).pow(&p_);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_2088(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; p_, q_, u_, v_);
    rules.push(rubi_rule!(
        order: 2088,
        source: "Int[u_^q_.*v_^p_.,x_Symbol] :=
          Int[ExpandToSum[u,x]^q*ExpandToSum[v,x]^p,x] /;
        FreeQ[{p,q},x] && BinomialQ[u,x] && BinomialQ[v,x] && Not[BinomialMatchQ[u,x] && BinomialMatchQ[v,x]]",
        desc: "Algebraic normalization",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [u_, q_, v_, p_, x_],
        optional: [q_, p_],
        when: {
            freeq!([p_, q_], x_)
                && rubi_binomial_q(&u_, x_)
                && rubi_binomial_q(&v_, x_)
                && !(rubi_binomial_match_q(&u_, x_) && rubi_binomial_match_q(&v_, x_))
        },
        rhs: {
            let recursive_integrand = rubi_expand_to_sum(&u_, x_).pow(&q_) * rubi_expand_to_sum(&v_, x_).pow(&p_);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_2089(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; f__, m_, p_, q_, u_, x_, z_);
    rules.push(rubi_rule!(
        order: 2089,
        source: "Int[(f_.*x_)^m_.*z_^q_.*u_^p_.,x_Symbol] :=
          Int[(f*x)^m*ExpandToSum[z,x]^q*ExpandToSum[u,x]^p,x] /;
        FreeQ[{f,m,p,q},x] && BinomialQ[z,x] && TrinomialQ[u,x] && Not[BinomialMatchQ[z,x] && TrinomialMatchQ[u,x]]",
        desc: "Algebraic normalization",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [f__, m_, z_, q_, u_, p_, x_],
        optional: [f__, m_, q_, p_],
        when: {
            freeq!([f__, m_, p_, q_], x_)
                && rubi_binomial_q(&z_, x_)
                && rubi_trinomial_q(&u_, x_)
                && !(rubi_binomial_match_q(&z_, x_) && rubi_trinomial_match_q(&u_, x_))
        },
        rhs: {
            let recursive_integrand =
                (&f__ * x_).pow(&m_) * rubi_expand_to_sum(&z_, x_).pow(&q_) * rubi_expand_to_sum(&u_, x_).pow(&p_);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_2090(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; f__, m_, p_, q_, u_, x_, z_);
    rules.push(rubi_rule!(
        order: 2090,
        source: "Int[(f_.*x_)^m_.*z_^q_.*u_^p_.,x_Symbol] :=
          Int[(f*x)^m*ExpandToSum[z,x]^q*ExpandToSum[u,x]^p,x] /;
        FreeQ[{f,m,p,q},x] && BinomialQ[z,x] && BinomialQ[u,x] && Not[BinomialMatchQ[z,x] && BinomialMatchQ[u,x]]",
        desc: "Algebraic normalization",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [f__, m_, z_, q_, u_, p_, x_],
        optional: [f__, m_, q_, p_],
        when: {
            freeq!([f__, m_, p_, q_], x_)
                && rubi_binomial_q(&z_, x_)
                && rubi_binomial_q(&u_, x_)
                && !(rubi_binomial_match_q(&z_, x_) && rubi_binomial_match_q(&u_, x_))
        },
        rhs: {
            let recursive_integrand =
                (&f__ * x_).pow(&m_) * rubi_expand_to_sum(&z_, x_).pow(&q_) * rubi_expand_to_sum(&u_, x_).pow(&p_);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_2091(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; p_, px__, q_, u_, z_);
    rules.push(rubi_rule!(
        order: 2091,
        source: "Int[Px_*z_^q_.*u_^p_.,x_Symbol] :=
          Int[Px*ExpandToSum[z,x]^q*ExpandToSum[u,x]^p,x] /;
        FreeQ[{p,q},x] && PolyQ[Px,x] && BinomialQ[z,x] && TrinomialQ[u,x] && Not[BinomialMatchQ[z,x] && TrinomialMatchQ[u,x]]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [px__, u_, p_, z_, q_, x_],
        optional: [p_, q_],
        x_free: [p_, q_],
        when: {
            freeq!([p_, q_], x_)
                && rubi_poly_q(&px__, x_)
                && rubi_binomial_q(&z_, x_)
                && rubi_trinomial_q(&u_, x_)
                && !(rubi_binomial_match_q(&z_, x_) && rubi_trinomial_match_q(&u_, x_))
        },
        rhs: {
            rubi_rhs_int(
                &(&px__
                    * rubi_expand_to_sum(&z_, x_).pow(&q_)
                    * rubi_expand_to_sum(&u_, x_).pow(&p_)),
                x_,
            )
        },
    ));
}

fn push_rules_rule_2092(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; p_, px__, q_, u_, z_);
    rules.push(rubi_rule!(
        order: 2092,
        source: "Int[Px_*z_^q_.*u_^p_.,x_Symbol] :=
          Int[Px*ExpandToSum[z,x]^q*ExpandToSum[u,x]^p,x] /;
        FreeQ[{p,q},x] && BinomialQ[z,x] && BinomialQ[u,x] && Not[BinomialMatchQ[z,x] && BinomialMatchQ[u,x]]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [px__, u_, p_, z_, q_, x_],
        optional: [p_, q_],
        x_free: [p_, q_],
        when: {
            freeq!([p_, q_], x_)
                && rubi_binomial_q(&z_, x_)
                && rubi_binomial_q(&u_, x_)
                && !(rubi_binomial_match_q(&z_, x_) && rubi_binomial_match_q(&u_, x_))
        },
        rhs: {
            rubi_rhs_int(
                &(&px__
                    * rubi_expand_to_sum(&z_, x_).pow(&q_)
                    * rubi_expand_to_sum(&u_, x_).pow(&p_)),
                x_,
            )
        },
    ));
}

fn push_rules_rule_2454(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; p_, pq__, u_);
    rules.push(rubi_rule!(
        order: 2454,
        source: "Int[Pq_*u_^p_.,x_Symbol] :=
          Int[Pq*ExpandToSum[u,x]^p,x] /;
        FreeQ[p,x] && PolyQ[Pq,x] && TrinomialQ[u,x] && Not[TrinomialMatchQ[u,x]]",
        desc: "Algebraic normalization",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [pq__, u_, p_, x_],
        optional: [p_],
        when: {
            freeq!(p_, x_)
                && rubi_poly_q(&pq__, x_)
                && rubi_trinomial_q(&u_, x_)
                && !rubi_trinomial_match_q(&u_, x_)
        },
        rhs: {
            let recursive_integrand = &pq__ * rubi_expand_to_sum(&u_, x_).pow(&p_);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_2455(rules: &mut Vec<RubiRule>) {
    rubi_symb!(d__, m_, p_, pq__, u_, x_);
    rules.push(rubi_rule!(
        order: 2455,
        source: "Int[(d_.*x_)^m_.*Pq_*u_^p_.,x_Symbol] :=
          Int[(d*x)^m*Pq*ExpandToSum[u,x]^p,x] /;
        FreeQ[{d,m,p},x] && PolyQ[Pq,x] && TrinomialQ[u,x] && Not[TrinomialMatchQ[u,x]]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: (d__ * x_).pow(m_) * pq__ * u_.pow(p_),
        with: [d__, m_, pq__, u_, p_, x_],
        optional: [d__, m_, p_],
        when: {
            freeq!([d__, m_, p_], x_)
                && rubi_poly_q(&pq__, x_)
                && rubi_trinomial_q(&u_, x_)
                && !rubi_trinomial_match_q(&u_, x_)
        },
        rhs: {
            let recursive_integrand = (&d__ * x_).pow(&m_) * &pq__ * rubi_expand_to_sum(&u_, x_).pow(&p_);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_2093(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; p_, u_);
    rules.push(rubi_rule!(
        order: 2093,
        source: "Int[u_^p_,x_Symbol] :=
          Int[ExpandToSum[u,x]^p,x] /;
        FreeQ[p,x] && GeneralizedTrinomialQ[u,x] && Not[GeneralizedTrinomialMatchQ[u,x]]",
        desc: "Algebraic normalization",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [u_, p_, x_],
        optional: [],
        when: {
            freeq!(p_, x_)
                && rubi_generalized_trinomial_q(&u_, x_)
                && !rubi_generalized_trinomial_match_q(&u_, x_)
        },
        rhs: {
            let recursive_integrand = rubi_expand_to_sum(&u_, x_).pow(&p_);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_2094(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; d__, m_, p_, u_, x_);
    rules.push(rubi_rule!(
        order: 2094,
        source: "Int[(d_.*x_)^m_.*u_^p_.,x_Symbol] :=
          Int[(d*x)^m*ExpandToSum[u,x]^p,x] /;
        FreeQ[{d,m,p},x] && GeneralizedTrinomialQ[u,x] && Not[GeneralizedTrinomialMatchQ[u,x]]",
        desc: "Algebraic normalization",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [d__, m_, u_, p_, x_],
        optional: [d__, m_, p_],
        when: {
            freeq!([d__, m_, p_], x_)
                && rubi_generalized_trinomial_q(&u_, x_)
                && !rubi_generalized_trinomial_match_q(&u_, x_)
        },
        rhs: {
            let recursive_integrand = (&d__ * x_).pow(&m_) * rubi_expand_to_sum(&u_, x_).pow(&p_);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_2095(rules: &mut Vec<RubiRule>) {
    rubi_symb!(p_, u_, z_);
    rules.push(rubi_rule!(
        order: 2095,
        source: "Int[z_*u_^p_.,x_Symbol] :=
          Int[ExpandToSum[z,x]*ExpandToSum[u,x]^p,x] /;
        FreeQ[p,x] && BinomialQ[z,x] && GeneralizedTrinomialQ[u,x] &&
          EqQ[BinomialDegree[z,x]-GeneralizedTrinomialDegree[u,x],0] && Not[BinomialMatchQ[z,x] && GeneralizedTrinomialMatchQ[u,x]]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: z_ * u_.pow(p_),
        with: [z_, u_, p_, x_],
        optional: [p_],
        when: {
            let z_degree = rubi_binomial_degree(&z_, x_);
            let u_degree = rubi_generalized_trinomial_degree(&u_, x_);

            freeq!(p_, x_)
                && rubi_binomial_q(&z_, x_)
                && rubi_generalized_trinomial_q(&u_, x_)
                && matches!((z_degree, u_degree), (Some(z_degree), Some(u_degree)) if eqq!(&z_degree - &u_degree, 0))
                && !(rubi_binomial_match_q(&z_, x_) && rubi_generalized_trinomial_match_q(&u_, x_))
        },
        rhs: {
            let recursive_integrand = rubi_expand_to_sum(&z_, x_) * rubi_expand_to_sum(&u_, x_).pow(&p_);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_2096(rules: &mut Vec<RubiRule>) {
    rubi_symb!(f__, m_, p_, u_, x_, z_);
    rules.push(rubi_rule!(
        order: 2096,
        source: "Int[(f_.*x_)^m_.*z_*u_^p_.,x_Symbol] :=
          Int[(f*x)^m*ExpandToSum[z,x]*ExpandToSum[u,x]^p,x] /;
        FreeQ[{f,m,p},x] && BinomialQ[z,x] && GeneralizedTrinomialQ[u,x] &&
          EqQ[BinomialDegree[z,x]-GeneralizedTrinomialDegree[u,x],0] && Not[BinomialMatchQ[z,x] && GeneralizedTrinomialMatchQ[u,x]]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: (f__ * x_).pow(m_) * z_ * u_.pow(p_),
        with: [f__, m_, z_, u_, p_, x_],
        optional: [f__, m_, p_],
        when: {
            let z_degree = rubi_binomial_degree(&z_, x_);
            let u_degree = rubi_generalized_trinomial_degree(&u_, x_);

            freeq!([f__, m_, p_], x_)
                && rubi_binomial_q(&z_, x_)
                && rubi_generalized_trinomial_q(&u_, x_)
                && matches!((z_degree, u_degree), (Some(z_degree), Some(u_degree)) if eqq!(&z_degree - &u_degree, 0))
                && !(rubi_binomial_match_q(&z_, x_) && rubi_generalized_trinomial_match_q(&u_, x_))
        },
        rhs: {
            let recursive_integrand =
                (&f__ * x_).pow(&m_) * rubi_expand_to_sum(&z_, x_) * rubi_expand_to_sum(&u_, x_).pow(&p_);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

// Generated shared pattern builders.

#[inline(never)]
fn rubi_shared_pattern_0(symbols: &RubiSymbols) -> Atom {
    let c__ = symbols.c__;
    let m_ = symbols.m_;
    let p_ = symbols.p_;
    let u_ = symbols.u_;
    let x_ = symbols.x_;
    (c__ * x_).pow(m_) * u_.pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let d__ = symbols.d__;
    let m_ = symbols.m_;
    let p_ = symbols.p_;
    let u_ = symbols.u_;
    let x_ = symbols.x_;
    (d__ * x_).pow(m_) * u_.pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_2(symbols: &RubiSymbols) -> Atom {
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let p_ = symbols.p_;
    let q_ = symbols.q_;
    let u_ = symbols.u_;
    let x_ = symbols.x_;
    let z_ = symbols.z_;
    (f__ * x_).pow(m_) * z_.pow(q_) * u_.pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_3(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let fx__ = symbols.fx__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let v__ = symbols.v__;
    fx__ * (a__ * v__).pow(m_) * (b__ * v__).pow(n_)
}

#[inline(never)]
fn rubi_shared_pattern_4(symbols: &RubiSymbols) -> Atom {
    let p_ = symbols.p_;
    let pq__ = symbols.pq__;
    let u_ = symbols.u_;
    pq__ * u_.pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_5(symbols: &RubiSymbols) -> Atom {
    let p_ = symbols.p_;
    let px__ = symbols.px__;
    let q_ = symbols.q_;
    let u_ = symbols.u_;
    let z_ = symbols.z_;
    px__ * u_.pow(p_) * z_.pow(q_)
}

#[inline(never)]
fn rubi_shared_pattern_6(symbols: &RubiSymbols) -> Atom {
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let u_ = symbols.u_;
    let v_ = symbols.v_;
    let w_ = symbols.w_;
    u_.pow(m_) * v_.pow(n_) * w_.pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_7(symbols: &RubiSymbols) -> Atom {
    let p_ = symbols.p_;
    let u_ = symbols.u_;
    u_.pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_8(symbols: &RubiSymbols) -> Atom {
    let p_ = symbols.p_;
    let q_ = symbols.q_;
    let u_ = symbols.u_;
    let v_ = symbols.v_;
    u_.pow(p_) * v_.pow(q_)
}

#[inline(never)]
fn rubi_shared_pattern_9(symbols: &RubiSymbols) -> Atom {
    let p_ = symbols.p_;
    let q_ = symbols.q_;
    let u_ = symbols.u_;
    let v_ = symbols.v_;
    u_.pow(q_) * v_.pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_10(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c_ = symbols.c_;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let q_ = symbols.q_;
    let u__ = symbols.u__;
    let x_ = symbols.x_;
    u__ * (e__ * (a__ + b__ * x_.pow(n_)).pow(q_) * (c_ + d__ * x_.pow(n_)).pow(q_)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_11(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c_ = symbols.c_;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let u__ = symbols.u__;
    let x_ = symbols.x_;
    u__ * (e__ * (a__ + b__ * x_.pow(n_)) / (c_ + d__ * x_.pow(n_))).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_12(symbols: &RubiSymbols) -> Atom {
    let px_ = symbols.px_;
    let u__ = symbols.u__;
    u__ * px_
}

#[inline(never)]
fn rubi_shared_pattern_13(symbols: &RubiSymbols) -> Atom {
    let p_ = symbols.p_;
    let px_ = symbols.px_;
    let u__ = symbols.u__;
    u__ * px_.pow(p_)
}
