use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_2998(rules);
    push_rules_rule_2999(rules);
    push_rules_rule_3000(rules);
    push_rules_rule_3001(rules);
    push_rules_rule_3002(rules);
    push_rules_rule_3003(rules);
    push_rules_rule_3004(rules);
    push_rules_rule_3005(rules);
    push_rules_rule_3006(rules);
    push_rules_rule_3007(rules);
    push_rules_rule_3008(rules);
    push_rules_rule_3009(rules);
    push_rules_rule_3010(rules);
    push_rules_rule_3011(rules);
    push_rules_rule_3012(rules);
    push_rules_rule_3013(rules);
    push_rules_rule_3014(rules);
    push_rules_rule_3015(rules);
    push_rules_rule_3016(rules);
    push_rules_rule_3017(rules);
    push_rules_rule_3018(rules);
    push_rules_rule_3019(rules);
    push_rules_rule_3020(rules);
    push_rules_rule_3021(rules);
    push_rules_rule_3022(rules);
    push_rules_rule_3023(rules);
    push_rules_rule_3024(rules);
    push_rules_rule_3025(rules);
    push_rules_rule_3026(rules);
    push_rules_rule_3027(rules);
    push_rules_rule_3028(rules);
    push_rules_rule_3029(rules);
    push_rules_rule_3030(rules);
    push_rules_rule_3031(rules);
    push_rules_rule_3032(rules);
    push_rules_rule_3033(rules);
    push_rules_rule_3034(rules);
    push_rules_rule_3035(rules);
    push_rules_rule_3036(rules);
    push_rules_rule_3037(rules);
    push_rules_rule_3038(rules);
    push_rules_rule_3039(rules);
    push_rules_rule_3040(rules);
    push_rules_rule_3041(rules);
}

fn push_rules_rule_2998(rules: &mut Vec<RubiRule>) {
    rubi_symb!(u__, v__);
    let rule = rubi_rule!(
        order: 2998,
        source: "Int[u_*Log[v_],x_Symbol] :=
          With[{w=DerivativeDivides[v,u*(1-v),x]},
          w*PolyLog[2,1-v] /;
         Not[FalseQ[w]]]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern: u__ * Atom::var(v__).log(),
        with: [u__, v__, x_],
        when: { rubi_derivative_divides(&v__, &(&u__ * (Atom::num(1) - &v__)), x_).is_some() },
        rhs: {
            let w = rubi_derivative_divides(&v__, &(&u__ * (Atom::num(1) - &v__)), x_).rubi_rhs();

            rubi_simp(&(w * (Atom::num(1) - &v__).polylog(2)), x_)
        },
    );
    rules.push(rule.with_early_x_dependent(v__));
}

fn push_rules_rule_2999(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, u__, v__, w__);
    let rule = rubi_rule!(
        order: 2999,
        source: "Int[(a_.+b_.*Log[u_])*Log[v_]*w_,x_Symbol] :=
          With[{z=DerivativeDivides[v,w*(1-v),x]},
          z*(a+b*Log[u])*PolyLog[2,1-v] -
          b \\[Star] Int[SimplifyIntegrand[z*PolyLog[2,1-v]*D[u,x]/u,x],x] /;
         Not[FalseQ[z]]] /;
        FreeQ[{a,b},x] && InverseFunctionFreeQ[u,x]",
        desc: "Integration by parts",
        refs: [],
        pattern: (a__ + b__ * Atom::var(u__).log()) * Atom::var(v__).log() * w__,
        with: [a__, b__, u__, v__, w__, x_],
        optional: [a__, b__],
        when: {
            freeq!([a__, b__], x_)
                && rubi_inverse_function_free_q(&u__, x_)
                && rubi_derivative_divides(&v__, &(&w__ * (Atom::num(1) - &v__)), x_).is_some()
        },
        rhs: {
            let z = rubi_derivative_divides(&v__, &(&w__ * (Atom::num(1) - &v__)), x_).rubi_rhs();
            let logarithmic = &a__ + &b__ * u__.log();
            let polylogarithm = (Atom::num(1) - &v__).polylog(2);
            let recursive_integrand =
                rubi_simplify_integrand(&(&z * &polylogarithm * rubi_d(&u__, x_) / &u__), x_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(z * logarithmic * polylogarithm), x_)
                    - rubi_star(b__, recursive)
        },
    );
    rules.push(rule.with_early_x_dependent(v__));
}

fn push_rules_rule_3000(rules: &mut Vec<RubiRule>) {
    rubi_symb!(c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3000,
        source: "Int[Log[c_.*Log[d_.*x_^n_.]^p_.],x_Symbol] :=
          x*Log[c*Log[d*x^n]^p] - n*p \\[Star] Int[1/Log[d*x^n],x] /;
        FreeQ[{c,d,n,p},x]",
        desc: "Integration by parts",
        refs: [],
        pattern: (c__ * (d__ * x_.pow(n_)).log().pow(p_)).log(),
        with: [c__, d__, n_, p_, x_],
        optional: [c__, d__, n_, p_],
        when: { freeq!([c__, d__, n_, p_], x_) },
        rhs: {
            let logarithmic = (&c__ * (&d__ * x_.pow(&n_)).log().pow(&p_)).log();
            let recursive_integrand = Atom::num(1) / (&d__ * x_.pow(&n_)).log();
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(x_ * logarithmic), x_)
                    - rubi_star(&n_ * &p_, recursive)
        },
    ));
}

fn push_rules_rule_3001(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3001,
        source: "Int[(a_.+b_.*Log[c_.*Log[d_.*x_^n_.]^p_.])/x_,x_Symbol] :=
          Log[d*x^n]*(a+b*Log[c*Log[d*x^n]^p])/n - b*p*Log[x] /;
        FreeQ[{a,b,c,d,n,p},x]",
        desc: "Integration by parts",
        refs: [],
        pattern: (a__ + b__ * (c__ * (d__ * x_.pow(n_)).log().pow(p_)).log()) / x_,
        with: [a__, b__, c__, d__, n_, p_, x_],
        optional: [a__, b__, c__, d__, n_, p_],
        when: { freeq!([a__, b__, c__, d__, n_, p_], x_) },
        rhs: {
            let inner_log = (&d__ * x_.pow(&n_)).log();
            let logarithmic = &a__ + &b__ * (&c__ * inner_log.pow(&p_)).log();

            rubi_simp(&(inner_log * logarithmic / &n_), x_)
                    - rubi_simp(&(&b__ * &p_ * x_.log()), x_)
        },
    ));
}

fn push_rules_rule_3002(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3002,
        source: "Int[(e_.*x_)^m_.*(a_.+b_.*Log[c_.*Log[d_.*x_^n_.]^p_.]),x_Symbol] :=
          (e*x)^(m+1)*(a+b*Log[c*Log[d*x^n]^p])/(e*(m+1)) - b*n*p/(m+1) \\[Star] Int[(e*x)^m/Log[d*x^n],x] /;
        FreeQ[{a,b,c,d,e,m,n,p},x] && NeQ[m,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern: (e__ * x_).pow(m_) * (a__ + b__ * (c__ * (d__ * x_.pow(n_)).log().pow(p_)).log()),
        with: [e__, m_, a__, b__, c__, d__, n_, p_, x_],
        optional: [e__, m_, a__, b__, c__, d__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_, p_], x_)
                && neq!(m_, -1)
        },
        rhs: {
            let scaled = &e__ * x_;
            let logarithmic =
                &a__ + &b__ * (&c__ * (&d__ * x_.pow(&n_)).log().pow(&p_)).log();
            let recursive_integrand = scaled.pow(&m_) / (&d__ * x_.pow(&n_)).log();
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(
                    &(scaled.pow(&m_ + 1) * logarithmic / (&e__ * (&m_ + 1))),
                    x_,
                ) - rubi_star(&b__ * &n_ * &p_ / (&m_ + 1), recursive)
        },
    ));
}

fn push_rules_rule_3003(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, n_, p_, rfx__);
    rules.push(rubi_rule!(
        order: 3003,
        source: "Int[(a_.+b_.*Log[c_.*RFx_^p_.])^n_.,x_Symbol] :=
          x*(a+b*Log[c*RFx^p])^n -
          b*n*p \\[Star] Int[SimplifyIntegrand[x*(a+b*Log[c*RFx^p])^(n-1)*D[RFx,x]/RFx,x],x] /;
        FreeQ[{a,b,c,p},x] && RationalFunctionQ[RFx,x] && IGtQ[n,0]",
        desc: "Integration by parts",
        refs: [],
        pattern: (a__ + b__ * (c__ * rfx__.pow(p_)).log()).pow(n_),
        with: [a__, b__, c__, rfx__, p_, n_, x_],
        optional: [a__, b__, c__, p_, n_],
        when: {
            freeq!([a__, b__, c__, p_], x_) && rubi_rational_function_q(&rfx__, x_) && igtq!(n_, 0)
        },
        rhs: {
            let logarithmic = &a__ + &b__ * (&c__ * rfx__.pow(&p_)).log();
            let recursive_integrand = rubi_simplify_integrand(
                &(x_ * logarithmic.pow(&n_ - 1) * rubi_d(&rfx__, x_) / &rfx__),
                x_,
            );
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(x_ * logarithmic.pow(&n_)), x_)
                    - rubi_star(&b__ * &n_ * &p_, recursive)
        },
    ));
}

fn push_rules_rule_3004(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, n_, p_, rfx__, x_);
    rules.push(rubi_rule!(
        order: 3004,
        source: "Int[(a_.+b_.*Log[c_.*RFx_^p_.])^n_./(d_.+e_.*x_),x_Symbol] :=
          Log[d+e*x]*(a+b*Log[c*RFx^p])^n/e -
          b*n*p/e \\[Star] Int[Log[d+e*x]*(a+b*Log[c*RFx^p])^(n-1)*D[RFx,x]/RFx,x] /;
        FreeQ[{a,b,c,d,e,p},x] && RationalFunctionQ[RFx,x] && IGtQ[n,0]",
        desc: "Integration by parts",
        refs: [],
        pattern: (a__ + b__ * (c__ * rfx__.pow(p_)).log()).pow(n_) / (d__ + e__ * x_),
        with: [a__, b__, c__, rfx__, p_, n_, d__, e__, x_],
        optional: [a__, b__, c__, p_, n_, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__, p_], x_)
                && rubi_rational_function_q(&rfx__, x_)
                && igtq!(n_, 0)
        },
        rhs: {
            let affine = &d__ + &e__ * x_;
            let logarithmic = &a__ + &b__ * (&c__ * rfx__.pow(&p_)).log();
            let recursive_integrand =
                affine.log() * logarithmic.pow(&n_ - 1) * rubi_d(&rfx__, x_) / &rfx__;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(affine.log() * logarithmic.pow(&n_) / &e__), x_)
                    - rubi_star(&b__ * &n_ * &p_ / &e__, recursive)
        },
    ));
}

fn push_rules_rule_3005(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, n_, p_, rfx__, x_);
    rules.push(rubi_rule!(
        order: 3005,
        source: "Int[(d_.+e_.*x_)^m_.*(a_.+b_.*Log[c_.*RFx_^p_.])^n_.,x_Symbol] :=
          (d+e*x)^(m+1)*(a+b*Log[c*RFx^p])^n/(e*(m+1)) -
          b*n*p/(e*(m+1)) \\[Star] Int[SimplifyIntegrand[(d+e*x)^(m+1)*(a+b*Log[c*RFx^p])^(n-1)*D[RFx,x]/RFx,x],x] /;
        FreeQ[{a,b,c,d,e,m,p},x] && RationalFunctionQ[RFx,x] && IGtQ[n,0] && (EqQ[n,1] || IntegerQ[m]) && NeQ[m,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern: (d__ + e__ * x_).pow(m_) * (a__ + b__ * (c__ * rfx__.pow(p_)).log()).pow(n_),
        with: [d__, e__, m_, a__, b__, c__, rfx__, p_, n_, x_],
        optional: [d__, e__, m_, a__, b__, c__, p_, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, p_], x_)
                && rubi_rational_function_q(&rfx__, x_)
                && igtq!(n_, 0)
                && (eqq!(n_, 1) || integerq!(m_))
                && neq!(m_, -1)
        },
        rhs: {
            let affine = &d__ + &e__ * x_;
            let logarithmic = &a__ + &b__ * (&c__ * rfx__.pow(&p_)).log();
            let recursive_integrand = rubi_simplify_integrand(
                &(affine.pow(&m_ + 1) * logarithmic.pow(&n_ - 1) * rubi_d(&rfx__, x_) / &rfx__),
                x_,
            );
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(
                    &(affine.pow(&m_ + 1) * logarithmic.pow(&n_) / (&e__ * (&m_ + 1))),
                    x_,
                ) - rubi_star(&b__ * &n_ * &p_ / (&e__ * (&m_ + 1)), recursive)
        },
    ));
}

fn push_rules_rule_3006(rules: &mut Vec<RubiRule>) {
    rubi_symb!(c__, d__, e__, n_, rfx__, x_);
    rules.push(rubi_rule!(
        order: 3006,
        source: "Int[Log[c_.*RFx_^n_.]/(d_+e_.*x_^2),x_Symbol] :=
          With[{u=IntHide[1/(d+e*x^2),x]},
          u*Log[c*RFx^n] - n \\[Star] Int[SimplifyIntegrand[u*D[RFx,x]/RFx,x],x]] /;
        FreeQ[{c,d,e,n},x] && RationalFunctionQ[RFx,x] && Not[PolynomialQ[RFx,x]]",
        desc: "Integration by parts",
        refs: [],
        pattern: (c__ * rfx__.pow(n_)).log() / (d__ + e__ * x_.pow(2)),
        with: [c__, rfx__, n_, d__, e__, x_],
        optional: [c__, n_, e__],
        when: {
            freeq!([c__, d__, e__, n_], x_)
                && rubi_rational_function_q(&rfx__, x_)
                && !rubi_polynomial_q(&rfx__, x_)
        },
        rhs: {
            let u = rubi_int_hide(&(Atom::num(1) / (&d__ + &e__ * x_.pow(2))), x_).rubi_rhs();
            let logarithmic = (&c__ * rfx__.pow(&n_)).log();
            let recursive_integrand =
                rubi_simplify_integrand(&(&u * rubi_d(&rfx__, x_) / &rfx__), x_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(&u * logarithmic), x_) - rubi_star(n_, recursive)
        },
    ));
}

fn push_rules_rule_3007(rules: &mut Vec<RubiRule>) {
    rubi_symb!(c__, n_, px__, qx__);
    rules.push(rubi_rule!(
        order: 3007,
        source: "Int[Log[c_.*Px_^n_.]/Qx_,x_Symbol] :=
          With[{u=IntHide[1/Qx,x]},
          u*Log[c*Px^n] - n \\[Star] Int[SimplifyIntegrand[u*D[Px,x]/Px,x],x]] /;
        FreeQ[{c,n},x] && QuadraticQ[{Qx,Px},x] && EqQ[D[Px/Qx,x],0]",
        desc: "Integration by parts",
        refs: [],
        pattern: (c__ * px__.pow(n_)).log() / qx__,
        with: [c__, px__, n_, qx__, x_],
        optional: [c__, n_],
        when: {
            freeq!([c__, n_], x_)
                && rubi_quadratic_q_list(&[&qx__, &px__], x_)
                && eqq!(rubi_d(&(&px__ / &qx__), x_), 0)
        },
        rhs: {
            let u = rubi_int_hide(&(Atom::num(1) / &qx__), x_).rubi_rhs();
            let logarithmic = (&c__ * px__.pow(&n_)).log();
            let recursive_integrand =
                rubi_simplify_integrand(&(&u * rubi_d(&px__, x_) / &px__), x_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(&u * logarithmic), x_) - rubi_star(n_, recursive)
        },
    ));
}

fn push_rules_rule_3008(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, n_, p_, rfx__, rgx__);
    rules.push(rubi_rule!(
        order: 3008,
        source: "Int[RGx_*(a_.+b_.*Log[c_.*RFx_^p_.])^n_.,x_Symbol] :=
          With[{u=ExpandIntegrand[(a+b*Log[c*RFx^p])^n,RGx,x]},
          Int[u,x] /;
         SumQ[u]] /;
        FreeQ[{a,b,c,p},x] && RationalFunctionQ[RFx,x] && RationalFunctionQ[RGx,x] && IGtQ[n,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [rgx__, a__, b__, c__, rfx__, p_, n_, x_],
        optional: [a__, b__, c__, p_, n_],
        when: {
            freeq!([a__, b__, c__, p_], x_)
                && rubi_rational_function_q(&rfx__, x_)
                && rubi_rational_function_q(&rgx__, x_)
                && igtq!(n_, 0)
                && rubi_expand_integrand_product_sum(
                    &(&a__ + &b__ * (&c__ * rfx__.pow(&p_)).log()).pow(&n_),
                    &rgx__,
                    x_,
                )
                .is_some()
        },
        rhs: {
            let u = rubi_expand_integrand_product_sum(
                &(&a__ + &b__ * (&c__ * rfx__.pow(&p_)).log()).pow(&n_),
                &rgx__,
                x_,
            )
            .expect("when clause should ensure expanded integrand is a sum");

            rubi_rhs_int(&u, x_)
        },
    ));
}

fn push_rules_rule_3009(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, n_, p_, rfx__, rgx__);
    rules.push(rubi_rule!(
        order: 3009,
        source: "Int[RGx_*(a_.+b_.*Log[c_.*RFx_^p_.])^n_.,x_Symbol] :=
          With[{u=ExpandIntegrand[RGx*(a+b*Log[c*RFx^p])^n,x]},
          Int[u,x] /;
         SumQ[u]] /;
        FreeQ[{a,b,c,p},x] && RationalFunctionQ[RFx,x] && RationalFunctionQ[RGx,x] && IGtQ[n,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [rgx__, a__, b__, c__, rfx__, p_, n_, x_],
        optional: [a__, b__, c__, p_, n_],
        when: {
            freeq!([a__, b__, c__, p_], x_)
                && rubi_rational_function_q(&rfx__, x_)
                && rubi_rational_function_q(&rgx__, x_)
                && igtq!(n_, 0)
                && rubi_expand_integrand_sum(
                    &(&rgx__ * (&a__ + &b__ * (&c__ * rfx__.pow(&p_)).log()).pow(&n_)),
                    x_,
                )
                .is_some()
        },
        rhs: {
            let u = rubi_expand_integrand_sum(
                &(&rgx__ * (&a__ + &b__ * (&c__ * rfx__.pow(&p_)).log()).pow(&n_)),
                x_,
            )
            .expect("when clause should ensure expanded integrand is a sum");

            rubi_rhs_int(&u, x_)
        },
    ));
}

fn push_rules_rule_3010(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, rfx__, u__);
    rules.push(rubi_rule!(
        order: 3010,
        source: "Int[RFx_*(a_.+b_.*Log[u_]),x_Symbol] :=
          With[{lst=SubstForFractionalPowerOfLinear[RFx*(a+b*Log[u]),x]},
          lst[[2]]*lst[[4]] \\[Star] Subst[Int[lst[[1]],x],x,lst[[3]]^(1/lst[[2]])] /;
         Not[FalseQ[lst]]] /;
        FreeQ[{a,b},x] && RationalFunctionQ[RFx,x]",
        desc: "Integration by substitution",
        refs: [],
        pattern: rfx__ * (a__ + b__ * Atom::var(u__).log()),
        with: [rfx__, a__, b__, u__, x_],
        optional: [a__, b__],
        when: {
            freeq!([a__, b__], x_)
                && rubi_rational_function_q(&rfx__, x_)
                && {
                    let substitution_guard = fresh_substitution_symbol().unwrap();
                    rubi_subst_for_fractional_power_of_linear(
                        &(&rfx__ * (&a__ + &b__ * u__.log())),
                        x_,
                        substitution_guard.symbol(),
                    )
                    .is_some()
                }
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let lst = rubi_subst_for_fractional_power_of_linear(
                &(&rfx__ * (&a__ + &b__ * u__.log())),
                x_,
                substitution_symbol,
            ).rubi_rhs();
            let transformed_primitive = rubi_rhs_int(&lst.integrand, substitution_symbol);
            let substitution = lst.base.pow(Atom::num(1) / Atom::num(lst.denominator));
            let substituted = rubi_subst(
                &transformed_primitive,
                substitution_symbol,
                substitution,
            );

            rubi_star(Atom::num(lst.denominator) * lst.multiplier, substituted)
        },
    ));
}

fn push_rules_rule_3011(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, e__, f__, g__, capital_f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 3011,
        source: "Int[(f_.+g_.*x_)^m_.*Log[1+e_.*(F_^(c_.*(a_.+b_.*x_)))^n_.],x_Symbol] :=
          -(f+g*x)^m*PolyLog[2,-e*(F^(c*(a+b*x)))^n]/(b*c*n*Log[F]) +
          g*m/(b*c*n*Log[F]) \\[Star] Int[(f+g*x)^(m-1)*PolyLog[2,-e*(F^(c*(a+b*x)))^n],x] /;
        FreeQ[{F,a,b,c,e,f,g,n},x] && GtQ[m,0]",
        desc: "Integration by parts",
        refs: [],
        pattern: (f__ + g__ * x_).pow(m_)
            * (Atom::num(1) + e__ * capital_f__.pow(c__ * (a__ + b__ * x_)).pow(n_)).log(),
        with: [f__, g__, m_, e__, capital_f__, c__, a__, b__, n_, x_],
        optional: [f__, g__, m_, e__, c__, a__, b__, n_],
        when: {
            freeq!([capital_f__, a__, b__, c__, e__, f__, g__, n_], x_)
                && gtq!(m_, 0)
        },
        rhs: {
            let affine = &f__ + &g__ * x_;
            let exponential = capital_f__.pow(&c__ * (&a__ + &b__ * x_)).pow(&n_);
            let polylogarithm = (-&e__ * exponential).polylog(2);
            let denominator = &b__ * &c__ * &n_ * capital_f__.log();
            let recursive_integrand = affine.pow(&m_ - 1) * &polylogarithm;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(-affine.pow(&m_) * polylogarithm / &denominator), x_)
                    + rubi_star(&g__ * &m_ / denominator, recursive)
        },
    ));
}

fn push_rules_rule_3012(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, capital_f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 3012,
        source: "Int[(f_.+g_.*x_)^m_.*Log[d_+e_.*(F_^(c_.*(a_.+b_.*x_)))^n_.],x_Symbol] :=
          (f+g*x)^(m+1)*Log[d+e*(F^(c*(a+b*x)))^n]/(g*(m+1)) -
          (f+g*x)^(m+1)*Log[1+e/d*(F^(c*(a+b*x)))^n]/(g*(m+1)) +
          Int[(f+g*x)^m*Log[1+e/d*(F^(c*(a+b*x)))^n],x] /;
        FreeQ[{F,a,b,c,d,e,f,g,n},x] && GtQ[m,0] && NeQ[d,1]",
        desc: "Integration by parts",
        refs: [],
        pattern: (f__ + g__ * x_).pow(m_)
            * (d__ + e__ * capital_f__.pow(c__ * (a__ + b__ * x_)).pow(n_)).log(),
        with: [f__, g__, m_, d__, e__, capital_f__, c__, a__, b__, n_, x_],
        optional: [f__, g__, m_, e__, c__, a__, b__, n_],
        when: {
            freeq!([capital_f__, a__, b__, c__, d__, e__, f__, g__, n_], x_)
                && gtq!(m_, 0)
                && neq!(d__, 1)
        },
        rhs: {
            let affine = &f__ + &g__ * x_;
            let exponential = capital_f__.pow(&c__ * (&a__ + &b__ * x_)).pow(&n_);
            let logarithmic = (&d__ + &e__ * &exponential).log();
            let normalized_logarithmic = (Atom::num(1) + &e__ * &exponential / &d__).log();
            let recursive_integrand = affine.pow(&m_) * &normalized_logarithmic;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let denominator = &g__ * (&m_ + 1);

            rubi_simp(
                    &(affine.pow(&m_ + 1) * logarithmic / &denominator),
                    x_,
                ) + recursive
                    - rubi_simp(
                        &(affine.pow(&m_ + 1) * normalized_logarithmic / &denominator),
                        x_,
                    )
        },
    ));
}

fn push_rules_rule_3013(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 3013,
        source: "Int[Log[d_.+e_.*x_+f_.*Sqrt[a_.+b_.*x_+c_.*x_^2]],x_Symbol] :=
          x*Log[d+e*x+f*Sqrt[a+b*x+c*x^2]] +
          f^2*(b^2-4*a*c)/2 \\[Star] Int[x/((2*d*e-b*f^2)*(a+b*x+c*x^2)-f*(b*d-2*a*e+(2*c*d-b*e)*x)*Sqrt[a+b*x+c*x^2]),x] /;
        FreeQ[{a,b,c,d,e,f},x] && EqQ[e^2-c*f^2,0]",
        desc: "Integration by parts and algebraic simplification",
        refs: [],
        pattern: (d__ + e__ * x_ + f__ * (a__ + b__ * x_ + c__ * x_.pow(2)).sqrt()).log(),
        with: [d__, e__, f__, a__, b__, c__, x_],
        optional: [d__, e__, f__, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && eqq!(e__.pow(2) - &c__ * f__.pow(2), 0)
        },
        rhs: {
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let radical = quadratic.sqrt();
            let logarithmic = (&d__ + &e__ * x_ + &f__ * &radical).log();
            let recursive_coefficient = f__.pow(2) * (&b__.pow(2) - Atom::num(4) * &a__ * &c__)
                / Atom::num(2);

            let denominator =
                (Atom::num(2) * &d__ * &e__ - &b__ * f__.pow(2)) * &quadratic
                    - &f__
                        * (&b__ * &d__ - Atom::num(2) * &a__ * &e__
                            + (Atom::num(2) * &c__ * &d__ - &b__ * &e__) * x_)
                        * &radical;
            let recursive = rubi_rhs_int(&(x_ / denominator), x_);

            rubi_simp(&(x_ * logarithmic), x_)
                    + rubi_star(recursive_coefficient, recursive)
        },
    ));
}

fn push_rules_rule_3014(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 3014,
        source: "Int[Log[d_.+e_.*x_+f_.*Sqrt[a_.+c_.*x_^2]],x_Symbol] :=
          x*Log[d+e*x+f*Sqrt[a+c*x^2]] -
          a*c*f^2 \\[Star] Int[x/(d*e*(a+c*x^2)+f*(a*e-c*d*x)*Sqrt[a+c*x^2]),x] /;
        FreeQ[{a,c,d,e,f},x] && EqQ[e^2-c*f^2,0]",
        desc: "Integration by parts and algebraic simplification",
        refs: [],
        pattern: (d__ + e__ * x_ + f__ * (a__ + c__ * x_.pow(2)).sqrt()).log(),
        with: [d__, e__, f__, a__, c__, x_],
        optional: [d__, e__, f__, a__, c__],
        when: {
            freeq!([a__, c__, d__, e__, f__], x_)
                && eqq!(e__.pow(2) - &c__ * f__.pow(2), 0)
        },
        rhs: {
            let quadratic = &a__ + &c__ * x_.pow(2);
            let radical = quadratic.sqrt();
            let logarithmic = (&d__ + &e__ * x_ + &f__ * &radical).log();
            let recursive_coefficient = -&a__ * &c__ * f__.pow(2);

            let denominator = &d__ * &e__ * &quadratic
                + &f__ * (&a__ * &e__ - &c__ * &d__ * x_) * &radical;
            let recursive = rubi_rhs_int(&(x_ / denominator), x_);

            rubi_simp(&(x_ * logarithmic), x_)
                    + rubi_star(recursive_coefficient, recursive)
        },
    ));
}

fn push_rules_rule_3015(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, m_, x_);
    rules.push(rubi_rule!(
        order: 3015,
        source: "Int[(g_.*x_)^m_.*Log[d_.+e_.*x_+f_.*Sqrt[a_.+b_.*x_+c_.*x_^2]],x_Symbol] :=
          (g*x)^(m+1)*Log[d+e*x+f*Sqrt[a+b*x+c*x^2]]/(g*(m+1)) +
          f^2*(b^2-4*a*c)/(2*g*(m+1)) \\[Star] Int[(g*x)^(m+1)/((2*d*e-b*f^2)*(a+b*x+c*x^2)-f*(b*d-2*a*e+(2*c*d-b*e)*x)*Sqrt[a+b*x+c*x^2]),x] /;
        FreeQ[{a,b,c,d,e,f,g,m},x] && EqQ[e^2-c*f^2,0] && NeQ[m,-1] && IntegerQ[2*m]",
        desc: "Integration by parts and algebraic simplification",
        refs: [],
        pattern: (g__ * x_).pow(m_)
            * (d__ + e__ * x_ + f__ * (a__ + b__ * x_ + c__ * x_.pow(2)).sqrt()).log(),
        with: [g__, m_, d__, e__, f__, a__, b__, c__, x_],
        optional: [g__, m_, d__, e__, f__, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, m_], x_)
                && eqq!(e__.pow(2) - &c__ * f__.pow(2), 0)
                && neq!(m_, -1)
                && integerq!(Atom::num(2) * &m_)
        },
        rhs: {
            let scaled = &g__ * x_;
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let radical = quadratic.sqrt();
            let logarithmic = (&d__ + &e__ * x_ + &f__ * &radical).log();
            let denominator_coefficient = &g__ * (&m_ + 1);
            let recursive_coefficient = f__.pow(2)
                * (&b__.pow(2) - Atom::num(4) * &a__ * &c__)
                / (Atom::num(2) * &denominator_coefficient);

            let denominator =
                (Atom::num(2) * &d__ * &e__ - &b__ * f__.pow(2)) * &quadratic
                    - &f__
                        * (&b__ * &d__ - Atom::num(2) * &a__ * &e__
                            + (Atom::num(2) * &c__ * &d__ - &b__ * &e__) * x_)
                        * &radical;
            let recursive = rubi_rhs_int(&(scaled.pow(&m_ + 1) / denominator), x_);

            rubi_simp(
                    &(scaled.pow(&m_ + 1) * logarithmic / denominator_coefficient),
                    x_,
                ) + rubi_star(recursive_coefficient, recursive)
        },
    ));
}

fn push_rules_rule_3016(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, c__, d__, e__, f__, g__, m_, x_);
    rules.push(rubi_rule!(
        order: 3016,
        source: "Int[(g_.*x_)^m_.*Log[d_.+e_.*x_+f_.*Sqrt[a_.+c_.*x_^2]],x_Symbol] :=
          (g*x)^(m+1)*Log[d+e*x+f*Sqrt[a+c*x^2]]/(g*(m+1)) -
          a*c*f^2/(g*(m+1)) \\[Star] Int[(g*x)^(m+1)/(d*e*(a+c*x^2)+f*(a*e-c*d*x)*Sqrt[a+c*x^2]),x] /;
        FreeQ[{a,c,d,e,f,g,m},x] && EqQ[e^2-c*f^2,0] && NeQ[m,-1] && IntegerQ[2*m]",
        desc: "Integration by parts and algebraic simplification",
        refs: [],
        pattern: (g__ * x_).pow(m_)
            * (d__ + e__ * x_ + f__ * (a__ + c__ * x_.pow(2)).sqrt()).log(),
        with: [g__, m_, d__, e__, f__, a__, c__, x_],
        optional: [g__, m_, d__, e__, f__, a__, c__],
        when: {
            freeq!([a__, c__, d__, e__, f__, g__, m_], x_)
                && eqq!(e__.pow(2) - &c__ * f__.pow(2), 0)
                && neq!(m_, -1)
                && integerq!(Atom::num(2) * &m_)
        },
        rhs: {
            let scaled = &g__ * x_;
            let quadratic = &a__ + &c__ * x_.pow(2);
            let radical = quadratic.sqrt();
            let logarithmic = (&d__ + &e__ * x_ + &f__ * &radical).log();
            let denominator_coefficient = &g__ * (&m_ + 1);
            let recursive_coefficient = -&a__ * &c__ * f__.pow(2) / &denominator_coefficient;

            let denominator = &d__ * &e__ * &quadratic
                + &f__ * (&a__ * &e__ - &c__ * &d__ * x_) * &radical;
            let recursive = rubi_rhs_int(&(scaled.pow(&m_ + 1) / denominator), x_);

            rubi_simp(
                    &(scaled.pow(&m_ + 1) * logarithmic / denominator_coefficient),
                    x_,
                ) + rubi_star(recursive_coefficient, recursive)
        },
    ));
}

fn push_rules_rule_3017(rules: &mut Vec<RubiRule>) {
    rubi_symb!(d__, e__, f__, u__, v__, x_);
    rules.push(rubi_rule!(
        order: 3017,
        source: "Int[v_.*Log[d_.+e_.*x_+f_.*Sqrt[u_]],x_Symbol] :=
          Int[v*Log[d+e*x+f*Sqrt[ExpandToSum[u,x]]],x] /;
        FreeQ[{d,e,f},x] && QuadraticQ[u,x] && Not[QuadraticMatchQ[u,x]] && (EqQ[v,1] || MatchQ[v,(g_.*x)^m_. /; FreeQ[{g,m},x]])",
        desc: "Integration by parts and algebraic simplification",
        refs: [],
        pattern: v__ * (d__ + e__ * x_ + f__ * Atom::var(u__).sqrt()).log(),
        with: [v__, d__, e__, f__, u__, x_],
        optional: [v__, d__, e__, f__],
        when: {
            freeq!([d__, e__, f__], x_)
                && rubi_quadratic_q(&u__, x_)
                && !rubi_quadratic_match_q(&u__, x_)
                && (eqq!(v__, 1) || rubi_match_optional_scaled_monomial_power_q(&v__, x_))
        },
        rhs: {
            let expanded = rubi_expand_to_sum(&u__, x_);
            let transformed_integrand =
                &v__ * (&d__ + &e__ * x_ + &f__ * expanded.sqrt()).log();

            rubi_rhs_int(&transformed_integrand, x_)
        },
    ));
}

fn push_rules_rule_3018(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, m_, n_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 3018,
        source: "Int[Log[c_.*x_^n_.]^r_./(x_*(a_.*x_^m_.+b_.*Log[c_.*x_^n_.]^q_)),x_Symbol] :=
          Log[a*x^m+b*Log[c*x^n]^q]/(b*n*q) - a*m/(b*n*q) \\[Star] Int[x^(m-1)/(a*x^m+b*Log[c*x^n]^q),x] /;
        FreeQ[{a,b,c,m,n,q,r},x] && EqQ[r,q-1]",
        desc: "Algebraic expansion and reciprocal rule for integration",
        refs: [],
        pattern: (c__ * x_.pow(n_)).log().pow(r_)
            / (x_ * (a__ * x_.pow(m_) + b__ * (c__ * x_.pow(n_)).log().pow(q_))),
        with: [c__, n_, r_, a__, m_, b__, q_, x_],
        optional: [c__, n_, r_, a__, m_, b__],
        when: {
            freeq!([a__, b__, c__, m_, n_, q_, r_], x_)
                && eqq!(r_, &q_ - 1)
        },
        rhs: {
            let logarithmic = (&c__ * x_.pow(&n_)).log();
            let denominator = &b__ * &n_ * &q_;
            let binomial = &a__ * x_.pow(&m_) + &b__ * logarithmic.pow(&q_);
            let recursive_coefficient = &a__ * &m_ / &denominator;

            let recursive_integrand = x_.pow(&m_ - 1) / &binomial;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(binomial.log() / denominator), x_)
                    - rubi_star(recursive_coefficient, recursive)
        },
    ));
}

fn push_rules_rule_3019(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, p_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 3019,
        source: "Int[Log[c_.*x_^n_.]^r_.*(a_.*x_^m_.+b_.*Log[c_.*x_^n_.]^q_)^p_./x_,x_Symbol] :=
          Int[ExpandIntegrand[Log[c*x^n]^r/x,(a*x^m+b*Log[c*x^n]^q)^p,x],x] /;
        FreeQ[{a,b,c,m,n,p,q,r},x] && EqQ[r,q-1] && IGtQ[p,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [c__, n_, r_, a__, m_, b__, q_, p_, x_],
        optional: [c__, n_, r_, a__, m_, b__, p_],
        when: {
            freeq!([a__, b__, c__, m_, n_, p_, q_, r_], x_)
                && eqq!(r_, &q_ - 1)
                && igtq!(p_, 0)
        },
        rhs: {
            let logarithmic = (&c__ * x_.pow(&n_)).log();
            let multiplier = logarithmic.pow(&r_) / x_;
            let binomial = &a__ * x_.pow(&m_) + &b__ * logarithmic.pow(&q_);
            let binomial_power = binomial.pow(&p_);
            let expanded = rubi_expand_integrand_product(&multiplier, &binomial_power, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_3020(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, p_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 3020,
        source: "Int[Log[c_.*x_^n_.]^r_.*(a_.*x_^m_.+b_.*Log[c_.*x_^n_.]^q_)^p_./x_,x_Symbol] :=
          (a*x^m+b*Log[c*x^n]^q)^(p+1)/(b*n*q*(p+1)) -
          a*m/(b*n*q) \\[Star] Int[x^(m-1)*(a*x^m+b*Log[c*x^n]^q)^p,x] /;
        FreeQ[{a,b,c,m,n,p,q,r},x] && EqQ[r,q-1] && NeQ[p,-1]",
        desc: "Algebraic expansion and reciprocal rule for integration",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [c__, n_, r_, a__, m_, b__, q_, p_, x_],
        optional: [c__, n_, r_, a__, m_, b__, p_],
        when: {
            freeq!([a__, b__, c__, m_, n_, p_, q_, r_], x_)
                && eqq!(r_, &q_ - 1)
                && neq!(p_, -1)
        },
        rhs: {
            let logarithmic = (&c__ * x_.pow(&n_)).log();
            let binomial = &a__ * x_.pow(&m_) + &b__ * logarithmic.pow(&q_);
            let denominator = &b__ * &n_ * &q_;
            let recursive_coefficient = &a__ * &m_ / &denominator;
            let direct = binomial.pow(&p_ + 1) / (&denominator * (&p_ + 1));

            let recursive_integrand = x_.pow(&m_ - 1) * binomial.pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&direct, x_) - rubi_star(recursive_coefficient, recursive)
        },
    ));
}

fn push_rules_rule_3021(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 3021,
        source: "Int[(d_.*x_^m_.+e_.*Log[c_.*x_^n_.]^r_.)/(x_*(a_.*x_^m_.+b_.*Log[c_.*x_^n_.]^q_)),x_Symbol] :=
          e*Log[a*x^m+b*Log[c*x^n]^q]/(b*n*q) /;
        FreeQ[{a,b,c,d,e,m,n,q,r},x] && EqQ[r,q-1] && EqQ[a*e*m-b*d*n*q,0]",
        desc: "Reciprocal rule for integration",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [d__, m_, e__, c__, n_, r_, a__, b__, q_, x_],
        optional: [d__, m_, e__, c__, n_, r_, a__, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_, q_, r_], x_)
                && eqq!(r_, &q_ - 1)
                && eqq!(&a__ * &e__ * &m_ - &b__ * &d__ * &n_ * &q_, 0)
        },
        rhs: {
            let logarithmic = (&c__ * x_.pow(&n_)).log();
            let binomial = &a__ * x_.pow(&m_) + &b__ * logarithmic.pow(&q_);

            rubi_simp(
                &(&e__ * binomial.log() / (&b__ * &n_ * &q_)),
                x_,
            )
        },
    ));
}

fn push_rules_rule_3022(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, n_, q_, r_, u__, x_);
    rules.push(rubi_rule!(
        order: 3022,
        source: "Int[(u_+d_.*x_^m_.+e_.*Log[c_.*x_^n_.]^r_.)/(x_*(a_.*x_^m_.+b_.*Log[c_.*x_^n_.]^q_)),x_Symbol] :=
          e*Log[a*x^m+b*Log[c*x^n]^q]/(b*n*q) + Int[u/(x*(a*x^m+b*Log[c*x^n]^q)),x] /;
        FreeQ[{a,b,c,d,e,m,n,q,r},x] && EqQ[r,q-1] && EqQ[a*e*m-b*d*n*q,0]",
        desc: "Reciprocal rule for integration",
        refs: [],
        pattern: (u__ + d__ * x_.pow(m_) + e__ * (c__ * x_.pow(n_)).log().pow(r_))
            / (x_ * (a__ * x_.pow(m_) + b__ * (c__ * x_.pow(n_)).log().pow(q_))),
        with: [u__, d__, m_, e__, c__, n_, r_, a__, b__, q_, x_],
        optional: [d__, m_, e__, c__, n_, r_, a__, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_, q_, r_], x_)
                && eqq!(r_, &q_ - 1)
                && eqq!(&a__ * &e__ * &m_ - &b__ * &d__ * &n_ * &q_, 0)
        },
        rhs: {
            let logarithmic = (&c__ * x_.pow(&n_)).log();
            let binomial = &a__ * x_.pow(&m_) + &b__ * logarithmic.pow(&q_);
            let recursive = rubi_rhs_int(&(&u__ / (x_ * &binomial)), x_);

            rubi_simp(&(&e__ * binomial.log() / (&b__ * &n_ * &q_)), x_)
                    + recursive
        },
    ));
}

fn push_rules_rule_3023(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 3023,
        source: "Int[(d_.*x_^m_.+e_.*Log[c_.*x_^n_.]^r_.)/(x_*(a_.*x_^m_.+b_.*Log[c_.*x_^n_.]^q_)),x_Symbol] :=
          e*Log[a*x^m+b*Log[c*x^n]^q]/(b*n*q) -
          (a*e*m-b*d*n*q)/(b*n*q) \\[Star] Int[x^(m-1)/(a*x^m+b*Log[c*x^n]^q),x] /;
        FreeQ[{a,b,c,d,e,m,n,q,r},x] && EqQ[r,q-1] && NeQ[a*e*m-b*d*n*q,0]",
        desc: "Algebraic expansion and reciprocal rule for integration",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [d__, m_, e__, c__, n_, r_, a__, b__, q_, x_],
        optional: [d__, m_, e__, c__, n_, r_, a__, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_, q_, r_], x_)
                && eqq!(r_, &q_ - 1)
                && neq!(&a__ * &e__ * &m_ - &b__ * &d__ * &n_ * &q_, 0)
        },
        rhs: {
            let logarithmic = (&c__ * x_.pow(&n_)).log();
            let binomial = &a__ * x_.pow(&m_) + &b__ * logarithmic.pow(&q_);
            let balance = &a__ * &e__ * &m_ - &b__ * &d__ * &n_ * &q_;
            let denominator = &b__ * &n_ * &q_;
            let recursive_integrand = x_.pow(&m_ - 1) / &binomial;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(&e__ * binomial.log() / &denominator), x_)
                    - rubi_star(balance, recursive / denominator)
        },
    ));
}

fn push_rules_rule_3024(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 3024,
        source: "Int[(d_.*x_^m_.+e_.*Log[c_.*x_^n_.]^r_.)*(a_.*x_^m_.+b_.*Log[c_.*x_^n_.]^q_)^p_./x_,x_Symbol] :=
          e*(a*x^m+b*Log[c*x^n]^q)^(p+1)/(b*n*q*(p+1)) /;
        FreeQ[{a,b,c,d,e,m,n,p,q,r},x] && EqQ[r,q-1] && NeQ[p,-1] && EqQ[a*e*m-b*d*n*q,0]",
        desc: "Algebraic expansion and reciprocal rule for integration",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [d__, m_, e__, c__, n_, r_, a__, b__, q_, p_, x_],
        optional: [d__, m_, e__, c__, n_, r_, a__, b__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_, p_, q_, r_], x_)
                && eqq!(r_, &q_ - 1)
                && neq!(p_, -1)
                && eqq!(&a__ * &e__ * &m_ - &b__ * &d__ * &n_ * &q_, 0)
        },
        rhs: {
            let logarithmic = (&c__ * x_.pow(&n_)).log();
            let binomial = &a__ * x_.pow(&m_) + &b__ * logarithmic.pow(&q_);

            rubi_simp(
                &(&e__ * binomial.pow(&p_ + 1) / (&b__ * &n_ * &q_ * (&p_ + 1))),
                x_,
            )
        },
    ));
}

fn push_rules_rule_3025(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 3025,
        source: "Int[(d_.*x_^m_.+e_.*Log[c_.*x_^n_.]^r_.)*(a_.*x_^m_.+b_.*Log[c_.*x_^n_.]^q_)^p_./x_,x_Symbol] :=
          e*(a*x^m+b*Log[c*x^n]^q)^(p+1)/(b*n*q*(p+1)) -
          (a*e*m-b*d*n*q)/(b*n*q) \\[Star] Int[x^(m-1)*(a*x^m+b*Log[c*x^n]^q)^p,x] /;
        FreeQ[{a,b,c,d,e,m,n,p,q,r},x] && EqQ[r,q-1] && NeQ[p,-1] && NeQ[a*e*m-b*d*n*q,0]",
        desc: "Algebraic expansion and reciprocal rule for integration",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [d__, m_, e__, c__, n_, r_, a__, b__, q_, p_, x_],
        optional: [d__, m_, e__, c__, n_, r_, a__, b__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_, p_, q_, r_], x_)
                && eqq!(r_, &q_ - 1)
                && neq!(p_, -1)
                && neq!(&a__ * &e__ * &m_ - &b__ * &d__ * &n_ * &q_, 0)
        },
        rhs: {
            let logarithmic = (&c__ * x_.pow(&n_)).log();
            let binomial = &a__ * x_.pow(&m_) + &b__ * logarithmic.pow(&q_);
            let balance = &a__ * &e__ * &m_ - &b__ * &d__ * &n_ * &q_;
            let denominator = &b__ * &n_ * &q_;
            let direct = &e__ * binomial.pow(&p_ + 1) / (&denominator * (&p_ + 1));
            let recursive_integrand = x_.pow(&m_ - 1) * binomial.pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            rubi_simp(&direct, x_) - rubi_star(balance, recursive / denominator)
        },
    ));
}

fn push_rules_rule_3026(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, n_, q_, x_);
    rules.push(rubi_rule!(
        order: 3026,
        source: "Int[(d_.*x_^m_.+e_.*x_^m_.*Log[c_.*x_^n_.]+f_.*Log[c_.*x_^n_.]^q_.)/(x_*(a_.*x_^m_.+b_.*Log[c_.*x_^n_.]^q_)^2),x_Symbol] :=
          d*Log[c*x^n]/(a*n*(a*x^m+b*Log[c*x^n]^q)) /;
        FreeQ[{a,b,c,d,e,f,m,n,q},x] && EqQ[e*n+d*m,0] && EqQ[a*f+b*d*(q-1),0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: (d__ * x_.pow(m_)
            + e__ * x_.pow(m_) * (c__ * x_.pow(n_)).log()
            + f__ * (c__ * x_.pow(n_)).log().pow(q_))
            / (x_ * (a__ * x_.pow(m_) + b__ * (c__ * x_.pow(n_)).log().pow(q_)).pow(2)),
        with: [d__, m_, e__, c__, n_, f__, q_, a__, b__, x_],
        optional: [d__, m_, e__, c__, n_, f__, q_, a__, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_, q_], x_)
                && eqq!(&e__ * &n_ + &d__ * &m_, 0)
                && eqq!(&a__ * &f__ + &b__ * &d__ * (&q_ - 1), 0)
        },
        rhs: {
            let logarithmic = (&c__ * x_.pow(&n_)).log();
            let binomial = &a__ * x_.pow(&m_) + &b__ * logarithmic.pow(&q_);

            rubi_simp(
                &(&d__ * logarithmic / (&a__ * &n_ * binomial)),
                x_,
            )
        },
    ));
}

fn push_rules_rule_3027(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, n_, q_, x_);
    rules.push(rubi_rule!(
        order: 3027,
        source: "Int[(d_+e_.*Log[c_.*x_^n_.])/(a_.*x_+b_.*Log[c_.*x_^n_.]^q_)^2,x_Symbol] :=
          -e*Log[c*x^n]/(a*(a*x+b*Log[c*x^n]^q)) + (d+e*n)/a \\[Star] Int[1/(x*(a*x+b*Log[c*x^n]^q)),x] /;
        FreeQ[{a,b,c,d,e,n,q},x] && EqQ[d+e*n*q,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (d__ + e__ * (c__ * x_.pow(n_)).log())
            / (a__ * x_ + b__ * (c__ * x_.pow(n_)).log().pow(q_)).pow(2),
        with: [d__, e__, c__, n_, a__, b__, q_, x_],
        optional: [e__, c__, n_, a__, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, n_, q_], x_)
                && eqq!(&d__ + &e__ * &n_ * &q_, 0)
        },
        rhs: {
            let logarithmic = (&c__ * x_.pow(&n_)).log();
            let binomial = &a__ * x_ + &b__ * logarithmic.pow(&q_);
            let recursive_integrand = Atom::num(1) / (x_ * &binomial);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(-&e__ * &logarithmic / (&a__ * &binomial)), x_)
                    + rubi_star(&d__ + &e__ * &n_, recursive / &a__)
        },
    ));
}

fn push_rules_rule_3028(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; u__);
    rules.push(rubi_rule!(
        order: 3028,
        source: "Int[Log[u_],x_Symbol] :=
          x*Log[u] - Int[SimplifyIntegrand[x*D[u,x]/u,x],x] /;
        InverseFunctionFreeQ[u,x]",
        desc: "Integration by parts",
        refs: ["A&S 4.1.53"],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [u__, x_],
        when: { rubi_inverse_function_free_q(&u__, x_) },
        rhs: {
            let recursive_integrand =
                rubi_simplify_integrand(&(x_ * rubi_d(&u__, x_) / &u__), x_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(x_ * u__.log()), x_) - recursive
        },
    ));
}

fn push_rules_rule_3029(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; u__);
    rules.push(rubi_rule!(
        order: 3029,
        source: "Int[Log[u_],x_Symbol] :=
          x*Log[u] - Int[SimplifyIntegrand[x*Simplify[D[u,x]/u],x],x] /;
        ProductQ[u]",
        desc: "Integration by parts",
        refs: ["A&S 4.1.53"],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [u__, x_],
        when: { rubi_product_q(&u__) },
        rhs: {
            let derivative_quotient = rubi_simplify(&(rubi_d(&u__, x_) / &u__));
            let recursive_integrand =
                rubi_simplify_integrand(&(x_ * derivative_quotient), x_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(x_ * u__.log()), x_) - recursive
        },
    ));
}

fn push_rules_rule_3030(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, u__, x_);
    rules.push(rubi_rule!(
        order: 3030,
        source: "Int[Log[u_]/(a_.+b_.*x_),x_Symbol] :=
          Log[a+b*x]*Log[u]/b -
          1/b \\[Star] Int[SimplifyIntegrand[Log[a+b*x]*D[u,x]/u,x],x] /;
        FreeQ[{a,b},x] && RationalFunctionQ[D[u,x]/u,x] && (NeQ[a,0] || Not[BinomialQ[u,x] && EqQ[BinomialDegree[u,x]^2,1]])",
        desc: "Integration by parts",
        refs: ["G&R 2.727.2"],
        pattern: Atom::var(u__).log() / (a__ + b__ * x_),
        with: [u__, a__, b__, x_],
        optional: [a__, b__],
        when: {
            freeq!([a__, b__], x_)
                && rubi_rational_function_q(&(rubi_d(&u__, x_) / &u__), x_)
                && (neq!(a__, 0)
                    || !(rubi_binomial_q(&u__, x_)
                        && rubi_binomial_degree(&u__, x_)
                            .is_some_and(|degree| eqq!(degree.pow(2), 1))))
        },
        rhs: {
            let affine = &a__ + &b__ * x_;
            let affine_log = affine.log();
            let recursive_integrand =
                rubi_simplify_integrand(&(&affine_log * rubi_d(&u__, x_) / &u__), x_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(affine_log * u__.log() / &b__), x_)
                    - rubi_star(Atom::num(1) / &b__, recursive)
        },
    ));
}

fn push_rules_rule_3031(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, m_, u__, x_);
    rules.push(rubi_rule!(
        order: 3031,
        source: "Int[(a_.+b_.*x_)^m_.*Log[u_],x_Symbol] :=
          (a+b*x)^(m+1)*Log[u]/(b*(m+1)) -
          1/(b*(m+1)) \\[Star] Int[SimplifyIntegrand[(a+b*x)^(m+1)*D[u,x]/u,x],x] /;
        FreeQ[{a,b,m},x] && InverseFunctionFreeQ[u,x] && NeQ[m,-1] (* && Not[FunctionOfQ[x^(m+1),u,x]] && FalseQ[PowerVariableExpn[u,m+1,x]] *)",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern: (a__ + b__ * x_).pow(m_) * Atom::var(u__).log(),
        with: [a__, b__, m_, u__, x_],
        optional: [a__, b__, m_],
        when: {
            freeq!([a__, b__, m_], x_)
                && rubi_inverse_function_free_q(&u__, x_)
                && neq!(m_, -1)
        },
        rhs: {
            let affine = &a__ + &b__ * x_;
            let raised = affine.pow(&m_ + 1);
            let denominator = &b__ * (&m_ + 1);
            let recursive_integrand =
                rubi_simplify_integrand(&(&raised * rubi_d(&u__, x_) / &u__), x_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(raised * u__.log() / &denominator), x_)
                    - rubi_star(Atom::num(1) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_3032(rules: &mut Vec<RubiRule>) {
    rubi_symb!(qx__, u__);
    rules.push(rubi_rule!(
        order: 3032,
        source: "Int[Log[u_]/Qx_,x_Symbol] :=
          With[{v=IntHide[1/Qx,x]},
          v*Log[u] - Int[SimplifyIntegrand[v*D[u,x]/u,x],x]] /;
        QuadraticQ[Qx,x] && InverseFunctionFreeQ[u,x]",
        desc: "Integration by parts",
        refs: [],
        pattern: Atom::var(u__).log() / qx__,
        with: [u__, qx__, x_],
        when: { rubi_quadratic_q(&qx__, x_) && rubi_inverse_function_free_q(&u__, x_) },
        rhs: {
            let v = rubi_int_hide(&(Atom::num(1) / &qx__), x_).rubi_rhs();
            let recursive_integrand =
                rubi_simplify_integrand(&(&v * rubi_d(&u__, x_) / &u__), x_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(v * u__.log()), x_) - recursive
        },
    ));
}

fn push_rules_rule_3033(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, u__, x_);
    rules.push(rubi_rule!(
        order: 3033,
        source: "Int[u_^(a_.*x_)*Log[u_],x_Symbol] :=
          u^(a*x)/a - Int[SimplifyIntegrand[x*u^(a*x-1)*D[u,x],x],x] /;
        FreeQ[a,x] && InverseFunctionFreeQ[u,x]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern: Atom::var(u__).pow(a__ * x_) * Atom::var(u__).log(),
        with: [u__, a__, x_],
        optional: [a__],
        when: {
            freeq!(a__, x_)
                && rubi_inverse_function_free_q(&u__, x_)
        },
        rhs: {
            let exponential = u__.pow(&a__ * x_);
            let recursive_integrand =
                rubi_simplify_integrand(&(x_ * u__.pow(&a__ * x_ - 1) * rubi_d(&u__, x_)), x_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(exponential / &a__), x_) - recursive
        },
    ));
}

fn push_rules_rule_3034(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; u__, v__);
    rules.push(rubi_rule!(
        order: 3034,
        source: "Int[v_*Log[u_],x_Symbol] :=
          With[{w=IntHide[v,x]},
          Log[u] \\[Star] w - Int[SimplifyIntegrand[w*D[u,x]/u,x],x] /;
         InverseFunctionFreeQ[w,x]] /;
        InverseFunctionFreeQ[u,x]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [v__, u__, x_],
        when: {
            rubi_inverse_function_free_q(&u__, x_)
                && rubi_int_hide(&v__, x_)
                    .is_some_and(|w| rubi_inverse_function_free_q(&w, x_))
        },
        rhs: {
            let w = rubi_int_hide(&v__, x_).expect("when clause should ensure IntHide succeeds");

            let recursive_integrand =
                rubi_simplify_integrand(&(&w * rubi_d(&u__, x_) / &u__), x_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(u__.log(), w) - recursive
        },
    ));
}

fn push_rules_rule_3035(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; u__, v__);
    rules.push(rubi_rule!(
        order: 3035,
        source: "Int[v_*Log[u_],x_Symbol] :=
          With[{w=IntHide[v,x]},
          Log[u] \\[Star] w - Int[SimplifyIntegrand[w*Simplify[D[u,x]/u],x],x] /;
         InverseFunctionFreeQ[w,x]] /;
        ProductQ[u]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [v__, u__, x_],
        when: {
            rubi_product_q(&u__)
                && rubi_int_hide(&v__, x_)
                    .is_some_and(|w| rubi_inverse_function_free_q(&w, x_))
        },
        rhs: {
            let w = rubi_int_hide(&v__, x_).expect("when clause should ensure IntHide succeeds");

            let derivative_quotient = rubi_simplify(&(rubi_d(&u__, x_) / &u__));
            let recursive_integrand = rubi_simplify_integrand(&(&w * derivative_quotient), x_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(u__.log(), w) - recursive
        },
    ));
}

fn push_rules_rule_3036(rules: &mut Vec<RubiRule>) {
    rubi_symb!(v__, w__);
    rules.push(rubi_rule!(
        order: 3036,
        source: "Int[Log[v_]*Log[w_],x_Symbol] :=
          x*Log[v]*Log[w] -
          Int[SimplifyIntegrand[x*Log[w]*D[v,x]/v,x],x] -
          Int[SimplifyIntegrand[x*Log[v]*D[w,x]/w,x],x] /;
        InverseFunctionFreeQ[v,x] && InverseFunctionFreeQ[w,x]",
        desc: "Integration by parts",
        refs: [],
        pattern: Atom::var(v__).log() * Atom::var(w__).log(),
        with: [v__, w__, x_],
        when: { rubi_inverse_function_free_q(&v__, x_) && rubi_inverse_function_free_q(&w__, x_) },
        rhs: {
            let log_v = v__.log();
            let log_w = w__.log();
            let recursive_integrand_v =
                rubi_simplify_integrand(&(x_ * &log_w * rubi_d(&v__, x_) / &v__), x_);
            let recursive_v = rubi_rhs_int(&recursive_integrand_v, x_);
            let recursive_integrand_w =
                rubi_simplify_integrand(&(x_ * &log_v * rubi_d(&w__, x_) / &w__), x_);
            let recursive_w = rubi_rhs_int(&recursive_integrand_w, x_);

            rubi_simp(&(x_ * log_v * log_w), x_) - recursive_v - recursive_w
        },
    ));
}

fn push_rules_rule_3037(rules: &mut Vec<RubiRule>) {
    rubi_symb!(u__, v__, w__);
    rules.push(rubi_rule!(
        order: 3037,
        source: "Int[u_*Log[v_]*Log[w_],x_Symbol] :=
          With[{z=IntHide[u,x]},
          Log[v]*Log[w] \\[Star] z -
          Int[SimplifyIntegrand[z*Log[w]*D[v,x]/v,x],x] -
          Int[SimplifyIntegrand[z*Log[v]*D[w,x]/w,x],x] /;
         InverseFunctionFreeQ[z,x]] /;
        InverseFunctionFreeQ[v,x] && InverseFunctionFreeQ[w,x]",
        desc: "Integration by parts",
        refs: [],
        pattern: u__ * Atom::var(v__).log() * Atom::var(w__).log(),
        with: [u__, v__, w__, x_],
        when: {
            rubi_inverse_function_free_q(&v__, x_)
                && rubi_inverse_function_free_q(&w__, x_)
                && rubi_int_hide(&u__, x_)
                    .is_some_and(|z| rubi_inverse_function_free_q(&z, x_))
        },
        rhs: {
            let z = rubi_int_hide(&u__, x_).expect("when clause should ensure IntHide succeeds");

            let log_v = v__.log();
            let log_w = w__.log();
            let recursive_integrand_v =
                rubi_simplify_integrand(&(&z * &log_w * rubi_d(&v__, x_) / &v__), x_);
            let recursive_v = rubi_rhs_int(&recursive_integrand_v, x_);
            let recursive_integrand_w =
                rubi_simplify_integrand(&(&z * &log_v * rubi_d(&w__, x_) / &w__), x_);
            let recursive_w = rubi_rhs_int(&recursive_integrand_w, x_);

            rubi_star(log_v * log_w, z) - recursive_v - recursive_w
        },
    ));
}

fn push_rules_rule_3038(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, f__, u__);
    rules.push(rubi_rule!(
        order: 3038,
        source: "Int[f_^(a_.*Log[u_]),x_Symbol] :=
          Int[u^(a*Log[f]),x] /;
        FreeQ[{a,f},x]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: f__.pow(a__ * Atom::var(u__).log()),
        with: [f__, a__, u__, x_],
        optional: [a__],
        when: { freeq!([a__, f__], x_) },
        rhs: { rubi_rhs_int(&u__.pow(&a__ * f__.log()), x_) },
    ));
}

fn push_rules_rule_3039(rules: &mut Vec<RubiRule>) {
    rubi_symb!(u__);
    rules.push(rubi_rule!(
        order: 3039,
        source: "Int[u_,x_Symbol] :=
          With[{lst=FunctionOfLog[Cancel[x*u],x]},
          1/lst[[3]] \\[Star] Subst[Int[lst[[1]],x],x,Log[lst[[2]]]] /;
         Not[FalseQ[lst]]] /;
        NonsumQ[u]",
        desc: "Integration by substitution",
        refs: [],
        pattern: Atom::var(u__),
        with: [u__, x_],
        when: {
            rubi_nonsum_q(&u__)
                && rubi_function_of_log(&rubi_cancel(&(x_ * &u__)), x_).is_some()
        },
        rhs: {
            let lst = rubi_function_of_log(&rubi_cancel(&(x_ * &u__)), x_).rubi_rhs();
            let substitution_guard = fresh_substitution_symbol().rubi_rhs();
            let substitution_symbol = substitution_guard.symbol();
            let transformed_integrand =
                rubi_subst(&lst.function, x_, Atom::var(substitution_symbol));
            let transformed_primitive =
                rubi_rhs_int(&transformed_integrand, substitution_symbol);
            let substituted = rubi_subst(
                &transformed_primitive,
                substitution_symbol,
                lst.argument.log(),
            );
            let result = rubi_simp(&(&(Atom::num(1) / lst.n) * &substituted), x_);

            rubi_star(Atom::num(1), result)
        },
    ));
}

fn push_rules_rule_3040(rules: &mut Vec<RubiRule>) {
    rubi_symb!(u__, v__);
    rules.push(rubi_rule!(
        order: 3040,
        source: "Int[u_.*Log[Gamma[v_]],x_Symbol] :=
          (Log[Gamma[v]]-LogGamma[v]) \\[Star] Int[u,x] + Int[u*LogGamma[v],x]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: u__ * rubi_gamma_unary(Atom::var(v__)).log(),
        with: [u__, v__, x_],
        optional: [u__],
        when: { true },
        rhs: {
            let gamma = rubi_gamma_unary(&v__);
            let log_gamma = rubi_log_gamma(&v__);
            let integrated_u = rubi_rhs_int(&u__, x_);
            let integrated_log_gamma = rubi_rhs_int(&(&u__ * &log_gamma), x_);

            rubi_star(gamma.log() - log_gamma, integrated_u)
                    + integrated_log_gamma
        },
    ));
}

fn push_rules_rule_3041(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, m_, n_, p_, q_, r_, u__, x_);
    rules.push(rubi_rule!(
        order: 3041,
        source: "Int[u_.*(a_.*x_^m_.+b_.*x_^r_.*Log[c_.*x_^n_.]^q_.)^p_.,x_Symbol] :=
          Int[u*x^(p*r)*(a*x^(m-r)+b*Log[c*x^n]^q)^p,x] /;
        FreeQ[{a,b,c,m,n,p,q,r},x] && IntegerQ[p]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: u__
            * (a__ * x_.pow(m_) + b__ * x_.pow(r_) * (c__ * x_.pow(n_)).log().pow(q_)).pow(p_),
        with: [u__, a__, m_, b__, r_, c__, n_, q_, p_, x_],
        optional: [u__, a__, m_, b__, r_, c__, n_, q_, p_],
        when: {
            freeq!([a__, b__, c__, m_, n_, p_, q_, r_], x_) && integerq!(p_)
        },
        rhs: {
            let logarithmic = (&c__ * x_.pow(&n_)).log();
            let transformed_integrand = &u__
                * x_.pow(&p_ * &r_)
                * (&a__ * x_.pow(&m_ - &r_) + &b__ * logarithmic.pow(&q_)).pow(&p_);
            rubi_rhs_int(&transformed_integrand, x_)
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
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let q_ = symbols.q_;
    let r_ = symbols.r_;
    let x_ = symbols.x_;
    (c__ * x_.pow(n_)).log().pow(r_)
        * (a__ * x_.pow(m_) + b__ * (c__ * x_.pow(n_)).log().pow(q_)).pow(p_)
        / x_
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let q_ = symbols.q_;
    let r_ = symbols.r_;
    let x_ = symbols.x_;
    (d__ * x_.pow(m_) + e__ * (c__ * x_.pow(n_)).log().pow(r_))
        * (a__ * x_.pow(m_) + b__ * (c__ * x_.pow(n_)).log().pow(q_)).pow(p_)
        / x_
}

#[inline(never)]
fn rubi_shared_pattern_2(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let q_ = symbols.q_;
    let r_ = symbols.r_;
    let x_ = symbols.x_;
    (d__ * x_.pow(m_) + e__ * (c__ * x_.pow(n_)).log().pow(r_))
        / (x_ * (a__ * x_.pow(m_) + b__ * (c__ * x_.pow(n_)).log().pow(q_)))
}

#[inline(never)]
fn rubi_shared_pattern_3(symbols: &RubiSymbols) -> Atom {
    let u__ = symbols.u__;
    Atom::var(u__).log()
}

#[inline(never)]
fn rubi_shared_pattern_4(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let rfx__ = symbols.rfx__;
    let rgx__ = symbols.rgx__;
    rgx__ * (a__ + b__ * (c__ * rfx__.pow(p_)).log()).pow(n_)
}

#[inline(never)]
fn rubi_shared_pattern_5(symbols: &RubiSymbols) -> Atom {
    let u__ = symbols.u__;
    let v__ = symbols.v__;
    v__ * Atom::var(u__).log()
}
