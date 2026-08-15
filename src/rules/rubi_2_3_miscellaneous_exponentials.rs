use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_2624(rules);
    push_rules_rule_2625(rules);
    push_rules_rule_2626(rules);
    push_rules_rule_2627(rules);
    push_rules_rule_2628(rules);
    push_rules_rule_2629(rules);
    push_rules_rule_2630(rules);
    push_rules_rule_2631(rules);
    push_rules_rule_2632(rules);
    push_rules_rule_2633(rules);
    push_rules_rule_2634(rules);
    push_rules_rule_2635(rules);
    push_rules_rule_2636(rules);
    push_rules_rule_2637(rules);
    push_rules_rule_2638(rules);
    push_rules_rule_2639(rules);
    push_rules_rule_2640(rules);
    push_rules_rule_2641(rules);
    push_rules_rule_2642(rules);
    push_rules_rule_2643(rules);
    push_rules_rule_2644(rules);
    push_rules_rule_2645(rules);
    push_rules_rule_2646(rules);
    push_rules_rule_2647(rules);
    push_rules_rule_2648(rules);
    push_rules_rule_2649(rules);
    push_rules_rule_2650(rules);
    push_rules_rule_2651(rules);
    push_rules_rule_2652(rules);
    push_rules_rule_2653(rules);
    push_rules_rule_2654(rules);
    push_rules_rule_2655(rules);
    push_rules_rule_2656(rules);
    push_rules_rule_2657(rules);
    push_rules_rule_2658(rules);
    push_rules_rule_2659(rules);
    push_rules_rule_2660(rules);
    push_rules_rule_2661(rules);
    push_rules_rule_2662(rules);
    push_rules_rule_2663(rules);
    push_rules_rule_2664(rules);
    push_rules_rule_2665(rules);
    push_rules_rule_2666(rules);
    push_rules_rule_2667(rules);
    push_rules_rule_2668(rules);
    push_rules_rule_2669(rules);
    push_rules_rule_2670(rules);
    push_rules_rule_2671(rules);
    push_rules_rule_2672(rules);
    push_rules_rule_2673(rules);
    push_rules_rule_2674(rules);
    push_rules_rule_2675(rules);
    push_rules_rule_2676(rules);
    push_rules_rule_2677(rules);
    push_rules_rule_2678(rules);
    push_rules_rule_2679(rules);
    push_rules_rule_2680(rules);
    push_rules_rule_2681(rules);
    push_rules_rule_2682(rules);
    push_rules_rule_2683(rules);
    push_rules_rule_2684(rules);
    push_rules_rule_2685(rules);
    push_rules_rule_2686(rules);
    push_rules_rule_2687(rules);
    push_rules_rule_2688(rules);
    push_rules_rule_2689(rules);
    push_rules_rule_2690(rules);
    push_rules_rule_2691(rules);
    push_rules_rule_2692(rules);
    push_rules_rule_2693(rules);
    push_rules_rule_2694(rules);
    push_rules_rule_2695(rules);
    push_rules_rule_2696(rules);
    push_rules_rule_2697(rules);
    push_rules_rule_2698(rules);
    push_rules_rule_2699(rules);
    push_rules_rule_2700(rules);
    push_rules_rule_2701(rules);
    push_rules_rule_2702(rules);
    push_rules_rule_2703(rules);
    push_rules_rule_2704(rules);
    push_rules_rule_2705(rules);
    push_rules_rule_2706(rules);
    push_rules_rule_2707(rules);
    push_rules_rule_2708(rules);
    push_rules_rule_2709(rules);
    push_rules_rule_2710(rules);
    push_rules_rule_2711(rules);
    push_rules_rule_2712(rules);
    push_rules_rule_2713(rules);
    push_rules_rule_2714(rules);
    push_rules_rule_2715(rules);
    push_rules_rule_2716(rules);
    push_rules_rule_2717(rules);
    push_rules_rule_2718(rules);
    push_rules_rule_2719(rules);
    push_rules_rule_2720(rules);
    push_rules_rule_2721(rules);
    push_rules_rule_2722(rules);
    push_rules_rule_2723(rules);
    push_rules_rule_2724(rules);
    push_rules_rule_2725(rules);
    push_rules_rule_2726(rules);
    push_rules_rule_2727(rules);
    push_rules_rule_2728(rules);
    push_rules_rule_2729(rules);
    push_rules_rule_2730(rules);
    push_rules_rule_2731(rules);
}

fn push_rules_rule_2624(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_f_, n_, v_);
    rules.push(rubi_rule!(
        order: 2624,
        source: "Int[(F_^v_)^n_.,x_Symbol] :=
          (F^v)^n/(n*Log[F]*D[v,x]) /;
        FreeQ[{F,n},x] && LinearQ[v,x]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: capital_f_.pow(v_).pow(n_),
        with: [capital_f_, v_, n_, x_],
        optional: [n_],
        when: {
            freeq!([capital_f_, n_], x_) && rubi_linear_q(&v_, x_)
        },
        rhs: {
            let exponential = capital_f_.pow(&v_).pow(&n_);
            let denominator = &n_ * capital_f_.log() * rubi_d(&v_, x_);

            rubi_simp(&(exponential / denominator), x_)
        },
    ));
}

fn push_rules_rule_2625(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, px__, v_);
    rules.push(rubi_rule!(
        order: 2625,
        source: "Int[Px_*F_^v_,x_Symbol] :=
          Int[ExpandIntegrand[Px*F^v,x],x] /;
        FreeQ[F,x] && PolynomialQ[Px,x] && LinearQ[v,x] && TrueQ[$UseGamma]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_19(symbols),
        with: [px__, capital_f_, v_, x_],
        when: {
            freeq!(capital_f_, x_)
                && rubi_polynomial_q(&px__, x_)
                && rubi_linear_q(&v_, x_)
                && rubi_true_q_use_gamma()
        },
        rhs: {
            let expanded =
                rubi_expand_integrand_or_self(&(&px__ * capital_f_.pow(&v_)), x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_2626(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, px__, v_);
    rules.push(rubi_rule!(
        order: 2626,
        source: "Int[Px_*F_^v_,x_Symbol] :=
          Int[ExpandIntegrand[F^v,Px,x],x] /;
        FreeQ[F,x] && PolynomialQ[Px,x] && LinearQ[v,x] && Not[TrueQ[$UseGamma]]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_19(symbols),
        with: [px__, capital_f_, v_, x_],
        when: {
            freeq!(capital_f_, x_)
                && rubi_polynomial_q(&px__, x_)
                && rubi_linear_q(&v_, x_)
                && !rubi_true_q_use_gamma()
        },
        rhs: {
            let exponential = capital_f_.pow(&v_);
            let expanded = rubi_expand_integrand_product(&exponential, &px__, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_2627(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_f_, d__, e__, f__, g__, m_, v_, x_);
    rules.push(rubi_rule!(
        order: 2627,
        source: "Int[(d_.+e_.*x_)^m_.*(f_.+g_.*x_)*F_^v_,x_Symbol] :=
          g*(d+e*x)^(m+1)*F^v/(D[v,x]*e*Log[F]) /;
        FreeQ[{F,d,e,f,g,m},x] && LinearQ[v,x] && EqQ[e*g*(m+1)-D[v,x]*(e*f-d*g)*Log[F],0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: (d__ + e__ * x_).pow(m_) * (f__ + g__ * x_) * capital_f_.pow(v_),
        with: [d__, e__, m_, f__, g__, capital_f_, v_, x_],
        optional: [d__, e__, m_, f__, g__],
        when: {
            freeq!([capital_f_, d__, e__, f__, g__, m_], x_)
                && rubi_linear_q(&v_, x_)
                && eqq!(
                    &e__ * &g__ * (&m_ + 1)
                        - rubi_d(&v_, x_)
                            * (&e__ * &f__ - &d__ * &g__)
                            * capital_f_.log(),
                    0
                )
        },
        rhs: {
            let denominator = rubi_d(&v_, x_) * &e__ * capital_f_.log();

            rubi_simp(
                &(&g__ * (&d__ + &e__ * x_).pow(&m_ + 1)
                    * capital_f_.pow(&v_)
                    / denominator),
                x_,
            )
        },
    ));
}

fn push_rules_rule_2628(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, d__, e__, m_, px__, v_, x_);
    rules.push(rubi_rule!(
        order: 2628,
        source: "Int[Px_*(d_.+e_.*x_)^m_.*F_^v_,x_Symbol] :=
          Int[ExpandIntegrand[Px*(d+e*x)^m*F^v,x],x] /;
        FreeQ[{F,d,e,m},x] && PolynomialQ[Px,x] && LinearQ[v,x] && TrueQ[$UseGamma]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_18(symbols),
        with: [px__, d__, e__, m_, capital_f_, v_, x_],
        optional: [d__, e__, m_],
        when: {
            freeq!([capital_f_, d__, e__, m_], x_)
                && rubi_polynomial_q(&px__, x_)
                && rubi_linear_q(&v_, x_)
                && rubi_true_q_use_gamma()
        },
        rhs: {
            let expanded = rubi_expand_integrand_or_self(
                &(&px__
                    * (&d__ + &e__ * x_).pow(&m_)
                    * capital_f_.pow(&v_)),
                x_,
            );

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_2629(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, d__, e__, m_, px__, v_, x_);
    rules.push(rubi_rule!(
        order: 2629,
        source: "Int[Px_*(d_.+e_.*x_)^m_.*F_^v_,x_Symbol] :=
          Int[ExpandIntegrand[F^v,Px*(d+e*x)^m,x],x] /;
        FreeQ[{F,d,e,m},x] && PolynomialQ[Px,x] && LinearQ[v,x] && Not[TrueQ[$UseGamma]]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_18(symbols),
        with: [px__, d__, e__, m_, capital_f_, v_, x_],
        optional: [d__, e__, m_],
        when: {
            freeq!([capital_f_, d__, e__, m_], x_)
                && rubi_polynomial_q(&px__, x_)
                && rubi_linear_q(&v_, x_)
                && !rubi_true_q_use_gamma()
        },
        rhs: {
            let polynomial_factor =
                &px__ * (&d__ + &e__ * x_).pow(&m_);
            let exponential = capital_f_.pow(&v_);
            let expanded = rubi_expand_integrand_product(&exponential, &polynomial_factor, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_2630(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_f_, d__, e__, f__, g__, h__, n_, v_, x_);
    rules.push(rubi_rule!(
        order: 2630,
        source: "Int[F_^v_*Log[d_.*x_]^n_.*(e_+h_.*(f_.+g_.*x_)*Log[d_.*x_]),x_Symbol] :=
          e*x*F^v*Log[d*x]^(n+1)/(n+1) /;
        FreeQ[{F,d,e,f,g,h,n},x] && LinearQ[v,x] && EqQ[e,f*h*(n+1)] && EqQ[g*h*(n+1),D[v,x]*e*Log[F]] && NeQ[n,-1]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: capital_f_.pow(v_)
            * (d__ * x_).log().pow(n_)
            * (e__ + h__ * (f__ + g__ * x_) * (d__ * x_).log()),
        with: [capital_f_, v_, d__, n_, e__, h__, f__, g__, x_],
        optional: [d__, n_, h__, f__, g__],
        when: {
            freeq!([capital_f_, d__, e__, f__, g__, h__, n_], x_)
                && rubi_linear_q(&v_, x_)
                && eqq!(e__, &f__ * &h__ * (&n_ + 1))
                && eqq!(
                    &g__ * &h__ * (&n_ + 1),
                    rubi_d(&v_, x_) * &e__ * capital_f_.log()
                )
                && neq!(n_, -1)
        },
        rhs: {
            rubi_simp(
                &(&e__ * x_
                    * capital_f_.pow(&v_)
                    * (&d__ * x_).log().pow(&n_ + 1)
                    / (&n_ + 1)),
                x_,
            )
        },
    ));
}

fn push_rules_rule_2631(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_f_, d__, e__, f__, g__, h__, m_, n_, v_, x_);
    rules.push(rubi_rule!(
        order: 2631,
        source: "Int[x_^m_.*F_^v_*Log[d_.*x_]^n_.*(e_+h_.*(f_.+g_.*x_)*Log[d_.*x_]),x_Symbol] :=
          e*x^(m+1)*F^v*Log[d*x]^(n+1)/(n+1) /;
        FreeQ[{F,d,e,f,g,h,m,n},x] && LinearQ[v,x] && EqQ[e*(m+1),f*h*(n+1)] && EqQ[g*h*(n+1),D[v,x]*e*Log[F]] && NeQ[n,-1]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: x_.pow(m_)
            * capital_f_.pow(v_)
            * (d__ * x_).log().pow(n_)
            * (e__ + h__ * (f__ + g__ * x_) * (d__ * x_).log()),
        with: [m_, capital_f_, v_, d__, n_, e__, h__, f__, g__, x_],
        optional: [m_, d__, n_, h__, f__, g__],
        when: {
            freeq!([capital_f_, d__, e__, f__, g__, h__, m_, n_], x_)
                && rubi_linear_q(&v_, x_)
                && eqq!(&e__ * (&m_ + 1), &f__ * &h__ * (&n_ + 1))
                && eqq!(
                    &g__ * &h__ * (&n_ + 1),
                    rubi_d(&v_, x_) * &e__ * capital_f_.log()
                )
                && neq!(n_, -1)
        },
        rhs: {
            rubi_simp(
                &(&e__ * x_.pow(&m_ + 1)
                    * capital_f_.pow(&v_)
                    * (&d__ * x_).log().pow(&n_ + 1)
                    / (&n_ + 1)),
                x_,
            )
        },
    ));
}

fn push_rules_rule_2632(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_f_, a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 2632,
        source: "Int[F_^(a_.+b_.*(c_.+d_.*x_)),x_Symbol] :=
          F^(a+b*(c+d*x))/(b*d*Log[F]) /;
        FreeQ[{F,a,b,c,d},x]",
        desc: "Apply the direct antiderivative formula.",
        refs: ["G&R 2.311, CRC 519, A&S 4.2.54"],
        pattern: capital_f_.pow(a__ + b__ * (c__ + d__ * x_)),
        with: [capital_f_, a__, b__, c__, d__, x_],
        optional: [a__, b__, c__, d__],
        when: { freeq!([capital_f_, a__, b__, c__, d__], x_) },
        rhs: {
            rubi_simp(
                &(capital_f_.pow(&a__ + &b__ * (&c__ + &d__ * x_))
                    / (&b__ * &d__ * capital_f_.log())),
                x_,
            )
        },
    ));
}

fn push_rules_rule_2633(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 2633,
        source: "Int[F_^(a_.+b_.*(c_.+d_.*x_)^2),x_Symbol] :=
          F^a*Sqrt[Pi]*Erfi[(c+d*x)*Rt[b*Log[F],2]]/(2*d*Rt[b*Log[F],2]) /;
        FreeQ[{F,a,b,c,d},x] && PosQ[b]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_11(symbols),
        with: [capital_f_, a__, b__, c__, d__, x_],
        optional: [a__, b__, c__, d__],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__], x_) && posq!(b__)
        },
        rhs: {
            let rt = rubi_rt(&(&b__ * capital_f_.log()), 2);

            rubi_simp(
                &(capital_f_.pow(a__) * Atom::var(Symbol::PI).sqrt()
                    * rubi_erfi((&c__ + &d__ * x_) * &rt)
                    / (Atom::num(2) * d__ * rt)),
                x_,
            )
        },
    ));
}

fn push_rules_rule_2634(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 2634,
        source: "Int[F_^(a_.+b_.*(c_.+d_.*x_)^2),x_Symbol] :=
          F^a*Sqrt[Pi]*Erf[(c+d*x)*Rt[-b*Log[F],2]]/(2*d*Rt[-b*Log[F],2]) /;
        FreeQ[{F,a,b,c,d},x] && NegQ[b]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_11(symbols),
        with: [capital_f_, a__, b__, c__, d__, x_],
        optional: [a__, b__, c__, d__],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__], x_) && negq!(b__)
        },
        rhs: {
            let rt = rubi_rt(&(-&b__ * capital_f_.log()), 2);

            rubi_simp(
                &(capital_f_.pow(a__) * Atom::var(Symbol::PI).sqrt()
                    * ((&c__ + &d__ * x_) * &rt).erf()
                    / (Atom::num(2) * d__ * rt)),
                x_,
            )
        },
    ));
}

fn push_rules_rule_2635(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 2635,
        source: "Int[F_^(a_.+b_.*(c_.+d_.*x_)^n_),x_Symbol] :=
          (c+d*x)*F^(a+b*(c+d*x)^n)/d -
          b*n*Log[F] \\[Star] Int[(c+d*x)^n*F^(a+b*(c+d*x)^n),x] /;
        FreeQ[{F,a,b,c,d},x] && IntegerQ[2/n] && ILtQ[n,0]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_12(symbols),
        with: [capital_f_, a__, b__, c__, d__, n_, x_],
        optional: [a__, b__, c__, d__],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__], x_)
                && integerq!(Atom::num(2) / &n_)
                && iltq!(n_, 0)
        },
        rhs: {
            let affine = &c__ + &d__ * x_;
            let exponential = capital_f_.pow(&a__ + &b__ * affine.pow(&n_));
            let recursive_integrand = affine.pow(&n_) * &exponential;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(&affine * exponential / &d__), x_)
                    - rubi_star(&b__ * &n_ * capital_f_.log(), recursive)
        },
    ));
}

fn push_rules_rule_2636(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 2636,
        source: "Int[F_^(a_.+b_.*(c_.+d_.*x_)^n_),x_Symbol] :=
          With[{k=Denominator[n]},
          k/d \\[Star] Subst[Int[x^(k-1)*F^(a+b*x^(k*n)),x],x,(c+d*x)^(1/k)]] /;
        FreeQ[{F,a,b,c,d},x] && IntegerQ[2/n] && Not[IntegerQ[n]]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_12(symbols),
        with: [capital_f_, a__, b__, c__, d__, n_, x_],
        optional: [a__, b__, c__, d__],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__], x_)
                && integerq!(Atom::num(2) / &n_)
                && !integerq!(n_)
        },
        rhs: {
            let k = denominator!(n_);
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let substitution_variable = Atom::var(substitution_symbol);
            let transformed_integrand = substitution_variable.pow(k - 1)
                * capital_f_.pow(&a__ + &b__ * substitution_variable.pow(Atom::num(k) * &n_));
            let transformed_primitive = rubi_rhs_int(&transformed_integrand, substitution_symbol);
            let substitution = (&c__ + &d__ * x_).pow(Atom::num(1) / Atom::num(k));
            let substituted = rubi_subst(
                &transformed_primitive,
                substitution_symbol,
                substitution,
            );

            rubi_star(Atom::num(k), substituted / &d__)
        },
    ));
}

fn push_rules_rule_2637(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 2637,
        source: "Int[F_^(a_.+b_.*(c_.+d_.*x_)^n_),x_Symbol] :=
          -F^a*(c+d*x)*Gamma[1/n,-b*(c+d*x)^n*Log[F]]/(d*n*(-b*(c+d*x)^n*Log[F])^(1/n)) /;
        FreeQ[{F,a,b,c,d,n},x] && Not[IntegerQ[2/n]]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_12(symbols),
        with: [capital_f_, a__, b__, c__, d__, n_, x_],
        optional: [a__, b__, c__, d__],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, n_], x_)
                && !integerq!(Atom::num(2) / &n_)
        },
        rhs: {
            let affine = &c__ + &d__ * x_;
            let gamma_argument = -&b__ * affine.pow(&n_) * capital_f_.log();
            let gamma_power = gamma_argument.pow(Atom::num(1) / &n_);
            rubi_simp(&(
                -capital_f_.pow(a__) * affine * rubi_gamma(Atom::num(1) / &n_, gamma_argument)
                    / (&d__ * &n_ * gamma_power)
            ), x_)
        },
    ));
}

fn push_rules_rule_2638(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, d__, m_, n_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 2638,
        source: "Int[(e_.+f_.*x_)^m_.*F_^(a_.+b_.*(c_.+d_.*x_)^n_),x_Symbol] :=
          (e+f*x)^n*F^(a+b*(c+d*x)^n)/(b*f*n*(c+d*x)^n*Log[F]) /;
        FreeQ[{F,a,b,c,d,e,f,n},x] && EqQ[m,n-1] && EqQ[d*e-c*f,0]",
        desc: "Piecewise constant extraction and integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [e__, f__, m_, capital_f_, a__, b__, c__, d__, n_, x_],
        optional: [e__, f__, m_, a__, b__, c__, d__],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__, f__, n_], x_)
                && eqq!(m_, &n_ - 1)
                && eqq!(&d__ * &e__ - &c__ * &f__, 0)
        },
        rhs: {
            let power_affine = &c__ + &d__ * x_;
            let multiplier_affine = &e__ + &f__ * x_;
            rubi_simp(&(
                multiplier_affine.pow(&n_)
                    * capital_f_.pow(&a__ + &b__ * power_affine.pow(&n_))
                    / (&b__ * &f__ * &n_ * power_affine.pow(&n_) * capital_f_.log())
            ), x_)
        },
    ));
}

fn push_rules_rule_2639(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, d__, n_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 2639,
        source: "Int[F_^(a_.+b_.*(c_.+d_.*x_)^n_)/(e_.+f_.*x_),x_Symbol] :=
          F^a*ExpIntegralEi[b*(c+d*x)^n*Log[F]]/(f*n) /;
        FreeQ[{F,a,b,c,d,e,f,n},x] && EqQ[d*e-c*f,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_13(symbols),
        with: [capital_f_, a__, b__, c__, d__, n_, e__, f__, x_],
        optional: [a__, b__, c__, d__, e__, f__],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__, f__, n_], x_)
                && eqq!(&d__ * &e__ - &c__ * &f__, 0)
        },
        rhs: {
            let power_affine = &c__ + &d__ * x_;

            rubi_simp(&(
                capital_f_.pow(a__)
                    * rubi_exp_integral_ei(&b__ * power_affine.pow(&n_) * capital_f_.log())
                    / (&f__ * &n_)
            ), x_)
        },
    ));
}

fn push_rules_rule_2640(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, d__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 2640,
        source: "Int[(c_.+d_.*x_)^m_.*F_^(a_.+b_.*(c_.+d_.*x_)^n_),x_Symbol] :=
          1/(d*(m+1)) \\[Star] Subst[Int[F^(a+b*x^2),x],x,(c+d*x)^(m+1)] /;
        FreeQ[{F,a,b,c,d,m,n},x] && EqQ[n,2*(m+1)]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [c__, d__, m_, capital_f_, a__, b__, n_, x_],
        optional: [c__, d__, m_, a__, b__],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, m_, n_], x_)
                && eqq!(n_, Atom::num(2) * (&m_ + 1))
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let substitution_variable = Atom::var(substitution_symbol);
            let transformed_integrand =
                capital_f_.pow(&a__ + &b__ * substitution_variable.pow(2));
            let transformed_primitive = rubi_rhs_int(&transformed_integrand, substitution_symbol);
            let substitution = (&c__ + &d__ * x_).pow(&m_ + 1);
            let substituted = rubi_subst(&transformed_primitive, substitution_symbol, substitution);

            rubi_star(Atom::num(1) / (&d__ * (&m_ + 1)), substituted)
        },
    ));
}

fn push_rules_rule_2641(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, d__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 2641,
        source: "Int[(c_.+d_.*x_)^m_.*F_^(a_.+b_.*(c_.+d_.*x_)^n_),x_Symbol] :=
          (c+d*x)^(m-n+1)*F^(a+b*(c+d*x)^n)/(b*d*n*Log[F]) -
          (m-n+1)/(b*n*Log[F]) \\[Star] Int[(c+d*x)^(m-n)*F^(a+b*(c+d*x)^n),x] /;
        FreeQ[{F,a,b,c,d},x] && IntegerQ[2*(m+1)/n] && LtQ[0,(m+1)/n,5] && IntegerQ[n] && (LtQ[0,n,m+1] || LtQ[m,n,0])",
        desc: "Integration by parts",
        refs: ["G&R 2.321.1, CRC 521, A&S 4.2.55"],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [c__, d__, m_, capital_f_, a__, b__, n_, x_],
        optional: [c__, d__, m_, a__, b__],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__], x_)
                && integerq!(Atom::num(2) * (&m_ + 1) / &n_)
                && ltq!(0, (&m_ + 1) / &n_, 5)
                && integerq!(n_)
                && (gtq!(n_, 0) && ltq!(n_, &m_ + 1) || ltq!(m_, n_) && ltq!(n_, 0))
        },
        rhs: {
            let affine = &c__ + &d__ * x_;
            let lowered_power = &m_ - &n_;
            let direct_power = &m_ - &n_ + 1;
            let exponential = capital_f_.pow(&a__ + &b__ * affine.pow(&n_));
            let recursive_integrand = affine.pow(&lowered_power) * &exponential;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(
                    &(affine.pow(&direct_power) * exponential
                        / (&b__ * &d__ * &n_ * capital_f_.log())),
                    x_,
                ) - rubi_star(direct_power, recursive / (&b__ * &n_ * capital_f_.log()))
        },
    ));
}

fn push_rules_rule_2642(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, d__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 2642,
        source: "Int[(c_.+d_.*x_)^m_.*F_^(a_.+b_.*(c_.+d_.*x_)^n_),x_Symbol] :=
          (c+d*x)^(m-n+1)*F^(a+b*(c+d*x)^n)/(b*d*n*Log[F]) -
          (m-n+1)/(b*n*Log[F]) \\[Star] Int[(c+d*x)^Simplify[m-n]*F^(a+b*(c+d*x)^n),x] /;
        FreeQ[{F,a,b,c,d,m,n},x] && IntegerQ[2*Simplify[(m+1)/n]] && LtQ[0,Simplify[(m+1)/n],5] && Not[RationalQ[m]] && SumSimplerQ[m,-n]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [c__, d__, m_, capital_f_, a__, b__, n_, x_],
        optional: [c__, d__, m_, a__, b__],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, m_, n_], x_)
                && {
                    let ratio = rubi_simplify(&((&m_ + 1) / &n_));
                    integerq!(Atom::num(2) * &ratio) && ltq!(0, ratio, 5)
                }
                && !rationalq!(m_)
                && rubi_sum_simpler_q(&m_, &(-&n_))
        },
        rhs: {
            let affine = &c__ + &d__ * x_;
            let direct_power = &m_ - &n_ + 1;
            let recursive_power = rubi_simplify(&(&m_ - &n_));
            let exponential = capital_f_.pow(&a__ + &b__ * affine.pow(&n_));
            let recursive = rubi_rhs_int(
                &(affine.pow(recursive_power) * &exponential),
                x_,
            );

            rubi_simp(
                    &(affine.pow(&direct_power) * exponential
                        / (&b__ * &d__ * &n_ * capital_f_.log())),
                    x_,
                ) - rubi_star(direct_power, recursive / (&b__ * &n_ * capital_f_.log()))
        },
    ));
}

fn push_rules_rule_2643(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, d__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 2643,
        source: "Int[(c_.+d_.*x_)^m_.*F_^(a_.+b_.*(c_.+d_.*x_)^n_),x_Symbol] :=
          (c+d*x)^(m+1)*F^(a+b*(c+d*x)^n)/(d*(m+1)) -
          b*n*Log[F]/(m+1) \\[Star] Int[(c+d*x)^(m+n)*F^(a+b*(c+d*x)^n),x] /;
        FreeQ[{F,a,b,c,d},x] && IntegerQ[2*(m+1)/n] && LtQ[-4,(m+1)/n,5] && IntegerQ[n] && (GtQ[n,0] && LtQ[m,-1] || GtQ[-n,0] && LeQ[-n,m+1])",
        desc: "Integration by parts",
        refs: ["G&R 2.324.1, CRC 523, A&S 4.2.56"],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [c__, d__, m_, capital_f_, a__, b__, n_, x_],
        optional: [c__, d__, m_, a__, b__],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__], x_)
                && integerq!(Atom::num(2) * (&m_ + 1) / &n_)
                && ltq!(-4, (&m_ + 1) / &n_, 5)
                && integerq!(n_)
                && {
                    let neg_n = -&n_;
                    gtq!(n_, 0) && ltq!(m_, -1)
                        || gtq!(neg_n, 0) && leq!(neg_n, &m_ + 1)
                }
        },
        rhs: {
            let affine = &c__ + &d__ * x_;
            let direct_power = &m_ + 1;
            let raised_power = &m_ + &n_;
            let exponential = capital_f_.pow(&a__ + &b__ * affine.pow(&n_));
            let recursive = rubi_rhs_int(
                &(affine.pow(raised_power) * &exponential),
                x_,
            );

            rubi_simp(
                    &(affine.pow(&direct_power) * exponential / (&d__ * &direct_power)),
                    x_,
                ) - rubi_star(&b__ * &n_ * capital_f_.log() / &direct_power, recursive)
        },
    ));
}

fn push_rules_rule_2644(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, d__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 2644,
        source: "Int[(c_.+d_.*x_)^m_.*F_^(a_.+b_.*(c_.+d_.*x_)^n_),x_Symbol] :=
          (c+d*x)^(m+1)*F^(a+b*(c+d*x)^n)/(d*(m+1)) -
          b*n*Log[F]/(m+1) \\[Star] Int[(c+d*x)^Simplify[m+n]*F^(a+b*(c+d*x)^n),x] /;
        FreeQ[{F,a,b,c,d,m,n},x] && IntegerQ[2*Simplify[(m+1)/n]] && LtQ[-4,Simplify[(m+1)/n],5] && Not[RationalQ[m]] && SumSimplerQ[m,n]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [c__, d__, m_, capital_f_, a__, b__, n_, x_],
        optional: [c__, d__, m_, a__, b__],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, m_, n_], x_)
                && {
                    let ratio = rubi_simplify(&((&m_ + 1) / &n_));
                    integerq!(Atom::num(2) * &ratio) && ltq!(-4, ratio, 5)
                }
                && !rationalq!(m_)
                && rubi_sum_simpler_q(&m_, &n_)
        },
        rhs: {
            let affine = &c__ + &d__ * x_;
            let direct_power = &m_ + 1;
            let recursive_power = rubi_simplify(&(&m_ + &n_));
            let exponential = capital_f_.pow(&a__ + &b__ * affine.pow(&n_));
            let recursive = rubi_rhs_int(
                &(affine.pow(recursive_power) * &exponential),
                x_,
            );

            rubi_simp(
                    &(affine.pow(&direct_power) * exponential / (&d__ * &direct_power)),
                    x_,
                ) - rubi_star(&b__ * &n_ * capital_f_.log() / &direct_power, recursive)
        },
    ));
}

fn push_rules_rule_2645(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, d__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 2645,
        source: "Int[(c_.+d_.*x_)^m_.*F_^(a_.+b_.*(c_.+d_.*x_)^n_),x_Symbol] :=
          With[{k=Denominator[n]},
          k/d \\[Star] Subst[Int[x^(k*(m+1)-1)*F^(a+b*x^(k*n)),x],x,(c+d*x)^(1/k)]] /;
        FreeQ[{F,a,b,c,d,m,n},x] && IntegerQ[2*(m+1)/n] && LtQ[0,(m+1)/n,5] && Not[IntegerQ[n]]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [c__, d__, m_, capital_f_, a__, b__, n_, x_],
        optional: [c__, d__, m_, a__, b__],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, m_, n_], x_)
                && integerq!(Atom::num(2) * (&m_ + 1) / &n_)
                && ltq!(0, (&m_ + 1) / &n_, 5)
                && !integerq!(n_)
        },
        rhs: {
            let k = denominator!(n_);
            let k_atom = Atom::num(k);
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let substitution_variable = Atom::var(substitution_symbol);
            let transformed_monomial_power = &k_atom * (&m_ + 1) - 1;
            let transformed_exponent_power = &k_atom * &n_;
            let transformed_integrand = substitution_variable.pow(transformed_monomial_power)
                * capital_f_.pow(&a__ + &b__ * substitution_variable.pow(transformed_exponent_power));
            let transformed_primitive = rubi_rhs_int(&transformed_integrand, substitution_symbol);
            let substitution =
                (&c__ + &d__ * x_).pow(Atom::num(1) / &k_atom);
            let substituted = rubi_subst(&transformed_primitive, substitution_symbol, substitution);

            rubi_star(k_atom, substituted / &d__)
        },
    ));
}

fn push_rules_rule_2646(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, d__, m_, n_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 2646,
        source: "Int[(e_.+f_.*x_)^m_.*F_^(a_.+b_.*(c_.+d_.*x_)^n_),x_Symbol] :=
          (e+f*x)^m/(c+d*x)^m \\[Star] Int[(c+d*x)^m*F^(a+b*(c+d*x)^n),x] /;
        FreeQ[{F,a,b,c,d,e,f,m,n},x] && EqQ[d*e-c*f,0] && IntegerQ[2*Simplify[(m+1)/n]] && Not[IntegerQ[m]] && NeQ[f,d] && NeQ[c*e,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [e__, f__, m_, capital_f_, a__, b__, c__, d__, n_, x_],
        optional: [e__, f__, m_, a__, b__, c__, d__],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__, f__, m_, n_], x_)
                && eqq!(&d__ * &e__ - &c__ * &f__, 0)
                && integerq!(Atom::num(2) * rubi_simplify(&((&m_ + 1) / &n_)))
                && !integerq!(m_)
                && neq!(f__, d__)
                && neq!(&c__ * &e__, 0)
        },
        rhs: {
            let multiplier_affine = &e__ + &f__ * x_;
            let base_affine = &c__ + &d__ * x_;
            let exponential = capital_f_.pow(&a__ + &b__ * base_affine.pow(&n_));
            let recursive = rubi_rhs_int(&(base_affine.pow(&m_) * exponential), x_);

            rubi_star(multiplier_affine.pow(&m_), recursive / base_affine.pow(m_))
        },
    ));
}

fn push_rules_rule_2647(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, d__, m_, n_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 2647,
        source: "Int[(e_.+f_.*x_)^m_.*F_^(a_.+b_.*(c_.+d_.*x_)^n_),x_Symbol] :=
          With[{p=Simplify[(m+1)/n]},
          -F^a*(f/d)^m/(d*n*(-b*Log[F])^p)*Simplify[FunctionExpand[Gamma[p,-b*(c+d*x)^n*Log[F]]]] /;
          IGtQ[p,0]] /;
        FreeQ[{F,a,b,c,d,e,f,m,n},x] && EqQ[d*e-c*f,0] && Not[TrueQ[$UseGamma]]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [e__, f__, m_, capital_f_, a__, b__, c__, d__, n_, x_],
        optional: [e__, f__, m_, a__, b__, c__, d__],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__, f__, m_, n_], x_)
                && eqq!(&d__ * &e__ - &c__ * &f__, 0)
                && !rubi_true_q_use_gamma()
                && {
                    let p = rubi_simplify(&((&m_ + 1) / &n_));
                    igtq!(p, 0)
                }
        },
        rhs: {
            let p = rubi_simplify(&((&m_ + 1) / &n_));
            let base_affine = &c__ + &d__ * x_;
            let gamma_argument = -&b__ * base_affine.pow(&n_) * capital_f_.log();
            let gamma = rubi_simplify(&rubi_function_expand(&rubi_gamma(&p, gamma_argument)));

            rubi_simp(&(
                -capital_f_.pow(a__) * (&f__ / &d__).pow(&m_) * gamma
                    / (&d__ * &n_ * (-&b__ * capital_f_.log()).pow(p))
            ), x_)
        },
    ));
}

fn push_rules_rule_2648(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, d__, m_, n_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 2648,
        source: "Int[(e_.+f_.*x_)^m_.*F_^(a_.+b_.*(c_.+d_.*x_)^n_),x_Symbol] :=
          -F^a*(e+f*x)^(m+1)/(f*n*(-b*(c+d*x)^n*Log[F])^((m+1)/n))*Gamma[(m+1)/n,-b*(c+d*x)^n*Log[F]] /;
        FreeQ[{F,a,b,c,d,e,f,m,n},x] && EqQ[d*e-c*f,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [e__, f__, m_, capital_f_, a__, b__, c__, d__, n_, x_],
        optional: [e__, f__, m_, a__, b__, c__, d__],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__, f__, m_, n_], x_)
                && eqq!(&d__ * &e__ - &c__ * &f__, 0)
        },
        rhs: {
            let multiplier_affine = &e__ + &f__ * x_;
            let base_affine = &c__ + &d__ * x_;
            let p = (&m_ + 1) / &n_;
            let gamma_argument = -&b__ * base_affine.pow(&n_) * capital_f_.log();
            let gamma = rubi_gamma(&p, &gamma_argument);

            rubi_simp(&(
                -capital_f_.pow(a__) * multiplier_affine.pow(&m_ + 1) * gamma
                    / (&f__ * &n_ * gamma_argument.pow(p))
            ), x_)
        },
    ));
}

fn push_rules_rule_2649(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, d__, m_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 2649,
        source: "Int[(e_.+f_.*x_)^m_*F_^(a_.+b_.*(c_.+d_.*x_)^2),x_Symbol] :=
          f*(e+f*x)^(m-1)*F^(a+b*(c+d*x)^2)/(2*b*d^2*Log[F]) +
          (d*e-c*f)/d \\[Star] Int[(e+f*x)^(m-1)*F^(a+b*(c+d*x)^2),x] -
          (m-1)*f^2/(2*b*d^2*Log[F]) \\[Star] Int[(e+f*x)^(m-2)*F^(a+b*(c+d*x)^2),x] /;
        FreeQ[{F,a,b,c,d,e,f},x] && NeQ[d*e-c*f,0] && FractionQ[m] && GtQ[m,1]",
        desc: "Inverted integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [e__, f__, m_, capital_f_, a__, b__, c__, d__, x_],
        optional: [e__, f__, a__, b__, c__, d__],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__, f__], x_)
                && neq!(&d__ * &e__ - &c__ * &f__, 0)
                && fractionq!(m_)
                && gtq!(m_, 1)
        },
        rhs: {
            let multiplier_affine = &e__ + &f__ * x_;
            let base_affine = &c__ + &d__ * x_;
            let exponential = capital_f_.pow(&a__ + &b__ * base_affine.pow(2));
            let denominator = Atom::num(2) * &b__ * &d__ * &d__ * capital_f_.log();
            let recursive_1 = rubi_rhs_int(
                &(multiplier_affine.pow(&m_ - 1) * &exponential),
                x_,
            );
            let recursive_2 = rubi_rhs_int(
                &(multiplier_affine.pow(&m_ - 2) * &exponential),
                x_,
            );

            rubi_simp(
                    &(&f__ * multiplier_affine.pow(&m_ - 1) * exponential / &denominator),
                    x_,
                ) + rubi_star(&d__ * &e__ - &c__ * &f__, recursive_1 / &d__) - rubi_star((&m_ - 1) * &f__ * &f__ / denominator, recursive_2)
        },
    ));
}

fn push_rules_rule_2650(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, d__, m_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 2650,
        source: "Int[(e_.+f_.*x_)^m_*F_^(a_.+b_.*(c_.+d_.*x_)^2),x_Symbol] :=
          f*(e+f*x)^(m+1)*F^(a+b*(c+d*x)^2)/((m+1)*f^2) +
          2*b*d*(d*e-c*f)*Log[F]/(f^2*(m+1)) \\[Star] Int[(e+f*x)^(m+1)*F^(a+b*(c+d*x)^2),x] -
          2*b*d^2*Log[F]/(f^2*(m+1)) \\[Star] Int[(e+f*x)^(m+2)*F^(a+b*(c+d*x)^2),x] /;
        FreeQ[{F,a,b,c,d,e,f},x] && NeQ[d*e-c*f,0] && LtQ[m,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [e__, f__, m_, capital_f_, a__, b__, c__, d__, x_],
        optional: [e__, f__, a__, b__, c__, d__],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__, f__], x_)
                && neq!(&d__ * &e__ - &c__ * &f__, 0)
                && ltq!(m_, -1)
        },
        rhs: {
            let multiplier_affine = &e__ + &f__ * x_;
            let base_affine = &c__ + &d__ * x_;
            let exponential = capital_f_.pow(&a__ + &b__ * base_affine.pow(2));
            let denominator = &f__ * &f__ * (&m_ + 1);
            let recursive_1 = rubi_rhs_int(
                &(multiplier_affine.pow(&m_ + 1) * &exponential),
                x_,
            );
            let recursive_2 = rubi_rhs_int(
                &(multiplier_affine.pow(&m_ + 2) * &exponential),
                x_,
            );

            rubi_simp(
                    &(&f__ * multiplier_affine.pow(&m_ + 1) * exponential / &denominator),
                    x_,
                ) + rubi_star(Atom::num(2) * &b__ * &d__ * (&d__ * &e__ - &c__ * &f__) * capital_f_.log() / &denominator, recursive_1) - rubi_star(Atom::num(2) * &b__ * &d__ * &d__ * capital_f_.log() / denominator, recursive_2)
        },
    ));
}

fn push_rules_rule_2651(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, d__, m_, n_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 2651,
        source: "Int[(e_.+f_.*x_)^m_*F_^(a_.+b_.*(c_.+d_.*x_)^n_),x_Symbol] :=
          (e+f*x)^(m+1)*F^(a+b*(c+d*x)^n)/(f*(m+1)) -
          b*d*n*Log[F]/(f*(m+1)) \\[Star] Int[(e+f*x)^(m+1)*(c+d*x)^(n-1)*F^(a+b*(c+d*x)^n),x] /;
        FreeQ[{F,a,b,c,d,e,f},x] && NeQ[d*e-c*f,0] && IGtQ[n,2] && LtQ[m,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [e__, f__, m_, capital_f_, a__, b__, c__, d__, n_, x_],
        optional: [e__, f__, a__, b__, c__, d__],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__, f__], x_)
                && neq!(&d__ * &e__ - &c__ * &f__, 0)
                && igtq!(n_, 2)
                && ltq!(m_, -1)
        },
        rhs: {
            let multiplier_affine = &e__ + &f__ * x_;
            let base_affine = &c__ + &d__ * x_;
            let exponential = capital_f_.pow(&a__ + &b__ * base_affine.pow(&n_));
            let recursive_integrand = multiplier_affine.pow(&m_ + 1)
                * base_affine.pow(&n_ - 1)
                * &exponential;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(
                    &(multiplier_affine.pow(&m_ + 1) * exponential / (&f__ * (&m_ + 1))),
                    x_,
                ) - rubi_star(&b__ * &d__ * &n_ * capital_f_.log() / (&f__ * (&m_ + 1)), recursive)
        },
    ));
}

fn push_rules_rule_2652(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_f_, a__, b__, c__, d__, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 2652,
        source: "Int[F_^(a_.+b_./(c_.+d_.*x_))/(e_.+f_.*x_),x_Symbol] :=
          d/f \\[Star] Int[F^(a+b/(c+d*x))/(c+d*x),x] -
          (d*e-c*f)/f \\[Star] Int[F^(a+b/(c+d*x))/((c+d*x)*(e+f*x)),x] /;
        FreeQ[{F,a,b,c,d,e,f},x] && NeQ[d*e-c*f,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: capital_f_.pow(a__ + b__ / (c__ + d__ * x_)) / (e__ + f__ * x_),
        with: [capital_f_, a__, b__, c__, d__, e__, f__, x_],
        optional: [a__, b__, c__, d__, e__, f__],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__, f__], x_)
                && neq!(&d__ * &e__ - &c__ * &f__, 0)
        },
        rhs: {
            let base_affine = &c__ + &d__ * x_;
            let denominator_affine = &e__ + &f__ * x_;
            let exponential = capital_f_.pow(&a__ + &b__ / &base_affine);
            let first_integrand = &exponential / &base_affine;
            let first = rubi_rhs_int(&first_integrand, x_);
            let second_integrand = exponential / (&base_affine * denominator_affine);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(&d__, first / &f__)
                    - rubi_star(&d__ * &e__ - &c__ * &f__, second / &f__)
        },
    ));
}

fn push_rules_rule_2653(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_f_, a__, b__, c__, d__, m_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 2653,
        source: "Int[(e_.+f_.*x_)^m_*F_^(a_.+b_./(c_.+d_.*x_)),x_Symbol] :=
          (e+f*x)^(m+1)*F^(a+b/(c+d*x))/(f*(m+1)) +
          b*d*Log[F]/(f*(m+1)) \\[Star] Int[(e+f*x)^(m+1)*F^(a+b/(c+d*x))/(c+d*x)^2,x] /;
        FreeQ[{F,a,b,c,d,e,f},x] && NeQ[d*e-c*f,0] && ILtQ[m,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern: (e__ + f__ * x_).pow(m_) * capital_f_.pow(a__ + b__ / (c__ + d__ * x_)),
        with: [e__, f__, m_, capital_f_, a__, b__, c__, d__, x_],
        optional: [e__, f__, a__, b__, c__, d__],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__, f__], x_)
                && neq!(&d__ * &e__ - &c__ * &f__, 0)
                && iltq!(m_, -1)
        },
        rhs: {
            let multiplier_affine = &e__ + &f__ * x_;
            let base_affine = &c__ + &d__ * x_;
            let exponential = capital_f_.pow(&a__ + &b__ / &base_affine);
            let recursive_integrand =
                multiplier_affine.pow(&m_ + 1) * &exponential / base_affine.pow(2);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(
                    &(multiplier_affine.pow(&m_ + 1) * exponential / (&f__ * (&m_ + 1))),
                    x_,
                ) + rubi_star(&b__ * &d__ * capital_f_.log() / (&f__ * (&m_ + 1)), recursive)
        },
    ));
}

fn push_rules_rule_2654(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, d__, n_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 2654,
        source: "Int[F_^(a_.+b_.*(c_.+d_.*x_)^n_)/(e_.+f_.*x_),x_Symbol] :=
          Unintegrable[F^(a+b*(c+d*x)^n)/(e+f*x),x] /;
        FreeQ[{F,a,b,c,d,e,f,n},x] && NeQ[d*e-c*f,0]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_13(symbols),
        with: [capital_f_, a__, b__, c__, d__, n_, e__, f__, x_],
        optional: [a__, b__, c__, d__, e__, f__],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__, f__, n_], x_)
                && neq!(&d__ * &e__ - &c__ * &f__, 0)
        },
        rhs: {
            let integrand =
                capital_f_.pow(&a__ + &b__ * (&c__ + &d__ * x_).pow(&n_))
                    / (&e__ + &f__ * x_);

            rubi_unintegrable(integrand, x_)
        },
    ));
}

fn push_rules_rule_2655(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_f_, e__, f__, m_, v_, x_);
    rules.push(rubi_rule!(
        order: 2655,
        source: "Int[(e_.+f_.*x_)^m_.*F_^v_,x_Symbol] :=
          Int[(e+f*x)^m*F^ExpandToSum[v,x],x] /;
        FreeQ[{F,e,f,m},x] && BinomialQ[v,x] && Not[BinomialMatchQ[v,x]]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern: (e__ + f__ * x_).pow(m_) * capital_f_.pow(v_),
        with: [e__, f__, m_, capital_f_, v_, x_],
        optional: [e__, f__, m_],
        when: {
            freeq!([capital_f_, e__, f__, m_], x_)
                && rubi_binomial_q(&v_, x_)
                && !rubi_binomial_match_q(&v_, x_)
        },
        rhs: {
            let expanded_v = rubi_expand_to_sum(&v_, x_);
            let recursive_integrand = (&e__ + &f__ * x_).pow(&m_)
                * capital_f_.pow(expanded_v);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_2656(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_f_, a__, b__, c__, d__, n_, px__, x_);
    rules.push(rubi_rule!(
        order: 2656,
        source: "Int[Px_*F_^(a_.+b_.*(c_.+d_.*x_)^n_),x_Symbol] :=
          Int[ExpandLinearProduct[F^(a+b*(c+d*x)^n),Px,c,d,x],x] /;
        FreeQ[{F,a,b,c,d,n},x] && PolynomialQ[Px,x]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern: px__ * capital_f_.pow(a__ + b__ * (c__ + d__ * x_).pow(n_)),
        with: [px__, capital_f_, a__, b__, c__, d__, n_, x_],
        optional: [a__, b__, c__, d__],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, n_], x_)
                && rubi_polynomial_q(&px__, x_)
        },
        rhs: {
            let expanded = rubi_expand_linear_product(
                &capital_f_.pow(&a__ + &b__ * (&c__ + &d__ * x_).pow(&n_)),
                &px__,
                &c__,
                &d__,
                x_,
            )
            .unwrap();

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_2657(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_f_, a__, b__, n_, px__, v_);
    rules.push(rubi_rule!(
        order: 2657,
        source: "Int[Px_.*F_^(a_.+b_.*v_^n_.),x_Symbol] :=
          Int[Px*F^(a+b*ExpandToSum[v,x]^n),x] /;
        FreeQ[{F,a,b,n},x] && PolynomialQ[Px,x] && LinearQ[v,x] && Not[LinearMatchQ[v,x]]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern: px__ * capital_f_.pow(a__ + b__ * v_.pow(n_)),
        with: [px__, capital_f_, a__, b__, v_, n_, x_],
        optional: [px__, a__, b__, n_],
        when: {
            freeq!([capital_f_, a__, b__, n_], x_)
                && rubi_polynomial_q(&px__, x_)
                && rubi_linear_q(&v_, x_)
                && !rubi_linear_match_q(&v_, x_)
        },
        rhs: {
            let expanded = rubi_expand_to_sum(&v_, x_);
            let recursive_integrand =
                &px__ * capital_f_.pow(&a__ + &b__ * expanded.pow(&n_));

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_2658(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_f_, a__, b__, c__, d__, x_, e__, f__, g__, h__);
    rules.push(rubi_rule!(
        order: 2658,
        source: "Int[F_^(a_.+b_./(c_.+d_.*x_))/((e_.+f_.*x_)*(g_.+h_.*x_)),x_Symbol] :=
          -d/(f*(d*g-c*h)) \\[Star] Subst[Int[F^(a-b*h/(d*g-c*h)+d*b*x/(d*g-c*h))/x,x],x,(g+h*x)/(c+d*x)] /;
        FreeQ[{F,a,b,c,d,e,f},x] && EqQ[d*e-c*f,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: capital_f_.pow(a__ + b__ / (c__ + d__ * x_))
            / ((e__ + f__ * x_) * (g__ + h__ * x_)),
        with: [capital_f_, a__, b__, c__, d__, e__, f__, g__, h__, x_],
        optional: [a__, b__, c__, d__, e__, f__, g__, h__],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__, f__], x_)
                && eqq!(&d__ * &e__ - &c__ * &f__, 0)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let substitution_variable = Atom::var(substitution_symbol);
            let transformed_denominator = &d__ * &g__ - &c__ * &h__;
            let transformed_integrand = capital_f_.pow(
                &a__ - &b__ * &h__ / &transformed_denominator
                    + &d__ * &b__ * &substitution_variable / &transformed_denominator,
            ) / &substitution_variable;
            let transformed_primitive = rubi_rhs_int(&transformed_integrand, substitution_symbol);
            let substitution = (&g__ + &h__ * x_) / (&c__ + &d__ * x_);

            rubi_star(-&d__, rubi_subst(&transformed_primitive, substitution_symbol, substitution)
                    / (&f__ * transformed_denominator))
        },
    ));
}

fn push_rules_rule_2659(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, d__, m_, x_, e__, f__, g__, h__);
    rules.push(rubi_rule!(
        order: 2659,
        source: "Int[(g_.+h_.*x_)^m_.*F_^(e_.+f_.*(a_.+b_.*x_)/(c_.+d_.*x_)),x_Symbol] :=
          F^(e+f*b/d) \\[Star] Int[(g+h*x)^m,x] /;
        FreeQ[{F,a,b,c,d,e,f,g,h,m},x] && EqQ[b*c-a*d,0]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [g__, h__, m_, capital_f_, e__, f__, a__, b__, c__, d__, x_],
        optional: [g__, h__, m_, e__, f__, a__, b__, c__, d__],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__, f__, g__, h__, m_], x_)
                && eqq!(&b__ * &c__ - &a__ * &d__, 0)
        },
        rhs: {
            let exponential = capital_f_.pow(&e__ + &f__ * &b__ / &d__);
            let primitive = rubi_rhs_int(
                &(&g__ + &h__ * x_).pow(&m_),
                x_,
            );

            rubi_star(exponential, primitive)
        },
    ));
}

fn push_rules_rule_2660(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, d__, m_, x_, e__, f__, g__, h__);
    rules.push(rubi_rule!(
        order: 2660,
        source: "Int[(g_.+h_.*x_)^m_.*F_^(e_.+f_.*(a_.+b_.*x_)/(c_.+d_.*x_)),x_Symbol] :=
          Int[(g+h*x)^m*F^((d*e+b*f)/d-f*(b*c-a*d)/(d*(c+d*x))),x] /;
        FreeQ[{F,a,b,c,d,e,f,g,h,m},x] && NeQ[b*c-a*d,0] && EqQ[d*g-c*h,0]",
        desc: "Algebraic normalization",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [g__, h__, m_, capital_f_, e__, f__, a__, b__, c__, d__, x_],
        optional: [g__, h__, m_, e__, f__, a__, b__, c__, d__],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__, f__, g__, h__, m_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(&d__ * &g__ - &c__ * &h__, 0)
        },
        rhs: {
            let recursive_integrand = (&g__ + &h__ * x_).pow(&m_)
                * capital_f_.pow(
                    (&d__ * &e__ + &b__ * &f__) / &d__
                        - &f__ * (&b__ * &c__ - &a__ * &d__)
                            / (&d__ * (&c__ + &d__ * x_)),
                );
            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_2661(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_f_, a__, b__, c__, d__, x_, e__, f__, g__, h__);
    rules.push(rubi_rule!(
        order: 2661,
        source: "Int[F_^(e_.+f_.*(a_.+b_.*x_)/(c_.+d_.*x_))/(g_.+h_.*x_),x_Symbol] :=
          d/h \\[Star] Int[F^(e+f*(a+b*x)/(c+d*x))/(c+d*x),x] -
          (d*g-c*h)/h \\[Star] Int[F^(e+f*(a+b*x)/(c+d*x))/((c+d*x)*(g+h*x)),x] /;
        FreeQ[{F,a,b,c,d,e,f,g,h},x] && NeQ[b*c-a*d,0] && NeQ[d*g-c*h,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: capital_f_.pow(e__ + f__ * (a__ + b__ * x_) / (c__ + d__ * x_))
            / (g__ + h__ * x_),
        with: [capital_f_, e__, f__, a__, b__, c__, d__, g__, h__, x_],
        optional: [e__, f__, a__, b__, c__, d__, g__, h__],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__, f__, g__, h__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && neq!(&d__ * &g__ - &c__ * &h__, 0)
        },
        rhs: {
            let affine_denominator = &c__ + &d__ * x_;
            let other_denominator = &g__ + &h__ * x_;
            let exponential = capital_f_
                .pow(&e__ + &f__ * (&a__ + &b__ * x_) / &affine_denominator);
            let first_integrand = &exponential / &affine_denominator;
            let first_recursive = rubi_rhs_int(&first_integrand, x_);
            let second_integrand =
                &exponential / (&affine_denominator * &other_denominator);
            let second_recursive = rubi_rhs_int(&second_integrand, x_);

            rubi_star(&d__, first_recursive / &h__)
                    - rubi_star(&d__ * &g__ - &c__ * &h__, second_recursive / &h__)
        },
    ));
}

fn push_rules_rule_2662(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, d__, m_, x_, e__, f__, g__, h__);
    rules.push(rubi_rule!(
        order: 2662,
        source: "Int[(g_.+h_.*x_)^m_*F_^(e_.+f_.*(a_.+b_.*x_)/(c_.+d_.*x_)),x_Symbol] :=
          (g+h*x)^(m+1)*F^(e+f*(a+b*x)/(c+d*x))/(h*(m+1)) -
          f*(b*c-a*d)*Log[F]/(h*(m+1)) \\[Star] Int[(g+h*x)^(m+1)*F^(e+f*(a+b*x)/(c+d*x))/(c+d*x)^2,x] /;
        FreeQ[{F,a,b,c,d,e,f,g,h},x] && NeQ[b*c-a*d,0] && NeQ[d*g-c*h,0] && ILtQ[m,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [g__, h__, m_, capital_f_, e__, f__, a__, b__, c__, d__, x_],
        optional: [g__, h__, e__, f__, a__, b__, c__, d__],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__, f__, g__, h__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && neq!(&d__ * &g__ - &c__ * &h__, 0)
                && iltq!(m_, -1)
        },
        rhs: {
            let raised_power = &m_ + 1;
            let affine_denominator = &c__ + &d__ * x_;
            let other_affine = &g__ + &h__ * x_;
            let exponential = capital_f_
                .pow(&e__ + &f__ * (&a__ + &b__ * x_) / &affine_denominator);
            let recursive_integrand =
                other_affine.pow(&raised_power) * &exponential / affine_denominator.pow(2);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(
                    &(other_affine.pow(&raised_power) * &exponential / (&h__ * &raised_power)),
                    x_,
                ) - rubi_star(&f__ * (&b__ * &c__ - &a__ * &d__) * capital_f_.log() / (&h__ * &raised_power), recursive)
        },
    ));
}

fn push_rules_rule_2663(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        capital_f_, a__, b__, c__, d__, x_, e__, f__, g__, h__, i__, j__
    );
    rules.push(rubi_rule!(
        order: 2663,
        source: "Int[F_^(e_.+f_.*(a_.+b_.*x_)/(c_.+d_.*x_))/((g_.+h_.*x_)*(i_.+j_.*x_)),x_Symbol] :=
          -d/(h*(d*i-c*j)) \\[Star] Subst[Int[F^(e+f*(b*i-a*j)/(d*i-c*j)-(b*c-a*d)*f*x/(d*i-c*j))/x,x],x,(i+j*x)/(c+d*x)] /;
        FreeQ[{F,a,b,c,d,e,f,g,h},x] && EqQ[d*g-c*h,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: capital_f_.pow(e__ + f__ * (a__ + b__ * x_) / (c__ + d__ * x_))
            / ((g__ + h__ * x_) * (i__ + j__ * x_)),
        with: [capital_f_, e__, f__, a__, b__, c__, d__, g__, h__, i__, j__, x_],
        optional: [e__, f__, a__, b__, c__, d__, g__, h__, i__, j__],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__, f__, g__, h__], x_)
                && eqq!(&d__ * &g__ - &c__ * &h__, 0)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let substitution_variable = Atom::var(substitution_symbol);
            let transformed_denominator = &d__ * &i__ - &c__ * &j__;
            let transformed_integrand = capital_f_.pow(
                &e__ + &f__ * (&b__ * &i__ - &a__ * &j__) / &transformed_denominator
                    - (&b__ * &c__ - &a__ * &d__) * &f__ * &substitution_variable
                        / &transformed_denominator,
            ) / &substitution_variable;
            let transformed_primitive = rubi_rhs_int(&transformed_integrand, substitution_symbol);
            let substitution = (&i__ + &j__ * x_) / (&c__ + &d__ * x_);

            rubi_star(-&d__, rubi_subst(&transformed_primitive, substitution_symbol, substitution)
                    / (&h__ * transformed_denominator))
        },
    ));
}

fn push_rules_rule_2664(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_f_, a__, b__, c__, x_);
    rules.push(rubi_rule!(
        order: 2664,
        source: "Int[F_^(a_.+b_.*x_+c_.*x_^2),x_Symbol] :=
          F^(a-b^2/(4*c)) \\[Star] Int[F^((b+2*c*x)^2/(4*c)),x] /;
        FreeQ[{F,a,b,c},x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: capital_f_.pow(a__ + b__ * x_ + c__ * x_.pow(2)),
        with: [capital_f_, a__, b__, c__, x_],
        optional: [a__, b__, c__],
        when: {
            freeq!([capital_f_, a__, b__, c__], x_)
        },
        rhs: {
            let recursive_integrand =
                capital_f_.pow((&b__ + Atom::num(2) * &c__ * x_).pow(2) / (4 * &c__));
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(capital_f_.pow(&a__ - b__.pow(2) / (4 * &c__)), recursive)
        },
    ));
}

fn push_rules_rule_2665(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_f_, v_);
    rules.push(rubi_rule!(
        order: 2665,
        source: "Int[F_^v_,x_Symbol] :=
          Int[F^ExpandToSum[v,x],x] /;
        FreeQ[F,x] && QuadraticQ[v,x] && Not[QuadraticMatchQ[v,x]]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: capital_f_.pow(v_),
        with: [capital_f_, v_, x_],
        when: {
            freeq!(capital_f_, x_) && rubi_quadratic_q(&v_, x_) && !rubi_quadratic_match_q(&v_, x_)
        },
        rhs: {
            let recursive_integrand = capital_f_.pow(rubi_expand_to_sum(&v_, x_));
            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_2666(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, d__, x_, e__);
    rules.push(rubi_rule!(
        order: 2666,
        source: "Int[(d_.+e_.*x_)*F_^(a_.+b_.*x_+c_.*x_^2),x_Symbol] :=
          e*F^(a+b*x+c*x^2)/(2*c*Log[F]) /;
        FreeQ[{F,a,b,c,d,e},x] && EqQ[b*e-2*c*d,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [d__, e__, capital_f_, a__, b__, c__, x_],
        optional: [d__, e__, a__, b__, c__],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__], x_)
                && eqq!(&b__ * &e__ - Atom::num(2) * &c__ * &d__, 0)
        },
        rhs: {
            let denominator = Atom::num(2) * &c__ * capital_f_.log();
            let exponential = capital_f_.pow(&a__ + &b__ * x_ + &c__ * x_.pow(2));

            rubi_simp(&(&e__ * exponential / denominator), x_)
        },
    ));
}

fn push_rules_rule_2667(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, d__, m_, x_, e__);
    rules.push(rubi_rule!(
        order: 2667,
        source: "Int[(d_.+e_.*x_)^m_*F_^(a_.+b_.*x_+c_.*x_^2),x_Symbol] :=
          e*(d+e*x)^(m-1)*F^(a+b*x+c*x^2)/(2*c*Log[F]) -
          (m-1)*e^2/(2*c*Log[F]) \\[Star] Int[(d+e*x)^(m-2)*F^(a+b*x+c*x^2),x] /;
        FreeQ[{F,a,b,c,d,e},x] && EqQ[b*e-2*c*d,0] && GtQ[m,1]",
        desc: "Inverted integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [d__, e__, m_, capital_f_, a__, b__, c__, x_],
        optional: [d__, e__, a__, b__, c__],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__], x_)
                && eqq!(&b__ * &e__ - Atom::num(2) * &c__ * &d__, 0)
                && gtq!(m_, 1)
        },
        rhs: {
            let denominator = Atom::num(2) * &c__ * capital_f_.log();
            let affine = &d__ + &e__ * x_;
            let exponential = capital_f_.pow(&a__ + &b__ * x_ + &c__ * x_.pow(2));
            let recursive_integrand = affine.pow(&m_ - 2) * &exponential;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(
                    &(&e__ * affine.pow(&m_ - 1) * &exponential / &denominator),
                    x_,
                ) - rubi_star((&m_ - 1) * e__.pow(2) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_2668(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_f_, a__, b__, c__, d__, x_, e__);
    rules.push(rubi_rule!(
        order: 2668,
        source: "Int[F_^(a_.+b_.*x_+c_.*x_^2)/(d_.+e_.*x_),x_Symbol] :=
          1/(2*e)*F^(a-b^2/(4*c))*ExpIntegralEi[(b+2*c*x)^2*Log[F]/(4*c)] /;
        FreeQ[{F,a,b,c,d,e},x] && EqQ[b*e-2*c*d,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: capital_f_.pow(a__ + b__ * x_ + c__ * x_.pow(2)) / (d__ + e__ * x_),
        with: [capital_f_, a__, b__, c__, d__, e__, x_],
        optional: [a__, b__, c__, d__, e__],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__], x_)
                && eqq!(&b__ * &e__ - Atom::num(2) * &c__ * &d__, 0)
        },
        rhs: {
            let exp_integral_argument =
                (&b__ + Atom::num(2) * &c__ * x_).pow(2) * capital_f_.log() / (4 * &c__);

            rubi_simp(&(
                capital_f_.pow(&a__ - b__.pow(2) / (4 * &c__))
                    * rubi_exp_integral_ei(exp_integral_argument)
                    / (2 * &e__)
            ), x_)
        },
    ));
}

fn push_rules_rule_2669(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, d__, m_, x_, e__);
    rules.push(rubi_rule!(
        order: 2669,
        source: "Int[(d_.+e_.*x_)^m_*F_^(a_.+b_.*x_+c_.*x_^2),x_Symbol] :=
          (d+e*x)^(m+1)*F^(a+b*x+c*x^2)/(e*(m+1)) -
          2*c*Log[F]/(e^2*(m+1)) \\[Star] Int[(d+e*x)^(m+2)*F^(a+b*x+c*x^2),x] /;
        FreeQ[{F,a,b,c,d,e},x] && EqQ[b*e-2*c*d,0] && LtQ[m,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [d__, e__, m_, capital_f_, a__, b__, c__, x_],
        optional: [d__, e__, a__, b__, c__],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__], x_)
                && eqq!(&b__ * &e__ - Atom::num(2) * &c__ * &d__, 0)
                && ltq!(m_, -1)
        },
        rhs: {
            let raised_power = &m_ + 1;
            let affine = &d__ + &e__ * x_;
            let exponential = capital_f_.pow(&a__ + &b__ * x_ + &c__ * x_.pow(2));
            let recursive_integrand = affine.pow(&m_ + 2) * &exponential;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(
                    &(affine.pow(&raised_power) * &exponential / (&e__ * &raised_power)),
                    x_,
                ) - rubi_star(Atom::num(2) * &c__ * capital_f_.log() / (e__.pow(2) * raised_power), recursive)
        },
    ));
}

fn push_rules_rule_2670(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, d__, x_, e__);
    rules.push(rubi_rule!(
        order: 2670,
        source: "Int[(d_.+e_.*x_)*F_^(a_.+b_.*x_+c_.*x_^2),x_Symbol] :=
          e*F^(a+b*x+c*x^2)/(2*c*Log[F]) -
          (b*e-2*c*d)/(2*c) \\[Star] Int[F^(a+b*x+c*x^2),x] /;
        FreeQ[{F,a,b,c,d,e},x] && NeQ[b*e-2*c*d,0]",
        desc: "Inverted integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [d__, e__, capital_f_, a__, b__, c__, x_],
        optional: [d__, e__, a__, b__, c__],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__], x_)
                && neq!(&b__ * &e__ - Atom::num(2) * &c__ * &d__, 0)
        },
        rhs: {
            let exponential = capital_f_.pow(&a__ + &b__ * x_ + &c__ * x_.pow(2));
            let recursive = rubi_rhs_int(&exponential, x_);

            rubi_simp(
                    &(&e__ * &exponential / (Atom::num(2) * &c__ * capital_f_.log())),
                    x_,
                ) - rubi_star(&b__ * &e__ - Atom::num(2) * &c__ * &d__, recursive
                        / (2 * &c__))
        },
    ));
}

fn push_rules_rule_2671(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, d__, m_, x_, e__);
    rules.push(rubi_rule!(
        order: 2671,
        source: "Int[(d_.+e_.*x_)^m_*F_^(a_.+b_.*x_+c_.*x_^2),x_Symbol] :=
          e*(d+e*x)^(m-1)*F^(a+b*x+c*x^2)/(2*c*Log[F]) -
          (b*e-2*c*d)/(2*c) \\[Star] Int[(d+e*x)^(m-1)*F^(a+b*x+c*x^2),x] -
          (m-1)*e^2/(2*c*Log[F]) \\[Star] Int[(d+e*x)^(m-2)*F^(a+b*x+c*x^2),x] /;
        FreeQ[{F,a,b,c,d,e},x] && NeQ[b*e-2*c*d,0] && GtQ[m,1]",
        desc: "Inverted integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [d__, e__, m_, capital_f_, a__, b__, c__, x_],
        optional: [d__, e__, a__, b__, c__],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__], x_)
                && neq!(&b__ * &e__ - Atom::num(2) * &c__ * &d__, 0)
                && gtq!(m_, 1)
        },
        rhs: {
            let denominator = Atom::num(2) * &c__ * capital_f_.log();
            let affine = &d__ + &e__ * x_;
            let exponential = capital_f_.pow(&a__ + &b__ * x_ + &c__ * x_.pow(2));
            let balance = &b__ * &e__ - Atom::num(2) * &c__ * &d__;
            let first_recursive =
                rubi_rhs_int(&(affine.pow(&m_ - 1) * &exponential), x_);
            let second_recursive =
                rubi_rhs_int(&(affine.pow(&m_ - 2) * &exponential), x_);

            rubi_simp(
                    &(&e__ * affine.pow(&m_ - 1) * &exponential / &denominator),
                    x_,
                ) - rubi_star(balance, first_recursive / (2 * &c__))
                    - rubi_star((&m_ - 1) * e__.pow(2) / denominator, second_recursive)
        },
    ));
}

fn push_rules_rule_2672(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, d__, m_, x_, e__);
    rules.push(rubi_rule!(
        order: 2672,
        source: "Int[(d_.+e_.*x_)^m_*F_^(a_.+b_.*x_+c_.*x_^2),x_Symbol] :=
          (d+e*x)^(m+1)*F^(a+b*x+c*x^2)/(e*(m+1)) -
          (b*e-2*c*d)*Log[F]/(e^2*(m+1)) \\[Star] Int[(d+e*x)^(m+1)*F^(a+b*x+c*x^2),x] -
          2*c*Log[F]/(e^2*(m+1)) \\[Star] Int[(d+e*x)^(m+2)*F^(a+b*x+c*x^2),x] /;
        FreeQ[{F,a,b,c,d,e},x] && NeQ[b*e-2*c*d,0] && LtQ[m,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [d__, e__, m_, capital_f_, a__, b__, c__, x_],
        optional: [d__, e__, a__, b__, c__],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__], x_)
                && neq!(&b__ * &e__ - Atom::num(2) * &c__ * &d__, 0)
                && ltq!(m_, -1)
        },
        rhs: {
            let raised_power = &m_ + 1;
            let affine = &d__ + &e__ * x_;
            let exponential = capital_f_.pow(&a__ + &b__ * x_ + &c__ * x_.pow(2));
            let balance = &b__ * &e__ - Atom::num(2) * &c__ * &d__;
            let denominator = e__.pow(2) * &raised_power;
            let first_recursive =
                rubi_rhs_int(&(affine.pow(&raised_power) * &exponential), x_);
            let second_recursive =
                rubi_rhs_int(&(affine.pow(&m_ + 2) * &exponential), x_);

            rubi_simp(
                    &(affine.pow(&raised_power) * &exponential / (&e__ * &raised_power)),
                    x_,
                ) - rubi_star(balance * capital_f_.log() / &denominator, first_recursive) - rubi_star(Atom::num(2) * &c__ * capital_f_.log() / denominator, second_recursive)
        },
    ));
}

fn push_rules_rule_2673(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, d__, m_, x_, e__);
    rules.push(rubi_rule!(
        order: 2673,
        source: "Int[(d_.+e_.*x_)^m_.*F_^(a_.+b_.*x_+c_.*x_^2),x_Symbol] :=
          Unintegrable[(d+e*x)^m*F^(a+b*x+c*x^2),x] /;
        FreeQ[{F,a,b,c,d,e,m},x]",
        desc: "Algebraic normalization",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [d__, e__, m_, capital_f_, a__, b__, c__, x_],
        optional: [d__, e__, m_, a__, b__, c__],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__, m_], x_)
        },
        rhs: {
            let integrand = (&d__ + &e__ * x_).pow(&m_)
                * capital_f_.pow(&a__ + &b__ * x_ + &c__ * x_.pow(2));

            rubi_unintegrable(integrand, x_)
        },
    ));
}

fn push_rules_rule_2674(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_f_, m_, u_, v_);
    rules.push(rubi_rule!(
        order: 2674,
        source: "Int[u_^m_.*F_^v_,x_Symbol] :=
          Int[ExpandToSum[u,x]^m*F^ExpandToSum[v,x],x] /;
        FreeQ[{F,m},x] && LinearQ[u,x] && QuadraticQ[v,x] && Not[LinearMatchQ[u,x] && QuadraticMatchQ[v,x]]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: u_.pow(m_) * capital_f_.pow(v_),
        with: [u_, m_, capital_f_, v_, x_],
        optional: [m_],
        when: {
            freeq!([capital_f_, m_], x_)
                && rubi_linear_q(&u_, x_)
                && rubi_quadratic_q(&v_, x_)
                && !(rubi_linear_match_q(&u_, x_) && rubi_quadratic_match_q(&v_, x_))
        },
        rhs: {
            let recursive_integrand =
                rubi_expand_to_sum(&u_, x_).pow(&m_) * capital_f_.pow(rubi_expand_to_sum(&v_, x_));
            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_2675(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_f_, a__, b__, c__, d__, m_, p_, v_, x_, e__);
    rules.push(rubi_rule!(
        order: 2675,
        source: "Int[x_^m_.*F_^(e_.*(c_.+d_.*x_))*(a_.+b_.*F_^v_)^p_,x_Symbol] :=
          With[{u=IntHide[F^(e*(c+d*x))*(a+b*F^v)^p,x]},
          x^m \\[Star] u - m \\[Star] Int[x^(m-1)*u,x]] /;
        FreeQ[{F,a,b,c,d,e},x] && EqQ[v,2*e*(c+d*x)] && GtQ[m,0] && ILtQ[p,0]",
        desc: "Integration by parts",
        refs: [],
        pattern: x_.pow(m_)
            * capital_f_.pow(e__ * (c__ + d__ * x_))
            * (a__ + b__ * capital_f_.pow(v_)).pow(p_),
        with: [m_, capital_f_, e__, c__, d__, a__, b__, v_, p_, x_],
        optional: [m_, e__, c__, d__, a__, b__],
        x_free: [capital_f_, a__, b__, c__, d__, e__],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__], x_)
                && eqq!(v_, Atom::num(2) * &e__ * (&c__ + &d__ * x_))
                && gtq!(m_, 0)
                && iltq!(p_, 0)
        },
        rhs: {
            let u = rubi_int_hide(
                &(capital_f_.pow(&e__ * (&c__ + &d__ * x_))
                    * (&a__ + &b__ * capital_f_.pow(&v_)).pow(&p_)),
                x_,
            )
            .unwrap();
            let recursive_integrand = x_.pow(&m_ - 1) * &u;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(x_.pow(&m_), u)
                    - rubi_star(m_, recursive)
        },
    ));
}

fn push_rules_rule_2676(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_f_, a__, b__, c__, d__, n_, p_, x_, e__);
    let exponential_power = capital_f_.pow(e__ * (c__ + d__ * x_)).pow(n_);
    rules.push(rubi_rule!(
        order: 2676,
        source: "Int[(F_^(e_.*(c_.+d_.*x_)))^n_.*(a_+b_.*(F_^(e_.*(c_.+d_.*x_)))^n_.)^p_.,x_Symbol] :=
          1/(d*e*n*Log[F]) \\[Star] Subst[Int[(a+b*x)^p,x],x,(F^(e*(c+d*x)))^n] /;
        FreeQ[{F,a,b,c,d,e,n,p},x]",
        desc: "Integration by substitution",
        refs: [],
        pattern: &exponential_power * (a__ + b__ * &exponential_power).pow(p_),
        with: [capital_f_, e__, c__, d__, n_, a__, b__, p_, x_],
        optional: [e__, c__, d__, n_, b__, p_],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__, n_, p_], x_)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let substitution_variable = Atom::var(substitution_symbol);
            let substitution_integrand = (&a__ + &b__ * &substitution_variable).pow(&p_);
            let substitution_primitive = rubi_rhs_int(&substitution_integrand, substitution_symbol);
            let substitution =
                capital_f_.pow(&e__ * (&c__ + &d__ * x_)).pow(&n_);
            let denominator = &d__ * &e__ * &n_ * capital_f_.log();

            rubi_star(Atom::num(1) / denominator, rubi_subst(&substitution_primitive, substitution_symbol, substitution))
        },
    ));
}

fn push_rules_rule_2677(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        capital_f_, capital_g_, a__, b__, c__, d__, m_, n_, p_, x_, e__, f__, g__, h__
    );
    rules.push(rubi_rule!(
        order: 2677,
        source: "Int[(G_^(h_.(f_.+g_.*x_)))^m_.*(a_+b_.*(F_^(e_.*(c_.+d_.*x_)))^n_.)^p_.,x_Symbol] :=
          (G^(h*(f+g*x)))^m/(F^(e*(c+d*x)))^n \\[Star] Int[(F^(e*(c+d*x)))^n*(a+b*(F^(e*(c+d*x)))^n)^p,x] /;
        FreeQ[{F,G,a,b,c,d,e,f,g,h,m,n,p},x] && EqQ[d*e*n*Log[F],g*h*m*Log[G]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern: capital_g_.pow(h__ * (f__ + g__ * x_)).pow(m_)
            * (a__ + b__ * capital_f_.pow(e__ * (c__ + d__ * x_)).pow(n_)).pow(p_),
        with: [capital_g_, h__, f__, g__, m_, a__, b__, capital_f_, e__, c__, d__, n_, p_, x_],
        optional: [h__, f__, g__, m_, b__, e__, c__, d__, n_, p_],
        when: {
            freeq!([capital_f_, capital_g_, a__, b__, c__, d__, e__, f__, g__, h__, m_, n_, p_], x_)
                && eqq!(
                    &d__ * &e__ * &n_ * capital_f_.log(),
                    &g__ * &h__ * &m_ * capital_g_.log()
                )
        },
        rhs: {
            let g_exponential = capital_g_.pow(&h__ * (&f__ + &g__ * x_));
            let f_exponential = capital_f_.pow(&e__ * (&c__ + &d__ * x_));
            let recursive_integrand = f_exponential.pow(&n_)
                * (&a__ + &b__ * f_exponential.pow(&n_)).pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(g_exponential.pow(&m_), recursive / f_exponential.pow(&n_))
        },
    ));
}

fn push_rules_rule_2678(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_f_, capital_g_, a__, b__, c__, d__, p_, x_, e__, f__, g__, h__
    );
    rules.push(rubi_rule!(
        order: 2678,
        source: "Int[G_^(h_.(f_.+g_.*x_))*(a_+b_.*F_^(e_.*(c_.+d_.*x_)))^p_.,x_Symbol] :=
          With[{m=FullSimplify[g*h*Log[G]/(d*e*Log[F])]},
          Denominator[m]*G^(f*h-c*g*h/d)/(d*e*Log[F]) \\[Star] Subst[Int[x^(Numerator[m]-1)*(a+b*x^Denominator[m])^p,x],x,F^(e*(c+d*x)/Denominator[m])] /;
         LeQ[m,-1] || GeQ[m,1]] /;
        FreeQ[{F,G,a,b,c,d,e,f,g,h,p},x]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_16(symbols),
        with: [capital_g_, h__, f__, g__, a__, b__, capital_f_, e__, c__, d__, p_, x_],
        optional: [h__, f__, g__, b__, e__, c__, d__, p_],
        when: {
            freeq!([capital_f_, capital_g_, a__, b__, c__, d__, e__, f__, g__, h__, p_], x_)
                && {
                    let m = rubi_full_simplify(
                        &(&g__ * &h__ * capital_g_.log()
                            / (&d__ * &e__ * capital_f_.log())),
                    );
                    leq!(m, -1) || geq!(m, 1)
                }
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let substitution_variable = Atom::var(substitution_symbol);
            let m = rubi_full_simplify(
                &(&g__ * &h__ * capital_g_.log() / (&d__ * &e__ * capital_f_.log())),
            );
            let denominator_m = rubi_denominator_atom(&m);
            let numerator_m = rubi_numerator(&m);
            let substitution_integrand = substitution_variable.pow(&numerator_m - 1)
                * (&a__ + &b__ * substitution_variable.pow(&denominator_m)).pow(&p_);
            let substitution_primitive = rubi_rhs_int(&substitution_integrand, substitution_symbol);
            let substitution =
                capital_f_.pow(&e__ * (&c__ + &d__ * x_) / &denominator_m);
            let substituted = rubi_subst(&substitution_primitive, substitution_symbol, substitution);

            rubi_star(&denominator_m * capital_g_.pow(&f__ * &h__ - &c__ * &g__ * (&h__ / &d__)) / (&d__ * &e__ * capital_f_.log()), substituted)
        },
    ));
}

fn push_rules_rule_2679(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_f_, capital_g_, a__, b__, c__, d__, p_, x_, e__, f__, g__, h__
    );
    rules.push(rubi_rule!(
        order: 2679,
        source: "Int[G_^(h_.(f_.+g_.*x_))*(a_+b_.*F_^(e_.*(c_.+d_.*x_)))^p_.,x_Symbol] :=
          With[{m=FullSimplify[d*e*Log[F]/(g*h*Log[G])]},
          Denominator[m]/(g*h*Log[G]) \\[Star] Subst[Int[x^(Denominator[m]-1)*(a+b*F^(c*e-d*e*f/g)*x^Numerator[m])^p,x],x,G^(h*(f+g*x)/Denominator[m])] /;
         LtQ[m,-1] || GtQ[m,1]] /;
        FreeQ[{F,G,a,b,c,d,e,f,g,h,p},x]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_16(symbols),
        with: [capital_g_, h__, f__, g__, a__, b__, capital_f_, e__, c__, d__, p_, x_],
        optional: [h__, f__, g__, b__, e__, c__, d__, p_],
        when: {
            freeq!([capital_f_, capital_g_, a__, b__, c__, d__, e__, f__, g__, h__, p_], x_)
                && {
                    let m = rubi_full_simplify(
                        &(&d__ * &e__ * capital_f_.log()
                            / (&g__ * &h__ * capital_g_.log())),
                    );
                    ltq!(m, -1) || gtq!(m, 1)
                }
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let substitution_variable = Atom::var(substitution_symbol);
            let m = rubi_full_simplify(
                &(&d__ * &e__ * capital_f_.log() / (&g__ * &h__ * capital_g_.log())),
            );
            let denominator_m = rubi_denominator_atom(&m);
            let numerator_m = rubi_numerator(&m);
            let substitution_integrand = substitution_variable.pow(&denominator_m - 1)
                * (&a__
                    + &b__
                        * capital_f_.pow(&c__ * &e__ - &d__ * &e__ * &f__ / &g__)
                        * substitution_variable.pow(&numerator_m))
                .pow(&p_);
            let substitution_primitive = rubi_rhs_int(&substitution_integrand, substitution_symbol);
            let substitution =
                capital_g_.pow(&h__ * (&f__ + &g__ * x_) / &denominator_m);
            let substituted = rubi_subst(&substitution_primitive, substitution_symbol, substitution);

            rubi_star(denominator_m, substituted / (&g__ * &h__ * capital_g_.log()))
        },
    ));
}

fn push_rules_rule_2680(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_f_, capital_g_, a__, b__, c__, d__, p_, x_, e__, f__, g__, h__
    );
    rules.push(rubi_rule!(
        order: 2680,
        source: "Int[G_^(h_.(f_.+g_.*x_))*(a_+b_.*F_^(e_.*(c_.+d_.*x_)))^p_.,x_Symbol] :=
          Int[Expand[G^(h*(f+g*x))*(a+b*F^(e*(c+d*x)))^p,x],x] /;
        FreeQ[{F,G,a,b,c,d,e,f,g,h},x] && IGtQ[p,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_16(symbols),
        with: [capital_g_, h__, f__, g__, a__, b__, capital_f_, e__, c__, d__, p_, x_],
        optional: [h__, f__, g__, b__, e__, c__, d__, p_],
        when: {
            freeq!([capital_f_, capital_g_, a__, b__, c__, d__, e__, f__, g__, h__], x_)
                && igtq!(p_, 0)
        },
        rhs: {
            let integrand = capital_g_.pow(&h__ * (&f__ + &g__ * x_))
                * (&a__ + &b__ * capital_f_.pow(&e__ * (&c__ + &d__ * x_))).pow(&p_);
            let expanded = rubi_expand(&integrand, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_2681(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_f_, capital_g_, a__, b__, c__, d__, p_, x_, e__, f__, g__, h__
    );
    rules.push(rubi_rule!(
        order: 2681,
        source: "Int[G_^(h_.(f_.+g_.*x_))*(a_+b_.*F_^(e_.*(c_.+d_.*x_)))^p_,x_Symbol] :=
          a^p*G^(h*(f+g*x))/(g*h*Log[G])*Hypergeometric2F1[-p,g*h*Log[G]/(d*e*Log[F]),g*h*Log[G]/(d*e*Log[F])+1,Simplify[-b/a*F^(e*(c+d*x))]] /;
        FreeQ[{F,G,a,b,c,d,e,f,g,h,p},x] && (ILtQ[p,0] || GtQ[a,0])",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_16(symbols),
        with: [capital_g_, h__, f__, g__, a__, b__, capital_f_, e__, c__, d__, p_, x_],
        optional: [h__, f__, g__, b__, e__, c__, d__],
        when: {
            freeq!([capital_f_, capital_g_, a__, b__, c__, d__, e__, f__, g__, h__, p_], x_)
                && (iltq!(p_, 0) || gtq!(a__, 0))
        },
        rhs: {
            let exponential = capital_f_.pow(&e__ * (&c__ + &d__ * x_));
            let ratio = &g__ * &h__ * capital_g_.log() / (&d__ * &e__ * capital_f_.log());
            let shifted_ratio = &ratio + 1;
            let hypergeometric_argument = rubi_simplify(&(-&b__ / &a__ * exponential));

            rubi_simp(&(
                a__.pow(&p_) * capital_g_.pow(&h__ * (&f__ + &g__ * x_))
                    * rubi_hypergeometric2f1(-&p_, ratio, shifted_ratio, hypergeometric_argument)
                    / (&g__ * &h__ * capital_g_.log())
            ), x_)
        },
    ));
}

fn push_rules_rule_2682(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_f_, capital_g_, a__, b__, c__, d__, p_, x_, e__, f__, g__, h__
    );
    rules.push(rubi_rule!(
        order: 2682,
        source: "Int[G_^(h_.(f_.+g_.*x_))*(a_+b_.*F_^(e_.*(c_.+d_.*x_)))^p_,x_Symbol] :=
          (a+b*F^(e*(c+d*x)))^p/(1+(b/a)*F^(e*(c+d*x)))^p \\[Star] Int[G^(h*(f+g*x))*(1+b/a*F^(e*(c+d*x)))^p,x] /;
        FreeQ[{F,G,a,b,c,d,e,f,g,h,p},x] && Not[ILtQ[p,0] || GtQ[a,0]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_16(symbols),
        with: [capital_g_, h__, f__, g__, a__, b__, capital_f_, e__, c__, d__, p_, x_],
        optional: [h__, f__, g__, b__, e__, c__, d__],
        when: {
            freeq!([capital_f_, capital_g_, a__, b__, c__, d__, e__, f__, g__, h__, p_], x_)
                && !(iltq!(p_, 0) || gtq!(a__, 0))
        },
        rhs: {
            let f_exponential = capital_f_.pow(&e__ * (&c__ + &d__ * x_));
            let normalized_binomial = Atom::num(1) + &b__ / &a__ * &f_exponential;
            let recursive_integrand = capital_g_.pow(&h__ * (&f__ + &g__ * x_))
                * normalized_binomial.pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star((&a__ + &b__ * f_exponential).pow(&p_), recursive
                    / normalized_binomial.pow(&p_))
        },
    ));
}

fn push_rules_rule_2683(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_f_, capital_g_, a__, b__, p_, u_, v_, e__, h__);
    rules.push(rubi_rule!(
        order: 2683,
        source: "Int[G_^(h_. u_)*(a_+b_.*F_^(e_.*v_))^p_,x_Symbol] :=
          Int[G^(h*ExpandToSum[u,x])*(a+b*F^(e*ExpandToSum[v,x]))^p,x] /;
        FreeQ[{F,G,a,b,e,h,p},x] && LinearQ[{u,v},x] && Not[LinearMatchQ[{u,v},x]]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern: capital_g_.pow(h__ * u_) * (a__ + b__ * capital_f_.pow(e__ * v_)).pow(p_),
        with: [capital_g_, h__, u_, a__, b__, capital_f_, e__, v_, p_, x_],
        optional: [h__, b__, e__],
        when: {
            freeq!([capital_f_, capital_g_, a__, b__, e__, h__, p_], x_)
                && rubi_linear_q_list(&[&u_, &v_], x_)
                && !rubi_linear_match_q_list(&[&u_, &v_], x_)
        },
        rhs: {
            let expanded_u = rubi_expand_to_sum(&u_, x_);
            let expanded_v = rubi_expand_to_sum(&v_, x_);
            let recursive_integrand = capital_g_.pow(&h__ * expanded_u)
                * (&a__ + &b__ * capital_f_.pow(&e__ * expanded_v)).pow(&p_);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_2684(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        capital_f_, a__, b__, c__, d__, m_, p_, q_, u_, v_, x_, e__, f__
    );
    rules.push(rubi_rule!(
        order: 2684,
        source: "Int[(e_.+f_.*x_)^m_.*(a_.+b_.*F_^u_)^p_.*(c_.+d_.*F_^v_)^q_.,x_Symbol] :=
          With[{w=ExpandIntegrand[(e+f*x)^m,(a+b*F^u)^p*(c+d*F^v)^q,x]},
          Int[w,x] /;
         SumQ[w]] /;
        FreeQ[{F,a,b,c,d,e,f,m},x] && IntegersQ[p,q] && LinearQ[{u,v},x] && RationalQ[Simplify[u/v]]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (e__ + f__ * x_).pow(m_)
            * (a__ + b__ * capital_f_.pow(u_)).pow(p_)
            * (c__ + d__ * capital_f_.pow(v_)).pow(q_),
        with: [e__, f__, m_, a__, b__, capital_f_, u_, p_, c__, d__, v_, q_, x_],
        optional: [e__, f__, m_, a__, b__, p_, c__, d__, q_],
        x_dep: [u_, v_],
        x_free: [capital_f_, a__, b__, c__, d__, e__, f__, m_],
        x_linear: [u_, v_],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__, f__, m_], x_)
                && integersq!([p_, q_])
                && rubi_linear_q_list(&[&u_, &v_], x_)
                && rationalq!(rubi_simplify(&(&u_ / &v_)))
                && {
                    let multiplier = (&e__ + &f__ * x_).pow(&m_);
                    let product = (&a__ + &b__ * capital_f_.pow(&u_)).pow(&p_)
                        * (&c__ + &d__ * capital_f_.pow(&v_)).pow(&q_);
                    rubi_expand_integrand_product_sum(&multiplier, &product, x_).is_some()
                }
        },
        rhs: {
            let multiplier = (&e__ + &f__ * x_).pow(&m_);
            let product = (&a__ + &b__ * capital_f_.pow(&u_)).pow(&p_)
                * (&c__ + &d__ * capital_f_.pow(&v_)).pow(&q_);
            let expanded = rubi_expand_integrand_product_sum(&multiplier, &product, x_)
                .expect("when clause should ensure expanded integrand is a sum");

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_2685(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_f_, capital_g_, capital_h_, a__, b__, c__, d__, p_, r__, x_, e__, f__, g__, h__,
        s__, t__
    );
    rules.push(rubi_rule!(
        order: 2685,
        source: "Int[G_^(h_.(f_.+g_.*x_))*H_^(t_.(r_.+s_.*x_))*(a_+b_.*F_^(e_.*(c_.+d_.*x_)))^p_.,x_Symbol] :=
          With[{m=FullSimplify[(g*h*Log[G]+s*t*Log[H])/(d*e*Log[F])]},
          Denominator[m]*G^(f*h-c*g*h/d)*H^(r*t-c*s*t/d)/(d*e*Log[F]) \\[Star]
            Subst[Int[x^(Numerator[m]-1)*(a+b*x^Denominator[m])^p,x],x,F^(e*(c+d*x)/Denominator[m])] /;
         RationalQ[m]] /;
        FreeQ[{F,G,H,a,b,c,d,e,f,g,h,r,s,t,p},x]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_17(symbols),
        with: [capital_g_, h__, f__, g__, capital_h_, t__, r__, s__, a__, b__, capital_f_, e__, c__, d__, p_, x_],
        optional: [h__, f__, g__, t__, r__, s__, b__, e__, c__, d__, p_],
        when: {
            freeq!([capital_f_, capital_g_, capital_h_, a__, b__, c__, d__, e__, f__, g__, h__, r__, s__, t__], x_)
                && freeq!(p_, x_)
                && {
                    let m = rubi_full_simplify(
                        &((&g__ * &h__ * capital_g_.log()
                            + &s__ * &t__ * capital_h_.log())
                            / (&d__ * &e__ * capital_f_.log())),
                    );
                    rationalq!(m)
                }
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let substitution_variable = Atom::var(substitution_symbol);
            let m = rubi_full_simplify(
                &((&g__ * &h__ * capital_g_.log() + &s__ * &t__ * capital_h_.log())
                    / (&d__ * &e__ * capital_f_.log())),
            );
            let denominator_m = rubi_denominator_atom(&m);
            let numerator_m = rubi_numerator(&m);
            let substitution_integrand = substitution_variable.pow(&numerator_m - 1)
                * (&a__ + &b__ * substitution_variable.pow(&denominator_m)).pow(&p_);
            let substitution_primitive = rubi_rhs_int(&substitution_integrand, substitution_symbol);
            let substitution =
                capital_f_.pow(&e__ * (&c__ + &d__ * x_) / &denominator_m);
            let substituted = rubi_subst(&substitution_primitive, substitution_symbol, substitution);

            rubi_star(&denominator_m * capital_g_.pow(&f__ * &h__ - &c__ * &g__ * &h__ / &d__) * capital_h_.pow(&r__ * &t__ - &c__ * &s__ * &t__ / &d__) / (&d__ * &e__ * capital_f_.log()), substituted)
        },
    ));
}

fn push_rules_rule_2686(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_f_, capital_g_, capital_h_, a__, b__, c__, d__, p_, r__, x_, e__, f__, g__, h__,
        s__, t__
    );
    rules.push(rubi_rule!(
        order: 2686,
        source: "Int[G_^(h_.(f_.+g_.*x_))*H_^(t_.(r_.+s_.*x_))*(a_+b_.*F_^(e_.*(c_.+d_.*x_)))^p_.,x_Symbol] :=
          G^((f-c*g/d)*h) \\[Star] Int[H^(t*(r+s*x))*(b+a*F^(-e*(c+d*x)))^p,x] /;
        FreeQ[{F,G,H,a,b,c,d,e,f,g,h,r,s,t},x] && EqQ[d*e*p*Log[F]+g*h*Log[G],0] && IntegerQ[p]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_17(symbols),
        with: [capital_g_, h__, f__, g__, capital_h_, t__, r__, s__, a__, b__, capital_f_, e__, c__, d__, p_, x_],
        optional: [h__, f__, g__, t__, r__, s__, b__, e__, c__, d__, p_],
        when: {
            freeq!([capital_f_, capital_g_, capital_h_, a__, b__, c__, d__, e__, f__, g__, h__, r__, s__, t__], x_)
                && eqq!(&d__ * &e__ * &p_ * capital_f_.log() + &g__ * &h__ * capital_g_.log(), 0)
                && integerq!(p_)
        },
        rhs: {
            let recursive_integrand = capital_h_.pow(&t__ * (&r__ + &s__ * x_))
                * (&b__ + &a__ * capital_f_.pow(-&e__ * (&c__ + &d__ * x_))).pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(capital_g_.pow((&f__ - &c__ * &g__ / &d__) * &h__), recursive)
        },
    ));
}

fn push_rules_rule_2687(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_f_, capital_g_, capital_h_, a__, b__, c__, d__, p_, r__, x_, e__, f__, g__, h__,
        s__, t__
    );
    rules.push(rubi_rule!(
        order: 2687,
        source: "Int[G_^(h_.(f_.+g_.*x_))*H_^(t_.(r_.+s_.*x_))*(a_+b_.*F_^(e_.*(c_.+d_.*x_)))^p_.,x_Symbol] :=
          Int[Expand[G^(h*(f+g*x))*H^(t*(r+s*x))*(a+b*F^(e*(c+d*x)))^p,x],x] /;
        FreeQ[{F,G,H,a,b,c,d,e,f,g,h,r,s,t},x] && IGtQ[p,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_17(symbols),
        with: [capital_g_, h__, f__, g__, capital_h_, t__, r__, s__, a__, b__, capital_f_, e__, c__, d__, p_, x_],
        optional: [h__, f__, g__, t__, r__, s__, b__, e__, c__, d__, p_],
        when: {
            freeq!([capital_f_, capital_g_, capital_h_, a__, b__, c__, d__, e__, f__, g__, h__, r__, s__, t__], x_)
                && igtq!(p_, 0)
        },
        rhs: {
            let integrand = capital_g_.pow(&h__ * (&f__ + &g__ * x_))
                * capital_h_.pow(&t__ * (&r__ + &s__ * x_))
                * (&a__ + &b__ * capital_f_.pow(&e__ * (&c__ + &d__ * x_))).pow(&p_);
            let expanded = rubi_expand(&integrand, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_2688(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_f_, capital_g_, capital_h_, a__, b__, c__, d__, p_, r__, x_, e__, f__, g__, h__,
        s__, t__
    );
    rules.push(rubi_rule!(
        order: 2688,
        source: "Int[G_^(h_.(f_.+g_.*x_))*H_^(t_.(r_.+s_.*x_))*(a_+b_.*F_^(e_.*(c_.+d_.*x_)))^p_,x_Symbol] :=
          a^p*G^(h*(f+g*x))*H^(t*(r+s*x))/(g*h*Log[G]+s*t*Log[H])*
            Hypergeometric2F1[-p,(g*h*Log[G]+s*t*Log[H])/(d*e*Log[F]),(g*h*Log[G]+s*t*Log[H])/(d*e*Log[F])+1,Simplify[-b/a*F^(e*(c+d*x))]] /;
        FreeQ[{F,G,H,a,b,c,d,e,f,g,h,r,s,t},x] && ILtQ[p,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_17(symbols),
        with: [capital_g_, h__, f__, g__, capital_h_, t__, r__, s__, a__, b__, capital_f_, e__, c__, d__, p_, x_],
        optional: [h__, f__, g__, t__, r__, s__, b__, e__, c__, d__],
        when: {
            freeq!([capital_f_, capital_g_, capital_h_, a__, b__, c__, d__, e__, f__, g__, h__, r__, s__, t__], x_)
                && iltq!(p_, 0)
        },
        rhs: {
            let denominator = &g__ * &h__ * capital_g_.log() + &s__ * &t__ * capital_h_.log();
            let exponential = capital_f_.pow(&e__ * (&c__ + &d__ * x_));
            let ratio = &denominator / (&d__ * &e__ * capital_f_.log());
            let shifted_ratio = &ratio + 1;
            let hypergeometric_argument = rubi_simplify(&(-&b__ / &a__ * exponential));

            rubi_simp(&(
                a__.pow(&p_)
                    * capital_g_.pow(&h__ * (&f__ + &g__ * x_))
                    * capital_h_.pow(&t__ * (&r__ + &s__ * x_))
                    * rubi_hypergeometric2f1(-&p_, ratio, shifted_ratio, hypergeometric_argument)
                    / denominator
            ), x_)
        },
    ));
}

fn push_rules_rule_2689(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_f_, capital_g_, capital_h_, a__, b__, c__, d__, p_, r__, x_, e__, f__, g__, h__,
        s__, t__
    );
    rules.push(rubi_rule!(
        order: 2689,
        source: "Int[G_^(h_.(f_.+g_.*x_))*H_^(t_.(r_.+s_.*x_))*(a_+b_.*F_^(e_.*(c_.+d_.*x_)))^p_,x_Symbol] :=
          G^(h*(f+g*x))*H^(t*(r+s*x))*(a+b*F^(e*(c+d*x)))^p/((g*h*Log[G]+s*t*Log[H])*((a+b*F^(e*(c+d*x)))/a)^p)*
            Hypergeometric2F1[-p,(g*h*Log[G]+s*t*Log[H])/(d*e*Log[F]),(g*h*Log[G]+s*t*Log[H])/(d*e*Log[F])+1,Simplify[-b/a*F^(e*(c+d*x))]] /;
        FreeQ[{F,G,H,a,b,c,d,e,f,g,h,r,s,t,p},x] && Not[IntegerQ[p]]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_17(symbols),
        with: [capital_g_, h__, f__, g__, capital_h_, t__, r__, s__, a__, b__, capital_f_, e__, c__, d__, p_, x_],
        optional: [h__, f__, g__, t__, r__, s__, b__, e__, c__, d__],
        when: {
            freeq!([capital_f_, capital_g_, capital_h_, a__, b__, c__, d__, e__, f__, g__, h__, r__, s__, t__], x_)
                && freeq!(p_, x_)
                && !integerq!(p_)
        },
        rhs: {
            let denominator = &g__ * &h__ * capital_g_.log() + &s__ * &t__ * capital_h_.log();
            let exponential = capital_f_.pow(&e__ * (&c__ + &d__ * x_));
            let binomial = &a__ + &b__ * &exponential;
            let ratio = &denominator / (&d__ * &e__ * capital_f_.log());
            let shifted_ratio = &ratio + 1;
            let hypergeometric_argument = rubi_simplify(&(-&b__ / &a__ * exponential));

            rubi_simp(&(
                capital_g_.pow(&h__ * (&f__ + &g__ * x_))
                    * capital_h_.pow(&t__ * (&r__ + &s__ * x_))
                    * binomial.pow(&p_)
                    * rubi_hypergeometric2f1(-&p_, ratio, shifted_ratio, hypergeometric_argument)
                    / (denominator * (binomial / &a__).pow(&p_))
            ), x_)
        },
    ));
}

fn push_rules_rule_2690(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        capital_f_, capital_g_, capital_h_, a__, b__, p_, u_, v_, w_, e__, h__, t__
    );
    rules.push(rubi_rule!(
        order: 2690,
        source: "Int[G_^(h_. u_)*H_^(t_. w_)*(a_+b_.*F_^(e_.*v_))^p_,x_Symbol] :=
          Int[G^(h*ExpandToSum[u,x])*H^(t*ExpandToSum[w,x])*(a+b*F^(e*ExpandToSum[v,x]))^p,x] /;
        FreeQ[{F,G,H,a,b,e,h,t,p},x] && LinearQ[{u,v,w},x] && Not[LinearMatchQ[{u,v,w},x]]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern: capital_g_.pow(h__ * u_)
            * capital_h_.pow(t__ * w_)
            * (a__ + b__ * capital_f_.pow(e__ * v_)).pow(p_),
        with: [capital_g_, h__, u_, capital_h_, t__, w_, a__, b__, capital_f_, e__, v_, p_, x_],
        optional: [h__, t__, b__, e__],
        when: {
            freeq!([capital_f_, capital_g_, capital_h_, a__, b__, e__, h__, t__, p_], x_)
                && rubi_linear_q_list(&[&u_, &v_, &w_], x_)
                && !rubi_linear_match_q_list(&[&u_, &v_, &w_], x_)
        },
        rhs: {
            let expanded_u = rubi_expand_to_sum(&u_, x_);
            let expanded_v = rubi_expand_to_sum(&v_, x_);
            let expanded_w = rubi_expand_to_sum(&w_, x_);
            let recursive_integrand = capital_g_.pow(&h__ * expanded_u)
                * capital_h_.pow(&t__ * expanded_w)
                * (&a__ + &b__ * capital_f_.pow(&e__ * expanded_v)).pow(&p_);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_2691(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_f_, a__, b__, c__, d__, n_, p_, x_, e__);
    rules.push(rubi_rule!(
        order: 2691,
        source: "Int[F_^(e_.*(c_.+d_.*x_))*(a_.*x_^n_.+b_.*F_^(e_.*(c_.+d_.*x_)))^p_.,x_Symbol] :=
          (a*x^n+b*F^(e*(c+d*x)))^(p+1)/(b*d*e*(p+1)*Log[F]) -
          a*n/(b*d*e*Log[F]) \\[Star] Int[x^(n-1)*(a*x^n+b*F^(e*(c+d*x)))^p,x] /;
        FreeQ[{F,a,b,c,d,e,n,p},x] && NeQ[p,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern: capital_f_.pow(e__ * (c__ + d__ * x_))
            * (a__ * x_.pow(n_) + b__ * capital_f_.pow(e__ * (c__ + d__ * x_))).pow(p_),
        with: [capital_f_, e__, c__, d__, a__, n_, b__, p_, x_],
        optional: [e__, c__, d__, a__, n_, b__, p_],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__, n_, p_], x_)
                && neq!(p_, -1)
        },
        rhs: {
            let exponential = capital_f_.pow(&e__ * (&c__ + &d__ * x_));
            let binomial = &a__ * x_.pow(&n_) + &b__ * &exponential;
            let recursive_integrand = x_.pow(&n_ - 1) * binomial.pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let denominator = &b__ * &d__ * &e__ * rubi_log(&capital_f_);

            let first = rubi_simp(
                &(binomial.pow(&p_ + 1) / (&denominator * (&p_ + 1))),
                x_,
            );
            let second = rubi_simp(
                &rubi_star(-&a__ * &n_ / &denominator, recursive),
                x_,
            );
            rubi_simp(&(first), x_) + second
        },
    ));
}

fn push_rules_rule_2692(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_f_, a__, b__, c__, d__, m_, n_, p_, x_, e__);
    rules.push(rubi_rule!(
        order: 2692,
        source: "Int[x_^m_.*F_^(e_.*(c_.+d_.*x_))*(a_.*x_^n_.+b_.*F_^(e_.*(c_.+d_.*x_)))^p_.,x_Symbol] :=
          x^m*(a*x^n+b*F^(e*(c+d*x)))^(p+1)/(b*d*e*(p+1)*Log[F]) -
          a*n/(b*d*e*Log[F]) \\[Star] Int[x^(m+n-1)*(a*x^n+b*F^(e*(c+d*x)))^p,x] -
          m/(b*d*e*(p+1)*Log[F]) \\[Star] Int[x^(m-1)*(a*x^n+b*F^(e*(c+d*x)))^(p+1),x] /;
        FreeQ[{F,a,b,c,d,e,m,n,p},x] && NeQ[p,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern: x_.pow(m_)
            * capital_f_.pow(e__ * (c__ + d__ * x_))
            * (a__ * x_.pow(n_) + b__ * capital_f_.pow(e__ * (c__ + d__ * x_))).pow(p_),
        with: [m_, capital_f_, e__, c__, d__, a__, n_, b__, p_, x_],
        optional: [m_, e__, c__, d__, a__, n_, b__, p_],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__, m_, n_, p_], x_)
                && neq!(p_, -1)
        },
        rhs: {
            let exponential = capital_f_.pow(&e__ * (&c__ + &d__ * x_));
            let binomial = &a__ * x_.pow(&n_) + &b__ * &exponential;
            let denominator = &b__ * &d__ * &e__ * rubi_log(&capital_f_);
            let first_recursive_integrand = x_.pow(&m_ + &n_ - 1) * binomial.pow(&p_);
            let first_recursive =
                rubi_rhs_int(&first_recursive_integrand, x_);
            let second_recursive_integrand = x_.pow(&m_ - 1) * binomial.pow(&p_ + 1);
            let second_recursive =
                rubi_rhs_int(&second_recursive_integrand, x_);

            let first = rubi_simp(
                &(x_.pow(&m_) * binomial.pow(&p_ + 1)
                    / (&denominator * (&p_ + 1))),
                x_,
            );
            let second = rubi_simp(
                &rubi_star(
                    -&m_ / (&denominator * (&p_ + 1)),
                    second_recursive,
                ),
                x_,
            );
            let third = rubi_simp(
                &rubi_star(-&a__ * &n_ / &denominator, first_recursive),
                x_,
            );
            rubi_simp(&(first), x_) + second + third
        },
    ));
}

fn push_rules_rule_2693(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_f_, a__, b__, c__, m_, u_, v_, x_, f__, g__);
    rules.push(rubi_rule!(
        order: 2693,
        source: "Int[(f_.+g_.*x_)^m_./(a_.+b_.*F_^u_+c_.*F_^v_),x_Symbol] :=
          With[{q=Rt[b^2-4*a*c,2]},
          2*c/q \\[Star] Int[(f+g*x)^m/(b-q+2*c*F^u),x] - 2*c/q \\[Star] Int[(f+g*x)^m/(b+q+2*c*F^u),x]] /;
        FreeQ[{F,a,b,c,f,g},x] && EqQ[v,2*u] && LinearQ[u,x] && NeQ[b^2-4*a*c,0] && IGtQ[m,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (f__ + g__ * x_).pow(m_) / (a__ + b__ * capital_f_.pow(u_) + c__ * capital_f_.pow(v_)),
        with: [f__, g__, m_, a__, b__, capital_f_, u_, c__, v_, x_],
        optional: [f__, g__, m_, a__, b__, c__],
        when: {
            freeq!([capital_f_, a__, b__, c__, f__, g__], x_)
                && eqq!(v_, Atom::num(2) * &u_)
                && rubi_linear_q(&u_, x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && igtq!(m_, 0)
        },
        rhs: {
            let q = rubi_rt(&(b__.pow(2) - Atom::num(4) * &a__ * &c__), 2);
            let multiplier = (&f__ + &g__ * x_).pow(&m_);
            let first_denominator = &b__ - &q + Atom::num(2) * &c__ * capital_f_.pow(&u_);
            let second_denominator = &b__ + &q + Atom::num(2) * &c__ * capital_f_.pow(&u_);
            let first = rubi_rhs_int(&(&multiplier / first_denominator), x_);
            let second = rubi_rhs_int(&(multiplier / second_denominator), x_);
            let coefficient = Atom::num(2) * &c__ / &q;

            rubi_star(&coefficient, first)
                    - rubi_star(coefficient, second)
        },
    ));
}

fn push_rules_rule_2694(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_f_, a__, b__, c__, m_, u_, v_, x_, f__, g__);
    rules.push(rubi_rule!(
        order: 2694,
        source: "Int[(f_.+g_.*x_)^m_.*F_^u_/(a_.+b_.*F_^u_+c_.*F_^v_),x_Symbol] :=
          With[{q=Rt[b^2-4*a*c,2]},
          2*c/q \\[Star] Int[(f+g*x)^m*F^u/(b-q+2*c*F^u),x] - 2*c/q \\[Star] Int[(f+g*x)^m*F^u/(b+q+2*c*F^u),x]] /;
        FreeQ[{F,a,b,c,f,g},x] && EqQ[v,2*u] && LinearQ[u,x] && NeQ[b^2-4*a*c,0] && IGtQ[m,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (f__ + g__ * x_).pow(m_) * capital_f_.pow(u_)
            / (a__ + b__ * capital_f_.pow(u_) + c__ * capital_f_.pow(v_)),
        with: [f__, g__, m_, capital_f_, u_, a__, b__, c__, v_, x_],
        optional: [f__, g__, m_, a__, b__, c__],
        when: {
            freeq!([capital_f_, a__, b__, c__, f__, g__], x_)
                && eqq!(v_, Atom::num(2) * &u_)
                && rubi_linear_q(&u_, x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && igtq!(m_, 0)
        },
        rhs: {
            let q = rubi_rt(&(b__.pow(2) - Atom::num(4) * &a__ * &c__), 2);
            let multiplier = (&f__ + &g__ * x_).pow(&m_) * capital_f_.pow(&u_);
            let first_denominator = &b__ - &q + Atom::num(2) * &c__ * capital_f_.pow(&u_);
            let second_denominator = &b__ + &q + Atom::num(2) * &c__ * capital_f_.pow(&u_);
            let first = rubi_rhs_int(&(&multiplier / first_denominator), x_);
            let second = rubi_rhs_int(&(multiplier / second_denominator), x_);

            rubi_star(Atom::num(2) * &c__ / &q, first)
                    - rubi_star(Atom::num(2) * &c__ / q, second)
        },
    ));
}

fn push_rules_rule_2695(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        capital_f_, a__, b__, c__, m_, u_, v_, x_, f__, g__, h__, i__
    );
    rules.push(rubi_rule!(
        order: 2695,
        source: "Int[(f_.+g_.*x_)^m_.*(h_+i_.*F_^u_)/(a_.+b_.*F_^u_+c_.*F_^v_),x_Symbol] :=
          With[{q=Rt[b^2-4*a*c,2]},
          (Simplify[(2*c*h-b*i)/q]+i) \\[Star] Int[(f+g*x)^m/(b-q+2*c*F^u),x] -
          (Simplify[(2*c*h-b*i)/q]-i) \\[Star] Int[(f+g*x)^m/(b+q+2*c*F^u),x]] /;
        FreeQ[{F,a,b,c,f,g,h,i},x] && EqQ[v,2*u] && LinearQ[u,x] && NeQ[b^2-4*a*c,0] && IGtQ[m,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (f__ + g__ * x_).pow(m_) * (h__ + i__ * capital_f_.pow(u_))
            / (a__ + b__ * capital_f_.pow(u_) + c__ * capital_f_.pow(v_)),
        with: [f__, g__, m_, h__, i__, capital_f_, u_, a__, b__, c__, v_, x_],
        optional: [f__, g__, m_, i__, a__, b__, c__],
        when: {
            freeq!([capital_f_, a__, b__, c__, f__, g__, h__, i__], x_)
                && eqq!(v_, Atom::num(2) * &u_)
                && rubi_linear_q(&u_, x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && igtq!(m_, 0)
        },
        rhs: {
            let q = rubi_rt(&(b__.pow(2) - Atom::num(4) * &a__ * &c__), 2);
            let multiplier = (&f__ + &g__ * x_).pow(&m_);
            let coefficient = rubi_simplify(&((Atom::num(2) * &c__ * &h__ - &b__ * &i__) / &q));
            let first_denominator = &b__ - &q + Atom::num(2) * &c__ * capital_f_.pow(&u_);
            let second_denominator = &b__ + &q + Atom::num(2) * &c__ * capital_f_.pow(&u_);
            let first = rubi_rhs_int(&(&multiplier / first_denominator), x_);
            let second = rubi_rhs_int(&(multiplier / second_denominator), x_);

            rubi_star(&coefficient + &i__, first)
                    - rubi_star(coefficient - &i__, second)
        },
    ));
}

fn push_rules_rule_2696(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_f_, a__, b__, c__, d__, m_, v_, x_);
    rules.push(rubi_rule!(
        order: 2696,
        source: "Int[x_^m_./(a_.*F_^(c_.+d_.*x_)+b_.*F_^v_),x_Symbol] :=
          With[{u=IntHide[1/(a*F^(c+d*x)+b*F^v),x]},
          x^m*u - m \\[Star] Int[x^(m-1)*u,x]] /;
        FreeQ[{F,a,b,c,d},x] && EqQ[v,-(c+d*x)] && GtQ[m,0]",
        desc: "Integration by parts",
        refs: [],
        pattern: x_.pow(m_) / (a__ * capital_f_.pow(c__ + d__ * x_) + b__ * capital_f_.pow(v_)),
        with: [m_, a__, capital_f_, c__, d__, b__, v_, x_],
        optional: [m_, a__, c__, d__, b__],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__], x_)
                && eqq!(v_, -(&c__ + &d__ * x_))
                && gtq!(m_, 0)
        },
        rhs: {
            let u = rubi_int_hide(
                &(Atom::num(1)
                    / (&a__ * capital_f_.pow(&c__ + &d__ * x_) + &b__ * capital_f_.pow(&v_))),
                x_,
            )
            .unwrap();
            let recursive_integrand = x_.pow(&m_ - 1) * &u;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(x_.pow(&m_) * &u), x_)
                    - rubi_star(m_, recursive)
        },
    ));
}

fn push_rules_rule_2697(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_f_, a__, b__, c__, u__, v_, w_);
    rules.push(rubi_rule!(
        order: 2697,
        source: "Int[u_/(a_+b_.*F_^v_+c_.*F_^w_),x_Symbol] :=
          Int[u*F^v/(c+a*F^v+b*F^(2*v)),x] /;
        FreeQ[{F,a,b,c},x] && EqQ[w,-v] && LinearQ[v,x] && If[RationalQ[D[v,x]], GtQ[D[v,x],0], LtQ[LeafCount[v],LeafCount[w]]]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: u__ / (a__ + b__ * capital_f_.pow(v_) + c__ * capital_f_.pow(w_)),
        with: [u__, a__, b__, capital_f_, v_, c__, w_, x_],
        optional: [b__, c__],
        when: {
            freeq!([capital_f_, a__, b__, c__], x_)
                && eqq!(w_, -&v_)
                && rubi_linear_q(&v_, x_)
                && {
                    let derivative = v_.derivative(x_);
                    if rationalq!(derivative) {
                        gtq!(derivative, 0)
                    } else {
                        rubi_leaf_count(&v_) < rubi_leaf_count(&w_)
                    }
                }
        },
        rhs: {
            let recursive_integrand =
                &u__ * capital_f_.pow(&v_) / (&c__ + &a__ * capital_f_.pow(&v_) + &b__ * capital_f_.pow(Atom::num(2) * &v_));

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_2698(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_f_, a__, b__, c__, d__, n_, x_, e__, g__);
    rules.push(rubi_rule!(
        order: 2698,
        source: "Int[F_^(g_.*(d_.+e_.*x_)^n_.)/(a_.+b_.*x_+c_.*x_^2),x_Symbol] :=
          Int[ExpandIntegrand[F^(g*(d+e*x)^n),1/(a+b*x+c*x^2),x],x] /;
        FreeQ[{F,a,b,c,d,e,g,n},x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: capital_f_.pow(g__ * (d__ + e__ * x_).pow(n_))
            / (a__ + b__ * x_ + c__ * x_.pow(2)),
        with: [capital_f_, g__, d__, e__, n_, a__, b__, c__, x_],
        optional: [g__, d__, e__, n_, a__, b__, c__],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__, g__, n_], x_)
        },
        rhs: {
            let exponential = capital_f_.pow(&g__ * (&d__ + &e__ * x_).pow(&n_));
            let rational = Atom::num(1) / (&a__ + &b__ * x_ + &c__ * x_.pow(2));
            let expanded = rubi_expand_integrand_product(&exponential, &rational, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_2699(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_f_, a__, c__, d__, n_, x_, e__, g__);
    rules.push(rubi_rule!(
        order: 2699,
        source: "Int[F_^(g_.*(d_.+e_.*x_)^n_.)/(a_+c_.*x_^2),x_Symbol] :=
          Int[ExpandIntegrand[F^(g*(d+e*x)^n),1/(a+c*x^2),x],x] /;
        FreeQ[{F,a,c,d,e,g,n},x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: capital_f_.pow(g__ * (d__ + e__ * x_).pow(n_)) / (a__ + c__ * x_.pow(2)),
        with: [capital_f_, g__, d__, e__, n_, a__, c__, x_],
        optional: [g__, d__, e__, n_, c__],
        when: {
            freeq!([capital_f_, a__, c__, d__, e__, g__, n_], x_)
        },
        rhs: {
            let exponential = capital_f_.pow(&g__ * (&d__ + &e__ * x_).pow(&n_));
            let rational = Atom::num(1) / (&a__ + &c__ * x_.pow(2));
            let expanded = rubi_expand_integrand_product(&exponential, &rational, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_2700(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_f_, a__, b__, c__, d__, m_, n_, u__, x_, e__, g__);
    rules.push(rubi_rule!(
        order: 2700,
        source: "Int[u_^m_.*F_^(g_.*(d_.+e_.*x_)^n_.)/(a_.+b_.*x_+c_*x_^2),x_Symbol] :=
          Int[ExpandIntegrand[F^(g*(d+e*x)^n),u^m/(a+b*x+c*x^2),x],x] /;
        FreeQ[{F,a,b,c,d,e,g,n},x] && PolynomialQ[u,x] && IntegerQ[m]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: u__.pow(m_) * capital_f_.pow(g__ * (d__ + e__ * x_).pow(n_))
            / (a__ + b__ * x_ + c__ * x_.pow(2)),
        with: [u__, m_, capital_f_, g__, d__, e__, n_, a__, b__, c__, x_],
        optional: [m_, g__, d__, e__, n_, a__, b__],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__, g__, n_], x_)
                && rubi_polynomial_q(&u__, x_)
                && integerq!(m_)
        },
        rhs: {
            let exponential = capital_f_.pow(&g__ * (&d__ + &e__ * x_).pow(&n_));
            let rational =
                u__.pow(&m_) / (&a__ + &b__ * x_ + &c__ * x_.pow(2));
            let expanded = rubi_expand_integrand_product(&exponential, &rational, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_2701(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_f_, a__, c__, d__, m_, n_, u__, x_, e__, g__);
    rules.push(rubi_rule!(
        order: 2701,
        source: "Int[u_^m_.*F_^(g_.*(d_.+e_.*x_)^n_.)/(a_+c_*x_^2),x_Symbol] :=
          Int[ExpandIntegrand[F^(g*(d+e*x)^n),u^m/(a+c*x^2),x],x] /;
        FreeQ[{F,a,c,d,e,g,n},x] && PolynomialQ[u,x] && IntegerQ[m]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: u__.pow(m_) * capital_f_.pow(g__ * (d__ + e__ * x_).pow(n_))
            / (a__ + c__ * x_.pow(2)),
        with: [u__, m_, capital_f_, g__, d__, e__, n_, a__, c__, x_],
        optional: [m_, g__, d__, e__, n_],
        when: {
            freeq!([capital_f_, a__, c__, d__, e__, g__, n_], x_)
                && rubi_polynomial_q(&u__, x_)
                && integerq!(m_)
        },
        rhs: {
            let exponential = capital_f_.pow(&g__ * (&d__ + &e__ * x_).pow(&n_));
            let rational = u__.pow(&m_) / (&a__ + &c__ * x_.pow(2));
            let expanded = rubi_expand_integrand_product(&exponential, &rational, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_2702(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_f_, a__, b__, x_);
    rules.push(rubi_rule!(
        order: 2702,
        source: "Int[F_^((a_.+b_.*x_^4)/x_^2),x_Symbol] :=
          Sqrt[Pi]*Exp[2*Sqrt[-a*Log[F]]*Sqrt[-b*Log[F]]]*Erf[(Sqrt[-a*Log[F]]+Sqrt[-b*Log[F]]*x^2)/x]/
            (4*Sqrt[-b*Log[F]]) -
          Sqrt[Pi]*Exp[-2*Sqrt[-a*Log[F]]*Sqrt[-b*Log[F]]]*Erf[(Sqrt[-a*Log[F]]-Sqrt[-b*Log[F]]*x^2)/x]/
            (4*Sqrt[-b*Log[F]]) /;
        FreeQ[{F,a,b},x]",
        desc: "Integration by substitution",
        refs: [],
        pattern: capital_f_.pow((a__ + b__ * x_.pow(4)) / x_.pow(2)),
        with: [capital_f_, a__, b__, x_],
        optional: [a__, b__],
        when: {
            freeq!([capital_f_, a__, b__], x_)
        },
        rhs: {
            let sqrt_a = (-&a__ * capital_f_.log()).sqrt();
            let sqrt_b = (-&b__ * capital_f_.log()).sqrt();
            let erf_plus = ((&sqrt_a + &sqrt_b * x_.pow(2)) / x_).erf();
            let erf_minus = ((&sqrt_a - &sqrt_b * x_.pow(2)) / x_).erf();
            let scale = Atom::var(Symbol::PI).sqrt() / (Atom::num(4) * &sqrt_b);

            rubi_simp(
                    &(&scale * (Atom::num(2) * &sqrt_a * &sqrt_b).exp() * erf_plus),
                    x_,
                ) - rubi_simp(
                    &(scale * (-Atom::num(2) * sqrt_a * sqrt_b).exp() * erf_minus),
                    x_,
                )
        },
    ));
}

fn push_rules_rule_2703(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_f_, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 2703,
        source: "Int[x_^m_.*(E^x_+x_^m_.)^n_,x_Symbol] :=
          -(E^x+x^m)^(n+1)/(n+1) +
          Int[(E^x+x^m)^(n+1),x] +
          m \\[Star] Int[x^(m-1)*(E^x+x^m)^n,x] /;
        RationalQ[m,n] && GtQ[m,0] && LtQ[n,0] && NeQ[n,-1]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: x_.pow(m_)
            * (capital_f_.pow(x_) + x_.pow(m_)).pow(n_),
        with: [capital_f_, m_, n_, x_],
        optional: [m_],
        when: {
            rubi_euler_symbol_q(&capital_f_)
                && rationalq!([m_, n_])
                && gtq!(m_, 0)
                && ltq!(n_, 0)
                && neq!(n_, -1)
        },
        rhs: {
            let base = capital_f_.pow(x_) + x_.pow(&m_);
            let recursive_1 = rubi_rhs_int(&base.pow(&n_ + 1), x_);
            let recursive_2 =
                rubi_rhs_int(&(x_.pow(&m_ - 1) * base.pow(&n_)), x_);

            rubi_simp(&(-base.pow(&n_ + 1) / (&n_ + 1)), x_)
                    + recursive_1
                    + rubi_star(m_, recursive_2)
        },
    ));
}

fn push_rules_rule_2704(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_f_, a__, b__, u__, v__, z_);
    let z_atom = Atom::var(z_);
    rules.push(rubi_rule!(
        order: 2704,
        source: "Int[u_.*F_^(a_.*(v_.+b_.*Log[z_])),x_Symbol] :=
          Int[u*F^(a*v)*z^(a*b*Log[F]),x] /;
        FreeQ[{F,a,b},x]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: u__ * capital_f_.pow(a__ * (v__ + b__ * z_atom.log())),
        with: [u__, capital_f_, a__, v__, b__, z_, x_],
        optional: [u__, a__, v__, b__],
        when: { freeq!([capital_f_, a__, b__], x_) },
        rhs: {
            let recursive_integrand =
                u__ * capital_f_.pow(&a__ * &v__) * z_.pow(&a__ * &b__ * capital_f_.log());

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_2705(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_f_, a__, b__, c__, d__, n_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 2705,
        source: "Int[F_^(f_.*(a_.+b_.*Log[c_.*(d_.+e_.*x_)^n_.]^2)),x_Symbol] :=
          (d+e*x)/(e*n*(c*(d+e*x)^n)^(1/n)) \\[Star] Subst[Int[E^(a*f*Log[F]+x/n+b*f*Log[F]*x^2),x],x,Log[c*(d+e*x)^n]] /;
        FreeQ[{F,a,b,c,d,e,f,n},x]",
        desc: "Piecewise constant extraction, algebraic simplification, and integration by substitution",
        refs: [],
        pattern: capital_f_
            .pow(f__ * (a__ + b__ * (c__ * (d__ + e__ * x_).pow(n_)).log().pow(2))),
        with: [capital_f_, f__, a__, b__, c__, d__, e__, n_, x_],
        optional: [f__, a__, b__, c__, d__, e__, n_],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__, f__, n_], x_)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let substitution_variable = Atom::var(substitution_symbol);
            let transformed_integrand = (&a__ * &f__ * capital_f_.log()
                + &substitution_variable / &n_
                + &b__ * &f__ * capital_f_.log() * substitution_variable.pow(2))
            .exp();
            let transformed_primitive = rubi_rhs_int(&transformed_integrand, substitution_symbol);
            let affine = &d__ + &e__ * x_;
            let substitution = (&c__ * affine.pow(&n_)).log();
            let denominator = &e__ * &n_ * (&c__ * affine.pow(&n_)).pow(Atom::num(1) / &n_);

            rubi_star(affine, rubi_subst(&transformed_primitive, substitution_symbol, substitution)
                    / denominator)
        },
    ));
}

fn push_rules_rule_2706(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_f_, a__, b__, c__, d__, m_, n_, x_, e__, f__, g__, h__
    );
    rules.push(rubi_rule!(
        order: 2706,
        source: "Int[(g_.+h_.*x_)^m_.*F_^(f_.*(a_.+b_.*Log[c_.*(d_.+e_.*x_)^n_.]^2)),x_Symbol] :=
          (g+h*x)^(m+1)/(h*n*(c*(d+e*x)^n)^((m+1)/n)) \\[Star]
            Subst[Int[E^(a*f*Log[F]+((m+1)*x)/n+b*f*Log[F]*x^2),x],x,Log[c*(d+e*x)^n]] /;
        FreeQ[{F,a,b,c,d,e,f,g,h,m,n},x] && EqQ[e*g-d*h,0]",
        desc: "Piecewise constant extraction, algebraic simplification, and integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_10(symbols),
        with: [g__, h__, m_, capital_f_, f__, a__, b__, c__, d__, e__, n_, x_],
        optional: [g__, h__, m_, f__, a__, b__, c__, d__, e__, n_],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__, f__, g__, h__, m_, n_], x_)
                && eqq!(&e__ * &g__ - &d__ * &h__, 0)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let substitution_variable = Atom::var(substitution_symbol);
            let transformed_integrand = (&a__ * &f__ * capital_f_.log()
                + (&m_ + 1) * &substitution_variable / &n_
                + &b__ * &f__ * capital_f_.log() * substitution_variable.pow(2))
            .exp();
            let transformed_primitive = rubi_rhs_int(&transformed_integrand, substitution_symbol);
            let affine = &d__ + &e__ * x_;
            let substitution = (&c__ * affine.pow(&n_)).log();
            let multiplier_affine = &g__ + &h__ * x_;
            let denominator =
                &h__ * &n_ * (&c__ * affine.pow(&n_)).pow((&m_ + 1) / &n_);

            rubi_star(multiplier_affine.pow(&m_ + 1), rubi_subst(&transformed_primitive, substitution_symbol, substitution)
                    / denominator)
        },
    ));
}

fn push_rules_rule_2707(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_f_, a__, b__, c__, d__, m_, n_, x_, e__, f__, g__, h__
    );
    rules.push(rubi_rule!(
        order: 2707,
        source: "Int[(g_.+h_.*x_)^m_.*F_^(f_.*(a_.+b_.*Log[c_.*(d_.+e_.*x_)^n_.]^2)),x_Symbol] :=
          1/e^(m+1) \\[Star] Subst[Int[ExpandIntegrand[F^(f*(a+b*Log[c*x^n]^2)),(e*g-d*h+h*x)^m,x],x],x,d+e*x] /;
        FreeQ[{F,a,b,c,d,e,f,g,h,n},x] && IGtQ[m,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_10(symbols),
        with: [g__, h__, m_, capital_f_, f__, a__, b__, c__, d__, e__, n_, x_],
        optional: [g__, h__, m_, f__, a__, b__, c__, d__, e__, n_],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__, f__, g__, h__, n_], x_)
                && igtq!(m_, 0)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let substitution_variable = Atom::var(substitution_symbol);
            let exponential = capital_f_.pow(
                &f__ * (&a__ + &b__ * (&c__ * substitution_variable.pow(&n_)).log().pow(2)),
            );
            let multiplier =
                (&e__ * &g__ - &d__ * &h__ + &h__ * &substitution_variable).pow(&m_);
            let expanded = rubi_expand_integrand_product(
                &exponential,
                &multiplier,
                substitution_symbol,
            );
            let transformed_primitive = rubi_rhs_int(&expanded, substitution_symbol);
            let substitution = &d__ + &e__ * x_;

            rubi_star(Atom::num(1) / e__.pow(&m_ + 1), rubi_subst(&transformed_primitive, substitution_symbol, substitution))
        },
    ));
}

fn push_rules_rule_2708(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_f_, a__, b__, c__, d__, m_, n_, x_, e__, f__, g__, h__
    );
    rules.push(rubi_rule!(
        order: 2708,
        source: "Int[(g_.+h_.*x_)^m_.*F_^(f_.*(a_.+b_.*Log[c_.*(d_.+e_.*x_)^n_.]^2)),x_Symbol] :=
          Unintegrable[(g+h*x)^m*F^(f*(a+b*Log[c*(d+e*x)^n]^2)),x] /;
        FreeQ[{F,a,b,c,d,e,f,g,h,m,n},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_10(symbols),
        with: [g__, h__, m_, capital_f_, f__, a__, b__, c__, d__, e__, n_, x_],
        optional: [g__, h__, m_, f__, a__, b__, c__, d__, e__, n_],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__, f__, g__, h__, m_, n_], x_)
        },
        rhs: {
            let affine = &d__ + &e__ * x_;
            let integrand = (&g__ + &h__ * x_).pow(&m_)
                * capital_f_.pow(
                    &f__ * (&a__ + &b__ * (&c__ * affine.pow(&n_)).log().pow(2)),
                );

            rubi_unintegrable(integrand, x_)
        },
    ));
}

fn push_rules_rule_2709(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, d__, n_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 2709,
        source: "Int[F_^(f_.*(a_.+b_.*Log[c_.*(d_.+e_.*x_)^n_.])^2),x_Symbol] :=
          c^(2*a*b*f*Log[F]) \\[Star] Int[(d+e*x)^(2*a*b*f*n*Log[F])*F^(a^2*f+b^2*f*Log[c*(d+e*x)^n]^2),x] /;
        FreeQ[{F,a,b,c,d,e,f,n},x] && IntegerQ[2*a*b*f*Log[F]]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_15(symbols),
        with: [capital_f_, f__, a__, b__, c__, d__, e__, n_, x_],
        optional: [f__, a__, b__, c__, d__, e__, n_],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__, f__, n_], x_)
                && integerq!(Atom::num(2) * &a__ * &b__ * &f__ * capital_f_.log())
        },
        rhs: {
            let affine = &d__ + &e__ * x_;
            let log_arg = &c__ * affine.pow(&n_);
            let k = Atom::num(2) * &a__ * &b__ * &f__ * capital_f_.log();
            let recursive_integrand = affine.pow(&k * &n_)
                * capital_f_.pow(a__.pow(2) * &f__ + b__.pow(2) * &f__ * log_arg.log().pow(2));
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(c__.pow(k), recursive)
        },
    ));
}

fn push_rules_rule_2710(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, d__, n_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 2710,
        source: "Int[F_^(f_.*(a_.+b_.*Log[c_.*(d_.+e_.*x_)^n_.])^2),x_Symbol] :=
          (c*(d+e*x)^n)^(2*a*b*f*Log[F])/(d+e*x)^(2*a*b*f*n*Log[F])*
            Int[(d+e*x)^(2*a*b*f*n*Log[F])*F^(a^2*f+b^2*f*Log[c*(d+e*x)^n]^2),x] /;
        FreeQ[{F,a,b,c,d,e,f,n},x] && Not[IntegerQ[2*a*b*f*Log[F]]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_15(symbols),
        with: [capital_f_, f__, a__, b__, c__, d__, e__, n_, x_],
        optional: [f__, a__, b__, c__, d__, e__, n_],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__, f__, n_], x_)
                && !integerq!(Atom::num(2) * &a__ * &b__ * &f__ * capital_f_.log())
        },
        rhs: {
            let affine = &d__ + &e__ * x_;
            let log_arg = &c__ * affine.pow(&n_);
            let k = Atom::num(2) * &a__ * &b__ * &f__ * capital_f_.log();
            let recursive_integrand = affine.pow(&k * &n_)
                * capital_f_.pow(a__.pow(2) * &f__ + b__.pow(2) * &f__ * log_arg.log().pow(2));
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(
                &(log_arg.pow(&k) * recursive / affine.pow(&k * &n_)),
                x_,
            )
        },
    ));
}

fn push_rules_rule_2711(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_f_, a__, b__, c__, d__, m_, n_, x_, e__, f__, g__, h__
    );
    rules.push(rubi_rule!(
        order: 2711,
        source: "Int[(g_.+h_.*x_)^m_.*F_^(f_.*(a_.+b_.*Log[c_.*(d_.+e_.*x_)^n_.])^2),x_Symbol] :=
          h^m*c^(2*a*b*f*Log[F])/e^m \\[Star] Int[(d+e*x)^(m+2*a*b*f*n*Log[F])*F^(a^2*f+b^2*f*Log[c*(d+e*x)^n]^2),x] /;
        FreeQ[{F,a,b,c,d,e,f,g,h,m,n},x] && EqQ[e*g-d*h,0] && IntegerQ[2*a*b*f*Log[F]] && (IntegerQ[m] || EqQ[h,e])",
        desc: "Algebraic expansion and algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [g__, h__, m_, capital_f_, f__, a__, b__, c__, d__, e__, n_, x_],
        optional: [g__, h__, m_, f__, a__, b__, c__, d__, e__, n_],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__, f__, g__, h__, m_, n_], x_)
                && eqq!(&e__ * &g__ - &d__ * &h__, 0)
                && integerq!(Atom::num(2) * &a__ * &b__ * &f__ * capital_f_.log())
                && (integerq!(m_) || eqq!(h__, e__))
        },
        rhs: {
            let affine = &d__ + &e__ * x_;
            let log_arg = &c__ * affine.pow(&n_);
            let k = Atom::num(2) * &a__ * &b__ * &f__ * capital_f_.log();
            let recursive_integrand = affine.pow(&m_ + &k * &n_)
                * capital_f_.pow(a__.pow(2) * &f__ + b__.pow(2) * &f__ * log_arg.log().pow(2));
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(h__.pow(&m_) * c__.pow(k) / e__.pow(&m_), recursive)
        },
    ));
}

fn push_rules_rule_2712(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_f_, a__, b__, c__, d__, m_, n_, x_, e__, f__, g__, h__
    );
    rules.push(rubi_rule!(
        order: 2712,
        source: "Int[(g_.+h_.*x_)^m_.*F_^(f_.*(a_.+b_.*Log[c_.*(d_.+e_.*x_)^n_.])^2),x_Symbol] :=
          (g+h*x)^m*(c*(d+e*x)^n)^(2*a*b*f*Log[F])/(d+e*x)^(m+2*a*b*f*n*Log[F])*
            Int[(d+e*x)^(m+2*a*b*f*n*Log[F])*F^(a^2*f+b^2*f*Log[c*(d+e*x)^n]^2),x] /;
        FreeQ[{F,a,b,c,d,e,f,g,h,m,n},x] && EqQ[e*g-d*h,0]",
        desc: "Algebraic expansion and piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [g__, h__, m_, capital_f_, f__, a__, b__, c__, d__, e__, n_, x_],
        optional: [g__, h__, m_, f__, a__, b__, c__, d__, e__, n_],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__, f__, g__, h__, m_, n_], x_)
                && eqq!(&e__ * &g__ - &d__ * &h__, 0)
        },
        rhs: {
            let affine = &d__ + &e__ * x_;
            let multiplier_affine = &g__ + &h__ * x_;
            let log_arg = &c__ * affine.pow(&n_);
            let k = Atom::num(2) * &a__ * &b__ * &f__ * capital_f_.log();
            let exponent = &m_ + &k * &n_;
            let recursive_integrand = affine.pow(&exponent)
                * capital_f_.pow(a__.pow(2) * &f__ + b__.pow(2) * &f__ * log_arg.log().pow(2));
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(
                &(multiplier_affine.pow(&m_) * log_arg.pow(k) * recursive
                    / affine.pow(exponent)),
                x_,
            )
        },
    ));
}

fn push_rules_rule_2713(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_f_, a__, b__, c__, d__, m_, n_, x_, e__, f__, g__, h__
    );
    rules.push(rubi_rule!(
        order: 2713,
        source: "Int[(g_.+h_.*x_)^m_.*F_^(f_.*(a_.+b_.*Log[c_.*(d_.+e_.*x_)^n_.])^2),x_Symbol] :=
          1/e^(m+1) \\[Star] Subst[Int[ExpandIntegrand[F^(f*(a+b*Log[c*x^n])^2),(e*g-d*h+h*x)^m,x],x],x,d+e*x] /;
        FreeQ[{F,a,b,c,d,e,f,g,h,n},x] && IGtQ[m,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [g__, h__, m_, capital_f_, f__, a__, b__, c__, d__, e__, n_, x_],
        optional: [g__, h__, m_, f__, a__, b__, c__, d__, e__, n_],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__, f__, g__, h__, n_], x_)
                && igtq!(m_, 0)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let substitution_variable = Atom::var(substitution_symbol);
            let exponential = capital_f_.pow(
                &f__ * (&a__ + &b__ * (&c__ * substitution_variable.pow(&n_)).log()).pow(2),
            );
            let multiplier =
                (&e__ * &g__ - &d__ * &h__ + &h__ * &substitution_variable).pow(&m_);
            let expanded = rubi_expand_integrand_product(
                &exponential,
                &multiplier,
                substitution_symbol,
            );
            let transformed_primitive = rubi_rhs_int(&expanded, substitution_symbol);
            let substitution = &d__ + &e__ * x_;

            rubi_star(Atom::num(1) / e__.pow(&m_ + 1), rubi_subst(&transformed_primitive, substitution_symbol, substitution))
        },
    ));
}

fn push_rules_rule_2714(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_f_, a__, b__, c__, d__, m_, n_, x_, e__, f__, g__, h__
    );
    rules.push(rubi_rule!(
        order: 2714,
        source: "Int[(g_.+h_.*x_)^m_.*F_^(f_.*(a_.+b_.*Log[c_.*(d_.+e_.*x_)^n_.])^2),x_Symbol] :=
          Unintegrable[(g+h*x)^m*F^(f*(a+b*Log[c*(d+e*x)^n])^2),x] /;
        FreeQ[{F,a,b,c,d,e,f,g,h,m,n},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [g__, h__, m_, capital_f_, f__, a__, b__, c__, d__, e__, n_, x_],
        optional: [g__, h__, m_, f__, a__, b__, c__, d__, e__, n_],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__, f__, g__, h__, m_, n_], x_)
        },
        rhs: {
            let affine = &d__ + &e__ * x_;
            let integrand = (&g__ + &h__ * x_).pow(&m_)
                * capital_f_.pow(
                    &f__ * (&a__ + &b__ * (&c__ * affine.pow(&n_)).log()).pow(2),
                );

            rubi_unintegrable(integrand, x_)
        },
    ));
}

fn push_rules_rule_2715(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, d__, n_, x_, e__);
    rules.push(rubi_rule!(
        order: 2715,
        source: "Int[Log[a_+b_.*(F_^(e_.*(c_.+d_.*x_)))^n_.],x_Symbol] :=
          1/(d*e*n*Log[F]) \\[Star] Subst[Int[Log[a+b*x]/x,x],x,(F^(e*(c+d*x)))^n] /;
        FreeQ[{F,a,b,c,d,e,n},x] && GtQ[a,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, capital_f_, e__, c__, d__, n_, x_],
        optional: [b__, e__, c__, d__, n_],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__, n_], x_)
                && gtq!(a__, 0)
        },
        rhs: {
            let denominator = &d__ * &e__ * &n_ * capital_f_.log();
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let substitution_variable = Atom::var(substitution_symbol);
            let transformed_integrand = (&a__ + &b__ * &substitution_variable).log()
                / &substitution_variable;
            let transformed_primitive = rubi_rhs_int(&transformed_integrand, substitution_symbol);
            let substitution = capital_f_.pow(&e__ * (&c__ + &d__ * x_)).pow(&n_);

            rubi_star(Atom::num(1) / denominator, rubi_subst(&transformed_primitive, substitution_symbol, substitution))
        },
    ));
}

fn push_rules_rule_2716(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, d__, n_, x_, e__);
    rules.push(rubi_rule!(
        order: 2716,
        source: "Int[Log[a_+b_.*(F_^(e_.*(c_.+d_.*x_)))^n_.],x_Symbol] :=
          x*Log[a+b*(F^(e*(c+d*x)))^n] - b*d*e*n*Log[F] \\[Star] Int[x*(F^(e*(c+d*x)))^n/(a+b*(F^(e*(c+d*x)))^n),x] /;
        FreeQ[{F,a,b,c,d,e,n},x] && Not[GtQ[a,0]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, capital_f_, e__, c__, d__, n_, x_],
        optional: [b__, e__, c__, d__, n_],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__, n_], x_)
                && !gtq!(a__, 0)
        },
        rhs: {
            let exponential_power = capital_f_.pow(&e__ * (&c__ + &d__ * x_)).pow(&n_);
            let log_argument = &a__ + &b__ * &exponential_power;
            let recursive_integrand =
                x_ * &exponential_power / (&a__ + &b__ * &exponential_power);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(x_ * log_argument.log()), x_)
                    - rubi_star(&b__ * &d__ * &e__ * &n_ * capital_f_.log(), recursive)
        },
    ));
}

fn push_rules_rule_2717(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_f_, a__, n_, u__, v_);
    rules.push(rubi_rule!(
        order: 2717,
        source: "Int[u_.*(a_.*F_^v_)^n_,x_Symbol] :=
          (a*F^v)^n/F^(n*v) \\[Star] Int[u*F^(n*v),x] /;
        FreeQ[{F,a,n},x] && Not[IntegerQ[n]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: u__ * (a__ * capital_f_.pow(v_)).pow(n_),
        with: [u__, a__, capital_f_, v_, n_, x_],
        optional: [u__, a__],
        when: { freeq!([capital_f_, a__, n_], x_) && !integerq!(n_) },
        rhs: {
            let recursive_integrand = &u__ * capital_f_.pow(&n_ * &v_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star((a__ * capital_f_.pow(&v_)).pow(&n_), recursive
                    / capital_f_.pow(&n_ * &v_))
        },
    ));
}

fn push_rules_rule_2718(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, d__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 2718,
        source: "Int[F_^(d_.*(c_.*(a_.+b_.*x_)^n_)^m_),x_Symbol] :=
          (a+b*x)*F^(d*(c*(a+b*x)^n)^m)/(b*d*(c*(a+b*x)^n)^m*Log[F]) /;
        FreeQ[{F,a,b,c,d,m,n},x] && EqQ[m*n,1]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_14(symbols),
        with: [capital_f_, d__, c__, a__, b__, n_, m_, x_],
        optional: [d__, c__, a__, b__],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, m_, n_], x_)
                && eqq!(&m_ * &n_, 1)
        },
        rhs: {
            let affine = &a__ + &b__ * x_;
            let nested_power = (&c__ * affine.pow(&n_)).pow(&m_);

            rubi_simp(&(
                affine * capital_f_.pow(&d__ * &nested_power)
                    / (&b__ * &d__ * nested_power * capital_f_.log())
            ), x_)
        },
    ));
}

fn push_rules_rule_2719(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, d__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 2719,
        source: "Int[F_^(d_.*(c_.*(a_.+b_.*x_)^n_)^m_),x_Symbol] :=
          -(a+b*x)*Gamma[1/(m*n),(-d*(c*(a+b*x)^n)^m)*Log[F]]/(b*m*n*((-d*(c*(a+b*x)^n)^m)*Log[F])^(1/(m*n))) /;
        FreeQ[{F,a,b,c,d,m,n},x]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_14(symbols),
        with: [capital_f_, d__, c__, a__, b__, n_, m_, x_],
        optional: [d__, c__, a__, b__],
        when: { freeq!([capital_f_, a__, b__, c__, d__, m_, n_], x_) },
        rhs: {
            let affine = &a__ + &b__ * x_;
            let nested_power = (&c__ * affine.pow(&n_)).pow(&m_);
            let gamma_argument = -&d__ * &nested_power * capital_f_.log();
            let reciprocal_power = Atom::num(1) / (&m_ * &n_);

            rubi_simp(&(
                -affine
                    * rubi_gamma(&reciprocal_power, &gamma_argument)
                    / (&b__
                        * &m_
                        * &n_
                        * gamma_argument.pow(reciprocal_power))
            ), x_)
        },
    ));
}

fn push_rules_rule_2720(rules: &mut Vec<RubiRule>) {
    rubi_symb!(u_);
    let u_atom = Atom::var(u_);
    rules.push(rubi_rule!(
        order: 2720,
        source: "Int[u_,x_Symbol] :=
          With[{v=FunctionOfExponential[u,x]},
          v/D[v,x] \\[Star] Subst[Int[FunctionOfExponentialFunction[u,x]/x,x],x,v]] /;
        FunctionOfExponentialQ[u,x] &&
          Not[MatchQ[u,w_*(a_.*v_^n_)^m_ /; FreeQ[{a,m,n},x] && IntegerQ[m*n]]] &&
          Not[MatchQ[u,E^(c_.*(a_.+b_.*x))*F_[v_] /; FreeQ[{a,b,c},x] && InverseFunctionQ[F[x]]]]",
        desc: "Integration by substitution",
        refs: [],
        pattern: u_atom,
        with: [u_, x_],
        when: {
            rubi_function_of_exponential_q(u_.as_view(), x_)
                && !rubi_function_of_exponential_rule_exclusion_q(u_.as_view(), x_)
        },
        rhs: {
            let exponential_function = rubi_function_of_exponential(u_.as_view(), x_).unwrap();
            let v = exponential_function.exponential;
            let dv = v.derivative(x_);
            let inner_integrand = exponential_function.function / x_;
            let inner = rubi_rhs_int(&inner_integrand, x_);

            rubi_star(&v, rubi_subst(&inner, x_, &v) / dv)
        },
    ));
}

fn push_rules_rule_2721(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, n_, u__, v_, w_);
    rules.push(rubi_rule!(
        order: 2721,
        source: "Int[u_.*(a_.*F_^v_+b_.*F_^w_)^n_,x_Symbol] :=
          Int[u*F^(n*v)*(a+b*F^ExpandToSum[w-v,x])^n,x] /;
        FreeQ[{F,a,b,n},x] && ILtQ[n,0] && LinearQ[{v,w},x]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_20(symbols),
        with: [u__, a__, capital_f_, v_, b__, w_, n_, x_],
        optional: [u__, a__, b__],
        when: {
            freeq!([capital_f_, a__, b__, n_], x_)
                && iltq!(n_, 0)
                && rubi_linear_q_list(&[&v_, &w_], x_)
        },
        rhs: {
            let expanded = rubi_expand_to_sum(&(&w_ - &v_), x_);
            let recursive_integrand = u__
                * capital_f_.pow(&n_ * &v_)
                * (&a__ + &b__ * capital_f_.pow(expanded)).pow(&n_);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_2722(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, capital_g_, a__, b__, n_, u__, v_, w_);
    rules.push(rubi_rule!(
        order: 2722,
        source: "Int[u_.*(a_.*F_^v_+b_.*G_^w_)^n_,x_Symbol] :=
          Int[u*F^(n*v)*(a+b*E^ExpandToSum[Log[G]*w-Log[F]*v,x])^n,x] /;
        FreeQ[{F,G,a,b,n},x] && ILtQ[n,0] && LinearQ[{v,w},x]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_21(symbols),
        with: [u__, a__, capital_f_, v_, b__, capital_g_, w_, n_, x_],
        optional: [u__, a__, b__],
        when: {
            freeq!([capital_f_, capital_g_, a__, b__, n_], x_)
                && iltq!(n_, 0)
                && rubi_linear_q_list(&[&v_, &w_], x_)
        },
        rhs: {
            let expanded = rubi_expand_to_sum(&(capital_g_.log() * &w_ - capital_f_.log() * &v_), x_);
            let recursive_integrand = u__
                * capital_f_.pow(&n_ * &v_)
                * (&a__ + &b__ * expanded.exp()).pow(&n_);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_2723(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, n_, u__, v_, w_);
    rules.push(rubi_rule!(
        order: 2723,
        source: "Int[u_.*(a_.*F_^v_+b_.*F_^w_)^n_,x_Symbol] :=
          (a*F^v+b*F^w)^n/(F^(n*v)*(a+b*F^ExpandToSum[w-v,x])^n) \\[Star] Int[u*F^(n*v)*(a+b*F^ExpandToSum[w-v,x])^n,x] /;
        FreeQ[{F,a,b,n},x] && Not[IntegerQ[n]] && LinearQ[{v,w},x]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_20(symbols),
        with: [u__, a__, capital_f_, v_, b__, w_, n_, x_],
        optional: [u__, a__, b__],
        when: {
            freeq!([capital_f_, a__, b__, n_], x_)
                && !integerq!(n_)
                && rubi_linear_q_list(&[&v_, &w_], x_)
        },
        rhs: {
            let expanded = rubi_expand_to_sum(&(&w_ - &v_), x_);
            let normalized_base = &a__ + &b__ * capital_f_.pow(expanded);
            let recursive_integrand =
                &u__ * capital_f_.pow(&n_ * &v_) * normalized_base.pow(&n_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let source_base = &a__ * capital_f_.pow(&v_) + &b__ * capital_f_.pow(&w_);

            rubi_star(source_base.pow(&n_), recursive
                    / (capital_f_.pow(&n_ * &v_) * normalized_base.pow(n_)))
        },
    ));
}

fn push_rules_rule_2724(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, capital_g_, a__, b__, n_, u__, v_, w_);
    rules.push(rubi_rule!(
        order: 2724,
        source: "Int[u_.*(a_.*F_^v_+b_.*G_^w_)^n_,x_Symbol] :=
          (a*F^v+b*G^w)^n/(F^(n*v)*(a+b*E^ExpandToSum[Log[G]*w-Log[F]*v,x])^n) \\[Star] Int[u*F^(n*v)*(a+b*E^ExpandToSum[Log[G]*w-Log[F]*v,x])^n,x] /;
        FreeQ[{F,G,a,b,n},x] && Not[IntegerQ[n]] && LinearQ[{v,w},x]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_21(symbols),
        with: [u__, a__, capital_f_, v_, b__, capital_g_, w_, n_, x_],
        optional: [u__, a__, b__],
        when: {
            freeq!([capital_f_, capital_g_, a__, b__, n_], x_)
                && !integerq!(n_)
                && rubi_linear_q_list(&[&v_, &w_], x_)
        },
        rhs: {
            let expanded = rubi_expand_to_sum(&(capital_g_.log() * &w_ - capital_f_.log() * &v_), x_);
            let normalized_base = &a__ + &b__ * expanded.exp();
            let recursive_integrand =
                &u__ * capital_f_.pow(&n_ * &v_) * normalized_base.pow(&n_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let source_base = &a__ * capital_f_.pow(&v_) + &b__ * capital_g_.pow(&w_);

            rubi_star(source_base.pow(&n_), recursive
                    / (capital_f_.pow(&n_ * &v_) * normalized_base.pow(n_)))
        },
    ));
}

fn push_rules_rule_2725(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_f_, capital_g_, u__, v_, w_);
    rules.push(rubi_rule!(
        order: 2725,
        source: "Int[u_.*F_^v_*G_^w_,x_Symbol] :=
          With[{z=v*Log[F]+w*Log[G]},
          Int[u*NormalizeIntegrand[E^z,x],x] /;
         BinomialQ[z,x] || PolynomialQ[z,x] && LeQ[Exponent[z,x],2]] /;
        FreeQ[{F,G},x]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: u__ * capital_f_.pow(v_) * capital_g_.pow(w_),
        with: [u__, capital_f_, v_, capital_g_, w_, x_],
        optional: [u__],
        when: {
            freeq!([capital_f_, capital_g_], x_)
                && {
                    let z = &v_ * rubi_log(&capital_f_) + &w_ * rubi_log(&capital_g_);
                    rubi_binomial_q(&z, x_)
                        || rubi_polynomial_q(&z, x_)
                            && polynomial_degree(&z, x_).is_some_and(|degree| degree <= 2)
                }
        },
        rhs: {
            let z = &v_ * rubi_log(&capital_f_) + &w_ * rubi_log(&capital_g_);
            let normalized = rubi_normalize_exponential_integrand(&z, x_);
            let recursive_integrand = u__ * normalized;

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_2726(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_f_, u_, v__, w__, y__);
    rules.push(rubi_rule!(
        order: 2726,
        source: "Int[F_^u_*(v_+w_)*y_.,x_Symbol] :=
          With[{z=v*y/(Log[F]*D[u,x])},
          F^u*z /;
         EqQ[D[z,x],w*y]] /;
        FreeQ[F,x]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: capital_f_.pow(u_) * (v__ + w__) * y__,
        with: [capital_f_, u_, v__, w__, y__, x_],
        optional: [y__],
        x_dep: [u_],
        x_free: [capital_f_],
        when: {
            freeq!(capital_f_, x_) && {
                let z = &v__ * &y__ / (rubi_log(&capital_f_) * rubi_d(&u_, x_));
                eqq!(rubi_d(&z, x_), &w__ * &y__)
            }
        },
        rhs: {
            let z = &v__ * &y__ / (rubi_log(&capital_f_) * rubi_d(&u_, x_));

            rubi_simp(&(capital_f_.pow(u_) * z), x_)
        },
    ));
}

fn push_rules_rule_2727(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_f_, n_, u_, v_, w__);
    rules.push(rubi_rule!(
        order: 2727,
        source: "Int[F_^u_*v_^n_.*w_,x_Symbol] :=
          With[{z=Log[F]*v*D[u,x]+(n+1)*D[v,x]},
          Coefficient[w,x,Exponent[w,x]]/Coefficient[z,x,Exponent[z,x]]*F^u*v^(n+1) /;
         EqQ[Exponent[w,x],Exponent[z,x]] && EqQ[w*Coefficient[z,x,Exponent[z,x]],z*Coefficient[w,x,Exponent[w,x]]]] /;
        FreeQ[{F,n},x] && PolynomialQ[u,x] && PolynomialQ[v,x] && PolynomialQ[w,x]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: capital_f_.pow(u_) * v_.pow(n_) * w__,
        with: [capital_f_, u_, v_, n_, w__, x_],
        optional: [n_],
        when: {
            freeq!([capital_f_, n_], x_)
                && rubi_polynomial_q(&u_, x_)
                && rubi_polynomial_q(&v_, x_)
                && rubi_polynomial_q(&w__, x_)
                && {
                    let z = rubi_log(&capital_f_) * &v_ * rubi_d(&u_, x_)
                        + (&n_ + 1) * rubi_d(&v_, x_);
                    polynomial_degree(&w__, x_).is_some_and(|w_exponent| {
                        polynomial_degree(&z, x_).is_some_and(|z_exponent| {
                            w_exponent == z_exponent
                                && rubi_coefficient(&w__, x_, w_exponent).is_some_and(
                                    |w_coefficient| {
                                        rubi_coefficient(&z, x_, z_exponent).is_some_and(
                                            |z_coefficient| {
                                                eqq!(
                                                    &w__ * &z_coefficient,
                                                    &z * &w_coefficient
                                                )
                                            },
                                        )
                                    },
                                )
                        })
                    })
                }
        },
        rhs: {
            let z = rubi_log(&capital_f_) * &v_ * rubi_d(&u_, x_) + (&n_ + 1) * rubi_d(&v_, x_);
            let w_exponent = polynomial_degree(&w__, x_).unwrap();
            let z_exponent = polynomial_degree(&z, x_).unwrap();
            let w_coefficient = rubi_coefficient(&w__, x_, w_exponent).unwrap();
            let z_coefficient = rubi_coefficient(&z, x_, z_exponent).unwrap();

            rubi_simp(
                &(w_coefficient / z_coefficient * capital_f_.pow(u_) * v_.pow(&n_ + 1)),
                x_,
            )
        },
    ));
}

fn push_rules_rule_2728(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_a__,
        capital_b__,
        capital_c__,
        capital_f_,
        a__,
        b__,
        c__,
        d__,
        n_,
        x_,
        e__,
        f__,
        g__
    );
    rules.push(rubi_rule!(
        order: 2728,
        source: "Int[(a_.+b_.*F_^(c_.*Sqrt[d_.+e_.*x_]/Sqrt[f_.+g_.*x_]))^n_./(A_.+B_.*x_+C_.*x_^2),x_Symbol] :=
          2*e*g/(C*(e*f-d*g)) \\[Star] Subst[Int[(a+b*F^(c*x))^n/x,x],x,Sqrt[d+e*x]/Sqrt[f+g*x]] /;
        FreeQ[{a,b,c,d,e,f,g,A,B,C,F},x] && EqQ[C*d*f-A*e*g,0] && EqQ[B*e*g-C*(e*f+d*g),0] && IGtQ[n,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, capital_f_, c__, d__, e__, f__, g__, n_, capital_a__, capital_b__, capital_c__, x_],
        optional: [
            a__, b__, c__, d__, e__, f__, g__, n_, capital_a__, capital_b__, capital_c__
        ],
        when: {
            freeq!(
                    [
                        a__,
                        b__,
                        c__,
                        d__,
                        e__,
                        f__,
                        g__,
                        capital_a__,
                        capital_b__,
                        capital_c__,
                        capital_f_
                    ],
                    x_
                )
                && eqq!(&capital_c__ * &d__ * &f__ - &capital_a__ * &e__ * &g__, 0)
                && eqq!(
                    &capital_b__ * &e__ * &g__
                        - &capital_c__ * (&e__ * &f__ + &d__ * &g__),
                    0
                )
                && igtq!(n_, 0)
        },
        rhs: {
            let denominator = &capital_c__ * (&e__ * &f__ - &d__ * &g__);
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let substitution_variable = Atom::var(substitution_symbol);
            let transformed_integrand =
                (&a__ + &b__ * capital_f_.pow(&c__ * &substitution_variable)).pow(&n_)
                    / &substitution_variable;
            let transformed_primitive = rubi_rhs_int(&transformed_integrand, substitution_symbol);
            let substitution =
                (&d__ + &e__ * x_).sqrt() / (&f__ + &g__ * x_).sqrt();

            rubi_star(Atom::num(2) * &e__ * &g__ / denominator, rubi_subst(&transformed_primitive, substitution_symbol, substitution))
        },
    ));
}

fn push_rules_rule_2729(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_a__,
        capital_c__,
        capital_f_,
        a__,
        b__,
        c__,
        d__,
        n_,
        x_,
        e__,
        f__,
        g__
    );
    rules.push(rubi_rule!(
        order: 2729,
        source: "Int[(a_.+b_.*F_^(c_.*Sqrt[d_.+e_.*x_]/Sqrt[f_.+g_.*x_]))^n_./(A_+C_.*x_^2),x_Symbol] :=
          2*e*g/(C*(e*f-d*g)) \\[Star] Subst[Int[(a+b*F^(c*x))^n/x,x],x,Sqrt[d+e*x]/Sqrt[f+g*x]] /;
        FreeQ[{a,b,c,d,e,f,g,A,C,F},x] && EqQ[C*d*f-A*e*g,0] && EqQ[e*f+d*g,0] && IGtQ[n,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, capital_f_, c__, d__, e__, f__, g__, n_, capital_a__, capital_c__, x_],
        optional: [a__, b__, c__, d__, e__, f__, g__, n_, capital_c__],
        when: {
            freeq!(
                    [
                        a__,
                        b__,
                        c__,
                        d__,
                        e__,
                        f__,
                        g__,
                        capital_a__,
                        capital_c__,
                        capital_f_
                    ],
                    x_
                )
                && eqq!(&capital_c__ * &d__ * &f__ - &capital_a__ * &e__ * &g__, 0)
                && eqq!(&e__ * &f__ + &d__ * &g__, 0)
                && igtq!(n_, 0)
        },
        rhs: {
            let denominator = &capital_c__ * (&e__ * &f__ - &d__ * &g__);
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let substitution_variable = Atom::var(substitution_symbol);
            let transformed_integrand =
                (&a__ + &b__ * capital_f_.pow(&c__ * &substitution_variable)).pow(&n_)
                    / &substitution_variable;
            let transformed_primitive = rubi_rhs_int(&transformed_integrand, substitution_symbol);
            let substitution =
                (&d__ + &e__ * x_).sqrt() / (&f__ + &g__ * x_).sqrt();

            rubi_star(Atom::num(2) * &e__ * &g__ / denominator, rubi_subst(&transformed_primitive, substitution_symbol, substitution))
        },
    ));
}

fn push_rules_rule_2730(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_a__,
        capital_b__,
        capital_c__,
        capital_f_,
        a__,
        b__,
        c__,
        d__,
        n_,
        x_,
        e__,
        f__,
        g__
    );
    rules.push(rubi_rule!(
        order: 2730,
        source: "Int[(a_.+b_.*F_^(c_.*Sqrt[d_.+e_.*x_]/Sqrt[f_.+g_.*x_]))^n_/(A_.+B_.*x_+C_.*x_^2),x_Symbol] :=
          Unintegrable[(a+b*F^(c*Sqrt[d+e*x]/Sqrt[f+g*x]))^n/(A+B*x+C*x^2),x] /;
        FreeQ[{a,b,c,d,e,f,g,A,B,C,F,n},x] && EqQ[C*d*f-A*e*g,0] && EqQ[B*e*g-C*(e*f+d*g),0] && Not[IGtQ[n,0]]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, capital_f_, c__, d__, e__, f__, g__, n_, capital_a__, capital_b__, capital_c__, x_],
        optional: [a__, b__, c__, d__, e__, f__, g__, capital_a__, capital_b__, capital_c__],
        when: {
            freeq!(
                    [
                        a__,
                        b__,
                        c__,
                        d__,
                        e__,
                        f__,
                        g__,
                        capital_a__,
                        capital_b__,
                        capital_c__,
                        capital_f_,
                        n_
                    ],
                    x_
                )
                && eqq!(&capital_c__ * &d__ * &f__ - &capital_a__ * &e__ * &g__, 0)
                && eqq!(
                    &capital_b__ * &e__ * &g__
                        - &capital_c__ * (&e__ * &f__ + &d__ * &g__),
                    0
                )
                && !igtq!(n_, 0)
        },
        rhs: {
            let integrand = (&a__
                + &b__
                    * capital_f_.pow(
                        &c__ * (&d__ + &e__ * x_).sqrt()
                            / (&f__ + &g__ * x_).sqrt(),
                    ))
            .pow(&n_)
                / (&capital_a__ + &capital_b__ * x_ + &capital_c__ * x_.pow(2));

            rubi_unintegrable(integrand, x_)
        },
    ));
}

fn push_rules_rule_2731(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_a__,
        capital_c__,
        capital_f_,
        a__,
        b__,
        c__,
        d__,
        n_,
        x_,
        e__,
        f__,
        g__
    );
    rules.push(rubi_rule!(
        order: 2731,
        source: "Int[(a_.+b_.*F_^(c_.*Sqrt[d_.+e_.*x_]/Sqrt[f_.+g_.*x_]))^n_/(A_+C_.*x_^2),x_Symbol] :=
          Unintegrable[(a+b*F^(c*Sqrt[d+e*x]/Sqrt[f+g*x]))^n/(A+C*x^2),x] /;
        FreeQ[{a,b,c,d,e,f,g,A,C,F,n},x] && EqQ[C*d*f-A*e*g,0] && EqQ[e*f+d*g,0] && Not[IGtQ[n,0]]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, capital_f_, c__, d__, e__, f__, g__, n_, capital_a__, capital_c__, x_],
        optional: [a__, b__, c__, d__, e__, f__, g__, capital_c__],
        when: {
            freeq!(
                    [
                        a__,
                        b__,
                        c__,
                        d__,
                        e__,
                        f__,
                        g__,
                        capital_a__,
                        capital_c__,
                        capital_f_,
                        n_
                    ],
                    x_
                )
                && eqq!(&capital_c__ * &d__ * &f__ - &capital_a__ * &e__ * &g__, 0)
                && eqq!(&e__ * &f__ + &d__ * &g__, 0)
                && !igtq!(n_, 0)
        },
        rhs: {
            let integrand = (&a__
                + &b__
                    * capital_f_.pow(
                        &c__ * (&d__ + &e__ * x_).sqrt()
                            / (&f__ + &g__ * x_).sqrt(),
                    ))
            .pow(&n_)
                / (&capital_a__ + &capital_c__ * x_.pow(2));

            rubi_unintegrable(integrand, x_)
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
    let capital_c__ = symbols.capital_c__;
    let capital_f_ = symbols.capital_f_;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let g__ = symbols.g__;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    (a__ + b__ * capital_f_.pow(c__ * (d__ + e__ * x_).sqrt() / (f__ + g__ * x_).sqrt())).pow(n_)
        / (capital_a__ + capital_b__ * x_ + capital_c__ * x_.pow(2))
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let capital_a__ = symbols.capital_a__;
    let capital_c__ = symbols.capital_c__;
    let capital_f_ = symbols.capital_f_;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let g__ = symbols.g__;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    (a__ + b__ * capital_f_.pow(c__ * (d__ + e__ * x_).sqrt() / (f__ + g__ * x_).sqrt())).pow(n_)
        / (capital_a__ + capital_c__ * x_.pow(2))
}

#[inline(never)]
fn rubi_shared_pattern_2(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let capital_f_ = symbols.capital_f_;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    (a__ + b__ * capital_f_.pow(e__ * (c__ + d__ * x_)).pow(n_)).log()
}

#[inline(never)]
fn rubi_shared_pattern_3(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let capital_f_ = symbols.capital_f_;
    let d__ = symbols.d__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    (c__ + d__ * x_).pow(m_) * capital_f_.pow(a__ + b__ * (c__ + d__ * x_).pow(n_))
}

#[inline(never)]
fn rubi_shared_pattern_4(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let capital_f_ = symbols.capital_f_;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let x_ = symbols.x_;
    (d__ + e__ * x_) * capital_f_.pow(a__ + b__ * x_ + c__ * x_.pow(2))
}

#[inline(never)]
fn rubi_shared_pattern_5(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let capital_f_ = symbols.capital_f_;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let m_ = symbols.m_;
    let x_ = symbols.x_;
    (d__ + e__ * x_).pow(m_) * capital_f_.pow(a__ + b__ * x_ + c__ * x_.pow(2))
}

#[inline(never)]
fn rubi_shared_pattern_6(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let capital_f_ = symbols.capital_f_;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let x_ = symbols.x_;
    (e__ + f__ * x_).pow(m_) * capital_f_.pow(a__ + b__ * (c__ + d__ * x_).pow(2))
}

#[inline(never)]
fn rubi_shared_pattern_7(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let capital_f_ = symbols.capital_f_;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    (e__ + f__ * x_).pow(m_) * capital_f_.pow(a__ + b__ * (c__ + d__ * x_).pow(n_))
}

#[inline(never)]
fn rubi_shared_pattern_8(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let capital_f_ = symbols.capital_f_;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let g__ = symbols.g__;
    let h__ = symbols.h__;
    let m_ = symbols.m_;
    let x_ = symbols.x_;
    (g__ + h__ * x_).pow(m_) * capital_f_.pow(e__ + f__ * (a__ + b__ * x_) / (c__ + d__ * x_))
}

#[inline(never)]
fn rubi_shared_pattern_9(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let capital_f_ = symbols.capital_f_;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let g__ = symbols.g__;
    let h__ = symbols.h__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    (g__ + h__ * x_).pow(m_)
        * capital_f_.pow(f__ * (a__ + b__ * (c__ * (d__ + e__ * x_).pow(n_)).log()).pow(2))
}

#[inline(never)]
fn rubi_shared_pattern_10(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let capital_f_ = symbols.capital_f_;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let g__ = symbols.g__;
    let h__ = symbols.h__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    (g__ + h__ * x_).pow(m_)
        * capital_f_.pow(f__ * (a__ + b__ * (c__ * (d__ + e__ * x_).pow(n_)).log().pow(2)))
}

#[inline(never)]
fn rubi_shared_pattern_11(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let capital_f_ = symbols.capital_f_;
    let d__ = symbols.d__;
    let x_ = symbols.x_;
    capital_f_.pow(a__ + b__ * (c__ + d__ * x_).pow(2))
}

#[inline(never)]
fn rubi_shared_pattern_12(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let capital_f_ = symbols.capital_f_;
    let d__ = symbols.d__;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    capital_f_.pow(a__ + b__ * (c__ + d__ * x_).pow(n_))
}

#[inline(never)]
fn rubi_shared_pattern_13(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let capital_f_ = symbols.capital_f_;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    capital_f_.pow(a__ + b__ * (c__ + d__ * x_).pow(n_)) / (e__ + f__ * x_)
}

#[inline(never)]
fn rubi_shared_pattern_14(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let capital_f_ = symbols.capital_f_;
    let d__ = symbols.d__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    capital_f_.pow(d__ * (c__ * (a__ + b__ * x_).pow(n_)).pow(m_))
}

#[inline(never)]
fn rubi_shared_pattern_15(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let capital_f_ = symbols.capital_f_;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    capital_f_.pow(f__ * (a__ + b__ * (c__ * (d__ + e__ * x_).pow(n_)).log()).pow(2))
}

#[inline(never)]
fn rubi_shared_pattern_16(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let capital_f_ = symbols.capital_f_;
    let capital_g_ = symbols.capital_g_;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let g__ = symbols.g__;
    let h__ = symbols.h__;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    capital_g_.pow(h__ * (f__ + g__ * x_))
        * (a__ + b__ * capital_f_.pow(e__ * (c__ + d__ * x_))).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_17(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let capital_f_ = symbols.capital_f_;
    let capital_g_ = symbols.capital_g_;
    let capital_h_ = symbols.capital_h_;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let g__ = symbols.g__;
    let h__ = symbols.h__;
    let p_ = symbols.p_;
    let r__ = symbols.r__;
    let s__ = symbols.s__;
    let t__ = symbols.t__;
    let x_ = symbols.x_;
    capital_g_.pow(h__ * (f__ + g__ * x_))
        * capital_h_.pow(t__ * (r__ + s__ * x_))
        * (a__ + b__ * capital_f_.pow(e__ * (c__ + d__ * x_))).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_18(symbols: &RubiSymbols) -> Atom {
    let capital_f_ = symbols.capital_f_;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let m_ = symbols.m_;
    let px__ = symbols.px__;
    let v_ = symbols.v_;
    let x_ = symbols.x_;
    px__ * (d__ + e__ * x_).pow(m_) * capital_f_.pow(v_)
}

#[inline(never)]
fn rubi_shared_pattern_19(symbols: &RubiSymbols) -> Atom {
    let capital_f_ = symbols.capital_f_;
    let px__ = symbols.px__;
    let v_ = symbols.v_;
    px__ * capital_f_.pow(v_)
}

#[inline(never)]
fn rubi_shared_pattern_20(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let capital_f_ = symbols.capital_f_;
    let n_ = symbols.n_;
    let u__ = symbols.u__;
    let v_ = symbols.v_;
    let w_ = symbols.w_;
    u__ * (a__ * capital_f_.pow(v_) + b__ * capital_f_.pow(w_)).pow(n_)
}

#[inline(never)]
fn rubi_shared_pattern_21(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let capital_f_ = symbols.capital_f_;
    let capital_g_ = symbols.capital_g_;
    let n_ = symbols.n_;
    let u__ = symbols.u__;
    let v_ = symbols.v_;
    let w_ = symbols.w_;
    u__ * (a__ * capital_f_.pow(v_) + b__ * capital_g_.pow(w_)).pow(n_)
}
