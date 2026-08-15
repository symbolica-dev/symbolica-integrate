use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_3042(rules);
    push_rules_rule_3043(rules);
    push_rules_rule_3044(rules);
    push_rules_rule_3045(rules);
    push_rules_rule_3046(rules);
    push_rules_rule_3047(rules);
    push_rules_rule_3048(rules);
    push_rules_rule_3049(rules);
    push_rules_rule_3050(rules);
    push_rules_rule_3051(rules);
    push_rules_rule_3052(rules);
    push_rules_rule_3053(rules);
    push_rules_rule_3054(rules);
    push_rules_rule_3055(rules);
    push_rules_rule_3056(rules);
    push_rules_rule_3057(rules);
    push_rules_rule_3058(rules);
    push_rules_rule_3059(rules);
    push_rules_rule_3060(rules);
    push_rules_rule_3061(rules);
    push_rules_rule_3062(rules);
    push_rules_rule_3063(rules);
    push_rules_rule_3064(rules);
    push_rules_rule_3065(rules);
    push_rules_rule_3066(rules);
    push_rules_rule_3067(rules);
    push_rules_rule_3068(rules);
    push_rules_rule_3069(rules);
    push_rules_rule_3070(rules);
    push_rules_rule_3071(rules);
    push_rules_rule_3072(rules);
    push_rules_rule_3073(rules);
    push_rules_rule_3074(rules);
    push_rules_rule_3075(rules);
    push_rules_rule_3076(rules);
    push_rules_rule_3077(rules);
    push_rules_rule_3078(rules);
    push_rules_rule_3079(rules);
    push_rules_rule_3080(rules);
    push_rules_rule_3081(rules);
    push_rules_rule_3082(rules);
    push_rules_rule_3083(rules);
    push_rules_rule_3084(rules);
    push_rules_rule_3085(rules);
    push_rules_rule_3086(rules);
    push_rules_rule_3087(rules);
    push_rules_rule_3088(rules);
    push_rules_rule_3089(rules);
    push_rules_rule_3090(rules);
    push_rules_rule_3091(rules);
    push_rules_rule_3092(rules);
    push_rules_rule_3093(rules);
    push_rules_rule_3094(rules);
    push_rules_rule_3095(rules);
    push_rules_rule_3096(rules);
    push_rules_rule_3097(rules);
    push_rules_rule_3098(rules);
    push_rules_rule_3099(rules);
    push_rules_rule_3100(rules);
    push_rules_rule_3101(rules);
    push_rules_rule_3102(rules);
    push_rules_rule_3103(rules);
    push_rules_rule_3104(rules);
    push_rules_rule_3105(rules);
    push_rules_rule_3106(rules);
    push_rules_rule_3107(rules);
    push_rules_rule_3108(rules);
    push_rules_rule_3109(rules);
    push_rules_rule_3110(rules);
    push_rules_rule_3111(rules);
    push_rules_rule_3112(rules);
}

fn push_rules_rule_3042(rules: &mut Vec<RubiRule>) {
    rubi_symb!(u__);
    rules.push(rubi_rule!(
        order: 3042,
        source: "Int[u_,x_Symbol] :=
          Int[DeactivateTrig[u,x],x] /;
        FunctionOfTrigOfLinearQ[u,x]",
        desc: "Rewrite trigonometric functions to Rubi's inert form before integrating.",
        refs: [],
        pattern: Atom::var(u__),
        with: [u__, x_],
        when: { rubi_function_of_trig_of_linear_q(&u__, x_) },
        rhs: {
            let deactivated = rubi_deactivate_trig(&u__, x_);
            rubi_rhs_int(&deactivated, x_)
        },
    ));
}

fn push_rules_rule_3043(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, n_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 3043,
        source: "Int[(a_.*sin[e_.+f_.*x_])^m_.*(b_.*cos[e_.+f_.*x_])^n_.,x_Symbol] :=
          (a*Sin[e+f*x])^(m+1)*(b*Cos[e+f*x])^(n+1)/(a*b*f*(m+1)) /;
        FreeQ[{a,b,e,f,m,n},x] && EqQ[m+n+2,0] && NeQ[m,-1]",
        desc: "Apply the direct antiderivative formula.",
        refs: ["G&R 2.510.3, CRC 334a, A&S 4.3.128b with m+n+2\\[Equal]0Bold", "G&R 2.510.6, CRC 334b, A&S 4.3.128a with m+n+2\\[Equal]0Bold"],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, e__, f__, m_, b__, n_, x_],
        optional: [a__, e__, f__, m_, b__, n_],
        when: {
            freeq!([a__, b__, e__, f__, m_, n_], x_)
                && eqq!(&m_ + &n_ + 2, 0)
                && neq!(m_, -Atom::num(1))
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            rubi_simp(
                &((&a__ * angle.sin()).pow(&m_ + 1) * (&b__ * angle.cos()).pow(&n_ + 1)
                    / (&a__ * &b__ * &f__ * (&m_ + 1))),
                x_,
            )
        },
    ));
}

fn push_rules_rule_3044(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, m_, n_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 3044,
        source: "Int[(a_.*sin[e_.+f_.*x_])^m_.*cos[e_.+f_.*x_]^n_.,x_Symbol] :=
          1/(a*f) \\[Star] Subst[Int[x^m*(1-x^2/a^2)^((n-1)/2),x],x,a*Sin[e+f*x]] /;
        FreeQ[{a,e,f,m},x] && IntegerQ[(n-1)/2] && Not[IntegerQ[(m-1)/2] && LtQ[0,m,n]]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (a__ * i_sin(e__ + f__ * x_)).pow(m_) * i_cos(e__ + f__ * x_).pow(n_),
        with: [a__, e__, f__, m_, n_, x_],
        optional: [a__, e__, f__, m_, n_],
        when: {
            freeq!([a__, e__, f__, m_], x_)
                && integerq!((&n_ - 1) / 2)
                && !(integerq!((&m_ - 1) / 2) && gtq!(m_, 0) && ltq!(m_, n_))
        },
        rhs: {
            let subst_guard = fresh_substitution_symbol().unwrap();
            let subst = subst_guard.symbol();
            let z = Atom::var(subst);
            let transformed = z.pow(&m_) * (Atom::num(1) - z.pow(2) / a__.pow(2)).pow((&n_ - 1) / 2);
            let primitive = rubi_rhs_int(&transformed, subst);
            let substituted = rubi_subst(
                    &primitive,
                    subst,
                    &a__ * (&e__ + &f__ * x_).sin(),
                );
            rubi_star(Atom::num(1) / (&a__ * &f__), substituted)
        },
    ));
}

fn push_rules_rule_3045(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, m_, n_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 3045,
        source: "Int[(a_.*cos[e_.+f_.*x_])^m_.*sin[e_.+f_.*x_]^n_.,x_Symbol] :=
          -1/(a*f) \\[Star] Subst[Int[x^m*(1-x^2/a^2)^((n-1)/2),x],x,a*Cos[e+f*x]] /;
        FreeQ[{a,e,f,m},x] && IntegerQ[(n-1)/2] && Not[IntegerQ[(m-1)/2] && GtQ[m,0] && LeQ[m,n]]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (a__ * i_cos(e__ + f__ * x_)).pow(m_) * i_sin(e__ + f__ * x_).pow(n_),
        with: [a__, e__, f__, m_, n_, x_],
        optional: [a__, e__, f__, m_, n_],
        when: {
            freeq!([a__, e__, f__, m_], x_)
                && integerq!((&n_ - 1) / 2)
                && !(integerq!((&m_ - 1) / 2) && gtq!(m_, 0) && leq!(m_, n_))
        },
        rhs: {
            let subst_guard = fresh_substitution_symbol().unwrap();
            let subst = subst_guard.symbol();
            let z = Atom::var(subst);
            let transformed = z.pow(&m_) * (Atom::num(1) - z.pow(2) / a__.pow(2)).pow((&n_ - 1) / 2);
            let primitive = rubi_rhs_int(&transformed, subst);
            let substituted = rubi_subst(
                    &primitive,
                    subst,
                    &a__ * (&e__ + &f__ * x_).cos(),
                );
            rubi_star(-(Atom::num(1) / (&a__ * &f__)), substituted)
        },
    ));
}

fn push_rules_rule_3046(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, n_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 3046,
        source: "Int[(a_.*sin[e_.+f_.*x_])^m_*(b_.*cos[e_.+f_.*x_])^n_,x_Symbol] :=
          -a*(a*Sin[e+f*x])^(m-1)*(b*Cos[e+f*x])^(n+1)/(b*f*(n+1)) +
          a^2*(m-1)/(b^2*(n+1)) \\[Star] Int[(a*Sin[e+f*x])^(m-2)*(b*Cos[e+f*x])^(n+2),x] /;
        FreeQ[{a,b,e,f},x] && GtQ[m,1] && LtQ[n,-1] && (IntegersQ[2*m,2*n] || EqQ[m+n,0])",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: ["G&R 2.510.1", "G&R 2.510.4"],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, e__, f__, m_, b__, n_, x_],
        optional: [a__, e__, f__, b__],
        when: {
            freeq!([a__, b__, e__, f__], x_)
                && gtq!(m_, 1)
                && ltq!(n_, -1)
                && (integersq!([Atom::num(2) * &m_, Atom::num(2) * &n_]) || eqq!(&m_ + &n_, 0))
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_sin = &a__ * angle.sin();
            let scaled_cos = &b__ * angle.cos();
            let recursive_integrand = scaled_sin.pow(&m_ - 2) * scaled_cos.pow(&n_ + 2);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(
                    &(-&a__ * scaled_sin.pow(&m_ - 1) * scaled_cos.pow(&n_ + 1)
                        / (&b__ * &f__ * (&n_ + 1))),
                    x_,
                ) + rubi_star(a__.pow(2) * (&m_ - 1) / (b__.pow(2) * (&n_ + 1)), recursive)
        },
    ));
}

fn push_rules_rule_3047(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, n_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 3047,
        source: "Int[(a_.*cos[e_.+f_.*x_])^m_*(b_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
          a*(a*Cos[e+f*x])^(m-1)*(b*Sin[e+f*x])^(n+1)/(b*f*(n+1)) +
          a^2*(m-1)/(b^2*(n+1)) \\[Star] Int[(a*Cos[e+f*x])^(m-2)*(b*Sin[e+f*x])^(n+2),x] /;
        FreeQ[{a,b,e,f},x] && GtQ[m,1] && LtQ[n,-1] && (IntegersQ[2*m,2*n] || EqQ[m+n,0])",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: ["G&R 2.510.1", "G&R 2.510.4"],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, e__, f__, m_, b__, n_, x_],
        optional: [a__, e__, f__, b__],
        when: {
            freeq!([a__, b__, e__, f__], x_)
                && gtq!(m_, 1)
                && ltq!(n_, -1)
                && (integersq!([Atom::num(2) * &m_, Atom::num(2) * &n_]) || eqq!(&m_ + &n_, 0))
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_cos = &a__ * angle.cos();
            let scaled_sin = &b__ * angle.sin();
            let recursive_integrand = scaled_cos.pow(&m_ - 2) * scaled_sin.pow(&n_ + 2);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(
                    &(&a__ * scaled_cos.pow(&m_ - 1) * scaled_sin.pow(&n_ + 1)
                        / (&b__ * &f__ * (&n_ + 1))),
                    x_,
                ) + rubi_star(a__.pow(2) * (&m_ - 1) / (b__.pow(2) * (&n_ + 1)), recursive)
        },
    ));
}

fn push_rules_rule_3048(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, n_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 3048,
        source: "Int[(a_.*sin[e_.+f_.*x_])^m_*(b_.*cos[e_.+f_.*x_])^n_,x_Symbol] :=
          -a*(b*Cos[e+f*x])^(n+1)*(a*Sin[e+f*x])^(m-1)/(b*f*(m+n)) +
          a^2*(m-1)/(m+n) \\[Star] Int[(b*Cos[e+f*x])^n*(a*Sin[e+f*x])^(m-2),x] /;
        FreeQ[{a,b,e,f,n},x] && GtQ[m,1] && NeQ[m+n,0] && IntegersQ[2*m,2*n]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: ["G&R 2.510.2, CRC 323b, A&S 4.3.127b", "G&R 2.510.5, CRC 323a, A&S 4.3.127a"],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, e__, f__, m_, b__, n_, x_],
        optional: [a__, e__, f__, b__],
        when: {
            freeq!([a__, b__, e__, f__, n_], x_)
                && gtq!(m_, 1)
                && neq!(&m_ + &n_, 0)
                && integersq!([Atom::num(2) * &m_, Atom::num(2) * &n_])
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_sin = &a__ * angle.sin();
            let scaled_cos = &b__ * angle.cos();
            let recursive_integrand = scaled_cos.pow(&n_) * scaled_sin.pow(&m_ - 2);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(
                    &(-&a__ * scaled_cos.pow(&n_ + 1) * scaled_sin.pow(&m_ - 1)
                        / (&b__ * &f__ * (&m_ + &n_))),
                    x_,
                ) + rubi_star(a__.pow(2) * (&m_ - 1) / (&m_ + &n_), recursive)
        },
    ));
}

fn push_rules_rule_3049(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, n_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 3049,
        source: "Int[(a_.*cos[e_.+f_.*x_])^m_*(b_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
          a*(b*Sin[e+f*x])^(n+1)*(a*Cos[e+f*x])^(m-1)/(b*f*(m+n)) +
          a^2*(m-1)/(m+n) \\[Star] Int[(b*Sin[e+f*x])^n*(a*Cos[e+f*x])^(m-2),x] /;
        FreeQ[{a,b,e,f,n},x] && GtQ[m,1] && NeQ[m+n,0] && IntegersQ[2*m,2*n]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: ["G&R 2.510.2, CRC 323b, A&S 4.3.127b", "G&R 2.510.5, CRC 323a, A&S 4.3.127a"],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, e__, f__, m_, b__, n_, x_],
        optional: [a__, e__, f__, b__],
        when: {
            freeq!([a__, b__, e__, f__, n_], x_)
                && gtq!(m_, 1)
                && neq!(&m_ + &n_, 0)
                && integersq!([Atom::num(2) * &m_, Atom::num(2) * &n_])
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_cos = &a__ * angle.cos();
            let scaled_sin = &b__ * angle.sin();
            let recursive_integrand = scaled_sin.pow(&n_) * scaled_cos.pow(&m_ - 2);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(
                    &(&a__ * scaled_sin.pow(&n_ + 1) * scaled_cos.pow(&m_ - 1)
                        / (&b__ * &f__ * (&m_ + &n_))),
                    x_,
                ) + rubi_star(a__.pow(2) * (&m_ - 1) / (&m_ + &n_), recursive)
        },
    ));
}

fn push_rules_rule_3050(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, n_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 3050,
        source: "Int[(a_.*sin[e_.+f_.*x_])^m_*(b_.*cos[e_.+f_.*x_])^n_,x_Symbol] :=
          (b*Cos[e+f*x])^(n+1)*(a*Sin[e+f*x])^(m+1)/(a*b*f*(m+1)) +
          (m+n+2)/(a^2*(m+1)) \\[Star] Int[(b*Cos[e+f*x])^n*(a*Sin[e+f*x])^(m+2),x] /;
        FreeQ[{a,b,e,f,n},x] && LtQ[m,-1] && IntegersQ[2*m,2*n]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: ["G&R 2.510.3, CRC 334a, A&S 4.3.128b", "G&R 2.510.6, CRC 334b, A&S 4.3.128a"],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, e__, f__, m_, b__, n_, x_],
        optional: [a__, e__, f__, b__],
        when: {
            freeq!([a__, b__, e__, f__, n_], x_)
                && ltq!(m_, -1)
                && integersq!([Atom::num(2) * &m_, Atom::num(2) * &n_])
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_sin = &a__ * angle.sin();
            let scaled_cos = &b__ * angle.cos();
            let recursive_integrand = scaled_cos.pow(&n_) * scaled_sin.pow(&m_ + 2);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(
                    &(scaled_cos.pow(&n_ + 1) * scaled_sin.pow(&m_ + 1)
                        / (&a__ * &b__ * &f__ * (&m_ + 1))),
                    x_,
                ) + rubi_star(&m_ + &n_ + 2, recursive / (a__.pow(2) * (&m_ + 1)))
        },
    ));
}

fn push_rules_rule_3051(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, n_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 3051,
        source: "Int[(a_.*cos[e_.+f_.*x_])^m_*(b_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
          -(b*Sin[e+f*x])^(n+1)*(a*Cos[e+f*x])^(m+1)/(a*b*f*(m+1)) +
          (m+n+2)/(a^2*(m+1)) \\[Star] Int[(b*Sin[e+f*x])^n*(a*Cos[e+f*x])^(m+2),x] /;
        FreeQ[{a,b,e,f,n},x] && LtQ[m,-1] && IntegersQ[2*m,2*n]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: ["G&R 2.510.3, CRC 334a, A&S 4.3.128b", "G&R 2.510.6, CRC 334b, A&S 4.3.128a"],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, e__, f__, m_, b__, n_, x_],
        optional: [a__, e__, f__, b__],
        when: {
            freeq!([a__, b__, e__, f__, n_], x_)
                && ltq!(m_, -1)
                && integersq!([Atom::num(2) * &m_, Atom::num(2) * &n_])
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_cos = &a__ * angle.cos();
            let scaled_sin = &b__ * angle.sin();
            let recursive_integrand = scaled_sin.pow(&n_) * scaled_cos.pow(&m_ + 2);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(
                    &(-scaled_sin.pow(&n_ + 1) * scaled_cos.pow(&m_ + 1)
                        / (&a__ * &b__ * &f__ * (&m_ + 1))),
                    x_,
                ) + rubi_star(&m_ + &n_ + 2, recursive / (a__.pow(2) * (&m_ + 1)))
        },
    ));
}

fn push_rules_rule_3052(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 3052,
        source: "Int[Sqrt[a_.*sin[e_.+f_.*x_]]*Sqrt[b_.*cos[e_.+f_.*x_]],x_Symbol] :=
          Sqrt[a*Sin[e+f*x]]*Sqrt[b*Cos[e+f*x]]/Sqrt[Sin[2*e+2*f*x]] \\[Star] Int[Sqrt[Sin[2*e+2*f*x]],x] /;
        FreeQ[{a,b,e,f},x]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: (b__ * i_cos(e__ + f__ * x_)).sqrt()
            * (a__ * i_sin(e__ + f__ * x_)).sqrt(),
        with: [a__, b__, e__, f__, x_],
        optional: [a__, b__, e__, f__],
        when: { freeq!([a__, b__, e__, f__], x_) },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let double_angle = Atom::num(2) * &e__ + Atom::num(2) * &f__ * x_;
            let recursive = rubi_rhs_int(&double_angle.sin().sqrt(), x_);
            let coefficient = (&a__ * angle.sin()).sqrt() * (&b__ * angle.cos()).sqrt()
                / double_angle.sin().sqrt();
            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_3053(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 3053,
        source: "Int[1/(Sqrt[a_.*sin[e_.+f_.*x_]]*Sqrt[b_.*cos[e_.+f_.*x_]]),x_Symbol] :=
          Sqrt[Sin[2*e+2*f*x]]/(Sqrt[a*Sin[e+f*x]]*Sqrt[b*Cos[e+f*x]]) \\[Star] Int[1/Sqrt[Sin[2*e+2*f*x]],x] /;
        FreeQ[{a,b,e,f},x]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: Atom::num(1)
            / ((b__ * i_cos(e__ + f__ * x_)).sqrt()
                * (a__ * i_sin(e__ + f__ * x_)).sqrt()),
        with: [a__, b__, e__, f__, x_],
        optional: [a__, b__, e__, f__],
        when: { freeq!([a__, b__, e__, f__], x_) },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let double_angle = Atom::num(2) * &e__ + Atom::num(2) * &f__ * x_;
            let recursive = rubi_rhs_int(&(Atom::num(1) / double_angle.sin().sqrt()), x_);
            let coefficient = double_angle.sin().sqrt()
                / ((&a__ * angle.sin()).sqrt() * (&b__ * angle.cos()).sqrt());
            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_3054(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, n_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 3054,
        source: "Int[(a_.*sin[e_.+f_.*x_])^m_*(b_.*cos[e_.+f_.*x_])^n_,x_Symbol] :=
          With[{k=Denominator[m]},
          k*a*b/f \\[Star] Subst[Int[x^(k*(m+1)-1)/(a^2+b^2*x^(2*k)),x],x,(a*Sin[e+f*x])^(1/k)/(b*Cos[e+f*x])^(1/k)]] /;
        FreeQ[{a,b,e,f},x] && EqQ[m+n,0] && GtQ[m,0] && LtQ[m,1]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, e__, f__, m_, b__, n_, x_],
        optional: [a__, e__, f__, b__],
        when: {
            freeq!([a__, b__, e__, f__], x_)
                && eqq!(&m_ + &n_, 0)
                && gtq!(m_, 0)
                && ltq!(m_, 1)
        },
        rhs: {
            let k = Atom::num(denominator!(m_));
            let subst_guard = fresh_substitution_symbol().unwrap();
            let subst = subst_guard.symbol();
            let z = Atom::var(subst);
            let transformed = z.pow(&k * (&m_ + 1) - 1) / (a__.pow(2) + b__.pow(2) * z.pow(2 * &k));
            let primitive = rubi_rhs_int(&transformed, subst);
            let angle = &e__ + &f__ * x_;
            let replacement = (&a__ * angle.sin()).pow(Atom::num(1) / &k)
                / (&b__ * angle.cos()).pow(Atom::num(1) / &k);

            let substituted = rubi_subst(&primitive, subst, replacement);
            rubi_star(&k * &a__ * &b__ / &f__, substituted)
        },
    ));
}

fn push_rules_rule_3055(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, n_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 3055,
        source: "Int[(a_.*cos[e_.+f_.*x_])^m_*(b_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
          With[{k=Denominator[m]},
          -k*a*b/f \\[Star] Subst[Int[x^(k*(m+1)-1)/(a^2+b^2*x^(2*k)),x],x,(a*Cos[e+f*x])^(1/k)/(b*Sin[e+f*x])^(1/k)]] /;
        FreeQ[{a,b,e,f},x] && EqQ[m+n,0] && GtQ[m,0] && LtQ[m,1]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, e__, f__, m_, b__, n_, x_],
        optional: [a__, e__, f__, b__],
        when: {
            freeq!([a__, b__, e__, f__], x_)
                && eqq!(&m_ + &n_, 0)
                && gtq!(m_, 0)
                && ltq!(m_, 1)
        },
        rhs: {
            let k = Atom::num(denominator!(m_));
            let subst_guard = fresh_substitution_symbol().unwrap();
            let subst = subst_guard.symbol();
            let z = Atom::var(subst);
            let transformed = z.pow(&k * (&m_ + 1) - 1) / (a__.pow(2) + b__.pow(2) * z.pow(2 * &k));
            let primitive = rubi_rhs_int(&transformed, subst);
            let angle = &e__ + &f__ * x_;
            let replacement = (&a__ * angle.cos()).pow(Atom::num(1) / &k)
                / (&b__ * angle.sin()).pow(Atom::num(1) / &k);

            let substituted = rubi_subst(&primitive, subst, replacement);
            rubi_star(-&k * &a__ * &b__ / &f__, substituted)
        },
    ));
}

fn push_rules_rule_3056(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, n_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 3056,
        source: "Int[(a_.*cos[e_.+f_.*x_])^m_*(b_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
          -b^(2*IntPart[(n-1)/2]+1)*(b*Sin[e+f*x])^(2*FracPart[(n-1)/2])*(a*Cos[e+f*x])^(m+1)/(a*f*(m+1)*(Sin[e+f*x]^2)^FracPart[(n-1)/2])*
            Hypergeometric2F1[(1+m)/2,(1-n)/2,(3+m)/2,Cos[e+f*x]^2] /;
        FreeQ[{a,b,e,f,m,n},x] && SimplerQ[n,m]",
        desc: "Piecewise constant extraction and integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, e__, f__, m_, b__, n_, x_],
        optional: [a__, e__, f__, b__],
        when: {
            freeq!([a__, b__, e__, f__, m_, n_], x_) && rubi_simpler_q(&n_, &m_)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let cos = angle.cos();
            let half_n_minus_one = (&n_ - 1) / 2;
            let int_part = rubi_int_part(&half_n_minus_one);
            let frac_part = rubi_frac_part(&half_n_minus_one);
            let hypergeometric = rubi_hypergeometric2f1(
                (&m_ + 1) / 2,
                (Atom::num(1) - &n_) / 2,
                (&m_ + 3) / 2,
                cos.pow(2),
            );

            rubi_simp(
                &(
                -b__.pow(Atom::num(2) * int_part + 1)
                    * (&b__ * &sin).pow(Atom::num(2) * &frac_part)
                    * (&a__ * &cos).pow(&m_ + 1)
                    * hypergeometric
                    / (&a__
                        * &f__
                        * (&m_ + 1)
                        * sin.pow(2).pow(frac_part))
                ),
                x_,
            )
        },
    ));
}

fn push_rules_rule_3057(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, n_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 3057,
        source: "Int[(a_.*sin[e_.+f_.*x_])^m_*(b_.*cos[e_.+f_.*x_])^n_,x_Symbol] :=
          b^(2*IntPart[(n-1)/2]+1)*(b*Cos[e+f*x])^(2*FracPart[(n-1)/2])*(a*Sin[e+f*x])^(m+1)/(a*f*(m+1)*(Cos[e+f*x]^2)^FracPart[(n-1)/2])*
            Hypergeometric2F1[(1+m)/2,(1-n)/2,(3+m)/2,Sin[e+f*x]^2] /;
        FreeQ[{a,b,e,f,m,n},x]",
        desc: "Piecewise constant extraction and integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, e__, f__, m_, b__, n_, x_],
        optional: [a__, e__, f__, b__],
        when: { freeq!([a__, b__, e__, f__, m_, n_], x_) },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let cos = angle.cos();
            let half_n_minus_one = (&n_ - 1) / 2;
            let int_part = rubi_int_part(&half_n_minus_one);
            let frac_part = rubi_frac_part(&half_n_minus_one);
            let hypergeometric = rubi_hypergeometric2f1(
                (&m_ + 1) / 2,
                (Atom::num(1) - &n_) / 2,
                (&m_ + 3) / 2,
                sin.pow(2),
            );

            rubi_simp(
                &(
                b__.pow(Atom::num(2) * int_part + 1)
                    * (&b__ * &cos).pow(Atom::num(2) * &frac_part)
                    * (&a__ * &sin).pow(&m_ + 1)
                    * hypergeometric
                    / (&a__
                        * &f__
                        * (&m_ + 1)
                        * cos.pow(2).pow(frac_part))
                ),
                x_,
            )
        },
    ));
}

fn push_rules_rule_3058(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, n_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 3058,
        source: "Int[(a_.*sin[e_.+f_.*x_])^m_.*(b_.*sec[e_.+f_.*x_])^n_.,x_Symbol] :=
          b*(a*Sin[e+f*x])^(m+1)*(b*Sec[e+f*x])^(n-1)/(a*f*(m+1)) /;
        FreeQ[{a,b,e,f,m,n},x] && EqQ[m-n+2,0] && NeQ[m,-1]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, e__, f__, m_, b__, n_, x_],
        optional: [a__, e__, f__, m_, b__, n_],
        when: {
            freeq!([a__, b__, e__, f__, m_, n_], x_)
                && eqq!(&m_ - &n_ + 2, 0)
                && neq!(m_, -Atom::num(1))
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            rubi_simp(
                &(&b__ * (&a__ * angle.sin()).pow(&m_ + 1)
                    * (&b__ * angle.sec()).pow(&n_ - 1)
                    / (&a__ * &f__ * (&m_ + 1))),
                x_,
            )
        },
    ));
}

fn push_rules_rule_3059(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, n_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 3059,
        source: "Int[(a_.*sin[e_.+f_.*x_])^m_*(b_.*sec[e_.+f_.*x_])^n_,x_Symbol] :=
          a*b*(a*Sin[e+f*x])^(m-1)*(b*Sec[e+f*x])^(n-1)/(f*(n-1)) -
          a^2*b^2*(m-1)/(n-1) \\[Star] Int[(a*Sin[e+f*x])^(m-2)*(b*Sec[e+f*x])^(n-2),x] /;
        FreeQ[{a,b,e,f},x] && GtQ[n,1] && GtQ[m,1] && IntegersQ[2*m,2*n]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, e__, f__, m_, b__, n_, x_],
        optional: [a__, e__, f__, b__],
        when: {
            freeq!([a__, b__, e__, f__], x_)
                && gtq!(n_, 1)
                && gtq!(m_, 1)
                && integerq!(Atom::num(2) * &m_)
                && integerq!(Atom::num(2) * &n_)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_sine = &a__ * angle.sin();
            let scaled_secant = &b__ * angle.sec();
            let recursive_integrand =
                scaled_sine.pow(&m_ - 2) * scaled_secant.pow(&n_ - 2);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(
                    &(&a__ * &b__ * scaled_sine.pow(&m_ - 1) * scaled_secant.pow(&n_ - 1)
                        / (&f__ * (&n_ - 1))),
                    x_,
                ) - rubi_star(a__.pow(2) * b__.pow(2) * (&m_ - 1) / (&n_ - 1), recursive)
        },
    ));
}

fn push_rules_rule_3060(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, n_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 3060,
        source: "Int[(a_.*sin[e_.+f_.*x_])^m_*(b_.*sec[e_.+f_.*x_])^n_,x_Symbol] :=
          (a*Sin[e+f*x])^(m+1)*(b*Sec[e+f*x])^(n+1)/(a*b*f*(m-n)) -
          (n+1)/(b^2*(m-n)) \\[Star] Int[(a*Sin[e+f*x])^m*(b*Sec[e+f*x])^(n+2),x] /;
        FreeQ[{a,b,e,f,m},x] && GtQ[n,1] && IntegersQ[2*m,2*n]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, e__, f__, m_, b__, n_, x_],
        optional: [a__, e__, f__, b__],
        when: {
            freeq!([a__, b__, e__, f__, m_], x_)
                && gtq!(n_, 1)
                && integerq!(Atom::num(2) * &m_)
                && integerq!(Atom::num(2) * &n_)
                && neq!(&m_ - &n_, 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_sine = &a__ * angle.sin();
            let scaled_secant = &b__ * angle.sec();
            let recursive_integrand = scaled_sine.pow(&m_) * scaled_secant.pow(&n_ + 2);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(
                    &(scaled_sine.pow(&m_ + 1) * scaled_secant.pow(&n_ + 1)
                        / (&a__ * &b__ * &f__ * (&m_ - &n_))),
                    x_,
                ) - rubi_star(&n_ + 1, recursive / (b__.pow(2) * (&m_ - &n_)))
        },
    ));
}

fn push_rules_rule_3061(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, n_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 3061,
        source: "Int[(a_.*sin[e_.+f_.*x_])^m_*(b_.*sec[e_.+f_.*x_])^n_,x_Symbol] :=
          (a*Sin[e+f*x])^(m+1)*(b*Sec[e+f*x])^(n+1)/(a*b*f*(m+1)) -
          (n+1)/(a^2*b^2*(m+1)) \\[Star] Int[(a*Sin[e+f*x])^(m+2)*(b*Sec[e+f*x])^(n+2),x] /;
        FreeQ[{a,b,e,f},x] && LtQ[n,-1] && LtQ[m,-1] && IntegersQ[2*m,2*n]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, e__, f__, m_, b__, n_, x_],
        optional: [a__, e__, f__, b__],
        when: {
            freeq!([a__, b__, e__, f__], x_)
                && ltq!(n_, -1)
                && ltq!(m_, -1)
                && integerq!(Atom::num(2) * &m_)
                && integerq!(Atom::num(2) * &n_)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_sine = &a__ * angle.sin();
            let scaled_secant = &b__ * angle.sec();
            let recursive_integrand =
                scaled_sine.pow(&m_ + 2) * scaled_secant.pow(&n_ + 2);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(
                    &(scaled_sine.pow(&m_ + 1) * scaled_secant.pow(&n_ + 1)
                        / (&a__ * &b__ * &f__ * (&m_ + 1))),
                    x_,
                ) - rubi_star(&n_ + 1, recursive
                        / (a__.pow(2) * b__.pow(2) * (&m_ + 1)))
        },
    ));
}

fn push_rules_rule_3062(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, n_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 3062,
        source: "Int[(a_.*sin[e_.+f_.*x_])^m_*(b_.*sec[e_.+f_.*x_])^n_,x_Symbol] :=
          (a*Sin[e+f*x])^(m+1)*(b*Sec[e+f*x])^(n+1)/(a*b*f*(m-n)) -
          (n+1)/(b^2*(m-n)) \\[Star] Int[(a*Sin[e+f*x])^m*(b*Sec[e+f*x])^(n+2),x] /;
        FreeQ[{a,b,e,f,m},x] && LtQ[n,-1] && NeQ[m-n,0] && IntegersQ[2*m,2*n]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, e__, f__, m_, b__, n_, x_],
        optional: [a__, e__, f__, b__],
        when: {
            freeq!([a__, b__, e__, f__, m_], x_)
                && ltq!(n_, -1)
                && neq!(&m_ - &n_, 0)
                && integerq!(Atom::num(2) * &m_)
                && integerq!(Atom::num(2) * &n_)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_sine = &a__ * angle.sin();
            let scaled_secant = &b__ * angle.sec();
            let recursive_integrand = scaled_sine.pow(&m_) * scaled_secant.pow(&n_ + 2);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(
                    &(scaled_sine.pow(&m_ + 1) * scaled_secant.pow(&n_ + 1)
                        / (&a__ * &b__ * &f__ * (&m_ - &n_))),
                    x_,
                ) - rubi_star(&n_ + 1, recursive / (b__.pow(2) * (&m_ - &n_)))
        },
    ));
}

fn push_rules_rule_3063(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, n_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 3063,
        source: "Int[(a_.*sin[e_.+f_.*x_])^m_*(b_.*sec[e_.+f_.*x_])^n_,x_Symbol] :=
          -a*b*(a*Sin[e+f*x])^(m-1)*(b*Sec[e+f*x])^(n-1)/(f*(m-n)) +
          a^2*(m-1)/(m-n) \\[Star] Int[(a*Sin[e+f*x])^(m-2)*(b*Sec[e+f*x])^n,x] /;
        FreeQ[{a,b,e,f,n},x] && GtQ[m,1] && NeQ[m-n,0] && IntegersQ[2*m,2*n]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, e__, f__, m_, b__, n_, x_],
        optional: [a__, e__, f__, b__],
        when: {
            freeq!([a__, b__, e__, f__, n_], x_)
                && gtq!(m_, 1)
                && neq!(&m_ - &n_, 0)
                && integerq!(Atom::num(2) * &m_)
                && integerq!(Atom::num(2) * &n_)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_sine = &a__ * angle.sin();
            let scaled_secant = &b__ * angle.sec();
            let recursive_integrand = scaled_sine.pow(&m_ - 2) * scaled_secant.pow(&n_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(
                    &(-&a__ * &b__ * scaled_sine.pow(&m_ - 1) * scaled_secant.pow(&n_ - 1)
                        / (&f__ * (&m_ - &n_))),
                    x_,
                ) + rubi_star(a__.pow(2) * (&m_ - 1) / (&m_ - &n_), recursive)
        },
    ));
}

fn push_rules_rule_3064(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, n_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 3064,
        source: "Int[(a_.*sin[e_.+f_.*x_])^m_*(b_.*sec[e_.+f_.*x_])^n_,x_Symbol] :=
          b*(a*Sin[e+f*x])^(m+1)*(b*Sec[e+f*x])^(n-1)/(a*f*(m+1)) +
          (m-n+2)/(a^2*(m+1)) \\[Star] Int[(a*Sin[e+f*x])^(m+2)*(b*Sec[e+f*x])^n,x] /;
        FreeQ[{a,b,e,f,n},x] && LtQ[m,-1] && IntegersQ[2*m,2*n]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, e__, f__, m_, b__, n_, x_],
        optional: [a__, e__, f__, b__],
        when: {
            freeq!([a__, b__, e__, f__, n_], x_)
                && ltq!(m_, -1)
                && integerq!(Atom::num(2) * &m_)
                && integerq!(Atom::num(2) * &n_)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_sine = &a__ * angle.sin();
            let scaled_secant = &b__ * angle.sec();
            let recursive_integrand = scaled_sine.pow(&m_ + 2) * scaled_secant.pow(&n_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(
                    &(&b__ * scaled_sine.pow(&m_ + 1) * scaled_secant.pow(&n_ - 1)
                        / (&a__ * &f__ * (&m_ + 1))),
                    x_,
                ) + rubi_star((&m_ - &n_ + 2) / (a__.pow(2) * (&m_ + 1)), recursive)
        },
    ));
}

fn push_rules_rule_3065(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, n_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 3065,
        source: "Int[(a_.*sin[e_.+f_.*x_])^m_*(b_.*sec[e_.+f_.*x_])^n_,x_Symbol] :=
          (b*Cos[e+f*x])^n*(b*Sec[e+f*x])^n \\[Star] Int[(a*Sin[e+f*x])^m/(b*Cos[e+f*x])^n,x] /;
        FreeQ[{a,b,e,f,m,n},x] && IntegerQ[m-1/2] && IntegerQ[n-1/2]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, e__, f__, m_, b__, n_, x_],
        optional: [a__, e__, f__, b__],
        when: {
            freeq!([a__, b__, e__, f__, m_, n_], x_)
                && integerq!(&m_ - &(Atom::num(1) / 2))
                && integerq!(&n_ - &(Atom::num(1) / 2))
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_cosine = &b__ * angle.cos();
            let scaled_secant = &b__ * angle.sec();
            let transformed_integrand =
                (&a__ * angle.sin()).pow(&m_) / scaled_cosine.pow(&n_);
            let recursive = rubi_rhs_int(&transformed_integrand, x_);

            rubi_star(scaled_cosine.pow(&n_) * scaled_secant.pow(&n_), recursive)
        },
    ));
}

fn push_rules_rule_3066(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, n_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 3066,
        source: "Int[(a_.*sin[e_.+f_.*x_])^m_*(b_.*sec[e_.+f_.*x_])^n_,x_Symbol] :=
          1/b^2*(b*Cos[e+f*x])^(n+1)*(b*Sec[e+f*x])^(n+1) \\[Star] Int[(a*Sin[e+f*x])^m/(b*Cos[e+f*x])^n,x] /;
        FreeQ[{a,b,e,f,m,n},x] && Not[IntegerQ[m]] && Not[IntegerQ[n]] && LtQ[n,1]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, e__, f__, m_, b__, n_, x_],
        optional: [a__, e__, f__, b__],
        when: {
            freeq!([a__, b__, e__, f__, m_, n_], x_)
                && !integerq!(m_)
                && !integerq!(n_)
                && ltq!(n_, 1)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_cosine = &b__ * angle.cos();
            let scaled_secant = &b__ * angle.sec();
            let transformed_integrand =
                (&a__ * angle.sin()).pow(&m_) / scaled_cosine.pow(&n_);
            let recursive = rubi_rhs_int(&transformed_integrand, x_);

            rubi_star(scaled_cosine.pow(&n_ + 1) * scaled_secant.pow(&n_ + 1) / b__.pow(2), recursive)
        },
    ));
}

fn push_rules_rule_3067(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, n_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 3067,
        source: "Int[(a_.*sin[e_.+f_.*x_])^m_*(b_.*sec[e_.+f_.*x_])^n_,x_Symbol] :=
          b^2*(b*Cos[e+f*x])^(n-1)*(b*Sec[e+f*x])^(n-1) \\[Star] Int[(a*Sin[e+f*x])^m/(b*Cos[e+f*x])^n,x] /;
        FreeQ[{a,b,e,f,m,n},x] && Not[IntegerQ[m]] && Not[IntegerQ[n]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, e__, f__, m_, b__, n_, x_],
        optional: [a__, e__, f__, b__],
        when: {
            freeq!([a__, b__, e__, f__, m_, n_], x_)
                && !integerq!(m_)
                && !integerq!(n_)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_cos = &b__ * angle.cos();
            let scaled_sec = &b__ * angle.sec();
            let recursive_integrand = (&a__ * angle.sin()).pow(&m_) / scaled_cos.pow(&n_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(b__.pow(2) * scaled_cos.pow(&n_ - 1) * scaled_sec.pow(&n_ - 1), recursive)
        },
    ));
}

fn push_rules_rule_3068(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, m_, n_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 3068,
        source: "Int[(a_.*sin[e_.+f_.*x_])^m_.*(b_.*csc[e_.+f_.*x_])^n_,x_Symbol] :=
          (a*b)^IntPart[n]*(a*Sin[e+f*x])^FracPart[n]*(b*Csc[e+f*x])^FracPart[n] \\[Star] Int[(a*Sin[e+f*x])^(m-n),x] /;
        FreeQ[{a,b,e,f,m,n},x] && Not[IntegerQ[m]] && Not[IntegerQ[n]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: (a__ * i_sin(e__ + f__ * x_)).pow(m_)
            * (b__ * i_csc(e__ + f__ * x_)).pow(n_),
        with: [a__, e__, f__, m_, b__, n_, x_],
        optional: [a__, e__, f__, m_, b__],
        when: {
            freeq!([a__, b__, e__, f__, m_, n_], x_)
                && !integerq!(m_)
                && !integerq!(n_)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_sin = &a__ * angle.sin();
            let scaled_csc = &b__ * angle.csc();
            let recursive_integrand = scaled_sin.pow(&m_ - &n_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star((&a__ * &b__).pow(rubi_int_part(&n_)) * scaled_sin.pow(rubi_frac_part(&n_)) * scaled_csc.pow(rubi_frac_part(&n_)), recursive)
        },
    ));
}

fn push_rules_rule_3069(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, n_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 3069,
        source: "Int[(a_.*sin[e_.+f_.*x_])^m_*(b_.*tan[e_.+f_.*x_])^n_,x_Symbol]:=
          -b*(a*Sin[e+f*x])^m*(b*Tan[e+f*x])^(n-1)/(f*m) /;
        FreeQ[{a,b,e,f,m,n},x] && EqQ[m+n-1,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [a__, e__, f__, m_, b__, n_, x_],
        optional: [a__, e__, f__, b__],
        when: {
            freeq!([a__, b__, e__, f__, m_, n_], x_)
                && eqq!(&m_ + &n_ - 1, 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;

            rubi_simp(
                &(-&b__
                    * (&a__ * angle.sin()).pow(&m_)
                    * (&b__ * angle.tan()).pow(&n_ - 1)
                    / (&f__ * &m_)),
                x_,
            )
        },
    ));
}

fn push_rules_rule_3070(rules: &mut Vec<RubiRule>) {
    rubi_symb!(m_, n_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 3070,
        source: "Int[sin[e_.+f_.*x_]^m_.*tan[e_.+f_.*x_]^n_.,x_Symbol] :=
          -1/f \\[Star] Subst[Int[(1-x^2)^((m+n-1)/2)/x^n,x],x,Cos[e+f*x]] /;
        FreeQ[{e,f},x] && IntegersQ[m,n,(m+n-1)/2]",
        desc: "Integration by substitution",
        refs: [],
        pattern: i_sin(e__ + f__ * x_).pow(m_) * i_tan(e__ + f__ * x_).pow(n_),
        with: [e__, f__, m_, n_, x_],
        optional: [e__, f__, m_, n_],
        when: {
            freeq!([e__, f__], x_) && integersq!([m_, n_, (&m_ + &n_ - 1) / 2])
        },
        rhs: {
            let subst_guard = fresh_substitution_symbol().unwrap();
            let subst = subst_guard.symbol();
            let z = Atom::var(subst);
            let transformed = (Atom::num(1) - z.pow(2)).pow((&m_ + &n_ - 1) / 2) / z.pow(&n_);
            let primitive = rubi_rhs_int(&transformed, subst);
            let angle = &e__ + &f__ * x_;

            let substituted = rubi_subst(&primitive, subst, angle.cos());
            rubi_star(-(Atom::num(1) / &f__), substituted)
        },
    ));
}

fn push_rules_rule_3071(rules: &mut Vec<RubiRule>) {
    rubi_symb!(b__, m_, n_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 3071,
        source: "Int[sin[e_.+f_.*x_]^m_*(b_.*tan[e_.+f_.*x_])^n_.,x_Symbol] :=
          With[{ff=FreeFactors[Tan[e+f*x],x]},
          b*ff/f \\[Star] Subst[Int[(ff*x)^(m+n)/(b^2+ff^2*x^2)^(m/2+1),x],x,b*Tan[e+f*x]/ff]] /;
        FreeQ[{b,e,f,n},x] && IntegerQ[m/2]",
        desc: "Integration by substitution",
        refs: [],
        pattern: i_sin(e__ + f__ * x_).pow(m_) * (b__ * i_tan(e__ + f__ * x_)).pow(n_),
        with: [e__, f__, m_, b__, n_, x_],
        optional: [e__, f__, b__, n_],
        when: {
            freeq!([b__, e__, f__, n_], x_) && integerq!(&m_ / 2)
        },
        rhs: {
            let subst_guard = fresh_substitution_symbol().unwrap();
            let subst = subst_guard.symbol();
            let z = Atom::var(subst);
            let angle = &e__ + &f__ * x_;
            let ff = rubi_free_factors(&angle.tan(), x_);
            let transformed = (&ff * &z).pow(&m_ + &n_)
                / (b__.pow(2) + ff.pow(2) * z.pow(2)).pow(&m_ / 2 + 1);
            let primitive = rubi_rhs_int(&transformed, subst);
            let replacement = &b__ * angle.tan() / &ff;

            let substituted = rubi_subst(&primitive, subst, replacement);
            rubi_star(&b__ * &ff / &f__, substituted)
        },
    ));
}

fn push_rules_rule_3072(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, m_, n_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 3072,
        source: "Int[(a_.*sin[e_.+f_.*x_])^m_.*tan[e_.+f_.*x_]^n_.,x_Symbol] :=
          With[{ff=FreeFactors[Sin[e+f*x],x]},
          ff/f \\[Star] Subst[Int[(ff*x)^(m+n)/(a^2-ff^2*x^2)^((n+1)/2),x],x,a*Sin[e+f*x]/ff]] /;
        FreeQ[{a,e,f,m},x] && IntegerQ[(n+1)/2]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [a__, e__, f__, m_, n_, x_],
        optional: [a__, e__, f__, m_, n_],
        when: {
            freeq!([a__, e__, f__, m_], x_) && integerq!((&n_ + 1) / 2)
        },
        rhs: {
            let subst_guard = fresh_substitution_symbol().unwrap();
            let subst = subst_guard.symbol();
            let z = Atom::var(subst);
            let angle = &e__ + &f__ * x_;
            let ff = rubi_free_factors(&angle.sin(), x_);
            let transformed = (&ff * &z).pow(&m_ + &n_)
                / (a__.pow(2) - ff.pow(2) * z.pow(2)).pow((&n_ + 1) / 2);
            let primitive = rubi_rhs_int(&transformed, subst);
            let replacement = &a__ * angle.sin() / &ff;

            let substituted = rubi_subst(&primitive, subst, replacement);
            rubi_star(&ff / &f__, substituted)
        },
    ));
}

fn push_rules_rule_3073(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, n_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 3073,
        source: "Int[(a_.*sin[e_.+f_.*x_])^m_*(b_.*tan[e_.+f_.*x_])^n_,x_Symbol] :=
          b*(a*Sin[e+f*x])^(m+2)*(b*Tan[e+f*x])^(n-1)/(a^2*f*(n-1)) -
          b^2*(m+2)/(a^2*(n-1)) \\[Star] Int[(a*Sin[e+f*x])^(m+2)*(b*Tan[e+f*x])^(n-2),x] /;
        FreeQ[{a,b,e,f},x] && GtQ[n,1] && (LtQ[m,-1] || EqQ[m,-1] && EqQ[n,3/2]) && IntegersQ[2*m,2*n]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: ["G&R 2.510.6, CRC 334b", "G&R 2.510.3, CRC 334a"],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [a__, e__, f__, m_, b__, n_, x_],
        optional: [a__, e__, f__, b__],
        when: {
            freeq!([a__, b__, e__, f__], x_)
                && gtq!(n_, 1)
                && (ltq!(m_, -1) || eqq!(&m_ + 1, 0) && eqq!(n_, Atom::num(3) / Atom::num(2)))
                && integersq!([Atom::num(2) * &m_, Atom::num(2) * &n_])
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_sin = &a__ * angle.sin();
            let scaled_tan = &b__ * angle.tan();
            let recursive_integrand = scaled_sin.pow(&m_ + 2) * scaled_tan.pow(&n_ - 2);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(
                    &(&b__ * scaled_sin.pow(&m_ + 2) * scaled_tan.pow(&n_ - 1)
                        / (a__.pow(2) * &f__ * (&n_ - 1))),
                    x_,
                ) - rubi_star(b__.pow(2) * (&m_ + 2) / (a__.pow(2) * (&n_ - 1)), recursive)
        },
    ));
}

fn push_rules_rule_3074(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, n_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 3074,
        source: "Int[(a_.*sin[e_.+f_.*x_])^m_.*(b_.*tan[e_.+f_.*x_])^n_,x_Symbol] :=
          b*(a*Sin[e+f*x])^m*(b*Tan[e+f*x])^(n-1)/(f*(n-1)) -
          b^2*(m+n-1)/(n-1) \\[Star] Int[(a*Sin[e+f*x])^m*(b*Tan[e+f*x])^(n-2),x] /;
        FreeQ[{a,b,e,f,m},x] && GtQ[n,1] && IntegersQ[2*m,2*n] && Not[GtQ[m,1] && Not[IntegerQ[(m-1)/2]]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [a__, e__, f__, m_, b__, n_, x_],
        optional: [a__, e__, f__, m_, b__],
        when: {
            freeq!([a__, b__, e__, f__, m_], x_)
                && gtq!(n_, 1)
                && integersq!([Atom::num(2) * &m_, Atom::num(2) * &n_])
                && !(gtq!(m_, 1) && !integerq!((&m_ - 1) / 2))
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_sin = &a__ * angle.sin();
            let scaled_tan = &b__ * angle.tan();
            let recursive_integrand = scaled_sin.pow(&m_) * scaled_tan.pow(&n_ - 2);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(
                    &(&b__ * scaled_sin.pow(&m_) * scaled_tan.pow(&n_ - 1)
                        / (&f__ * (&n_ - 1))),
                    x_,
                ) - rubi_star(b__.pow(2) * (&m_ + &n_ - 1) / (&n_ - 1), recursive)
        },
    ));
}

fn push_rules_rule_3075(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 3075,
        source: "Int[Sqrt[a_.*sin[e_.+f_.*x_]]/(b_.*tan[e_.+f_.*x_])^(3/2),x_Symbol]:=
          2*Sqrt[a*Sin[e+f*x]]/(b*f*Sqrt[b*Tan[e+f*x]]) + a^2/b^2 \\[Star] Int[Sqrt[b*Tan[e+f*x]]/(a*Sin[e+f*x])^(3/2),x] /;
        FreeQ[{a,b,e,f},x]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern: (a__ * i_sin(e__ + f__ * x_)).sqrt()
            / (b__ * i_tan(e__ + f__ * x_)).pow(Atom::num(3) / Atom::num(2)),
        with: [a__, e__, f__, b__, x_],
        optional: [a__, e__, f__, b__],
        when: { freeq!([a__, b__, e__, f__], x_) },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_sin = &a__ * angle.sin();
            let scaled_tan = &b__ * angle.tan();
            let recursive_integrand = scaled_tan.sqrt() / scaled_sin.pow(Atom::num(3) / Atom::num(2));
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(
                    &(Atom::num(2) * scaled_sin.sqrt()
                        / (&b__ * &f__ * scaled_tan.sqrt())),
                    x_,
                ) + rubi_star(a__.pow(2) / b__.pow(2), recursive)
        },
    ));
}

fn push_rules_rule_3076(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, n_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 3076,
        source: "Int[(a_.*sin[e_.+f_.*x_])^m_*(b_.*tan[e_.+f_.*x_])^n_,x_Symbol] :=
          (a*Sin[e+f*x])^m*(b*Tan[e+f*x])^(n+1)/(b*f*m) -
          a^2*(n+1)/(b^2*m) \\[Star] Int[(a*Sin[e+f*x])^(m-2)*(b*Tan[e+f*x])^(n+2),x] /;
        FreeQ[{a,b,e,f},x] && LtQ[n,-1] && GtQ[m,1] && IntegersQ[2*m,2*n]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: ["G&R 2.510.5, CRC 323a", "G&R 2.510.2, CRC 323b"],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [a__, e__, f__, m_, b__, n_, x_],
        optional: [a__, e__, f__, b__],
        when: {
            freeq!([a__, b__, e__, f__], x_)
                && ltq!(n_, -1)
                && gtq!(m_, 1)
                && integersq!([Atom::num(2) * &m_, Atom::num(2) * &n_])
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_sin = &a__ * angle.sin();
            let scaled_tan = &b__ * angle.tan();
            let recursive_integrand = scaled_sin.pow(&m_ - 2) * scaled_tan.pow(&n_ + 2);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(
                    &(scaled_sin.pow(&m_) * scaled_tan.pow(&n_ + 1)
                        / (&b__ * &f__ * &m_)),
                    x_,
                ) - rubi_star(a__.pow(2) * (&n_ + 1) / (b__.pow(2) * &m_), recursive)
        },
    ));
}

fn push_rules_rule_3077(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, n_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 3077,
        source: "Int[(a_.*sin[e_.+f_.*x_])^m_.*(b_.*tan[e_.+f_.*x_])^n_,x_Symbol]:=
          (a*Sin[e+f*x])^m*(b*Tan[e+f*x])^(n+1)/(b*f*(m+n+1)) -
          (n+1)/(b^2*(m+n+1)) \\[Star] Int[(a*Sin[e+f*x])^m*(b*Tan[e+f*x])^(n+2),x] /;
        FreeQ[{a,b,e,f,m},x] && LtQ[n,-1] && NeQ[m+n+1,0] && IntegersQ[2*m,2*n] && Not[EqQ[n,-3/2] && EqQ[m,1]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [a__, e__, f__, m_, b__, n_, x_],
        optional: [a__, e__, f__, m_, b__],
        when: {
            freeq!([a__, b__, e__, f__, m_], x_)
                && ltq!(n_, -1)
                && neq!(&m_ + &n_ + 1, 0)
                && integersq!([Atom::num(2) * &m_, Atom::num(2) * &n_])
                && !(eqq!(n_, -Atom::num(3) / Atom::num(2)) && eqq!(m_, 1))
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_sin = &a__ * angle.sin();
            let scaled_tan = &b__ * angle.tan();
            let recursive_integrand = scaled_sin.pow(&m_) * scaled_tan.pow(&n_ + 2);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(
                    &(scaled_sin.pow(&m_) * scaled_tan.pow(&n_ + 1)
                        / (&b__ * &f__ * (&m_ + &n_ + 1))),
                    x_,
                ) - rubi_star((&n_ + 1) / (b__.pow(2) * (&m_ + &n_ + 1)), recursive)
        },
    ));
}

fn push_rules_rule_3078(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, n_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 3078,
        source: "Int[(a_.*sin[e_.+f_.*x_])^m_.*(b_.*tan[e_.+f_.*x_])^n_.,x_Symbol]:=
          -b*(a*Sin[e+f*x])^m*(b*Tan[e+f*x])^(n-1)/(f*m) +
          a^2*(m+n-1)/m \\[Star] Int[(a*Sin[e+f*x])^(m-2)*(b*Tan[e+f*x])^n,x] /;
        FreeQ[{a,b,e,f,n},x] && (GtQ[m,1] || EqQ[m,1] && EqQ[n,1/2]) && IntegersQ[2*m,2*n]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: ["G&R 2.510.2, CRC 323b", "G&R 2.510.5, CRC 323a"],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [a__, e__, f__, m_, b__, n_, x_],
        optional: [a__, e__, f__, m_, b__, n_],
        when: {
            freeq!([a__, b__, e__, f__, n_], x_)
                && (gtq!(m_, 1) || eqq!(m_, 1) && eqq!(n_, Atom::num(1) / Atom::num(2)))
                && integersq!([Atom::num(2) * &m_, Atom::num(2) * &n_])
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_sin = &a__ * angle.sin();
            let scaled_tan = &b__ * angle.tan();
            let recursive_integrand = scaled_sin.pow(&m_ - 2) * scaled_tan.pow(&n_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(
                    &(-&b__ * scaled_sin.pow(&m_) * scaled_tan.pow(&n_ - 1)
                        / (&f__ * &m_)),
                    x_,
                ) + rubi_star(a__.pow(2) * (&m_ + &n_ - 1) / &m_, recursive)
        },
    ));
}

fn push_rules_rule_3079(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, n_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 3079,
        source: "Int[(a_.*sin[e_.+f_.*x_])^m_*(b_.*tan[e_.+f_.*x_])^n_.,x_Symbol]:=
          b*(a*Sin[e+f*x])^(m+2)*(b*Tan[e+f*x])^(n-1)/(a^2*f*(m+n+1)) +
          (m+2)/(a^2*(m+n+1)) \\[Star] Int[(a*Sin[e+f*x])^(m+2)*(b*Tan[e+f*x])^n,x] /;
        FreeQ[{a,b,e,f,n},x] && LtQ[m,-1] && NeQ[m+n+1,0] && IntegersQ[2*m,2*n]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: ["G&R 2.510.3, CRC 334a", "G&R 2.510.6, CRC 334b"],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [a__, e__, f__, m_, b__, n_, x_],
        optional: [a__, e__, f__, b__, n_],
        when: {
            freeq!([a__, b__, e__, f__, n_], x_)
                && ltq!(m_, -1)
                && neq!(&m_ + &n_ + 1, 0)
                && integersq!([Atom::num(2) * &m_, Atom::num(2) * &n_])
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_sin = &a__ * angle.sin();
            let scaled_tan = &b__ * angle.tan();
            let recursive_integrand = scaled_sin.pow(&m_ + 2) * scaled_tan.pow(&n_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(
                    &(&b__ * scaled_sin.pow(&m_ + 2) * scaled_tan.pow(&n_ - 1)
                        / (a__.pow(2) * &f__ * (&m_ + &n_ + 1))),
                    x_,
                ) + rubi_star((&m_ + 2) / (a__.pow(2) * (&m_ + &n_ + 1)), recursive)
        },
    ));
}

fn push_rules_rule_3080(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, m_, n_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 3080,
        source: "Int[(a_.*sin[e_.+f_.*x_])^m_*tan[e_.+f_.*x_]^n_,x_Symbol]:=
          1/a^n \\[Star] Int[(a*Sin[e+f*x])^(m+n)/Cos[e+f*x]^n,x] /;
        FreeQ[{a,e,f,m},x] && IntegerQ[n] && Not[IntegerQ[m]]",
        desc: "Algebraic normalization",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [a__, e__, f__, m_, n_, x_],
        optional: [a__, e__, f__],
        when: {
            freeq!([a__, e__, f__, m_], x_)
                && integerq!(n_)
                && !integerq!(m_)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_sin = &a__ * angle.sin();
            let recursive_integrand = scaled_sin.pow(&m_ + &n_) / angle.cos().pow(&n_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(Atom::num(1) / a__.pow(&n_), recursive)
        },
    ));
}

fn push_rules_rule_3081(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, n_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 3081,
        source: "Int[(a_.*sin[e_.+f_.*x_])^m_.*(b_.*tan[e_.+f_.*x_])^n_,x_Symbol]:=
          Cos[e+f*x]^n*(b*Tan[e+f*x])^n/(a*Sin[e+f*x])^n \\[Star] Int[(a*Sin[e+f*x])^(m+n)/Cos[e+f*x]^n,x] /;
        FreeQ[{a,b,e,f,m,n},x] && Not[IntegerQ[n]] && (ILtQ[m,0] || EqQ[m,1] && EqQ[n,-1/2] || IntegersQ[m-1/2,n-1/2])",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [a__, e__, f__, m_, b__, n_, x_],
        optional: [a__, e__, f__, m_, b__],
        when: {
            freeq!([a__, b__, e__, f__, m_, n_], x_)
                && !integerq!(n_)
                && (iltq!(m_, 0)
                    || eqq!(m_, 1) && eqq!(n_, -Atom::num(1) / Atom::num(2))
                    || integersq!([&m_ - Atom::num(1) / Atom::num(2), &n_ - Atom::num(1) / Atom::num(2)]))
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let cos = angle.cos();
            let scaled_sin = &a__ * angle.sin();
            let scaled_tan = &b__ * angle.tan();
            let recursive_integrand = scaled_sin.pow(&m_ + &n_) / cos.pow(&n_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(cos.pow(&n_) * scaled_tan.pow(&n_) / scaled_sin.pow(&n_), recursive)
        },
    ));
}

fn push_rules_rule_3082(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, n_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 3082,
        source: "Int[(a_.*sin[e_.+f_.*x_])^m_.*(b_.*tan[e_.+f_.*x_])^n_,x_Symbol]:=
          a*Cos[e+f*x]^(n+1)*(b*Tan[e+f*x])^(n+1)/(b*(a*Sin[e+f*x])^(n+1)) \\[Star] Int[(a*Sin[e+f*x])^(m+n)/Cos[e+f*x]^n,x] /;
        FreeQ[{a,b,e,f,m,n},x] && Not[IntegerQ[n]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [a__, e__, f__, m_, b__, n_, x_],
        optional: [a__, e__, f__, m_, b__],
        when: { freeq!([a__, b__, e__, f__, m_, n_], x_) && !integerq!(n_) },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let cos = angle.cos();
            let scaled_sin = &a__ * angle.sin();
            let scaled_tan = &b__ * angle.tan();
            let recursive_integrand = scaled_sin.pow(&m_ + &n_) / cos.pow(&n_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(&a__ * cos.pow(&n_ + 1) * scaled_tan.pow(&n_ + 1) / (&b__ * scaled_sin.pow(&n_ + 1)), recursive)
        },
    ));
}

fn push_rules_rule_3083(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, m_, n_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 3083,
        source: "Int[(a_.*cos[e_.+f_.*x_])^m_*(b_.*tan[e_.+f_.*x_])^n_,x_Symbol] :=
          (a*Cos[e+f*x])^FracPart[m]*(Sec[e+f*x]/a)^FracPart[m] \\[Star] Int[(b*Tan[e+f*x])^n/(Sec[e+f*x]/a)^m,x] /;
        FreeQ[{a,b,e,f,m,n},x] && Not[IntegerQ[m]] && Not[IntegerQ[n]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: (a__ * i_cos(e__ + f__ * x_)).pow(m_)
            * (b__ * i_tan(e__ + f__ * x_)).pow(n_),
        with: [a__, e__, f__, m_, b__, n_, x_],
        optional: [a__, e__, f__, b__],
        when: {
            freeq!([a__, b__, e__, f__, m_, n_], x_)
                && !integerq!(m_)
                && !integerq!(n_)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_cos = &a__ * angle.cos();
            let scaled_tan = &b__ * angle.tan();
            let sec_over_a = angle.sec() / &a__;
            let frac_m = rubi_frac_part(&m_);
            let recursive_integrand = scaled_tan.pow(&n_) / sec_over_a.pow(&m_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(scaled_cos.pow(&frac_m) * sec_over_a.pow(frac_m), recursive)
        },
    ));
}

fn push_rules_rule_3084(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, m_, n_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 3084,
        source: "Int[(a_.*cot[e_.+f_.*x_])^m_*(b_.*tan[e_.+f_.*x_])^n_,x_Symbol] :=
          (a*Cot[e+f*x])^m*(b*Tan[e+f*x])^m \\[Star] Int[(b*Tan[e+f*x])^(n-m),x] /;
        FreeQ[{a,b,e,f,m,n},x] && Not[IntegerQ[m]] && Not[IntegerQ[n]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: (a__ * i_cot(e__ + f__ * x_)).pow(m_)
            * (b__ * i_tan(e__ + f__ * x_)).pow(n_),
        with: [a__, e__, f__, m_, b__, n_, x_],
        optional: [a__, e__, f__, b__],
        when: {
            freeq!([a__, b__, e__, f__, m_, n_], x_)
                && !integerq!(m_)
                && !integerq!(n_)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_cot = &a__ * angle.cot();
            let scaled_tan = &b__ * angle.tan();
            let recursive_integrand = scaled_tan.pow(&n_ - &m_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(scaled_cot.pow(&m_) * scaled_tan.pow(&m_), recursive)
        },
    ));
}

fn push_rules_rule_3085(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, n_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 3085,
        source: "Int[(a_.*sec[e_.+f_.*x_])^m_.*(b_.*tan[e_.+f_.*x_])^n_.,x_Symbol] :=
          -(a*Sec[e+f*x])^m*(b*Tan[e+f*x])^(n+1)/(b*f*m) /;
        FreeQ[{a,b,e,f,m,n},x] && EqQ[m+n+1,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, e__, f__, m_, b__, n_, x_],
        optional: [a__, e__, f__, m_, b__, n_],
        when: {
            freeq!([a__, b__, e__, f__, m_, n_], x_)
                && eqq!(&m_ + &n_ + 1, 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;

            rubi_simp(
                &(-(&a__ * angle.sec()).pow(&m_) * (&b__ * angle.tan()).pow(&n_ + 1)
                    / (&b__ * &f__ * &m_)),
                x_,
            )
        },
    ));
}

fn push_rules_rule_3086(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, n_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 3086,
        source: "Int[(a_.*sec[e_.+f_.*x_])^m_.*(b_.*tan[e_.+f_.*x_])^n_.,x_Symbol] :=
          a/f \\[Star] Subst[Int[(a*x)^(m-1)*(-1+x^2)^((n-1)/2),x],x,Sec[e+f*x]] /;
        FreeQ[{a,e,f,m},x] && IntegerQ[(n-1)/2] && Not[IntegerQ[m/2] && LtQ[0,m,n+1]]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, e__, f__, m_, b__, n_, x_],
        optional: [a__, e__, f__, m_, b__, n_],
        when: {
            freeq!([a__, e__, f__, m_], x_)
                && integerq!((&n_ - 1) / 2)
                && !(integerq!(&m_ / 2) && ltq!(Atom::num(0), m_) && ltq!(m_, &n_ + 1))
        },
        rhs: {
            let subst_guard = fresh_substitution_symbol().unwrap();
            let subst = subst_guard.symbol();
            let z = Atom::var(subst);
            let transformed = (&a__ * &z).pow(&m_ - 1) * (-Atom::num(1) + z.pow(2)).pow((&n_ - 1) / 2);
            let primitive = rubi_rhs_int(&transformed, subst);
            let angle = &e__ + &f__ * x_;

            let substituted = rubi_subst(&primitive, subst, angle.sec());
            rubi_star(&a__ / &f__, substituted)
        },
    ));
}

fn push_rules_rule_3087(rules: &mut Vec<RubiRule>) {
    rubi_symb!(b__, m_, n_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 3087,
        source: "Int[sec[e_.+f_.*x_]^m_*(b_.*tan[e_.+f_.*x_])^n_.,x_Symbol] :=
          1/f \\[Star] Subst[Int[(b*x)^n*(1+x^2)^(m/2-1),x],x,Tan[e+f*x]] /;
        FreeQ[{b,e,f,n},x] && IntegerQ[m/2] && Not[IntegerQ[(n-1)/2] && LtQ[0,n,m-1]]",
        desc: "Integration by substitution",
        refs: [],
        pattern: i_sec(e__ + f__ * x_).pow(m_) * (b__ * i_tan(e__ + f__ * x_)).pow(n_),
        with: [e__, f__, m_, b__, n_, x_],
        optional: [e__, f__, b__, n_],
        when: {
            freeq!([b__, e__, f__, n_], x_)
                && integerq!(&m_ / 2)
                && !(integerq!((&n_ - 1) / 2) && ltq!(Atom::num(0), n_) && ltq!(n_, &m_ - 1))
        },
        rhs: {
            let subst_guard = fresh_substitution_symbol().unwrap();
            let subst = subst_guard.symbol();
            let z = Atom::var(subst);
            let transformed = (&b__ * &z).pow(&n_) * (Atom::num(1) + z.pow(2)).pow(&m_ / 2 - 1);
            let primitive = rubi_rhs_int(&transformed, subst);
            let angle = &e__ + &f__ * x_;

            let substituted = rubi_subst(&primitive, subst, angle.tan());
            rubi_star(Atom::num(1) / &f__, substituted)
        },
    ));
}

fn push_rules_rule_3088(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, n_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 3088,
        source: "Int[(a_.*sec[e_.+f_.*x_])^m_.*(b_.*tan[e_.+f_.*x_])^n_,x_Symbol] :=
          a^2*(a*Sec[e+f*x])^(m-2)*(b*Tan[e+f*x])^(n+1)/(b*f*(n+1)) -
          a^2*(m-2)/(b^2*(n+1)) \\[Star] Int[(a*Sec[e+f*x])^(m-2)*(b*Tan[e+f*x])^(n+2),x] /;
        FreeQ[{a,b,e,f},x] && LtQ[n,-1] && (GtQ[m,1] || EqQ[m,1] && EqQ[n,-3/2]) && IntegersQ[2*m,2*n]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: ["G&R 2.510.5, CRC 323a", "G&R 2.510.2, CRC 323b"],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, e__, f__, m_, b__, n_, x_],
        optional: [a__, e__, f__, m_, b__],
        when: {
            freeq!([a__, b__, e__, f__], x_)
                && ltq!(n_, -1)
                && (gtq!(m_, 1) || eqq!(m_, 1) && eqq!(n_, -Atom::num(3) / Atom::num(2)))
                && integersq!([Atom::num(2) * &m_, Atom::num(2) * &n_])
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_sec = &a__ * angle.sec();
            let scaled_tan = &b__ * angle.tan();
            let recursive_integrand = scaled_sec.pow(&m_ - 2) * scaled_tan.pow(&n_ + 2);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(
                    &(a__.pow(2) * scaled_sec.pow(&m_ - 2) * scaled_tan.pow(&n_ + 1)
                        / (&b__ * &f__ * (&n_ + 1))),
                    x_,
                ) - rubi_star(a__.pow(2) * (&m_ - 2) / (b__.pow(2) * (&n_ + 1)), recursive)
        },
    ));
}

fn push_rules_rule_3089(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, n_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 3089,
        source: "Int[(a_.*sec[e_.+f_.*x_])^m_.*(b_.*tan[e_.+f_.*x_])^n_,x_Symbol] :=
          (a*Sec[e+f*x])^m*(b*Tan[e+f*x])^(n+1)/(b*f*(n+1)) -
          (m+n+1)/(b^2*(n+1)) \\[Star] Int[(a*Sec[e+f*x])^m*(b*Tan[e+f*x])^(n+2),x] /;
        FreeQ[{a,b,e,f,m},x] && LtQ[n,-1] && IntegersQ[2*m,2*n]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: ["G&R 2.510.4", "G&R 2.510.1"],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, e__, f__, m_, b__, n_, x_],
        optional: [a__, e__, f__, m_, b__],
        when: {
            freeq!([a__, b__, e__, f__, m_], x_)
                && ltq!(n_, -1)
                && integersq!([Atom::num(2) * &m_, Atom::num(2) * &n_])
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_sec = &a__ * angle.sec();
            let scaled_tan = &b__ * angle.tan();
            let recursive_integrand = scaled_sec.pow(&m_) * scaled_tan.pow(&n_ + 2);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(
                    &(scaled_sec.pow(&m_) * scaled_tan.pow(&n_ + 1)
                        / (&b__ * &f__ * (&n_ + 1))),
                    x_,
                ) - rubi_star((&m_ + &n_ + 1) / (b__.pow(2) * (&n_ + 1)), recursive)
        },
    ));
}

fn push_rules_rule_3090(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, n_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 3090,
        source: "Int[(a_.*sec[e_.+f_.*x_])^m_*(b_.*tan[e_.+f_.*x_])^n_,x_Symbol] :=
          b*(a*Sec[e+f*x])^m*(b*Tan[e+f*x])^(n-1)/(f*m) -
          b^2*(n-1)/(a^2*m) \\[Star] Int[(a*Sec[e+f*x])^(m+2)*(b*Tan[e+f*x])^(n-2),x] /;
        FreeQ[{a,b,e,f},x] && GtQ[n,1] && (LtQ[m,-1] || EqQ[m,-1] && EqQ[n,3/2]) && IntegersQ[2*m,2*n]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: ["G&R 2.510.6, CRC 334b", "G&R 2.510.3, CRC 334a"],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, e__, f__, m_, b__, n_, x_],
        optional: [a__, e__, f__, b__],
        when: {
            freeq!([a__, b__, e__, f__], x_)
                && gtq!(n_, 1)
                && (ltq!(m_, -1) || eqq!(m_, -1) && eqq!(n_, Atom::num(3) / Atom::num(2)))
                && integersq!([Atom::num(2) * &m_, Atom::num(2) * &n_])
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_sec = &a__ * angle.sec();
            let scaled_tan = &b__ * angle.tan();
            let recursive_integrand = scaled_sec.pow(&m_ + 2) * scaled_tan.pow(&n_ - 2);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(
                    &(&b__ * scaled_sec.pow(&m_) * scaled_tan.pow(&n_ - 1) / (&f__ * &m_)),
                    x_,
                ) - rubi_star(b__.pow(2) * (&n_ - 1) / (a__.pow(2) * &m_), recursive)
        },
    ));
}

fn push_rules_rule_3091(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, n_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 3091,
        source: "Int[(a_.*sec[e_.+f_.*x_])^m_.*(b_.*tan[e_.+f_.*x_])^n_,x_Symbol] :=
          b*(a*Sec[e+f*x])^m*(b*Tan[e+f*x])^(n-1)/(f*(m+n-1)) -
          b^2*(n-1)/(m+n-1) \\[Star] Int[(a*Sec[e+f*x])^m*(b*Tan[e+f*x])^(n-2),x] /;
        FreeQ[{a,b,e,f,m},x] && GtQ[n,1] && NeQ[m+n-1,0] && IntegersQ[2*m,2*n]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: ["G&R 2.510.1", "G&R 2.510.4"],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, e__, f__, m_, b__, n_, x_],
        optional: [a__, e__, f__, m_, b__],
        when: {
            freeq!([a__, b__, e__, f__, m_], x_)
                && gtq!(n_, 1)
                && neq!(&m_ + &n_ - 1, 0)
                && integersq!([Atom::num(2) * &m_, Atom::num(2) * &n_])
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_sec = &a__ * angle.sec();
            let scaled_tan = &b__ * angle.tan();
            let recursive_integrand = scaled_sec.pow(&m_) * scaled_tan.pow(&n_ - 2);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(
                    &(&b__ * scaled_sec.pow(&m_) * scaled_tan.pow(&n_ - 1)
                        / (&f__ * (&m_ + &n_ - 1))),
                    x_,
                ) - rubi_star(b__.pow(2) * (&n_ - 1) / (&m_ + &n_ - 1), recursive)
        },
    ));
}

fn push_rules_rule_3092(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, n_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 3092,
        source: "Int[(a_.*sec[e_.+f_.*x_])^m_*(b_.*tan[e_.+f_.*x_])^n_,x_Symbol] :=
          -(a*Sec[e+f*x])^m*(b*Tan[e+f*x])^(n+1)/(b*f*m) +
          (m+n+1)/(a^2*m) \\[Star] Int[(a*Sec[e+f*x])^(m+2)*(b*Tan[e+f*x])^n,x] /;
        FreeQ[{a,b,e,f,n},x] && (LtQ[m,-1] || EqQ[m,-1] && EqQ[n,-1/2]) && IntegersQ[2*m,2*n]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, e__, f__, m_, b__, n_, x_],
        optional: [a__, e__, f__, b__],
        when: {
            freeq!([a__, b__, e__, f__, n_], x_)
                && (ltq!(m_, -1) || eqq!(m_, -1) && eqq!(n_, -Atom::num(1) / Atom::num(2)))
                && integersq!([Atom::num(2) * &m_, Atom::num(2) * &n_])
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_sec = &a__ * angle.sec();
            let scaled_tan = &b__ * angle.tan();
            let recursive_integrand = scaled_sec.pow(&m_ + 2) * scaled_tan.pow(&n_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(
                    &(-scaled_sec.pow(&m_) * scaled_tan.pow(&n_ + 1) / (&b__ * &f__ * &m_)),
                    x_,
                ) + rubi_star((&m_ + &n_ + 1) / (a__.pow(2) * &m_), recursive)
        },
    ));
}

fn push_rules_rule_3093(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, n_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 3093,
        source: "Int[(a_.*sec[e_.+f_.*x_])^m_.*(b_.*tan[e_.+f_.*x_])^n_,x_Symbol] :=
          a^2*(a*Sec[e+f*x])^(m-2)*(b*Tan[e+f*x])^(n+1)/(b*f*(m+n-1)) +
          a^2*(m-2)/(m+n-1) \\[Star] Int[(a*Sec[e+f*x])^(m-2)*(b*Tan[e+f*x])^n,x] /;
        FreeQ[{a,b,e,f,n},x] && (GtQ[m,1] || EqQ[m,1] && EqQ[n,1/2]) && NeQ[m+n-1,0] && IntegersQ[2*m,2*n]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: ["G&R 2.510.2, CRC 323b", "G&R 2.510.5, CRC 323a"],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, e__, f__, m_, b__, n_, x_],
        optional: [a__, e__, f__, m_, b__],
        when: {
            freeq!([a__, b__, e__, f__, n_], x_)
                && (gtq!(m_, 1) || eqq!(m_, 1) && eqq!(n_, Atom::num(1) / Atom::num(2)))
                && neq!(&m_ + &n_ - 1, 0)
                && integersq!([Atom::num(2) * &m_, Atom::num(2) * &n_])
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_sec = &a__ * angle.sec();
            let scaled_tan = &b__ * angle.tan();
            let recursive_integrand = scaled_sec.pow(&m_ - 2) * scaled_tan.pow(&n_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(
                    &(a__.pow(2) * scaled_sec.pow(&m_ - 2) * scaled_tan.pow(&n_ + 1)
                        / (&b__ * &f__ * (&m_ + &n_ - 1))),
                    x_,
                ) + rubi_star(a__.pow(2) * (&m_ - 2) / (&m_ + &n_ - 1), recursive)
        },
    ));
}

fn push_rules_rule_3094(rules: &mut Vec<RubiRule>) {
    rubi_symb!(b__, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 3094,
        source: "Int[sec[e_.+f_.*x_]/Sqrt[b_.*tan[e_.+f_.*x_]],x_Symbol]:=
          Sqrt[Sin[e+f*x]]/(Sqrt[Cos[e+f*x]]*Sqrt[b*Tan[e+f*x]]) \\[Star] Int[1/(Sqrt[Cos[e+f*x]]*Sqrt[Sin[e+f*x]]),x] /;
        FreeQ[{b,e,f},x]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: i_sec(e__ + f__ * x_) / (b__ * i_tan(e__ + f__ * x_)).sqrt(),
        with: [e__, f__, b__, x_],
        optional: [e__, f__, b__],
        when: { freeq!([b__, e__, f__], x_) },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let recursive_integrand = Atom::num(1) / (angle.cos().sqrt() * angle.sin().sqrt());
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(angle.sin().sqrt()
                    / (angle.cos().sqrt() * (&b__ * angle.tan()).sqrt()), recursive)
        },
    ));
}

fn push_rules_rule_3095(rules: &mut Vec<RubiRule>) {
    rubi_symb!(b__, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 3095,
        source: "Int[Sqrt[b_.*tan[e_.+f_.*x_]]/sec[e_.+f_.*x_],x_Symbol]:=
          Sqrt[Cos[e+f*x]]*Sqrt[b*Tan[e+f*x]]/Sqrt[Sin[e+f*x]] \\[Star] Int[Sqrt[Cos[e+f*x]]*Sqrt[Sin[e+f*x]],x] /;
        FreeQ[{b,e,f},x]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: (b__ * i_tan(e__ + f__ * x_)).sqrt() / i_sec(e__ + f__ * x_),
        with: [b__, e__, f__, x_],
        optional: [b__, e__, f__],
        when: { freeq!([b__, e__, f__], x_) },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let recursive_integrand = angle.cos().sqrt() * angle.sin().sqrt();
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(angle.cos().sqrt() * (&b__ * angle.tan()).sqrt() / angle.sin().sqrt(), recursive)
        },
    ));
}

fn push_rules_rule_3096(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, n_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 3096,
        source: "Int[(a_.*sec[e_.+f_.*x_])^m_*(b_.*tan[e_.+f_.*x_])^n_,x_Symbol]:=
          a^(m+n)*(b*Tan[e+f*x])^n/((a*Sec[e+f*x])^n*(b*Sin[e+f*x])^n) \\[Star] Int[(b*Sin[e+f*x])^n/Cos[e+f*x]^(m+n),x] /;
        FreeQ[{a,b,e,f,m,n},x] && IntegerQ[n+1/2] && IntegerQ[m+1/2]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, e__, f__, m_, b__, n_, x_],
        optional: [a__, e__, f__, b__],
        when: {
            freeq!([a__, b__, e__, f__, m_, n_], x_)
                && integerq!(&n_ + Atom::num(1) / Atom::num(2))
                && integerq!(&m_ + Atom::num(1) / Atom::num(2))
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_sec = &a__ * angle.sec();
            let scaled_tan = &b__ * angle.tan();
            let scaled_sin = &b__ * angle.sin();
            let recursive_integrand = scaled_sin.pow(&n_) / angle.cos().pow(&m_ + &n_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(a__.pow(&m_ + &n_) * scaled_tan.pow(&n_) / (scaled_sec.pow(&n_) * scaled_sin.pow(&n_)), recursive)
        },
    ));
}

fn push_rules_rule_3097(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, n_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 3097,
        source: "Int[(a_.*sec[e_.+f_.*x_])^m_.*(b_.*tan[e_.+f_.*x_])^n_,x_Symbol]:=
          (a*Sec[e+f*x])^m*(b*Tan[e+f*x])^(n+1)*(Cos[e+f*x]^2)^((m+n+1)/2)/(b*f*(n+1))*
            Hypergeometric2F1[(n+1)/2,(m+n+1)/2,(n+3)/2,Sin[e+f*x]^2] /;
        FreeQ[{a,b,e,f,m,n},x] && Not[IntegerQ[(n-1)/2]] && Not[IntegerQ[m/2]]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, e__, f__, m_, b__, n_, x_],
        optional: [a__, e__, f__, m_, b__],
        when: {
            freeq!([a__, b__, e__, f__, m_, n_], x_)
                && !integerq!((&n_ - 1) / 2)
                && !integerq!(&m_ / 2)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_sec = &a__ * angle.sec();
            let scaled_tan = &b__ * angle.tan();

            rubi_simp(
                &(scaled_sec.pow(&m_)
                    * scaled_tan.pow(&n_ + 1)
                    * angle.cos().pow(2).pow((&m_ + &n_ + 1) / 2)
                    * rubi_hypergeometric2f1(
                        (&n_ + 1) / 2,
                        (&m_ + &n_ + 1) / 2,
                        (&n_ + 3) / 2,
                        angle.sin().pow(2),
                    )
                    / (&b__ * &f__ * (&n_ + 1))),
                x_,
            )
        },
    ));
}

fn push_rules_rule_3098(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, m_, n_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 3098,
        source: "Int[(a_.*csc[e_.+f_.*x_])^m_*(b_.*tan[e_.+f_.*x_])^n_,x_Symbol] :=
          (a*Csc[e+f*x])^FracPart[m]*(Sin[e+f*x]/a)^FracPart[m] \\[Star] Int[(b*Tan[e+f*x])^n/(Sin[e+f*x]/a)^m,x] /;
        FreeQ[{a,b,e,f,m,n},x] && Not[IntegerQ[m]] && Not[IntegerQ[n]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: (a__ * i_csc(e__ + f__ * x_)).pow(m_)
            * (b__ * i_tan(e__ + f__ * x_)).pow(n_),
        with: [a__, e__, f__, m_, b__, n_, x_],
        optional: [a__, e__, f__, b__],
        when: {
            freeq!([a__, b__, e__, f__, m_, n_], x_)
                && !integerq!(m_)
                && !integerq!(n_)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_csc = &a__ * angle.csc();
            let scaled_tan = &b__ * angle.tan();
            let sin_over_a = angle.sin() / &a__;
            let frac_m = rubi_frac_part(&m_);
            let recursive_integrand = scaled_tan.pow(&n_) / sin_over_a.pow(&m_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(scaled_csc.pow(&frac_m) * sin_over_a.pow(frac_m), recursive)
        },
    ));
}

fn push_rules_rule_3099(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, n_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 3099,
        source: "Int[(a_.*csc[e_.+f_.*x_])^m_*(b_.*sec[e_.+f_.*x_])^n_,x_Symbol] :=
          a*b*(a*Csc[e+f*x])^(m-1)*(b*Sec[e+f*x])^(n-1)/(f*(n-1)) /;
        FreeQ[{a,b,e,f,m,n},x] && EqQ[m+n-2,0] && NeQ[n,1]",
        desc: "Apply the direct antiderivative formula.",
        refs: ["G&R 2.510.3, CRC 334a, A&S 4.3.128b with m+n-2\\[Equal]0Bold", "G&R 2.510.6, CRC 334b, A&S 4.3.128a with m+n-2\\[Equal]0Bold"],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, e__, f__, m_, b__, n_, x_],
        optional: [a__, e__, f__, b__],
        when: {
            freeq!([a__, b__, e__, f__, m_, n_], x_)
                && eqq!(&m_ + &n_ - 2, 0)
                && neq!(n_, 1)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;

            rubi_simp(
                &(&a__
                    * &b__
                    * (&a__ * angle.csc()).pow(&m_ - 1)
                    * (&b__ * angle.sec()).pow(&n_ - 1)
                    / (&f__ * (&n_ - 1))),
                x_,
            )
        },
    ));
}

fn push_rules_rule_3100(rules: &mut Vec<RubiRule>) {
    rubi_symb!(m_, n_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 3100,
        source: "Int[csc[e_.+f_.*x_]^m_.*sec[e_.+f_.*x_]^n_.,x_Symbol] :=
          1/f \\[Star] Subst[Int[(1+x^2)^((m+n)/2-1)/x^m,x],x,Tan[e+f*x]] /;
        FreeQ[{e,f},x] && IntegersQ[m,n,(m+n)/2]",
        desc: "Integration by substitution",
        refs: [],
        pattern: i_csc(e__ + f__ * x_).pow(m_) * i_sec(e__ + f__ * x_).pow(n_),
        with: [e__, f__, m_, n_, x_],
        optional: [e__, f__, m_, n_],
        when: {
            freeq!([e__, f__], x_)
                && integersq!([m_, n_, (&m_ + &n_) / 2])
        },
        rhs: {
            let subst_guard = fresh_substitution_symbol().unwrap();
            let subst = subst_guard.symbol();
            let z = Atom::var(subst);
            let transformed = (Atom::num(1) + z.pow(2)).pow((&m_ + &n_) / 2 - 1) / z.pow(&m_);
            let primitive = rubi_rhs_int(&transformed, subst);
            let angle = &e__ + &f__ * x_;
            let substituted = rubi_subst(&primitive, subst, angle.tan());

            rubi_star(Atom::num(1) / &f__, substituted)
        },
    ));
}

fn push_rules_rule_3101(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, m_, n_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 3101,
        source: "Int[(a_.*csc[e_.+f_.*x_])^m_*sec[e_.+f_.*x_]^n_.,x_Symbol] :=
          -1/(f*a^n) \\[Star] Subst[Int[x^(m+n-1)/(-1+x^2/a^2)^((n+1)/2),x],x,a*Csc[e+f*x]] /;
        FreeQ[{a,e,f,m},x] && IntegerQ[(n+1)/2] && Not[IntegerQ[(m+1)/2] && LtQ[0,m,n]]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (a__ * i_csc(e__ + f__ * x_)).pow(m_) * i_sec(e__ + f__ * x_).pow(n_),
        with: [a__, e__, f__, m_, n_, x_],
        optional: [a__, e__, f__, n_],
        when: {
            freeq!([a__, e__, f__, m_], x_)
                && integerq!((&n_ + 1) / 2)
                && !(integerq!((&m_ + 1) / 2) && ltq!(0, m_, n_))
        },
        rhs: {
            let subst_guard = fresh_substitution_symbol().unwrap();
            let subst = subst_guard.symbol();
            let z = Atom::var(subst);
            let transformed =
                z.pow(&m_ + &n_ - 1) / (-Atom::num(1) + z.pow(2) / a__.pow(2)).pow((&n_ + 1) / 2);
            let primitive = rubi_rhs_int(&transformed, subst);
            let angle = &e__ + &f__ * x_;
            let substituted = rubi_subst(&primitive, subst, &a__ * angle.csc());

            rubi_star(-(Atom::num(1) / (&f__ * a__.pow(&n_))), substituted)
        },
    ));
}

fn push_rules_rule_3102(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, m_, n_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 3102,
        source: "Int[(a_.*sec[e_.+f_.*x_])^m_*csc[e_.+f_.*x_]^n_.,x_Symbol] :=
          1/(f*a^n) \\[Star] Subst[Int[x^(m+n-1)/(-1+x^2/a^2)^((n+1)/2),x],x,a*Sec[e+f*x]] /;
        FreeQ[{a,e,f,m},x] && IntegerQ[(n+1)/2] && Not[IntegerQ[(m+1)/2] && LtQ[0,m,n]]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (a__ * i_sec(e__ + f__ * x_)).pow(m_) * i_csc(e__ + f__ * x_).pow(n_),
        with: [a__, e__, f__, m_, n_, x_],
        optional: [a__, e__, f__, n_],
        when: {
            freeq!([a__, e__, f__, m_], x_)
                && integerq!((&n_ + 1) / 2)
                && !(integerq!((&m_ + 1) / 2) && ltq!(0, m_, n_))
        },
        rhs: {
            let subst_guard = fresh_substitution_symbol().unwrap();
            let subst = subst_guard.symbol();
            let z = Atom::var(subst);
            let transformed =
                z.pow(&m_ + &n_ - 1) / (-Atom::num(1) + z.pow(2) / a__.pow(2)).pow((&n_ + 1) / 2);
            let primitive = rubi_rhs_int(&transformed, subst);
            let angle = &e__ + &f__ * x_;
            let substituted = rubi_subst(&primitive, subst, &a__ * angle.sec());

            rubi_star(Atom::num(1) / (&f__ * a__.pow(&n_)), substituted)
        },
    ));
}

fn push_rules_rule_3103(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, n_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 3103,
        source: "Int[(a_.*csc[e_.+f_.*x_])^m_*(b_.*sec[e_.+f_.*x_])^n_,x_Symbol] :=
          -a*(a*Csc[e+f*x])^(m-1)*(b*Sec[e+f*x])^(n+1)/(f*b*(m-1)) +
          a^2*(n+1)/(b^2*(m-1)) \\[Star] Int[(a*Csc[e+f*x])^(m-2)*(b*Sec[e+f*x])^(n+2),x] /;
        FreeQ[{a,b,e,f},x] && GtQ[m,1] && LtQ[n,-1] && IntegersQ[2*m,2*n]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: ["G&R 2.510.1", "G&R 2.510.4"],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, e__, f__, m_, b__, n_, x_],
        optional: [a__, e__, f__, b__],
        when: {
            freeq!([a__, b__, e__, f__], x_)
                && gtq!(m_, 1)
                && ltq!(n_, -1)
                && integersq!([Atom::num(2) * &m_, Atom::num(2) * &n_])
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_csc = &a__ * angle.csc();
            let scaled_sec = &b__ * angle.sec();
            let recursive_integrand = scaled_csc.pow(&m_ - 2) * scaled_sec.pow(&n_ + 2);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(
                    &(-&a__ * scaled_csc.pow(&m_ - 1) * scaled_sec.pow(&n_ + 1)
                        / (&f__ * &b__ * (&m_ - 1))),
                    x_,
                ) + rubi_star(a__.pow(2) * (&n_ + 1) / (b__.pow(2) * (&m_ - 1)), recursive)
        },
    ));
}

fn push_rules_rule_3104(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, n_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 3104,
        source: "Int[(a_.*csc[e_.+f_.*x_])^m_*(b_.*sec[e_.+f_.*x_])^n_,x_Symbol] :=
          b*(a*Csc[e+f*x])^(m+1)*(b*Sec[e+f*x])^(n-1)/(f*a*(n-1)) +
          b^2*(m+1)/(a^2*(n-1)) \\[Star] Int[(a*Csc[e+f*x])^(m+2)*(b*Sec[e+f*x])^(n-2),x] /;
        FreeQ[{a,b,e,f},x] && GtQ[n,1] && LtQ[m,-1] && IntegersQ[2*m,2*n]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: ["G&R 2.510.1", "G&R 2.510.4"],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, e__, f__, m_, b__, n_, x_],
        optional: [a__, e__, f__, b__],
        when: {
            freeq!([a__, b__, e__, f__], x_)
                && gtq!(n_, 1)
                && ltq!(m_, -1)
                && integersq!([Atom::num(2) * &m_, Atom::num(2) * &n_])
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_csc = &a__ * angle.csc();
            let scaled_sec = &b__ * angle.sec();
            let recursive_integrand = scaled_csc.pow(&m_ + 2) * scaled_sec.pow(&n_ - 2);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(
                    &(&b__ * scaled_csc.pow(&m_ + 1) * scaled_sec.pow(&n_ - 1)
                        / (&f__ * &a__ * (&n_ - 1))),
                    x_,
                ) + rubi_star(b__.pow(2) * (&m_ + 1) / (a__.pow(2) * (&n_ - 1)), recursive)
        },
    ));
}

fn push_rules_rule_3105(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, n_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 3105,
        source: "Int[(a_.*csc[e_.+f_.*x_])^m_*(b_.*sec[e_.+f_.*x_])^n_.,x_Symbol] :=
          -a*b*(a*Csc[e+f*x])^(m-1)*(b*Sec[e+f*x])^(n-1)/(f*(m-1)) +
          a^2*(m+n-2)/(m-1) \\[Star] Int[(a*Csc[e+f*x])^(m-2)*(b*Sec[e+f*x])^n,x] /;
        FreeQ[{a,b,e,f,n},x] && GtQ[m,1] && IntegersQ[2*m,2*n] && Not[GtQ[n,m]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, e__, f__, m_, b__, n_, x_],
        optional: [a__, e__, f__, b__, n_],
        when: {
            freeq!([a__, b__, e__, f__, n_], x_)
                && gtq!(m_, 1)
                && integersq!([Atom::num(2) * &m_, Atom::num(2) * &n_])
                && !gtq!(n_, m_)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_csc = &a__ * angle.csc();
            let scaled_sec = &b__ * angle.sec();
            let recursive_integrand = scaled_csc.pow(&m_ - 2) * scaled_sec.pow(&n_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(
                    &(-&a__ * &b__ * scaled_csc.pow(&m_ - 1) * scaled_sec.pow(&n_ - 1)
                        / (&f__ * (&m_ - 1))),
                    x_,
                ) + rubi_star(a__.pow(2) * (&m_ + &n_ - 2) / (&m_ - 1), recursive)
        },
    ));
}

fn push_rules_rule_3106(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, n_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 3106,
        source: "Int[(a_.*csc[e_.+f_.*x_])^m_.*(b_.*sec[e_.+f_.*x_])^n_,x_Symbol] :=
          a*b*(a*Csc[e+f*x])^(m-1)*(b*Sec[e+f*x])^(n-1)/(f*(n-1)) +
          b^2*(m+n-2)/(n-1) \\[Star] Int[(a*Csc[e+f*x])^m*(b*Sec[e+f*x])^(n-2),x] /;
        FreeQ[{a,b,e,f,m},x] && GtQ[n,1] && IntegersQ[2*m,2*n]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: ["G&R 2.510.2, CRC 323b, A&S 4.3.127b", "G&R 2.510.5, CRC 323a, A&S 4.3.127a"],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, e__, f__, m_, b__, n_, x_],
        optional: [a__, e__, f__, m_, b__],
        when: {
            freeq!([a__, b__, e__, f__, m_], x_)
                && gtq!(n_, 1)
                && integersq!([Atom::num(2) * &m_, Atom::num(2) * &n_])
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_csc = &a__ * angle.csc();
            let scaled_sec = &b__ * angle.sec();
            let recursive_integrand = scaled_csc.pow(&m_) * scaled_sec.pow(&n_ - 2);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(
                    &(&a__ * &b__ * scaled_csc.pow(&m_ - 1) * scaled_sec.pow(&n_ - 1)
                        / (&f__ * (&n_ - 1))),
                    x_,
                ) + rubi_star(b__.pow(2) * (&m_ + &n_ - 2) / (&n_ - 1), recursive)
        },
    ));
}

fn push_rules_rule_3107(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, n_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 3107,
        source: "Int[(a_.*csc[e_.+f_.*x_])^m_*(b_.*sec[e_.+f_.*x_])^n_.,x_Symbol] :=
          b*(a*Csc[e+f*x])^(m+1)*(b*Sec[e+f*x])^(n-1)/(a*f*(m+n)) +
          (m+1)/(a^2*(m+n)) \\[Star] Int[(a*Csc[e+f*x])^(m+2)*(b*Sec[e+f*x])^n,x] /;
        FreeQ[{a,b,e,f,n},x] && LtQ[m,-1] && NeQ[m+n,0] && IntegersQ[2*m,2*n]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: ["G&R 2.510.3, CRC 334a, A&S 4.3.128b", "G&R 2.510.6, CRC 334b, A&S 4.3.128a"],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, e__, f__, m_, b__, n_, x_],
        optional: [a__, e__, f__, b__, n_],
        when: {
            freeq!([a__, b__, e__, f__, n_], x_)
                && ltq!(m_, -1)
                && neq!(&m_ + &n_, 0)
                && integersq!([Atom::num(2) * &m_, Atom::num(2) * &n_])
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_csc = &a__ * angle.csc();
            let scaled_sec = &b__ * angle.sec();
            let recursive_integrand = scaled_csc.pow(&m_ + 2) * scaled_sec.pow(&n_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(
                    &(&b__ * scaled_csc.pow(&m_ + 1) * scaled_sec.pow(&n_ - 1)
                        / (&a__ * &f__ * (&m_ + &n_))),
                    x_,
                ) + rubi_star((&m_ + 1) / (a__.pow(2) * (&m_ + &n_)), recursive)
        },
    ));
}

fn push_rules_rule_3108(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, n_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 3108,
        source: "Int[(a_.*csc[e_.+f_.*x_])^m_.*(b_.*sec[e_.+f_.*x_])^n_,x_Symbol] :=
          -a*(a*Csc[e+f*x])^(m-1)*(b*Sec[e+f*x])^(n+1)/(b*f*(m+n)) +
          (n+1)/(b^2*(m+n)) \\[Star] Int[(a*Csc[e+f*x])^m*(b*Sec[e+f*x])^(n+2),x] /;
        FreeQ[{a,b,e,f,m},x] && LtQ[n,-1] && NeQ[m+n,0] && IntegersQ[2*m,2*n]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: ["G&R 2.510.3, CRC 334a, A&S 4.3.128b", "G&R 2.510.6, CRC 334b, A&S 4.3.128a"],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, e__, f__, m_, b__, n_, x_],
        optional: [a__, e__, f__, m_, b__],
        when: {
            freeq!([a__, b__, e__, f__, m_], x_)
                && ltq!(n_, -1)
                && neq!(&m_ + &n_, 0)
                && integersq!([Atom::num(2) * &m_, Atom::num(2) * &n_])
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_csc = &a__ * angle.csc();
            let scaled_sec = &b__ * angle.sec();
            let recursive_integrand = scaled_csc.pow(&m_) * scaled_sec.pow(&n_ + 2);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(
                    &(-&a__ * scaled_csc.pow(&m_ - 1) * scaled_sec.pow(&n_ + 1)
                        / (&b__ * &f__ * (&m_ + &n_))),
                    x_,
                ) + rubi_star((&n_ + 1) / (b__.pow(2) * (&m_ + &n_)), recursive)
        },
    ));
}

fn push_rules_rule_3109(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, n_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 3109,
        source: "Int[(a_.*csc[e_.+f_.*x_])^m_*(b_.*sec[e_.+f_.*x_])^n_,x_Symbol] :=
          (a*Csc[e+f*x])^m*(b*Sec[e+f*x])^n/Tan[e+f*x]^n \\[Star] Int[Tan[e+f*x]^n,x] /;
        FreeQ[{a,b,e,f,m,n},x] && Not[IntegerQ[n]] && EqQ[m+n,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, e__, f__, m_, b__, n_, x_],
        optional: [a__, e__, f__, b__],
        when: {
            freeq!([a__, b__, e__, f__, m_, n_], x_)
                && !integerq!(n_)
                && eqq!(&m_ + &n_, 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let tan = angle.tan();
            let scaled_csc = &a__ * angle.csc();
            let scaled_sec = &b__ * angle.sec();
            let recursive_integrand = tan.pow(&n_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(scaled_csc.pow(&m_) * scaled_sec.pow(&n_) / tan.pow(&n_), recursive)
        },
    ));
}

fn push_rules_rule_3110(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, n_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 3110,
        source: "Int[(a_.*csc[e_.+f_.*x_])^m_*(b_.*sec[e_.+f_.*x_])^n_,x_Symbol] :=
          (a*Csc[e+f*x])^m*(b*Sec[e+f*x])^n*(a*Sin[e+f*x])^m*(b*Cos[e+f*x])^n \\[Star] Int[(a*Sin[e+f*x])^(-m)*(b*Cos[e+f*x])^(-n),x] /;
        FreeQ[{a,b,e,f,m,n},x] && IntegerQ[m-1/2] && IntegerQ[n-1/2]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, e__, f__, m_, b__, n_, x_],
        optional: [a__, e__, f__, b__],
        when: {
            freeq!([a__, b__, e__, f__, m_, n_], x_)
                && integerq!(&m_ - Atom::num(1) / Atom::num(2))
                && integerq!(&n_ - Atom::num(1) / Atom::num(2))
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_csc = &a__ * angle.csc();
            let scaled_sec = &b__ * angle.sec();
            let scaled_sin = &a__ * angle.sin();
            let scaled_cos = &b__ * angle.cos();
            let recursive_integrand = scaled_sin.pow(-&m_) * scaled_cos.pow(-&n_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(scaled_csc.pow(&m_) * scaled_sec.pow(&n_) * scaled_sin.pow(&m_) * scaled_cos.pow(&n_), recursive)
        },
    ));
}

fn push_rules_rule_3111(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, n_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 3111,
        source: "Int[(a_.*csc[e_.+f_.*x_])^m_*(b_.*sec[e_.+f_.*x_])^n_,x_Symbol] :=
          a^2/b^2*(a*Csc[e+f*x])^(m-1)*(b*Sec[e+f*x])^(n+1)*(a*Sin[e+f*x])^(m-1)*(b*Cos[e+f*x])^(n+1) \\[Star]
            Int[(a*Sin[e+f*x])^(-m)*(b*Cos[e+f*x])^(-n),x] /;
        FreeQ[{a,b,e,f,m,n},x] && Not[SimplerQ[-m,-n]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, e__, f__, m_, b__, n_, x_],
        optional: [a__, e__, f__, b__],
        when: {
            freeq!([a__, b__, e__, f__, m_, n_], x_)
                && !simplerq!(-&m_, -&n_)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_csc = &a__ * angle.csc();
            let scaled_sec = &b__ * angle.sec();
            let scaled_sin = &a__ * angle.sin();
            let scaled_cos = &b__ * angle.cos();
            let recursive_integrand = scaled_sin.pow(-&m_) * scaled_cos.pow(-&n_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(a__.pow(2) * scaled_csc.pow(&m_ - 1) * scaled_sec.pow(&n_ + 1) * scaled_sin.pow(&m_ - 1) * scaled_cos.pow(&n_ + 1) / b__.pow(2), recursive)
        },
    ));
}

fn push_rules_rule_3112(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, m_, n_, x_, e__, f__);
    rules.push(rubi_rule!(
        order: 3112,
        source: "Int[(a_.*sec[e_.+f_.*x_])^m_*(b_.*csc[e_.+f_.*x_])^n_,x_Symbol] :=
          a^2/b^2*(a*Sec[e+f*x])^(m-1)*(b*Csc[e+f*x])^(n+1)*(a*Cos[e+f*x])^(m-1)*(b*Sin[e+f*x])^(n+1) \\[Star]
            Int[(a*Cos[e+f*x])^(-m)*(b*Sin[e+f*x])^(-n),x] /;
        FreeQ[{a,b,e,f,m,n},x]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: (a__ * i_sec(e__ + f__ * x_)).pow(m_)
            * (b__ * i_csc(e__ + f__ * x_)).pow(n_),
        with: [a__, e__, f__, m_, b__, n_, x_],
        optional: [a__, e__, f__, b__],
        when: {
            freeq!([a__, b__, e__, f__, m_, n_], x_)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_sec = &a__ * angle.sec();
            let scaled_csc = &b__ * angle.csc();
            let scaled_cos = &a__ * angle.cos();
            let scaled_sin = &b__ * angle.sin();
            let recursive_integrand = scaled_cos.pow(-&m_) * scaled_sin.pow(-&n_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(a__.pow(2) * scaled_sec.pow(&m_ - 1) * scaled_csc.pow(&n_ + 1) * scaled_cos.pow(&m_ - 1) * scaled_sin.pow(&n_ + 1) / b__.pow(2), recursive)
        },
    ));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn downvalues_3043_through_3092_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .filter(|order| (3043..=3092).contains(order))
            .collect::<Vec<_>>();

        assert_eq!(orders, (3043..=3092).collect::<Vec<_>>());
    }

    #[test]
    fn downvalues_3093_through_3112_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .filter(|order| (3093..=3112).contains(order))
            .collect::<Vec<_>>();

        assert_eq!(orders, (3093..=3112).collect::<Vec<_>>());
    }
}

// Generated shared pattern builders.

#[inline(never)]
fn rubi_shared_pattern_0(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    (a__ * i_cos(e__ + f__ * x_)).pow(m_) * (b__ * i_sin(e__ + f__ * x_)).pow(n_)
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    (a__ * i_csc(e__ + f__ * x_)).pow(m_) * (b__ * i_sec(e__ + f__ * x_)).pow(n_)
}

#[inline(never)]
fn rubi_shared_pattern_2(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    (a__ * i_sec(e__ + f__ * x_)).pow(m_) * (b__ * i_tan(e__ + f__ * x_)).pow(n_)
}

#[inline(never)]
fn rubi_shared_pattern_3(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    (a__ * i_sin(e__ + f__ * x_)).pow(m_) * (b__ * i_cos(e__ + f__ * x_)).pow(n_)
}

#[inline(never)]
fn rubi_shared_pattern_4(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    (a__ * i_sin(e__ + f__ * x_)).pow(m_) * (b__ * i_sec(e__ + f__ * x_)).pow(n_)
}

#[inline(never)]
fn rubi_shared_pattern_5(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    (a__ * i_sin(e__ + f__ * x_)).pow(m_) * (b__ * i_tan(e__ + f__ * x_)).pow(n_)
}

#[inline(never)]
fn rubi_shared_pattern_6(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    (a__ * i_sin(e__ + f__ * x_)).pow(m_) * i_tan(e__ + f__ * x_).pow(n_)
}
