use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_3777(rules);
    push_rules_rule_3778(rules);
    push_rules_rule_3779(rules);
    push_rules_rule_3780(rules);
    push_rules_rule_3781(rules);
    push_rules_rule_3782(rules);
    push_rules_rule_3783(rules);
    push_rules_rule_3784(rules);
    push_rules_rule_3785(rules);
    push_rules_rule_3786(rules);
    push_rules_rule_3787(rules);
    push_rules_rule_3788(rules);
    push_rules_rule_3789(rules);
    push_rules_rule_3790(rules);
    push_rules_rule_3791(rules);
    push_rules_rule_3792(rules);
    push_rules_rule_3793(rules);
    push_rules_rule_3794(rules);
    push_rules_rule_3795(rules);
    push_rules_rule_3796(rules);
    push_rules_rule_3797(rules);
    push_rules_rule_3798(rules);
    push_rules_rule_3799(rules);
    push_rules_rule_3800(rules);
    push_rules_rule_3801(rules);
    push_rules_rule_3802(rules);
    push_rules_rule_3803(rules);
    push_rules_rule_3804(rules);
    push_rules_rule_3805(rules);
    push_rules_rule_3806(rules);
    push_rules_rule_3807(rules);
    push_rules_rule_3808(rules);
    push_rules_rule_3809(rules);
}

fn push_rules_rule_3777(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; c__, d__, e__, f__, m_, x_);
    rules.push(rubi_rule!(
        order: 3777,
        source: "Int[(c_.+d_.*x_)^m_.*sin[e_.+f_.*x_],x_Symbol] :=
          -(c+d*x)^m*Cos[e+f*x]/f +
          d*m/f \\[Star] Int[(c+d*x)^(m-1)*Cos[e+f*x],x] /;
        FreeQ[{c,d,e,f},x] && GtQ[m,0]",
        desc: "Integration by parts",
        refs: ["CRC 392, A&S 4.3.119", "CRC 396, A&S 4.3.123"],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [c__, d__, m_, e__, f__, x_],
        optional: [c__, d__, m_, e__, f__],
        when: {
            freeq!([c__, d__, e__, f__], x_) && gtq!(m_, 0)
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let angle = &e__ + &f__ * x_;
            let cos = angle.cos();
            let recursive_integrand = linear.pow(&m_ - 1) * &cos;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(-linear.pow(&m_) * cos / &f__), x_)
                    + rubi_star(&d__ * &m_ / &f__, recursive)
        },
    ));
}

fn push_rules_rule_3778(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; c__, d__, e__, f__, m_, x_);
    rules.push(rubi_rule!(
        order: 3778,
        source: "Int[(c_.+d_.*x_)^m_*sin[e_.+f_.*x_],x_Symbol] :=
          (c+d*x)^(m+1)*Sin[e+f*x]/(d*(m+1)) -
          f/(d*(m+1)) \\[Star] Int[(c+d*x)^(m+1)*Cos[e+f*x],x] /;
        FreeQ[{c,d,e,f},x] && LtQ[m,-1]",
        desc: "Integration by parts",
        refs: ["CRC 405, A&S 4.3.120", "CRC 406, A&S 4.3.124"],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [c__, d__, m_, e__, f__, x_],
        optional: [c__, d__, e__, f__],
        when: {
            freeq!([c__, d__, e__, f__], x_) && ltq!(m_, -1)
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let cos = angle.cos();
            let recursive_integrand = linear.pow(&m_ + 1) * &cos;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(linear.pow(&m_ + 1) * sin / (&d__ * (&m_ + 1))), x_)
                    + rubi_star(-&f__ / (&d__ * (&m_ + 1)), recursive)
        },
    ));
}

fn push_rules_rule_3779(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; c__, d__, e__, f__, z_, x_);
    rules.push(rubi_rule!(
        order: 3779,
        source: "Int[sin[e_.+f_.*Complex[0,fz_]*x_]/(c_.+d_.*x_),x_Symbol] :=
          I*SinhIntegral[c*f*fz/d+f*fz*x]/d /;
        FreeQ[{c,d,e,f,fz},x] && EqQ[d*e-c*f*fz*I,0]",
        desc: "Primitive rule",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [e__, f__, z_, c__, d__, x_],
        optional: [e__, f__, c__, d__],
        when: {
            freeq!([c__, d__, e__, f__, z_], x_)
                && eqq!(&d__ * &e__ - &c__ * &f__ * &z_ * rubi_i(), 0)
        },
        rhs: {
            rubi_simp(&(rubi_i()
                    * rubi_sinh_integral(&c__ * &f__ * &z_ / &d__ + &f__ * &z_ * x_)
                    / &d__), x_)
        },
    ));
}

fn push_rules_rule_3780(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 3780,
        source: "Int[sin[e_.+f_.*x_]/(c_.+d_.*x_),x_Symbol] :=
          SinIntegral[e+f*x]/d /;
        FreeQ[{c,d,e,f},x] && EqQ[d*e-c*f,0]",
        desc: "Primitive rule",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [e__, f__, c__, d__, x_],
        optional: [e__, f__, c__, d__],
        when: {
            freeq!([c__, d__, e__, f__], x_)
                && eqq!(&d__ * &e__ - &c__ * &f__, 0)
        },
        rhs: {
            rubi_simp(&(rubi_sin_integral(&e__ + &f__ * x_) / &d__), x_)
        },
    ));
}

fn push_rules_rule_3781(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; c__, d__, e__, f__, z_, x_);
    rules.push(rubi_rule!(
        order: 3781,
        source: "Int[sin[e_.+f_.*Complex[0,fz_]*x_]/(c_.+d_.*x_),x_Symbol] :=
          CoshIntegral[-c*f*fz/d-f*fz*x]/d /;
        FreeQ[{c,d,e,f,fz},x] && EqQ[d*(e-Pi/2)-c*f*fz*I,0] && NegQ[c*f*fz/d,0]",
        desc: "Primitive rule",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [e__, f__, z_, c__, d__, x_],
        optional: [e__, f__, c__, d__],
        when: {
            freeq!([c__, d__, e__, f__, z_], x_)
                && eqq!(
                    &d__ * (&e__ - Atom::var(Symbol::PI) / 2)
                        - &c__ * &f__ * &z_ * rubi_i(),
                    0
                )
                && negq!(&c__ * &f__ * &z_ / &d__)
        },
        rhs: {
            rubi_simp(&(rubi_cosh_integral(-&c__ * &f__ * &z_ / &d__ - &f__ * &z_ * x_) / &d__), x_)
        },
    ));
}

fn push_rules_rule_3782(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; c__, d__, e__, f__, z_, x_);
    rules.push(rubi_rule!(
        order: 3782,
        source: "Int[sin[e_.+f_.*Complex[0,fz_]*x_]/(c_.+d_.*x_),x_Symbol] :=
          CoshIntegral[c*f*fz/d+f*fz*x]/d /;
        FreeQ[{c,d,e,f,fz},x] && EqQ[d*(e-Pi/2)-c*f*fz*I,0]",
        desc: "Primitive rule",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [e__, f__, z_, c__, d__, x_],
        optional: [e__, f__, c__, d__],
        when: {
            freeq!([c__, d__, e__, f__, z_], x_)
                && eqq!(
                    &d__ * (&e__ - Atom::var(Symbol::PI) / 2)
                        - &c__ * &f__ * &z_ * rubi_i(),
                    0
                )
        },
        rhs: {
            rubi_simp(&(rubi_cosh_integral(&c__ * &f__ * &z_ / &d__ + &f__ * &z_ * x_) / &d__), x_)
        },
    ));
}

fn push_rules_rule_3783(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 3783,
        source: "Int[sin[e_.+f_.*x_]/(c_.+d_.*x_),x_Symbol] :=
          CosIntegral[e-Pi/2+f*x]/d /;
        FreeQ[{c,d,e,f},x] && EqQ[d*(e-Pi/2)-c*f,0]",
        desc: "Primitive rule",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [e__, f__, c__, d__, x_],
        optional: [e__, f__, c__, d__],
        when: {
            freeq!([c__, d__, e__, f__], x_)
                && eqq!(&d__ * (&e__ - Atom::var(Symbol::PI) / 2) - &c__ * &f__, 0)
        },
        rhs: {
            rubi_simp(&(rubi_cos_integral(&e__ - Atom::var(Symbol::PI) / 2 + &f__ * x_) / &d__), x_)
        },
    ));
}

fn push_rules_rule_3784(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 3784,
        source: "Int[sin[e_.+f_.*x_]/(c_.+d_.*x_),x_Symbol] :=
          Cos[(d*e-c*f)/d] \\[Star] Int[Sin[c*f/d+f*x]/(c+d*x),x] +
          Sin[(d*e-c*f)/d] \\[Star] Int[Cos[c*f/d+f*x]/(c+d*x),x] /;
        FreeQ[{c,d,e,f},x] && NeQ[d*e-c*f,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [e__, f__, c__, d__, x_],
        optional: [e__, f__, c__, d__],
        when: {
            freeq!([c__, d__, e__, f__], x_)
                && neq!(&d__ * &e__ - &c__ * &f__, 0)
        },
        rhs: {
            let shifted_angle = &c__ * &f__ / &d__ + &f__ * x_;
            let denominator = &c__ + &d__ * x_;
            let phase = (&d__ * &e__ - &c__ * &f__) / &d__;
            let recursive1 = rubi_rhs_int(&(shifted_angle.sin() / &denominator), x_);
            let recursive2 = rubi_rhs_int(&(shifted_angle.cos() / denominator), x_);

            rubi_star(&phase.cos(), recursive1)
                    + rubi_star(phase.sin(), recursive2)
        },
    ));
}

fn push_rules_rule_3785(rules: &mut Vec<RubiRule>) {
    rubi_symb!(c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 3785,
        source: "Int[sin[e_.+Pi/2+f_.*x_]/Sqrt[c_.+d_.*x_],x_Symbol] :=
          2/d \\[Star] Subst[Int[Cos[f*x^2/d],x],x,Sqrt[c+d*x]] /;
        FreeQ[{c,d,e,f},x] && ComplexFreeQ[f] && EqQ[d*e-c*f,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: i_sin(e__ + Atom::var(Symbol::PI) / 2 + f__ * x_) / (c__ + d__ * x_).sqrt(),
        with: [e__, f__, c__, d__, x_],
        optional: [e__, f__, c__, d__],
        when: {
            freeq!([c__, d__, e__, f__], x_)
                && rubi_complex_free_q(&f__)
                && eqq!(&d__ * &e__ - &c__ * &f__, 0)
        },
        rhs: {
            let subst_guard = fresh_substitution_symbol().unwrap();
            let sub = subst_guard.symbol();
            let t = Atom::var(sub);
            let transformed_integrand = (&f__ * t.pow(2) / &d__).cos();
            let transformed_primitive = rubi_rhs_int(&transformed_integrand, sub);

            rubi_star(Atom::num(2) / &d__, rubi_subst(
                    &transformed_primitive,
                    sub,
                    (&c__ + &d__ * x_).sqrt(),
                ))
        },
    ));
}

fn push_rules_rule_3786(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 3786,
        source: "Int[sin[e_.+f_.*x_]/Sqrt[c_.+d_.*x_],x_Symbol] :=
          2/d \\[Star] Subst[Int[Sin[f*x^2/d],x],x,Sqrt[c+d*x]] /;
        FreeQ[{c,d,e,f},x] && ComplexFreeQ[f] && EqQ[d*e-c*f,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [e__, f__, c__, d__, x_],
        optional: [e__, f__, c__, d__],
        when: {
            freeq!([c__, d__, e__, f__], x_)
                && rubi_complex_free_q(&f__)
                && eqq!(&d__ * &e__ - &c__ * &f__, 0)
        },
        rhs: {
            let subst_guard = fresh_substitution_symbol().unwrap();
            let sub = subst_guard.symbol();
            let t = Atom::var(sub);
            let transformed_integrand = (&f__ * t.pow(2) / &d__).sin();
            let transformed_primitive = rubi_rhs_int(&transformed_integrand, sub);

            rubi_star(Atom::num(2) / &d__, rubi_subst(
                    &transformed_primitive,
                    sub,
                    (&c__ + &d__ * x_).sqrt(),
                ))
        },
    ));
}

fn push_rules_rule_3787(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 3787,
        source: "Int[sin[e_.+f_.*x_]/Sqrt[c_.+d_.*x_],x_Symbol] :=
          Cos[(d*e-c*f)/d] \\[Star] Int[Sin[c*f/d+f*x]/Sqrt[c+d*x],x] +
          Sin[(d*e-c*f)/d] \\[Star] Int[Cos[c*f/d+f*x]/Sqrt[c+d*x],x] /;
        FreeQ[{c,d,e,f},x] && ComplexFreeQ[f] && NeQ[d*e-c*f,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [e__, f__, c__, d__, x_],
        optional: [e__, f__, c__, d__],
        when: {
            freeq!([c__, d__, e__, f__], x_)
                && rubi_complex_free_q(&f__)
                && neq!(&d__ * &e__ - &c__ * &f__, 0)
        },
        rhs: {
            let shifted_angle = &c__ * &f__ / &d__ + &f__ * x_;
            let denominator = (&c__ + &d__ * x_).sqrt();
            let phase = (&d__ * &e__ - &c__ * &f__) / &d__;
            let recursive1 = rubi_rhs_int(&(shifted_angle.sin() / &denominator), x_);
            let recursive2 = rubi_rhs_int(&(shifted_angle.cos() / denominator), x_);

            rubi_star(&phase.cos(), recursive1)
                    + rubi_star(phase.sin(), recursive2)
        },
    ));
}

fn push_rules_rule_3788(rules: &mut Vec<RubiRule>) {
    rubi_symb!(c__, d__, e__, f__, k__, m_, x_);
    rules.push(rubi_rule!(
        order: 3788,
        source: "Int[(c_.+d_.*x_)^m_.*sin[e_.+k_.*Pi+f_.*x_],x_Symbol] :=
          I/2 \\[Star] Int[(c+d*x)^m*E^(-I*k*Pi)*E^(-I*(e+f*x)),x] - I/2 \\[Star] Int[(c+d*x)^m*E^(I*k*Pi)*E^(I*(e+f*x)),x] /;
        FreeQ[{c,d,e,f,m},x] && IntegerQ[2*k]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (c__ + d__ * x_).pow(m_) * i_sin(e__ + k__ * Atom::var(Symbol::PI) + f__ * x_),
        with: [c__, d__, m_, e__, k__, f__, x_],
        optional: [c__, d__, e__, k__, f__, m_],
        when: {
            freeq!([c__, d__, e__, f__, m_], x_)
                && integerq!(Atom::num(2) * &k__)
        },
        rhs: {
            let i = rubi_i();
            let linear = (&c__ + &d__ * x_).pow(&m_);
            let angle = &e__ + &f__ * x_;
            let recursive1 = rubi_rhs_int(
                &(&linear * (-&i * &k__ * Atom::var(Symbol::PI)).exp() * (-&i * &angle).exp()),
                x_,
            );
            let recursive2 = rubi_rhs_int(
                &(&linear * (&i * &k__ * Atom::var(Symbol::PI)).exp() * (&i * angle).exp()),
                x_,
            );

            rubi_star(&i / 2, recursive1)
                    + rubi_star(-i / 2, recursive2)
        },
    ));
}

fn push_rules_rule_3789(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; c__, d__, e__, f__, m_, x_);
    rules.push(rubi_rule!(
        order: 3789,
        source: "Int[(c_.+d_.*x_)^m_.*sin[e_.+f_.*x_],x_Symbol] :=
          I/2 \\[Star] Int[(c+d*x)^m*E^(-I*(e+f*x)),x] - I/2 \\[Star] Int[(c+d*x)^m*E^(I*(e+f*x)),x] /;
        FreeQ[{c,d,e,f,m},x]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [c__, d__, m_, e__, f__, x_],
        optional: [c__, d__, e__, f__, m_],
        when: {
            freeq!([c__, d__, e__, f__, m_], x_)
        },
        rhs: {
            let i = rubi_i();
            let linear = (&c__ + &d__ * x_).pow(&m_);
            let angle = &e__ + &f__ * x_;
            let recursive1 =
                rubi_rhs_int(&(&linear * (-&i * &angle).exp()), x_);
            let recursive2 = rubi_rhs_int(&(linear * (&i * angle).exp()), x_);

            rubi_star(&i / 2, recursive1)
                    + rubi_star(-i / 2, recursive2)
        },
    ));
}

fn push_rules_rule_3790(rules: &mut Vec<RubiRule>) {
    rubi_symb!(c__, d__, e__, f__, m_, x_);
    rules.push(rubi_rule!(
        order: 3790,
        source: "Int[(c_.+d_.*x_)^m_.*sin[e_.+f_.*x_/2]^2,x_Symbol] :=
          1/2 \\[Star] Int[(c+d*x)^m,x] - 1/2 \\[Star] Int[(c+d*x)^m*Cos[2*e+f*x],x] /;
        FreeQ[{c,d,e,f,m},x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (c__ + d__ * x_).pow(m_) * i_sin(e__ + f__ * x_ / 2).pow(2),
        with: [c__, d__, m_, e__, f__, x_],
        optional: [c__, d__, e__, f__, m_],
        when: {
            freeq!([c__, d__, e__, f__, m_], x_)
        },
        rhs: {
            let linear_power = (&c__ + &d__ * x_).pow(&m_);
            let recursive1 = rubi_rhs_int(&linear_power, x_);
            let recursive2 = rubi_rhs_int(
                &(linear_power * (Atom::num(2) * &e__ + &f__ * x_).cos()),
                x_,
            );

            rubi_star(Atom::num(1) / 2, recursive1)
                    + rubi_star(Atom::num(-1) / 2, recursive2)
        },
    ));
}

fn push_rules_rule_3791(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; b__, c__, d__, e__, f__, n_, x_);
    rules.push(rubi_rule!(
        order: 3791,
        source: "Int[(c_.+d_.*x_)*(b_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
          d*(b*Sin[e+f*x])^n/(f^2*n^2) -
          b*(c+d*x)*Cos[e+f*x]*(b*Sin[e+f*x])^(n-1)/(f*n) +
          b^2*(n-1)/n \\[Star] Int[(c+d*x)*(b*Sin[e+f*x])^(n-2),x] /;
        FreeQ[{b,c,d,e,f},x] && GtQ[n,1]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: ["G&R 2.631.2 with m\\[Rule]1", "G&R 2.631.3 with m\\[Rule]1"],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [c__, d__, b__, e__, f__, n_, x_],
        optional: [c__, d__, b__, e__, f__],
        when: {
            freeq!([b__, c__, d__, e__, f__], x_) && gtq!(n_, 1)
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let angle = &e__ + &f__ * x_;
            let scaled_sin = &b__ * angle.sin();
            let recursive_integrand = &linear * scaled_sin.pow(&n_ - 2);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(&d__ * scaled_sin.pow(&n_) / (f__.pow(2) * n_.pow(2))), x_)
                    - rubi_simp(&(&b__ * linear * angle.cos() * scaled_sin.pow(&n_ - 1) / (&f__ * &n_)), x_)
                    + rubi_star(b__.pow(2) * (&n_ - 1) / &n_, recursive)
        },
    ));
}

fn push_rules_rule_3792(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 3792,
        source: "Int[(c_.+d_.*x_)^m_*(b_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
          d*m*(c+d*x)^(m-1)*(b*Sin[e+f*x])^n/(f^2*n^2) -
          b*(c+d*x)^m*Cos[e+f*x]*(b*Sin[e+f*x])^(n-1)/(f*n) +
          b^2*(n-1)/n \\[Star] Int[(c+d*x)^m*(b*Sin[e+f*x])^(n-2),x] -
          d^2*m*(m-1)/(f^2*n^2) \\[Star] Int[(c+d*x)^(m-2)*(b*Sin[e+f*x])^n,x] /;
        FreeQ[{b,c,d,e,f},x] && GtQ[n,1] && GtQ[m,1]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: ["G&R 2.631.2", "G&R 2.631.3"],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [c__, d__, m_, b__, e__, f__, n_, x_],
        optional: [c__, d__, b__, e__, f__],
        when: {
            freeq!([b__, c__, d__, e__, f__], x_)
                && gtq!(n_, 1)
                && gtq!(m_, 1)
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let angle = &e__ + &f__ * x_;
            let scaled_sin = &b__ * angle.sin();
            let recursive1_integrand = linear.pow(&m_) * scaled_sin.pow(&n_ - 2);
            let recursive1 = rubi_rhs_int(&recursive1_integrand, x_);
            let recursive2_integrand = linear.pow(&m_ - 2) * scaled_sin.pow(&n_);
            let recursive2 = rubi_rhs_int(&recursive2_integrand, x_);

            rubi_simp(&(&d__ * &m_ * linear.pow(&m_ - 1) * scaled_sin.pow(&n_) / (f__.pow(2) * n_.pow(2))), x_)
                    - rubi_simp(&(&b__ * linear.pow(&m_) * angle.cos() * scaled_sin.pow(&n_ - 1) / (&f__ * &n_)), x_)
                    + rubi_star(b__.pow(2) * (&n_ - 1) / &n_, recursive1)
                    + rubi_star(-d__.pow(2) * &m_ * (&m_ - 1)
                            / (f__.pow(2) * n_.pow(2)), recursive2)
        },
    ));
}

fn push_rules_rule_3793(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 3793,
        source: "Int[(c_.+d_.*x_)^m_*sin[e_.+f_.*x_]^n_,x_Symbol] :=
          Int[ExpandTrigReduce[(c+d*x)^m,Sin[e+f*x]^n,x],x] /;
        FreeQ[{c,d,e,f,m},x] && IGtQ[n,1] && (Not[RationalQ[m]] || GeQ[m,-1] && LtQ[m,1])",
        desc: "Reduce the trigonometric expression and integrate the result.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [c__, d__, m_, e__, f__, n_, x_],
        optional: [c__, d__, e__, f__],
        when: {
            freeq!([c__, d__, e__, f__, m_], x_)
                && igtq!(n_, 1)
                && (!rationalq!(m_) || geq!(m_, -1) && ltq!(m_, 1))
        },
        rhs: {
            let expanded = rubi_expand_trig_reduce(
                &(&c__ + &d__ * x_).pow(&m_),
                &(e__ + &f__ * x_).sin().pow(&n_),
                x_,
            );

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_3794(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 3794,
        source: "Int[(c_.+d_.*x_)^m_*sin[e_.+f_.*x_]^n_,x_Symbol] :=
          (c+d*x)^(m+1)*Sin[e+f*x]^n/(d*(m+1)) -
          f*n/(d*(m+1)) \\[Star] Int[ExpandTrigReduce[(c+d*x)^(m+1),Cos[e+f*x]*Sin[e+f*x]^(n-1),x],x] /;
        FreeQ[{c,d,e,f,m},x] && IGtQ[n,1] && GeQ[m,-2] && LtQ[m,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [c__, d__, m_, e__, f__, n_, x_],
        optional: [c__, d__, e__, f__],
        when: {
            freeq!([c__, d__, e__, f__, m_], x_)
                && igtq!(n_, 1)
                && geq!(m_, -2)
                && ltq!(m_, -1)
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let angle = &e__ + &f__ * x_;
            let expanded = rubi_expand_trig_reduce(
                &linear.pow(&m_ + 1),
                &(angle.cos() * angle.sin().pow(&n_ - 1)),
                x_,
            );
            let recursive = rubi_rhs_int(&expanded, x_);

            rubi_simp(&(linear.pow(&m_ + 1) * angle.sin().pow(&n_) / (&d__ * (&m_ + 1))), x_)
                    + rubi_star(-&f__ * &n_ / (&d__ * (&m_ + 1)), recursive)
        },
    ));
}

fn push_rules_rule_3795(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 3795,
        source: "Int[(c_.+d_.*x_)^m_*(b_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
          (c+d*x)^(m+1)*(b*Sin[e+f*x])^n/(d*(m+1)) -
          b*f*n*(c+d*x)^(m+2)*Cos[e+f*x]*(b*Sin[e+f*x])^(n-1)/(d^2*(m+1)*(m+2)) -
          f^2*n^2/(d^2*(m+1)*(m+2)) \\[Star] Int[(c+d*x)^(m+2)*(b*Sin[e+f*x])^n,x] +
          b^2*f^2*n*(n-1)/(d^2*(m+1)*(m+2)) \\[Star] Int[(c+d*x)^(m+2)*(b*Sin[e+f*x])^(n-2),x] /;
        FreeQ[{b,c,d,e,f},x] && GtQ[n,1] && LtQ[m,-2]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: ["G&R 2.638.1", "G&R 2.638.2"],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [c__, d__, m_, b__, e__, f__, n_, x_],
        optional: [c__, d__, b__, e__, f__],
        when: {
            freeq!([b__, c__, d__, e__, f__], x_)
                && gtq!(n_, 1)
                && ltq!(m_, -2)
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let angle = &e__ + &f__ * x_;
            let scaled_sin = &b__ * angle.sin();
            let recursive1_integrand = linear.pow(&m_ + 2) * scaled_sin.pow(&n_);
            let recursive1 = rubi_rhs_int(&recursive1_integrand, x_);
            let recursive2_integrand = linear.pow(&m_ + 2) * scaled_sin.pow(&n_ - 2);
            let recursive2 = rubi_rhs_int(&recursive2_integrand, x_);

            rubi_simp(&(linear.pow(&m_ + 1) * scaled_sin.pow(&n_) / (&d__ * (&m_ + 1))), x_)
                    - rubi_simp(&(&b__ * &f__ * &n_ * linear.pow(&m_ + 2) * angle.cos() * scaled_sin.pow(&n_ - 1)
                        / (d__.pow(2) * (&m_ + 1) * (&m_ + 2))), x_)
                    + rubi_star(-f__.pow(2) * n_.pow(2)
                            / (d__.pow(2) * (&m_ + 1) * (&m_ + 2)), recursive1)
                    + rubi_star(b__.pow(2) * f__.pow(2) * &n_ * (&n_ - 1)
                            / (d__.pow(2) * (&m_ + 1) * (&m_ + 2)), recursive2)
        },
    ));
}

fn push_rules_rule_3796(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; b__, c__, d__, e__, f__, n_, x_);
    rules.push(rubi_rule!(
        order: 3796,
        source: "Int[(c_.+d_.*x_)*(b_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
          (c+d*x)*Cos[e+f*x]*(b*Sin[e+f*x])^(n+1)/(b*f*(n+1)) -
          d*(b*Sin[e+f*x])^(n+2)/(b^2*f^2*(n+1)*(n+2)) +
          (n+2)/(b^2*(n+1)) \\[Star] Int[(c+d*x)*(b*Sin[e+f*x])^(n+2),x] /;
        FreeQ[{b,c,d,e,f},x] && LtQ[n,-1] && NeQ[n,-2]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: ["G&R 2.643.1 with m\\[Rule]1", "G&R 2.643.2 with m\\[Rule]1"],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [c__, d__, b__, e__, f__, n_, x_],
        optional: [c__, d__, b__, e__, f__],
        when: {
            freeq!([b__, c__, d__, e__, f__], x_)
                && ltq!(n_, -1)
                && neq!(n_, -2)
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let angle = &e__ + &f__ * x_;
            let scaled_sin = &b__ * angle.sin();
            let recursive_integrand = &linear * scaled_sin.pow(&n_ + 2);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(linear * angle.cos() * scaled_sin.pow(&n_ + 1)
                    / (&b__ * &f__ * (&n_ + 1))), x_)
                    - rubi_simp(&(&d__ * scaled_sin.pow(&n_ + 2)
                        / (b__.pow(2) * f__.pow(2) * (&n_ + 1) * (&n_ + 2))), x_)
                    + rubi_star((&n_ + 2) / (b__.pow(2) * (&n_ + 1)), recursive)
        },
    ));
}

fn push_rules_rule_3797(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 3797,
        source: "Int[(c_.+d_.*x_)^m_.*(b_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
          (c+d*x)^m*Cos[e+f*x]*(b*Sin[e+f*x])^(n+1)/(b*f*(n+1)) -
          d*m*(c+d*x)^(m-1)*(b*Sin[e+f*x])^(n+2)/(b^2*f^2*(n+1)*(n+2)) +
          (n+2)/(b^2*(n+1)) \\[Star] Int[(c+d*x)^m*(b*Sin[e+f*x])^(n+2),x] +
          d^2*m*(m-1)/(b^2*f^2*(n+1)*(n+2)) \\[Star] Int[(c+d*x)^(m-2)*(b*Sin[e+f*x])^(n+2),x] /;
        FreeQ[{b,c,d,e,f},x] && LtQ[n,-1] && NeQ[n,-2] && GtQ[m,1]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: ["G&R 2.643.1", "G&R 2.643.2"],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [c__, d__, m_, b__, e__, f__, n_, x_],
        optional: [c__, d__, m_, b__, e__, f__],
        when: {
            freeq!([b__, c__, d__, e__, f__], x_)
                && ltq!(n_, -1)
                && neq!(n_, -2)
                && gtq!(m_, 1)
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let angle = &e__ + &f__ * x_;
            let scaled_sin = &b__ * angle.sin();
            let recursive1_integrand = linear.pow(&m_) * scaled_sin.pow(&n_ + 2);
            let recursive1 = rubi_rhs_int(&recursive1_integrand, x_);
            let recursive2_integrand = linear.pow(&m_ - 2) * scaled_sin.pow(&n_ + 2);
            let recursive2 = rubi_rhs_int(&recursive2_integrand, x_);

            rubi_simp(&(linear.pow(&m_) * angle.cos() * scaled_sin.pow(&n_ + 1)
                    / (&b__ * &f__ * (&n_ + 1))), x_)
                    - rubi_simp(&(&d__ * &m_ * linear.pow(&m_ - 1) * scaled_sin.pow(&n_ + 2)
                        / (b__.pow(2) * f__.pow(2) * (&n_ + 1) * (&n_ + 2))), x_)
                    + rubi_star((&n_ + 2) / (b__.pow(2) * (&n_ + 1)), recursive1)
                    + rubi_star(d__.pow(2) * &m_ * (&m_ - 1)
                            / (b__.pow(2) * f__.pow(2) * (&n_ + 1) * (&n_ + 2)), recursive2)
        },
    ));
}

fn push_rules_rule_3798(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 3798,
        source: "Int[(c_.+d_.*x_)^m_.*(a_+b_.*sin[e_.+f_.*x_])^n_.,x_Symbol] :=
          Int[ExpandIntegrand[(c+d*x)^m,(a+b*Sin[e+f*x])^n,x],x] /;
        FreeQ[{a,b,c,d,e,f,m},x] && IGtQ[n,0] && (EqQ[n,1] || IGtQ[m,0] || NeQ[a^2-b^2,0])",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [c__, d__, m_, a__, b__, e__, f__, n_, x_],
        optional: [c__, d__, m_, b__, e__, f__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_], x_)
                && igtq!(n_, 0)
                && (eqq!(n_, 1) || igtq!(m_, 0) || neq!(a__.pow(2) - b__.pow(2), 0))
        },
        rhs: {
            let expanded = rubi_expand_integrand_product(
                &(&c__ + &d__ * x_).pow(&m_),
                &(&a__ + &b__ * (&e__ + &f__ * x_).sin()).pow(&n_),
                x_,
            );

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_3799(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 3799,
        source: "Int[(c_.+d_.*x_)^m_.*(a_+b_.*sin[e_.+f_.*x_])^n_.,x_Symbol] :=
          (2*a)^n \\[Star] Int[(c+d*x)^m*Sin[1/2*(e+Pi*a/(2*b))+f*x/2]^(2*n),x] /;
        FreeQ[{a,b,c,d,e,f,m},x] && EqQ[a^2-b^2,0] && IntegerQ[n] && (GtQ[n,0] || IGtQ[m,0])",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [c__, d__, m_, a__, b__, e__, f__, n_, x_],
        optional: [c__, d__, m_, b__, e__, f__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_], x_)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && integerq!(n_)
                && (gtq!(n_, 0) || igtq!(m_, 0))
        },
        rhs: {
            let linear = (&c__ + &d__ * x_).pow(&m_);
            let angle =
                (&e__ + Atom::var(Symbol::PI) * &a__ / (Atom::num(2) * &b__)) / 2 + &f__ * x_ / 2;
            let recursive_integrand = linear * angle.sin().pow(Atom::num(2) * &n_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star((Atom::num(2) * &a__).pow(&n_), recursive)
        },
    ));
}

fn push_rules_rule_3800(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 3800,
        source: "Int[(c_.+d_.*x_)^m_.*(a_+b_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
          (2*a)^IntPart[n]*(a+b*Sin[e+f*x])^FracPart[n]/Sin[e/2+a*Pi/(4*b)+f*x/2]^(2*FracPart[n]) \\[Star]
            Int[(c+d*x)^m*Sin[e/2+a*Pi/(4*b)+f*x/2]^(2*n),x] /;
        FreeQ[{a,b,c,d,e,f,m},x] && EqQ[a^2-b^2,0] && IntegerQ[n+1/2] && (GtQ[n,0] || IGtQ[m,0])",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [c__, d__, m_, a__, b__, e__, f__, n_, x_],
        optional: [c__, d__, m_, b__, e__, f__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_], x_)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && integerq!(&n_ + Atom::num(1) / Atom::num(2))
                && (gtq!(n_, 0) || igtq!(m_, 0))
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let reduced_angle = &e__ / 2 + &a__ * Atom::var(Symbol::PI) / (Atom::num(4) * &b__)
                + &f__ * x_ / 2;
            let frac_n = rubi_frac_part(&n_);
            let recursive_integrand =
                (&c__ + &d__ * x_).pow(&m_) * reduced_angle.sin().pow(Atom::num(2) * &n_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star((Atom::num(2) * &a__).pow(rubi_int_part(&n_))
                    * (&a__ + &b__ * angle.sin()).pow(&frac_n)
                    / reduced_angle.sin().pow(Atom::num(2) * frac_n), recursive)
        },
    ));
}

fn push_rules_rule_3801(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, k__, m_, z_, x_);
    rules.push(rubi_rule!(
        order: 3801,
        source: "Int[(c_.+d_.*x_)^m_./(a_+b_.*sin[e_.+k_.*Pi+f_.*Complex[0,fz_]*x_]),x_Symbol] :=
          2 \\[Star] Int[(c+d*x)^m*E^(-I*Pi*(k-1/2))*E^(-I*e+f*fz*x)/(b+2*a*E^(-I*Pi*(k-1/2))*E^(-I*e+f*fz*x)-b*E^(-2*I*k*Pi)*E^(2*(-I*e+f*fz*x))),x] /;
        FreeQ[{a,b,c,d,e,f,fz},x] && IntegerQ[2*k] && NeQ[a^2-b^2,0] && IGtQ[m,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (c__ + d__ * x_).pow(m_)
            / (a__
                + b__
                    * i_sin(
                        e__ + Atom::var(Symbol::PI) * k__ + rubi_i() * Atom::var(z_) * f__ * x_,
                    )),
        with: [c__, d__, m_, a__, b__, e__, k__, z_, f__, x_],
        optional: [c__, d__, m_, b__, e__, k__, f__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, z_], x_)
                && integerq!(Atom::num(2) * &k__)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && igtq!(m_, 0)
        },
        rhs: {
            let i = rubi_i();
            let exponential = (-&i * &e__ + &f__ * &z_ * x_).exp();
            let phase = rubi_exp_i_pi_multiple(&(&k__ - Atom::num(1) / 2));
            let denominator = &b__ + Atom::num(2) * &a__ * &exponential / &phase
                - &b__ * exponential.pow(2) / rubi_exp_two_i_pi_multiple(&k__);
            let recursive_integrand =
                (&c__ + &d__ * x_).pow(&m_) * exponential / denominator / phase;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            rubi_star(Atom::num(2), recursive)
        },
    ));
}

fn push_rules_rule_3802(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, k__, m_, x_);
    rules.push(rubi_rule!(
        order: 3802,
        source: "Int[(c_.+d_.*x_)^m_./(a_+b_.*sin[e_.+k_.*Pi+f_.*x_]),x_Symbol] :=
          2 \\[Star] Int[(c+d*x)^m*E^(I*Pi*(k-1/2))*E^(I*(e+f*x))/(b+2*a*E^(I*Pi*(k-1/2))*E^(I*(e+f*x))-b*E^(2*I*k*Pi)*E^(2*I*(e+f*x))),x] /;
        FreeQ[{a,b,c,d,e,f},x] && IntegerQ[2*k] && NeQ[a^2-b^2,0] && IGtQ[m,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (c__ + d__ * x_).pow(m_) / (a__ + b__ * i_sin(e__ + k__ * Atom::var(Symbol::PI) + f__ * x_)),
        with: [c__, d__, m_, a__, b__, e__, k__, f__, x_],
        optional: [c__, d__, m_, b__, e__, k__, f__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && integerq!(Atom::num(2) * &k__)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && igtq!(m_, 0)
        },
        rhs: {
            let i = rubi_i();
            let linear_power = (&c__ + &d__ * x_).pow(&m_);
            let phase_exp = rubi_exp_i_pi_multiple(&(&k__ - Atom::num(1) / Atom::num(2)));
            let angle_exp = (&i * (&e__ + &f__ * x_)).exp();
            let denominator = &b__
                + Atom::num(2) * &a__ * &phase_exp * &angle_exp
                - &b__ * rubi_exp_two_i_pi_multiple(&k__) * angle_exp.pow(2);
            let recursive_integrand = linear_power * phase_exp * angle_exp / denominator;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(Atom::num(2), recursive)
        },
    ));
}

fn push_rules_rule_3803(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, z_, x_);
    rules.push(rubi_rule!(
        order: 3803,
        source: "Int[(c_.+d_.*x_)^m_./(a_+b_.*sin[e_.+f_.*Complex[0,fz_]*x_]),x_Symbol] :=
          2 \\[Star] Int[(c+d*x)^m*E^(-I*e+f*fz*x)/(-I*b+2*a*E^(-I*e+f*fz*x)+I*b*E^(2*(-I*e+f*fz*x))),x] /;
        FreeQ[{a,b,c,d,e,f,fz},x] && NeQ[a^2-b^2,0] && IGtQ[m,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (c__ + d__ * x_).pow(m_)
            / (a__ + b__ * i_sin(e__ + rubi_i() * Atom::var(z_) * f__ * x_)),
        with: [c__, d__, m_, a__, b__, e__, z_, f__, x_],
        optional: [c__, d__, m_, b__, e__, f__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, z_], x_)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && igtq!(m_, 0)
        },
        rhs: {
            let i = rubi_i();
            let exponential = (-&i * &e__ + &f__ * &z_ * x_).exp();
            let denominator = -&i * &b__ + Atom::num(2) * &a__ * &exponential
                + &i * &b__ * exponential.pow(2);
            let recursive_integrand =
                (&c__ + &d__ * x_).pow(&m_) * exponential / denominator;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            rubi_star(Atom::num(2), recursive)
        },
    ));
}

fn push_rules_rule_3804(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, x_);
    rules.push(rubi_rule!(
        order: 3804,
        source: "Int[(c_.+d_.*x_)^m_./(a_+b_.*sin[e_.+f_.*x_]),x_Symbol] :=
          2 \\[Star] Int[(c+d*x)^m*E^(I*(e+f*x))/(I*b+2*a*E^(I*(e+f*x))-I*b*E^(2*I*(e+f*x))),x] /;
        FreeQ[{a,b,c,d,e,f},x] && NeQ[a^2-b^2,0] && IGtQ[m,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (c__ + d__ * x_).pow(m_) / (a__ + b__ * i_sin(e__ + f__ * x_)),
        with: [c__, d__, m_, a__, b__, e__, f__, x_],
        optional: [c__, d__, m_, b__, e__, f__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && igtq!(m_, 0)
        },
        rhs: {
            let i = rubi_i();
            let linear_power = (&c__ + &d__ * x_).pow(&m_);
            let angle_exp = (&i * (&e__ + &f__ * x_)).exp();
            let denominator = &i * &b__ + Atom::num(2) * &a__ * &angle_exp - &i * &b__ * angle_exp.pow(2);
            let recursive_integrand = linear_power * angle_exp / denominator;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(Atom::num(2), recursive)
        },
    ));
}

fn push_rules_rule_3805(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, x_);
    rules.push(rubi_rule!(
        order: 3805,
        source: "Int[(c_.+d_.*x_)^m_./(a_+b_.*sin[e_.+f_.*x_])^2,x_Symbol] :=
          b*(c+d*x)^m*Cos[e+f*x]/(f*(a^2-b^2)*(a+b*Sin[e+f*x])) +
          a/(a^2-b^2) \\[Star] Int[(c+d*x)^m/(a+b*Sin[e+f*x]),x] -
          b*d*m/(f*(a^2-b^2)) \\[Star] Int[(c+d*x)^(m-1)*Cos[e+f*x]/(a+b*Sin[e+f*x]),x] /;
        FreeQ[{a,b,c,d,e,f},x] && NeQ[a^2-b^2,0] && IGtQ[m,0]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern: (c__ + d__ * x_).pow(m_) / (a__ + b__ * i_sin(e__ + f__ * x_)).pow(2),
        with: [c__, d__, m_, a__, b__, e__, f__, x_],
        optional: [c__, d__, m_, b__, e__, f__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && igtq!(m_, 0)
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let angle = &e__ + &f__ * x_;
            let affine_sin = &a__ + &b__ * angle.sin();
            let discriminant = a__.pow(2) - b__.pow(2);
            let recursive1 = rubi_rhs_int(&(linear.pow(&m_) / &affine_sin), x_);
            let recursive2 = rubi_rhs_int(
                &(linear.pow(&m_ - 1) * angle.cos() / affine_sin),
                x_,
            );

            rubi_simp(&(&b__ * linear.pow(&m_) * angle.cos()
                    / (&f__ * &discriminant * (&a__ + &b__ * angle.sin()))), x_)
                    + rubi_star(&a__ / &discriminant, recursive1)
                    + rubi_star(-&b__ * &d__ * &m_ / (&f__ * discriminant), recursive2)
        },
    ));
}

fn push_rules_rule_3806(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 3806,
        source: "Int[(c_.+d_.*x_)^m_.*(a_+b_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
          -b*(c+d*x)^m*Cos[e+f*x]*(a+b*Sin[e+f*x])^(n+1)/(f*(n+1)*(a^2-b^2)) +
          a/(a^2-b^2) \\[Star] Int[(c+d*x)^m*(a+b*Sin[e+f*x])^(n+1),x] +
          b*d*m/(f*(n+1)*(a^2-b^2)) \\[Star] Int[(c+d*x)^(m-1)*Cos[e+f*x]*(a+b*Sin[e+f*x])^(n+1),x] -
          b*(n+2)/((n+1)*(a^2-b^2)) \\[Star] Int[(c+d*x)^m*Sin[e+f*x]*(a+b*Sin[e+f*x])^(n+1),x] /;
        FreeQ[{a,b,c,d,e,f},x] && NeQ[a^2-b^2,0] && ILtQ[n,-2] && IGtQ[m,0]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [c__, d__, m_, a__, b__, e__, f__, n_, x_],
        optional: [c__, d__, m_, b__, e__, f__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && iltq!(n_, -2)
                && igtq!(m_, 0)
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let angle = &e__ + &f__ * x_;
            let affine_sin = &a__ + &b__ * angle.sin();
            let discriminant = a__.pow(2) - b__.pow(2);
            let recursive1_integrand = linear.pow(&m_) * affine_sin.pow(&n_ + 1);
            let recursive1 = rubi_rhs_int(&recursive1_integrand, x_);
            let recursive2_integrand = linear.pow(&m_ - 1) * angle.cos() * affine_sin.pow(&n_ + 1);
            let recursive2 = rubi_rhs_int(&recursive2_integrand, x_);
            let recursive3_integrand = linear.pow(&m_) * angle.sin() * affine_sin.pow(&n_ + 1);
            let recursive3 = rubi_rhs_int(&recursive3_integrand, x_);

            rubi_simp(&(-&b__ * linear.pow(&m_) * angle.cos() * affine_sin.pow(&n_ + 1)
                    / (&f__ * (&n_ + 1) * &discriminant)), x_)
                    + rubi_star(&a__ / &discriminant, recursive1)
                    + rubi_star(&b__ * &d__ * &m_ / (&f__ * (&n_ + 1) * &discriminant), recursive2)
                    + rubi_star(-&b__ * (&n_ + 2) / ((&n_ + 1) * discriminant), recursive3)
        },
    ));
}

fn push_rules_rule_3807(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 3807,
        source: "Int[(c_.+d_.*x_)^m_.*(a_.+b_.*sin[e_.+f_.*x_])^n_.,x_Symbol] :=
          Unintegrable[(c+d*x)^m*(a+b*Sin[e+f*x])^n,x] /;
        FreeQ[{a,b,c,d,e,f,m,n},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [c__, d__, m_, a__, b__, e__, f__, n_, x_],
        optional: [c__, d__, m_, a__, b__, e__, f__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_], x_)
        },
        rhs: {
            let integrand = (&c__ + &d__ * x_).pow(&m_)
                * (&a__ + &b__ * (&e__ + &f__ * x_).sin()).pow(&n_);

            rubi_unintegrable(integrand, x_)
        },
    ));
}

fn push_rules_rule_3808(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, m_, n_, u_, v_);
    rules.push(rubi_rule!(
        order: 3808,
        source: "Int[u_^m_.*(a_.+b_.*Sin[v_])^n_.,x_Symbol] :=
          Int[ExpandToSum[u,x]^m*(a+b*Sin[ExpandToSum[v,x]])^n,x] /;
        FreeQ[{a,b,m,n},x] && LinearQ[{u,v},x] && Not[LinearMatchQ[{u,v},x]]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: u_.pow(m_) * (a__ + b__ * (Atom::var(v_)).sin()).pow(n_),
        with: [u_, m_, a__, b__, v_, n_, x_],
        optional: [m_, a__, b__, n_],
        when: {
            freeq!([a__, b__, m_, n_], x_)
                && rubi_linear_q_list(&[&u_, &v_], x_)
                && !rubi_linear_match_q_list(&[&u_, &v_], x_)
        },
        rhs: {
            let expanded_u = rubi_expand_to_sum(&u_, x_);
            let expanded_v = rubi_expand_to_sum(&v_, x_);
            let recursive_integrand =
                expanded_u.pow(&m_) * (&a__ + &b__ * expanded_v.sin()).pow(&n_);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_3809(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, m_, n_, u_, v_);
    rules.push(rubi_rule!(
        order: 3809,
        source: "Int[u_^m_.*(a_.+b_.*Cos[v_])^n_.,x_Symbol] :=
          Int[ExpandToSum[u,x]^m*(a+b*Cos[ExpandToSum[v,x]])^n,x] /;
        FreeQ[{a,b,m,n},x] && LinearQ[{u,v},x] && Not[LinearMatchQ[{u,v},x]]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: u_.pow(m_) * (a__ + b__ * (Atom::var(v_)).cos()).pow(n_),
        with: [u_, m_, a__, b__, v_, n_, x_],
        optional: [m_, a__, b__, n_],
        when: {
            freeq!([a__, b__, m_, n_], x_)
                && rubi_linear_q_list(&[&u_, &v_], x_)
                && !rubi_linear_match_q_list(&[&u_, &v_], x_)
        },
        rhs: {
            let expanded_u = rubi_expand_to_sum(&u_, x_);
            let expanded_v = rubi_expand_to_sum(&v_, x_);
            let recursive_integrand =
                expanded_u.pow(&m_) * (&a__ + &b__ * expanded_v.cos()).pow(&n_);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn downvalues_3777_through_3792_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .filter(|order| (3777..=3792).contains(order))
            .collect::<Vec<_>>();
        assert_eq!(orders, (3777..=3792).collect::<Vec<_>>());
    }

    #[test]
    fn downvalues_3793_through_3809_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .filter(|order| (3793..=3809).contains(order))
            .collect::<Vec<_>>();
        assert_eq!(orders, (3793..=3809).collect::<Vec<_>>());
    }
}

// Generated shared pattern builders.

#[inline(never)]
fn rubi_shared_pattern_0(symbols: &RubiSymbols) -> Atom {
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    (c__ + d__ * x_) * (b__ * i_sin(e__ + f__ * x_)).pow(n_)
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    (c__ + d__ * x_).pow(m_) * (a__ + b__ * i_sin(e__ + f__ * x_)).pow(n_)
}

#[inline(never)]
fn rubi_shared_pattern_2(symbols: &RubiSymbols) -> Atom {
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    (c__ + d__ * x_).pow(m_) * (b__ * i_sin(e__ + f__ * x_)).pow(n_)
}

#[inline(never)]
fn rubi_shared_pattern_3(symbols: &RubiSymbols) -> Atom {
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let x_ = symbols.x_;
    (c__ + d__ * x_).pow(m_) * i_sin(e__ + f__ * x_)
}

#[inline(never)]
fn rubi_shared_pattern_4(symbols: &RubiSymbols) -> Atom {
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    (c__ + d__ * x_).pow(m_) * i_sin(e__ + f__ * x_).pow(n_)
}

#[inline(never)]
fn rubi_shared_pattern_5(symbols: &RubiSymbols) -> Atom {
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let x_ = symbols.x_;
    let z_ = symbols.z_;
    i_sin(e__ + f__ * rubi_i() * Atom::var(z_) * x_) / (c__ + d__ * x_)
}

#[inline(never)]
fn rubi_shared_pattern_6(symbols: &RubiSymbols) -> Atom {
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let x_ = symbols.x_;
    i_sin(e__ + f__ * x_) / (c__ + d__ * x_)
}

#[inline(never)]
fn rubi_shared_pattern_7(symbols: &RubiSymbols) -> Atom {
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let x_ = symbols.x_;
    i_sin(e__ + f__ * x_) / (c__ + d__ * x_).sqrt()
}
