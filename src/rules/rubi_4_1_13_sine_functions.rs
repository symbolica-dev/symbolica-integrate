use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_3926(rules);
    push_rules_rule_3927(rules);
    push_rules_rule_3928(rules);
    push_rules_rule_3929(rules);
    push_rules_rule_3930(rules);
    push_rules_rule_3931(rules);
    push_rules_rule_3932(rules);
    push_rules_rule_3933(rules);
    push_rules_rule_3934(rules);
    push_rules_rule_3935(rules);
    push_rules_rule_3936(rules);
    push_rules_rule_3937(rules);
    push_rules_rule_3938(rules);
    push_rules_rule_3939(rules);
    push_rules_rule_3940(rules);
    push_rules_rule_3941(rules);
    push_rules_rule_3942(rules);
    push_rules_rule_3943(rules);
    push_rules_rule_3944(rules);
    push_rules_rule_3945(rules);
    push_rules_rule_3946(rules);
    push_rules_rule_3947(rules);
    push_rules_rule_3948(rules);
    push_rules_rule_3949(rules);
    push_rules_rule_3950(rules);
    push_rules_rule_3951(rules);
    push_rules_rule_3952(rules);
    push_rules_rule_3953(rules);
}

fn push_rules_rule_3926(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, x_);
    rules.push(rubi_rule!(
        order: 3926,
        source: "Int[Sin[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
          Int[Sin[(b+2*c*x)^2/(4*c)],x] /;
        FreeQ[{a,b,c},x] && EqQ[b^2-4*a*c,0]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, x_],
        optional: [a__, b__, c__],
        when: {
            freeq!([a__, b__, c__], x_)
                && eqq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
        },
        rhs: {
            let transformed_integrand = ((&b__ + Atom::num(2) * &c__ * x_).pow(2) / (Atom::num(4) * &c__)).sin();

            rubi_rhs_int(&transformed_integrand, x_)
        },
    ));
}

fn push_rules_rule_3927(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, x_);
    rules.push(rubi_rule!(
        order: 3927,
        source: "Int[Cos[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
          Int[Cos[(b+2*c*x)^2/(4*c)],x] /;
        FreeQ[{a,b,c},x] && EqQ[b^2-4*a*c,0]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, x_],
        optional: [a__, b__, c__],
        when: {
            freeq!([a__, b__, c__], x_)
                && eqq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
        },
        rhs: {
            let transformed_integrand = ((&b__ + Atom::num(2) * &c__ * x_).pow(2) / (Atom::num(4) * &c__)).cos();

            rubi_rhs_int(&transformed_integrand, x_)
        },
    ));
}

fn push_rules_rule_3928(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, x_);
    rules.push(rubi_rule!(
        order: 3928,
        source: "Int[Sin[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
          Cos[(b^2-4*a*c)/(4*c)] \\[Star] Int[Sin[(b+2*c*x)^2/(4*c)],x] -
          Sin[(b^2-4*a*c)/(4*c)] \\[Star] Int[Cos[(b+2*c*x)^2/(4*c)],x] /;
        FreeQ[{a,b,c},x] && NeQ[b^2-4*a*c,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, x_],
        optional: [a__, b__, c__],
        when: {
            freeq!([a__, b__, c__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
        },
        rhs: {
            let discriminant = (&b__ * &b__ - Atom::num(4) * &a__ * &c__) / (Atom::num(4) * &c__);
            let reduced_angle = (&b__ + Atom::num(2) * &c__ * x_).pow(2) / (Atom::num(4) * &c__);
            let recursive1 = rubi_rhs_int(&reduced_angle.sin(), x_);
            let recursive2 = rubi_rhs_int(&reduced_angle.cos(), x_);

            rubi_star(discriminant.cos(), recursive1)
                    + rubi_star(-discriminant.sin(), recursive2)
        },
    ));
}

fn push_rules_rule_3929(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, x_);
    rules.push(rubi_rule!(
        order: 3929,
        source: "Int[Cos[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
          Cos[(b^2-4*a*c)/(4*c)] \\[Star] Int[Cos[(b+2*c*x)^2/(4*c)],x] +
          Sin[(b^2-4*a*c)/(4*c)] \\[Star] Int[Sin[(b+2*c*x)^2/(4*c)],x] /;
        FreeQ[{a,b,c},x] && NeQ[b^2-4*a*c,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, x_],
        optional: [a__, b__, c__],
        when: {
            freeq!([a__, b__, c__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
        },
        rhs: {
            let discriminant = (&b__ * &b__ - Atom::num(4) * &a__ * &c__) / (Atom::num(4) * &c__);
            let reduced_angle = (&b__ + Atom::num(2) * &c__ * x_).pow(2) / (Atom::num(4) * &c__);
            let recursive1 = rubi_rhs_int(&reduced_angle.cos(), x_);
            let recursive2 = rubi_rhs_int(&reduced_angle.sin(), x_);

            rubi_star(discriminant.cos(), recursive1)
                    + rubi_star(discriminant.sin(), recursive2)
        },
    ));
}

fn push_rules_rule_3930(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, n_, x_);
    rules.push(rubi_rule!(
        order: 3930,
        source: "Int[Sin[a_.+b_.*x_+c_.*x_^2]^n_,x_Symbol] :=
          Int[ExpandTrigReduce[Sin[a+b*x+c*x^2]^n,x],x] /;
        FreeQ[{a,b,c},x] && IGtQ[n,1]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, n_, x_],
        optional: [a__, b__, c__],
        when: { freeq!([a__, b__, c__], x_) && igtq!(n_, 1) },
        rhs: {
            let integrand = (&a__ + &b__ * x_ + &c__ * x_.pow(2)).sin().pow(&n_);
            let expanded = rubi_expand_trig_reduce_one(&integrand, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_3931(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, n_, x_);
    rules.push(rubi_rule!(
        order: 3931,
        source: "Int[Cos[a_.+b_.*x_+c_.*x_^2]^n_,x_Symbol] :=
          Int[ExpandTrigReduce[Cos[a+b*x+c*x^2]^n,x],x] /;
        FreeQ[{a,b,c},x] && IGtQ[n,1]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, n_, x_],
        optional: [a__, b__, c__],
        when: { freeq!([a__, b__, c__], x_) && igtq!(n_, 1) },
        rhs: {
            let integrand = (&a__ + &b__ * x_ + &c__ * x_.pow(2)).cos().pow(&n_);
            let expanded = rubi_expand_trig_reduce_one(&integrand, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_3932(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, n_, x_);
    rules.push(rubi_rule!(
        order: 3932,
        source: "Int[Sin[a_.+b_.*x_+c_.*x_^2]^n_.,x_Symbol] :=
          Unintegrable[Sin[a+b*x+c*x^2]^n,x] /;
        FreeQ[{a,b,c,n},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, n_, x_],
        optional: [a__, b__, c__, n_],
        when: { freeq!([a__, b__, c__, n_], x_) },
        rhs: {
            let integrand = (&a__ + &b__ * x_ + &c__ * x_.pow(2)).sin().pow(&n_);

            rubi_unintegrable(integrand, x_)
        },
    ));
}

fn push_rules_rule_3933(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, n_, x_);
    rules.push(rubi_rule!(
        order: 3933,
        source: "Int[Cos[a_.+b_.*x_+c_.*x_^2]^n_.,x_Symbol] :=
          Unintegrable[Cos[a+b*x+c*x^2]^n,x] /;
        FreeQ[{a,b,c,n},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, n_, x_],
        optional: [a__, b__, c__, n_],
        when: { freeq!([a__, b__, c__, n_], x_) },
        rhs: {
            let integrand = (&a__ + &b__ * x_ + &c__ * x_.pow(2)).cos().pow(&n_);

            rubi_unintegrable(integrand, x_)
        },
    ));
}

fn push_rules_rule_3934(rules: &mut Vec<RubiRule>) {
    rubi_symb!(n_, v__);
    rules.push(rubi_rule!(
        order: 3934,
        source: "Int[Sin[v_]^n_.,x_Symbol] :=
          Int[Sin[ExpandToSum[v,x]]^n,x] /;
        IGtQ[n,0] && QuadraticQ[v,x] && Not[QuadraticMatchQ[v,x]]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: (Atom::var(v__)).sin().pow(n_),
        with: [v__, n_, x_],
        optional: [n_],
        when: { igtq!(n_, 0) && rubi_quadratic_q(&v__, x_) && !rubi_quadratic_match_q(&v__, x_) },
        rhs: {
            let integrand = rubi_expand_to_sum(&v__, x_).sin().pow(&n_);

            rubi_rhs_int(&integrand, x_)
        },
    ));
}

fn push_rules_rule_3935(rules: &mut Vec<RubiRule>) {
    rubi_symb!(n_, v__);
    rules.push(rubi_rule!(
        order: 3935,
        source: "Int[Cos[v_]^n_.,x_Symbol] :=
          Int[Cos[ExpandToSum[v,x]]^n,x] /;
        IGtQ[n,0] && QuadraticQ[v,x] && Not[QuadraticMatchQ[v,x]]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: (Atom::var(v__)).cos().pow(n_),
        with: [v__, n_, x_],
        optional: [n_],
        when: { igtq!(n_, 0) && rubi_quadratic_q(&v__, x_) && !rubi_quadratic_match_q(&v__, x_) },
        rhs: {
            let integrand = rubi_expand_to_sum(&v__, x_).cos().pow(&n_);

            rubi_rhs_int(&integrand, x_)
        },
    ));
}

fn push_rules_rule_3936(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 3936,
        source: "Int[(d_+e_.*x_)*Sin[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
          -e*Cos[a+b*x+c*x^2]/(2*c) /;
        FreeQ[{a,b,c,d,e},x] && EqQ[2*c*d-b*e,0]",
        desc: "Inverted integration by parts with m\\[Rule]1Bold",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [d__, e__, a__, b__, c__, x_],
        optional: [e__, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(Atom::num(2) * &c__ * &d__ - &b__ * &e__, 0)
        },
        rhs: {
            rubi_simp(&(-&e__ * (&a__ + &b__ * x_ + &c__ * x_.pow(2)).cos() / (Atom::num(2) * &c__)), x_)
        },
    ));
}

fn push_rules_rule_3937(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 3937,
        source: "Int[(d_+e_.*x_)*Cos[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
          e*Sin[a+b*x+c*x^2]/(2*c) /;
        FreeQ[{a,b,c,d,e},x] && EqQ[2*c*d-b*e,0]",
        desc: "Inverted integration by parts with m\\[Rule]1Bold",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [d__, e__, a__, b__, c__, x_],
        optional: [e__, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(Atom::num(2) * &c__ * &d__ - &b__ * &e__, 0)
        },
        rhs: {
            rubi_simp(&(&e__ * (&a__ + &b__ * x_ + &c__ * x_.pow(2)).sin() / (Atom::num(2) * &c__)), x_)
        },
    ));
}

fn push_rules_rule_3938(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, x_);
    rules.push(rubi_rule!(
        order: 3938,
        source: "Int[(d_.+e_.*x_)^m_*Sin[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
          -e*(d+e*x)^(m-1)*Cos[a+b*x+c*x^2]/(2*c) +
          e^2*(m-1)/(2*c) \\[Star] Int[(d+e*x)^(m-2)*Cos[a+b*x+c*x^2],x] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[2*c*d-b*e,0] && GtQ[m,1]",
        desc: "Inverted integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [d__, e__, m_, a__, b__, c__, x_],
        optional: [d__, e__, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(Atom::num(2) * &c__ * &d__ - &b__ * &e__, 0)
                && gtq!(m_, 1)
        },
        rhs: {
            let affine = &d__ + &e__ * x_;
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let recursive_integrand = affine.pow(&m_ - 2) * quadratic.cos();
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(-&e__ * affine.pow(&m_ - 1) * quadratic.cos() / (Atom::num(2) * &c__)), x_)
                    + rubi_star(e__.pow(2) * (&m_ - 1) / (Atom::num(2) * &c__), recursive)
        },
    ));
}

fn push_rules_rule_3939(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, x_);
    rules.push(rubi_rule!(
        order: 3939,
        source: "Int[(d_.+e_.*x_)^m_*Cos[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
          e*(d+e*x)^(m-1)*Sin[a+b*x+c*x^2]/(2*c) -
          e^2*(m-1)/(2*c) \\[Star] Int[(d+e*x)^(m-2)*Sin[a+b*x+c*x^2],x] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[2*c*d-b*e,0] && GtQ[m,1]",
        desc: "Inverted integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [d__, e__, m_, a__, b__, c__, x_],
        optional: [d__, e__, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(Atom::num(2) * &c__ * &d__ - &b__ * &e__, 0)
                && gtq!(m_, 1)
        },
        rhs: {
            let affine = &d__ + &e__ * x_;
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let recursive_integrand = affine.pow(&m_ - 2) * quadratic.sin();
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(&e__ * affine.pow(&m_ - 1) * quadratic.sin() / (Atom::num(2) * &c__)), x_)
                    + rubi_star(-e__.pow(2) * (&m_ - 1) / (Atom::num(2) * &c__), recursive)
        },
    ));
}

fn push_rules_rule_3940(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, x_);
    rules.push(rubi_rule!(
        order: 3940,
        source: "Int[(d_.+e_.*x_)^m_*Sin[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
          (d+e*x)^(m+1)*Sin[a+b*x+c*x^2]/(e*(m+1)) -
          2*c/(e^2*(m+1)) \\[Star] Int[(d+e*x)^(m+2)*Cos[a+b*x+c*x^2],x] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[2*c*d-b*e,0] && LtQ[m,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [d__, e__, m_, a__, b__, c__, x_],
        optional: [d__, e__, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(Atom::num(2) * &c__ * &d__ - &b__ * &e__, 0)
                && ltq!(m_, -1)
        },
        rhs: {
            let affine = &d__ + &e__ * x_;
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let recursive_integrand = affine.pow(&m_ + 2) * quadratic.cos();
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(affine.pow(&m_ + 1) * quadratic.sin() / (&e__ * (&m_ + 1))), x_)
                    + rubi_star(-Atom::num(2) * &c__ / (e__.pow(2) * (&m_ + 1)), recursive)
        },
    ));
}

fn push_rules_rule_3941(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, x_);
    rules.push(rubi_rule!(
        order: 3941,
        source: "Int[(d_.+e_.*x_)^m_*Cos[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
          (d+e*x)^(m+1)*Cos[a+b*x+c*x^2]/(e*(m+1)) +
          2*c/(e^2*(m+1)) \\[Star] Int[(d+e*x)^(m+2)*Sin[a+b*x+c*x^2],x] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[2*c*d-b*e,0] && LtQ[m,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [d__, e__, m_, a__, b__, c__, x_],
        optional: [d__, e__, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(Atom::num(2) * &c__ * &d__ - &b__ * &e__, 0)
                && ltq!(m_, -1)
        },
        rhs: {
            let affine = &d__ + &e__ * x_;
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let recursive_integrand = affine.pow(&m_ + 2) * quadratic.sin();
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(affine.pow(&m_ + 1) * quadratic.cos() / (&e__ * (&m_ + 1))), x_)
                    + rubi_star(Atom::num(2) * &c__ / (e__.pow(2) * (&m_ + 1)), recursive)
        },
    ));
}

fn push_rules_rule_3942(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 3942,
        source: "Int[(d_.+e_.*x_)*Sin[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
          -e*Cos[a+b*x+c*x^2]/(2*c) +
          (2*c*d-b*e)/(2*c) \\[Star] Int[Sin[a+b*x+c*x^2],x] /;
        FreeQ[{a,b,c,d,e},x] && NeQ[2*c*d-b*e,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [d__, e__, a__, b__, c__, x_],
        optional: [d__, e__, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && neq!(Atom::num(2) * &c__ * &d__ - &b__ * &e__, 0)
        },
        rhs: {
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let recursive = rubi_rhs_int(&quadratic.sin(), x_);

            rubi_simp(&(-&e__ * quadratic.cos() / (Atom::num(2) * &c__)), x_)
                    + rubi_star((Atom::num(2) * &c__ * &d__ - &b__ * &e__)
                            / (Atom::num(2) * &c__), recursive)
        },
    ));
}

fn push_rules_rule_3943(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 3943,
        source: "Int[(d_.+e_.*x_)*Cos[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
          e*Sin[a+b*x+c*x^2]/(2*c) +
          (2*c*d-b*e)/(2*c) \\[Star] Int[Cos[a+b*x+c*x^2],x] /;
        FreeQ[{a,b,c,d,e},x] && NeQ[2*c*d-b*e,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [d__, e__, a__, b__, c__, x_],
        optional: [d__, e__, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && neq!(Atom::num(2) * &c__ * &d__ - &b__ * &e__, 0)
        },
        rhs: {
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let recursive = rubi_rhs_int(&quadratic.cos(), x_);

            rubi_simp(&(&e__ * quadratic.sin() / (Atom::num(2) * &c__)), x_)
                    + rubi_star((Atom::num(2) * &c__ * &d__ - &b__ * &e__)
                            / (Atom::num(2) * &c__), recursive)
        },
    ));
}

fn push_rules_rule_3944(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, x_);
    rules.push(rubi_rule!(
        order: 3944,
        source: "Int[(d_.+e_.*x_)^m_*Sin[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
          -e*(d+e*x)^(m-1)*Cos[a+b*x+c*x^2]/(2*c) -
          (b*e-2*c*d)/(2*c) \\[Star] Int[(d+e*x)^(m-1)*Sin[a+b*x+c*x^2],x] +
          e^2*(m-1)/(2*c) \\[Star] Int[(d+e*x)^(m-2)*Cos[a+b*x+c*x^2],x] /;
        FreeQ[{a,b,c,d,e},x] && NeQ[b*e-2*c*d,0] && GtQ[m,1]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [d__, e__, m_, a__, b__, c__, x_],
        optional: [d__, e__, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && neq!(&b__ * &e__ - Atom::num(2) * &c__ * &d__, 0)
                && gtq!(m_, 1)
        },
        rhs: {
            let affine = &d__ + &e__ * x_;
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let recursive1 = rubi_rhs_int(&(affine.pow(&m_ - 1) * quadratic.sin()), x_);
            let recursive2 = rubi_rhs_int(&(affine.pow(&m_ - 2) * quadratic.cos()), x_);

            rubi_simp(&(-&e__ * affine.pow(&m_ - 1) * quadratic.cos() / (Atom::num(2) * &c__)), x_)
                    + rubi_star(-(&b__ * &e__ - Atom::num(2) * &c__ * &d__)
                            / (Atom::num(2) * &c__), recursive1)
                    + rubi_star(e__.pow(2) * (&m_ - 1) / (Atom::num(2) * &c__), recursive2)
        },
    ));
}

fn push_rules_rule_3945(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, x_);
    rules.push(rubi_rule!(
        order: 3945,
        source: "Int[(d_.+e_.*x_)^m_*Cos[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
          e*(d+e*x)^(m-1)*Sin[a+b*x+c*x^2]/(2*c) -
          (b*e-2*c*d)/(2*c) \\[Star] Int[(d+e*x)^(m-1)*Cos[a+b*x+c*x^2],x] -
          e^2*(m-1)/(2*c) \\[Star] Int[(d+e*x)^(m-2)*Sin[a+b*x+c*x^2],x] /;
        FreeQ[{a,b,c,d,e},x] && NeQ[b*e-2*c*d,0] && GtQ[m,1]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [d__, e__, m_, a__, b__, c__, x_],
        optional: [d__, e__, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && neq!(&b__ * &e__ - Atom::num(2) * &c__ * &d__, 0)
                && gtq!(m_, 1)
        },
        rhs: {
            let affine = &d__ + &e__ * x_;
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let recursive1 = rubi_rhs_int(&(affine.pow(&m_ - 1) * quadratic.cos()), x_);
            let recursive2 = rubi_rhs_int(&(affine.pow(&m_ - 2) * quadratic.sin()), x_);

            rubi_simp(&(&e__ * affine.pow(&m_ - 1) * quadratic.sin() / (Atom::num(2) * &c__)), x_)
                    + rubi_star(-(&b__ * &e__ - Atom::num(2) * &c__ * &d__)
                            / (Atom::num(2) * &c__), recursive1)
                    + rubi_star(-e__.pow(2) * (&m_ - 1) / (Atom::num(2) * &c__), recursive2)
        },
    ));
}

fn push_rules_rule_3946(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, x_);
    rules.push(rubi_rule!(
        order: 3946,
        source: "Int[(d_.+e_.*x_)^m_*Sin[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
          (d+e*x)^(m+1)*Sin[a+b*x+c*x^2]/(e*(m+1)) -
          (b*e-2*c*d)/(e^2*(m+1)) \\[Star] Int[(d+e*x)^(m+1)*Cos[a+b*x+c*x^2],x] -
          2*c/(e^2*(m+1)) \\[Star] Int[(d+e*x)^(m+2)*Cos[a+b*x+c*x^2],x] /;
        FreeQ[{a,b,c,d,e},x] && NeQ[b*e-2*c*d,0] && LtQ[m,-1]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [d__, e__, m_, a__, b__, c__, x_],
        optional: [d__, e__, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && neq!(&b__ * &e__ - Atom::num(2) * &c__ * &d__, 0)
                && ltq!(m_, -1)
        },
        rhs: {
            let affine = &d__ + &e__ * x_;
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let recursive1 = rubi_rhs_int(&(affine.pow(&m_ + 1) * quadratic.cos()), x_);
            let recursive2 = rubi_rhs_int(&(affine.pow(&m_ + 2) * quadratic.cos()), x_);

            rubi_simp(&(affine.pow(&m_ + 1) * quadratic.sin() / (&e__ * (&m_ + 1))), x_)
                    + rubi_star(-(&b__ * &e__ - Atom::num(2) * &c__ * &d__)
                            / (e__.pow(2) * (&m_ + 1)), recursive1)
                    + rubi_star(-Atom::num(2) * &c__ / (e__.pow(2) * (&m_ + 1)), recursive2)
        },
    ));
}

fn push_rules_rule_3947(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, x_);
    rules.push(rubi_rule!(
        order: 3947,
        source: "Int[(d_.+e_.*x_)^m_*Cos[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
          (d+e*x)^(m+1)*Cos[a+b*x+c*x^2]/(e*(m+1)) +
          (b*e-2*c*d)/(e^2*(m+1)) \\[Star] Int[(d+e*x)^(m+1)*Sin[a+b*x+c*x^2],x] +
          2*c/(e^2*(m+1)) \\[Star] Int[(d+e*x)^(m+2)*Sin[a+b*x+c*x^2],x] /;
        FreeQ[{a,b,c,d,e},x] && NeQ[b*e-2*c*d,0] && LtQ[m,-1]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [d__, e__, m_, a__, b__, c__, x_],
        optional: [d__, e__, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && neq!(&b__ * &e__ - Atom::num(2) * &c__ * &d__, 0)
                && ltq!(m_, -1)
        },
        rhs: {
            let affine = &d__ + &e__ * x_;
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let recursive1 = rubi_rhs_int(&(affine.pow(&m_ + 1) * quadratic.sin()), x_);
            let recursive2 = rubi_rhs_int(&(affine.pow(&m_ + 2) * quadratic.sin()), x_);

            rubi_simp(&(affine.pow(&m_ + 1) * quadratic.cos() / (&e__ * (&m_ + 1))), x_)
                    + rubi_star((&b__ * &e__ - Atom::num(2) * &c__ * &d__)
                            / (e__.pow(2) * (&m_ + 1)), recursive1)
                    + rubi_star(Atom::num(2) * &c__ / (e__.pow(2) * (&m_ + 1)), recursive2)
        },
    ));
}

fn push_rules_rule_3948(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 3948,
        source: "Int[(d_.+e_.*x_)^m_.*Sin[a_.+b_.*x_+c_.*x_^2]^n_,x_Symbol] :=
          Int[ExpandTrigReduce[(d+e*x)^m,Sin[a+b*x+c*x^2]^n,x],x] /;
        FreeQ[{a,b,c,d,e,m},x] && IGtQ[n,1]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [d__, e__, m_, a__, b__, c__, n_, x_],
        optional: [d__, e__, m_, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_], x_)
                && igtq!(n_, 1)
        },
        rhs: {
            let u = (&d__ + &e__ * x_).pow(&m_);
            let v = (&a__ + &b__ * x_ + &c__ * x_.pow(2)).sin().pow(&n_);
            let expanded = rubi_expand_trig_reduce(&u, &v, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_3949(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 3949,
        source: "Int[(d_.+e_.*x_)^m_.*Cos[a_.+b_.*x_+c_.*x_^2]^n_,x_Symbol] :=
          Int[ExpandTrigReduce[(d+e*x)^m,Cos[a+b*x+c*x^2]^n,x],x] /;
        FreeQ[{a,b,c,d,e,m},x] && IGtQ[n,1]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [d__, e__, m_, a__, b__, c__, n_, x_],
        optional: [d__, e__, m_, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_], x_)
                && igtq!(n_, 1)
        },
        rhs: {
            let u = (&d__ + &e__ * x_).pow(&m_);
            let v = (&a__ + &b__ * x_ + &c__ * x_.pow(2)).cos().pow(&n_);
            let expanded = rubi_expand_trig_reduce(&u, &v, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_3950(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 3950,
        source: "Int[(d_.+e_.*x_)^m_.*Sin[a_.+b_.*x_+c_.*x_^2]^n_.,x_Symbol] :=
          Unintegrable[(d+e*x)^m*Sin[a+b*x+c*x^2]^n,x] /;
        FreeQ[{a,b,c,d,e,m,n},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [d__, e__, m_, a__, b__, c__, n_, x_],
        optional: [d__, e__, m_, a__, b__, c__, n_],
        when: { freeq!([a__, b__, c__, d__, e__, m_, n_], x_) },
        rhs: {
            let integrand = (&d__ + &e__ * x_).pow(&m_)
                * (&a__ + &b__ * x_ + &c__ * x_.pow(2)).sin().pow(&n_);

            rubi_unintegrable(integrand, x_)
        },
    ));
}

fn push_rules_rule_3951(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 3951,
        source: "Int[(d_.+e_.*x_)^m_.*Cos[a_.+b_.*x_+c_.*x_^2]^n_.,x_Symbol] :=
          Unintegrable[(d+e*x)^m*Cos[a+b*x+c*x^2]^n,x] /;
        FreeQ[{a,b,c,d,e,m,n},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [d__, e__, m_, a__, b__, c__, n_, x_],
        optional: [d__, e__, m_, a__, b__, c__, n_],
        when: { freeq!([a__, b__, c__, d__, e__, m_, n_], x_) },
        rhs: {
            let integrand = (&d__ + &e__ * x_).pow(&m_)
                * (&a__ + &b__ * x_ + &c__ * x_.pow(2)).cos().pow(&n_);

            rubi_unintegrable(integrand, x_)
        },
    ));
}

fn push_rules_rule_3952(rules: &mut Vec<RubiRule>) {
    rubi_symb!(m_, n_, u__, v__);
    rules.push(rubi_rule!(
        order: 3952,
        source: "Int[u_^m_.*Sin[v_]^n_.,x_Symbol] :=
          Int[ExpandToSum[u,x]^m*Sin[ExpandToSum[v,x]]^n,x] /;
        FreeQ[m,x] && IGtQ[n,0] && LinearQ[u,x] && QuadraticQ[v,x] && Not[LinearMatchQ[u,x] && QuadraticMatchQ[v,x]]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: Atom::var(u__).pow(m_) * (Atom::var(v__)).sin().pow(n_),
        with: [u__, m_, v__, n_, x_],
        optional: [m_, n_],
        when: {
            freeq!(m_, x_)
                && igtq!(n_, 0)
                && rubi_linear_q(&u__, x_)
                && rubi_quadratic_q(&v__, x_)
                && !(rubi_linear_match_q(&u__, x_) && rubi_quadratic_match_q(&v__, x_))
        },
        rhs: {
            let integrand = rubi_expand_to_sum(&u__, x_).pow(&m_) * rubi_expand_to_sum(&v__, x_).sin().pow(&n_);

            rubi_rhs_int(&integrand, x_)
        },
    ));
}

fn push_rules_rule_3953(rules: &mut Vec<RubiRule>) {
    rubi_symb!(m_, n_, u__, v__);
    rules.push(rubi_rule!(
        order: 3953,
        source: "Int[u_^m_.*Cos[v_]^n_.,x_Symbol] :=
          Int[ExpandToSum[u,x]^m*Cos[ExpandToSum[v,x]]^n,x] /;
        FreeQ[m,x] && IGtQ[n,0] && LinearQ[u,x] && QuadraticQ[v,x] && Not[LinearMatchQ[u,x] && QuadraticMatchQ[v,x]]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: Atom::var(u__).pow(m_) * (Atom::var(v__)).cos().pow(n_),
        with: [u__, m_, v__, n_, x_],
        optional: [m_, n_],
        when: {
            freeq!(m_, x_)
                && igtq!(n_, 0)
                && rubi_linear_q(&u__, x_)
                && rubi_quadratic_q(&v__, x_)
                && !(rubi_linear_match_q(&u__, x_) && rubi_quadratic_match_q(&v__, x_))
        },
        rhs: {
            let integrand = rubi_expand_to_sum(&u__, x_).pow(&m_) * rubi_expand_to_sum(&v__, x_).cos().pow(&n_);

            rubi_rhs_int(&integrand, x_)
        },
    ));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn downvalues_3926_through_3942_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .filter(|order| (3926..=3942).contains(order))
            .collect::<Vec<_>>();
        assert_eq!(orders, (3926..=3942).collect::<Vec<_>>());
    }

    #[test]
    fn downvalues_3943_through_3953_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .filter(|order| (3943..=3953).contains(order))
            .collect::<Vec<_>>();
        assert_eq!(orders, (3943..=3953).collect::<Vec<_>>());
    }
}

// Generated shared pattern builders.

#[inline(never)]
fn rubi_shared_pattern_0(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let x_ = symbols.x_;
    (a__ + b__ * x_ + c__ * x_.pow(2)).cos()
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    (a__ + b__ * x_ + c__ * x_.pow(2)).cos().pow(n_)
}

#[inline(never)]
fn rubi_shared_pattern_2(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let x_ = symbols.x_;
    (a__ + b__ * x_ + c__ * x_.pow(2)).sin()
}

#[inline(never)]
fn rubi_shared_pattern_3(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    (a__ + b__ * x_ + c__ * x_.pow(2)).sin().pow(n_)
}

#[inline(never)]
fn rubi_shared_pattern_4(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let x_ = symbols.x_;
    (d__ + e__ * x_) * (a__ + b__ * x_ + c__ * x_.pow(2)).cos()
}

#[inline(never)]
fn rubi_shared_pattern_5(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let x_ = symbols.x_;
    (d__ + e__ * x_) * (a__ + b__ * x_ + c__ * x_.pow(2)).sin()
}

#[inline(never)]
fn rubi_shared_pattern_6(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let m_ = symbols.m_;
    let x_ = symbols.x_;
    (d__ + e__ * x_).pow(m_) * (a__ + b__ * x_ + c__ * x_.pow(2)).cos()
}

#[inline(never)]
fn rubi_shared_pattern_7(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    (d__ + e__ * x_).pow(m_) * (a__ + b__ * x_ + c__ * x_.pow(2)).cos().pow(n_)
}

#[inline(never)]
fn rubi_shared_pattern_8(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let m_ = symbols.m_;
    let x_ = symbols.x_;
    (d__ + e__ * x_).pow(m_) * (a__ + b__ * x_ + c__ * x_.pow(2)).sin()
}

#[inline(never)]
fn rubi_shared_pattern_9(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    (d__ + e__ * x_).pow(m_) * (a__ + b__ * x_ + c__ * x_.pow(2)).sin().pow(n_)
}
