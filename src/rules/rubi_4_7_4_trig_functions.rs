use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_4770(rules);
    push_rules_rule_4771(rules);
    push_rules_rule_4772(rules);
    push_rules_rule_4773(rules);
    push_rules_rule_4774(rules);
    push_rules_rule_4775(rules);
    push_rules_rule_4776(rules);
    push_rules_rule_4777(rules);
    push_rules_rule_4778(rules);
    push_rules_rule_4779(rules);
    push_rules_rule_4780(rules);
    push_rules_rule_4781(rules);
    push_rules_rule_4782(rules);
    push_rules_rule_4783(rules);
    push_rules_rule_4784(rules);
    push_rules_rule_4785(rules);
    push_rules_rule_4786(rules);
    push_rules_rule_4787(rules);
    push_rules_rule_4788(rules);
    push_rules_rule_4789(rules);
    push_rules_rule_4790(rules);
    push_rules_rule_4791(rules);
    push_rules_rule_4792(rules);
    push_rules_rule_4793(rules);
    push_rules_rule_4794(rules);
    push_rules_rule_4795(rules);
    push_rules_rule_4796(rules);
    // Rubi 4.7.4 block 16 is commented out in docs/rubi_pdf_rules.md.
    push_rules_rule_4797(rules);
    push_rules_rule_4798(rules);
    push_rules_rule_4799(rules);
    push_rules_rule_4800(rules);
    push_rules_rule_4801(rules);
    push_rules_rule_4802(rules);
    push_rules_rule_4803(rules);
    push_rules_rule_4804(rules);
    push_rules_rule_4805(rules);
    push_rules_rule_4806(rules);
    push_rules_rule_4807(rules);
    push_rules_rule_4808(rules);
    push_rules_rule_4809(rules);
    push_rules_rule_4810(rules);
    push_rules_rule_4811(rules);
    push_rules_rule_4812(rules);
    push_rules_rule_4813(rules);
    push_rules_rule_4814(rules);
    push_rules_rule_4815(rules);
    push_rules_rule_4816(rules);
    push_rules_rule_4817(rules);
    push_rules_rule_4818(rules);
    push_rules_rule_4819(rules);
}

fn push_rules_rule_4770(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 4770,
        source: "Int[sin[a_.+b_.*x_]*sin[c_.+d_.*x_],x_Symbol] :=
          Sin[a-c+(b-d)*x]/(2*(b-d)) - Sin[a+c+(b+d)*x]/(2*(b+d)) /;
        FreeQ[{a,b,c,d},x] && NeQ[b^2-d^2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: i_sin(a__ + b__ * x_) * i_sin(c__ + d__ * x_),
        with: [a__, b__, c__, d__, x_],
        optional: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_) && neq!(b__.pow(2) - d__.pow(2), 0)
        },
        rhs: {
            rubi_simp(&((&a__ - &c__ + (&b__ - &d__) * x_).sin() / (2 * (&b__ - &d__))), x_)
                    - rubi_simp(&((&a__ + &c__ + (&b__ + &d__) * x_).sin() / (2 * (&b__ + &d__))), x_)
        },
    ));
}

fn push_rules_rule_4771(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 4771,
        source: "Int[cos[a_.+b_.*x_]*cos[c_.+d_.*x_],x_Symbol] :=
          Sin[a-c+(b-d)*x]/(2*(b-d)) + Sin[a+c+(b+d)*x]/(2*(b+d)) /;
        FreeQ[{a,b,c,d},x] && NeQ[b^2-d^2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: i_cos(a__ + b__ * x_) * i_cos(c__ + d__ * x_),
        with: [a__, b__, c__, d__, x_],
        optional: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_) && neq!(b__.pow(2) - d__.pow(2), 0)
        },
        rhs: {
            rubi_simp(&((&a__ - &c__ + (&b__ - &d__) * x_).sin() / (2 * (&b__ - &d__))), x_)
                    + rubi_simp(&((&a__ + &c__ + (&b__ + &d__) * x_).sin() / (2 * (&b__ + &d__))), x_)
        },
    ));
}

fn push_rules_rule_4772(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 4772,
        source: "Int[sin[a_.+b_.*x_]*cos[c_.+d_.*x_],x_Symbol] :=
          -Cos[a-c+(b-d)*x]/(2*(b-d)) - Cos[a+c+(b+d)*x]/(2*(b+d)) /;
        FreeQ[{a,b,c,d},x] && NeQ[b^2-d^2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: i_sin(a__ + b__ * x_) * i_cos(c__ + d__ * x_),
        with: [a__, b__, c__, d__, x_],
        optional: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_) && neq!(b__.pow(2) - d__.pow(2), 0)
        },
        rhs: {
            rubi_simp(&(-(&a__ - &c__ + (&b__ - &d__) * x_).cos() / (2 * (&b__ - &d__))), x_)
                    - rubi_simp(&((&a__ + &c__ + (&b__ + &d__) * x_).cos() / (2 * (&b__ + &d__))), x_)
        },
    ));
}

fn push_rules_rule_4773(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, g__, p_, x_);
    rules.push(rubi_rule!(
        order: 4773,
        source: "Int[cos[a_.+b_.*x_]^2*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
          1/2 \\[Star] Int[(g*Sin[c+d*x])^p,x] +
          1/2 \\[Star] Int[Cos[c+d*x]*(g*Sin[c+d*x])^p,x] /;
        FreeQ[{a,b,c,d,g},x] && EqQ[b*c-a*d,0] && EqQ[d/b,2] && IGtQ[p/2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: i_cos(a__ + b__ * x_).pow(2) * (g__ * i_sin(c__ + d__ * x_)).pow(p_),
        with: [a__, b__, c__, d__, g__, p_, x_],
        optional: [a__, b__, c__, d__, g__],
        when: {
            freeq!([a__, b__, c__, d__, g__], x_)
                && eqq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(&d__ / &b__, 2)
                && igtq!(&p_ / 2, 0)
        },
        rhs: {
            let angle2 = &c__ + &d__ * x_;
            let recursive1 = rubi_rhs_int(&((&g__ * angle2.sin()).pow(&p_)), x_);
            let recursive2 = rubi_rhs_int(&(angle2.cos() * (&g__ * angle2.sin()).pow(&p_)), x_);

            rubi_star(Atom::num(1) / 2, recursive1)
                    + rubi_star(Atom::num(1) / 2, recursive2)
        },
    ));
}

fn push_rules_rule_4774(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, g__, p_, x_);
    rules.push(rubi_rule!(
        order: 4774,
        source: "Int[sin[a_.+b_.*x_]^2*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
          1/2 \\[Star] Int[(g*Sin[c+d*x])^p,x] -
          1/2 \\[Star] Int[Cos[c+d*x]*(g*Sin[c+d*x])^p,x] /;
        FreeQ[{a,b,c,d,g},x] && EqQ[b*c-a*d,0] && EqQ[d/b,2] && IGtQ[p/2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: i_sin(a__ + b__ * x_).pow(2) * (g__ * i_sin(c__ + d__ * x_)).pow(p_),
        with: [a__, b__, c__, d__, g__, p_, x_],
        optional: [a__, b__, c__, d__, g__],
        when: {
            freeq!([a__, b__, c__, d__, g__], x_)
                && eqq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(&d__ / &b__, 2)
                && igtq!(&p_ / 2, 0)
        },
        rhs: {
            let angle2 = &c__ + &d__ * x_;
            let recursive1 = rubi_rhs_int(&((&g__ * angle2.sin()).pow(&p_)), x_);
            let recursive2 = rubi_rhs_int(&(angle2.cos() * (&g__ * angle2.sin()).pow(&p_)), x_);

            rubi_star(Atom::num(1) / 2, recursive1)
                    - rubi_star(Atom::num(1) / 2, recursive2)
        },
    ));
}

fn push_rules_rule_4775(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 4775,
        source: "Int[(e_.*cos[a_.+b_.*x_])^m_.*sin[c_.+d_.*x_]^p_.,x_Symbol] :=
          2^p/e^p \\[Star] Int[(e*Cos[a+b*x])^(m+p)*Sin[a+b*x]^p,x] /;
        FreeQ[{a,b,c,d,e,m},x] && EqQ[b*c-a*d,0] && EqQ[d/b,2] && IntegerQ[p]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: (e__ * i_cos(a__ + b__ * x_)).pow(m_) * i_sin(c__ + d__ * x_).pow(p_),
        with: [e__, a__, b__, m_, c__, d__, p_, x_],
        optional: [e__, a__, b__, m_, c__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_], x_)
                && eqq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(&d__ / &b__, 2)
                && integerq!(p_)
        },
        rhs: {
            let angle = &a__ + &b__ * x_;
            let recursive =
                rubi_rhs_int(&((&e__ * angle.cos()).pow(&m_ + &p_) * angle.sin().pow(&p_)), x_);

            let coefficient = Atom::num(2).pow(&p_) / e__.pow(&p_);
            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_4776(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, f__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 4776,
        source: "Int[(f_.*sin[a_.+b_.*x_])^n_.*sin[c_.+d_.*x_]^p_.,x_Symbol] :=
          2^p/f^p \\[Star] Int[Cos[a+b*x]^p*(f*Sin[a+b*x])^(n+p),x] /;
        FreeQ[{a,b,c,d,f,n},x] && EqQ[b*c-a*d,0] && EqQ[d/b,2] && IntegerQ[p]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: (f__ * i_sin(a__ + b__ * x_)).pow(n_) * i_sin(c__ + d__ * x_).pow(p_),
        with: [f__, a__, b__, n_, c__, d__, p_, x_],
        optional: [f__, a__, b__, n_, c__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__, f__, n_], x_)
                && eqq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(&d__ / &b__, 2)
                && integerq!(p_)
        },
        rhs: {
            let angle = &a__ + &b__ * x_;
            let recursive =
                rubi_rhs_int(&(angle.cos().pow(&p_) * (&f__ * angle.sin()).pow(&n_ + &p_)), x_);

            let coefficient = Atom::num(2).pow(&p_) / f__.pow(&p_);
            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_4777(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 4777,
        source: "Int[(e_.*cos[a_.+b_.*x_])^m_*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
          e^2*(e*Cos[a+b*x])^(m-2)*(g*Sin[c+d*x])^(p+1)/(2*b*g*(p+1)) /;
        FreeQ[{a,b,c,d,e,g,m,p},x] && EqQ[b*c-a*d,0] && EqQ[d/b,2] && Not[IntegerQ[p]] && EqQ[m+p-1,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [e__, a__, b__, m_, g__, c__, d__, p_, x_],
        optional: [e__, a__, b__, g__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, g__, m_, p_], x_)
                && eqq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(&d__ / &b__, 2)
                && !integerq!(p_)
                && eqq!(&m_ + &p_ - 1, 0)
        },
        rhs: {
            let angle1 = &a__ + &b__ * x_;
            let angle2 = &c__ + &d__ * x_;

            rubi_simp(&(e__.pow(2) * (&e__ * angle1.cos()).pow(&m_ - 2) * (&g__ * angle2.sin()).pow(&p_ + 1)
                / (2 * &b__ * &g__ * (&p_ + 1))), x_)
        },
    ));
}

fn push_rules_rule_4778(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 4778,
        source: "Int[(e_.*sin[a_.+b_.*x_])^m_*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
          -e^2*(e*Sin[a+b*x])^(m-2)*(g*Sin[c+d*x])^(p+1)/(2*b*g*(p+1)) /;
        FreeQ[{a,b,c,d,e,g,m,p},x] && EqQ[b*c-a*d,0] && EqQ[d/b,2] && Not[IntegerQ[p]] && EqQ[m+p-1,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [e__, a__, b__, m_, g__, c__, d__, p_, x_],
        optional: [e__, a__, b__, g__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, g__, m_, p_], x_)
                && eqq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(&d__ / &b__, 2)
                && !integerq!(p_)
                && eqq!(&m_ + &p_ - 1, 0)
        },
        rhs: {
            let angle1 = &a__ + &b__ * x_;
            let angle2 = &c__ + &d__ * x_;

            rubi_simp(&(-e__.pow(2) * (&e__ * angle1.sin()).pow(&m_ - 2) * (&g__ * angle2.sin()).pow(&p_ + 1)
                / (2 * &b__ * &g__ * (&p_ + 1))), x_)
        },
    ));
}

fn push_rules_rule_4779(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 4779,
        source: "Int[(e_.*cos[a_.+b_.*x_])^m_.*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
          -(e*Cos[a+b*x])^m*(g*Sin[c+d*x])^(p+1)/(b*g*m) /;
        FreeQ[{a,b,c,d,e,g,m,p},x] && EqQ[b*c-a*d,0] && EqQ[d/b,2] && Not[IntegerQ[p]] && EqQ[m+2*p+2,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [e__, a__, b__, m_, g__, c__, d__, p_, x_],
        optional: [e__, a__, b__, m_, g__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, g__, m_, p_], x_)
                && eqq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(&d__ / &b__, 2)
                && !integerq!(p_)
                && eqq!(&m_ + Atom::num(2) * &p_ + 2, 0)
        },
        rhs: {
            let angle1 = &a__ + &b__ * x_;
            let angle2 = &c__ + &d__ * x_;

            rubi_simp(&(-(&e__ * angle1.cos()).pow(&m_) * (&g__ * angle2.sin()).pow(&p_ + 1) / (&b__ * &g__ * &m_)), x_)
        },
    ));
}

fn push_rules_rule_4780(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 4780,
        source: "Int[(e_.*sin[a_.+b_.*x_])^m_.*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
          (e*Sin[a+b*x])^m*(g*Sin[c+d*x])^(p+1)/(b*g*m) /;
        FreeQ[{a,b,c,d,e,g,m,p},x] && EqQ[b*c-a*d,0] && EqQ[d/b,2] && Not[IntegerQ[p]] && EqQ[m+2*p+2,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [e__, a__, b__, m_, g__, c__, d__, p_, x_],
        optional: [e__, a__, b__, m_, g__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, g__, m_, p_], x_)
                && eqq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(&d__ / &b__, 2)
                && !integerq!(p_)
                && eqq!(&m_ + Atom::num(2) * &p_ + 2, 0)
        },
        rhs: {
            let angle1 = &a__ + &b__ * x_;
            let angle2 = &c__ + &d__ * x_;

            rubi_simp(&((&e__ * angle1.sin()).pow(&m_) * (&g__ * angle2.sin()).pow(&p_ + 1) / (&b__ * &g__ * &m_)), x_)
        },
    ));
}

fn push_rules_rule_4781(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 4781,
        source: "Int[(e_.*cos[a_.+b_.*x_])^m_*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
          e^2*(e*Cos[a+b*x])^(m-2)*(g*Sin[c+d*x])^(p+1)/(2*b*g*(p+1)) +
          e^4*(m+p-1)/(4*g^2*(p+1)) \\[Star] Int[(e*Cos[a+b*x])^(m-4)*(g*Sin[c+d*x])^(p+2),x] /;
        FreeQ[{a,b,c,d,e,g},x] && EqQ[b*c-a*d,0] && EqQ[d/b,2] && Not[IntegerQ[p]] && GtQ[m,2] && LtQ[p,-1] && (GtQ[m,3] || EqQ[p,-3/2]) && IntegersQ[2*m,2*p]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [e__, a__, b__, m_, g__, c__, d__, p_, x_],
        optional: [e__, a__, b__, g__, c__, d__],
        when: {
            let minus_three_halves = -Atom::num(3) / Atom::num(2);
            freeq!([a__, b__, c__, d__, e__, g__], x_)
                && eqq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(&d__ / &b__, 2)
                && !integerq!(p_)
                && gtq!(m_, 2)
                && ltq!(p_, -1)
                && (gtq!(m_, 3) || eqq!(p_, minus_three_halves))
                && integersq!([Atom::num(2) * &m_, Atom::num(2) * &p_])
        },
        rhs: {
            let angle1 = &a__ + &b__ * x_;
            let angle2 = &c__ + &d__ * x_;
            let recursive = rubi_rhs_int(
                &((&e__ * angle1.cos()).pow(&m_ - 4) * (&g__ * angle2.sin()).pow(&p_ + 2)),
                x_,
            );

            rubi_simp(&(e__.pow(2) * (&e__ * angle1.cos()).pow(&m_ - 2) * (&g__ * angle2.sin()).pow(&p_ + 1)
                    / (2 * &b__ * &g__ * (&p_ + 1))), x_)
                    + rubi_star(e__.pow(4) * (&m_ + &p_ - 1)
                            / (4 * g__.pow(2) * (&p_ + 1)), recursive)
        },
    ));
}

fn push_rules_rule_4782(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 4782,
        source: "Int[(e_.*sin[a_.+b_.*x_])^m_*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
          -e^2*(e*Sin[a+b*x])^(m-2)*(g*Sin[c+d*x])^(p+1)/(2*b*g*(p+1)) +
          e^4*(m+p-1)/(4*g^2*(p+1)) \\[Star] Int[(e*Sin[a+b*x])^(m-4)*(g*Sin[c+d*x])^(p+2),x] /;
        FreeQ[{a,b,c,d,e,g},x] && EqQ[b*c-a*d,0] && EqQ[d/b,2] && Not[IntegerQ[p]] && GtQ[m,2] && LtQ[p,-1] && (GtQ[m,3] || EqQ[p,-3/2]) && IntegersQ[2*m,2*p]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [e__, a__, b__, m_, g__, c__, d__, p_, x_],
        optional: [e__, a__, b__, g__, c__, d__],
        when: {
            let minus_three_halves = -Atom::num(3) / Atom::num(2);
            freeq!([a__, b__, c__, d__, e__, g__], x_)
                && eqq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(&d__ / &b__, 2)
                && !integerq!(p_)
                && gtq!(m_, 2)
                && ltq!(p_, -1)
                && (gtq!(m_, 3) || eqq!(p_, minus_three_halves))
                && integersq!([Atom::num(2) * &m_, Atom::num(2) * &p_])
        },
        rhs: {
            let angle1 = &a__ + &b__ * x_;
            let angle2 = &c__ + &d__ * x_;
            let recursive = rubi_rhs_int(
                &((&e__ * angle1.sin()).pow(&m_ - 4) * (&g__ * angle2.sin()).pow(&p_ + 2)),
                x_,
            );

            rubi_simp(&(-e__.pow(2) * (&e__ * angle1.sin()).pow(&m_ - 2) * (&g__ * angle2.sin()).pow(&p_ + 1)
                    / (2 * &b__ * &g__ * (&p_ + 1))), x_)
                    + rubi_star(e__.pow(4) * (&m_ + &p_ - 1)
                            / (4 * g__.pow(2) * (&p_ + 1)), recursive)
        },
    ));
}

fn push_rules_rule_4783(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 4783,
        source: "Int[(e_.*cos[a_.+b_.*x_])^m_*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
          (e*Cos[a+b*x])^m*(g*Sin[c+d*x])^(p+1)/(2*b*g*(p+1)) +
          e^2*(m+2*p+2)/(4*g^2*(p+1)) \\[Star] Int[(e*Cos[a+b*x])^(m-2)*(g*Sin[c+d*x])^(p+2),x] /;
        FreeQ[{a,b,c,d,e,g},x] && EqQ[b*c-a*d,0] && EqQ[d/b,2] && Not[IntegerQ[p]] && GtQ[m,1] && LtQ[p,-1] && NeQ[m+2*p+2,0] &&
          (LtQ[p,-2] || EqQ[m,2]) && IntegersQ[2*m,2*p]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [e__, a__, b__, m_, g__, c__, d__, p_, x_],
        optional: [e__, a__, b__, g__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, g__], x_)
                && eqq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(&d__ / &b__, 2)
                && !integerq!(p_)
                && gtq!(m_, 1)
                && ltq!(p_, -1)
                && neq!(&m_ + Atom::num(2) * &p_ + 2, 0)
                && (ltq!(p_, -2) || eqq!(m_, 2))
                && integersq!([Atom::num(2) * &m_, Atom::num(2) * &p_])
        },
        rhs: {
            let angle1 = &a__ + &b__ * x_;
            let angle2 = &c__ + &d__ * x_;
            let recursive = rubi_rhs_int(
                &((&e__ * angle1.cos()).pow(&m_ - 2) * (&g__ * angle2.sin()).pow(&p_ + 2)),
                x_,
            );

            rubi_simp(&((&e__ * angle1.cos()).pow(&m_) * (&g__ * angle2.sin()).pow(&p_ + 1)
                    / (2 * &b__ * &g__ * (&p_ + 1))), x_)
                    + rubi_star(e__.pow(2) * (&m_ + Atom::num(2) * &p_ + 2)
                            / (4 * g__.pow(2) * (&p_ + 1)), recursive)
        },
    ));
}

fn push_rules_rule_4784(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 4784,
        source: "Int[(e_.*sin[a_.+b_.*x_])^m_*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
          -(e*Sin[a+b*x])^m*(g*Sin[c+d*x])^(p+1)/(2*b*g*(p+1)) +
          e^2*(m+2*p+2)/(4*g^2*(p+1)) \\[Star] Int[(e*Sin[a+b*x])^(m-2)*(g*Sin[c+d*x])^(p+2),x] /;
        FreeQ[{a,b,c,d,e,g},x] && EqQ[b*c-a*d,0] && EqQ[d/b,2] && Not[IntegerQ[p]] && GtQ[m,1] && LtQ[p,-1] && NeQ[m+2*p+2,0] &&
          (LtQ[p,-2] || EqQ[m,2]) && IntegersQ[2*m,2*p]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [e__, a__, b__, m_, g__, c__, d__, p_, x_],
        optional: [e__, a__, b__, g__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, g__], x_)
                && eqq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(&d__ / &b__, 2)
                && !integerq!(p_)
                && gtq!(m_, 1)
                && ltq!(p_, -1)
                && neq!(&m_ + Atom::num(2) * &p_ + 2, 0)
                && (ltq!(p_, -2) || eqq!(m_, 2))
                && integersq!([Atom::num(2) * &m_, Atom::num(2) * &p_])
        },
        rhs: {
            let angle1 = &a__ + &b__ * x_;
            let angle2 = &c__ + &d__ * x_;
            let recursive = rubi_rhs_int(
                &((&e__ * angle1.sin()).pow(&m_ - 2) * (&g__ * angle2.sin()).pow(&p_ + 2)),
                x_,
            );

            rubi_simp(&(-(&e__ * angle1.sin()).pow(&m_) * (&g__ * angle2.sin()).pow(&p_ + 1)
                    / (2 * &b__ * &g__ * (&p_ + 1))), x_)
                    + rubi_star(e__.pow(2) * (&m_ + Atom::num(2) * &p_ + 2)
                            / (4 * g__.pow(2) * (&p_ + 1)), recursive)
        },
    ));
}

fn push_rules_rule_4785(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 4785,
        source: "Int[(e_.*cos[a_.+b_.*x_])^m_*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
          e^2*(e*Cos[a+b*x])^(m-2)*(g*Sin[c+d*x])^(p+1)/(2*b*g*(m+2*p)) +
          e^2*(m+p-1)/(m+2*p) \\[Star] Int[(e*Cos[a+b*x])^(m-2)*(g*Sin[c+d*x])^p,x] /;
        FreeQ[{a,b,c,d,e,g,p},x] && EqQ[b*c-a*d,0] && EqQ[d/b,2] && Not[IntegerQ[p]] && GtQ[m,1] && NeQ[m+2*p,0] && IntegersQ[2*m,2*p]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [e__, a__, b__, m_, g__, c__, d__, p_, x_],
        optional: [e__, a__, b__, g__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, g__, p_], x_)
                && eqq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(&d__ / &b__, 2)
                && !integerq!(p_)
                && gtq!(m_, 1)
                && neq!(&m_ + Atom::num(2) * &p_, 0)
                && integersq!([Atom::num(2) * &m_, Atom::num(2) * &p_])
        },
        rhs: {
            let angle1 = &a__ + &b__ * x_;
            let angle2 = &c__ + &d__ * x_;
            let recursive = rubi_rhs_int(
                &((&e__ * angle1.cos()).pow(&m_ - 2) * (&g__ * angle2.sin()).pow(&p_)),
                x_,
            );

            rubi_simp(&(e__.pow(2) * (&e__ * angle1.cos()).pow(&m_ - 2) * (&g__ * angle2.sin()).pow(&p_ + 1)
                    / (2 * &b__ * &g__ * (&m_ + Atom::num(2) * &p_))), x_)
                    + rubi_star(e__.pow(2) * (&m_ + &p_ - 1)
                            / (&m_ + Atom::num(2) * &p_), recursive)
        },
    ));
}

fn push_rules_rule_4786(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 4786,
        source: "Int[(e_.*sin[a_.+b_.*x_])^m_*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
          -e^2*(e*Sin[a+b*x])^(m-2)*(g*Sin[c+d*x])^(p+1)/(2*b*g*(m+2*p)) +
          e^2*(m+p-1)/(m+2*p) \\[Star] Int[(e*Sin[a+b*x])^(m-2)*(g*Sin[c+d*x])^p,x] /;
        FreeQ[{a,b,c,d,e,g,p},x] && EqQ[b*c-a*d,0] && EqQ[d/b,2] && Not[IntegerQ[p]] && GtQ[m,1] && NeQ[m+2*p,0] && IntegersQ[2*m,2*p]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [e__, a__, b__, m_, g__, c__, d__, p_, x_],
        optional: [e__, a__, b__, g__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, g__, p_], x_)
                && eqq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(&d__ / &b__, 2)
                && !integerq!(p_)
                && gtq!(m_, 1)
                && neq!(&m_ + Atom::num(2) * &p_, 0)
                && integersq!([Atom::num(2) * &m_, Atom::num(2) * &p_])
        },
        rhs: {
            let angle1 = &a__ + &b__ * x_;
            let angle2 = &c__ + &d__ * x_;
            let recursive = rubi_rhs_int(
                &((&e__ * angle1.sin()).pow(&m_ - 2) * (&g__ * angle2.sin()).pow(&p_)),
                x_,
            );

            rubi_simp(&(-e__.pow(2) * (&e__ * angle1.sin()).pow(&m_ - 2) * (&g__ * angle2.sin()).pow(&p_ + 1)
                    / (2 * &b__ * &g__ * (&m_ + Atom::num(2) * &p_))), x_)
                    + rubi_star(e__.pow(2) * (&m_ + &p_ - 1)
                            / (&m_ + Atom::num(2) * &p_), recursive)
        },
    ));
}

fn push_rules_rule_4787(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 4787,
        source: "Int[(e_.*cos[a_.+b_.*x_])^m_*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
          -(e*Cos[a+b*x])^m*(g*Sin[c+d*x])^(p+1)/(2*b*g*(m+p+1)) +
          (m+2*p+2)/(e^2*(m+p+1)) \\[Star] Int[(e*Cos[a+b*x])^(m+2)*(g*Sin[c+d*x])^p,x] /;
        FreeQ[{a,b,c,d,e,g,p},x] && EqQ[b*c-a*d,0] && EqQ[d/b,2] && Not[IntegerQ[p]] && LtQ[m,-1] && NeQ[m+2*p+2,0] && NeQ[m+p+1,0] && IntegersQ[2*m,2*p]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [e__, a__, b__, m_, g__, c__, d__, p_, x_],
        optional: [e__, a__, b__, g__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, g__, p_], x_)
                && eqq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(&d__ / &b__, 2)
                && !integerq!(p_)
                && ltq!(m_, -1)
                && neq!(&m_ + Atom::num(2) * &p_ + 2, 0)
                && neq!(&m_ + &p_ + 1, 0)
                && integersq!([Atom::num(2) * &m_, Atom::num(2) * &p_])
        },
        rhs: {
            let angle1 = &a__ + &b__ * x_;
            let angle2 = &c__ + &d__ * x_;
            let recursive = rubi_rhs_int(
                &((&e__ * angle1.cos()).pow(&m_ + 2) * (&g__ * angle2.sin()).pow(&p_)),
                x_,
            );

            rubi_simp(&(-(&e__ * angle1.cos()).pow(&m_) * (&g__ * angle2.sin()).pow(&p_ + 1)
                    / (2 * &b__ * &g__ * (&m_ + &p_ + 1))), x_)
                    + rubi_star((&m_ + Atom::num(2) * &p_ + 2)
                            / (e__.pow(2) * (&m_ + &p_ + 1)), recursive)
        },
    ));
}

fn push_rules_rule_4788(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 4788,
        source: "Int[(e_.*sin[a_.+b_.*x_])^m_*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
          (e*Sin[a+b*x])^m*(g*Sin[c+d*x])^(p+1)/(2*b*g*(m+p+1)) +
          (m+2*p+2)/(e^2*(m+p+1)) \\[Star] Int[(e*Sin[a+b*x])^(m+2)*(g*Sin[c+d*x])^p,x] /;
        FreeQ[{a,b,c,d,e,g,p},x] && EqQ[b*c-a*d,0] && EqQ[d/b,2] && Not[IntegerQ[p]] && LtQ[m,-1] && NeQ[m+2*p+2,0] && NeQ[m+p+1,0] && IntegersQ[2*m,2*p]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [e__, a__, b__, m_, g__, c__, d__, p_, x_],
        optional: [e__, a__, b__, g__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, g__, p_], x_)
                && eqq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(&d__ / &b__, 2)
                && !integerq!(p_)
                && ltq!(m_, -1)
                && neq!(&m_ + Atom::num(2) * &p_ + 2, 0)
                && neq!(&m_ + &p_ + 1, 0)
                && integersq!([Atom::num(2) * &m_, Atom::num(2) * &p_])
        },
        rhs: {
            let angle1 = &a__ + &b__ * x_;
            let angle2 = &c__ + &d__ * x_;
            let recursive = rubi_rhs_int(
                &((&e__ * angle1.sin()).pow(&m_ + 2) * (&g__ * angle2.sin()).pow(&p_)),
                x_,
            );

            rubi_simp(&((&e__ * angle1.sin()).pow(&m_) * (&g__ * angle2.sin()).pow(&p_ + 1)
                    / (2 * &b__ * &g__ * (&m_ + &p_ + 1))), x_)
                    + rubi_star((&m_ + Atom::num(2) * &p_ + 2)
                            / (e__.pow(2) * (&m_ + &p_ + 1)), recursive)
        },
    ));
}

fn push_rules_rule_4789(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, g__, p_, x_);
    rules.push(rubi_rule!(
        order: 4789,
        source: "Int[cos[a_.+b_.*x_]*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
          2*Sin[a+b*x]*(g*Sin[c+d*x])^p/(d*(2*p+1)) + 2*p*g/(2*p+1) \\[Star] Int[Sin[a+b*x]*(g*Sin[c+d*x])^(p-1),x] /;
        FreeQ[{a,b,c,d,g},x] && EqQ[b*c-a*d,0] && EqQ[d/b,2] && Not[IntegerQ[p]] && GtQ[p,0] && IntegerQ[2*p]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, b__, g__, c__, d__, p_, x_],
        optional: [a__, b__, g__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, g__], x_)
                && eqq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(&d__ / &b__, 2)
                && !integerq!(p_)
                && gtq!(p_, 0)
                && integerq!(Atom::num(2) * &p_)
        },
        rhs: {
            let angle1 = &a__ + &b__ * x_;
            let angle2 = &c__ + &d__ * x_;
            let recursive = rubi_rhs_int(&(angle1.sin() * (&g__ * angle2.sin()).pow(&p_ - 1)), x_);

            rubi_simp(&(2 * angle1.sin() * (&g__ * angle2.sin()).pow(&p_) / (&d__ * (Atom::num(2) * &p_ + 1))), x_)
                    + rubi_star(Atom::num(2) * &p_ * &g__ / (Atom::num(2) * &p_ + 1), recursive)
        },
    ));
}

fn push_rules_rule_4790(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, g__, p_, x_);
    rules.push(rubi_rule!(
        order: 4790,
        source: "Int[sin[a_.+b_.*x_]*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
          -2*Cos[a+b*x]*(g*Sin[c+d*x])^p/(d*(2*p+1)) + 2*p*g/(2*p+1) \\[Star] Int[Cos[a+b*x]*(g*Sin[c+d*x])^(p-1),x] /;
        FreeQ[{a,b,c,d,g},x] && EqQ[b*c-a*d,0] && EqQ[d/b,2] && Not[IntegerQ[p]] && GtQ[p,0] && IntegerQ[2*p]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [a__, b__, g__, c__, d__, p_, x_],
        optional: [a__, b__, g__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, g__], x_)
                && eqq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(&d__ / &b__, 2)
                && !integerq!(p_)
                && gtq!(p_, 0)
                && integerq!(Atom::num(2) * &p_)
        },
        rhs: {
            let angle1 = &a__ + &b__ * x_;
            let angle2 = &c__ + &d__ * x_;
            let recursive = rubi_rhs_int(&(angle1.cos() * (&g__ * angle2.sin()).pow(&p_ - 1)), x_);

            rubi_simp(&(-Atom::num(2) * angle1.cos() * (&g__ * angle2.sin()).pow(&p_) / (&d__ * (Atom::num(2) * &p_ + 1))), x_)
                    + rubi_star(Atom::num(2) * &p_ * &g__ / (Atom::num(2) * &p_ + 1), recursive)
        },
    ));
}

fn push_rules_rule_4791(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, g__, p_, x_);
    rules.push(rubi_rule!(
        order: 4791,
        source: "Int[cos[a_.+b_.*x_]*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
          Cos[a+b*x]*(g*Sin[c+d*x])^(p+1)/(2*b*g*(p+1)) +
          (2*p+3)/(2*g*(p+1)) \\[Star] Int[Sin[a+b*x]*(g*Sin[c+d*x])^(p+1),x] /;
        FreeQ[{a,b,c,d,g},x] && EqQ[b*c-a*d,0] && EqQ[d/b,2] && Not[IntegerQ[p]] && LtQ[p,-1] && IntegerQ[2*p]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, b__, g__, c__, d__, p_, x_],
        optional: [a__, b__, g__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, g__], x_)
                && eqq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(&d__ / &b__, 2)
                && !integerq!(p_)
                && ltq!(p_, -1)
                && integerq!(Atom::num(2) * &p_)
        },
        rhs: {
            let angle1 = &a__ + &b__ * x_;
            let angle2 = &c__ + &d__ * x_;
            let recursive = rubi_rhs_int(&(angle1.sin() * (&g__ * angle2.sin()).pow(&p_ + 1)), x_);

            rubi_simp(&(angle1.cos() * (&g__ * angle2.sin()).pow(&p_ + 1) / (2 * &b__ * &g__ * (&p_ + 1))), x_)
                    + rubi_star((Atom::num(2) * &p_ + 3) / (2 * &g__ * (&p_ + 1)), recursive)
        },
    ));
}

fn push_rules_rule_4792(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, g__, p_, x_);
    rules.push(rubi_rule!(
        order: 4792,
        source: "Int[sin[a_.+b_.*x_]*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
          -Sin[a+b*x]*(g*Sin[c+d*x])^(p+1)/(2*b*g*(p+1)) +
          (2*p+3)/(2*g*(p+1)) \\[Star] Int[Cos[a+b*x]*(g*Sin[c+d*x])^(p+1),x] /;
        FreeQ[{a,b,c,d,g},x] && EqQ[b*c-a*d,0] && EqQ[d/b,2] && Not[IntegerQ[p]] && LtQ[p,-1] && IntegerQ[2*p]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [a__, b__, g__, c__, d__, p_, x_],
        optional: [a__, b__, g__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, g__], x_)
                && eqq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(&d__ / &b__, 2)
                && !integerq!(p_)
                && ltq!(p_, -1)
                && integerq!(Atom::num(2) * &p_)
        },
        rhs: {
            let angle1 = &a__ + &b__ * x_;
            let angle2 = &c__ + &d__ * x_;
            let recursive = rubi_rhs_int(&(angle1.cos() * (&g__ * angle2.sin()).pow(&p_ + 1)), x_);

            rubi_simp(&(-angle1.sin() * (&g__ * angle2.sin()).pow(&p_ + 1) / (2 * &b__ * &g__ * (&p_ + 1))), x_)
                    + rubi_star((Atom::num(2) * &p_ + 3) / (2 * &g__ * (&p_ + 1)), recursive)
        },
    ));
}

fn push_rules_rule_4793(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 4793,
        source: "Int[cos[a_.+b_.*x_]/Sqrt[sin[c_.+d_.*x_]],x_Symbol] :=
          -ArcSin[Cos[a+b*x]-Sin[a+b*x]]/d + Log[Cos[a+b*x]+Sin[a+b*x]+Sqrt[Sin[c+d*x]]]/d /;
        FreeQ[{a,b,c,d},x] && EqQ[b*c-a*d,0] && EqQ[d/b,2]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: i_cos(a__ + b__ * x_) / i_sin(c__ + d__ * x_).sqrt(),
        with: [a__, b__, c__, d__, x_],
        optional: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && eqq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(&d__ / &b__, 2)
        },
        rhs: {
            let angle1 = &a__ + &b__ * x_;
            let angle2 = &c__ + &d__ * x_;

            rubi_simp(&(-(angle1.cos() - angle1.sin()).asin() / &d__), x_)
                    + rubi_simp(&((angle1.cos() + angle1.sin() + angle2.sin().sqrt()).log() / &d__), x_)
        },
    ));
}

fn push_rules_rule_4794(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 4794,
        source: "Int[sin[a_.+b_.*x_]/Sqrt[sin[c_.+d_.*x_]],x_Symbol] :=
          -ArcSin[Cos[a+b*x]-Sin[a+b*x]]/d - Log[Cos[a+b*x]+Sin[a+b*x]+Sqrt[Sin[c+d*x]]]/d /;
        FreeQ[{a,b,c,d},x] && EqQ[b*c-a*d,0] && EqQ[d/b,2]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: i_sin(a__ + b__ * x_) / i_sin(c__ + d__ * x_).sqrt(),
        with: [a__, b__, c__, d__, x_],
        optional: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && eqq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(&d__ / &b__, 2)
        },
        rhs: {
            let angle1 = &a__ + &b__ * x_;
            let angle2 = &c__ + &d__ * x_;

            rubi_simp(&(-(angle1.cos() - angle1.sin()).asin() / &d__), x_)
                    - rubi_simp(&((angle1.cos() + angle1.sin() + angle2.sin().sqrt()).log() / &d__), x_)
        },
    ));
}

fn push_rules_rule_4795(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, g__, p_, x_);
    rules.push(rubi_rule!(
        order: 4795,
        source: "Int[(g_.*sin[c_.+d_.*x_])^p_/cos[a_.+b_.*x_],x_Symbol] :=
          2*g \\[Star] Int[Sin[a+b*x]*(g*Sin[c+d*x])^(p-1),x] /;
        FreeQ[{a,b,c,d,g,p},x] && EqQ[b*c-a*d,0] && EqQ[d/b,2] && Not[IntegerQ[p]] && IntegerQ[2*p]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: (g__ * i_sin(c__ + d__ * x_)).pow(p_) / i_cos(a__ + b__ * x_),
        with: [g__, c__, d__, p_, a__, b__, x_],
        optional: [g__, c__, d__, a__, b__],
        when: {
            freeq!([a__, b__, c__, d__, g__, p_], x_)
                && eqq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(&d__ / &b__, 2)
                && !integerq!(p_)
                && integerq!(Atom::num(2) * &p_)
        },
        rhs: {
            let angle1 = &a__ + &b__ * x_;
            let angle2 = &c__ + &d__ * x_;
            let recursive = rubi_rhs_int(&(angle1.sin() * (&g__ * angle2.sin()).pow(&p_ - 1)), x_);

            rubi_star(Atom::num(2) * &g__, recursive)
        },
    ));
}

fn push_rules_rule_4796(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, g__, p_, x_);
    rules.push(rubi_rule!(
        order: 4796,
        source: "Int[(g_.*sin[c_.+d_.*x_])^p_/sin[a_.+b_.*x_],x_Symbol] :=
          2*g \\[Star] Int[Cos[a+b*x]*(g*Sin[c+d*x])^(p-1),x] /;
        FreeQ[{a,b,c,d,g,p},x] && EqQ[b*c-a*d,0] && EqQ[d/b,2] && Not[IntegerQ[p]] && IntegerQ[2*p]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: (g__ * i_sin(c__ + d__ * x_)).pow(p_) / i_sin(a__ + b__ * x_),
        with: [g__, c__, d__, p_, a__, b__, x_],
        optional: [g__, c__, d__, a__, b__],
        when: {
            freeq!([a__, b__, c__, d__, g__, p_], x_)
                && eqq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(&d__ / &b__, 2)
                && !integerq!(p_)
                && integerq!(Atom::num(2) * &p_)
        },
        rhs: {
            let angle1 = &a__ + &b__ * x_;
            let angle2 = &c__ + &d__ * x_;
            let recursive = rubi_rhs_int(&(angle1.cos() * (&g__ * angle2.sin()).pow(&p_ - 1)), x_);

            rubi_star(Atom::num(2) * &g__, recursive)
        },
    ));
}

fn push_rules_rule_4797(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 4797,
        source: "Int[(e_.*cos[a_.+b_.*x_])^m_.*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
          (g*Sin[c+d*x])^p/((e*Cos[a+b*x])^p*Sin[a+b*x]^p) \\[Star] Int[(e*Cos[a+b*x])^(m+p)*Sin[a+b*x]^p,x] /;
        FreeQ[{a,b,c,d,e,g,m,p},x] && EqQ[b*c-a*d,0] && EqQ[d/b,2] && Not[IntegerQ[p]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [e__, a__, b__, m_, g__, c__, d__, p_, x_],
        optional: [e__, a__, b__, m_, g__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, g__, m_, p_], x_)
                && eqq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(&d__ / &b__, 2)
                && !integerq!(p_)
        },
        rhs: {
            let angle1 = &a__ + &b__ * x_;
            let angle2 = &c__ + &d__ * x_;
            let recursive = rubi_rhs_int(&((&e__ * angle1.cos()).pow(&m_ + &p_) * angle1.sin().pow(&p_)), x_);

            let coefficient = (&g__ * angle2.sin()).pow(&p_)
                / ((&e__ * angle1.cos()).pow(&p_) * angle1.sin().pow(&p_));
            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_4798(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, f__, g__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 4798,
        source: "Int[(f_.*sin[a_.+b_.*x_])^n_.*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
          (g*Sin[c+d*x])^p/(Cos[a+b*x]^p*(f*Sin[a+b*x])^p) \\[Star] Int[Cos[a+b*x]^p*(f*Sin[a+b*x])^(n+p),x] /;
        FreeQ[{a,b,c,d,f,g,n,p},x] && EqQ[b*c-a*d,0] && EqQ[d/b,2] && Not[IntegerQ[p]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: (f__ * i_sin(a__ + b__ * x_)).pow(n_) * (g__ * i_sin(c__ + d__ * x_)).pow(p_),
        with: [f__, a__, b__, n_, g__, c__, d__, p_, x_],
        optional: [f__, a__, b__, n_, g__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, f__, g__, n_, p_], x_)
                && eqq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(&d__ / &b__, 2)
                && !integerq!(p_)
        },
        rhs: {
            let angle1 = &a__ + &b__ * x_;
            let angle2 = &c__ + &d__ * x_;
            let recursive = rubi_rhs_int(&(angle1.cos().pow(&p_) * (&f__ * angle1.sin()).pow(&n_ + &p_)), x_);

            let coefficient = (&g__ * angle2.sin()).pow(&p_)
                / (angle1.cos().pow(&p_) * (&f__ * angle1.sin()).pow(&p_));
            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_4799(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, g__, p_, x_);
    rules.push(rubi_rule!(
        order: 4799,
        source: "Int[cos[a_.+b_.*x_]^2*sin[a_.+b_.*x_]^2*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
          1/4 \\[Star] Int[(g*Sin[c+d*x])^p,x] -
          1/4 \\[Star] Int[Cos[c+d*x]^2*(g*Sin[c+d*x])^p,x] /;
        FreeQ[{a,b,c,d,g},x] && EqQ[b*c-a*d,0] && EqQ[d/b,2] && IGtQ[p/2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: i_cos(a__ + b__ * x_).pow(2) * i_sin(a__ + b__ * x_).pow(2) * (g__ * i_sin(c__ + d__ * x_)).pow(p_),
        with: [a__, b__, g__, c__, d__, p_, x_],
        optional: [a__, b__, g__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, g__], x_)
                && eqq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(&d__ / &b__, 2)
                && igtq!(&p_ / 2, 0)
        },
        rhs: {
            let angle2 = &c__ + &d__ * x_;
            let recursive1 = rubi_rhs_int(&((&g__ * angle2.sin()).pow(&p_)), x_);
            let recursive2 = rubi_rhs_int(&(angle2.cos().pow(2) * (&g__ * angle2.sin()).pow(&p_)), x_);

            rubi_star(Atom::num(1) / 4, recursive1)
                    - rubi_star(Atom::num(1) / 4, recursive2)
        },
    ));
}

fn push_rules_rule_4800(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 4800,
        source: "Int[(e_.*cos[a_.+b_.*x_])^m_.*(f_.*sin[a_.+b_.*x_])^n_.*sin[c_.+d_.*x_]^p_.,x_Symbol] :=
          2^p/(e^p*f^p) \\[Star] Int[(e*Cos[a+b*x])^(m+p)*(f*Sin[a+b*x])^(n+p),x] /;
        FreeQ[{a,b,c,d,e,f,m,n},x] && EqQ[b*c-a*d,0] && EqQ[d/b,2] && IntegerQ[p]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: (e__ * i_cos(a__ + b__ * x_)).pow(m_) * (f__ * i_sin(a__ + b__ * x_)).pow(n_) * i_sin(c__ + d__ * x_).pow(p_),
        with: [e__, a__, b__, m_, f__, n_, c__, d__, p_, x_],
        optional: [e__, a__, b__, m_, f__, n_, c__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_], x_)
                && eqq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(&d__ / &b__, 2)
                && integerq!(p_)
        },
        rhs: {
            let angle = &a__ + &b__ * x_;
            let recursive =
                rubi_rhs_int(&((&e__ * angle.cos()).pow(&m_ + &p_) * (&f__ * angle.sin()).pow(&n_ + &p_)), x_);

            let coefficient = Atom::num(2).pow(&p_) / (e__.pow(&p_) * f__.pow(&p_));
            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_4801(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 4801,
        source: "Int[(e_.*cos[a_.+b_.*x_])^m_.*(f_.*sin[a_.+b_.*x_])^n_.*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
          e*(e*Cos[a+b*x])^(m-1)*(f*Sin[a+b*x])^(n+1)*(g*Sin[c+d*x])^p/(b*f*(n+p+1)) /;
        FreeQ[{a,b,c,d,e,f,g,m,n,p},x] && EqQ[b*c-a*d,0] && EqQ[d/b,2] && Not[IntegerQ[p]] && EqQ[m+p+1,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [e__, a__, b__, m_, f__, n_, g__, c__, d__, p_, x_],
        optional: [e__, a__, b__, m_, f__, n_, g__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, m_, n_, p_], x_)
                && eqq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(&d__ / &b__, 2)
                && !integerq!(p_)
                && eqq!(&m_ + &p_ + 1, 0)
        },
        rhs: {
            let angle1 = &a__ + &b__ * x_;
            let angle2 = &c__ + &d__ * x_;

            rubi_simp(&(&e__ * (&e__ * angle1.cos()).pow(&m_ - 1)
                    * (&f__ * angle1.sin()).pow(&n_ + 1)
                    * (&g__ * angle2.sin()).pow(&p_)
                    / (&b__ * &f__ * (&n_ + &p_ + 1))), x_)
        },
    ));
}

fn push_rules_rule_4802(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 4802,
        source: "Int[(e_.*sin[a_.+b_.*x_])^m_*(f_.*cos[a_.+b_.*x_])^n_*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
          -e*(e*Sin[a+b*x])^(m-1)*(f*Cos[a+b*x])^(n+1)*(g*Sin[c+d*x])^p/(b*f*(n+p+1)) /;
        FreeQ[{a,b,c,d,e,f,g,m,n,p},x] && EqQ[b*c-a*d,0] && EqQ[d/b,2] && Not[IntegerQ[p]] && EqQ[m+p+1,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [e__, a__, b__, m_, f__, n_, g__, c__, d__, p_, x_],
        optional: [e__, a__, b__, f__, g__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, m_, n_, p_], x_)
                && eqq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(&d__ / &b__, 2)
                && !integerq!(p_)
                && eqq!(&m_ + &p_ + 1, 0)
        },
        rhs: {
            let angle1 = &a__ + &b__ * x_;
            let angle2 = &c__ + &d__ * x_;

            rubi_simp(&(-&e__ * (&e__ * angle1.sin()).pow(&m_ - 1)
                    * (&f__ * angle1.cos()).pow(&n_ + 1)
                    * (&g__ * angle2.sin()).pow(&p_)
                    / (&b__ * &f__ * (&n_ + &p_ + 1))), x_)
        },
    ));
}

fn push_rules_rule_4803(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 4803,
        source: "Int[(e_.*cos[a_.+b_.*x_])^m_.*(f_.*sin[a_.+b_.*x_])^n_.*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
          -(e*Cos[a+b*x])^(m+1)*(f*Sin[a+b*x])^(n+1)*(g*Sin[c+d*x])^p/(b*e*f*(m+p+1)) /;
        FreeQ[{a,b,c,d,e,f,g,m,n,p},x] && EqQ[b*c-a*d,0] && EqQ[d/b,2] && Not[IntegerQ[p]] && EqQ[m+n+2*p+2,0] && NeQ[m+p+1,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [e__, a__, b__, m_, f__, n_, g__, c__, d__, p_, x_],
        optional: [e__, a__, b__, m_, f__, n_, g__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, m_, n_, p_], x_)
                && eqq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(&d__ / &b__, 2)
                && !integerq!(p_)
                && eqq!(&m_ + &n_ + Atom::num(2) * &p_ + 2, 0)
                && neq!(&m_ + &p_ + 1, 0)
        },
        rhs: {
            let angle1 = &a__ + &b__ * x_;
            let angle2 = &c__ + &d__ * x_;

            rubi_simp(&(-(&e__ * angle1.cos()).pow(&m_ + 1)
                    * (&f__ * angle1.sin()).pow(&n_ + 1)
                    * (&g__ * angle2.sin()).pow(&p_)
                    / (&b__ * &e__ * &f__ * (&m_ + &p_ + 1))), x_)
        },
    ));
}

fn push_rules_rule_4804(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 4804,
        source: "Int[(e_.*cos[a_.+b_.*x_])^m_*(f_.*sin[a_.+b_.*x_])^n_*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
          e^2*(e*Cos[a+b*x])^(m-2)*(f*Sin[a+b*x])^n*(g*Sin[c+d*x])^(p+1)/(2*b*g*(n+p+1)) +
          e^4*(m+p-1)/(4*g^2*(n+p+1)) \\[Star] Int[(e*Cos[a+b*x])^(m-4)*(f*Sin[a+b*x])^n*(g*Sin[c+d*x])^(p+2),x] /;
        FreeQ[{a,b,c,d,e,f,g,n},x] && EqQ[b*c-a*d,0] && EqQ[d/b,2] && Not[IntegerQ[p]] && GtQ[m,3] && LtQ[p,-1] && NeQ[n+p+1,0] && IntegersQ[2*m,2*n,2*p]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [e__, a__, b__, m_, f__, n_, g__, c__, d__, p_, x_],
        optional: [e__, a__, b__, f__, g__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, n_], x_)
                && eqq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(&d__ / &b__, 2)
                && !integerq!(p_)
                && gtq!(m_, 3)
                && ltq!(p_, -1)
                && neq!(&n_ + &p_ + 1, 0)
                && integersq!([Atom::num(2) * &m_, Atom::num(2) * &n_, Atom::num(2) * &p_])
        },
        rhs: {
            let angle1 = &a__ + &b__ * x_;
            let angle2 = &c__ + &d__ * x_;
            let recursive = rubi_rhs_int(
                &((&e__ * angle1.cos()).pow(&m_ - 4)
                    * (&f__ * angle1.sin()).pow(&n_)
                    * (&g__ * angle2.sin()).pow(&p_ + 2)),
                x_,
            );
            let coefficient = e__.pow(4) * (&m_ + &p_ - 1)
                / (4 * g__.pow(2) * (&n_ + &p_ + 1));

            rubi_simp(&(e__.pow(2)
                    * (&e__ * angle1.cos()).pow(&m_ - 2)
                    * (&f__ * angle1.sin()).pow(&n_)
                    * (&g__ * angle2.sin()).pow(&p_ + 1)
                    / (2 * &b__ * &g__ * (&n_ + &p_ + 1))), x_)
                    + rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_4805(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 4805,
        source: "Int[(e_.*sin[a_.+b_.*x_])^m_*(f_.*cos[a_.+b_.*x_])^n_*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
          -e^2*(e*Sin[a+b*x])^(m-2)*(f*Cos[a+b*x])^n*(g*Sin[c+d*x])^(p+1)/(2*b*g*(n+p+1)) +
          e^4*(m+p-1)/(4*g^2*(n+p+1)) \\[Star] Int[(e*Sin[a+b*x])^(m-4)*(f*Cos[a+b*x])^n*(g*Sin[c+d*x])^(p+2),x] /;
        FreeQ[{a,b,c,d,e,f,g,n},x] && EqQ[b*c-a*d,0] && EqQ[d/b,2] && Not[IntegerQ[p]] && GtQ[m,3] && LtQ[p,-1] && NeQ[n+p+1,0] && IntegersQ[2*m,2*n,2*p]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [e__, a__, b__, m_, f__, n_, g__, c__, d__, p_, x_],
        optional: [e__, a__, b__, f__, g__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, n_], x_)
                && eqq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(&d__ / &b__, 2)
                && !integerq!(p_)
                && gtq!(m_, 3)
                && ltq!(p_, -1)
                && neq!(&n_ + &p_ + 1, 0)
                && integersq!([Atom::num(2) * &m_, Atom::num(2) * &n_, Atom::num(2) * &p_])
        },
        rhs: {
            let angle1 = &a__ + &b__ * x_;
            let angle2 = &c__ + &d__ * x_;
            let recursive = rubi_rhs_int(
                &((&e__ * angle1.sin()).pow(&m_ - 4)
                    * (&f__ * angle1.cos()).pow(&n_)
                    * (&g__ * angle2.sin()).pow(&p_ + 2)),
                x_,
            );
            let coefficient = e__.pow(4) * (&m_ + &p_ - 1)
                / (4 * g__.pow(2) * (&n_ + &p_ + 1));

            rubi_simp(&(-e__.pow(2)
                    * (&e__ * angle1.sin()).pow(&m_ - 2)
                    * (&f__ * angle1.cos()).pow(&n_)
                    * (&g__ * angle2.sin()).pow(&p_ + 1)
                    / (2 * &b__ * &g__ * (&n_ + &p_ + 1))), x_)
                    + rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_4806(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 4806,
        source: "Int[(e_.*cos[a_.+b_.*x_])^m_*(f_.*sin[a_.+b_.*x_])^n_.*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
          (e*Cos[a+b*x])^m*(f*Sin[a+b*x])^n*(g*Sin[c+d*x])^(p+1)/(2*b*g*(n+p+1)) +
          e^2*(m+n+2*p+2)/(4*g^2*(n+p+1)) \\[Star] Int[(e*Cos[a+b*x])^(m-2)*(f*Sin[a+b*x])^n*(g*Sin[c+d*x])^(p+2),x] /;
        FreeQ[{a,b,c,d,e,f,g,n},x] && EqQ[b*c-a*d,0] && EqQ[d/b,2] && Not[IntegerQ[p]] && GtQ[m,1] && LtQ[p,-1] && NeQ[m+n+2*p+2,0] && NeQ[n+p+1,0] &&
          IntegersQ[2*m,2*n,2*p] && (LtQ[p,-2] || EqQ[m,2] || EqQ[m,3])",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [e__, a__, b__, m_, f__, n_, g__, c__, d__, p_, x_],
        optional: [e__, a__, b__, f__, n_, g__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, n_], x_)
                && eqq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(&d__ / &b__, 2)
                && !integerq!(p_)
                && gtq!(m_, 1)
                && ltq!(p_, -1)
                && neq!(&m_ + &n_ + Atom::num(2) * &p_ + 2, 0)
                && neq!(&n_ + &p_ + 1, 0)
                && integersq!([Atom::num(2) * &m_, Atom::num(2) * &n_, Atom::num(2) * &p_])
                && (ltq!(p_, -2) || eqq!(m_, 2) || eqq!(m_, 3))
        },
        rhs: {
            let angle1 = &a__ + &b__ * x_;
            let angle2 = &c__ + &d__ * x_;
            let recursive = rubi_rhs_int(
                &((&e__ * angle1.cos()).pow(&m_ - 2)
                    * (&f__ * angle1.sin()).pow(&n_)
                    * (&g__ * angle2.sin()).pow(&p_ + 2)),
                x_,
            );
            let coefficient = e__.pow(2) * (&m_ + &n_ + Atom::num(2) * &p_ + 2)
                / (4 * g__.pow(2) * (&n_ + &p_ + 1));

            rubi_simp(&((&e__ * angle1.cos()).pow(&m_)
                    * (&f__ * angle1.sin()).pow(&n_)
                    * (&g__ * angle2.sin()).pow(&p_ + 1)
                    / (2 * &b__ * &g__ * (&n_ + &p_ + 1))), x_)
                    + rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_4807(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 4807,
        source: "Int[(e_.*sin[a_.+b_.*x_])^m_*(f_.*cos[a_.+b_.*x_])^n_.*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
          -(e*Sin[a+b*x])^m*(f*Cos[a+b*x])^n*(g*Sin[c+d*x])^(p+1)/(2*b*g*(n+p+1)) +
          e^2*(m+n+2*p+2)/(4*g^2*(n+p+1)) \\[Star] Int[(e*Sin[a+b*x])^(m-2)*(f*Cos[a+b*x])^n*(g*Sin[c+d*x])^(p+2),x] /;
        FreeQ[{a,b,c,d,e,f,g,n},x] && EqQ[b*c-a*d,0] && EqQ[d/b,2] && Not[IntegerQ[p]] && GtQ[m,1] && LtQ[p,-1] && NeQ[m+n+2*p+2,0] && NeQ[n+p+1,0] &&
          IntegersQ[2*m,2*n,2*p] && (LtQ[p,-2] || EqQ[m,2] || EqQ[m,3])",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [e__, a__, b__, m_, f__, n_, g__, c__, d__, p_, x_],
        optional: [e__, a__, b__, f__, n_, g__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, n_], x_)
                && eqq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(&d__ / &b__, 2)
                && !integerq!(p_)
                && gtq!(m_, 1)
                && ltq!(p_, -1)
                && neq!(&m_ + &n_ + Atom::num(2) * &p_ + 2, 0)
                && neq!(&n_ + &p_ + 1, 0)
                && integersq!([Atom::num(2) * &m_, Atom::num(2) * &n_, Atom::num(2) * &p_])
                && (ltq!(p_, -2) || eqq!(m_, 2) || eqq!(m_, 3))
        },
        rhs: {
            let angle1 = &a__ + &b__ * x_;
            let angle2 = &c__ + &d__ * x_;
            let recursive = rubi_rhs_int(
                &((&e__ * angle1.sin()).pow(&m_ - 2)
                    * (&f__ * angle1.cos()).pow(&n_)
                    * (&g__ * angle2.sin()).pow(&p_ + 2)),
                x_,
            );
            let coefficient = e__.pow(2) * (&m_ + &n_ + Atom::num(2) * &p_ + 2)
                / (4 * g__.pow(2) * (&n_ + &p_ + 1));

            rubi_simp(&(-(&e__ * angle1.sin()).pow(&m_)
                    * (&f__ * angle1.cos()).pow(&n_)
                    * (&g__ * angle2.sin()).pow(&p_ + 1)
                    / (2 * &b__ * &g__ * (&n_ + &p_ + 1))), x_)
                    + rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_4808(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 4808,
        source: "Int[(e_.*cos[a_.+b_.*x_])^m_*(f_.*sin[a_.+b_.*x_])^n_*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
          e*(e*Cos[a+b*x])^(m-1)*(f*Sin[a+b*x])^(n+1)*(g*Sin[c+d*x])^p/(b*f*(n+p+1)) +
          e^2*(m+p-1)/(f^2*(n+p+1)) \\[Star] Int[(e*Cos[a+b*x])^(m-2)*(f*Sin[a+b*x])^(n+2)*(g*Sin[c+d*x])^p,x] /;
        FreeQ[{a,b,c,d,e,f,g,p},x] && EqQ[b*c-a*d,0] && EqQ[d/b,2] && Not[IntegerQ[p]] && GtQ[m,1] && LtQ[n,-1] && NeQ[n+p+1,0] && IntegersQ[2*m,2*n,2*p]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [e__, a__, b__, m_, f__, n_, g__, c__, d__, p_, x_],
        optional: [e__, a__, b__, f__, g__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, p_], x_)
                && eqq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(&d__ / &b__, 2)
                && !integerq!(p_)
                && gtq!(m_, 1)
                && ltq!(n_, -1)
                && neq!(&n_ + &p_ + 1, 0)
                && integersq!([Atom::num(2) * &m_, Atom::num(2) * &n_, Atom::num(2) * &p_])
        },
        rhs: {
            let angle1 = &a__ + &b__ * x_;
            let angle2 = &c__ + &d__ * x_;
            let recursive = rubi_rhs_int(
                &((&e__ * angle1.cos()).pow(&m_ - 2)
                    * (&f__ * angle1.sin()).pow(&n_ + 2)
                    * (&g__ * angle2.sin()).pow(&p_)),
                x_,
            );
            let coefficient = e__.pow(2) * (&m_ + &p_ - 1)
                / (f__.pow(2) * (&n_ + &p_ + 1));

            rubi_simp(&(&e__ * (&e__ * angle1.cos()).pow(&m_ - 1)
                    * (&f__ * angle1.sin()).pow(&n_ + 1)
                    * (&g__ * angle2.sin()).pow(&p_)
                    / (&b__ * &f__ * (&n_ + &p_ + 1))), x_)
                    + rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_4809(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 4809,
        source: "Int[(e_.*sin[a_.+b_.*x_])^m_*(f_.*cos[a_.+b_.*x_])^n_*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
          -e*(e*Sin[a+b*x])^(m-1)*(f*Cos[a+b*x])^(n+1)*(g*Sin[c+d*x])^p/(b*f*(n+p+1)) +
          e^2*(m+p-1)/(f^2*(n+p+1)) \\[Star] Int[(e*Sin[a+b*x])^(m-2)*(f*Cos[a+b*x])^(n+2)*(g*Sin[c+d*x])^p,x] /;
        FreeQ[{a,b,c,d,e,f,g,p},x] && EqQ[b*c-a*d,0] && EqQ[d/b,2] && Not[IntegerQ[p]] && GtQ[m,1] && LtQ[n,-1] && NeQ[n+p+1,0] && IntegersQ[2*m,2*n,2*p]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [e__, a__, b__, m_, f__, n_, g__, c__, d__, p_, x_],
        optional: [e__, a__, b__, f__, g__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, p_], x_)
                && eqq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(&d__ / &b__, 2)
                && !integerq!(p_)
                && gtq!(m_, 1)
                && ltq!(n_, -1)
                && neq!(&n_ + &p_ + 1, 0)
                && integersq!([Atom::num(2) * &m_, Atom::num(2) * &n_, Atom::num(2) * &p_])
        },
        rhs: {
            let angle1 = &a__ + &b__ * x_;
            let angle2 = &c__ + &d__ * x_;
            let recursive = rubi_rhs_int(
                &((&e__ * angle1.sin()).pow(&m_ - 2)
                    * (&f__ * angle1.cos()).pow(&n_ + 2)
                    * (&g__ * angle2.sin()).pow(&p_)),
                x_,
            );
            let coefficient = e__.pow(2) * (&m_ + &p_ - 1)
                / (f__.pow(2) * (&n_ + &p_ + 1));

            rubi_simp(&(-&e__ * (&e__ * angle1.sin()).pow(&m_ - 1)
                    * (&f__ * angle1.cos()).pow(&n_ + 1)
                    * (&g__ * angle2.sin()).pow(&p_)
                    / (&b__ * &f__ * (&n_ + &p_ + 1))), x_)
                    + rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_4810(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 4810,
        source: "Int[(e_.*cos[a_.+b_.*x_])^m_*(f_.*sin[a_.+b_.*x_])^n_.*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
          e*(e*Cos[a+b*x])^(m-1)*(f*Sin[a+b*x])^(n+1)*(g*Sin[c+d*x])^p/(b*f*(m+n+2*p)) +
          e^2*(m+p-1)/(m+n+2*p) \\[Star] Int[(e*Cos[a+b*x])^(m-2)*(f*Sin[a+b*x])^n*(g*Sin[c+d*x])^p,x] /;
        FreeQ[{a,b,c,d,e,f,g,n,p},x] && EqQ[b*c-a*d,0] && EqQ[d/b,2] && Not[IntegerQ[p]] && GtQ[m,1] && NeQ[m+n+2*p,0] && IntegersQ[2*m,2*n,2*p]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [e__, a__, b__, m_, f__, n_, g__, c__, d__, p_, x_],
        optional: [e__, a__, b__, f__, n_, g__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, n_, p_], x_)
                && eqq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(&d__ / &b__, 2)
                && !integerq!(p_)
                && gtq!(m_, 1)
                && neq!(&m_ + &n_ + Atom::num(2) * &p_, 0)
                && integersq!([Atom::num(2) * &m_, Atom::num(2) * &n_, Atom::num(2) * &p_])
        },
        rhs: {
            let angle1 = &a__ + &b__ * x_;
            let angle2 = &c__ + &d__ * x_;
            let recursive = rubi_rhs_int(
                &((&e__ * angle1.cos()).pow(&m_ - 2)
                    * (&f__ * angle1.sin()).pow(&n_)
                    * (&g__ * angle2.sin()).pow(&p_)),
                x_,
            );
            let coefficient = e__.pow(2) * (&m_ + &p_ - 1)
                / (&m_ + &n_ + Atom::num(2) * &p_);

            rubi_simp(&(&e__ * (&e__ * angle1.cos()).pow(&m_ - 1)
                    * (&f__ * angle1.sin()).pow(&n_ + 1)
                    * (&g__ * angle2.sin()).pow(&p_)
                    / (&b__ * &f__ * (&m_ + &n_ + Atom::num(2) * &p_))), x_)
                    + rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_4811(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 4811,
        source: "Int[(e_.*sin[a_.+b_.*x_])^m_*(f_.*cos[a_.+b_.*x_])^n_.*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
          -e*(e*Sin[a+b*x])^(m-1)*(f*Cos[a+b*x])^(n+1)*(g*Sin[c+d*x])^p/(b*f*(m+n+2*p)) +
          e^2*(m+p-1)/(m+n+2*p) \\[Star] Int[(e*Sin[a+b*x])^(m-2)*(f*Cos[a+b*x])^n*(g*Sin[c+d*x])^p,x] /;
        FreeQ[{a,b,c,d,e,f,g,n,p},x] && EqQ[b*c-a*d,0] && EqQ[d/b,2] && Not[IntegerQ[p]] && GtQ[m,1] && NeQ[m+n+2*p,0] && IntegersQ[2*m,2*n,2*p]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [e__, a__, b__, m_, f__, n_, g__, c__, d__, p_, x_],
        optional: [e__, a__, b__, f__, n_, g__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, n_, p_], x_)
                && eqq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(&d__ / &b__, 2)
                && !integerq!(p_)
                && gtq!(m_, 1)
                && neq!(&m_ + &n_ + Atom::num(2) * &p_, 0)
                && integersq!([Atom::num(2) * &m_, Atom::num(2) * &n_, Atom::num(2) * &p_])
        },
        rhs: {
            let angle1 = &a__ + &b__ * x_;
            let angle2 = &c__ + &d__ * x_;
            let recursive = rubi_rhs_int(
                &((&e__ * angle1.sin()).pow(&m_ - 2)
                    * (&f__ * angle1.cos()).pow(&n_)
                    * (&g__ * angle2.sin()).pow(&p_)),
                x_,
            );
            let coefficient = e__.pow(2) * (&m_ + &p_ - 1)
                / (&m_ + &n_ + Atom::num(2) * &p_);

            rubi_simp(&(-&e__ * (&e__ * angle1.sin()).pow(&m_ - 1)
                    * (&f__ * angle1.cos()).pow(&n_ + 1)
                    * (&g__ * angle2.sin()).pow(&p_)
                    / (&b__ * &f__ * (&m_ + &n_ + Atom::num(2) * &p_))), x_)
                    + rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_4812(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 4812,
        source: "Int[(e_.*cos[a_.+b_.*x_])^m_*(f_.*sin[a_.+b_.*x_])^n_.*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
          -f*(e*Cos[a+b*x])^(m+1)*(f*Sin[a+b*x])^(n-1)*(g*Sin[c+d*x])^p/(b*e*(m+n+2*p)) +
          2*f*g*(n+p-1)/(e*(m+n+2*p)) \\[Star] Int[(e*Cos[a+b*x])^(m+1)*(f*Sin[a+b*x])^(n-1)*(g*Sin[c+d*x])^(p-1),x] /;
        FreeQ[{a,b,c,d,e,f,g},x] && EqQ[b*c-a*d,0] && EqQ[d/b,2] && Not[IntegerQ[p]] && LtQ[m,-1] && GtQ[n,0] && GtQ[p,0] && NeQ[m+n+2*p,0] &&
          IntegersQ[2*m,2*n,2*p]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [e__, a__, b__, m_, f__, n_, g__, c__, d__, p_, x_],
        optional: [e__, a__, b__, f__, n_, g__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__], x_)
                && eqq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(&d__ / &b__, 2)
                && !integerq!(p_)
                && ltq!(m_, -1)
                && gtq!(n_, 0)
                && gtq!(p_, 0)
                && neq!(&m_ + &n_ + Atom::num(2) * &p_, 0)
                && integersq!([Atom::num(2) * &m_, Atom::num(2) * &n_, Atom::num(2) * &p_])
        },
        rhs: {
            let angle1 = &a__ + &b__ * x_;
            let angle2 = &c__ + &d__ * x_;
            let recursive = rubi_rhs_int(
                &((&e__ * angle1.cos()).pow(&m_ + 1)
                    * (&f__ * angle1.sin()).pow(&n_ - 1)
                    * (&g__ * angle2.sin()).pow(&p_ - 1)),
                x_,
            );
            let coefficient = Atom::num(2) * &f__ * &g__ * (&n_ + &p_ - 1)
                / (&e__ * (&m_ + &n_ + Atom::num(2) * &p_));

            rubi_simp(&(-&f__ * (&e__ * angle1.cos()).pow(&m_ + 1)
                    * (&f__ * angle1.sin()).pow(&n_ - 1)
                    * (&g__ * angle2.sin()).pow(&p_)
                    / (&b__ * &e__ * (&m_ + &n_ + Atom::num(2) * &p_))), x_)
                    + rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_4813(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 4813,
        source: "Int[(e_.*sin[a_.+b_.*x_])^m_*(f_.*cos[a_.+b_.*x_])^n_.*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
          f*(e*Sin[a+b*x])^(m+1)*(f*Cos[a+b*x])^(n-1)*(g*Sin[c+d*x])^p/(b*e*(m+n+2*p)) +
          2*f*g*(n+p-1)/(e*(m+n+2*p)) \\[Star] Int[(e*Sin[a+b*x])^(m+1)*(f*Cos[a+b*x])^(n-1)*(g*Sin[c+d*x])^(p-1),x] /;
        FreeQ[{a,b,c,d,e,f,g},x] && EqQ[b*c-a*d,0] && EqQ[d/b,2] && Not[IntegerQ[p]] && LtQ[m,-1] && GtQ[n,0] && GtQ[p,0] && NeQ[m+n+2*p,0] &&
          IntegersQ[2*m,2*n,2*p]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [e__, a__, b__, m_, f__, n_, g__, c__, d__, p_, x_],
        optional: [e__, a__, b__, f__, n_, g__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__], x_)
                && eqq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(&d__ / &b__, 2)
                && !integerq!(p_)
                && ltq!(m_, -1)
                && gtq!(n_, 0)
                && gtq!(p_, 0)
                && neq!(&m_ + &n_ + Atom::num(2) * &p_, 0)
                && integersq!([Atom::num(2) * &m_, Atom::num(2) * &n_, Atom::num(2) * &p_])
        },
        rhs: {
            let angle1 = &a__ + &b__ * x_;
            let angle2 = &c__ + &d__ * x_;
            let recursive = rubi_rhs_int(
                &((&e__ * angle1.sin()).pow(&m_ + 1)
                    * (&f__ * angle1.cos()).pow(&n_ - 1)
                    * (&g__ * angle2.sin()).pow(&p_ - 1)),
                x_,
            );
            let coefficient = Atom::num(2) * &f__ * &g__ * (&n_ + &p_ - 1)
                / (&e__ * (&m_ + &n_ + Atom::num(2) * &p_));

            rubi_simp(&(&f__ * (&e__ * angle1.sin()).pow(&m_ + 1)
                    * (&f__ * angle1.cos()).pow(&n_ - 1)
                    * (&g__ * angle2.sin()).pow(&p_)
                    / (&b__ * &e__ * (&m_ + &n_ + Atom::num(2) * &p_))), x_)
                    + rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_4814(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 4814,
        source: "Int[(e_.*cos[a_.+b_.*x_])^m_*(f_.*sin[a_.+b_.*x_])^n_.*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
          -(e*Cos[a+b*x])^(m+1)*(f*Sin[a+b*x])^(n+1)*(g*Sin[c+d*x])^p/(b*e*f*(m+p+1)) +
          f*(m+n+2*p+2)/(2*e*g*(m+p+1)) \\[Star] Int[(e*Cos[a+b*x])^(m+1)*(f*Sin[a+b*x])^(n-1)*(g*Sin[c+d*x])^(p+1),x] /;
        FreeQ[{a,b,c,d,e,f,g},x] && EqQ[b*c-a*d,0] && EqQ[d/b,2] && Not[IntegerQ[p]] && LtQ[m,-1] && GtQ[n,0] && LtQ[p,-1] && NeQ[m+n+2*p+2,0] &&
          NeQ[m+p+1,0] && IntegersQ[2*m,2*n,2*p]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [e__, a__, b__, m_, f__, n_, g__, c__, d__, p_, x_],
        optional: [e__, a__, b__, f__, n_, g__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__], x_)
                && eqq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(&d__ / &b__, 2)
                && !integerq!(p_)
                && ltq!(m_, -1)
                && gtq!(n_, 0)
                && ltq!(p_, -1)
                && neq!(&m_ + &n_ + Atom::num(2) * &p_ + 2, 0)
                && neq!(&m_ + &p_ + 1, 0)
                && integersq!([Atom::num(2) * &m_, Atom::num(2) * &n_, Atom::num(2) * &p_])
        },
        rhs: {
            let angle1 = &a__ + &b__ * x_;
            let angle2 = &c__ + &d__ * x_;
            let recursive = rubi_rhs_int(
                &((&e__ * angle1.cos()).pow(&m_ + 1)
                    * (&f__ * angle1.sin()).pow(&n_ - 1)
                    * (&g__ * angle2.sin()).pow(&p_ + 1)),
                x_,
            );
            let coefficient = &f__ * (&m_ + &n_ + Atom::num(2) * &p_ + 2)
                / (Atom::num(2) * &e__ * &g__ * (&m_ + &p_ + 1));

            rubi_simp(&(-(&e__ * angle1.cos()).pow(&m_ + 1)
                    * (&f__ * angle1.sin()).pow(&n_ + 1)
                    * (&g__ * angle2.sin()).pow(&p_)
                    / (&b__ * &e__ * &f__ * (&m_ + &p_ + 1))), x_)
                    + rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_4815(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 4815,
        source: "Int[(e_.*sin[a_.+b_.*x_])^m_*(f_.*cos[a_.+b_.*x_])^n_.*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
          (e*Sin[a+b*x])^(m+1)*(f*Cos[a+b*x])^(n+1)*(g*Sin[c+d*x])^p/(b*e*f*(m+p+1)) +
          f*(m+n+2*p+2)/(2*e*g*(m+p+1)) \\[Star] Int[(e*Sin[a+b*x])^(m+1)*(f*Cos[a+b*x])^(n-1)*(g*Sin[c+d*x])^(p+1),x] /;
        FreeQ[{a,b,c,d,e,f,g},x] && EqQ[b*c-a*d,0] && EqQ[d/b,2] && Not[IntegerQ[p]] && LtQ[m,-1] && GtQ[n,0] && LtQ[p,-1] && NeQ[m+n+2*p+2,0] &&
          NeQ[m+p+1,0] && IntegersQ[2*m,2*n,2*p]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [e__, a__, b__, m_, f__, n_, g__, c__, d__, p_, x_],
        optional: [e__, a__, b__, f__, n_, g__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__], x_)
                && eqq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(&d__ / &b__, 2)
                && !integerq!(p_)
                && ltq!(m_, -1)
                && gtq!(n_, 0)
                && ltq!(p_, -1)
                && neq!(&m_ + &n_ + Atom::num(2) * &p_ + 2, 0)
                && neq!(&m_ + &p_ + 1, 0)
                && integersq!([Atom::num(2) * &m_, Atom::num(2) * &n_, Atom::num(2) * &p_])
        },
        rhs: {
            let angle1 = &a__ + &b__ * x_;
            let angle2 = &c__ + &d__ * x_;
            let recursive = rubi_rhs_int(
                &((&e__ * angle1.sin()).pow(&m_ + 1)
                    * (&f__ * angle1.cos()).pow(&n_ - 1)
                    * (&g__ * angle2.sin()).pow(&p_ + 1)),
                x_,
            );
            let coefficient = &f__ * (&m_ + &n_ + Atom::num(2) * &p_ + 2)
                / (Atom::num(2) * &e__ * &g__ * (&m_ + &p_ + 1));

            rubi_simp(&((&e__ * angle1.sin()).pow(&m_ + 1)
                    * (&f__ * angle1.cos()).pow(&n_ + 1)
                    * (&g__ * angle2.sin()).pow(&p_)
                    / (&b__ * &e__ * &f__ * (&m_ + &p_ + 1))), x_)
                    + rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_4816(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 4816,
        source: "Int[(e_.*cos[a_.+b_.*x_])^m_*(f_.*sin[a_.+b_.*x_])^n_.*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
          -(e*Cos[a+b*x])^(m+1)*(f*Sin[a+b*x])^(n+1)*(g*Sin[c+d*x])^p/(b*e*f*(m+p+1)) +
          (m+n+2*p+2)/(e^2*(m+p+1)) \\[Star] Int[(e*Cos[a+b*x])^(m+2)*(f*Sin[a+b*x])^n*(g*Sin[c+d*x])^p,x] /;
        FreeQ[{a,b,c,d,e,f,g,n,p},x] && EqQ[b*c-a*d,0] && EqQ[d/b,2] && Not[IntegerQ[p]] && LtQ[m,-1] && NeQ[m+n+2*p+2,0] && NeQ[m+p+1,0] &&
          IntegersQ[2*m,2*n,2*p]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [e__, a__, b__, m_, f__, n_, g__, c__, d__, p_, x_],
        optional: [e__, a__, b__, f__, n_, g__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, n_, p_], x_)
                && eqq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(&d__ / &b__, 2)
                && !integerq!(p_)
                && ltq!(m_, -1)
                && neq!(&m_ + &n_ + Atom::num(2) * &p_ + 2, 0)
                && neq!(&m_ + &p_ + 1, 0)
                && integersq!([Atom::num(2) * &m_, Atom::num(2) * &n_, Atom::num(2) * &p_])
        },
        rhs: {
            let angle1 = &a__ + &b__ * x_;
            let angle2 = &c__ + &d__ * x_;
            let recursive = rubi_rhs_int(
                &((&e__ * angle1.cos()).pow(&m_ + 2)
                    * (&f__ * angle1.sin()).pow(&n_)
                    * (&g__ * angle2.sin()).pow(&p_)),
                x_,
            );
            let coefficient = (&m_ + &n_ + Atom::num(2) * &p_ + 2)
                / (e__.pow(2) * (&m_ + &p_ + 1));

            rubi_simp(&(-(&e__ * angle1.cos()).pow(&m_ + 1)
                    * (&f__ * angle1.sin()).pow(&n_ + 1)
                    * (&g__ * angle2.sin()).pow(&p_)
                    / (&b__ * &e__ * &f__ * (&m_ + &p_ + 1))), x_)
                    + rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_4817(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 4817,
        source: "Int[(e_.*sin[a_.+b_.*x_])^m_*(f_.*cos[a_.+b_.*x_])^n_.*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
          (e*Sin[a+b*x])^(m+1)*(f*Cos[a+b*x])^(n+1)*(g*Sin[c+d*x])^p/(b*e*f*(m+p+1)) +
          (m+n+2*p+2)/(e^2*(m+p+1)) \\[Star] Int[(e*Sin[a+b*x])^(m+2)*(f*Cos[a+b*x])^n*(g*Sin[c+d*x])^p,x] /;
        FreeQ[{a,b,c,d,e,f,g,n,p},x] && EqQ[b*c-a*d,0] && EqQ[d/b,2] && Not[IntegerQ[p]] && LtQ[m,-1] && NeQ[m+n+2*p+2,0] && NeQ[m+p+1,0] &&
          IntegersQ[2*m,2*n,2*p]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [e__, a__, b__, m_, f__, n_, g__, c__, d__, p_, x_],
        optional: [e__, a__, b__, f__, n_, g__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, n_, p_], x_)
                && eqq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(&d__ / &b__, 2)
                && !integerq!(p_)
                && ltq!(m_, -1)
                && neq!(&m_ + &n_ + Atom::num(2) * &p_ + 2, 0)
                && neq!(&m_ + &p_ + 1, 0)
                && integersq!([Atom::num(2) * &m_, Atom::num(2) * &n_, Atom::num(2) * &p_])
        },
        rhs: {
            let angle1 = &a__ + &b__ * x_;
            let angle2 = &c__ + &d__ * x_;
            let recursive = rubi_rhs_int(
                &((&e__ * angle1.sin()).pow(&m_ + 2)
                    * (&f__ * angle1.cos()).pow(&n_)
                    * (&g__ * angle2.sin()).pow(&p_)),
                x_,
            );
            let coefficient = (&m_ + &n_ + Atom::num(2) * &p_ + 2)
                / (e__.pow(2) * (&m_ + &p_ + 1));

            rubi_simp(&((&e__ * angle1.sin()).pow(&m_ + 1)
                    * (&f__ * angle1.cos()).pow(&n_ + 1)
                    * (&g__ * angle2.sin()).pow(&p_)
                    / (&b__ * &e__ * &f__ * (&m_ + &p_ + 1))), x_)
                    + rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_4818(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 4818,
        source: "Int[(e_.*cos[a_.+b_.*x_])^m_.*(f_.*sin[a_.+b_.*x_])^n_.*(g_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
          (g*Sin[c+d*x])^p/((e*Cos[a+b*x])^p*(f*Sin[a+b*x])^p) \\[Star] Int[(e*Cos[a+b*x])^(m+p)*(f*Sin[a+b*x])^(n+p),x] /;
        FreeQ[{a,b,c,d,e,f,g,m,n,p},x] && EqQ[b*c-a*d,0] && EqQ[d/b,2] && Not[IntegerQ[p]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [e__, a__, b__, m_, f__, n_, g__, c__, d__, p_, x_],
        optional: [e__, a__, b__, m_, f__, n_, g__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, m_, n_, p_], x_)
                && eqq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(&d__ / &b__, 2)
                && !integerq!(p_)
        },
        rhs: {
            let angle1 = &a__ + &b__ * x_;
            let angle2 = &c__ + &d__ * x_;
            let recursive =
                rubi_rhs_int(&((&e__ * angle1.cos()).pow(&m_ + &p_) * (&f__ * angle1.sin()).pow(&n_ + &p_)), x_);
            let coefficient = (&g__ * angle2.sin()).pow(&p_)
                / ((&e__ * angle1.cos()).pow(&p_) * (&f__ * angle1.sin()).pow(&p_));

            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_4819(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, x_);
    rules.push(rubi_rule!(
        order: 4819,
        source: "Int[(e_.*cos[a_.+b_.*x_])^m_.*sin[c_.+d_.*x_],x_Symbol] :=
          -(m+2)*(e*Cos[a+b*x])^(m+1)*Cos[(m+1)*(a+b*x)]/(d*e*(m+1)) /;
        FreeQ[{a,b,c,d,e,m},x] && EqQ[b*c-a*d,0] && EqQ[d/b,Abs[m+2]]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: (e__ * i_cos(a__ + b__ * x_)).pow(m_) * i_sin(c__ + d__ * x_),
        with: [e__, a__, b__, m_, c__, d__, x_],
        optional: [e__, a__, b__, m_, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_], x_)
                && eqq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(&d__ / &b__, Symbol::ABS.call((&m_ + 2,)))
        },
        rhs: {
            let angle = &a__ + &b__ * x_;

            rubi_simp(&(-(&m_ + 2) * (&e__ * angle.cos()).pow(&m_ + 1) * ((&m_ + 1) * &angle).cos()
                    / (&d__ * &e__ * (&m_ + 1))), x_)
        },
    ));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn downvalues_4770_through_4792_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .filter(|order| (4770..=4792).contains(order))
            .collect::<Vec<_>>();
        assert_eq!(orders, (4770..=4792).collect::<Vec<_>>());
    }

    #[test]
    fn downvalues_4793_through_4819_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .filter(|order| (4793..=4819).contains(order))
            .collect::<Vec<_>>();
        assert_eq!(orders, (4793..=4819).collect::<Vec<_>>());
    }
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
    let g__ = symbols.g__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (e__ * i_cos(a__ + b__ * x_)).pow(m_)
        * (f__ * i_sin(a__ + b__ * x_)).pow(n_)
        * (g__ * i_sin(c__ + d__ * x_)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let g__ = symbols.g__;
    let m_ = symbols.m_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (e__ * i_cos(a__ + b__ * x_)).pow(m_) * (g__ * i_sin(c__ + d__ * x_)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_2(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let g__ = symbols.g__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (e__ * i_sin(a__ + b__ * x_)).pow(m_)
        * (f__ * i_cos(a__ + b__ * x_)).pow(n_)
        * (g__ * i_sin(c__ + d__ * x_)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_3(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let g__ = symbols.g__;
    let m_ = symbols.m_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (e__ * i_sin(a__ + b__ * x_)).pow(m_) * (g__ * i_sin(c__ + d__ * x_)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_4(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let g__ = symbols.g__;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    i_cos(a__ + b__ * x_) * (g__ * i_sin(c__ + d__ * x_)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_5(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let g__ = symbols.g__;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    i_sin(a__ + b__ * x_) * (g__ * i_sin(c__ + d__ * x_)).pow(p_)
}
