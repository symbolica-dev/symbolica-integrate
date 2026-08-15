use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_3185(rules);
    push_rules_rule_3186(rules);
    push_rules_rule_3187(rules);
    push_rules_rule_3188(rules);
    push_rules_rule_3189(rules);
    push_rules_rule_3190(rules);
    push_rules_rule_3191(rules);
    push_rules_rule_3192(rules);
    push_rules_rule_3193(rules);
    push_rules_rule_3194(rules);
    push_rules_rule_3195(rules);
    push_rules_rule_3196(rules);
    push_rules_rule_3197(rules);
    push_rules_rule_3198(rules);
    push_rules_rule_3199(rules);
    push_rules_rule_3200(rules);
    push_rules_rule_3201(rules);
    push_rules_rule_3202(rules);
    push_rules_rule_3203(rules);
    push_rules_rule_3204(rules);
    push_rules_rule_3205(rules);
    push_rules_rule_3206(rules);
    push_rules_rule_3207(rules);
    push_rules_rule_3208(rules);
    push_rules_rule_3209(rules);
    push_rules_rule_3210(rules);
    push_rules_rule_3211(rules);
    push_rules_rule_3212(rules);
}

fn push_rules_rule_3185(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, e__, f__, g__, p_, x_);
    rules.push(rubi_rule!(
        order: 3185,
        source: "Int[(g_.*tan[e_.+f_.*x_])^p_./(a_+b_.*sin[e_.+f_.*x_]),x_Symbol] :=
          1/a \\[Star] Int[Sec[e+f*x]^2*(g*Tan[e+f*x])^p,x] - 1/(b*g) \\[Star] Int[Sec[e+f*x]*(g*Tan[e+f*x])^(p+1),x] /;
        FreeQ[{a,b,e,f,g,p},x] && EqQ[a^2-b^2,0] && NeQ[p,-1]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [g__, e__, f__, p_, a__, b__, x_],
        optional: [g__, p_, b__, e__, f__],
        when: {
            freeq!([a__, b__, e__, f__, g__, p_], x_)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && neq!(p_, -1)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_tan = &g__ * angle.tan();
            let recursive1 = rubi_rhs_int(&(angle.sec().pow(2) * scaled_tan.pow(&p_)), x_);
            let recursive2 = rubi_rhs_int(&(angle.sec() * scaled_tan.pow(&p_ + 1)), x_);

            rubi_star(Atom::num(1) / &a__, recursive1)
                    - rubi_star(Atom::num(1) / (&b__ * &g__), recursive2)
        },
    ));
}

fn push_rules_rule_3186(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, e__, f__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 3186,
        source: "Int[tan[e_.+f_.*x_]^p_.*(a_+b_.*sin[e_.+f_.*x_])^m_.,x_Symbol] :=
          1/f \\[Star] Subst[Int[x^p*(a+x)^(m-(p+1)/2)/(a-x)^((p+1)/2),x],x,b*Sin[e+f*x]] /;
        FreeQ[{a,b,e,f,m},x] && EqQ[a^2-b^2,0] && IntegerQ[(p+1)/2]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [e__, f__, p_, a__, b__, m_, x_],
        optional: [p_, b__, e__, f__, m_],
        when: {
            freeq!([a__, b__, e__, f__, m_], x_)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && integerq!((&p_ + 1) / 2)
        },
        rhs: {
            let subst_guard = fresh_substitution_symbol().unwrap();
            let subst = subst_guard.symbol();
            let z = Atom::var(subst);
            let transformed = z.pow(&p_) * (&a__ + &z).pow(&m_ - (&p_ + 1) / 2)
                / (&a__ - &z).pow((&p_ + 1) / 2);
            let primitive = rubi_rhs_int(&transformed, subst);
            let replacement = &b__ * (&e__ + &f__ * x_).sin();
            let substituted = rubi_subst(&primitive, subst, replacement);

            rubi_star(Atom::num(1) / &f__, substituted)
        },
    ));
}

fn push_rules_rule_3187(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, e__, f__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 3187,
        source: "Int[tan[e_.+f_.*x_]^p_*(a_+b_.*sin[e_.+f_.*x_])^m_.,x_Symbol] :=
          a^p \\[Star] Int[Sin[e+f*x]^p/(a-b*Sin[e+f*x])^m,x] /;
        FreeQ[{a,b,e,f},x] && EqQ[a^2-b^2,0] && IntegersQ[m,p] && EqQ[p,2*m]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [e__, f__, p_, a__, b__, m_, x_],
        optional: [b__, e__, f__, m_],
        when: {
            freeq!([a__, b__, e__, f__], x_)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && integersq!([m_, p_])
                && eqq!(p_, Atom::num(2) * &m_)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let recursive_integrand = sin.pow(&p_) / (&a__ - &b__ * sin).pow(&m_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(a__.pow(&p_), recursive)
        },
    ));
}

fn push_rules_rule_3188(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, e__, f__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 3188,
        source: "Int[tan[e_.+f_.*x_]^p_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
          a^p \\[Star] Int[ExpandIntegrand[Sin[e+f*x]^p*(a+b*Sin[e+f*x])^(m-p/2)/(a-b*Sin[e+f*x])^(p/2),x],x] /;
        FreeQ[{a,b,e,f},x] && EqQ[a^2-b^2,0] && IntegersQ[m,p/2] && (LtQ[p,0] || GtQ[m-p/2,0])",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [e__, f__, p_, a__, b__, m_, x_],
        optional: [b__, e__, f__],
        when: {
            freeq!([a__, b__, e__, f__], x_)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && integersq!([m_, &p_ / 2])
                && (ltq!(p_, 0) || gtq!(&m_ - &p_ / 2, 0))
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let payload = sin.pow(&p_) * (&a__ + &b__ * &sin).pow(&m_ - &p_ / 2)
                / (&a__ - &b__ * sin).pow(&p_ / 2);
            let expanded = rubi_expand_integrand(&payload, x_);
            let recursive = rubi_rhs_int(&expanded, x_);

            rubi_star(a__.pow(&p_), recursive)
        },
    ));
}

fn push_rules_rule_3189(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, e__, f__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 3189,
        source: "Int[(g_.*tan[e_.+f_.*x_])^p_.*(a_+b_.*sin[e_.+f_.*x_])^m_.,x_Symbol] :=
          Int[ExpandIntegrand[(g*Tan[e+f*x])^p,(a+b*Sin[e+f*x])^m,x],x] /;
        FreeQ[{a,b,e,f,g,p},x] && EqQ[a^2-b^2,0] && IGtQ[m,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [g__, e__, f__, p_, a__, b__, m_, x_],
        optional: [g__, p_, b__, e__, f__, m_],
        when: {
            freeq!([a__, b__, e__, f__, g__, p_], x_)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && igtq!(m_, 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let payload = (&g__ * angle.tan()).pow(&p_)
                * (&a__ + &b__ * angle.sin()).pow(&m_);
            let expanded = rubi_expand_integrand(&payload, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_3190(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, e__, f__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 3190,
        source: "Int[(g_.*tan[e_.+f_.*x_])^p_.*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
          a^(2*m) \\[Star] Int[ExpandIntegrand[(g*Tan[e+f*x])^p*Sec[e+f*x]^(-m),(a*Sec[e+f*x]-b*Tan[e+f*x])^(-m),x],x] /;
        FreeQ[{a,b,e,f,g,p},x] && EqQ[a^2-b^2,0] && ILtQ[m,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [g__, e__, f__, p_, a__, b__, m_, x_],
        optional: [g__, p_, b__, e__, f__],
        when: {
            freeq!([a__, b__, e__, f__, g__, p_], x_)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && iltq!(m_, 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let payload = (&g__ * angle.tan()).pow(&p_)
                * angle.sec().pow(-&m_)
                * (&a__ * angle.sec() - &b__ * angle.tan()).pow(-&m_);
            let expanded = rubi_expand_integrand(&payload, x_);
            let recursive = rubi_rhs_int(&expanded, x_);

            rubi_star(a__.pow(Atom::num(2) * &m_), recursive)
        },
    ));
}

fn push_rules_rule_3191(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, e__, f__, m_, x_);
    rules.push(rubi_rule!(
        order: 3191,
        source: "Int[tan[e_.+f_.*x_]^2*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
          b*(a+b*Sin[e+f*x])^m/(a*f*(2*m-1)*Cos[e+f*x]) -
          1/(a^2*(2*m-1)) \\[Star] Int[(a+b*Sin[e+f*x])^(m+1)*(a*m-b*(2*m-1)*Sin[e+f*x])/Cos[e+f*x]^2,x] /;
        FreeQ[{a,b,e,f},x] && EqQ[a^2-b^2,0] && Not[IntegerQ[m]] && LtQ[m,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [e__, f__, a__, b__, m_, x_],
        optional: [b__, e__, f__],
        when: {
            freeq!([a__, b__, e__, f__], x_)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && !integerq!(m_)
                && ltq!(m_, 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let cos = angle.cos();
            let affine_sin = &a__ + &b__ * &sin;
            let recursive_integrand = affine_sin.pow(&m_ + 1)
                * (&a__ * &m_ - &b__ * (Atom::num(2) * &m_ - 1) * &sin)
                / cos.pow(2);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(&b__ * affine_sin.pow(&m_) / (&a__ * &f__ * (Atom::num(2) * &m_ - 1) * &cos)), x_)
                    - rubi_star(Atom::num(1) / (a__.pow(2) * (Atom::num(2) * &m_ - 1)), recursive)
        },
    ));
}

fn push_rules_rule_3192(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, e__, f__, m_, x_);
    rules.push(rubi_rule!(
        order: 3192,
        source: "Int[tan[e_.+f_.*x_]^2*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
          -(a+b*Sin[e+f*x])^(m+1)/(b*f*m*Cos[e+f*x]) +
          1/(b*m) \\[Star] Int[(a+b*Sin[e+f*x])^m*(b*(m+1)+a*Sin[e+f*x])/Cos[e+f*x]^2,x] /;
        FreeQ[{a,b,e,f,m},x] && EqQ[a^2-b^2,0] && Not[IntegerQ[m]] && Not[LtQ[m,0]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [e__, f__, a__, b__, m_, x_],
        optional: [b__, e__, f__],
        when: {
            freeq!([a__, b__, e__, f__, m_], x_)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && !integerq!(m_)
                && !ltq!(m_, 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let cos = angle.cos();
            let affine_sin = &a__ + &b__ * &sin;
            let recursive_integrand =
                affine_sin.pow(&m_) * (&b__ * (&m_ + 1) + &a__ * &sin) / cos.pow(2);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(-affine_sin.pow(&m_ + 1) / (&b__ * &f__ * &m_ * &cos)), x_)
                    + rubi_star(Atom::num(1) / (&b__ * &m_), recursive)
        },
    ));
}

fn push_rules_rule_3193(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, e__, f__, m_, x_);
    rules.push(rubi_rule!(
        order: 3193,
        source: "Int[tan[e_.+f_.*x_]^4*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
          Int[(a+b*Sin[e+f*x])^m,x] - Int[(a+b*Sin[e+f*x])^m*(1-2*Sin[e+f*x]^2)/Cos[e+f*x]^4,x] /;
        FreeQ[{a,b,e,f,m},x] && EqQ[a^2-b^2,0] && IntegerQ[m-1/2]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: i_tan(e__ + f__ * x_).pow(4)
            * (a__ + b__ * i_sin(e__ + f__ * x_)).pow(m_),
        with: [e__, f__, a__, b__, m_, x_],
        optional: [b__, e__, f__],
        when: {
            freeq!([a__, b__, e__, f__, m_], x_)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && integerq!(&m_ - Atom::num(1) / Atom::num(2))
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let cos = angle.cos();
            let affine_sin = &a__ + &b__ * &sin;
            let recursive1 = rubi_rhs_int(&affine_sin.pow(&m_), x_);
            let recursive2 = rubi_rhs_int(
                &(affine_sin.pow(&m_) * (Atom::num(1) - Atom::num(2) * sin.pow(2)) / cos.pow(4)),
                x_,
            );

            recursive1 - recursive2
        },
    ));
}

fn push_rules_rule_3194(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, e__, f__, m_, x_);
    rules.push(rubi_rule!(
        order: 3194,
        source: "Int[(a_+b_.*sin[e_.+f_.*x_])^m_/tan[e_.+f_.*x_]^2,x_Symbol] :=
          -(a+b*Sin[e+f*x])^(m+1)/(a*f*Tan[e+f*x]) +
          1/b^2 \\[Star] Int[(a+b*Sin[e+f*x])^(m+1)*(b*m-a*(m+1)*Sin[e+f*x])/Sin[e+f*x],x] /;
        FreeQ[{a,b,e,f},x] && EqQ[a^2-b^2,0] && IntegerQ[m-1/2] && LtQ[m,-1]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, e__, f__, m_, x_],
        optional: [b__, e__, f__],
        when: {
            freeq!([a__, b__, e__, f__], x_)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && integerq!(&m_ - Atom::num(1) / Atom::num(2))
                && ltq!(m_, -1)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let tan = angle.tan();
            let affine_sin = &a__ + &b__ * &sin;
            let recursive_integrand = affine_sin.pow(&m_ + 1)
                * (&b__ * &m_ - &a__ * (&m_ + 1) * &sin)
                / &sin;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(-affine_sin.pow(&m_ + 1) / (&a__ * &f__ * tan)), x_)
                    + rubi_star(Atom::num(1) / b__.pow(2), recursive)
        },
    ));
}

fn push_rules_rule_3195(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, e__, f__, m_, x_);
    rules.push(rubi_rule!(
        order: 3195,
        source: "Int[(a_+b_.*sin[e_.+f_.*x_])^m_./tan[e_.+f_.*x_]^2,x_Symbol] :=
          -(a+b*Sin[e+f*x])^m/(f*Tan[e+f*x]) +
          1/a \\[Star] Int[(a+b*Sin[e+f*x])^m*(b*m-a*(m+1)*Sin[e+f*x])/Sin[e+f*x],x] /;
        FreeQ[{a,b,e,f,m},x] && EqQ[a^2-b^2,0] && IntegerQ[m-1/2] && Not[LtQ[m,-1]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, e__, f__, m_, x_],
        optional: [b__, e__, f__, m_],
        when: {
            freeq!([a__, b__, e__, f__, m_], x_)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && integerq!(&m_ - Atom::num(1) / Atom::num(2))
                && !ltq!(m_, -1)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let tan = angle.tan();
            let affine_sin = &a__ + &b__ * &sin;
            let recursive_integrand = affine_sin.pow(&m_)
                * (&b__ * &m_ - &a__ * (&m_ + 1) * &sin)
                / &sin;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(-affine_sin.pow(&m_) / (&f__ * tan)), x_)
                    + rubi_star(Atom::num(1) / &a__, recursive)
        },
    ));
}

fn push_rules_rule_3196(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, e__, f__, m_, x_);
    rules.push(rubi_rule!(
        order: 3196,
        source: "Int[(a_+b_.*sin[e_.+f_.*x_])^m_/tan[e_.+f_.*x_]^4,x_Symbol] :=
          -2/(a*b) \\[Star] Int[(a+b*Sin[e+f*x])^(m+2)/Sin[e+f*x]^3,x] +
          1/a^2 \\[Star] Int[(a+b*Sin[e+f*x])^(m+2)*(1+Sin[e+f*x]^2)/Sin[e+f*x]^4,x] /;
        FreeQ[{a,b,e,f},x] && EqQ[a^2-b^2,0] && IntegerQ[m-1/2] && LtQ[m,-1]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, e__, f__, m_, x_],
        optional: [b__, e__, f__],
        when: {
            freeq!([a__, b__, e__, f__], x_)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && integerq!(&m_ - Atom::num(1) / Atom::num(2))
                && ltq!(m_, -1)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let affine_sin = &a__ + &b__ * &sin;
            let recursive1 = rubi_rhs_int(&(affine_sin.pow(&m_ + 2) / sin.pow(3)), x_);
            let recursive2 = rubi_rhs_int(
                &(affine_sin.pow(&m_ + 2) * (Atom::num(1) + sin.pow(2)) / sin.pow(4)),
                x_,
            );

            rubi_star(-Atom::num(2) / (&a__ * &b__), recursive1)
                    + rubi_star(Atom::num(1) / a__.pow(2), recursive2)
        },
    ));
}

fn push_rules_rule_3197(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, e__, f__, m_, x_);
    rules.push(rubi_rule!(
        order: 3197,
        source: "Int[(a_+b_.*sin[e_.+f_.*x_])^m_/tan[e_.+f_.*x_]^4,x_Symbol] :=
          Int[(a+b*Sin[e+f*x])^m,x] + Int[(a+b*Sin[e+f*x])^m*(1-2*Sin[e+f*x]^2)/Sin[e+f*x]^4,x] /;
        FreeQ[{a,b,e,f,m},x] && EqQ[a^2-b^2,0] && IntegerQ[m-1/2] && Not[LtQ[m,-1]]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, e__, f__, m_, x_],
        optional: [b__, e__, f__],
        when: {
            freeq!([a__, b__, e__, f__, m_], x_)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && integerq!(&m_ - Atom::num(1) / Atom::num(2))
                && !ltq!(m_, -1)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let affine_sin = &a__ + &b__ * &sin;
            let recursive1 = rubi_rhs_int(&affine_sin.pow(&m_), x_);
            let recursive2 = rubi_rhs_int(
                &(affine_sin.pow(&m_) * (Atom::num(1) - Atom::num(2) * sin.pow(2)) / sin.pow(4)),
                x_,
            );

            recursive1 + recursive2
        },
    ));
}

fn push_rules_rule_3198(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, e__, f__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 3198,
        source: "Int[tan[e_.+f_.*x_]^p_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
          Sqrt[a+b*Sin[e+f*x]]*Sqrt[a-b*Sin[e+f*x]]/(b*f*Cos[e+f*x]) \\[Star]
            Subst[Int[x^p*(a+x)^(m-(p+1)/2)/(a-x)^((p+1)/2),x],x,b*Sin[e+f*x]] /;
        FreeQ[{a,b,e,f,m},x] && EqQ[a^2-b^2,0] && Not[IntegerQ[m]] && IntegerQ[p/2]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [e__, f__, p_, a__, b__, m_, x_],
        optional: [b__, e__, f__],
        when: {
            freeq!([a__, b__, e__, f__, m_], x_)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && !integerq!(m_)
                && integerq!(&p_ / 2)
        },
        rhs: {
            let subst_guard = fresh_substitution_symbol().unwrap();
            let subst = subst_guard.symbol();
            let z = Atom::var(subst);
            let transformed = z.pow(&p_) * (&a__ + &z).pow(&m_ - (&p_ + 1) / 2)
                / (&a__ - &z).pow((&p_ + 1) / 2);
            let primitive = rubi_rhs_int(&transformed, subst);
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let replacement = &b__ * &sin;
            let substituted = rubi_subst(&primitive, subst, replacement);

            rubi_star((&a__ + &b__ * &sin).sqrt()
                    * (&a__ - &b__ * &sin).sqrt()
                    / (&b__ * &f__ * angle.cos()), substituted)
        },
    ));
}

fn push_rules_rule_3199(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, e__, f__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 3199,
        source: "Int[(g_.*tan[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
          (g*Tan[e+f*x])^(p+1)*(a-b*Sin[e+f*x])^((p+1)/2)*(a+b*Sin[e+f*x])^((p+1)/2)/(f*g*(b*Sin[e+f*x])^(p+1)) \\[Star]
            Subst[Int[x^p*(a+x)^(m-(p+1)/2)/(a-x)^((p+1)/2),x],x,b*Sin[e+f*x]] /;
        FreeQ[{a,b,e,f,g,m,p},x] && EqQ[a^2-b^2,0] && Not[IntegerQ[m]] && Not[IntegerQ[p]]",
        desc: "Piecewise constant extraction and integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [g__, e__, f__, p_, a__, b__, m_, x_],
        optional: [g__, b__, e__, f__],
        when: {
            freeq!([a__, b__, e__, f__, g__, m_, p_], x_)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && !integerq!(m_)
                && !integerq!(p_)
        },
        rhs: {
            let subst_guard = fresh_substitution_symbol().unwrap();
            let subst = subst_guard.symbol();
            let z = Atom::var(subst);
            let transformed = z.pow(&p_) * (&a__ + &z).pow(&m_ - (&p_ + 1) / 2)
                / (&a__ - &z).pow((&p_ + 1) / 2);
            let primitive = rubi_rhs_int(&transformed, subst);
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let scaled_tan = &g__ * angle.tan();
            let replacement = &b__ * &sin;
            let substituted = rubi_subst(&primitive, subst, replacement);

            rubi_star(scaled_tan.pow(&p_ + 1)
                    * (&a__ - &b__ * &sin).pow((&p_ + 1) / 2)
                    * (&a__ + &b__ * &sin).pow((&p_ + 1) / 2)
                    / (&f__ * &g__ * (&b__ * sin).pow(&p_ + 1)), substituted)
        },
    ));
}

fn push_rules_rule_3200(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, e__, f__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 3200,
        source: "Int[tan[e_.+f_.*x_]^p_.*(a_+b_.*sin[e_.+f_.*x_])^m_.,x_Symbol] :=
          1/f \\[Star] Subst[Int[(x^p*(a+x)^m)/(b^2-x^2)^((p+1)/2),x],x,b*Sin[e+f*x]] /;
        FreeQ[{a,b,e,f,m},x] && NeQ[a^2-b^2,0] && IntegerQ[(p+1)/2]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [e__, f__, p_, a__, b__, m_, x_],
        optional: [p_, b__, e__, f__, m_],
        when: {
            freeq!([a__, b__, e__, f__, m_], x_)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && integerq!((&p_ + 1) / 2)
        },
        rhs: {
            let subst_guard = fresh_substitution_symbol().unwrap();
            let subst = subst_guard.symbol();
            let z = Atom::var(subst);
            let transformed =
                z.pow(&p_) * (&a__ + &z).pow(&m_) / (b__.pow(2) - z.pow(2)).pow((&p_ + 1) / 2);
            let primitive = rubi_rhs_int(&transformed, subst);
            let replacement = &b__ * (&e__ + &f__ * x_).sin();
            let substituted = rubi_subst(&primitive, subst, replacement);

            rubi_star(Atom::num(1) / &f__, substituted)
        },
    ));
}

fn push_rules_rule_3201(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, e__, f__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 3201,
        source: "Int[(g_.*tan[e_.+f_.*x_])^p_.*(a_+b_.*sin[e_.+f_.*x_])^m_.,x_Symbol] :=
          Int[ExpandIntegrand[(g*Tan[e+f*x])^p,(a+b*Sin[e+f*x])^m,x],x] /;
        FreeQ[{a,b,e,f,g,p},x] && NeQ[a^2-b^2,0] && IGtQ[m,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [g__, e__, f__, p_, a__, b__, m_, x_],
        optional: [g__, p_, b__, e__, f__, m_],
        when: {
            freeq!([a__, b__, e__, f__, g__, p_], x_)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && igtq!(m_, 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let payload = (&g__ * angle.tan()).pow(&p_)
                * (&a__ + &b__ * angle.sin()).pow(&m_);
            let expanded = rubi_expand_integrand(&payload, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_3202(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, e__, f__, m_, x_);
    rules.push(rubi_rule!(
        order: 3202,
        source: "Int[(a_+b_.*sin[e_.+f_.*x_])^m_/tan[e_.+f_.*x_]^2,x_Symbol] :=
          Int[(a+b*Sin[e+f*x])^m*(1-Sin[e+f*x]^2)/Sin[e+f*x]^2,x] /;
        FreeQ[{a,b,e,f,m},x] && NeQ[a^2-b^2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, e__, f__, m_, x_],
        optional: [b__, e__, f__],
        when: {
            freeq!([a__, b__, e__, f__, m_], x_)
                && neq!(a__.pow(2) - b__.pow(2), 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let affine_sin = &a__ + &b__ * &sin;
            let recursive_integrand =
                affine_sin.pow(&m_) * (Atom::num(1) - sin.pow(2)) / sin.pow(2);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_3203(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, e__, f__, m_, x_);
    rules.push(rubi_rule!(
        order: 3203,
        source: "Int[(a_+b_.*sin[e_.+f_.*x_])^m_/tan[e_.+f_.*x_]^4,x_Symbol] :=
          -Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+1)/(3*a*f*Sin[e+f*x]^3) -
          (3*a^2+b^2*(m-2))*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+1)/(3*a^2*b*f*(m+1)*Sin[e+f*x]^2) -
          1/(3*a^2*b*(m+1)) \\[Star] Int[(a+b*Sin[e+f*x])^(m+1)/Sin[e+f*x]^3*
            Simp[6*a^2-b^2*(m-1)*(m-2)+a*b*(m+1)*Sin[e+f*x]-(3*a^2-b^2*m*(m-2))*Sin[e+f*x]^2,x],x] /;
        FreeQ[{a,b,e,f},x] && NeQ[a^2-b^2,0] && LtQ[m,-1] && IntegerQ[2*m]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, e__, f__, m_, x_],
        optional: [b__, e__, f__],
        when: {
            freeq!([a__, b__, e__, f__], x_)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && ltq!(m_, -1)
                && integerq!(Atom::num(2) * &m_)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let cos = angle.cos();
            let affine_sin = &a__ + &b__ * &sin;
            let simp_payload = Atom::num(6) * a__.pow(2)
                - b__.pow(2) * (&m_ - 1) * (&m_ - 2)
                + &a__ * &b__ * (&m_ + 1) * &sin
                - (Atom::num(3) * a__.pow(2) - b__.pow(2) * &m_ * (&m_ - 2)) * sin.pow(2);
            let recursive_integrand =
                affine_sin.pow(&m_ + 1) / sin.pow(3) * rubi_simp(&simp_payload, x_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(-&cos * affine_sin.pow(&m_ + 1) / (Atom::num(3) * &a__ * &f__ * sin.pow(3))), x_)
                    - rubi_simp(&((Atom::num(3) * a__.pow(2) + b__.pow(2) * (&m_ - 2))
                        * &cos
                        * affine_sin.pow(&m_ + 1)
                        / (Atom::num(3)
                            * a__.pow(2)
                            * &b__
                            * &f__
                            * (&m_ + 1)
                            * sin.pow(2))), x_)
                    - rubi_star(Atom::num(1)
                            / (Atom::num(3) * a__.pow(2) * &b__ * (&m_ + 1)), recursive)
        },
    ));
}

fn push_rules_rule_3204(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, e__, f__, m_, x_);
    rules.push(rubi_rule!(
        order: 3204,
        source: "Int[(a_+b_.*sin[e_.+f_.*x_])^m_/tan[e_.+f_.*x_]^4,x_Symbol] :=
          -Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+1)/(3*a*f*Sin[e+f*x]^3) -
          b*(m-2)*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+1)/(6*a^2*f*Sin[e+f*x]^2) -
          1/(6*a^2) \\[Star] Int[(a+b*Sin[e+f*x])^m/Sin[e+f*x]^2*
            Simp[8*a^2-b^2*(m-1)*(m-2)+a*b*m*Sin[e+f*x]-(6*a^2-b^2*m*(m-2))*Sin[e+f*x]^2,x],x] /;
        FreeQ[{a,b,e,f,m},x] && NeQ[a^2-b^2,0] && Not[LtQ[m,-1]] && IntegerQ[2*m]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, e__, f__, m_, x_],
        optional: [b__, e__, f__],
        when: {
            freeq!([a__, b__, e__, f__, m_], x_)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && !ltq!(m_, -1)
                && integerq!(Atom::num(2) * &m_)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let cos = angle.cos();
            let affine_sin = &a__ + &b__ * &sin;
            let simp_payload = Atom::num(8) * a__.pow(2)
                - b__.pow(2) * (&m_ - 1) * (&m_ - 2)
                + &a__ * &b__ * &m_ * &sin
                - (Atom::num(6) * a__.pow(2) - b__.pow(2) * &m_ * (&m_ - 2)) * sin.pow(2);
            let recursive_integrand =
                affine_sin.pow(&m_) / sin.pow(2) * rubi_simp(&simp_payload, x_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(-&cos * affine_sin.pow(&m_ + 1) / (Atom::num(3) * &a__ * &f__ * sin.pow(3))), x_)
                    - rubi_simp(&(&b__ * (&m_ - 2) * &cos * affine_sin.pow(&m_ + 1)
                        / (Atom::num(6) * a__.pow(2) * &f__ * sin.pow(2))), x_)
                    - rubi_star(Atom::num(1) / (Atom::num(6) * a__.pow(2)), recursive)
        },
    ));
}

fn push_rules_rule_3205(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, e__, f__, m_, x_);
    rules.push(rubi_rule!(
        order: 3205,
        source: "Int[(a_+b_.*sin[e_.+f_.*x_])^m_/tan[e_.+f_.*x_]^6,x_Symbol] :=
          -Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+1)/(5*a*f*Sin[e+f*x]^5) -
          b*(m-4)*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+1)/(20*a^2*f*Sin[e+f*x]^4) +
          a*Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+1)/(b^2*f*m*(m-1)*Sin[e+f*x]^3) +
          Cos[e+f*x]*(a+b*Sin[e+f*x])^(m+1)/(b*f*m*Sin[e+f*x]^2) +
          1/(20*a^2*b^2*m*(m-1)) \\[Star] Int[(a+b*Sin[e+f*x])^m/Sin[e+f*x]^4*
            Simp[60*a^4-44*a^2*b^2*(m-1)*m+b^4*m*(m-1)*(m-3)*(m-4)+a*b*m*(20*a^2-b^2*m*(m-1))*Sin[e+f*x]-
              (40*a^4+b^4*m*(m-1)*(m-2)*(m-4)-20*a^2*b^2*(m-1)*(2*m+1))*Sin[e+f*x]^2,x],x] /;
        FreeQ[{a,b,e,f,m},x] && NeQ[a^2-b^2,0] && NeQ[m,1] && IntegerQ[2*m]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern: (a__ + b__ * i_sin(e__ + f__ * x_)).pow(m_)
            / i_tan(e__ + f__ * x_).pow(6),
        with: [a__, b__, e__, f__, m_, x_],
        optional: [b__, e__, f__],
        when: {
            freeq!([a__, b__, e__, f__, m_], x_)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && neq!(m_, 1)
                && integerq!(Atom::num(2) * &m_)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let cos = angle.cos();
            let affine_sin = &a__ + &b__ * &sin;
            let simp_payload = Atom::num(60) * a__.pow(4)
                - Atom::num(44) * a__.pow(2) * b__.pow(2) * (&m_ - 1) * &m_
                + b__.pow(4) * &m_ * (&m_ - 1) * (&m_ - 3) * (&m_ - 4)
                + &a__ * &b__ * &m_ * (Atom::num(20) * a__.pow(2) - b__.pow(2) * &m_ * (&m_ - 1)) * &sin
                - (Atom::num(40) * a__.pow(4)
                    + b__.pow(4) * &m_ * (&m_ - 1) * (&m_ - 2) * (&m_ - 4)
                    - Atom::num(20) * a__.pow(2) * b__.pow(2) * (&m_ - 1) * (Atom::num(2) * &m_ + 1))
                    * sin.pow(2);
            let recursive_integrand =
                affine_sin.pow(&m_) / sin.pow(4) * rubi_simp(&simp_payload, x_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(-&cos * affine_sin.pow(&m_ + 1) / (Atom::num(5) * &a__ * &f__ * sin.pow(5))), x_)
                    - rubi_simp(&(&b__ * (&m_ - 4) * &cos * affine_sin.pow(&m_ + 1)
                        / (Atom::num(20) * a__.pow(2) * &f__ * sin.pow(4))), x_)
                    + rubi_simp(&(&a__ * &cos * affine_sin.pow(&m_ + 1)
                        / (b__.pow(2) * &f__ * &m_ * (&m_ - 1) * sin.pow(3))), x_)
                    + rubi_simp(&(&cos * affine_sin.pow(&m_ + 1) / (&b__ * &f__ * &m_ * sin.pow(2))), x_)
                    + rubi_star(Atom::num(1)
                            / (Atom::num(20)
                                * a__.pow(2)
                                * b__.pow(2)
                                * &m_
                                * (&m_ - 1)), recursive)
        },
    ));
}

fn push_rules_rule_3206(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, e__, f__, g__, p_, x_);
    rules.push(rubi_rule!(
        order: 3206,
        source: "Int[(g_.*tan[e_.+f_.*x_])^p_/(a_+b_.*sin[e_.+f_.*x_]),x_Symbol] :=
          a/(a^2-b^2) \\[Star] Int[(g*Tan[e+f*x])^p/Sin[e+f*x]^2,x] -
          b*g/(a^2-b^2) \\[Star] Int[(g*Tan[e+f*x])^(p-1)/Cos[e+f*x],x] -
          a^2*g^2/(a^2-b^2) \\[Star] Int[(g*Tan[e+f*x])^(p-2)/(a+b*Sin[e+f*x]),x] /;
        FreeQ[{a,b,e,f,g},x] && NeQ[a^2-b^2,0] && IntegersQ[2*p] && GtQ[p,1]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [g__, e__, f__, p_, a__, b__, x_],
        optional: [g__, b__, e__, f__],
        when: {
            freeq!([a__, b__, e__, f__, g__], x_)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && integersq!([Atom::num(2) * &p_])
                && gtq!(p_, 1)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let cos = angle.cos();
            let scaled_tan = &g__ * angle.tan();
            let affine_sin = &a__ + &b__ * &sin;
            let discriminant = a__.pow(2) - b__.pow(2);
            let recursive1 = rubi_rhs_int(&(scaled_tan.pow(&p_) / sin.pow(2)), x_);
            let recursive2 = rubi_rhs_int(&(scaled_tan.pow(&p_ - 1) / &cos), x_);
            let recursive3 = rubi_rhs_int(&(scaled_tan.pow(&p_ - 2) / affine_sin), x_);

            rubi_star(&a__ / &discriminant, recursive1)
                    - rubi_star(&b__ * &g__ / &discriminant, recursive2)
                    - rubi_star(a__.pow(2) * g__.pow(2) / discriminant, recursive3)
        },
    ));
}

fn push_rules_rule_3207(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, e__, f__, g__, p_, x_);
    rules.push(rubi_rule!(
        order: 3207,
        source: "Int[(g_.*tan[e_.+f_.*x_])^p_/(a_+b_.*sin[e_.+f_.*x_]),x_Symbol] :=
          1/a \\[Star] Int[(g*Tan[e+f*x])^p/Cos[e+f*x]^2,x] -
          b/(a^2*g) \\[Star] Int[(g*Tan[e+f*x])^(p+1)/Cos[e+f*x],x] -
          (a^2-b^2)/(a^2*g^2) \\[Star] Int[(g*Tan[e+f*x])^(p+2)/(a+b*Sin[e+f*x]),x] /;
        FreeQ[{a,b,e,f,g},x] && NeQ[a^2-b^2,0] && IntegersQ[2*p] && LtQ[p,-1]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [g__, e__, f__, p_, a__, b__, x_],
        optional: [g__, b__, e__, f__],
        when: {
            freeq!([a__, b__, e__, f__, g__], x_)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && integersq!([Atom::num(2) * &p_])
                && ltq!(p_, -1)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let cos = angle.cos();
            let scaled_tan = &g__ * angle.tan();
            let affine_sin = &a__ + &b__ * angle.sin();
            let discriminant = a__.pow(2) - b__.pow(2);
            let recursive1 = rubi_rhs_int(&(scaled_tan.pow(&p_) / cos.pow(2)), x_);
            let recursive2 = rubi_rhs_int(&(scaled_tan.pow(&p_ + 1) / &cos), x_);
            let recursive3 = rubi_rhs_int(&(scaled_tan.pow(&p_ + 2) / affine_sin), x_);

            rubi_star(Atom::num(1) / &a__, recursive1)
                    - rubi_star(&b__ / (a__.pow(2) * &g__), recursive2)
                    - rubi_star(discriminant / (a__.pow(2) * g__.pow(2)), recursive3)
        },
    ));
}

fn push_rules_rule_3208(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, e__, f__, g__, x_);
    rules.push(rubi_rule!(
        order: 3208,
        source: "Int[Sqrt[g_.*tan[e_.+f_.*x_]]/(a_+b_.*sin[e_.+f_.*x_]),x_Symbol] :=
          Sqrt[Cos[e+f*x]]*Sqrt[g*Tan[e+f*x]]/Sqrt[Sin[e+f*x]] \\[Star] Int[Sqrt[Sin[e+f*x]]/(Sqrt[Cos[e+f*x]]*(a+b*Sin[e+f*x])),x] /;
        FreeQ[{a,b,e,f,g},x] && NeQ[a^2-b^2,0]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: (g__ * i_tan(e__ + f__ * x_)).sqrt()
            / (a__ + b__ * i_sin(e__ + f__ * x_)),
        with: [g__, e__, f__, a__, b__, x_],
        optional: [g__, b__, e__, f__],
        when: {
            freeq!([a__, b__, e__, f__, g__], x_)
                && neq!(a__.pow(2) - b__.pow(2), 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let cos = angle.cos();
            let recursive_integrand =
                sin.sqrt() / (cos.sqrt() * (&a__ + &b__ * &sin));
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(cos.sqrt() * (&g__ * angle.tan()).sqrt() / sin.sqrt(), recursive)
        },
    ));
}

fn push_rules_rule_3209(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, e__, f__, g__, x_);
    rules.push(rubi_rule!(
        order: 3209,
        source: "Int[1/(Sqrt[g_*tan[e_.+f_.*x_]]*(a_+b_.*sin[e_.+f_.*x_])),x_Symbol] :=
          Sqrt[Sin[e+f*x]]/(Sqrt[Cos[e+f*x]]*Sqrt[g*Tan[e+f*x]]) \\[Star] Int[Sqrt[Cos[e+f*x]]/(Sqrt[Sin[e+f*x]]*(a+b*Sin[e+f*x])),x] /;
        FreeQ[{a,b,e,f,g},x] && NeQ[a^2-b^2,0]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: Atom::num(1)
            / ((g__ * i_tan(e__ + f__ * x_)).sqrt()
                * (a__ + b__ * i_sin(e__ + f__ * x_))),
        with: [g__, e__, f__, a__, b__, x_],
        optional: [b__, e__, f__],
        when: {
            freeq!([a__, b__, e__, f__, g__], x_)
                && neq!(a__.pow(2) - b__.pow(2), 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let cos = angle.cos();
            let recursive_integrand =
                cos.sqrt() / (sin.sqrt() * (&a__ + &b__ * &sin));
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(sin.sqrt() / (cos.sqrt() * (&g__ * angle.tan()).sqrt()), recursive)
        },
    ));
}

fn push_rules_rule_3210(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, e__, f__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 3210,
        source: "Int[tan[e_.+f_.*x_]^p_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
          Int[ExpandIntegrand[Sin[e+f*x]^p*(a+b*Sin[e+f*x])^m/(1-Sin[e+f*x]^2)^(p/2),x],x] /;
        FreeQ[{a,b,e,f},x] && NeQ[a^2-b^2,0] && IntegersQ[m,p/2]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [e__, f__, p_, a__, b__, m_, x_],
        optional: [b__, e__, f__],
        when: {
            freeq!([a__, b__, e__, f__], x_)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && integersq!([m_, &p_ / 2])
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let payload = sin.pow(&p_)
                * (&a__ + &b__ * &sin).pow(&m_)
                / (Atom::num(1) - sin.pow(2)).pow(&p_ / 2);
            let expanded = rubi_expand_integrand(&payload, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_3211(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, e__, f__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 3211,
        source: "Int[(g_.*tan[e_.+f_.*x_])^p_.*(a_+b_.*sin[e_.+f_.*x_])^m_.,x_Symbol] :=
          Unintegrable[(g*Tan[e+f*x])^p*(a+b*Sin[e+f*x])^m,x] /;
        FreeQ[{a,b,e,f,g,m,p},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [g__, e__, f__, p_, a__, b__, m_, x_],
        optional: [g__, p_, b__, e__, f__, m_],
        when: {
            freeq!([a__, b__, e__, f__, g__, m_, p_], x_)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let integrand = (&g__ * angle.tan()).pow(&p_)
                * (&a__ + &b__ * angle.sin()).pow(&m_);

            rubi_unintegrable(integrand, x_)
        },
    ));
}

fn push_rules_rule_3212(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, e__, f__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 3212,
        source: "Int[(g_.*cot[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_.,x_Symbol] :=
          g^(2*IntPart[p])*(g*Cot[e+f*x])^FracPart[p]*(g*Tan[e+f*x])^FracPart[p] \\[Star] Int[(a+b*Sin[e+f*x])^m/(g*Tan[e+f*x])^p,x] /;
        FreeQ[{a,b,e,f,g,m,p},x] && Not[IntegerQ[p]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: (g__ * i_cot(e__ + f__ * x_)).pow(p_)
            * (a__ + b__ * i_sin(e__ + f__ * x_)).pow(m_),
        with: [g__, e__, f__, p_, a__, b__, m_, x_],
        optional: [g__, b__, e__, f__, m_],
        when: {
            freeq!([a__, b__, e__, f__, g__, m_, p_], x_)
                && !integerq!(p_)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_cot = &g__ * angle.cot();
            let scaled_tan = &g__ * angle.tan();
            let affine_sin = &a__ + &b__ * angle.sin();
            let recursive_integrand = affine_sin.pow(&m_) / scaled_tan.pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(g__.pow(Atom::num(2) * rubi_int_part(&p_))
                    * scaled_cot.pow(rubi_frac_part(&p_))
                    * scaled_tan.pow(rubi_frac_part(&p_)), recursive)
        },
    ));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn downvalues_3185_through_3192_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .filter(|order| (3185..=3192).contains(order))
            .collect::<Vec<_>>();

        assert_eq!(orders, (3185..=3192).collect::<Vec<_>>());
    }

    #[test]
    fn downvalues_3193_through_3212_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .filter(|order| (3193..=3212).contains(order))
            .collect::<Vec<_>>();

        assert_eq!(orders, (3193..=3212).collect::<Vec<_>>());
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
    let x_ = symbols.x_;
    (a__ + b__ * i_sin(e__ + f__ * x_)).pow(m_) / i_tan(e__ + f__ * x_).pow(2)
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let x_ = symbols.x_;
    (a__ + b__ * i_sin(e__ + f__ * x_)).pow(m_) / i_tan(e__ + f__ * x_).pow(4)
}

#[inline(never)]
fn rubi_shared_pattern_2(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let g__ = symbols.g__;
    let m_ = symbols.m_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (g__ * i_tan(e__ + f__ * x_)).pow(p_) * (a__ + b__ * i_sin(e__ + f__ * x_)).pow(m_)
}

#[inline(never)]
fn rubi_shared_pattern_3(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let g__ = symbols.g__;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (g__ * i_tan(e__ + f__ * x_)).pow(p_) / (a__ + b__ * i_sin(e__ + f__ * x_))
}

#[inline(never)]
fn rubi_shared_pattern_4(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let x_ = symbols.x_;
    i_tan(e__ + f__ * x_).pow(2) * (a__ + b__ * i_sin(e__ + f__ * x_)).pow(m_)
}

#[inline(never)]
fn rubi_shared_pattern_5(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    i_tan(e__ + f__ * x_).pow(p_) * (a__ + b__ * i_sin(e__ + f__ * x_)).pow(m_)
}
