use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_3146(rules);
    push_rules_rule_3147(rules);
    push_rules_rule_3148(rules);
    push_rules_rule_3149(rules);
    push_rules_rule_3150(rules);
    push_rules_rule_3151(rules);
    push_rules_rule_3152(rules);
    push_rules_rule_3153(rules);
    push_rules_rule_3154(rules);
    push_rules_rule_3155(rules);
    push_rules_rule_3156(rules);
    push_rules_rule_3157(rules);
    push_rules_rule_3158(rules);
    push_rules_rule_3159(rules);
    push_rules_rule_3160(rules);
    push_rules_rule_3161(rules);
    push_rules_rule_3162(rules);
    push_rules_rule_3163(rules);
    push_rules_rule_3164(rules);
    push_rules_rule_3165(rules);
    push_rules_rule_3166(rules);
    push_rules_rule_3167(rules);
    push_rules_rule_3168(rules);
    push_rules_rule_3169(rules);
    push_rules_rule_3170(rules);
    push_rules_rule_3171(rules);
    push_rules_rule_3172(rules);
    push_rules_rule_3173(rules);
    push_rules_rule_3174(rules);
    push_rules_rule_3175(rules);
    push_rules_rule_3176(rules);
    push_rules_rule_3177(rules);
    push_rules_rule_3178(rules);
    push_rules_rule_3179(rules);
    push_rules_rule_3180(rules);
    push_rules_rule_3181(rules);
    push_rules_rule_3182(rules);
    push_rules_rule_3183(rules);
    push_rules_rule_3184(rules);
}

fn push_rules_rule_3146(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, e__, f__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 3146,
        source: "Int[cos[e_.+f_.*x_]^p_.*(a_+b_.*sin[e_.+f_.*x_])^m_.,x_Symbol] :=
          1/(b^p*f) \\[Star] Subst[Int[(a+x)^(m+(p-1)/2)*(a-x)^((p-1)/2),x],x,b*Sin[e+f*x]] /;
        FreeQ[{a,b,e,f,m},x] && IntegerQ[(p-1)/2] && EqQ[a^2-b^2,0] && (GeQ[p,-1] || Not[IntegerQ[m+1/2]])",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [e__, f__, p_, a__, b__, m_, x_],
        optional: [p_, b__, e__, f__, m_],
        when: {
            freeq!([a__, b__, e__, f__, m_], x_)
                && integerq!((&p_ - 1) / 2)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && (geq!(p_, -1) || !integerq!(&m_ + Atom::num(1) / Atom::num(2)))
        },
        rhs: {
            let subst_guard = fresh_substitution_symbol().unwrap();
            let subst = subst_guard.symbol();
            let z = Atom::var(subst);
            let transformed =
                (&a__ + &z).pow(&m_ + (&p_ - 1) / 2) * (&a__ - &z).pow((&p_ - 1) / 2);
            let primitive = rubi_rhs_int(&transformed, subst);
            let replacement = &b__ * (&e__ + &f__ * x_).sin();
            let substituted = rubi_subst(&primitive, subst, replacement);

            rubi_star(Atom::num(1) / (b__.pow(&p_) * &f__), substituted)
        },
    ));
}

fn push_rules_rule_3147(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, e__, f__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 3147,
        source: "Int[cos[e_.+f_.*x_]^p_.*(a_+b_.*sin[e_.+f_.*x_])^m_.,x_Symbol] :=
          1/(b^p*f) \\[Star] Subst[Int[(a+x)^m*(b^2-x^2)^((p-1)/2),x],x,b*Sin[e+f*x]] /;
        FreeQ[{a,b,e,f,m},x] && IntegerQ[(p-1)/2] && NeQ[a^2-b^2,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [e__, f__, p_, a__, b__, m_, x_],
        optional: [p_, b__, e__, f__, m_],
        when: {
            freeq!([a__, b__, e__, f__, m_], x_)
                && integerq!((&p_ - 1) / 2)
                && neq!(a__.pow(2) - b__.pow(2), 0)
        },
        rhs: {
            let subst_guard = fresh_substitution_symbol().unwrap();
            let subst = subst_guard.symbol();
            let z = Atom::var(subst);
            let transformed = (&a__ + &z).pow(&m_) * (b__.pow(2) - z.pow(2)).pow((&p_ - 1) / 2);
            let primitive = rubi_rhs_int(&transformed, subst);
            let replacement = &b__ * (&e__ + &f__ * x_).sin();
            let substituted = rubi_subst(&primitive, subst, replacement);

            rubi_star(Atom::num(1) / (b__.pow(&p_) * &f__), substituted)
        },
    ));
}

fn push_rules_rule_3148(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, e__, f__, g__, p_, x_);
    rules.push(rubi_rule!(
        order: 3148,
        source: "Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_]),x_Symbol] :=
          -b*(g*Cos[e+f*x])^(p+1)/(f*g*(p+1)) + a \\[Star] Int[(g*Cos[e+f*x])^p,x] /;
        FreeQ[{a,b,e,f,g,p},x] && (IntegerQ[2*p] || NeQ[a^2-b^2,0])",
        desc: "Nondegenerate sine recurrence 1b with c\\[Rule]0,d\\[Rule]1,A\\[Rule]0,B\\[Rule]a,C\\[Rule]b,m\\[Rule]0,n\\[Rule]-1",
        refs: [],
        pattern: (g__ * i_cos(e__ + f__ * x_)).pow(p_) * (a__ + b__ * i_sin(e__ + f__ * x_)),
        with: [g__, e__, f__, p_, a__, b__, x_],
        optional: [g__, b__, e__, f__],
        when: {
            freeq!([a__, b__, e__, f__, g__, p_], x_)
                && (integerq!(Atom::num(2) * &p_) || neq!(a__.pow(2) - b__.pow(2), 0))
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_cos = &g__ * angle.cos();
            let recursive_integrand = scaled_cos.pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(
                    &(-&b__ * scaled_cos.pow(&p_ + 1) / (&f__ * &g__ * (&p_ + 1))),
                    x_,
                ) + rubi_star(a__, recursive)
        },
    ));
}

fn push_rules_rule_3149(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, e__, f__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 3149,
        source: "Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
          (a/g)^(2*m) \\[Star] Int[(g*Cos[e+f*x])^(2*m+p)/(a-b*Sin[e+f*x])^m,x] /;
        FreeQ[{a,b,e,f,g},x] && EqQ[a^2-b^2,0] && IntegerQ[m] && LtQ[p,-1] && GeQ[2*m+p,0]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [g__, e__, f__, p_, a__, b__, m_, x_],
        optional: [g__, b__, e__, f__],
        when: {
            freeq!([a__, b__, e__, f__, g__], x_)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && integerq!(m_)
                && ltq!(p_, -1)
                && geq!(Atom::num(2) * &m_ + &p_, 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_cos = &g__ * angle.cos();
            let recursive_integrand = scaled_cos.pow(Atom::num(2) * &m_ + &p_)
                / (&a__ - &b__ * angle.sin()).pow(&m_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star((&a__ / &g__).pow(Atom::num(2) * &m_), recursive)
        },
    ));
}

fn push_rules_rule_3150(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, e__, f__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 3150,
        source: "Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
          b*(g*Cos[e+f*x])^(p+1)*(a+b*Sin[e+f*x])^m/(a*f*g*m) /;
        FreeQ[{a,b,e,f,g,m,p},x] && EqQ[a^2-b^2,0] && EqQ[Simplify[m+p+1],0] && Not[ILtQ[p,0]]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [g__, e__, f__, p_, a__, b__, m_, x_],
        optional: [g__, b__, e__, f__],
        when: {
            freeq!([a__, b__, e__, f__, g__, m_, p_], x_)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && {
                    eqq!(rubi_simplify(&(&m_ + &p_ + 1)), 0) && !iltq!(p_, 0)
                }
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_cos = &g__ * angle.cos();
            let affine_sin = &a__ + &b__ * angle.sin();

            rubi_simp(
                &(&b__ * scaled_cos.pow(&p_ + 1) * affine_sin.pow(&m_)
                    / (&a__ * &f__ * &g__ * &m_)),
                x_,
            )
        },
    ));
}

fn push_rules_rule_3151(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, e__, f__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 3151,
        source: "Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
          b*(g*Cos[e+f*x])^(p+1)*(a+b*Sin[e+f*x])^m/(a*f*g*Simplify[2*m+p+1]) +
          Simplify[m+p+1]/(a*Simplify[2*m+p+1]) \\[Star] Int[(g*Cos[e+f*x])^p*(a+b*Sin[e+f*x])^(m+1),x] /;
        FreeQ[{a,b,e,f,g,m,p},x] && EqQ[a^2-b^2,0] && ILtQ[Simplify[m+p+1],0] && NeQ[2*m+p+1,0] && Not[IGtQ[m,0]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [g__, e__, f__, p_, a__, b__, m_, x_],
        optional: [g__, b__, e__, f__],
        when: {
            freeq!([a__, b__, e__, f__, g__, m_, p_], x_)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && {
                    iltq!(rubi_simplify(&(&m_ + &p_ + 1)), 0)
                        && neq!(Atom::num(2) * &m_ + &p_ + 1, 0)
                        && !igtq!(m_, 0)
                }
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_cos = &g__ * angle.cos();
            let affine_sin = &a__ + &b__ * angle.sin();
            let m_p_1 = rubi_simplify(&(&m_ + &p_ + 1));
            let two_m_p_1 = rubi_simplify(&(Atom::num(2) * &m_ + &p_ + 1));
            let recursive_integrand = scaled_cos.pow(&p_) * affine_sin.pow(&m_ + 1);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(
                    &(&b__ * scaled_cos.pow(&p_ + 1) * affine_sin.pow(&m_)
                        / (&a__ * &f__ * &g__ * &two_m_p_1)),
                    x_,
                ) + rubi_star(m_p_1 / (&a__ * two_m_p_1), recursive)
        },
    ));
}

fn push_rules_rule_3152(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, e__, f__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 3152,
        source: "Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
          b*(g*Cos[e+f*x])^(p+1)*(a+b*Sin[e+f*x])^(m-1)/(f*g*(m-1)) /;
        FreeQ[{a,b,e,f,g,m,p},x] && EqQ[a^2-b^2,0] && EqQ[2*m+p-1,0] && NeQ[m,1]",
        desc: "Symmetric cosine/sine recurrence 1c with m\\[Rule]-2m+1",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [g__, e__, f__, p_, a__, b__, m_, x_],
        optional: [g__, b__, e__, f__],
        when: {
            freeq!([a__, b__, e__, f__, g__, m_, p_], x_)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && eqq!(Atom::num(2) * &m_ + &p_ - 1, 0)
                && neq!(m_, 1)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_cos = &g__ * angle.cos();
            let affine_sin = &a__ + &b__ * angle.sin();

            rubi_simp(
                &(&b__ * scaled_cos.pow(&p_ + 1) * affine_sin.pow(&m_ - 1)
                    / (&f__ * &g__ * (&m_ - 1))),
                x_,
            )
        },
    ));
}

fn push_rules_rule_3153(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, e__, f__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 3153,
        source: "Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
          -b*(g*Cos[e+f*x])^(p+1)*(a+b*Sin[e+f*x])^(m-1)/(f*g*(m+p)) +
          a*(2*m+p-1)/(m+p) \\[Star] Int[(g*Cos[e+f*x])^p*(a+b*Sin[e+f*x])^(m-1),x] /;
        FreeQ[{a,b,e,f,g,m,p},x] && EqQ[a^2-b^2,0] && IGtQ[Simplify[(2*m+p-1)/2],0] && NeQ[m+p,0]",
        desc: "Symmetric cosine/sine recurrence 1c",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [g__, e__, f__, p_, a__, b__, m_, x_],
        optional: [g__, b__, e__, f__],
        when: {
            freeq!([a__, b__, e__, f__, g__, m_, p_], x_)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && {
                    igtq!(
                        rubi_simplify(&((Atom::num(2) * &m_ + &p_ - 1) / 2)),
                        0
                    ) && neq!(&m_ + &p_, 0)
                }
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_cos = &g__ * angle.cos();
            let affine_sin = &a__ + &b__ * angle.sin();
            let recursive_integrand = scaled_cos.pow(&p_) * affine_sin.pow(&m_ - 1);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(
                    &(-&b__ * scaled_cos.pow(&p_ + 1) * affine_sin.pow(&m_ - 1)
                        / (&f__ * &g__ * (&m_ + &p_))),
                    x_,
                ) + rubi_star(&a__ * (Atom::num(2) * &m_ + &p_ - 1) / (&m_ + &p_), recursive)
        },
    ));
}

fn push_rules_rule_3154(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, e__, f__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 3154,
        source: "Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
          -b*(g*Cos[e+f*x])^(p+1)*(a+b*Sin[e+f*x])^m/(a*f*g*(p+1)) +
          a*(m+p+1)/(g^2*(p+1)) \\[Star] Int[(g*Cos[e+f*x])^(p+2)*(a+b*Sin[e+f*x])^(m-1),x] /;
        FreeQ[{a,b,e,f,g},x] && EqQ[a^2-b^2,0] && GtQ[m,0] && LeQ[p,-2*m] && IntegersQ[m+1/2,2*p]",
        desc: "Symmetric cosine/sine recurrence 1b",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [g__, e__, f__, p_, a__, b__, m_, x_],
        optional: [g__, b__, e__, f__],
        when: {
            let minus_2m = -(Atom::num(2) * &m_);
            freeq!([a__, b__, e__, f__, g__], x_)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && gtq!(m_, 0)
                && leq!(p_, minus_2m)
                && integersq!([&m_ + Atom::num(1) / Atom::num(2), Atom::num(2) * &p_])
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_cos = &g__ * angle.cos();
            let affine_sin = &a__ + &b__ * angle.sin();
            let recursive_integrand = scaled_cos.pow(&p_ + 2) * affine_sin.pow(&m_ - 1);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(
                    &(-&b__ * scaled_cos.pow(&p_ + 1) * affine_sin.pow(&m_)
                        / (&a__ * &f__ * &g__ * (&p_ + 1))),
                    x_,
                ) + rubi_star(&a__ * (&m_ + &p_ + 1) / (g__.pow(2) * (&p_ + 1)), recursive)
        },
    ));
}

fn push_rules_rule_3155(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, e__, f__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 3155,
        source: "Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
          -2*b*(g*Cos[e+f*x])^(p+1)*(a+b*Sin[e+f*x])^(m-1)/(f*g*(p+1)) +
          b^2*(2*m+p-1)/(g^2*(p+1)) \\[Star] Int[(g*Cos[e+f*x])^(p+2)*(a+b*Sin[e+f*x])^(m-2),x] /;
        FreeQ[{a,b,e,f,g},x] && EqQ[a^2-b^2,0] && GtQ[m,1] && LtQ[p,-1] && IntegersQ[2*m,2*p]",
        desc: "Symmetric cosine/sine recurrence 1a",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [g__, e__, f__, p_, a__, b__, m_, x_],
        optional: [g__, b__, e__, f__],
        when: {
            freeq!([a__, b__, e__, f__, g__], x_)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && gtq!(m_, 1)
                && ltq!(p_, -1)
                && integersq!([Atom::num(2) * &m_, Atom::num(2) * &p_])
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_cos = &g__ * angle.cos();
            let affine_sin = &a__ + &b__ * angle.sin();
            let recursive_integrand = scaled_cos.pow(&p_ + 2) * affine_sin.pow(&m_ - 2);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(
                    &(-Atom::num(2)
                        * &b__
                        * scaled_cos.pow(&p_ + 1)
                        * affine_sin.pow(&m_ - 1)
                        / (&f__ * &g__ * (&p_ + 1))),
                    x_,
                ) + rubi_star(b__.pow(2) * (Atom::num(2) * &m_ + &p_ - 1) / (g__.pow(2) * (&p_ + 1)), recursive)
        },
    ));
}

fn push_rules_rule_3156(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, e__, f__, g__, x_);
    rules.push(rubi_rule!(
        order: 3156,
        source: "Int[Sqrt[a_+b_.*sin[e_.+f_.*x_]]/Sqrt[g_.*cos[e_.+f_.*x_]],x_Symbol] :=
          a*Sqrt[1+Cos[e+f*x]]*Sqrt[a+b*Sin[e+f*x]]/(a+a*Cos[e+f*x]+b*Sin[e+f*x]) \\[Star] Int[Sqrt[1+Cos[e+f*x]]/Sqrt[g*Cos[e+f*x]],x] +
          b*Sqrt[1+Cos[e+f*x]]*Sqrt[a+b*Sin[e+f*x]]/(a+a*Cos[e+f*x]+b*Sin[e+f*x]) \\[Star] Int[Sin[e+f*x]/(Sqrt[g*Cos[e+f*x]]*Sqrt[1+Cos[e+f*x]]),x] /;
        FreeQ[{a,b,e,f,g},x] && EqQ[a^2-b^2,0]",
        desc: "Piecewise constant extraction and algebraic expansion",
        refs: [],
        pattern: (a__ + b__ * i_sin(e__ + f__ * x_)).sqrt()
            / (g__ * i_cos(e__ + f__ * x_)).sqrt(),
        with: [a__, b__, e__, f__, g__, x_],
        optional: [b__, e__, f__, g__],
        when: {
            freeq!([a__, b__, e__, f__, g__], x_)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let cos = angle.cos();
            let scaled_cos = &g__ * &cos;
            let affine_sin = &a__ + &b__ * &sin;
            let one_plus_cos = Atom::num(1) + &cos;
            let recursive1 = rubi_rhs_int(
                &(one_plus_cos.sqrt() / scaled_cos.sqrt()),
                x_,
            );
            let recursive2 = rubi_rhs_int(
                &(&sin / (scaled_cos.sqrt() * one_plus_cos.sqrt())),
                x_,
            );
            let denominator = &a__ + &a__ * &cos + &b__ * &sin;
            let factor = one_plus_cos.sqrt() * affine_sin.sqrt() / denominator;

            rubi_star(&a__ * &factor, recursive1)
                    + rubi_star(&b__ * factor, recursive2)
        },
    ));
}

fn push_rules_rule_3157(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, e__, f__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 3157,
        source: "Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
          -b*(g*Cos[e+f*x])^(p+1)*(a+b*Sin[e+f*x])^(m-1)/(f*g*(m+p)) +
          a*(2*m+p-1)/(m+p) \\[Star] Int[(g*Cos[e+f*x])^p*(a+b*Sin[e+f*x])^(m-1),x] /;
        FreeQ[{a,b,e,f,g,m,p},x] && EqQ[a^2-b^2,0] && GtQ[m,0] && NeQ[m+p,0] && IntegersQ[2*m,2*p]",
        desc: "Symmetric cosine/sine recurrence 1c",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [g__, e__, f__, p_, a__, b__, m_, x_],
        optional: [g__, b__, e__, f__],
        when: {
            freeq!([a__, b__, e__, f__, g__, m_, p_], x_)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && gtq!(m_, 0)
                && neq!(&m_ + &p_, 0)
                && integersq!([Atom::num(2) * &m_, Atom::num(2) * &p_])
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_cos = &g__ * angle.cos();
            let affine_sin = &a__ + &b__ * angle.sin();
            let recursive_integrand = scaled_cos.pow(&p_) * affine_sin.pow(&m_ - 1);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(-&b__ * scaled_cos.pow(&p_ + 1) * affine_sin.pow(&m_ - 1)
                    / (&f__ * &g__ * (&m_ + &p_))), x_)
                    + rubi_star(&a__ * (Atom::num(2) * &m_ + &p_ - 1) / (&m_ + &p_), recursive)
        },
    ));
}

fn push_rules_rule_3158(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, e__, f__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 3158,
        source: "Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
          g*(g*Cos[e+f*x])^(p-1)*(a+b*Sin[e+f*x])^(m+1)/(b*f*(m+p)) +
          g^2*(p-1)/(a*(m+p)) \\[Star] Int[(g*Cos[e+f*x])^(p-2)*(a+b*Sin[e+f*x])^(m+1),x] /;
        FreeQ[{a,b,e,f,g},x] && EqQ[a^2-b^2,0] && LtQ[m,-1] && GtQ[p,1] && (GtQ[m,-2] || EqQ[2*m+p+1,0] || EqQ[m,-2] && IntegerQ[p]) &&
          NeQ[m+p,0] && IntegersQ[2*m,2*p]",
        desc: "Symmetric cosine/sine recurrence 2a and 1c",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [g__, e__, f__, p_, a__, b__, m_, x_],
        optional: [g__, b__, e__, f__],
        when: {
            freeq!([a__, b__, e__, f__, g__], x_)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && ltq!(m_, -1)
                && gtq!(p_, 1)
                && (gtq!(m_, -2)
                    || eqq!(Atom::num(2) * &m_ + &p_ + 1, 0)
                    || eqq!(m_, -2) && integerq!(p_))
                && neq!(&m_ + &p_, 0)
                && integersq!([Atom::num(2) * &m_, Atom::num(2) * &p_])
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_cos = &g__ * angle.cos();
            let affine_sin = &a__ + &b__ * angle.sin();
            let recursive_integrand = scaled_cos.pow(&p_ - 2) * affine_sin.pow(&m_ + 1);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(&g__ * scaled_cos.pow(&p_ - 1) * affine_sin.pow(&m_ + 1)
                    / (&b__ * &f__ * (&m_ + &p_))), x_)
                    + rubi_star(g__.pow(2) * (&p_ - 1) / (&a__ * (&m_ + &p_)), recursive)
        },
    ));
}

fn push_rules_rule_3159(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, e__, f__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 3159,
        source: "Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
          2*g*(g*Cos[e+f*x])^(p-1)*(a+b*Sin[e+f*x])^(m+1)/(b*f*(2*m+p+1)) +
          g^2*(p-1)/(b^2*(2*m+p+1)) \\[Star] Int[(g*Cos[e+f*x])^(p-2)*(a+b*Sin[e+f*x])^(m+2),x] /;
        FreeQ[{a,b,e,f,g},x] && EqQ[a^2-b^2,0] && LeQ[m,-2] && GtQ[p,1] && NeQ[2*m+p+1,0] && Not[ILtQ[m+p+1,0]] && IntegersQ[2*m,2*p]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [g__, e__, f__, p_, a__, b__, m_, x_],
        optional: [g__, b__, e__, f__],
        when: {
            freeq!([a__, b__, e__, f__, g__], x_)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && leq!(m_, -2)
                && gtq!(p_, 1)
                && neq!(Atom::num(2) * &m_ + &p_ + 1, 0)
                && !iltq!(&m_ + &p_ + 1, 0)
                && integersq!([Atom::num(2) * &m_, Atom::num(2) * &p_])
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_cos = &g__ * angle.cos();
            let affine_sin = &a__ + &b__ * angle.sin();
            let two_m_p_1 = Atom::num(2) * &m_ + &p_ + 1;
            let recursive_integrand = scaled_cos.pow(&p_ - 2) * affine_sin.pow(&m_ + 2);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(Atom::num(2) * &g__ * scaled_cos.pow(&p_ - 1) * affine_sin.pow(&m_ + 1)
                    / (&b__ * &f__ * &two_m_p_1)), x_)
                    + rubi_star(g__.pow(2) * (&p_ - 1) / (b__.pow(2) * two_m_p_1), recursive)
        },
    ));
}

fn push_rules_rule_3160(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, e__, f__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 3160,
        source: "Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
          b*(g*Cos[e+f*x])^(p+1)*(a+b*Sin[e+f*x])^m/(a*f*g*(2*m+p+1)) +
          (m+p+1)/(a*(2*m+p+1)) \\[Star] Int[(g*Cos[e+f*x])^p*(a+b*Sin[e+f*x])^(m+1),x] /;
        FreeQ[{a,b,e,f,g,m,p},x] && EqQ[a^2-b^2,0] && LtQ[m,-1] && NeQ[2*m+p+1,0] && IntegersQ[2*m,2*p]",
        desc: "Symmetric cosine/sine recurrence 2c",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [g__, e__, f__, p_, a__, b__, m_, x_],
        optional: [g__, b__, e__, f__],
        when: {
            freeq!([a__, b__, e__, f__, g__, m_, p_], x_)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && ltq!(m_, -1)
                && neq!(Atom::num(2) * &m_ + &p_ + 1, 0)
                && integersq!([Atom::num(2) * &m_, Atom::num(2) * &p_])
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_cos = &g__ * angle.cos();
            let affine_sin = &a__ + &b__ * angle.sin();
            let two_m_p_1 = Atom::num(2) * &m_ + &p_ + 1;
            let recursive_integrand = scaled_cos.pow(&p_) * affine_sin.pow(&m_ + 1);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(&b__ * scaled_cos.pow(&p_ + 1) * affine_sin.pow(&m_)
                    / (&a__ * &f__ * &g__ * &two_m_p_1)), x_)
                    + rubi_star((&m_ + &p_ + 1) / (&a__ * two_m_p_1), recursive)
        },
    ));
}

fn push_rules_rule_3161(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, e__, f__, g__, p_, x_);
    rules.push(rubi_rule!(
        order: 3161,
        source: "Int[(g_.*cos[e_.+f_.*x_])^p_/(a_+b_.*sin[e_.+f_.*x_]),x_Symbol] :=
          g*(g*Cos[e+f*x])^(p-1)/(b*f*(p-1)) + g^2/a \\[Star] Int[(g*Cos[e+f*x])^(p-2),x] /;
        FreeQ[{a,b,e,f,g},x] && EqQ[a^2-b^2,0] && GtQ[p,1] && IntegerQ[2*p]",
        desc: "Symmetric cosine/sine recurrence 2a and 1c",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [g__, e__, f__, p_, a__, b__, x_],
        optional: [g__, b__, e__, f__],
        when: {
            freeq!([a__, b__, e__, f__, g__], x_)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && gtq!(p_, 1)
                && integerq!(Atom::num(2) * &p_)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_cos = &g__ * angle.cos();
            let recursive_integrand = scaled_cos.pow(&p_ - 2);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(&g__ * scaled_cos.pow(&p_ - 1) / (&b__ * &f__ * (&p_ - 1))), x_)
                    + rubi_star(g__.pow(2) / &a__, recursive)
        },
    ));
}

fn push_rules_rule_3162(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, e__, f__, g__, p_, x_);
    rules.push(rubi_rule!(
        order: 3162,
        source: "Int[(g_.*cos[e_.+f_.*x_])^p_/(a_+b_.*sin[e_.+f_.*x_]),x_Symbol] :=
          b*(g*Cos[e+f*x])^(p+1)/(a*f*g*(p-1)*(a+b*Sin[e+f*x])) +
          p/(a*(p-1)) \\[Star] Int[(g*Cos[e+f*x])^p,x] /;
        FreeQ[{a,b,e,f,g,p},x] && EqQ[a^2-b^2,0] && Not[GeQ[p,1]] && IntegerQ[2*p]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [g__, e__, f__, p_, a__, b__, x_],
        optional: [g__, b__, e__, f__],
        when: {
            freeq!([a__, b__, e__, f__, g__, p_], x_)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && !geq!(p_, 1)
                && integerq!(Atom::num(2) * &p_)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_cos = &g__ * angle.cos();
            let affine_sin = &a__ + &b__ * angle.sin();
            let recursive_integrand = scaled_cos.pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(&b__ * scaled_cos.pow(&p_ + 1)
                    / (&a__ * &f__ * &g__ * (&p_ - 1) * affine_sin)), x_)
                    + rubi_star(&p_ / (&a__ * (&p_ - 1)), recursive)
        },
    ));
}

fn push_rules_rule_3163(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, e__, f__, g__, x_);
    rules.push(rubi_rule!(
        order: 3163,
        source: "Int[Sqrt[g_.*cos[e_.+f_.*x_]]/Sqrt[a_+b_.*sin[e_.+f_.*x_]],x_Symbol] :=
          g*Sqrt[1+Cos[e+f*x]]*Sqrt[a+b*Sin[e+f*x]]/(a+a*Cos[e+f*x]+b*Sin[e+f*x]) \\[Star] Int[Sqrt[1+Cos[e+f*x]]/Sqrt[g*Cos[e+f*x]],x] -
          g*Sqrt[1+Cos[e+f*x]]*Sqrt[a+b*Sin[e+f*x]]/(b+b*Cos[e+f*x]+a*Sin[e+f*x]) \\[Star] Int[Sin[e+f*x]/(Sqrt[g*Cos[e+f*x]]*Sqrt[1+Cos[e+f*x]]),x] /;
        FreeQ[{a,b,e,f,g},x] && EqQ[a^2-b^2,0]",
        desc: "Piecewise constant extraction and algebraic expansion",
        refs: [],
        pattern: (g__ * i_cos(e__ + f__ * x_)).sqrt()
            / (a__ + b__ * i_sin(e__ + f__ * x_)).sqrt(),
        with: [g__, e__, f__, a__, b__, x_],
        optional: [g__, b__, e__, f__],
        when: {
            freeq!([a__, b__, e__, f__, g__], x_)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let cos = angle.cos();
            let scaled_cos = &g__ * &cos;
            let affine_sin = &a__ + &b__ * &sin;
            let one_plus_cos = Atom::num(1) + &cos;
            let recursive1 = rubi_rhs_int(
                &(one_plus_cos.sqrt() / scaled_cos.sqrt()),
                x_,
            );
            let recursive2 = rubi_rhs_int(
                &(&sin / (scaled_cos.sqrt() * one_plus_cos.sqrt())),
                x_,
            );

            rubi_star(&g__ * one_plus_cos.sqrt() * affine_sin.sqrt()
                        / (&a__ + &a__ * &cos + &b__ * &sin), recursive1) - rubi_star(&g__ * one_plus_cos.sqrt() * affine_sin.sqrt()
                        / (&b__ + &b__ * &cos + &a__ * &sin), recursive2)
        },
    ));
}

fn push_rules_rule_3164(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, e__, f__, g__, x_);
    rules.push(rubi_rule!(
        order: 3164,
        source: "Int[(g_.*cos[e_.+f_.*x_])^(3/2)/Sqrt[a_+b_.*sin[e_.+f_.*x_]],x_Symbol] :=
          g*Sqrt[g*Cos[e+f*x]]*Sqrt[a+b*Sin[e+f*x]]/(b*f) +
          g^2/(2*a) \\[Star] Int[Sqrt[a+b*Sin[e+f*x]]/Sqrt[g*Cos[e+f*x]],x] /;
        FreeQ[{a,b,e,f,g},x] && EqQ[a^2-b^2,0]",
        desc: "Symmetric cosine/sine recurrence 2a and 1c",
        refs: [],
        pattern: (g__ * i_cos(e__ + f__ * x_)).pow(Atom::num(3) / Atom::num(2))
            / (a__ + b__ * i_sin(e__ + f__ * x_)).sqrt(),
        with: [g__, e__, f__, a__, b__, x_],
        optional: [g__, b__, e__, f__],
        when: {
            freeq!([a__, b__, e__, f__, g__], x_)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_cos = &g__ * angle.cos();
            let affine_sin = &a__ + &b__ * angle.sin();
            let recursive_integrand = affine_sin.sqrt() / scaled_cos.sqrt();
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(&g__ * scaled_cos.sqrt() * affine_sin.sqrt() / (&b__ * &f__)), x_)
                    + rubi_star(g__.pow(2) / (Atom::num(2) * &a__), recursive)
        },
    ));
}

fn push_rules_rule_3165(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, e__, f__, g__, p_, x_);
    rules.push(rubi_rule!(
        order: 3165,
        source: "Int[(g_.*cos[e_.+f_.*x_])^p_/Sqrt[a_+b_.*sin[e_.+f_.*x_]],x_Symbol] :=
          -2*b*(g*Cos[e+f*x])^(p+1)/(f*g*(2*p-1)*(a+b*Sin[e+f*x])^(3/2)) +
          2*a*(p-2)/(2*p-1) \\[Star] Int[(g*Cos[e+f*x])^p/(a+b*Sin[e+f*x])^(3/2),x] /;
        FreeQ[{a,b,e,f,g},x] && EqQ[a^2-b^2,0] && GtQ[p,2] && IntegerQ[2*p]",
        desc: "Symmetric cosine/sine recurrence 1c with n\\[Rule]-12",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [g__, e__, f__, p_, a__, b__, x_],
        optional: [g__, b__, e__, f__],
        when: {
            freeq!([a__, b__, e__, f__, g__], x_)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && gtq!(p_, 2)
                && integerq!(Atom::num(2) * &p_)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_cos = &g__ * angle.cos();
            let affine_sin = &a__ + &b__ * angle.sin();
            let recursive_integrand =
                scaled_cos.pow(&p_) / affine_sin.pow(Atom::num(3) / Atom::num(2));
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(-Atom::num(2) * &b__ * scaled_cos.pow(&p_ + 1)
                    / (&f__
                        * &g__
                        * (Atom::num(2) * &p_ - 1)
                        * affine_sin.pow(Atom::num(3) / Atom::num(2)))), x_)
                    + rubi_star(Atom::num(2) * &a__ * (&p_ - 2)
                            / (Atom::num(2) * &p_ - 1), recursive)
        },
    ));
}

fn push_rules_rule_3166(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, e__, f__, g__, p_, x_);
    rules.push(rubi_rule!(
        order: 3166,
        source: "Int[(g_.*cos[e_.+f_.*x_])^p_/Sqrt[a_+b_.*sin[e_.+f_.*x_]],x_Symbol] :=
          -b*(g*Cos[e+f*x])^(p+1)/(a*f*g*(p+1)*Sqrt[a+b*Sin[e+f*x]]) +
          a*(2*p+1)/(2*g^2*(p+1)) \\[Star] Int[(g*Cos[e+f*x])^(p+2)/(a+b*Sin[e+f*x])^(3/2),x] /;
        FreeQ[{a,b,e,f,g},x] && EqQ[a^2-b^2,0] && LtQ[p,-1] && IntegerQ[2*p]",
        desc: "Symmetric cosine/sine recurrence 1b with n\\[Rule]-12",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [g__, e__, f__, p_, a__, b__, x_],
        optional: [g__, b__, e__, f__],
        when: {
            freeq!([a__, b__, e__, f__, g__], x_)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && ltq!(p_, -1)
                && integerq!(Atom::num(2) * &p_)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_cos = &g__ * angle.cos();
            let affine_sin = &a__ + &b__ * angle.sin();
            let recursive_integrand =
                scaled_cos.pow(&p_ + 2) / affine_sin.pow(Atom::num(3) / Atom::num(2));
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(-&b__ * scaled_cos.pow(&p_ + 1)
                    / (&a__ * &f__ * &g__ * (&p_ + 1) * affine_sin.sqrt())), x_)
                    + rubi_star(&a__ * (Atom::num(2) * &p_ + 1)
                            / (Atom::num(2) * g__.pow(2) * (&p_ + 1)), recursive)
        },
    ));
}

fn push_rules_rule_3167(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, e__, f__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 3167,
        source: "Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_.,x_Symbol] :=
          a^m*(g*Cos[e+f*x])^(p+1)/(f*g*(1+Sin[e+f*x])^((p+1)/2)*(1-Sin[e+f*x])^((p+1)/2)) \\[Star]
            Subst[Int[(1+b/a*x)^(m+(p-1)/2)*(1-b/a*x)^((p-1)/2),x],x,Sin[e+f*x]] /;
        FreeQ[{a,b,e,f,g,p},x] && EqQ[a^2-b^2,0] && IntegerQ[m]",
        desc: "Piecewise constant extraction and integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [g__, e__, f__, p_, a__, b__, m_, x_],
        optional: [g__, b__, e__, f__, m_],
        when: {
            freeq!([a__, b__, e__, f__, g__, p_], x_)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && integerq!(m_)
        },
        rhs: {
            let subst_guard = fresh_substitution_symbol().unwrap();
            let subst = subst_guard.symbol();
            let z = Atom::var(subst);
            let transformed = (Atom::num(1) + &b__ / &a__ * &z).pow(&m_ + (&p_ - 1) / 2)
                * (Atom::num(1) - &b__ / &a__ * &z).pow((&p_ - 1) / 2);
            let primitive = rubi_rhs_int(&transformed, subst);
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let scaled_cos = &g__ * angle.cos();
            let substituted = rubi_subst(&primitive, subst, &sin);

            rubi_star(a__.pow(&m_) * scaled_cos.pow(&p_ + 1)
                    / (&f__
                        * &g__
                        * (Atom::num(1) + &sin).pow((&p_ + 1) / 2)
                        * (Atom::num(1) - sin).pow((&p_ + 1) / 2)), substituted)
        },
    ));
}

fn push_rules_rule_3168(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, e__, f__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 3168,
        source: "Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_.,x_Symbol] :=
          a^2*(g*Cos[e+f*x])^(p+1)/(f*g*(a+b*Sin[e+f*x])^((p+1)/2)*(a-b*Sin[e+f*x])^((p+1)/2)) \\[Star]
            Subst[Int[(a+b*x)^(m+(p-1)/2)*(a-b*x)^((p-1)/2),x],x,Sin[e+f*x]] /;
        FreeQ[{a,b,e,f,g,m,p},x] && EqQ[a^2-b^2,0] && Not[IntegerQ[m]]",
        desc: "Piecewise constant extraction and integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [g__, e__, f__, p_, a__, b__, m_, x_],
        optional: [g__, b__, e__, f__, m_],
        when: {
            freeq!([a__, b__, e__, f__, g__, m_, p_], x_)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && !integerq!(m_)
        },
        rhs: {
            let subst_guard = fresh_substitution_symbol().unwrap();
            let subst = subst_guard.symbol();
            let z = Atom::var(subst);
            let transformed =
                (&a__ + &b__ * &z).pow(&m_ + (&p_ - 1) / 2) * (&a__ - &b__ * &z).pow((&p_ - 1) / 2);
            let primitive = rubi_rhs_int(&transformed, subst);
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let scaled_cos = &g__ * angle.cos();
            let substituted = rubi_subst(&primitive, subst, &sin);

            rubi_star(a__.pow(2) * scaled_cos.pow(&p_ + 1)
                    / (&f__
                        * &g__
                        * (&a__ + &b__ * &sin).pow((&p_ + 1) / 2)
                        * (&a__ - &b__ * sin).pow((&p_ + 1) / 2)), substituted)
        },
    ));
}

fn push_rules_rule_3169(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, e__, f__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 3169,
        source: "Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
          -(g*Cos[e+f*x])^(p+1)*(a+b*Sin[e+f*x])^m*Sin[e+f*x]/(f*g*(p+1)) +
          1/(g^2*(p+1)) \\[Star] Int[(g*Cos[e+f*x])^(p+2)*(a+b*Sin[e+f*x])^(m-1)*(a*(p+2)+b*(m+p+2)*Sin[e+f*x]),x] /;
        FreeQ[{a,b,e,f,g},x] && NeQ[a^2-b^2,0] && LtQ[0,m,1] && LtQ[p,-1] && (IntegersQ[2*m,2*p] || IntegerQ[m])",
        desc: "Nondegenerate sine recurrence 3a with c\\[Rule]0,d\\[Rule]1,A\\[Rule]0,B\\[Rule]1,C\\[Rule]0,n\\[Rule]-1",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [g__, e__, f__, p_, a__, b__, m_, x_],
        optional: [g__, b__, e__, f__],
        when: {
            freeq!([a__, b__, e__, f__, g__], x_)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && ltq!(0, m_, 1)
                && ltq!(p_, -1)
                && (integersq!([Atom::num(2) * &m_, Atom::num(2) * &p_]) || integerq!(m_))
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let scaled_cos = &g__ * angle.cos();
            let affine_sin = &a__ + &b__ * &sin;
            let recursive_integrand = scaled_cos.pow(&p_ + 2)
                * affine_sin.pow(&m_ - 1)
                * (&a__ * (&p_ + 2) + &b__ * (&m_ + &p_ + 2) * &sin);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(-scaled_cos.pow(&p_ + 1) * affine_sin.pow(&m_) * sin
                    / (&f__ * &g__ * (&p_ + 1))), x_)
                    + rubi_star(Atom::num(1) / (g__.pow(2) * (&p_ + 1)), recursive)
        },
    ));
}

fn push_rules_rule_3170(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, e__, f__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 3170,
        source: "Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
          -(g*Cos[e+f*x])^(p+1)*(a+b*Sin[e+f*x])^(m-1)*(b+a*Sin[e+f*x])/(f*g*(p+1)) +
          1/(g^2*(p+1)) \\[Star] Int[(g*Cos[e+f*x])^(p+2)*(a+b*Sin[e+f*x])^(m-2)*(b^2*(m-1)+a^2*(p+2)+a*b*(m+p+1)*Sin[e+f*x]),x] /;
        FreeQ[{a,b,e,f,g},x] && NeQ[a^2-b^2,0] && GtQ[m,1] && LtQ[p,-1] && (IntegersQ[2*m,2*p] || IntegerQ[m])",
        desc: "Nondegenerate sine recurrence 3a with c\\[Rule]0,d\\[Rule]1,A\\[Rule]0,B\\[Rule]a,C\\[Rule]b,m\\[Rule]m-1,n\\[Rule]-1",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [g__, e__, f__, p_, a__, b__, m_, x_],
        optional: [g__, b__, e__, f__],
        when: {
            freeq!([a__, b__, e__, f__, g__], x_)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && gtq!(m_, 1)
                && ltq!(p_, -1)
                && (integersq!([Atom::num(2) * &m_, Atom::num(2) * &p_]) || integerq!(m_))
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let scaled_cos = &g__ * angle.cos();
            let affine_sin = &a__ + &b__ * &sin;
            let recursive_integrand = scaled_cos.pow(&p_ + 2)
                * affine_sin.pow(&m_ - 2)
                * (b__.pow(2) * (&m_ - 1)
                    + a__.pow(2) * (&p_ + 2)
                    + &a__ * &b__ * (&m_ + &p_ + 1) * &sin);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(-scaled_cos.pow(&p_ + 1) * affine_sin.pow(&m_ - 1) * (&b__ + &a__ * sin)
                    / (&f__ * &g__ * (&p_ + 1))), x_)
                    + rubi_star(Atom::num(1) / (g__.pow(2) * (&p_ + 1)), recursive)
        },
    ));
}

fn push_rules_rule_3171(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, e__, f__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 3171,
        source: "Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
          -b*(g*Cos[e+f*x])^(p+1)*(a+b*Sin[e+f*x])^(m-1)/(f*g*(m+p)) +
          1/(m+p) \\[Star] Int[(g*Cos[e+f*x])^p*(a+b*Sin[e+f*x])^(m-2)*(b^2*(m-1)+a^2*(m+p)+a*b*(2*m+p-1)*Sin[e+f*x]),x] /;
        FreeQ[{a,b,e,f,g,p},x] && NeQ[a^2-b^2,0] && GtQ[m,1] && NeQ[m+p,0] && (IntegersQ[2*m,2*p] || IntegerQ[m])",
        desc: "Nondegenerate sine recurrence 1b with c\\[Rule]0,d\\[Rule]1,A\\[Rule]0,B\\[Rule]a,C\\[Rule]b,m\\[Rule]m-1,n\\[Rule]-1",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [g__, e__, f__, p_, a__, b__, m_, x_],
        optional: [g__, b__, e__, f__],
        when: {
            freeq!([a__, b__, e__, f__, g__, p_], x_)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && gtq!(m_, 1)
                && neq!(&m_ + &p_, 0)
                && (integersq!([Atom::num(2) * &m_, Atom::num(2) * &p_]) || integerq!(m_))
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let scaled_cos = &g__ * angle.cos();
            let affine_sin = &a__ + &b__ * &sin;
            let recursive_integrand = scaled_cos.pow(&p_)
                * affine_sin.pow(&m_ - 2)
                * (b__.pow(2) * (&m_ - 1)
                    + a__.pow(2) * (&m_ + &p_)
                    + &a__ * &b__ * (Atom::num(2) * &m_ + &p_ - 1) * &sin);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(-&b__ * scaled_cos.pow(&p_ + 1) * affine_sin.pow(&m_ - 1)
                    / (&f__ * &g__ * (&m_ + &p_))), x_)
                    + rubi_star(Atom::num(1) / (&m_ + &p_), recursive)
        },
    ));
}

fn push_rules_rule_3172(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, e__, f__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 3172,
        source: "Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
          g*(g*Cos[e+f*x])^(p-1)*(a+b*Sin[e+f*x])^(m+1)/(b*f*(m+1)) +
          g^2*(p-1)/(b*(m+1)) \\[Star] Int[(g*Cos[e+f*x])^(p-2)*(a+b*Sin[e+f*x])^(m+1)*Sin[e+f*x],x] /;
        FreeQ[{a,b,e,f,g},x] && NeQ[a^2-b^2,0] && LtQ[m,-1] && GtQ[p,1] && IntegersQ[2*m,2*p]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [g__, e__, f__, p_, a__, b__, m_, x_],
        optional: [g__, b__, e__, f__],
        when: {
            freeq!([a__, b__, e__, f__, g__], x_)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && ltq!(m_, -1)
                && gtq!(p_, 1)
                && integersq!([Atom::num(2) * &m_, Atom::num(2) * &p_])
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let scaled_cos = &g__ * angle.cos();
            let affine_sin = &a__ + &b__ * &sin;
            let recursive_integrand = scaled_cos.pow(&p_ - 2) * affine_sin.pow(&m_ + 1) * sin;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(&g__ * scaled_cos.pow(&p_ - 1) * affine_sin.pow(&m_ + 1)
                    / (&b__ * &f__ * (&m_ + 1))), x_)
                    + rubi_star(g__.pow(2) * (&p_ - 1) / (&b__ * (&m_ + 1)), recursive)
        },
    ));
}

fn push_rules_rule_3173(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, e__, f__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 3173,
        source: "Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
          -b*(g*Cos[e+f*x])^(p+1)*(a+b*Sin[e+f*x])^(m+1)/(f*g*(a^2-b^2)*(m+1)) +
          1/((a^2-b^2)*(m+1)) \\[Star] Int[(g*Cos[e+f*x])^p*(a+b*Sin[e+f*x])^(m+1)*(a*(m+1)-b*(m+p+2)*Sin[e+f*x]),x] /;
        FreeQ[{a,b,e,f,g,p},x] && NeQ[a^2-b^2,0] && LtQ[m,-1] && IntegersQ[2*m,2*p]",
        desc: "Nondegenerate sine recurrence 1c with c\\[Rule]0,d\\[Rule]1,A\\[Rule]0,B\\[Rule]1,C\\[Rule]0,n\\[Rule]-1",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [g__, e__, f__, p_, a__, b__, m_, x_],
        optional: [g__, b__, e__, f__],
        when: {
            freeq!([a__, b__, e__, f__, g__, p_], x_)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && ltq!(m_, -1)
                && integersq!([Atom::num(2) * &m_, Atom::num(2) * &p_])
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let scaled_cos = &g__ * angle.cos();
            let affine_sin = &a__ + &b__ * &sin;
            let discriminant = a__.pow(2) - b__.pow(2);
            let recursive_integrand = scaled_cos.pow(&p_)
                * affine_sin.pow(&m_ + 1)
                * (&a__ * (&m_ + 1) - &b__ * (&m_ + &p_ + 2) * &sin);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(-&b__ * scaled_cos.pow(&p_ + 1) * affine_sin.pow(&m_ + 1)
                    / (&f__ * &g__ * &discriminant * (&m_ + 1))), x_)
                    + rubi_star(Atom::num(1) / (discriminant * (&m_ + 1)), recursive)
        },
    ));
}

fn push_rules_rule_3174(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, e__, f__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 3174,
        source: "Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
          g*(g*Cos[e+f*x])^(p-1)*(a+b*Sin[e+f*x])^(m+1)/(b*f*(m+p)) +
          g^2*(p-1)/(b*(m+p)) \\[Star] Int[(g*Cos[e+f*x])^(p-2)*(a+b*Sin[e+f*x])^m*(b+a*Sin[e+f*x]),x] /;
        FreeQ[{a,b,e,f,g,m},x] && NeQ[a^2-b^2,0] && GtQ[p,1] && NeQ[m+p,0] && IntegersQ[2*m,2*p]",
        desc: "Nondegenerate sine recurrence 2b with c\\[Rule]0,d\\[Rule]1,A\\[Rule]0,B\\[Rule]1,C\\[Rule]0,n\\[Rule]-1",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [g__, e__, f__, p_, a__, b__, m_, x_],
        optional: [g__, b__, e__, f__],
        when: {
            freeq!([a__, b__, e__, f__, g__, m_], x_)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && gtq!(p_, 1)
                && neq!(&m_ + &p_, 0)
                && integersq!([Atom::num(2) * &m_, Atom::num(2) * &p_])
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let scaled_cos = &g__ * angle.cos();
            let affine_sin = &a__ + &b__ * &sin;
            let recursive_integrand =
                scaled_cos.pow(&p_ - 2) * affine_sin.pow(&m_) * (&b__ + &a__ * sin);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(&g__ * scaled_cos.pow(&p_ - 1) * affine_sin.pow(&m_ + 1)
                    / (&b__ * &f__ * (&m_ + &p_))), x_)
                    + rubi_star(g__.pow(2) * (&p_ - 1) / (&b__ * (&m_ + &p_)), recursive)
        },
    ));
}

fn push_rules_rule_3175(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, e__, f__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 3175,
        source: "Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
          (g*Cos[e+f*x])^(p+1)*(a+b*Sin[e+f*x])^(m+1)*(b-a*Sin[e+f*x])/(f*g*(a^2-b^2)*(p+1)) +
          1/(g^2*(a^2-b^2)*(p+1)) \\[Star] Int[(g*Cos[e+f*x])^(p+2)*(a+b*Sin[e+f*x])^m*(a^2*(p+2)-b^2*(m+p+2)+a*b*(m+p+3)*Sin[e+f*x]),x] /;
        FreeQ[{a,b,e,f,g,m},x] && NeQ[a^2-b^2,0] && LtQ[p,-1] && IntegersQ[2*m,2*p]",
        desc: "Nondegenerate sine recurrence 3b with c\\[Rule]0,d\\[Rule]1,A\\[Rule]0,B\\[Rule]1,C\\[Rule]0,n\\[Rule]-1",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [g__, e__, f__, p_, a__, b__, m_, x_],
        optional: [g__, b__, e__, f__],
        when: {
            freeq!([a__, b__, e__, f__, g__, m_], x_)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && ltq!(p_, -1)
                && integersq!([Atom::num(2) * &m_, Atom::num(2) * &p_])
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let scaled_cos = &g__ * angle.cos();
            let affine_sin = &a__ + &b__ * &sin;
            let discriminant = a__.pow(2) - b__.pow(2);
            let recursive_integrand = scaled_cos.pow(&p_ + 2)
                * affine_sin.pow(&m_)
                * (a__.pow(2) * (&p_ + 2) - b__.pow(2) * (&m_ + &p_ + 2)
                    + &a__ * &b__ * (&m_ + &p_ + 3) * &sin);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(scaled_cos.pow(&p_ + 1)
                    * affine_sin.pow(&m_ + 1)
                    * (&b__ - &a__ * sin)
                    / (&f__ * &g__ * &discriminant * (&p_ + 1))), x_)
                    + rubi_star(Atom::num(1) / (g__.pow(2) * discriminant * (&p_ + 1)), recursive)
        },
    ));
}

fn push_rules_rule_3176(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, e__, f__, g__, x_);
    rules.push(rubi_rule!(
        order: 3176,
        source: "Int[1/(Sqrt[g_.*cos[e_.+f_.*x_]]*Sqrt[a_+b_.*sin[e_.+f_.*x_]]),x_Symbol] :=
          2*Sqrt[2]*Sqrt[g*Cos[e+f*x]]*Sqrt[(a+b*Sin[e+f*x])/((a-b)*(1-Sin[e+f*x]))]/
           (f*g*Sqrt[a+b*Sin[e+f*x]]*Sqrt[(1+Cos[e+f*x]+Sin[e+f*x])/(1+Cos[e+f*x]-Sin[e+f*x])]) \\[Star]
           Subst[Int[1/Sqrt[1+(a+b)*x^4/(a-b)],x],x,Sqrt[(1+Cos[e+f*x]+Sin[e+f*x])/(1+Cos[e+f*x]-Sin[e+f*x])]] /;
        FreeQ[{a,b,e,f,g},x] && NeQ[a^2-b^2,0]",
        desc: "Piecewise constant extraction and integration by substitution",
        refs: [],
        pattern: Atom::num(1)
            / ((g__ * i_cos(e__ + f__ * x_)).sqrt()
                * (a__ + b__ * i_sin(e__ + f__ * x_)).sqrt()),
        with: [g__, e__, f__, a__, b__, x_],
        optional: [g__, b__, e__, f__],
        when: {
            freeq!([a__, b__, e__, f__, g__], x_)
                && neq!(a__.pow(2) - b__.pow(2), 0)
        },
        rhs: {
            let subst_guard = fresh_substitution_symbol().unwrap();
            let subst = subst_guard.symbol();
            let z = Atom::var(subst);
            let transformed = Atom::num(1)
                / (Atom::num(1) + (&a__ + &b__) * z.pow(4) / (&a__ - &b__)).sqrt();
            let primitive = rubi_rhs_int(&transformed, subst);
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let cos = angle.cos();
            let scaled_cos = &g__ * &cos;
            let affine_sin = &a__ + &b__ * &sin;
            let replacement =
                ((Atom::num(1) + &cos + &sin) / (Atom::num(1) + &cos - &sin)).sqrt();
            let substituted = rubi_subst(&primitive, subst, &replacement);

            rubi_star(Atom::num(2)
                    * Atom::num(2).sqrt()
                    * scaled_cos.sqrt()
                    * (&affine_sin / ((&a__ - &b__) * (Atom::num(1) - &sin))).sqrt()
                    / (&f__ * &g__ * affine_sin.sqrt() * replacement), substituted)
        },
    ));
}

fn push_rules_rule_3177(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, e__, f__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 3177,
        source: "Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
          g*(g*Cos[e+f*x])^(p-1)*(1-Sin[e+f*x])*(a+b*Sin[e+f*x])^(m+1)*(-(a-b)*(1-Sin[e+f*x])/((a+b)*(1+Sin[e+f*x])))^(m/2)/
            (f*(a+b)*(m+1))*
            Hypergeometric2F1[m+1,m/2+1,m+2,2*(a+b*Sin[e+f*x])/((a+b)*(1+Sin[e+f*x]))] /;
        FreeQ[{a,b,e,f,g,m,p},x] && NeQ[a^2-b^2,0] && EqQ[m+p+1,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [g__, e__, f__, p_, a__, b__, m_, x_],
        optional: [g__, b__, e__, f__],
        when: {
            freeq!([a__, b__, e__, f__, g__, m_, p_], x_)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && eqq!(&m_ + &p_ + 1, 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let scaled_cos = &g__ * angle.cos();
            let affine_sin = &a__ + &b__ * &sin;
            let argument = Atom::num(2) * &affine_sin / ((&a__ + &b__) * (Atom::num(1) + &sin));

            rubi_simp(&(&g__ * scaled_cos.pow(&p_ - 1)
                    * (Atom::num(1) - &sin)
                    * affine_sin.pow(&m_ + 1)
                    * (-(&a__ - &b__) * (Atom::num(1) - &sin)
                        / ((&a__ + &b__) * (Atom::num(1) + &sin)))
                        .pow(&m_ / 2)
                    * rubi_hypergeometric2f1(
                        &m_ + 1,
                        &m_ / 2 + 1,
                        &m_ + 2,
                        argument,
                    )
                    / (&f__ * (&a__ + &b__) * (&m_ + 1))), x_)
        },
    ));
}

fn push_rules_rule_3178(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, e__, f__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 3178,
        source: "Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
          (g*Cos[e+f*x])^(p+1)*(a+b*Sin[e+f*x])^(m+1)/(f*g*(a-b)*(p+1)) +
          a/(g^2*(a-b)) \\[Star] Int[(g*Cos[e+f*x])^(p+2)*(a+b*Sin[e+f*x])^m/(1-Sin[e+f*x]),x] /;
        FreeQ[{a,b,e,f,g,m,p},x] && NeQ[a^2-b^2,0] && EqQ[m+p+2,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [g__, e__, f__, p_, a__, b__, m_, x_],
        optional: [g__, b__, e__, f__],
        when: {
            freeq!([a__, b__, e__, f__, g__, m_, p_], x_)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && eqq!(&m_ + &p_ + 2, 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let scaled_cos = &g__ * angle.cos();
            let affine_sin = &a__ + &b__ * &sin;
            let recursive_integrand =
                scaled_cos.pow(&p_ + 2) * affine_sin.pow(&m_) / (Atom::num(1) - &sin);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(scaled_cos.pow(&p_ + 1) * affine_sin.pow(&m_ + 1)
                    / (&f__ * &g__ * (&a__ - &b__) * (&p_ + 1))), x_)
                    + rubi_star(&a__ / (g__.pow(2) * (&a__ - &b__)), recursive)
        },
    ));
}

fn push_rules_rule_3179(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, e__, f__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 3179,
        source: "Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
          (g*Cos[e+f*x])^(p+1)*(a+b*Sin[e+f*x])^(m+1)/(f*g*(a-b)*(p+1)) -
          b*(m+p+2)/(g^2*(a-b)*(p+1)) \\[Star] Int[(g*Cos[e+f*x])^(p+2)*(a+b*Sin[e+f*x])^m,x] +
          a/(g^2*(a-b)) \\[Star] Int[(g*Cos[e+f*x])^(p+2)*(a+b*Sin[e+f*x])^m/(1-Sin[e+f*x]),x] /;
        FreeQ[{a,b,e,f,g,m,p},x] && NeQ[a^2-b^2,0] && ILtQ[m+p+2,0]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [g__, e__, f__, p_, a__, b__, m_, x_],
        optional: [g__, b__, e__, f__],
        when: {
            freeq!([a__, b__, e__, f__, g__, m_, p_], x_)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && iltq!(&m_ + &p_ + 2, 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let scaled_cos = &g__ * angle.cos();
            let affine_sin = &a__ + &b__ * &sin;
            let recursive_integrand1 = scaled_cos.pow(&p_ + 2) * affine_sin.pow(&m_);
            let recursive1 = rubi_rhs_int(&recursive_integrand1, x_);
            let recursive_integrand2 =
                scaled_cos.pow(&p_ + 2) * affine_sin.pow(&m_) / (Atom::num(1) - &sin);
            let recursive2 = rubi_rhs_int(&recursive_integrand2, x_);

            rubi_simp(&(scaled_cos.pow(&p_ + 1) * affine_sin.pow(&m_ + 1)
                    / (&f__ * &g__ * (&a__ - &b__) * (&p_ + 1))), x_)
                    - rubi_star(&b__ * (&m_ + &p_ + 2)
                            / (g__.pow(2) * (&a__ - &b__) * (&p_ + 1)), recursive1)
                    + rubi_star(&a__ / (g__.pow(2) * (&a__ - &b__)), recursive2)
        },
    ));
}

fn push_rules_rule_3180(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, e__, f__, g__, x_);
    rules.push(rubi_rule!(
        order: 3180,
        source: "Int[Sqrt[g_.*cos[e_.+f_.*x_]]/(a_+b_.*sin[e_.+f_.*x_]),x_Symbol] :=
          With[{q=Rt[-a^2+b^2,2]},
          a*g/(2*b) \\[Star] Int[1/(Sqrt[g*Cos[e+f*x]]*(q+b*Cos[e+f*x])),x] -
          a*g/(2*b) \\[Star] Int[1/(Sqrt[g*Cos[e+f*x]]*(q-b*Cos[e+f*x])),x] +
          b*g/f \\[Star] Subst[Int[Sqrt[x]/(g^2*(a^2-b^2)+b^2*x^2),x],x,g*Cos[e+f*x]]] /;
        FreeQ[{a,b,e,f,g},x] && NeQ[a^2-b^2,0]",
        desc: "Algebraic expansion and integration by substitution",
        refs: [],
        pattern: (g__ * i_cos(e__ + f__ * x_)).sqrt()
            / (a__ + b__ * i_sin(e__ + f__ * x_)),
        with: [g__, e__, f__, a__, b__, x_],
        optional: [g__, b__, e__, f__],
        when: {
            freeq!([a__, b__, e__, f__, g__], x_)
                && neq!(a__.pow(2) - b__.pow(2), 0)
        },
        rhs: {
            let q = rubi_rt(&(-a__.pow(2) + b__.pow(2)), 2);
            let subst_guard = fresh_substitution_symbol().unwrap();
            let subst = subst_guard.symbol();
            let z = Atom::var(subst);
            let transformed = z.sqrt() / (g__.pow(2) * (a__.pow(2) - b__.pow(2)) + b__.pow(2) * z.pow(2));
            let primitive = rubi_rhs_int(&transformed, subst);
            let angle = &e__ + &f__ * x_;
            let scaled_cos = &g__ * angle.cos();
            let recursive1 = rubi_rhs_int(
                &(Atom::num(1) / (scaled_cos.sqrt() * (&q + &b__ * angle.cos()))),
                x_,
            );
            let recursive2 = rubi_rhs_int(
                &(Atom::num(1) / (scaled_cos.sqrt() * (&q - &b__ * angle.cos()))),
                x_,
            );
            let substituted = rubi_subst(&primitive, subst, scaled_cos);

            rubi_star(&a__ * &g__ / (Atom::num(2) * &b__), recursive1) - rubi_star(&a__ * &g__ / (Atom::num(2) * &b__), recursive2) + rubi_star(&b__ * &g__ / &f__, substituted)
        },
    ));
}

fn push_rules_rule_3181(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, e__, f__, g__, x_);
    rules.push(rubi_rule!(
        order: 3181,
        source: "Int[1/(Sqrt[g_.*cos[e_.+f_.*x_]]*(a_+b_.*sin[e_.+f_.*x_])),x_Symbol] :=
          With[{q=Rt[-a^2+b^2,2]},
          -a/(2*q) \\[Star] Int[1/(Sqrt[g*Cos[e+f*x]]*(q+b*Cos[e+f*x])),x] -
          a/(2*q) \\[Star] Int[1/(Sqrt[g*Cos[e+f*x]]*(q-b*Cos[e+f*x])),x] +
          b*g/f \\[Star] Subst[Int[1/(Sqrt[x]*(g^2*(a^2-b^2)+b^2*x^2)),x],x,g*Cos[e+f*x]]] /;
        FreeQ[{a,b,e,f,g},x] && NeQ[a^2-b^2,0]",
        desc: "Algebraic expansion and integration by substitution",
        refs: [],
        pattern: Atom::num(1)
            / ((g__ * i_cos(e__ + f__ * x_)).sqrt()
                * (a__ + b__ * i_sin(e__ + f__ * x_))),
        with: [g__, e__, f__, a__, b__, x_],
        optional: [g__, b__, e__, f__],
        when: {
            freeq!([a__, b__, e__, f__, g__], x_)
                && neq!(a__.pow(2) - b__.pow(2), 0)
        },
        rhs: {
            let q = rubi_rt(&(-a__.pow(2) + b__.pow(2)), 2);
            let subst_guard = fresh_substitution_symbol().unwrap();
            let subst = subst_guard.symbol();
            let z = Atom::var(subst);
            let transformed = Atom::num(1)
                / (z.sqrt() * (g__.pow(2) * (a__.pow(2) - b__.pow(2)) + b__.pow(2) * z.pow(2)));
            let primitive = rubi_rhs_int(&transformed, subst);
            let angle = &e__ + &f__ * x_;
            let scaled_cos = &g__ * angle.cos();
            let recursive1 = rubi_rhs_int(
                &(Atom::num(1) / (scaled_cos.sqrt() * (&q + &b__ * angle.cos()))),
                x_,
            );
            let recursive2 = rubi_rhs_int(
                &(Atom::num(1) / (scaled_cos.sqrt() * (&q - &b__ * angle.cos()))),
                x_,
            );
            let substituted = rubi_subst(&primitive, subst, scaled_cos);

            rubi_star(-&a__ / (Atom::num(2) * &q), recursive1)
                    - rubi_star(&a__ / (Atom::num(2) * &q), recursive2)
                    + rubi_star(&b__ * &g__ / &f__, substituted)
        },
    ));
}

fn push_rules_rule_3182(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, e__, f__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 3182,
        source: "Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
          g*(g*Cos[e+f*x])^(p-1)*(a+b*Sin[e+f*x])^(m+1)/
            (b*f*(m+p)*(-b*(1-Sin[e+f*x])/(a+b*Sin[e+f*x]))^((p-1)/2)*(b*(1+Sin[e+f*x])/(a+b*Sin[e+f*x]))^((p-1)/2))*
          AppellF1[-p-m,(1-p)/2,(1-p)/2,1-p-m,(a+b)/(a+b*Sin[e+f*x]),(a-b)/(a+b*Sin[e+f*x])] /;
        FreeQ[{a,b,e,f,g,p},x] && NeQ[a^2-b^2,0] && ILtQ[m,0] && Not[IGtQ[m+p+1,0]]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [g__, e__, f__, p_, a__, b__, m_, x_],
        optional: [g__, b__, e__, f__],
        when: {
            freeq!([a__, b__, e__, f__, g__, p_], x_)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && iltq!(m_, 0)
                && !igtq!(&m_ + &p_ + 1, 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let scaled_cos = &g__ * angle.cos();
            let affine_sin = &a__ + &b__ * &sin;

            rubi_simp(&(&g__ * scaled_cos.pow(&p_ - 1) * affine_sin.pow(&m_ + 1)
                    * rubi_appell_f1(
                        -&p_ - &m_,
                        (Atom::num(1) - &p_) / 2,
                        (Atom::num(1) - &p_) / 2,
                        Atom::num(1) - &p_ - &m_,
                        (&a__ + &b__) / &affine_sin,
                        (&a__ - &b__) / &affine_sin,
                    )
                    / (&b__
                        * &f__
                        * (&m_ + &p_)
                        * (-&b__ * (Atom::num(1) - &sin) / &affine_sin).pow((&p_ - 1) / 2)
                        * (&b__ * (Atom::num(1) + &sin) / affine_sin).pow((&p_ - 1) / 2))), x_)
        },
    ));
}

fn push_rules_rule_3183(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, e__, f__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 3183,
        source: "Int[(g_.*cos[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_,x_Symbol] :=
          g*(g*Cos[e+f*x])^(p-1)/(f*(1-(a+b*Sin[e+f*x])/(a-b))^((p-1)/2)*(1-(a+b*Sin[e+f*x])/(a+b))^((p-1)/2)) \\[Star]
            Subst[Int[(-b/(a-b)-b*x/(a-b))^((p-1)/2)*(b/(a+b)-b*x/(a+b))^((p-1)/2)*(a+b*x)^m,x],x,Sin[e+f*x]] /;
        FreeQ[{a,b,e,f,g,m,p},x] && NeQ[a^2-b^2,0] && Not[IGtQ[m,0]]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [g__, e__, f__, p_, a__, b__, m_, x_],
        optional: [g__, b__, e__, f__],
        when: {
            freeq!([a__, b__, e__, f__, g__, m_, p_], x_)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && !igtq!(m_, 0)
        },
        rhs: {
            let subst_guard = fresh_substitution_symbol().unwrap();
            let subst = subst_guard.symbol();
            let z = Atom::var(subst);
            let transformed = (-&b__ / (&a__ - &b__) - &b__ * &z / (&a__ - &b__)).pow((&p_ - 1) / 2)
                * (&b__ / (&a__ + &b__) - &b__ * &z / (&a__ + &b__)).pow((&p_ - 1) / 2)
                * (&a__ + &b__ * &z).pow(&m_);
            let primitive = rubi_rhs_int(&transformed, subst);
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let scaled_cos = &g__ * angle.cos();
            let affine_sin = &a__ + &b__ * &sin;
            let substituted = rubi_subst(&primitive, subst, sin);

            rubi_star(&g__ * scaled_cos.pow(&p_ - 1)
                    / (&f__
                        * (Atom::num(1) - &affine_sin / (&a__ - &b__)).pow((&p_ - 1) / 2)
                        * (Atom::num(1) - affine_sin / (&a__ + &b__)).pow((&p_ - 1) / 2)), substituted)
        },
    ));
}

fn push_rules_rule_3184(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, e__, f__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 3184,
        source: "Int[(g_.*sec[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_.,x_Symbol] :=
          g^(2*IntPart[p])*(g*Cos[e+f*x])^FracPart[p]*(g*Sec[e+f*x])^FracPart[p] \\[Star] Int[(a+b*Sin[e+f*x])^m/(g*Cos[e+f*x])^p,x] /;
        FreeQ[{a,b,e,f,g,m,p},x] && Not[IntegerQ[p]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: (g__ * i_sec(e__ + f__ * x_)).pow(p_)
            * (a__ + b__ * i_sin(e__ + f__ * x_)).pow(m_),
        with: [g__, e__, f__, p_, a__, b__, m_, x_],
        optional: [g__, b__, e__, f__, m_],
        when: {
            freeq!([a__, b__, e__, f__, g__, m_, p_], x_)
                && !integerq!(p_)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let scaled_cos = &g__ * angle.cos();
            let scaled_sec = &g__ * angle.sec();
            let affine_sin = &a__ + &b__ * angle.sin();
            let recursive_integrand = affine_sin.pow(&m_) / scaled_cos.pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(g__.pow(Atom::num(2) * rubi_int_part(&p_))
                    * scaled_cos.pow(rubi_frac_part(&p_))
                    * scaled_sec.pow(rubi_frac_part(&p_)), recursive)
        },
    ));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn downvalues_3146_through_3184_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .filter(|order| (3146..=3184).contains(order))
            .collect::<Vec<_>>();

        assert_eq!(orders, (3146..=3184).collect::<Vec<_>>());
    }
}

// Generated shared pattern builders.

#[inline(never)]
fn rubi_shared_pattern_0(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let g__ = symbols.g__;
    let m_ = symbols.m_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (g__ * i_cos(e__ + f__ * x_)).pow(p_) * (a__ + b__ * i_sin(e__ + f__ * x_)).pow(m_)
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let g__ = symbols.g__;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (g__ * i_cos(e__ + f__ * x_)).pow(p_) / (a__ + b__ * i_sin(e__ + f__ * x_))
}

#[inline(never)]
fn rubi_shared_pattern_2(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let g__ = symbols.g__;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (g__ * i_cos(e__ + f__ * x_)).pow(p_) / (a__ + b__ * i_sin(e__ + f__ * x_)).sqrt()
}

#[inline(never)]
fn rubi_shared_pattern_3(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    i_cos(e__ + f__ * x_).pow(p_) * (a__ + b__ * i_sin(e__ + f__ * x_)).pow(m_)
}
