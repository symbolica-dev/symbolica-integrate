use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_3407(rules);
    push_rules_rule_3408(rules);
    push_rules_rule_3409(rules);
    push_rules_rule_3410(rules);
    push_rules_rule_3411(rules);
    push_rules_rule_3412(rules);
    push_rules_rule_3413(rules);
    push_rules_rule_3414(rules);
    push_rules_rule_3415(rules);
    push_rules_rule_3416(rules);
    push_rules_rule_3417(rules);
    push_rules_rule_3418(rules);
    push_rules_rule_3419(rules);
    push_rules_rule_3420(rules);
    push_rules_rule_3421(rules);
    push_rules_rule_3422(rules);
    push_rules_rule_3423(rules);
    push_rules_rule_3424(rules);
    push_rules_rule_3425(rules);
    push_rules_rule_3426(rules);
    push_rules_rule_3427(rules);
    push_rules_rule_3428(rules);
    push_rules_rule_3429(rules);
    push_rules_rule_3430(rules);
    push_rules_rule_3431(rules);
    push_rules_rule_3432(rules);
    push_rules_rule_3433(rules);
    push_rules_rule_3434(rules);
    push_rules_rule_3435(rules);
    push_rules_rule_3436(rules);
    push_rules_rule_3437(rules);
    push_rules_rule_3438(rules);
    push_rules_rule_3439(rules);
    push_rules_rule_3440(rules);
    push_rules_rule_3441(rules);
    push_rules_rule_3442(rules);
    push_rules_rule_3443(rules);
    push_rules_rule_3444(rules);
}

fn push_rules_rule_3407(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, x_);
    rules.push(rubi_rule!(
        order: 3407,
        source: "Int[Sqrt[g_.*sin[e_.+f_.*x_]]*Sqrt[a_+b_.*sin[e_.+f_.*x_]]/(c_+d_.*sin[e_.+f_.*x_]),x_Symbol] :=
          g/d \\[Star] Int[Sqrt[a+b*Sin[e+f*x]]/Sqrt[g*Sin[e+f*x]],x] -
          c*g/d \\[Star] Int[Sqrt[a+b*Sin[e+f*x]]/(Sqrt[g*Sin[e+f*x]]*(c+d*Sin[e+f*x])),x] /;
        FreeQ[{a,b,c,d,e,f,g},x] && NeQ[b*c-a*d,0] && (EqQ[a^2-b^2,0] || EqQ[c^2-d^2,0])",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [g__, e__, f__, a__, b__, c__, d__, x_],
        optional: [g__, e__, f__, b__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && (eqq!(a__.pow(2) - b__.pow(2), 0) || eqq!(c__.pow(2) - d__.pow(2), 0))
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let recursive1 = rubi_rhs_int(
                &((&a__ + &b__ * angle.sin()).sqrt() / (&g__ * angle.sin()).sqrt()),
                x_,
            );
            let recursive2 = rubi_rhs_int(
                &((&a__ + &b__ * angle.sin()).sqrt()
                    / ((&g__ * angle.sin()).sqrt() * (&c__ + &d__ * angle.sin()))),
                x_,
            );

            rubi_star(&g__ / &d__, recursive1)
                    - rubi_star(&c__ * &g__ / &d__, recursive2)
        },
    ));
}

fn push_rules_rule_3408(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, x_);
    rules.push(rubi_rule!(
        order: 3408,
        source: "Int[Sqrt[g_.*sin[e_.+f_.*x_]]*Sqrt[a_+b_.*sin[e_.+f_.*x_]]/(c_+d_.*sin[e_.+f_.*x_]),x_Symbol] :=
          b/d \\[Star] Int[Sqrt[g*Sin[e+f*x]]/Sqrt[a+b*Sin[e+f*x]],x] -
          (b*c-a*d)/d \\[Star] Int[Sqrt[g*Sin[e+f*x]]/(Sqrt[a+b*Sin[e+f*x]]*(c+d*Sin[e+f*x])),x] /;
        FreeQ[{a,b,c,d,e,f,g},x] && NeQ[b*c-a*d,0] && NeQ[a^2-b^2,0] && NeQ[c^2-d^2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [g__, e__, f__, a__, b__, c__, d__, x_],
        optional: [g__, e__, f__, b__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && neq!(c__.pow(2) - d__.pow(2), 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let recursive1 = rubi_rhs_int(
                &((&g__ * angle.sin()).sqrt() / (&a__ + &b__ * angle.sin()).sqrt()),
                x_,
            );
            let recursive2 = rubi_rhs_int(
                &((&g__ * angle.sin()).sqrt()
                    / ((&a__ + &b__ * angle.sin()).sqrt() * (&c__ + &d__ * angle.sin()))),
                x_,
            );

            rubi_star(&b__ / &d__, recursive1)
                    - rubi_star((&b__ * &c__ - &a__ * &d__) / &d__, recursive2)
        },
    ));
}

fn push_rules_rule_3409(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, x_);
    rules.push(rubi_rule!(
        order: 3409,
        source: "Int[Sqrt[a_+b_.*sin[e_.+f_.*x_]]/(Sqrt[g_.*sin[e_.+f_.*x_]]*(c_+d_.*sin[e_.+f_.*x_])),x_Symbol] :=
          -2*b/f \\[Star] Subst[Int[1/(b*c+a*d+c*g*x^2),x],x,b*Cos[e+f*x]/(Sqrt[g*Sin[e+f*x]]*Sqrt[a+b*Sin[e+f*x]])] /;
        FreeQ[{a,b,c,d,e,f,g},x] && NeQ[b*c-a*d,0] && EqQ[a^2-b^2,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, e__, f__, g__, c__, d__, x_],
        optional: [b__, e__, f__, g__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let z = Atom::var(sub);
            let transformed = Atom::num(1) / (&b__ * &c__ + &a__ * &d__ + &c__ * &g__ * z.pow(2));
            let primitive = rubi_rhs_int(&transformed, sub);
            let angle = &e__ + &f__ * x_;
            let replacement =
                &b__ * angle.cos() / ((&g__ * angle.sin()).sqrt() * (&a__ + &b__ * angle.sin()).sqrt());

            let substituted = rubi_subst(&primitive, sub, replacement);
            rubi_star(-Atom::num(2) * &b__ / &f__, substituted)
        },
    ));
}

fn push_rules_rule_3410(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 3410,
        source: "Int[Sqrt[a_+b_.*sin[e_.+f_.*x_]]/(Sqrt[sin[e_.+f_.*x_]]*(c_+d_.*sin[e_.+f_.*x_])),x_Symbol] :=
          -Sqrt[a+b]/(c*f)*EllipticE[ArcSin[Cos[e+f*x]/(1+Sin[e+f*x])],-(a-b)/(a+b)] /;
        FreeQ[{a,b,c,d,e,f},x] && EqQ[d,c] && GtQ[b^2-a^2,0] && GtQ[b,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: (a__ + b__ * i_sin(e__ + f__ * x_)).sqrt()
            / (i_sin(e__ + f__ * x_).sqrt() * (c__ + d__ * i_sin(e__ + f__ * x_))),
        with: [a__, b__, e__, f__, c__, d__, x_],
        optional: [b__, e__, f__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && eqq!(d__, c__)
                && gtq!(b__.pow(2) - a__.pow(2), 0)
                && gtq!(b__, 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let phi = (angle.cos() / (Atom::num(1) + angle.sin())).asin();
            let elliptic_m = -(&a__ - &b__) / (&a__ + &b__);

            rubi_simp(&(-(&a__ + &b__).sqrt() * rubi_elliptic_e(phi, elliptic_m) / (&c__ * &f__)), x_)
        },
    ));
}

fn push_rules_rule_3411(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, x_);
    rules.push(rubi_rule!(
        order: 3411,
        source: "Int[Sqrt[a_+b_.*sin[e_.+f_.*x_]]/(Sqrt[g_.*sin[e_.+f_.*x_]]*(c_+d_.*sin[e_.+f_.*x_])),x_Symbol] :=
          -Sqrt[a+b*Sin[e+f*x]]*Sqrt[d*Sin[e+f*x]/(c+d*Sin[e+f*x])]/
            (d*f*Sqrt[g*Sin[e+f*x]]*Sqrt[c^2*(a+b*Sin[e+f*x])/((a*c+b*d)*(c+d*Sin[e+f*x]))])*
            EllipticE[ArcSin[c*Cos[e+f*x]/(c+d*Sin[e+f*x])],(b*c-a*d)/(b*c+a*d)] /;
        FreeQ[{a,b,c,d,e,f,g},x] && NeQ[b*c-a*d,0] && NeQ[a^2-b^2,0] && EqQ[c^2-d^2,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, e__, f__, g__, c__, d__, x_],
        optional: [b__, e__, f__, g__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && eqq!(c__.pow(2) - d__.pow(2), 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let phi = (&c__ * angle.cos() / (&c__ + &d__ * &sin)).asin();
            let elliptic_m = (&b__ * &c__ - &a__ * &d__) / (&b__ * &c__ + &a__ * &d__);

            rubi_simp(&(-(&a__ + &b__ * &sin).sqrt()
                    * (&d__ * &sin / (&c__ + &d__ * &sin)).sqrt()
                    * rubi_elliptic_e(phi, elliptic_m)
                    / (&d__
                        * &f__
                        * (&g__ * &sin).sqrt()
                        * (c__.pow(2) * (&a__ + &b__ * &sin)
                            / ((&a__ * &c__ + &b__ * &d__) * (&c__ + &d__ * &sin)))
                            .sqrt())), x_)
        },
    ));
}

fn push_rules_rule_3412(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, x_);
    rules.push(rubi_rule!(
        order: 3412,
        source: "Int[Sqrt[a_+b_.*sin[e_.+f_.*x_]]/(Sqrt[g_.*sin[e_.+f_.*x_]]*(c_+d_.*sin[e_.+f_.*x_])),x_Symbol] :=
          a/c \\[Star] Int[1/(Sqrt[g*Sin[e+f*x]]*Sqrt[a+b*Sin[e+f*x]]),x] +
          (b*c-a*d)/(c*g) \\[Star] Int[Sqrt[g*Sin[e+f*x]]/(Sqrt[a+b*Sin[e+f*x]]*(c+d*Sin[e+f*x])),x] /;
        FreeQ[{a,b,c,d,e,f,g},x] && NeQ[b*c-a*d,0] && NeQ[a^2-b^2,0] && NeQ[c^2-d^2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, e__, f__, g__, c__, d__, x_],
        optional: [b__, e__, f__, g__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && neq!(c__.pow(2) - d__.pow(2), 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let recursive1 = rubi_rhs_int(
                &(Atom::num(1) / ((&g__ * angle.sin()).sqrt() * (&a__ + &b__ * angle.sin()).sqrt())),
                x_,
            );
            let recursive2 = rubi_rhs_int(
                &((&g__ * angle.sin()).sqrt()
                    / ((&a__ + &b__ * angle.sin()).sqrt() * (&c__ + &d__ * angle.sin()))),
                x_,
            );

            rubi_star(&a__ / &c__, recursive1)
                    + rubi_star((&b__ * &c__ - &a__ * &d__) / (&c__ * &g__), recursive2)
        },
    ));
}

fn push_rules_rule_3413(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 3413,
        source: "Int[Sqrt[a_+b_.*sin[e_.+f_.*x_]]/(sin[e_.+f_.*x_]*(c_+d_.*sin[e_.+f_.*x_])),x_Symbol] :=
          1/c \\[Star] Int[Sqrt[a+b*Sin[e+f*x]]/Sin[e+f*x],x] -
          d/c \\[Star] Int[Sqrt[a+b*Sin[e+f*x]]/(c+d*Sin[e+f*x]),x] /;
        FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d,0] && EqQ[a^2-b^2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, e__, f__, c__, d__, x_],
        optional: [b__, e__, f__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let recursive1 = rubi_rhs_int(
                &((&a__ + &b__ * angle.sin()).sqrt() / angle.sin()),
                x_,
            );
            let recursive2 = rubi_rhs_int(
                &((&a__ + &b__ * angle.sin()).sqrt() / (&c__ + &d__ * angle.sin())),
                x_,
            );

            rubi_star(Atom::num(1) / &c__, recursive1)
                    - rubi_star(&d__ / &c__, recursive2)
        },
    ));
}

fn push_rules_rule_3414(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 3414,
        source: "Int[Sqrt[a_+b_.*sin[e_.+f_.*x_]]/(sin[e_.+f_.*x_]*(c_+d_.*sin[e_.+f_.*x_])),x_Symbol] :=
          a/c \\[Star] Int[1/(Sin[e+f*x]*Sqrt[a+b*Sin[e+f*x]]),x] +
          (b*c-a*d)/c \\[Star] Int[1/(Sqrt[a+b*Sin[e+f*x]]*(c+d*Sin[e+f*x])),x] /;
        FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d,0] && NeQ[a^2-b^2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, e__, f__, c__, d__, x_],
        optional: [b__, e__, f__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && neq!(a__.pow(2) - b__.pow(2), 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let recursive1 = rubi_rhs_int(
                &(Atom::num(1) / (angle.sin() * (&a__ + &b__ * angle.sin()).sqrt())),
                x_,
            );
            let recursive2 = rubi_rhs_int(
                &(Atom::num(1) / ((&a__ + &b__ * angle.sin()).sqrt() * (&c__ + &d__ * angle.sin()))),
                x_,
            );

            rubi_star(&a__ / &c__, recursive1)
                    + rubi_star((&b__ * &c__ - &a__ * &d__) / &c__, recursive2)
        },
    ));
}

fn push_rules_rule_3415(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, x_);
    rules.push(rubi_rule!(
        order: 3415,
        source: "Int[Sqrt[g_.*sin[e_.+f_.*x_]]/(Sqrt[a_+b_.*sin[e_.+f_.*x_]]*(c_+d_.*sin[e_.+f_.*x_])),x_Symbol] :=
          -a*g/(b*c-a*d) \\[Star] Int[1/(Sqrt[g*Sin[e+f*x]]*Sqrt[a+b*Sin[e+f*x]]),x] +
          c*g/(b*c-a*d) \\[Star] Int[Sqrt[a+b*Sin[e+f*x]]/(Sqrt[g*Sin[e+f*x]]*(c+d*Sin[e+f*x])),x] /;
        FreeQ[{a,b,c,d,e,f,g},x] && NeQ[b*c-a*d,0] && (EqQ[a^2-b^2,0] || EqQ[c^2-d^2,0])",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_10(symbols),
        with: [g__, e__, f__, a__, b__, c__, d__, x_],
        optional: [g__, e__, f__, b__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && (eqq!(a__.pow(2) - b__.pow(2), 0) || eqq!(c__.pow(2) - d__.pow(2), 0))
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let recursive1 = rubi_rhs_int(
                &(Atom::num(1) / ((&g__ * angle.sin()).sqrt() * (&a__ + &b__ * angle.sin()).sqrt())),
                x_,
            );
            let recursive2 = rubi_rhs_int(
                &((&a__ + &b__ * angle.sin()).sqrt()
                    / ((&g__ * angle.sin()).sqrt() * (&c__ + &d__ * angle.sin()))),
                x_,
            );

            rubi_star(-&a__ * &g__ / (&b__ * &c__ - &a__ * &d__), recursive1)
                    + rubi_star(&c__ * &g__ / (&b__ * &c__ - &a__ * &d__), recursive2)
        },
    ));
}

fn push_rules_rule_3416(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, x_);
    rules.push(rubi_rule!(
        order: 3416,
        source: "Int[Sqrt[g_.*sin[e_.+f_.*x_]]/(Sqrt[a_+b_.*sin[e_.+f_.*x_]]*(c_+d_.*sin[e_.+f_.*x_])),x_Symbol] :=
          2*Sqrt[-Cot[e+f*x]^2]*Sqrt[g*Sin[e+f*x]]/(f*(c+d)*Cot[e+f*x]*Sqrt[a+b*Sin[e+f*x]])*Sqrt[(b+a*Csc[e+f*x])/(a+b)]*
            EllipticPi[2*c/(c+d),ArcSin[Sqrt[1-Csc[e+f*x]]/Sqrt[2]],2*a/(a+b)] /;
        FreeQ[{a,b,c,d,e,f,g},x] && NeQ[b*c-a*d,0] && NeQ[a^2-b^2,0] && NeQ[c^2-d^2,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_10(symbols),
        with: [g__, e__, f__, a__, b__, c__, d__, x_],
        optional: [g__, e__, f__, b__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && neq!(c__.pow(2) - d__.pow(2), 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let elliptic_n = Atom::num(2) * &c__ / (&c__ + &d__);
            let elliptic_phi = ((Atom::num(1) - angle.csc()).sqrt() / Atom::num(2).sqrt()).asin();
            let elliptic_m = Atom::num(2) * &a__ / (&a__ + &b__);

            rubi_simp(&(Atom::num(2)
                    * (-(angle.cot().pow(2))).sqrt()
                    * (&g__ * angle.sin()).sqrt()
                    * ((&b__ + &a__ * angle.csc()) / (&a__ + &b__)).sqrt()
                    * rubi_elliptic_pi(elliptic_n, elliptic_phi, elliptic_m)
                    / (&f__ * (&c__ + &d__) * angle.cot() * (&a__ + &b__ * angle.sin()).sqrt())), x_)
        },
    ));
}

fn push_rules_rule_3417(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, x_);
    rules.push(rubi_rule!(
        order: 3417,
        source: "Int[1/(Sqrt[g_.*sin[e_.+f_.*x_]]*Sqrt[a_+b_.*sin[e_.+f_.*x_]]*(c_+d_.*sin[e_.+f_.*x_])),x_Symbol] :=
          b/(b*c-a*d) \\[Star] Int[1/(Sqrt[g*Sin[e+f*x]]*Sqrt[a+b*Sin[e+f*x]]),x] -
          d/(b*c-a*d) \\[Star] Int[Sqrt[a+b*Sin[e+f*x]]/(Sqrt[g*Sin[e+f*x]]*(c+d*Sin[e+f*x])),x] /;
        FreeQ[{a,b,c,d,e,f,g},x] && NeQ[b*c-a*d,0] && (EqQ[a^2-b^2,0] || EqQ[c^2-d^2,0])",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_11(symbols),
        with: [g__, e__, f__, a__, b__, c__, d__, x_],
        optional: [g__, e__, f__, b__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && (eqq!(a__.pow(2) - b__.pow(2), 0) || eqq!(c__.pow(2) - d__.pow(2), 0))
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let recursive1 = rubi_rhs_int(
                &(Atom::num(1) / ((&g__ * angle.sin()).sqrt() * (&a__ + &b__ * angle.sin()).sqrt())),
                x_,
            );
            let recursive2 = rubi_rhs_int(
                &((&a__ + &b__ * angle.sin()).sqrt()
                    / ((&g__ * angle.sin()).sqrt() * (&c__ + &d__ * angle.sin()))),
                x_,
            );

            rubi_star(&b__ / (&b__ * &c__ - &a__ * &d__), recursive1)
                    - rubi_star(&d__ / (&b__ * &c__ - &a__ * &d__), recursive2)
        },
    ));
}

fn push_rules_rule_3418(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, x_);
    rules.push(rubi_rule!(
        order: 3418,
        source: "Int[1/(Sqrt[g_.*sin[e_.+f_.*x_]]*Sqrt[a_+b_.*sin[e_.+f_.*x_]]*(c_+d_.*sin[e_.+f_.*x_])),x_Symbol] :=
          1/c \\[Star] Int[1/(Sqrt[g*Sin[e+f*x]]*Sqrt[a+b*Sin[e+f*x]]),x] -
          d/(c*g) \\[Star] Int[Sqrt[g*Sin[e+f*x]]/(Sqrt[a+b*Sin[e+f*x]]*(c+d*Sin[e+f*x])),x] /;
        FreeQ[{a,b,c,d,e,f,g},x] && NeQ[b*c-a*d,0] && NeQ[a^2-b^2,0] && NeQ[c^2-d^2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_11(symbols),
        with: [g__, e__, f__, a__, b__, c__, d__, x_],
        optional: [g__, e__, f__, b__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && neq!(c__.pow(2) - d__.pow(2), 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let recursive1 = rubi_rhs_int(
                &(Atom::num(1) / ((&g__ * angle.sin()).sqrt() * (&a__ + &b__ * angle.sin()).sqrt())),
                x_,
            );
            let recursive2 = rubi_rhs_int(
                &((&g__ * angle.sin()).sqrt()
                    / ((&a__ + &b__ * angle.sin()).sqrt() * (&c__ + &d__ * angle.sin()))),
                x_,
            );

            rubi_star(Atom::num(1) / &c__, recursive1)
                    - rubi_star(&d__ / (&c__ * &g__), recursive2)
        },
    ));
}

fn push_rules_rule_3419(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 3419,
        source: "Int[1/(sin[e_.+f_.*x_]*Sqrt[a_+b_.*sin[e_.+f_.*x_]]*(c_+d_.*sin[e_.+f_.*x_])),x_Symbol] :=
          d^2/(c*(b*c-a*d)) \\[Star] Int[Sqrt[a+b*Sin[e+f*x]]/(c+d*Sin[e+f*x]),x] +
          1/(c*(b*c-a*d)) \\[Star] Int[(b*c-a*d-b*d*Sin[e+f*x])/(Sin[e+f*x]*Sqrt[a+b*Sin[e+f*x]]),x] /;
        FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d,0] && EqQ[a^2-b^2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_12(symbols),
        with: [e__, f__, a__, b__, c__, d__, x_],
        optional: [e__, f__, b__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let recursive1 = rubi_rhs_int(
                &((&a__ + &b__ * angle.sin()).sqrt() / (&c__ + &d__ * angle.sin())),
                x_,
            );
            let recursive2 = rubi_rhs_int(
                &((&b__ * &c__ - &a__ * &d__ - &b__ * &d__ * angle.sin())
                    / (angle.sin() * (&a__ + &b__ * angle.sin()).sqrt())),
                x_,
            );

            rubi_star(d__.pow(2) / (&c__ * (&b__ * &c__ - &a__ * &d__)), recursive1)
                    + rubi_star(Atom::num(1) / (&c__ * (&b__ * &c__ - &a__ * &d__)), recursive2)
        },
    ));
}

fn push_rules_rule_3420(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 3420,
        source: "Int[1/(sin[e_.+f_.*x_]*Sqrt[a_+b_.*sin[e_.+f_.*x_]]*(c_+d_.*sin[e_.+f_.*x_])),x_Symbol] :=
          1/c \\[Star] Int[1/(Sin[e+f*x]*Sqrt[a+b*Sin[e+f*x]]),x] - d/c \\[Star] Int[1/(Sqrt[a+b*Sin[e+f*x]]*(c+d*Sin[e+f*x])),x] /;
        FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d,0] && NeQ[a^2-b^2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_12(symbols),
        with: [e__, f__, a__, b__, c__, d__, x_],
        optional: [e__, f__, b__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && neq!(a__.pow(2) - b__.pow(2), 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let recursive1 = rubi_rhs_int(
                &(Atom::num(1) / (angle.sin() * (&a__ + &b__ * angle.sin()).sqrt())),
                x_,
            );
            let recursive2 = rubi_rhs_int(
                &(Atom::num(1) / ((&a__ + &b__ * angle.sin()).sqrt() * (&c__ + &d__ * angle.sin()))),
                x_,
            );

            rubi_star(Atom::num(1) / &c__, recursive1)
                    - rubi_star(&d__ / &c__, recursive2)
        },
    ));
}

fn push_rules_rule_3421(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 3421,
        source: "Int[Sqrt[a_+b_.*sin[e_.+f_.*x_]]/(sin[e_.+f_.*x_]*Sqrt[c_+d_.*sin[e_.+f_.*x_]]),x_Symbol] :=
          -d/c \\[Star] Int[Sqrt[a+b*Sin[e+f*x]]/Sqrt[c+d*Sin[e+f*x]],x] +
          1/c \\[Star] Int[Sqrt[a+b*Sin[e+f*x]]*Sqrt[c+d*Sin[e+f*x]]/Sin[e+f*x],x] /;
        FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d,0] && EqQ[a^2-b^2,0] && EqQ[b*c+a*d,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, e__, f__, c__, d__, x_],
        optional: [b__, e__, f__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && eqq!(&b__ * &c__ + &a__ * &d__, 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let recursive1 = rubi_rhs_int(
                &((&a__ + &b__ * angle.sin()).sqrt() / (&c__ + &d__ * angle.sin()).sqrt()),
                x_,
            );
            let recursive2 = rubi_rhs_int(
                &((&a__ + &b__ * angle.sin()).sqrt() * (&c__ + &d__ * angle.sin()).sqrt()
                    / angle.sin()),
                x_,
            );

            rubi_star(-&d__ / &c__, recursive1)
                    + rubi_star(Atom::num(1) / &c__, recursive2)
        },
    ));
}

fn push_rules_rule_3422(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 3422,
        source: "Int[Sqrt[a_+b_.*sin[e_.+f_.*x_]]/(sin[e_.+f_.*x_]*Sqrt[c_+d_.*sin[e_.+f_.*x_]]),x_Symbol] :=
          -2*a/f \\[Star] Subst[Int[1/(1-a*c*x^2),x],x,Cos[e+f*x]/(Sqrt[a+b*Sin[e+f*x]]*Sqrt[c+d*Sin[e+f*x]])] /;
        FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d,0] && EqQ[a^2-b^2,0] && NeQ[b*c+a*d,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, e__, f__, c__, d__, x_],
        optional: [b__, e__, f__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && neq!(&b__ * &c__ + &a__ * &d__, 0)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let z = Atom::var(sub);
            let transformed = Atom::num(1) / (Atom::num(1) - &a__ * &c__ * z.pow(2));
            let primitive = rubi_rhs_int(&transformed, sub);
            let angle = &e__ + &f__ * x_;
            let replacement =
                angle.cos() / ((&a__ + &b__ * angle.sin()).sqrt() * (&c__ + &d__ * angle.sin()).sqrt());

            let substituted = rubi_subst(&primitive, sub, replacement);
            rubi_star(-Atom::num(2) * &a__ / &f__, substituted)
        },
    ));
}

fn push_rules_rule_3423(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 3423,
        source: "Int[Sqrt[a_+b_.*sin[e_.+f_.*x_]]/(sin[e_.+f_.*x_]*Sqrt[c_+d_.*sin[e_.+f_.*x_]]),x_Symbol] :=
          (b*c-a*d)/c \\[Star] Int[1/(Sqrt[a+b*Sin[e+f*x]]*Sqrt[c+d*Sin[e+f*x]]),x] +
          a/c \\[Star] Int[Sqrt[c+d*Sin[e+f*x]]/(Sin[e+f*x]*Sqrt[a+b*Sin[e+f*x]]),x] /;
        FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d,0] && NeQ[a^2-b^2,0] && EqQ[c^2-d^2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, e__, f__, c__, d__, x_],
        optional: [b__, e__, f__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && eqq!(c__.pow(2) - d__.pow(2), 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let recursive1 = rubi_rhs_int(
                &(Atom::num(1)
                    / ((&a__ + &b__ * angle.sin()).sqrt() * (&c__ + &d__ * angle.sin()).sqrt())),
                x_,
            );
            let recursive2 = rubi_rhs_int(
                &((&c__ + &d__ * angle.sin()).sqrt()
                    / (angle.sin() * (&a__ + &b__ * angle.sin()).sqrt())),
                x_,
            );

            rubi_star((&b__ * &c__ - &a__ * &d__) / &c__, recursive1)
                    + rubi_star(&a__ / &c__, recursive2)
        },
    ));
}

fn push_rules_rule_3424(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 3424,
        source: "Int[Sqrt[a_+b_.*sin[e_.+f_.*x_]]/(sin[e_.+f_.*x_]*Sqrt[c_+d_.*sin[e_.+f_.*x_]]),x_Symbol] :=
          -2*(a+b*Sin[e+f*x])/(c*f*Rt[(a+b)/(c+d),2]*Cos[e+f*x])*
            Sqrt[-(b*c-a*d)*(1-Sin[e+f*x])/((c+d)*(a+b*Sin[e+f*x]))]*Sqrt[(b*c-a*d)*(1+Sin[e+f*x])/((c-d)*(a+b*Sin[e+f*x]))]*
            EllipticPi[a*(c+d)/(c*(a+b)),ArcSin[Rt[(a+b)/(c+d),2]*Sqrt[c+d*Sin[e+f*x]]/Sqrt[a+b*Sin[e+f*x]]],(a-b)*(c+d)/((a+b)*(c-d))] /;
        FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d,0] && NeQ[a^2-b^2,0] && NeQ[c^2-d^2,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, e__, f__, c__, d__, x_],
        optional: [b__, e__, f__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && neq!(c__.pow(2) - d__.pow(2), 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let rt = rubi_rt(&((&a__ + &b__) / (&c__ + &d__)), 2);
            let elliptic_n = &a__ * (&c__ + &d__) / (&c__ * (&a__ + &b__));
            let elliptic_phi =
                (&rt * (&c__ + &d__ * &sin).sqrt() / (&a__ + &b__ * &sin).sqrt()).asin();
            let elliptic_m = (&a__ - &b__) * (&c__ + &d__) / ((&a__ + &b__) * (&c__ - &d__));

            rubi_simp(&(-Atom::num(2)
                    * (&a__ + &b__ * &sin)
                    * (-(&b__ * &c__ - &a__ * &d__) * (Atom::num(1) - &sin)
                        / ((&c__ + &d__) * (&a__ + &b__ * &sin)))
                        .sqrt()
                    * ((&b__ * &c__ - &a__ * &d__) * (Atom::num(1) + &sin)
                        / ((&c__ - &d__) * (&a__ + &b__ * &sin)))
                        .sqrt()
                    * rubi_elliptic_pi(elliptic_n, elliptic_phi, elliptic_m)
                    / (&c__ * &f__ * &rt * angle.cos())), x_)
        },
    ));
}

fn push_rules_rule_3425(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 3425,
        source: "Int[1/(sin[e_.+f_.*x_]*Sqrt[a_+b_.*sin[e_.+f_.*x_]]*Sqrt[c_+d_.*sin[e_.+f_.*x_]]),x_Symbol] :=
          Cos[e+f*x]/(Sqrt[a+b*Sin[e+f*x]]*Sqrt[c+d*Sin[e+f*x]]) \\[Star] Int[1/(Cos[e+f*x]*Sin[e+f*x]),x] /;
        FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d,0] && EqQ[a^2-b^2,0] && EqQ[c^2-d^2,0]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_13(symbols),
        with: [e__, f__, a__, b__, c__, d__, x_],
        optional: [e__, f__, b__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && eqq!(c__.pow(2) - d__.pow(2), 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let recursive = rubi_rhs_int(&(Atom::num(1) / (angle.cos() * angle.sin())), x_);

            rubi_star(angle.cos()
                    / ((&a__ + &b__ * angle.sin()).sqrt()
                        * (&c__ + &d__ * angle.sin()).sqrt()), recursive)
        },
    ));
}

fn push_rules_rule_3426(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 3426,
        source: "Int[1/(sin[e_.+f_.*x_]*Sqrt[a_+b_.*sin[e_.+f_.*x_]]*Sqrt[c_+d_.*sin[e_.+f_.*x_]]),x_Symbol] :=
          -b/a \\[Star] Int[1/(Sqrt[a+b*Sin[e+f*x]]*Sqrt[c+d*Sin[e+f*x]]),x] +
          1/a \\[Star] Int[Sqrt[a+b*Sin[e+f*x]]/(Sin[e+f*x]*Sqrt[c+d*Sin[e+f*x]]),x] /;
        FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d,0] && (NeQ[a^2-b^2,0] || NeQ[c^2-d^2,0])",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_13(symbols),
        with: [e__, f__, a__, b__, c__, d__, x_],
        optional: [e__, f__, b__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && (neq!(a__.pow(2) - b__.pow(2), 0) || neq!(c__.pow(2) - d__.pow(2), 0))
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let recursive1 = rubi_rhs_int(
                &(Atom::num(1)
                    / ((&a__ + &b__ * angle.sin()).sqrt() * (&c__ + &d__ * angle.sin()).sqrt())),
                x_,
            );
            let recursive2 = rubi_rhs_int(
                &((&a__ + &b__ * angle.sin()).sqrt()
                    / (angle.sin() * (&c__ + &d__ * angle.sin()).sqrt())),
                x_,
            );

            rubi_star(-&b__ / &a__, recursive1)
                    + rubi_star(Atom::num(1) / &a__, recursive2)
        },
    ));
}

fn push_rules_rule_3427(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 3427,
        source: "Int[Sqrt[a_+b_.*sin[e_.+f_.*x_]]*Sqrt[c_+d_.*sin[e_.+f_.*x_]]/sin[e_.+f_.*x_],x_Symbol] :=
          Sqrt[a+b*Sin[e+f*x]]*Sqrt[c+d*Sin[e+f*x]]/Cos[e+f*x] \\[Star] Int[Cot[e+f*x],x] /;
        FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d,0] && EqQ[a^2-b^2,0] && EqQ[c^2-d^2,0]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, e__, f__, c__, d__, x_],
        optional: [b__, e__, f__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && eqq!(c__.pow(2) - d__.pow(2), 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let recursive = rubi_rhs_int(&angle.cot(), x_);

            rubi_star((&a__ + &b__ * angle.sin()).sqrt()
                    * (&c__ + &d__ * angle.sin()).sqrt()
                    / angle.cos(), recursive)
        },
    ));
}

fn push_rules_rule_3428(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 3428,
        source: "Int[Sqrt[a_+b_.*sin[e_.+f_.*x_]]*Sqrt[c_+d_.*sin[e_.+f_.*x_]]/sin[e_.+f_.*x_],x_Symbol] :=
          d \\[Star] Int[Sqrt[a+b*Sin[e+f*x]]/Sqrt[c+d*Sin[e+f*x]],x] +
          c \\[Star] Int[Sqrt[a+b*Sin[e+f*x]]/(Sin[e+f*x]*Sqrt[c+d*Sin[e+f*x]]),x] /;
        FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d,0] && (NeQ[a^2-b^2,0] || NeQ[c^2-d^2,0])",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, e__, f__, c__, d__, x_],
        optional: [b__, e__, f__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && (neq!(a__.pow(2) - b__.pow(2), 0) || neq!(c__.pow(2) - d__.pow(2), 0))
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let recursive1 = rubi_rhs_int(
                &((&a__ + &b__ * angle.sin()).sqrt() / (&c__ + &d__ * angle.sin()).sqrt()),
                x_,
            );
            let recursive2 = rubi_rhs_int(
                &((&a__ + &b__ * angle.sin()).sqrt()
                    / (angle.sin() * (&c__ + &d__ * angle.sin()).sqrt())),
                x_,
            );

            rubi_star(d__, recursive1) + rubi_star(c__, recursive2)
        },
    ));
}

fn push_rules_rule_3429(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3429,
        source: "Int[sin[e_.+f_.*x_]^p_*(a_+b_.*sin[e_.+f_.*x_])^m_.*(c_+d_.*sin[e_.+f_.*x_])^n_.,x_Symbol] :=
          a^n*c^n \\[Star] Int[Tan[e+f*x]^p*(a+b*Sin[e+f*x])^(m-n),x] /;
        FreeQ[{a,b,c,d,e,f,m},x] && EqQ[b*c+a*d,0] && EqQ[a^2-b^2,0] && EqQ[p+2*n,0] && IntegerQ[n]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: i_sin(e__ + f__ * x_).pow(p_)
            * (a__ + b__ * i_sin(e__ + f__ * x_)).pow(m_)
            * (c__ + d__ * i_sin(e__ + f__ * x_)).pow(n_),
        with: [e__, f__, p_, a__, b__, m_, c__, d__, n_, x_],
        optional: [e__, f__, b__, m_, d__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_], x_)
                && eqq!(&b__ * &c__ + &a__ * &d__, 0)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && eqq!(&p_ + Atom::num(2) * &n_, 0)
                && integerq!(n_)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let recursive = rubi_rhs_int(
                &(angle.tan().pow(&p_) * (&a__ + &b__ * angle.sin()).pow(&m_ - &n_)),
                x_,
            );

            rubi_star(a__.pow(&n_) * c__.pow(&n_), recursive)
        },
    ));
}

fn push_rules_rule_3430(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3430,
        source: "Int[(g_.*sin[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_*(c_+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
          Sqrt[a-b*Sin[e+f*x]]*Sqrt[a+b*Sin[e+f*x]]/(f*Cos[e+f*x]) \\[Star]
            Subst[Int[(g*x)^p*(a+b*x)^(m-1/2)*(c+d*x)^n/Sqrt[a-b*x],x],x,Sin[e+f*x]] /;
        FreeQ[{a,b,c,d,e,f,g,m,n,p},x] && NeQ[b*c-a*d,0] && EqQ[a^2-b^2,0] && NeQ[c^2-d^2,0] && IntegerQ[m-1/2]",
        desc: "Piecewise constant extraction and integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [g__, e__, f__, p_, a__, b__, m_, c__, d__, n_, x_],
        optional: [g__, e__, f__, b__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, m_, n_, p_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && neq!(c__.pow(2) - d__.pow(2), 0)
                && integerq!(&m_ - Atom::num(1) / Atom::num(2))
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let z = Atom::var(sub);
            let transformed = (&g__ * &z).pow(&p_)
                * (&a__ + &b__ * &z).pow(&m_ - Atom::num(1) / Atom::num(2))
                * (&c__ + &d__ * &z).pow(&n_)
                / (&a__ - &b__ * &z).sqrt();
            let primitive = rubi_rhs_int(&transformed, sub);
            let angle = &e__ + &f__ * x_;

            let substituted = rubi_subst(&primitive, sub, i_sin(&angle));
            rubi_star((&a__ - &b__ * i_sin(&angle)).sqrt()
                    * (&a__ + &b__ * i_sin(&angle)).sqrt()
                    / (&f__ * angle.cos()), substituted)
        },
    ));
}

fn push_rules_rule_3431(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3431,
        source: "Int[(g_.*sin[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_*(c_+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
          Int[ExpandTrig[(g*sin[e+f*x])^p*(a+b*sin[e+f*x])^m*(c+d*sin[e+f*x])^n,x],x] /;
        FreeQ[{a,b,c,d,e,f,g,n,p},x] && NeQ[b*c-a*d,0] && (IntegersQ[m,n] || IntegersQ[m,p] || IntegersQ[n,p]) && NeQ[p,2]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [g__, e__, f__, p_, a__, b__, m_, c__, d__, n_, x_],
        optional: [g__, e__, f__, b__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, n_, p_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && (integersq!([m_, n_]) || integersq!([m_, p_]) || integersq!([n_, p_]))
                && neq!(p_, 2)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let payload = (&g__ * i_sin(&angle)).pow(&p_)
                * (&a__ + &b__ * i_sin(&angle)).pow(&m_)
                * (&c__ + &d__ * i_sin(&angle)).pow(&n_);
            let expanded = rubi_expand_trig(&payload, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_3432(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3432,
        source: "Int[(g_.*sin[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_*(c_+d_.*sin[e_.+f_.*x_])^n_,x_Symbol] :=
          Unintegrable[(g*Sin[e+f*x])^p*(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^n,x] /;
        FreeQ[{a,b,c,d,e,f,g,m,n,p},x] && NeQ[p,2]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [g__, e__, f__, p_, a__, b__, m_, c__, d__, n_, x_],
        optional: [g__, e__, f__, b__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, m_, n_, p_], x_)
                && neq!(p_, 2)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let integrand = (&g__ * i_sin(&angle)).pow(&p_)
                * (&a__ + &b__ * i_sin(&angle)).pow(&m_)
                * (&c__ + &d__ * i_sin(&angle)).pow(&n_);

            rubi_unintegrable(integrand, x_)
        },
    ));
}

fn push_rules_rule_3433(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3433,
        source: "Int[(g_.*sin[e_.+f_.*x_])^p_.*(a_.+b_.*csc[e_.+f_.*x_])^m_.*(c_+d_.*csc[e_.+f_.*x_])^n_.,x_Symbol] :=
          g^(m+n) \\[Star] Int[(g*Sin[e+f*x])^(p-m-n)*(b+a*Sin[e+f*x])^m*(d+c*Sin[e+f*x])^n,x] /;
        FreeQ[{a,b,c,d,e,f,g,p},x] && NeQ[b*c-a*d,0] && Not[IntegerQ[p]] && IntegerQ[m] && IntegerQ[n]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [g__, e__, f__, p_, a__, b__, m_, c__, d__, n_, x_],
        optional: [g__, e__, f__, p_, a__, b__, m_, d__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, p_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && !integerq!(p_)
                && integerq!(m_)
                && integerq!(n_)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let recursive = rubi_rhs_int(
                &((&g__ * angle.sin()).pow(&p_ - &m_ - &n_)
                    * (&b__ + &a__ * angle.sin()).pow(&m_)
                    * (&d__ + &c__ * angle.sin()).pow(&n_)),
                x_,
            );

            rubi_star(g__.pow(&m_ + &n_), recursive)
        },
    ));
}

fn push_rules_rule_3434(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3434,
        source: "Int[(g_.*sin[e_.+f_.*x_])^p_.*(a_.+b_.*csc[e_.+f_.*x_])^m_.*(c_+d_.*csc[e_.+f_.*x_])^n_.,x_Symbol] :=
          (g*Csc[e+f*x])^p*(g*Sin[e+f*x])^p \\[Star] Int[(a+b*Csc[e+f*x])^m*(c+d*Csc[e+f*x])^n/(g*Csc[e+f*x])^p,x] /;
        FreeQ[{a,b,c,d,e,f,g,m,n,p},x] && NeQ[b*c-a*d,0] && Not[IntegerQ[p]] && Not[IntegerQ[m] && IntegerQ[n]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [g__, e__, f__, p_, a__, b__, m_, c__, d__, n_, x_],
        optional: [g__, e__, f__, p_, a__, b__, m_, d__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, m_, n_, p_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && !integerq!(p_)
                && !(integerq!(m_) && integerq!(n_))
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let recursive = rubi_rhs_int(
                &((&a__ + &b__ * angle.csc()).pow(&m_)
                    * (&c__ + &d__ * angle.csc()).pow(&n_)
                    / (&g__ * angle.csc()).pow(&p_)),
                x_,
            );

            rubi_star((&g__ * angle.csc()).pow(&p_)
                    * (&g__ * angle.sin()).pow(&p_), recursive)
        },
    ));
}

fn push_rules_rule_3435(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3435,
        source: "Int[(g_.*sin[e_.+f_.*x_])^p_.*(a_+b_.*sin[e_.+f_.*x_])^m_.*(c_+d_.*csc[e_.+f_.*x_])^n_.,x_Symbol] :=
          g^n \\[Star] Int[(g*Sin[e+f*x])^(p-n)*(a+b*Sin[e+f*x])^m*(d+c*Sin[e+f*x])^n,x] /;
        FreeQ[{a,b,c,d,e,f,g,m,p},x] && IntegerQ[n]",
        desc: "Algebraic normalization",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [g__, e__, f__, p_, a__, b__, m_, c__, d__, n_, x_],
        optional: [g__, e__, f__, p_, b__, m_, d__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, m_, p_], x_)
                && integerq!(n_)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let recursive = rubi_rhs_int(
                &((&g__ * angle.sin()).pow(&p_ - &n_)
                    * (&a__ + &b__ * angle.sin()).pow(&m_)
                    * (&d__ + &c__ * angle.sin()).pow(&n_)),
                x_,
            );

            rubi_star(g__.pow(&n_), recursive)
        },
    ));
}

fn push_rules_rule_3436(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3436,
        source: "Int[sin[e_.+f_.*x_]^p_.*(a_+b_.*sin[e_.+f_.*x_])^m_.*(c_+d_.*csc[e_.+f_.*x_])^n_,x_Symbol] :=
          Int[(b+a*Csc[e+f*x])^m*(c+d*Csc[e+f*x])^n/Csc[e+f*x]^(m+p),x] /;
        FreeQ[{a,b,c,d,e,f,n},x] && Not[IntegerQ[n]] && IntegerQ[m] && IntegerQ[p]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: i_sin(e__ + f__ * x_).pow(p_)
            * (a__ + b__ * i_sin(e__ + f__ * x_)).pow(m_)
            * (c__ + d__ * i_csc(e__ + f__ * x_)).pow(n_),
        with: [e__, f__, p_, a__, b__, m_, c__, d__, n_, x_],
        optional: [e__, f__, p_, b__, m_, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, n_], x_)
                && !integerq!(n_)
                && integerq!(m_)
                && integerq!(p_)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;

            rubi_rhs_int(
                &((&b__ + &a__ * angle.csc()).pow(&m_)
                    * (&c__ + &d__ * angle.csc()).pow(&n_)
                    / angle.csc().pow(&m_ + &p_)),
                x_,
            )
        },
    ));
}

fn push_rules_rule_3437(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3437,
        source: "Int[(g_.*sin[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_.*(c_+d_.*csc[e_.+f_.*x_])^n_,x_Symbol] :=
          Csc[e+f*x]^p*(g*Sin[e+f*x])^p \\[Star] Int[(b+a*Csc[e+f*x])^m*(c+d*Csc[e+f*x])^n/Csc[e+f*x]^(m+p),x] /;
        FreeQ[{a,b,c,d,e,f,g,n,p},x] && Not[IntegerQ[n]] && IntegerQ[m] && Not[IntegerQ[p]]",
        desc: "Algebraic normalization and piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [g__, e__, f__, p_, a__, b__, m_, c__, d__, n_, x_],
        optional: [g__, e__, f__, b__, m_, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, n_, p_], x_)
                && !integerq!(n_)
                && integerq!(m_)
                && !integerq!(p_)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let recursive = rubi_rhs_int(
                &((&b__ + &a__ * angle.csc()).pow(&m_)
                    * (&c__ + &d__ * angle.csc()).pow(&n_)
                    / angle.csc().pow(&m_ + &p_)),
                x_,
            );

            rubi_star(angle.csc().pow(&p_) * (&g__ * angle.sin()).pow(&p_), recursive)
        },
    ));
}

fn push_rules_rule_3438(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3438,
        source: "Int[(g_.*sin[e_.+f_.*x_])^p_.*(a_+b_.*sin[e_.+f_.*x_])^m_*(c_+d_.*csc[e_.+f_.*x_])^n_,x_Symbol] :=
          (g*Sin[e+f*x])^n*(c+d*Csc[e+f*x])^n/(d+c*Sin[e+f*x])^n \\[Star] Int[(g*Sin[e+f*x])^(p-n)*(a+b*Sin[e+f*x])^m*(d+c*Sin[e+f*x])^n,x] /;
        FreeQ[{a,b,c,d,e,f,g,m,n,p},x] && Not[IntegerQ[n]] && Not[IntegerQ[m]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [g__, e__, f__, p_, a__, b__, m_, c__, d__, n_, x_],
        optional: [g__, e__, f__, p_, b__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, m_, n_, p_], x_)
                && !integerq!(n_)
                && !integerq!(m_)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let recursive = rubi_rhs_int(
                &((&g__ * angle.sin()).pow(&p_ - &n_)
                    * (&a__ + &b__ * angle.sin()).pow(&m_)
                    * (&d__ + &c__ * angle.sin()).pow(&n_)),
                x_,
            );

            rubi_star((&g__ * angle.sin()).pow(&n_)
                    * (&c__ + &d__ * angle.csc()).pow(&n_)
                    / (&d__ + &c__ * angle.sin()).pow(&n_), recursive)
        },
    ));
}

fn push_rules_rule_3439(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3439,
        source: "Int[(g_.*csc[e_.+f_.*x_])^p_.*(a_.+b_.*sin[e_.+f_.*x_])^m_.*(c_+d_.*sin[e_.+f_.*x_])^n_.,x_Symbol] :=
          g^(m+n) \\[Star] Int[(g*Csc[e+f*x])^(p-m-n)*(b+a*Csc[e+f*x])^m*(d+c*Csc[e+f*x])^n,x] /;
        FreeQ[{a,b,c,d,e,f,g,p},x] && NeQ[b*c-a*d,0] && Not[IntegerQ[p]] && IntegerQ[m] && IntegerQ[n]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [g__, e__, f__, p_, a__, b__, m_, c__, d__, n_, x_],
        optional: [g__, e__, f__, p_, a__, b__, m_, d__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, p_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && !integerq!(p_)
                && integerq!(m_)
                && integerq!(n_)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let recursive = rubi_rhs_int(
                &((&g__ * angle.csc()).pow(&p_ - &m_ - &n_)
                    * (&b__ + &a__ * angle.csc()).pow(&m_)
                    * (&d__ + &c__ * angle.csc()).pow(&n_)),
                x_,
            );

            rubi_star(g__.pow(&m_ + &n_), recursive)
        },
    ));
}

fn push_rules_rule_3440(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3440,
        source: "Int[(g_.*csc[e_.+f_.*x_])^p_.*(a_.+b_.*sin[e_.+f_.*x_])^m_.*(c_+d_.*sin[e_.+f_.*x_])^n_.,x_Symbol] :=
          (g*Csc[e+f*x])^p*(g*Sin[e+f*x])^p \\[Star] Int[(a+b*Sin[e+f*x])^m*(c+d*Sin[e+f*x])^n/(g*Sin[e+f*x])^p,x] /;
        FreeQ[{a,b,c,d,e,f,g,m,n,p},x] && NeQ[b*c-a*d,0] && Not[IntegerQ[p]] && Not[IntegerQ[m] && IntegerQ[n]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [g__, e__, f__, p_, a__, b__, m_, c__, d__, n_, x_],
        optional: [g__, e__, f__, p_, a__, b__, m_, d__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, m_, n_, p_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && !integerq!(p_)
                && !(integerq!(m_) && integerq!(n_))
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let recursive = rubi_rhs_int(
                &((&a__ + &b__ * angle.sin()).pow(&m_)
                    * (&c__ + &d__ * angle.sin()).pow(&n_)
                    / (&g__ * angle.sin()).pow(&p_)),
                x_,
            );

            rubi_star((&g__ * angle.csc()).pow(&p_)
                    * (&g__ * angle.sin()).pow(&p_), recursive)
        },
    ));
}

fn push_rules_rule_3441(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3441,
        source: "Int[(g_.*csc[e_.+f_.*x_])^p_.*(a_+b_.*sin[e_.+f_.*x_])^m_.*(c_+d_.*csc[e_.+f_.*x_])^n_.,x_Symbol] :=
          g^m \\[Star] Int[(g*Csc[e+f*x])^(p-m)*(b+a*Csc[e+f*x])^m*(c+d*Csc[e+f*x])^n,x] /;
        FreeQ[{a,b,c,d,e,f,g,n,p},x] && IntegerQ[m]",
        desc: "Algebraic normalization",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [g__, e__, f__, p_, a__, b__, m_, c__, d__, n_, x_],
        optional: [g__, e__, f__, p_, b__, m_, d__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, n_, p_], x_)
                && integerq!(m_)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let recursive = rubi_rhs_int(
                &((&g__ * angle.csc()).pow(&p_ - &m_)
                    * (&b__ + &a__ * angle.csc()).pow(&m_)
                    * (&c__ + &d__ * angle.csc()).pow(&n_)),
                x_,
            );

            rubi_star(g__.pow(&m_), recursive)
        },
    ));
}

fn push_rules_rule_3442(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3442,
        source: "Int[csc[e_.+f_.*x_]^p_.*(a_+b_.*sin[e_.+f_.*x_])^m_*(c_+d_.*csc[e_.+f_.*x_])^n_.,x_Symbol] :=
          Int[(a+b*Sin[e+f*x])^m*(d+c*Sin[e+f*x])^n/Sin[e+f*x]^(n+p),x] /;
        FreeQ[{a,b,c,d,e,f,m},x] && Not[IntegerQ[m]] && IntegerQ[n] && IntegerQ[p]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: i_csc(e__ + f__ * x_).pow(p_)
            * (a__ + b__ * i_sin(e__ + f__ * x_)).pow(m_)
            * (c__ + d__ * i_csc(e__ + f__ * x_)).pow(n_),
        with: [e__, f__, p_, a__, b__, m_, c__, d__, n_, x_],
        optional: [e__, f__, p_, b__, d__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_], x_)
                && !integerq!(m_)
                && integerq!(n_)
                && integerq!(p_)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;

            rubi_rhs_int(
                &((&a__ + &b__ * angle.sin()).pow(&m_)
                    * (&d__ + &c__ * angle.sin()).pow(&n_)
                    / angle.sin().pow(&n_ + &p_)),
                x_,
            )
        },
    ));
}

fn push_rules_rule_3443(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3443,
        source: "Int[(g_.*csc[e_.+f_.*x_])^p_*(a_+b_.*sin[e_.+f_.*x_])^m_*(c_+d_.*csc[e_.+f_.*x_])^n_.,x_Symbol] :=
          Sin[e+f*x]^p*(g*Csc[e+f*x])^p \\[Star] Int[(a+b*Sin[e+f*x])^m*(d+c*Sin[e+f*x])^n/Sin[e+f*x]^(n+p),x] /;
        FreeQ[{a,b,c,d,e,f,g,m,p},x] && Not[IntegerQ[m]] && IntegerQ[n] && Not[IntegerQ[p]]",
        desc: "Algebraic normalization and piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [g__, e__, f__, p_, a__, b__, m_, c__, d__, n_, x_],
        optional: [g__, e__, f__, b__, d__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, m_, p_], x_)
                && !integerq!(m_)
                && integerq!(n_)
                && !integerq!(p_)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let recursive = rubi_rhs_int(
                &((&a__ + &b__ * angle.sin()).pow(&m_)
                    * (&d__ + &c__ * angle.sin()).pow(&n_)
                    / angle.sin().pow(&n_ + &p_)),
                x_,
            );

            rubi_star(angle.sin().pow(&p_) * (&g__ * angle.csc()).pow(&p_), recursive)
        },
    ));
}

fn push_rules_rule_3444(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3444,
        source: "Int[(g_.*csc[e_.+f_.*x_])^p_.*(a_+b_.*sin[e_.+f_.*x_])^m_*(c_+d_.*csc[e_.+f_.*x_])^n_,x_Symbol] :=
          (a+b*Sin[e+f*x])^m*(g*Csc[e+f*x])^m/(b+a*Csc[e+f*x])^m \\[Star]
            Int[(g*Csc[e+f*x])^(p-m)*(b+a*Csc[e+f*x])^m*(c+d*Csc[e+f*x])^n,x] /;
        FreeQ[{a,b,c,d,e,f,g,m,n,p},x] && Not[IntegerQ[m]] && Not[IntegerQ[n]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [g__, e__, f__, p_, a__, b__, m_, c__, d__, n_, x_],
        optional: [g__, e__, f__, p_, b__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, m_, n_, p_], x_)
                && !integerq!(m_)
                && !integerq!(n_)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let recursive = rubi_rhs_int(
                &((&g__ * angle.csc()).pow(&p_ - &m_)
                    * (&b__ + &a__ * angle.csc()).pow(&m_)
                    * (&c__ + &d__ * angle.csc()).pow(&n_)),
                x_,
            );

            rubi_star((&a__ + &b__ * angle.sin()).pow(&m_)
                    * (&g__ * angle.csc()).pow(&m_)
                    / (&b__ + &a__ * angle.csc()).pow(&m_), recursive)
        },
    ));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn downvalues_3407_through_3442_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .filter(|order| (3407..=3442).contains(order))
            .collect::<Vec<_>>();
        assert_eq!(orders, (3407..=3442).collect::<Vec<_>>());
    }

    #[test]
    fn downvalues_3443_through_3444_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .filter(|order| (3443..=3444).contains(order))
            .collect::<Vec<_>>();
        assert_eq!(orders, (3443..=3444).collect::<Vec<_>>());
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
    let x_ = symbols.x_;
    (a__ + b__ * i_sin(e__ + f__ * x_)).sqrt() * (c__ + d__ * i_sin(e__ + f__ * x_)).sqrt()
        / i_sin(e__ + f__ * x_)
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let g__ = symbols.g__;
    let x_ = symbols.x_;
    (a__ + b__ * i_sin(e__ + f__ * x_)).sqrt()
        / ((g__ * i_sin(e__ + f__ * x_)).sqrt() * (c__ + d__ * i_sin(e__ + f__ * x_)))
}

#[inline(never)]
fn rubi_shared_pattern_2(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let x_ = symbols.x_;
    (a__ + b__ * i_sin(e__ + f__ * x_)).sqrt()
        / (i_sin(e__ + f__ * x_) * (c__ + d__ * i_sin(e__ + f__ * x_)))
}

#[inline(never)]
fn rubi_shared_pattern_3(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let x_ = symbols.x_;
    (a__ + b__ * i_sin(e__ + f__ * x_)).sqrt()
        / (i_sin(e__ + f__ * x_) * (c__ + d__ * i_sin(e__ + f__ * x_)).sqrt())
}

#[inline(never)]
fn rubi_shared_pattern_4(symbols: &RubiSymbols) -> Atom {
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
    (g__ * i_csc(e__ + f__ * x_)).pow(p_)
        * (a__ + b__ * i_sin(e__ + f__ * x_)).pow(m_)
        * (c__ + d__ * i_csc(e__ + f__ * x_)).pow(n_)
}

#[inline(never)]
fn rubi_shared_pattern_5(symbols: &RubiSymbols) -> Atom {
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
    (g__ * i_csc(e__ + f__ * x_)).pow(p_)
        * (a__ + b__ * i_sin(e__ + f__ * x_)).pow(m_)
        * (c__ + d__ * i_sin(e__ + f__ * x_)).pow(n_)
}

#[inline(never)]
fn rubi_shared_pattern_6(symbols: &RubiSymbols) -> Atom {
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
    (g__ * i_sin(e__ + f__ * x_)).pow(p_)
        * (a__ + b__ * i_csc(e__ + f__ * x_)).pow(m_)
        * (c__ + d__ * i_csc(e__ + f__ * x_)).pow(n_)
}

#[inline(never)]
fn rubi_shared_pattern_7(symbols: &RubiSymbols) -> Atom {
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
    (g__ * i_sin(e__ + f__ * x_)).pow(p_)
        * (a__ + b__ * i_sin(e__ + f__ * x_)).pow(m_)
        * (c__ + d__ * i_csc(e__ + f__ * x_)).pow(n_)
}

#[inline(never)]
fn rubi_shared_pattern_8(symbols: &RubiSymbols) -> Atom {
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
    (g__ * i_sin(e__ + f__ * x_)).pow(p_)
        * (a__ + b__ * i_sin(e__ + f__ * x_)).pow(m_)
        * (c__ + d__ * i_sin(e__ + f__ * x_)).pow(n_)
}

#[inline(never)]
fn rubi_shared_pattern_9(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let g__ = symbols.g__;
    let x_ = symbols.x_;
    (g__ * i_sin(e__ + f__ * x_)).sqrt() * (a__ + b__ * i_sin(e__ + f__ * x_)).sqrt()
        / (c__ + d__ * i_sin(e__ + f__ * x_))
}

#[inline(never)]
fn rubi_shared_pattern_10(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let g__ = symbols.g__;
    let x_ = symbols.x_;
    (g__ * i_sin(e__ + f__ * x_)).sqrt()
        / ((a__ + b__ * i_sin(e__ + f__ * x_)).sqrt() * (c__ + d__ * i_sin(e__ + f__ * x_)))
}

#[inline(never)]
fn rubi_shared_pattern_11(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let g__ = symbols.g__;
    let x_ = symbols.x_;
    Atom::num(1)
        / ((g__ * i_sin(e__ + f__ * x_)).sqrt()
            * (a__ + b__ * i_sin(e__ + f__ * x_)).sqrt()
            * (c__ + d__ * i_sin(e__ + f__ * x_)))
}

#[inline(never)]
fn rubi_shared_pattern_12(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let x_ = symbols.x_;
    Atom::num(1)
        / (i_sin(e__ + f__ * x_)
            * (a__ + b__ * i_sin(e__ + f__ * x_)).sqrt()
            * (c__ + d__ * i_sin(e__ + f__ * x_)))
}

#[inline(never)]
fn rubi_shared_pattern_13(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let x_ = symbols.x_;
    Atom::num(1)
        / (i_sin(e__ + f__ * x_)
            * (a__ + b__ * i_sin(e__ + f__ * x_)).sqrt()
            * (c__ + d__ * i_sin(e__ + f__ * x_)).sqrt())
}
