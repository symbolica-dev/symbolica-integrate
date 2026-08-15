use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_3648(rules);
    push_rules_rule_3649(rules);
    push_rules_rule_3650(rules);
    push_rules_rule_3651(rules);
    push_rules_rule_3652(rules);
    push_rules_rule_3653(rules);
    push_rules_rule_3654(rules);
    push_rules_rule_3655(rules);
    push_rules_rule_3656(rules);
    push_rules_rule_3657(rules);
    push_rules_rule_3658(rules);
    push_rules_rule_3659(rules);
    push_rules_rule_3660(rules);
    push_rules_rule_3661(rules);
    push_rules_rule_3662(rules);
    push_rules_rule_3663(rules);
    push_rules_rule_3664(rules);
    push_rules_rule_3665(rules);
    push_rules_rule_3666(rules);
    push_rules_rule_3667(rules);
    push_rules_rule_3668(rules);
    push_rules_rule_3669(rules);
    push_rules_rule_3670(rules);
    push_rules_rule_3671(rules);
    push_rules_rule_3672(rules);
    push_rules_rule_3673(rules);
    push_rules_rule_3674(rules);
    push_rules_rule_3675(rules);
    push_rules_rule_3676(rules);
    push_rules_rule_3677(rules);
    push_rules_rule_3678(rules);
    push_rules_rule_3679(rules);
    push_rules_rule_3680(rules);
    push_rules_rule_3681(rules);
    push_rules_rule_3682(rules);
    push_rules_rule_3683(rules);
    push_rules_rule_3684(rules);
    push_rules_rule_3685(rules);
    push_rules_rule_3686(rules);
    push_rules_rule_3687(rules);
    push_rules_rule_3688(rules);
    push_rules_rule_3689(rules);
    push_rules_rule_3690(rules);
    push_rules_rule_3691(rules);
    push_rules_rule_3692(rules);
    push_rules_rule_3693(rules);
    push_rules_rule_3694(rules);
    push_rules_rule_3695(rules);
    push_rules_rule_3696(rules);
    push_rules_rule_3697(rules);
    push_rules_rule_3698(rules);
    push_rules_rule_3699(rules);
    push_rules_rule_3700(rules);
    push_rules_rule_3701(rules);
    push_rules_rule_3702(rules);
    push_rules_rule_3703(rules);
    push_rules_rule_3704(rules);
    push_rules_rule_3705(rules);
    push_rules_rule_3706(rules);
    push_rules_rule_3707(rules);
    push_rules_rule_3708(rules);
    push_rules_rule_3709(rules);
    push_rules_rule_3710(rules);
    push_rules_rule_3711(rules);
    push_rules_rule_3712(rules);
    push_rules_rule_3713(rules);
    push_rules_rule_3714(rules);
    push_rules_rule_3715(rules);
    push_rules_rule_3716(rules);
    push_rules_rule_3717(rules);
    push_rules_rule_3718(rules);
    push_rules_rule_3719(rules);
    push_rules_rule_3720(rules);
}

fn push_rules_rule_3648(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_a__, capital_b__, a__, b__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 3648,
        source: "Int[(a_+b_.*sin[e_.+f_.*x_]^2)*(A_.+B_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
          (4*A*(2*a+b)+B*(4*a+3*b))*x/8 -
          (4*A*b+B*(4*a+3*b))*Cos[e+f*x]*Sin[e+f*x]/(8*f) -
          b*B*Cos[e+f*x]*Sin[e+f*x]^3/(4*f) /;
        FreeQ[{a,b,e,f,A,B},x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (a__ + b__ * i_sin(e__ + f__ * x_).pow(2))
            * (capital_a__ + capital_b__ * i_sin(e__ + f__ * x_).pow(2)),
        with: [a__, b__, e__, f__, capital_a__, capital_b__, x_],
        optional: [b__, e__, f__, capital_a__, capital_b__],
        when: { freeq!([a__, b__, e__, f__, capital_a__, capital_b__], x_) },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let cos = angle.cos();

            rubi_simp(&((Atom::num(4) * &capital_a__ * (Atom::num(2) * &a__ + &b__)
                    + &capital_b__ * (Atom::num(4) * &a__ + Atom::num(3) * &b__))
                    * x_
                    / 8), x_)
                    - rubi_simp(&((Atom::num(4) * &capital_a__ * &b__
                        + &capital_b__ * (Atom::num(4) * &a__ + Atom::num(3) * &b__))
                        * &cos
                        * &sin
                        / (Atom::num(8) * &f__)), x_)
                    - rubi_simp(&(&b__ * &capital_b__ * cos * sin.pow(3) / (Atom::num(4) * &f__)), x_)
        },
    ));
}

fn push_rules_rule_3649(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_a__, capital_b__, a__, b__, e__, f__, p_, x_);
    rules.push(rubi_rule!(
        order: 3649,
        source: "Int[(a_+b_.*sin[e_.+f_.*x_]^2)^p_*(A_.+B_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
          -B*Cos[e+f*x]*Sin[e+f*x]*(a+b*Sin[e+f*x]^2)^p/(2*f*(p+1)) +
          1/(2*(p+1)) \\[Star] Int[(a+b*Sin[e+f*x]^2)^(p-1)*
            Simp[a*B+2*a*A*(p+1)+(2*A*b*(p+1)+B*(b+2*a*p+2*b*p))*Sin[e+f*x]^2,x],x] /;
        FreeQ[{a,b,e,f,A,B},x] && GtQ[p,0]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, e__, f__, p_, capital_a__, capital_b__, x_],
        optional: [b__, e__, f__, capital_a__, capital_b__],
        when: {
            freeq!([a__, b__, e__, f__, capital_a__, capital_b__], x_)
                && gtq!(p_, 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let cos = angle.cos();
            let base = &a__ + &b__ * sin.pow(2);
            let p1 = &p_ + 1;
            let payload = rubi_simp(&(&a__ * &capital_b__
                    + Atom::num(2) * &a__ * &capital_a__ * &p1
                    + (Atom::num(2) * &capital_a__ * &b__ * &p1
                        + &capital_b__ * (&b__ + Atom::num(2) * &a__ * &p_ + Atom::num(2) * &b__ * &p_))
                        * sin.pow(2)), x_);
            let recursive = rubi_rhs_int(&(base.pow(&p_ - 1) * payload), x_);

            rubi_simp(&(-&capital_b__ * cos * sin * base.pow(&p_) / (Atom::num(2) * &f__ * &p1)), x_)
                    + rubi_star(Atom::num(1) / (Atom::num(2) * &p1), recursive)
        },
    ));
}

fn push_rules_rule_3650(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_a__, capital_b__, a__, b__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 3650,
        source: "Int[(A_.+B_.*sin[e_.+f_.*x_]^2)/(a_+b_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
          B*x/b + (A*b-a*B)/b \\[Star] Int[1/(a+b*Sin[e+f*x]^2),x] /;
        FreeQ[{a,b,e,f,A,B},x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (capital_a__ + capital_b__ * i_sin(e__ + f__ * x_).pow(2))
            / (a__ + b__ * i_sin(e__ + f__ * x_).pow(2)),
        with: [a__, b__, e__, f__, capital_a__, capital_b__, x_],
        optional: [b__, e__, f__, capital_a__, capital_b__],
        when: { freeq!([a__, b__, e__, f__, capital_a__, capital_b__], x_) },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let base = &a__ + &b__ * angle.sin().pow(2);
            let recursive = rubi_rhs_int(&(Atom::num(1) / base), x_);

            rubi_simp(&(&capital_b__ * x_ / &b__), x_)
                    + rubi_star((&capital_a__ * &b__ - &a__ * &capital_b__) / &b__, recursive)
        },
    ));
}

fn push_rules_rule_3651(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_a__, capital_b__, a__, b__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 3651,
        source: "Int[(A_.+B_.*sin[e_.+f_.*x_]^2)/Sqrt[a_+b_.*sin[e_.+f_.*x_]^2],x_Symbol] :=
          B/b \\[Star] Int[Sqrt[a+b*Sin[e+f*x]^2],x] + (A*b-a*B)/b \\[Star] Int[1/Sqrt[a+b*Sin[e+f*x]^2],x] /;
        FreeQ[{a,b,e,f,A,B},x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (capital_a__ + capital_b__ * i_sin(e__ + f__ * x_).pow(2))
            / (a__ + b__ * i_sin(e__ + f__ * x_).pow(2)).sqrt(),
        with: [a__, b__, e__, f__, capital_a__, capital_b__, x_],
        optional: [b__, e__, f__, capital_a__, capital_b__],
        when: { freeq!([a__, b__, e__, f__, capital_a__, capital_b__], x_) },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let base = &a__ + &b__ * angle.sin().pow(2);
            let recursive1 = rubi_rhs_int(&base.sqrt(), x_);
            let recursive2 = rubi_rhs_int(&(Atom::num(1) / base.sqrt()), x_);

            rubi_star(&capital_b__ / &b__, recursive1)
                    + rubi_star((&capital_a__ * &b__ - &a__ * &capital_b__) / &b__, recursive2)
        },
    ));
}

fn push_rules_rule_3652(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_a__, capital_b__, a__, b__, e__, f__, p_, x_);
    rules.push(rubi_rule!(
        order: 3652,
        source: "Int[(a_+b_.*sin[e_.+f_.*x_]^2)^p_*(A_.+B_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
          -(A*b-a*B)*Cos[e+f*x]*Sin[e+f*x]*(a+b*Sin[e+f*x]^2)^(p+1)/(2*a*f*(a+b)*(p+1)) -
          1/(2*a*(a+b)*(p+1)) \\[Star] Int[(a+b*Sin[e+f*x]^2)^(p+1)*
            Simp[a*B-A*(2*a*(p+1)+b*(2*p+3))+2*(A*b-a*B)*(p+2)*Sin[e+f*x]^2,x],x] /;
        FreeQ[{a,b,e,f,A,B},x] && LtQ[p,-1] && NeQ[a+b,0]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, e__, f__, p_, capital_a__, capital_b__, x_],
        optional: [b__, e__, f__, capital_a__, capital_b__],
        when: {
            freeq!([a__, b__, e__, f__, capital_a__, capital_b__], x_)
                && ltq!(p_, -1)
                && neq!(&a__ + &b__, 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let cos = angle.cos();
            let base = &a__ + &b__ * sin.pow(2);
            let p1 = &p_ + 1;
            let payload = rubi_simp(&(&a__ * &capital_b__
                    - &capital_a__ * (Atom::num(2) * &a__ * &p1 + &b__ * (Atom::num(2) * &p_ + 3))
                    + Atom::num(2) * (&capital_a__ * &b__ - &a__ * &capital_b__) * (&p_ + 2) * sin.pow(2)), x_);
            let recursive = rubi_rhs_int(&(base.pow(&p1) * payload), x_);

            rubi_simp(&(-(&capital_a__ * &b__ - &a__ * &capital_b__) * cos * sin * base.pow(&p1)
                    / (Atom::num(2) * &a__ * &f__ * (&a__ + &b__) * &p1)), x_)
                    - rubi_star(Atom::num(1)
                            / (Atom::num(2) * &a__ * (&a__ + &b__) * &p1), recursive)
        },
    ));
}

fn push_rules_rule_3653(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_a__, capital_b__, a__, b__, e__, f__, p_, x_);
    rules.push(rubi_rule!(
        order: 3653,
        source: "Int[(a_.+b_.*sin[e_.+f_.*x_]^2)^p_*(A_.+B_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
          With[{ff=FreeFactors[Tan[e+f*x],x]},
          ff*(a+b*Sin[e+f*x]^2)^p*(Sec[e+f*x]^2)^p/(f*(a+(a+b)*Tan[e+f*x]^2)^p) \\[Star]
            Subst[Int[(a+(a+b)*ff^2*x^2)^p*(A+(A+B)*ff^2*x^2)/(1+ff^2*x^2)^(p+2),x],x,Tan[e+f*x]/ff]] /;
        FreeQ[{a,b,e,f,A,B},x] && Not[IntegerQ[p]]",
        desc: "Piecewise constant extraction and integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, e__, f__, p_, capital_a__, capital_b__, x_],
        optional: [a__, b__, e__, f__, capital_a__, capital_b__],
        when: {
            freeq!([a__, b__, e__, f__, capital_a__, capital_b__], x_)
                && !integerq!(p_)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let z = Atom::var(sub);
            let angle = &e__ + &f__ * x_;
            let ff = rubi_free_factors(&angle.tan(), x_);
            let sin = angle.sin();
            let tan = angle.tan();
            let transformed = (&a__ + (&a__ + &b__) * ff.pow(2) * z.pow(2)).pow(&p_)
                * (&capital_a__ + (&capital_a__ + &capital_b__) * ff.pow(2) * z.pow(2))
                / (Atom::num(1) + ff.pow(2) * z.pow(2)).pow(&p_ + 2);
            let primitive = rubi_rhs_int(&transformed, sub);
            let denominator = (&a__ + (&a__ + &b__) * tan.pow(2)).pow(&p_);

            rubi_star(&ff * (&a__ + &b__ * sin.pow(2)).pow(&p_) * angle.sec().pow(2).pow(&p_)
                    / (&f__ * denominator), rubi_subst(&primitive, sub, tan / &ff))
        },
    ));
}

fn push_rules_rule_3654(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, e__, f__, p_, u__, x_);
    rules.push(rubi_rule!(
        order: 3654,
        source: "Int[u_.*(a_+b_.*sin[e_.+f_.*x_]^2)^p_,x_Symbol] :=
          a^p \\[Star] Int[ActivateTrig[u*cos[e+f*x]^(2*p)],x] /;
        FreeQ[{a,b,e,f,p},x] && EqQ[a+b,0] && IntegerQ[p]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_19(symbols),
        with: [u__, a__, b__, e__, f__, p_, x_],
        optional: [u__, b__, e__, f__],
        when: {
            freeq!([a__, b__, e__, f__, p_], x_)
                && eqq!(&a__ + &b__, 0)
                && integerq!(p_)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let payload = &u__ * i_cos(&angle).pow(Atom::num(2) * &p_);
            let recursive = rubi_rhs_int(&payload, x_);

            rubi_star(a__.pow(&p_), recursive)
        },
    ));
}

fn push_rules_rule_3655(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, e__, f__, p_, u__, x_);
    rules.push(rubi_rule!(
        order: 3655,
        source: "Int[u_.*(a_+b_.*sin[e_.+f_.*x_]^2)^p_,x_Symbol] :=
          Int[ActivateTrig[u*(a*cos[e+f*x]^2)^p],x] /;
        FreeQ[{a,b,e,f,p},x] && EqQ[a+b,0]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_19(symbols),
        with: [u__, a__, b__, e__, f__, p_, x_],
        optional: [u__, b__, e__, f__],
        when: {
            freeq!([a__, b__, e__, f__, p_], x_)
                && eqq!(&a__ + &b__, 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let payload = &u__ * (&a__ * i_cos(&angle).pow(2)).pow(&p_);

            rubi_rhs_int(&payload, x_)
        },
    ));
}

fn push_rules_rule_3656(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 3656,
        source: "Int[Sqrt[a_+b_.*sin[e_.+f_.*x_]^2],x_Symbol] :=
          Sqrt[a]/f*EllipticE[e+f*x,-b/a] /;
        FreeQ[{a,b,e,f},x] && GtQ[a,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, b__, e__, f__, x_],
        optional: [b__, e__, f__],
        when: {
            freeq!([a__, b__, e__, f__], x_)
                && gtq!(a__, 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;

            rubi_simp(&(a__.sqrt() * rubi_elliptic_e(angle, -&b__ / &a__) / &f__), x_)
        },
    ));
}

fn push_rules_rule_3657(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 3657,
        source: "Int[Sqrt[a_+b_.*sin[e_.+f_.*x_]^2],x_Symbol] :=
          Sqrt[a+b*Sin[e+f*x]^2]/Sqrt[1+b*Sin[e+f*x]^2/a] \\[Star] Int[Sqrt[1+(b*Sin[e+f*x]^2)/a],x] /;
        FreeQ[{a,b,e,f},x] && Not[GtQ[a,0]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, b__, e__, f__, x_],
        optional: [b__, e__, f__],
        when: {
            freeq!([a__, b__, e__, f__], x_)
                && !gtq!(a__, 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin_squared = angle.sin().pow(2);
            let base = &a__ + &b__ * &sin_squared;
            let normalized = Atom::num(1) + &b__ * sin_squared / &a__;
            let recursive = rubi_rhs_int(&normalized.sqrt(), x_);

            rubi_star(base.sqrt() / normalized.sqrt(), recursive)
        },
    ));
}

fn push_rules_rule_3658(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 3658,
        source: "Int[(a_+b_.*sin[e_.+f_.*x_]^2)^2,x_Symbol] :=
          (8*a^2+8*a*b+3*b^2)*x/8 -
          b*(8*a+3*b)*Cos[e+f*x]*Sin[e+f*x]/(8*f) -
          b^2*Cos[e+f*x]*Sin[e+f*x]^3/(4*f) /;
        FreeQ[{a,b,e,f},x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (a__ + b__ * i_sin(e__ + f__ * x_).pow(2)).pow(2),
        with: [a__, b__, e__, f__, x_],
        optional: [b__, e__, f__],
        when: { freeq!([a__, b__, e__, f__], x_) },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let cos = angle.cos();

            rubi_simp(&((Atom::num(8) * a__.pow(2) + Atom::num(8) * &a__ * &b__ + Atom::num(3) * b__.pow(2)) * x_
                    / 8), x_)
                    - rubi_simp(&(&b__ * (Atom::num(8) * &a__ + Atom::num(3) * &b__) * &cos * &sin
                        / (Atom::num(8) * &f__)), x_)
                    - rubi_simp(&(b__.pow(2) * cos * sin.pow(3) / (Atom::num(4) * &f__)), x_)
        },
    ));
}

fn push_rules_rule_3659(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, e__, f__, p_, x_);
    rules.push(rubi_rule!(
        order: 3659,
        source: "Int[(a_+b_.*sin[e_.+f_.*x_]^2)^p_,x_Symbol] :=
          -b*Cos[e+f*x]*Sin[e+f*x]*(a+b*Sin[e+f*x]^2)^(p-1)/(2*f*p) +
          1/(2*p) \\[Star] Int[(a+b*Sin[e+f*x]^2)^(p-2)*Simp[a*(b+2*a*p)+b*(2*a+b)*(2*p-1)*Sin[e+f*x]^2,x],x] /;
        FreeQ[{a,b,e,f},x] && NeQ[a+b,0] && GtQ[p,1]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, e__, f__, p_, x_],
        optional: [b__, e__, f__],
        when: {
            freeq!([a__, b__, e__, f__], x_)
                && neq!(&a__ + &b__, 0)
                && gtq!(p_, 1)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let cos = angle.cos();
            let base = &a__ + &b__ * sin.pow(2);
            let payload = rubi_simp(&(&a__ * (&b__ + Atom::num(2) * &a__ * &p_)
                    + &b__ * (Atom::num(2) * &a__ + &b__) * (Atom::num(2) * &p_ - 1) * sin.pow(2)), x_);
            let recursive = rubi_rhs_int(&(base.pow(&p_ - 2) * payload), x_);

            rubi_simp(&(-&b__ * cos * sin * base.pow(&p_ - 1) / (Atom::num(2) * &f__ * &p_)), x_)
                    + rubi_star(Atom::num(1) / (Atom::num(2) * &p_), recursive)
        },
    ));
}

fn push_rules_rule_3660(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 3660,
        source: "Int[1/(a_+b_.*sin[e_.+f_.*x_]^2),x_Symbol] :=
          With[{ff=FreeFactors[Tan[e+f*x],x]},
          ff/f \\[Star] Subst[Int[1/(a+(a+b)*ff^2*x^2),x],x,Tan[e+f*x]/ff]] /;
        FreeQ[{a,b,e,f},x]",
        desc: "Integration by substitution",
        refs: [],
        pattern: Atom::num(1) / (a__ + b__ * i_sin(e__ + f__ * x_).pow(2)),
        with: [a__, b__, e__, f__, x_],
        optional: [b__, e__, f__],
        when: { freeq!([a__, b__, e__, f__], x_) },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let z = Atom::var(sub);
            let angle = &e__ + &f__ * x_;
            let tan = angle.tan();
            let ff = rubi_free_factors(&tan, x_);
            let transformed = Atom::num(1) / (&a__ + (&a__ + &b__) * ff.pow(2) * z.pow(2));
            let primitive = rubi_rhs_int(&transformed, sub);

            rubi_star(&ff / &f__, rubi_subst(&primitive, sub, tan / &ff))
        },
    ));
}

fn push_rules_rule_3661(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 3661,
        source: "Int[1/Sqrt[a_+b_.*sin[e_.+f_.*x_]^2],x_Symbol] :=
          1/(Sqrt[a]*f)*EllipticF[e+f*x,-b/a] /;
        FreeQ[{a,b,e,f},x] && GtQ[a,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_12(symbols),
        with: [a__, b__, e__, f__, x_],
        optional: [b__, e__, f__],
        when: {
            freeq!([a__, b__, e__, f__], x_)
                && gtq!(a__, 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;

            rubi_simp(&(rubi_elliptic_f(angle, -&b__ / &a__) / (a__.sqrt() * &f__)), x_)
        },
    ));
}

fn push_rules_rule_3662(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 3662,
        source: "Int[1/Sqrt[a_+b_.*sin[e_.+f_.*x_]^2],x_Symbol] :=
          Sqrt[1+b*Sin[e+f*x]^2/a]/Sqrt[a+b*Sin[e+f*x]^2] \\[Star] Int[1/Sqrt[1+(b*Sin[e+f*x]^2)/a],x] /;
        FreeQ[{a,b,e,f},x] && Not[GtQ[a,0]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_12(symbols),
        with: [a__, b__, e__, f__, x_],
        optional: [b__, e__, f__],
        when: {
            freeq!([a__, b__, e__, f__], x_)
                && !gtq!(a__, 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin_squared = angle.sin().pow(2);
            let base = &a__ + &b__ * &sin_squared;
            let normalized = Atom::num(1) + &b__ * sin_squared / &a__;
            let recursive = rubi_rhs_int(&(Atom::num(1) / normalized.sqrt()), x_);

            rubi_star(normalized.sqrt() / base.sqrt(), recursive)
        },
    ));
}

fn push_rules_rule_3663(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, e__, f__, p_, x_);
    rules.push(rubi_rule!(
        order: 3663,
        source: "Int[(a_+b_.*sin[e_.+f_.*x_]^2)^p_,x_Symbol] :=
          -b*Cos[e+f*x]*Sin[e+f*x]*(a+b*Sin[e+f*x]^2)^(p+1)/(2*a*f*(p+1)*(a+b)) +
          1/(2*a*(p+1)*(a+b)) \\[Star] Int[(a+b*Sin[e+f*x]^2)^(p+1)*Simp[2*a*(p+1)+b*(2*p+3)-2*b*(p+2)*Sin[e+f*x]^2,x],x] /;
        FreeQ[{a,b,e,f},x] && NeQ[a+b,0] && LtQ[p,-1]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, e__, f__, p_, x_],
        optional: [b__, e__, f__],
        when: {
            freeq!([a__, b__, e__, f__], x_)
                && neq!(&a__ + &b__, 0)
                && ltq!(p_, -1)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let cos = angle.cos();
            let base = &a__ + &b__ * sin.pow(2);
            let p1 = &p_ + 1;
            let payload = rubi_simp(&(Atom::num(2) * &a__ * &p1
                    + &b__ * (Atom::num(2) * &p_ + 3)
                    - Atom::num(2) * &b__ * (&p_ + 2) * sin.pow(2)), x_);
            let recursive = rubi_rhs_int(&(base.pow(&p1) * payload), x_);

            rubi_simp(&(-&b__ * cos * sin * base.pow(&p1)
                    / (Atom::num(2) * &a__ * &f__ * &p1 * (&a__ + &b__))), x_)
                    + rubi_star(Atom::num(1)
                            / (Atom::num(2) * &a__ * &p1 * (&a__ + &b__)), recursive)
        },
    ));
}

fn push_rules_rule_3664(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, e__, f__, p_, x_);
    rules.push(rubi_rule!(
        order: 3664,
        source: "Int[(a_+b_.*sin[e_.+f_.*x_]^2)^p_.,x_Symbol] :=
          With[{ff=FreeFactors[Sin[e+f*x],x]},
          ff*Sqrt[Cos[e+f*x]^2]/(f*Cos[e+f*x]) \\[Star] Subst[Int[(a+b*ff^2*x^2)^p/Sqrt[1-ff^2*x^2],x],x,Sin[e+f*x]/ff]] /;
        FreeQ[{a,b,e,f,p},x] && Not[IntegerQ[p]]",
        desc: "Piecewise constant extraction and integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, e__, f__, p_, x_],
        optional: [b__, e__, f__, p_],
        when: {
            freeq!([a__, b__, e__, f__, p_], x_)
                && !integerq!(p_)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let z = Atom::var(sub);
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let cos = angle.cos();
            let ff = rubi_free_factors(&sin, x_);
            let transformed = (&a__ + &b__ * ff.pow(2) * z.pow(2)).pow(&p_)
                / (Atom::num(1) - ff.pow(2) * z.pow(2)).sqrt();
            let primitive = rubi_rhs_int(&transformed, sub);

            rubi_star(&ff * cos.pow(2).sqrt()
                    / (&f__ * cos), rubi_subst(&primitive, sub, sin / &ff))
        },
    ));
}

fn push_rules_rule_3665(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, e__, f__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 3665,
        source: "Int[sin[e_.+f_.*x_]^m_.*(a_+b_.*sin[e_.+f_.*x_]^2)^p_.,x_Symbol] :=
          With[{ff=FreeFactors[Cos[e+f*x],x]},
          -ff/f \\[Star] Subst[Int[(1-ff^2*x^2)^((m-1)/2)*(a+b-b*ff^2*x^2)^p,x],x,Cos[e+f*x]/ff]] /;
        FreeQ[{a,b,e,f,p},x] && IntegerQ[(m-1)/2]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_15(symbols),
        with: [a__, b__, e__, f__, m_, p_, x_],
        optional: [b__, e__, f__, m_, p_],
        when: {
            freeq!([a__, b__, e__, f__, p_], x_)
                && integerq!((&m_ - 1) / 2)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let z = Atom::var(sub);
            let angle = &e__ + &f__ * x_;
            let cos = angle.cos();
            let ff = rubi_free_factors(&cos, x_);
            let transformed = (Atom::num(1) - ff.pow(2) * z.pow(2)).pow((&m_ - 1) / 2)
                * (&a__ + &b__ - &b__ * ff.pow(2) * z.pow(2)).pow(&p_);
            let primitive = rubi_rhs_int(&transformed, sub);

            rubi_star(-&ff / &f__, rubi_subst(&primitive, sub, cos / &ff))
        },
    ));
}

fn push_rules_rule_3666(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, e__, f__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 3666,
        source: "Int[sin[e_.+f_.*x_]^m_*(a_+b_.*sin[e_.+f_.*x_]^2)^p_.,x_Symbol] :=
          With[{ff=FreeFactors[Tan[e+f*x],x]},
          ff^(m+1)/f \\[Star] Subst[Int[x^m*(a+(a+b)*ff^2*x^2)^p/(1+ff^2*x^2)^(m/2+p+1),x],x,Tan[e+f*x]/ff]] /;
        FreeQ[{a,b,e,f},x] && IntegerQ[m/2] && IntegerQ[p]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_15(symbols),
        with: [a__, b__, e__, f__, m_, p_, x_],
        optional: [b__, e__, f__, p_],
        when: {
            freeq!([a__, b__, e__, f__], x_)
                && integerq!(&m_ / 2)
                && integerq!(p_)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let z = Atom::var(sub);
            let angle = &e__ + &f__ * x_;
            let tan = angle.tan();
            let ff = rubi_free_factors(&tan, x_);
            let transformed = z.pow(&m_) * (&a__ + (&a__ + &b__) * ff.pow(2) * z.pow(2)).pow(&p_)
                / (Atom::num(1) + ff.pow(2) * z.pow(2)).pow(&m_ / 2 + &p_ + 1);
            let primitive = rubi_rhs_int(&transformed, sub);

            rubi_star(ff.pow(&m_ + 1) / &f__, rubi_subst(&primitive, sub, tan / &ff))
        },
    ));
}

fn push_rules_rule_3667(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, e__, f__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 3667,
        source: "Int[sin[e_.+f_.*x_]^m_*(a_+b_.*sin[e_.+f_.*x_]^2)^p_.,x_Symbol] :=
          With[{ff=FreeFactors[Sin[e+f*x],x]},
          ff^(m+1)*Sqrt[Cos[e+f*x]^2]/(f*Cos[e+f*x]) \\[Star] Subst[Int[x^m*(a+b*ff^2*x^2)^p/Sqrt[1-ff^2*x^2],x],x,Sin[e+f*x]/ff]] /;
        FreeQ[{a,b,e,f,p},x] && IntegerQ[m/2] && Not[IntegerQ[p]]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_15(symbols),
        with: [a__, b__, e__, f__, m_, p_, x_],
        optional: [b__, e__, f__, p_],
        when: {
            freeq!([a__, b__, e__, f__, p_], x_)
                && integerq!(&m_ / 2)
                && !integerq!(p_)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let z = Atom::var(sub);
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let cos = angle.cos();
            let ff = rubi_free_factors(&sin, x_);
            let transformed = z.pow(&m_) * (&a__ + &b__ * ff.pow(2) * z.pow(2)).pow(&p_)
                / (Atom::num(1) - ff.pow(2) * z.pow(2)).sqrt();
            let primitive = rubi_rhs_int(&transformed, sub);

            rubi_star(ff.pow(&m_ + 1) * cos.pow(2).sqrt()
                    / (&f__ * cos), rubi_subst(&primitive, sub, sin / &ff))
        },
    ));
}

fn push_rules_rule_3668(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, d__, e__, f__, m_, p_, x_);
    rules.push(rubi_rule!(
            order: 3668,
            source: "Int[(d_.*sin[e_.+f_.*x_])^m_*(a_+b_.*sin[e_.+f_.*x_]^2)^p_.,x_Symbol] :=
              With[{ff=FreeFactors[Cos[e+f*x],x]},
              -ff*d^(2*IntPart[(m-1)/2]+1)*(d*Sin[e+f*x])^(2*FracPart[(m-1)/2])/(f*(Sin[e+f*x]^2)^FracPart[(m-1)/2]) \\[Star]
                Subst[Int[(1-ff^2*x^2)^((m-1)/2)*(a+b-b*ff^2*x^2)^p,x],x,Cos[e+f*x]/ff]] /;
            FreeQ[{a,b,d,e,f,m,p},x] && Not[IntegerQ[m]]",
            desc: "Piecewise constant extraction and integration by substitution",
            refs: [],
            pattern: (d__ * i_sin(e__ + f__ * x_)).pow(m_)
                * (a__ + b__ * i_sin(e__ + f__ * x_).pow(2)).pow(p_),
            with: [a__, b__, d__, e__, f__, m_, p_, x_],
            optional: [d__, b__, e__, f__, p_],
            when: {
                freeq!([a__, b__, d__, e__, f__, m_, p_], x_)
                    && !integerq!(m_)
            },
            rhs: {
                let substitution_guard = fresh_substitution_symbol().unwrap();
                let sub = substitution_guard.symbol();
                let z = Atom::var(sub);
                let angle = &e__ + &f__ * x_;
                let sin = angle.sin();
                let cos = angle.cos();
                let ff = rubi_free_factors(&cos, x_);
                let half_m_minus_one = (&m_ - 1) / 2;
                let int_part = rubi_int_part(&half_m_minus_one);
                let frac_part = rubi_frac_part(&half_m_minus_one);
                let transformed = (Atom::num(1) - ff.pow(2) * z.pow(2)).pow(&half_m_minus_one)
                    * (&a__ + &b__ - &b__ * ff.pow(2) * z.pow(2)).pow(&p_);
                let primitive = rubi_rhs_int(&transformed, sub);

                rubi_star(-&ff * d__.pow(Atom::num(2) * int_part + 1)
                        * (&d__ * &sin).pow(Atom::num(2) * &frac_part)
                        / (&f__ * sin.pow(2).pow(frac_part)), rubi_subst(&primitive, sub, cos / &ff))
            },
        ));
}

fn push_rules_rule_3669(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, e__, f__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 3669,
        source: "Int[cos[e_.+f_.*x_]^m_.*(a_+b_.*sin[e_.+f_.*x_]^2)^p_.,x_Symbol] :=
          With[{ff=FreeFactors[Sin[e+f*x],x]},
          ff/f \\[Star] Subst[Int[(1-ff^2*x^2)^((m-1)/2)*(a+b*ff^2*x^2)^p,x],x,Sin[e+f*x]/ff]] /;
        FreeQ[{a,b,e,f,p},x] && IntegerQ[(m-1)/2]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_13(symbols),
        with: [a__, b__, e__, f__, m_, p_, x_],
        optional: [b__, e__, f__, m_, p_],
        when: {
            freeq!([a__, b__, e__, f__, p_], x_)
                && integerq!((&m_ - 1) / 2)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let z = Atom::var(sub);
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let ff = rubi_free_factors(&sin, x_);
            let transformed = (Atom::num(1) - ff.pow(2) * z.pow(2)).pow((&m_ - 1) / 2)
                * (&a__ + &b__ * ff.pow(2) * z.pow(2)).pow(&p_);
            let primitive = rubi_rhs_int(&transformed, sub);

            rubi_star(&ff / &f__, rubi_subst(&primitive, sub, sin / &ff))
        },
    ));
}

fn push_rules_rule_3670(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, e__, f__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 3670,
        source: "Int[cos[e_.+f_.*x_]^m_*(a_+b_.*sin[e_.+f_.*x_]^2)^p_.,x_Symbol] :=
          With[{ff=FreeFactors[Tan[e+f*x],x]},
          ff/f \\[Star] Subst[Int[(a+(a+b)*ff^2*x^2)^p/(1+ff^2*x^2)^(m/2+p+1),x],x,Tan[e+f*x]/ff]] /;
        FreeQ[{a,b,e,f},x] && IntegerQ[m/2] && IntegerQ[p]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_13(symbols),
        with: [a__, b__, e__, f__, m_, p_, x_],
        optional: [b__, e__, f__, p_],
        when: {
            freeq!([a__, b__, e__, f__], x_)
                && integerq!(&m_ / 2)
                && integerq!(p_)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let z = Atom::var(sub);
            let angle = &e__ + &f__ * x_;
            let tan = angle.tan();
            let ff = rubi_free_factors(&tan, x_);
            let transformed = (&a__ + (&a__ + &b__) * ff.pow(2) * z.pow(2)).pow(&p_)
                / (Atom::num(1) + ff.pow(2) * z.pow(2)).pow(&m_ / 2 + &p_ + 1);
            let primitive = rubi_rhs_int(&transformed, sub);

            rubi_star(&ff / &f__, rubi_subst(&primitive, sub, tan / &ff))
        },
    ));
}

fn push_rules_rule_3671(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, e__, f__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 3671,
        source: "Int[cos[e_.+f_.*x_]^m_*(a_+b_.*sin[e_.+f_.*x_]^2)^p_.,x_Symbol] :=
          With[{ff=FreeFactors[Sin[e+f*x],x]},
          ff*Sqrt[Cos[e+f*x]^2]/(f*Cos[e+f*x]) \\[Star] Subst[Int[(1-ff^2*x^2)^((m-1)/2)*(a+b*ff^2*x^2)^p,x],x,Sin[e+f*x]/ff]] /;
        FreeQ[{a,b,e,f,p},x] && IntegerQ[m/2] && Not[IntegerQ[p]]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_13(symbols),
        with: [a__, b__, e__, f__, m_, p_, x_],
        optional: [b__, e__, f__, p_],
        when: {
            freeq!([a__, b__, e__, f__, p_], x_)
                && integerq!(&m_ / 2)
                && !integerq!(p_)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let z = Atom::var(sub);
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let cos = angle.cos();
            let ff = rubi_free_factors(&sin, x_);
            let transformed = (Atom::num(1) - ff.pow(2) * z.pow(2)).pow((&m_ - 1) / 2)
                * (&a__ + &b__ * ff.pow(2) * z.pow(2)).pow(&p_);
            let primitive = rubi_rhs_int(&transformed, sub);

            rubi_star(&ff * cos.pow(2).sqrt()
                    / (&f__ * cos), rubi_subst(&primitive, sub, sin / &ff))
        },
    ));
}

fn push_rules_rule_3672(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, d__, e__, f__, m_, p_, x_);
    rules.push(rubi_rule!(
            order: 3672,
            source: "Int[(d_.*cos[e_.+f_.*x_])^m_*(a_+b_.*sin[e_.+f_.*x_]^2)^p_.,x_Symbol] :=
              With[{ff=FreeFactors[Sin[e+f*x],x]},
              ff*d^(2*IntPart[(m-1)/2]+1)*(d*Cos[e+f*x])^(2*FracPart[(m-1)/2])/(f*(Cos[e+f*x]^2)^FracPart[(m-1)/2]) \\[Star]
                Subst[Int[(1-ff^2*x^2)^((m-1)/2)*(a+b*ff^2*x^2)^p,x],x,Sin[e+f*x]/ff]] /;
            FreeQ[{a,b,d,e,f,m,p},x] && Not[IntegerQ[m]]",
            desc: "Piecewise constant extraction and integration by substitution",
            refs: [],
            pattern: (d__ * i_cos(e__ + f__ * x_)).pow(m_)
                * (a__ + b__ * i_sin(e__ + f__ * x_).pow(2)).pow(p_),
            with: [a__, b__, d__, e__, f__, m_, p_, x_],
            optional: [d__, b__, e__, f__, p_],
            when: {
                freeq!([a__, b__, d__, e__, f__, m_, p_], x_)
                    && !integerq!(m_)
            },
            rhs: {
                let substitution_guard = fresh_substitution_symbol().unwrap();
                let sub = substitution_guard.symbol();
                let z = Atom::var(sub);
                let angle = &e__ + &f__ * x_;
                let sin = angle.sin();
                let cos = angle.cos();
                let ff = rubi_free_factors(&sin, x_);
                let half_m_minus_one = (&m_ - 1) / 2;
                let int_part = rubi_int_part(&half_m_minus_one);
                let frac_part = rubi_frac_part(&half_m_minus_one);
                let transformed = (Atom::num(1) - ff.pow(2) * z.pow(2)).pow(&half_m_minus_one)
                    * (&a__ + &b__ * ff.pow(2) * z.pow(2)).pow(&p_);
                let primitive = rubi_rhs_int(&transformed, sub);

                rubi_star(&ff * d__.pow(Atom::num(2) * int_part + 1)
                        * (&d__ * &cos).pow(Atom::num(2) * &frac_part)
                        / (&f__ * cos.pow(2).pow(frac_part)), rubi_subst(&primitive, sub, sin / &ff))
            },
        ));
}

fn push_rules_rule_3673(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, e__, f__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 3673,
        source: "Int[tan[e_.+f_.*x_]^m_.*(a_+b_.*sin[e_.+f_.*x_]^2)^p_.,x_Symbol] :=
          With[{ff=FreeFactors[Sin[e+f*x]^2,x]},
          ff^((m+1)/2)/(2*f) \\[Star] Subst[Int[x^((m-1)/2)*(a+b*ff*x)^p/(1-ff*x)^((m+1)/2),x],x,Sin[e+f*x]^2/ff]] /;
        FreeQ[{a,b,e,f,p},x] && IntegerQ[(m-1)/2]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_18(symbols),
        with: [a__, b__, e__, f__, m_, p_, x_],
        optional: [b__, e__, f__, m_, p_],
        when: {
            freeq!([a__, b__, e__, f__, p_], x_)
                && integerq!((&m_ - 1) / 2)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let z = Atom::var(sub);
            let angle = &e__ + &f__ * x_;
            let sin_squared = angle.sin().pow(2);
            let ff = rubi_free_factors(&sin_squared, x_);
            let transformed = z.pow((&m_ - 1) / 2) * (&a__ + &b__ * &ff * &z).pow(&p_)
                / (Atom::num(1) - &ff * &z).pow((&m_ + 1) / 2);
            let primitive = rubi_rhs_int(&transformed, sub);

            rubi_star(ff.pow((&m_ + 1) / 2)
                    / (Atom::num(2) * &f__), rubi_subst(&primitive, sub, sin_squared / &ff))
        },
    ));
}

fn push_rules_rule_3674(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, e__, f__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 3674,
        source: "Int[(d_.*tan[e_.+f_.*x_])^m_*(a_+b_.*sin[e_.+f_.*x_]^2)^p_.,x_Symbol] :=
          With[{ff=FreeFactors[Tan[e+f*x],x]},
          ff/f \\[Star] Subst[Int[(d*ff*x)^m*(a+(a+b)*ff^2*x^2)^p/(1+ff^2*x^2)^(p+1),x],x,Tan[e+f*x]/ff]] /;
        FreeQ[{a,b,d,e,f,m},x] && IntegerQ[p]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_10(symbols),
        with: [a__, b__, d__, e__, f__, m_, p_, x_],
        optional: [d__, b__, e__, f__, p_],
        when: {
            freeq!([a__, b__, d__, e__, f__, m_], x_)
                && integerq!(p_)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let z = Atom::var(sub);
            let angle = &e__ + &f__ * x_;
            let tan = angle.tan();
            let ff = rubi_free_factors(&tan, x_);
            let transformed = (&d__ * &ff * &z).pow(&m_)
                * (&a__ + (&a__ + &b__) * ff.pow(2) * z.pow(2)).pow(&p_)
                / (Atom::num(1) + ff.pow(2) * z.pow(2)).pow(&p_ + 1);
            let primitive = rubi_rhs_int(&transformed, sub);

            rubi_star(&ff / &f__, rubi_subst(&primitive, sub, tan / &ff))
        },
    ));
}

fn push_rules_rule_3675(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, e__, f__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 3675,
        source: "Int[tan[e_.+f_.*x_]^m_*(a_+b_.*sin[e_.+f_.*x_]^2)^p_.,x_Symbol] :=
          With[{ff=FreeFactors[Sin[e+f*x],x]},
          ff^(m+1)*Sqrt[Cos[e+f*x]^2]/(f*Cos[e+f*x]) \\[Star]
            Subst[Int[x^m*(a+b*ff^2*x^2)^p/(1-ff^2*x^2)^((m+1)/2),x],x,Sin[e+f*x]/ff]] /;
        FreeQ[{a,b,e,f,p},x] && IntegerQ[m/2] && Not[IntegerQ[p]]",
        desc: "Piecewise constant extraction and integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_18(symbols),
        with: [a__, b__, e__, f__, m_, p_, x_],
        optional: [b__, e__, f__, p_],
        when: {
            freeq!([a__, b__, e__, f__, p_], x_)
                && integerq!(&m_ / 2)
                && !integerq!(p_)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let z = Atom::var(sub);
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let cos = angle.cos();
            let ff = rubi_free_factors(&sin, x_);
            let transformed = z.pow(&m_) * (&a__ + &b__ * ff.pow(2) * z.pow(2)).pow(&p_)
                / (Atom::num(1) - ff.pow(2) * z.pow(2)).pow((&m_ + 1) / 2);
            let primitive = rubi_rhs_int(&transformed, sub);

            rubi_star(ff.pow(&m_ + 1) * cos.pow(2).sqrt()
                    / (&f__ * cos), rubi_subst(&primitive, sub, sin / &ff))
        },
    ));
}

fn push_rules_rule_3676(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, e__, f__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 3676,
        source: "Int[(d_.*tan[e_.+f_.*x_])^m_*(a_+b_.*sin[e_.+f_.*x_]^2)^p_.,x_Symbol] :=
          With[{ff=FreeFactors[Sin[e+f*x],x]},
          ff*(d*Tan[e+f*x])^(m+1)*(Cos[e+f*x]^2)^((m+1)/2)/(d*f*Sin[e+f*x]^(m+1)) \\[Star]
            Subst[Int[(ff*x)^m*(a+b*ff^2*x^2)^p/(1-ff^2*x^2)^((m+1)/2),x],x,Sin[e+f*x]/ff]] /;
        FreeQ[{a,b,d,e,f,m,p},x] && Not[IntegerQ[m]]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_10(symbols),
        with: [a__, b__, d__, e__, f__, m_, p_, x_],
        optional: [d__, b__, e__, f__, p_],
        when: {
            freeq!([a__, b__, d__, e__, f__, m_, p_], x_)
                && !integerq!(m_)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let z = Atom::var(sub);
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let cos = angle.cos();
            let tan = angle.tan();
            let ff = rubi_free_factors(&sin, x_);
            let transformed = (&ff * &z).pow(&m_) * (&a__ + &b__ * ff.pow(2) * z.pow(2)).pow(&p_)
                / (Atom::num(1) - ff.pow(2) * z.pow(2)).pow((&m_ + 1) / 2);
            let primitive = rubi_rhs_int(&transformed, sub);
            let denominator = &d__ * &f__ * sin.pow(&m_ + 1);

            rubi_star(&ff * (&d__ * tan).pow(&m_ + 1) * cos.pow(2).pow((&m_ + 1) / 2)
                    / denominator, rubi_subst(&primitive, sub, sin / &ff))
        },
    ));
}

fn push_rules_rule_3677(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3677,
        source: "Int[cos[e_.+f_.*x_]^m_.*(d_.*sin[e_.+f_.*x_])^n_.*(a_+b_.*sin[e_.+f_.*x_]^2)^p_.,x_Symbol] :=
          With[{ff=FreeFactors[Sin[e+f*x],x]},
          ff/f \\[Star] Subst[Int[(d*ff*x)^n*(1-ff^2*x^2)^((m-1)/2)*(a+b*ff^2*x^2)^p,x],x,Sin[e+f*x]/ff]] /;
        FreeQ[{a,b,d,e,f,n,p},x] && IntegerQ[(m-1)/2]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_14(symbols),
        with: [a__, b__, d__, e__, f__, m_, n_, p_, x_],
        optional: [d__, b__, e__, f__, m_, n_, p_],
        when: {
            freeq!([a__, b__, d__, e__, f__, n_, p_], x_)
                && integerq!((&m_ - 1) / 2)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let z = Atom::var(sub);
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let ff = rubi_free_factors(&sin, x_);
            let transformed = (&d__ * &ff * &z).pow(&n_)
                * (Atom::num(1) - ff.pow(2) * z.pow(2)).pow((&m_ - 1) / 2)
                * (&a__ + &b__ * ff.pow(2) * z.pow(2)).pow(&p_);
            let primitive = rubi_rhs_int(&transformed, sub);

            rubi_star(&ff / &f__, rubi_subst(&primitive, sub, sin / &ff))
        },
    ));
}

fn push_rules_rule_3678(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3678,
        source: "Int[(c_.*sin[e_.+f_.*x_])^m_*sin[e_.+f_.*x_]^n_.*(a_+b_.*sin[e_.+f_.*x_]^2)^p_.,x_Symbol] :=
          With[{ff=FreeFactors[Cos[e+f*x],x]},
          -ff/f \\[Star] Subst[Int[(c*ff*x)^m*(1-ff^2*x^2)^((n-1)/2)*(a+b-b*ff^2*x^2)^p,x],x,Cos[e+f*x]/ff]] /;
        FreeQ[{a,b,c,e,f,m,p},x] && IntegerQ[(n-1)/2]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (c__ * i_sin(e__ + f__ * x_)).pow(m_)
            * i_sin(e__ + f__ * x_).pow(n_)
            * (a__ + b__ * i_sin(e__ + f__ * x_).pow(2)).pow(p_),
        with: [a__, b__, c__, e__, f__, m_, n_, p_, x_],
        optional: [c__, b__, e__, f__, n_, p_],
        when: {
            freeq!([a__, b__, c__, e__, f__, m_, p_], x_)
                && integerq!((&n_ - 1) / 2)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let z = Atom::var(sub);
            let angle = &e__ + &f__ * x_;
            let cos = angle.cos();
            let ff = rubi_free_factors(&cos, x_);
            let transformed = (&c__ * &ff * &z).pow(&m_)
                * (Atom::num(1) - ff.pow(2) * z.pow(2)).pow((&n_ - 1) / 2)
                * (&a__ + &b__ - &b__ * ff.pow(2) * z.pow(2)).pow(&p_);
            let primitive = rubi_rhs_int(&transformed, sub);

            rubi_star(-&ff / &f__, rubi_subst(&primitive, sub, cos / &ff))
        },
    ));
}

fn push_rules_rule_3679(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3679,
        source: "Int[cos[e_.+f_.*x_]^m_*sin[e_.+f_.*x_]^n_*(a_+b_.*sin[e_.+f_.*x_]^2)^p_.,x_Symbol] :=
          With[{ff=FreeFactors[Tan[e+f*x],x]},
          ff^(n+1)/f \\[Star] Subst[Int[x^n*(a+(a+b)*ff^2*x^2)^p/(1+ff^2*x^2)^((m+n)/2+p+1),x],x,Tan[e+f*x]/ff]] /;
        FreeQ[{a,b,e,f},x] && IntegerQ[m/2] && IntegerQ[n/2] && IntegerQ[p]",
        desc: "Integration by substitution",
        refs: [],
        pattern: i_cos(e__ + f__ * x_).pow(m_)
            * i_sin(e__ + f__ * x_).pow(n_)
            * (a__ + b__ * i_sin(e__ + f__ * x_).pow(2)).pow(p_),
        with: [a__, b__, e__, f__, m_, n_, p_, x_],
        optional: [b__, e__, f__, p_],
        when: {
            freeq!([a__, b__, e__, f__], x_)
                && integerq!(&m_ / 2)
                && integerq!(&n_ / 2)
                && integerq!(p_)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let z = Atom::var(sub);
            let angle = &e__ + &f__ * x_;
            let tan = angle.tan();
            let ff = rubi_free_factors(&tan, x_);
            let transformed = z.pow(&n_) * (&a__ + (&a__ + &b__) * ff.pow(2) * z.pow(2)).pow(&p_)
                / (Atom::num(1) + ff.pow(2) * z.pow(2)).pow((&m_ + &n_) / 2 + &p_ + 1);
            let primitive = rubi_rhs_int(&transformed, sub);

            rubi_star(ff.pow(&n_ + 1) / &f__, rubi_subst(&primitive, sub, tan / &ff))
        },
    ));
}

fn push_rules_rule_3680(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3680,
        source: "Int[cos[e_.+f_.*x_]^m_*(d_.*sin[e_.+f_.*x_])^n_.*(a_+b_.*sin[e_.+f_.*x_]^2)^p_.,x_Symbol] :=
          With[{ff=FreeFactors[Sin[e+f*x],x]},
          ff*Sqrt[Cos[e+f*x]^2]/(f*Cos[e+f*x]) \\[Star] Subst[Int[(d*ff*x)^n*(1-ff^2*x^2)^((m-1)/2)*(a+b*ff^2*x^2)^p,x],x,Sin[e+f*x]/ff]] /;
        FreeQ[{a,b,d,e,f,n,p},x] && IntegerQ[m/2]",
        desc: "Piecewise constant extraction and integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_14(symbols),
        with: [a__, b__, d__, e__, f__, m_, n_, p_, x_],
        optional: [d__, b__, e__, f__, n_, p_],
        when: {
            freeq!([a__, b__, d__, e__, f__, n_, p_], x_)
                && integerq!(&m_ / 2)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let z = Atom::var(sub);
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let cos = angle.cos();
            let ff = rubi_free_factors(&sin, x_);
            let transformed = (&d__ * &ff * &z).pow(&n_)
                * (Atom::num(1) - ff.pow(2) * z.pow(2)).pow((&m_ - 1) / 2)
                * (&a__ + &b__ * ff.pow(2) * z.pow(2)).pow(&p_);
            let primitive = rubi_rhs_int(&transformed, sub);

            rubi_star(&ff * cos.pow(2).sqrt()
                    / (&f__ * cos), rubi_subst(&primitive, sub, sin / &ff))
        },
    ));
}

fn push_rules_rule_3681(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3681,
        source: "Int[(c_.*cos[e_.+f_.*x_])^m_*(d_.*sin[e_.+f_.*x_])^n_.*(a_+b_.*sin[e_.+f_.*x_]^2)^p_.,x_Symbol] :=
          With[{ff=FreeFactors[Sin[e+f*x],x]},
          ff*c^(2*IntPart[(m-1)/2]+1)*(c*Cos[e+f*x])^(2*FracPart[(m-1)/2])/(f*(Cos[e+f*x]^2)^FracPart[(m-1)/2]) \\[Star]
            Subst[Int[(d*ff*x)^n*(1-ff^2*x^2)^((m-1)/2)*(a+b*ff^2*x^2)^p,x],x,Sin[e+f*x]/ff]] /;
        FreeQ[{a,b,c,d,e,f,m,n,p},x] && Not[IntegerQ[m]]",
        desc: "Piecewise constant extraction and integration by substitution",
        refs: [],
        pattern: (c__ * i_cos(e__ + f__ * x_)).pow(m_)
            * (d__ * i_sin(e__ + f__ * x_)).pow(n_)
            * (a__ + b__ * i_sin(e__ + f__ * x_).pow(2)).pow(p_),
        with: [a__, b__, c__, d__, e__, f__, m_, n_, p_, x_],
        optional: [c__, d__, b__, e__, f__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_, p_], x_)
                && !integerq!(m_)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let z = Atom::var(sub);
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let cos = angle.cos();
            let ff = rubi_free_factors(&sin, x_);
            let half_m_minus_one = (&m_ - 1) / 2;
            let int_part = rubi_int_part(&half_m_minus_one);
            let frac_part = rubi_frac_part(&half_m_minus_one);
            let transformed = (&d__ * &ff * &z).pow(&n_)
                * (Atom::num(1) - ff.pow(2) * z.pow(2)).pow(&half_m_minus_one)
                * (&a__ + &b__ * ff.pow(2) * z.pow(2)).pow(&p_);
            let primitive = rubi_rhs_int(&transformed, sub);

            rubi_star(&ff * c__.pow(Atom::num(2) * int_part + 1)
                    * (&c__ * &cos).pow(Atom::num(2) * &frac_part)
                    / (&f__ * cos.pow(2).pow(frac_part)), rubi_subst(&primitive, sub, sin / &ff))
        },
    ));
}

fn push_rules_rule_3682(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; b__, e__, f__, p_, x_);
    rules.push(rubi_rule!(
        order: 3682,
        source: "Int[(b_.*sin[e_.+f_.*x_]^2)^p_,x_Symbol] :=
          -Cot[e+f*x]*(b*Sin[e+f*x]^2)^p/(2*f*p) +
          b*(2*p-1)/(2*p) \\[Star] Int[(b*Sin[e+f*x]^2)^(p-1),x] /;
        FreeQ[{b,e,f},x] && Not[IntegerQ[p]] && GtQ[p,1]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [b__, e__, f__, p_, x_],
        optional: [b__, e__, f__],
        when: {
            freeq!([b__, e__, f__], x_) && !integerq!(p_) && gtq!(p_, 1)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let base = &b__ * angle.sin().pow(2);
            let recursive = rubi_rhs_int(&base.pow(&p_ - 1), x_);

            rubi_simp(&(-angle.cot() * base.pow(&p_) / (Atom::num(2) * &f__ * &p_)), x_)
                    + rubi_star(&b__ * (Atom::num(2) * &p_ - 1)
                            / (Atom::num(2) * &p_), recursive)
        },
    ));
}

fn push_rules_rule_3683(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; b__, e__, f__, p_, x_);
    rules.push(rubi_rule!(
        order: 3683,
        source: "Int[(b_.*sin[e_.+f_.*x_]^2)^p_,x_Symbol] :=
          Cot[e+f*x]*(b*Sin[e+f*x]^2)^(p+1)/(b*f*(2*p+1)) +
          2*(p+1)/(b*(2*p+1)) \\[Star] Int[(b*Sin[e+f*x]^2)^(p+1),x] /;
        FreeQ[{b,e,f},x] && Not[IntegerQ[p]] && LtQ[p,-1]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [b__, e__, f__, p_, x_],
        optional: [b__, e__, f__],
        when: {
            freeq!([b__, e__, f__], x_) && !integerq!(p_) && ltq!(p_, -1)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let base = &b__ * angle.sin().pow(2);
            let p1 = &p_ + 1;
            let recursive = rubi_rhs_int(&base.pow(&p1), x_);

            rubi_simp(&(angle.cot() * base.pow(&p1) / (&b__ * &f__ * (Atom::num(2) * &p_ + 1))), x_)
                    + rubi_star(Atom::num(2) * &p1
                            / (&b__ * (Atom::num(2) * &p_ + 1)), recursive)
        },
    ));
}

fn push_rules_rule_3684(rules: &mut Vec<RubiRule>) {
    rubi_symb!(b__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3684,
        source: "Int[tan[e_.+f_.*x_]^m_.*(b_.*sin[e_.+f_.*x_]^n_)^p_.,x_Symbol] :=
          With[{ff=FreeFactors[Sin[e+f*x]^2,x]},
          ff^((m+1)/2)/(2*f) \\[Star] Subst[Int[x^((m-1)/2)*(b*ff^(n/2)*x^(n/2))^p/(1-ff*x)^((m+1)/2),x],x,Sin[e+f*x]^2/ff]] /;
        FreeQ[{b,e,f,p},x] && IntegerQ[(m-1)/2] && IntegerQ[n/2]",
        desc: "Integration by substitution",
        refs: [],
        pattern: i_tan(e__ + f__ * x_).pow(m_)
            * (b__ * i_sin(e__ + f__ * x_).pow(n_)).pow(p_),
        with: [b__, e__, f__, m_, n_, p_, x_],
        optional: [b__, e__, f__, m_, p_],
        when: {
            freeq!([b__, e__, f__, p_], x_)
                && integerq!((&m_ - 1) / 2)
                && integerq!(&n_ / 2)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let z = Atom::var(sub);
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let ff = rubi_free_factors(&sin.pow(2), x_);
            let transformed = z.pow((&m_ - 1) / 2)
                * (&b__ * ff.pow(&n_ / 2) * z.pow(&n_ / 2)).pow(&p_)
                / (Atom::num(1) - &ff * &z).pow((&m_ + 1) / 2);
            let primitive = rubi_rhs_int(&transformed, sub);

            rubi_star(ff.pow((&m_ + 1) / 2)
                    / (Atom::num(2) * &f__), rubi_subst(&primitive, sub, sin.pow(2) / &ff))
        },
    ));
}

fn push_rules_rule_3685(rules: &mut Vec<RubiRule>) {
    rubi_symb!(b__, c__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3685,
        source: "Int[tan[e_.+f_.*x_]^m_.*(b_.*(c_.*sin[e_.+f_.*x_])^n_)^p_.,x_Symbol] :=
          With[{ff=FreeFactors[Sin[e+f*x],x]},
          ff^(m+1)/f \\[Star] Subst[Int[x^m*(b*(c*ff*x)^n)^p/(1-ff^2*x^2)^((m+1)/2),x],x,Sin[e+f*x]/ff]] /;
        FreeQ[{b,c,e,f,n,p},x] && ILtQ[(m-1)/2,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: i_tan(e__ + f__ * x_).pow(m_)
            * (b__ * (c__ * i_sin(e__ + f__ * x_)).pow(n_)).pow(p_),
        with: [b__, c__, e__, f__, m_, n_, p_, x_],
        optional: [b__, c__, e__, f__, m_, p_],
        when: {
            freeq!([b__, c__, e__, f__, n_, p_], x_)
                && iltq!((&m_ - 1) / 2, 0)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let z = Atom::var(sub);
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let ff = rubi_free_factors(&sin, x_);
            let transformed = z.pow(&m_) * (&b__ * (&c__ * &ff * &z).pow(&n_)).pow(&p_)
                / (Atom::num(1) - ff.pow(2) * z.pow(2)).pow((&m_ + 1) / 2);
            let primitive = rubi_rhs_int(&transformed, sub);

            rubi_star(ff.pow(&m_ + 1) / &f__, rubi_subst(&primitive, sub, sin / &ff))
        },
    ));
}

fn push_rules_rule_3686(rules: &mut Vec<RubiRule>) {
    rubi_symb!(b__, e__, f__, n_, p_, u__, x_);
    rules.push(rubi_rule!(
        order: 3686,
        source: "Int[u_.*(b_.*sin[e_.+f_.*x_]^n_)^p_,x_Symbol] :=
          With[{ff=FreeFactors[Sin[e+f*x],x]},
          (b*ff^n)^IntPart[p]*(b*Sin[e+f*x]^n)^FracPart[p]/(Sin[e+f*x]/ff)^(n*FracPart[p]) \\[Star]
            Int[ActivateTrig[u]*(Sin[e+f*x]/ff)^(n*p),x]] /;
        FreeQ[{b,e,f,n,p},x] && Not[IntegerQ[p]] && IntegerQ[n] &&
          (EqQ[u,1] || MatchQ[u,(d_.*trig_[e+f*x])^m_. /; FreeQ[{d,m},x] && MemberQ[{sin,cos,tan,cot,sec,csc},trig]])",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: u__ * (b__ * i_sin(e__ + f__ * x_).pow(n_)).pow(p_),
        with: [u__, b__, e__, f__, n_, p_, x_],
        optional: [u__, b__, e__, f__],
        when: {
            let angle = &e__ + &f__ * x_;
            freeq!([b__, e__, f__, n_, p_], x_)
                && !integerq!(p_)
                && integerq!(n_)
                && rubi_match_optional_scaled_trig_power_same_angle_q(&u__, &angle, x_)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let ff = rubi_free_factors(&sin, x_);
            let int_part = rubi_int_part(&p_);
            let frac_part = rubi_frac_part(&p_);
            let multiplier = (&b__ * ff.pow(&n_)).pow(int_part)
                * (&b__ * sin.pow(&n_)).pow(&frac_part)
                / (&sin / &ff).pow(&n_ * &frac_part);
            let recursive =
                rubi_rhs_int(&(rubi_activate_trig(&u__) * (sin / ff).pow(&n_ * &p_)), x_);

            rubi_star(multiplier, recursive)
        },
    ));
}

fn push_rules_rule_3687(rules: &mut Vec<RubiRule>) {
    rubi_symb!(b__, c__, e__, f__, n_, p_, u__, x_);
    rules.push(rubi_rule!(
        order: 3687,
        source: "Int[u_.*(b_.*(c_.*sin[e_.+f_.*x_])^n_)^p_,x_Symbol] :=
          b^IntPart[p]*(b*(c*Sin[e+f*x])^n)^FracPart[p]/(c*Sin[e+f*x])^(n*FracPart[p]) \\[Star]
            Int[ActivateTrig[u]*(c*Sin[e+f*x])^(n*p),x] /;
        FreeQ[{b,c,e,f,n,p},x] && Not[IntegerQ[p]] && Not[IntegerQ[n]] &&
          (EqQ[u,1] || MatchQ[u,(d_.*trig_[e+f*x])^m_. /; FreeQ[{d,m},x] && MemberQ[{sin,cos,tan,cot,sec,csc},trig]])",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: u__ * (b__ * (c__ * i_sin(e__ + f__ * x_)).pow(n_)).pow(p_),
        with: [u__, b__, c__, e__, f__, n_, p_, x_],
        optional: [u__, b__, c__, e__, f__],
        when: {
            let angle = &e__ + &f__ * x_;
            freeq!([b__, c__, e__, f__, n_, p_], x_)
                && !integerq!(p_)
                && !integerq!(n_)
                && rubi_match_optional_scaled_trig_power_same_angle_q(&u__, &angle, x_)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let int_part = rubi_int_part(&p_);
            let frac_part = rubi_frac_part(&p_);
            let c_sin = &c__ * &sin;
            let multiplier = b__.pow(int_part) * (&b__ * c_sin.pow(&n_)).pow(&frac_part)
                / c_sin.pow(&n_ * &frac_part);
            let recursive =
                rubi_rhs_int(&(rubi_activate_trig(&u__) * c_sin.pow(&n_ * &p_)), x_);

            rubi_star(multiplier, recursive)
        },
    ));
}

fn push_rules_rule_3688(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, e__, f__, p_, x_);
    rules.push(rubi_rule!(
        order: 3688,
        source: "Int[(a_+b_.*sin[e_.+f_.*x_]^4)^p_.,x_Symbol] :=
          With[{ff=FreeFactors[Tan[e+f*x],x]},
          ff/f \\[Star] Subst[Int[(a+2*a*ff^2*x^2+(a+b)*ff^4*x^4)^p/(1+ff^2*x^2)^(2*p+1),x],x,Tan[e+f*x]/ff]] /;
        FreeQ[{a,b,e,f},x] && IntegerQ[p]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [a__, b__, e__, f__, p_, x_],
        optional: [b__, e__, f__, p_],
        when: { freeq!([a__, b__, e__, f__], x_) && integerq!(p_) },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let z = Atom::var(sub);
            let angle = &e__ + &f__ * x_;
            let tan = angle.tan();
            let ff = rubi_free_factors(&tan, x_);
            let transformed = (&a__
                + Atom::num(2) * &a__ * ff.pow(2) * z.pow(2)
                + (&a__ + &b__) * ff.pow(4) * z.pow(4))
            .pow(&p_)
                / (Atom::num(1) + ff.pow(2) * z.pow(2)).pow(Atom::num(2) * &p_ + 1);
            let primitive = rubi_rhs_int(&transformed, sub);

            rubi_star(&ff / &f__, rubi_subst(&primitive, sub, tan / &ff))
        },
    ));
}

fn push_rules_rule_3689(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, e__, f__, p_, x_);
    rules.push(rubi_rule!(
            order: 3689,
            source: "Int[(a_+b_.*sin[e_.+f_.*x_]^4)^p_,x_Symbol] :=
              With[{ff=FreeFactors[Tan[e+f*x],x]},
              ff*(a+b*Sin[e+f*x]^4)^p*(Sec[e+f*x]^2)^(2*p)/(f*(a+2*a*Tan[e+f*x]^2+(a+b)*Tan[e+f*x]^4)^p) \\[Star]
                Subst[Int[(a+2*a*ff^2*x^2+(a+b)*ff^4*x^4)^p/(1+ff^2*x^2)^(2*p+1),x],x,Tan[e+f*x]/ff]] /;
            FreeQ[{a,b,e,f,p},x] && IntegerQ[p-1/2]",
            desc: "Piecewise constant extraction and integration by substitution",
            refs: [],
            pattern:  rubi_shared_pattern_5(symbols),
            with: [a__, b__, e__, f__, p_, x_],
            optional: [b__, e__, f__],
            when: {
                freeq!([a__, b__, e__, f__, p_], x_)
                    && integerq!(&p_ - Atom::num(1) / Atom::num(2))
            },
            rhs: {
                let substitution_guard = fresh_substitution_symbol().unwrap();
                let sub = substitution_guard.symbol();
                let z = Atom::var(sub);
                let angle = &e__ + &f__ * x_;
                let sin = angle.sin();
                let tan = angle.tan();
                let sec = angle.sec();
                let ff = rubi_free_factors(&tan, x_);
                let tan_denominator =
                    &a__ + Atom::num(2) * &a__ * tan.pow(2) + (&a__ + &b__) * tan.pow(4);
                let transformed = (&a__
                    + Atom::num(2) * &a__ * ff.pow(2) * z.pow(2)
                    + (&a__ + &b__) * ff.pow(4) * z.pow(4))
                .pow(&p_)
                    / (Atom::num(1) + ff.pow(2) * z.pow(2)).pow(Atom::num(2) * &p_ + 1);
                let primitive = rubi_rhs_int(&transformed, sub);

                rubi_star(&ff * (&a__ + &b__ * sin.pow(4)).pow(&p_) * sec.pow(2).pow(Atom::num(2) * &p_)
                        / (&f__ * tan_denominator.pow(&p_)), rubi_subst(&primitive, sub, tan / &ff))
            },
        ));
}

fn push_rules_rule_3690(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, e__, f__, n_, x_);
    rules.push(rubi_rule!(
        order: 3690,
        source: "Int[1/(a_+b_.*sin[e_.+f_.*x_]^n_),x_Symbol] :=
          Module[{k},
          2/(a*n) \\[Star] Sum[Int[1/(1-Sin[e+f*x]^2/((-1)^(4*k/n)*Rt[-a/b,n/2])),x],{k,1,n/2}]] /;
        FreeQ[{a,b,e,f},x] && IntegerQ[n/2]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: Atom::num(1) / (a__ + b__ * i_sin(e__ + f__ * x_).pow(n_)),
        with: [a__, b__, e__, f__, n_, x_],
        optional: [b__, e__, f__],
        when: {
            freeq!([a__, b__, e__, f__], x_) && integerq!(&n_ / 2)
        },
        rhs: {
            let half_n = integer_i64(&(&n_ / 2)).rubi_rhs();
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let mut sum = Atom::num(0);
            for k in 1..=half_n {
                let root = Atom::num(-1).pow(Atom::num(4 * k) / &n_) * rubi_rt(&(-&a__ / &b__), half_n);
                let payload = Atom::num(1) / (Atom::num(1) - sin.pow(2) / root);
                sum += rubi_rhs_int(&payload, x_);
            }

            rubi_star(Atom::num(2) / (&a__ * &n_), sum)
        },
    ));
}

fn push_rules_rule_3691(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, e__, f__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3691,
        source: "Int[(a_+b_.*sin[e_.+f_.*x_]^n_)^p_,x_Symbol] :=
          With[{ff=FreeFactors[Tan[e+f*x],x]},
          ff/f \\[Star] Subst[Int[(b*ff^n*x^n+a*(1+ff^2*x^2)^(n/2))^p/(1+ff^2*x^2)^(n*p/2+1),x],x,Tan[e+f*x]/ff]] /;
        FreeQ[{a,b,e,f},x] && IntegerQ[n/2] && IGtQ[p,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (a__ + b__ * i_sin(e__ + f__ * x_).pow(n_)).pow(p_),
        with: [a__, b__, e__, f__, n_, p_, x_],
        optional: [b__, e__, f__],
        when: {
            freeq!([a__, b__, e__, f__], x_)
                && integerq!(&n_ / 2)
                && igtq!(p_, 0)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let z = Atom::var(sub);
            let angle = &e__ + &f__ * x_;
            let tan = angle.tan();
            let ff = rubi_free_factors(&tan, x_);
            let transformed = (&b__ * ff.pow(&n_) * z.pow(&n_)
                + &a__ * (Atom::num(1) + ff.pow(2) * z.pow(2)).pow(&n_ / 2))
            .pow(&p_)
                / (Atom::num(1) + ff.pow(2) * z.pow(2)).pow(&n_ * &p_ / 2 + 1);
            let primitive = rubi_rhs_int(&transformed, sub);

            rubi_star(&ff / &f__, rubi_subst(&primitive, sub, tan / &ff))
        },
    ));
}

fn push_rules_rule_3692(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, e__, f__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3692,
        source: "Int[(a_+b_.*(c_.*sin[e_.+f_.*x_])^n_)^p_,x_Symbol] :=
          Int[ExpandTrig[(a+b*(c*sin[e+f*x])^n)^p,x],x] /;
        FreeQ[{a,b,c,e,f,n},x] && (IGtQ[p,0] || EqQ[p,-1] && IntegerQ[n])",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, e__, f__, n_, p_, x_],
        optional: [b__, c__, e__, f__],
        when: {
            freeq!([a__, b__, c__, e__, f__, n_], x_)
                && (igtq!(p_, 0) || eqq!(p_, -1) && integerq!(n_))
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let payload = (&a__ + &b__ * (&c__ * i_sin(&angle)).pow(&n_)).pow(&p_);
            let expanded = rubi_expand_trig(&payload, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_3693(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, e__, f__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3693,
        source: "Int[(a_+b_.*(c_.*sin[e_.+f_.*x_])^n_)^p_,x_Symbol] :=
          Unintegrable[(a+b*(c*Sin[e+f*x])^n)^p,x] /;
        FreeQ[{a,b,c,e,f,n,p},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, e__, f__, n_, p_, x_],
        optional: [b__, c__, e__, f__],
        when: { freeq!([a__, b__, c__, e__, f__, n_, p_], x_) },
        rhs: {
            let angle = &e__ + &f__ * x_;

            rubi_unintegrable(
                (&a__ + &b__ * (&c__ * i_sin(&angle)).pow(&n_)).pow(&p_),
                x_,
            )
        },
    ));
}

fn push_rules_rule_3694(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, e__, f__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 3694,
        source: "Int[sin[e_.+f_.*x_]^m_.*(a_+b_.*sin[e_.+f_.*x_]^4)^p_.,x_Symbol] :=
          With[{ff=FreeFactors[Cos[e+f*x],x]},
          -ff/f \\[Star] Subst[Int[(1-ff^2*x^2)^((m-1)/2)*(a+b-2*b*ff^2*x^2+b*ff^4*x^4)^p,x],x,Cos[e+f*x]/ff]] /;
        FreeQ[{a,b,e,f,p},x] && IntegerQ[(m-1)/2]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_16(symbols),
        with: [a__, b__, e__, f__, m_, p_, x_],
        optional: [b__, e__, f__, m_, p_],
        when: {
            freeq!([a__, b__, e__, f__, p_], x_)
                && integerq!((&m_ - 1) / 2)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let z = Atom::var(sub);
            let angle = &e__ + &f__ * x_;
            let cos = angle.cos();
            let ff = rubi_free_factors(&cos, x_);
            let transformed = (Atom::num(1) - ff.pow(2) * z.pow(2)).pow((&m_ - 1) / 2)
                * (&a__ + &b__ - Atom::num(2) * &b__ * ff.pow(2) * z.pow(2)
                    + &b__ * ff.pow(4) * z.pow(4))
                .pow(&p_);
            let primitive = rubi_rhs_int(&transformed, sub);

            rubi_star(-&ff / &f__, rubi_subst(&primitive, sub, cos / &ff))
        },
    ));
}

fn push_rules_rule_3695(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3695,
        source: "Int[sin[e_.+f_.*x_]^m_.*(a_+b_.*sin[e_.+f_.*x_]^n_)^p_.,x_Symbol] :=
          With[{ff=FreeFactors[Cos[e+f*x],x]},
          -ff/f \\[Star] Subst[Int[(1-ff^2*x^2)^((m-1)/2)*(a+b*(1-ff^2*x^2)^(n/2))^p,x],x,Cos[e+f*x]/ff]] /;
        FreeQ[{a,b,e,f,p},x] && IntegerQ[(m-1)/2] && IntegerQ[n/2]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_17(symbols),
        with: [a__, b__, e__, f__, m_, n_, p_, x_],
        optional: [b__, e__, f__, m_, p_],
        when: {
            freeq!([a__, b__, e__, f__, p_], x_)
                && integerq!((&m_ - 1) / 2)
                && integerq!(&n_ / 2)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let z = Atom::var(sub);
            let angle = &e__ + &f__ * x_;
            let cos = angle.cos();
            let ff = rubi_free_factors(&cos, x_);
            let transformed = (Atom::num(1) - ff.pow(2) * z.pow(2)).pow((&m_ - 1) / 2)
                * (&a__ + &b__ * (Atom::num(1) - ff.pow(2) * z.pow(2)).pow(&n_ / 2))
                    .pow(&p_);
            let primitive = rubi_rhs_int(&transformed, sub);

            rubi_star(-&ff / &f__, rubi_subst(&primitive, sub, cos / &ff))
        },
    ));
}

fn push_rules_rule_3696(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, e__, f__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 3696,
        source: "Int[sin[e_.+f_.*x_]^m_*(a_+b_.*sin[e_.+f_.*x_]^4)^p_.,x_Symbol] :=
          With[{ff=FreeFactors[Tan[e+f*x],x]},
          ff^(m+1)/f \\[Star] Subst[Int[x^m*(a+2*a*ff^2*x^2+(a+b)*ff^4*x^4)^p/(1+ff^2*x^2)^(m/2+2*p+1),x],x,Tan[e+f*x]/ff]] /;
        FreeQ[{a,b,e,f},x] && IntegerQ[m/2] && IntegerQ[p]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_16(symbols),
        with: [a__, b__, e__, f__, m_, p_, x_],
        optional: [b__, e__, f__, p_],
        when: {
            freeq!([a__, b__, e__, f__], x_)
                && integerq!(&m_ / 2)
                && integerq!(p_)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let z = Atom::var(sub);
            let angle = &e__ + &f__ * x_;
            let tan = angle.tan();
            let ff = rubi_free_factors(&tan, x_);
            let transformed = z.pow(&m_)
                * (&a__
                    + Atom::num(2) * &a__ * ff.pow(2) * z.pow(2)
                    + (&a__ + &b__) * ff.pow(4) * z.pow(4))
                .pow(&p_)
                / (Atom::num(1) + ff.pow(2) * z.pow(2)).pow(&m_ / 2 + Atom::num(2) * &p_ + 1);
            let primitive = rubi_rhs_int(&transformed, sub);

            rubi_star(ff.pow(&m_ + 1) / &f__, rubi_subst(&primitive, sub, tan / &ff))
        },
    ));
}

fn push_rules_rule_3697(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3697,
        source: "Int[sin[e_.+f_.*x_]^m_*(a_+b_.*sin[e_.+f_.*x_]^n_)^p_.,x_Symbol] :=
          With[{ff=FreeFactors[Tan[e+f*x],x]},
          ff^(m+1)/f \\[Star] Subst[Int[x^m*(a*(1+ff^2*x^2)^(n/2)+b*ff^n*x^n)^p/(1+ff^2*x^2)^(m/2+n*p/2+1),x],x,Tan[e+f*x]/ff]] /;
        FreeQ[{a,b,e,f},x] && IntegerQ[m/2] && IntegerQ[n/2] && IntegerQ[p]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_17(symbols),
        with: [a__, b__, e__, f__, m_, n_, p_, x_],
        optional: [b__, e__, f__, p_],
        when: {
            freeq!([a__, b__, e__, f__], x_)
                && integerq!(&m_ / 2)
                && integerq!(&n_ / 2)
                && integerq!(p_)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let z = Atom::var(sub);
            let angle = &e__ + &f__ * x_;
            let tan = angle.tan();
            let ff = rubi_free_factors(&tan, x_);
            let transformed = z.pow(&m_)
                * (&a__ * (Atom::num(1) + ff.pow(2) * z.pow(2)).pow(&n_ / 2)
                    + &b__ * ff.pow(&n_) * z.pow(&n_))
                .pow(&p_)
                / (Atom::num(1) + ff.pow(2) * z.pow(2)).pow(&m_ / 2 + &n_ * &p_ / 2 + 1);
            let primitive = rubi_rhs_int(&transformed, sub);

            rubi_star(ff.pow(&m_ + 1) / &f__, rubi_subst(&primitive, sub, tan / &ff))
        },
    ));
}

fn push_rules_rule_3698(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, e__, f__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 3698,
        source: "Int[sin[e_.+f_.*x_]^m_*(a_+b_.*sin[e_.+f_.*x_]^4)^p_,x_Symbol] :=
          With[{ff=FreeFactors[Tan[e+f*x],x]},
          ff^(m+1)*(a+b*Sin[e+f*x]^4)^p*(Sec[e+f*x]^2)^(2*p)/(f*Apart[a*(1+Tan[e+f*x]^2)^2+b*Tan[e+f*x]^4]^p) \\[Star]
            Subst[Int[x^m*ExpandToSum[a*(1+ff^2*x^2)^2+b*ff^4*x^4,x]^p/(1+ff^2*x^2)^(m/2+2*p+1),x],x,Tan[e+f*x]/ff]] /;
        FreeQ[{a,b,e,f,p},x] && IntegerQ[m/2] && IntegerQ[p-1/2]",
        desc: "Piecewise constant extraction and integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_16(symbols),
        with: [a__, b__, e__, f__, m_, p_, x_],
        optional: [b__, e__, f__],
        when: {
            freeq!([a__, b__, e__, f__, p_], x_)
                && integerq!(&m_ / 2)
                && integerq!(&p_ - Atom::num(1) / Atom::num(2))
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let z = Atom::var(sub);
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let tan = angle.tan();
            let sec = angle.sec();
            let ff = rubi_free_factors(&tan, x_);
            let apart =
                (&a__ * (Atom::num(1) + tan.pow(2)).pow(2) + &b__ * tan.pow(4)).apart(x_);
            let expand_to_sum = rubi_expand_to_sum(
                &(&a__ * (Atom::num(1) + ff.pow(2) * z.pow(2)).pow(2)
                    + &b__ * ff.pow(4) * z.pow(4)),
                sub,
            );
            let transformed = z.pow(&m_) * expand_to_sum.pow(&p_)
                / (Atom::num(1) + ff.pow(2) * z.pow(2))
                    .pow(&m_ / 2 + Atom::num(2) * &p_ + 1);
            let primitive = rubi_rhs_int(&transformed, sub);

            rubi_star(ff.pow(&m_ + 1)
                    * (&a__ + &b__ * sin.pow(4)).pow(&p_)
                    * sec.pow(2).pow(Atom::num(2) * &p_)
                    / (&f__ * apart.pow(&p_)), rubi_subst(&primitive, sub, tan / &ff))
        },
    ));
}

fn push_rules_rule_3699(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3699,
        source: "Int[sin[e_.+f_.*x_]^m_.*(a_+b_.*sin[e_.+f_.*x_]^n_)^p_.,x_Symbol] :=
          Int[ExpandTrig[sin[e+f*x]^m*(a+b*sin[e+f*x]^n)^p,x],x] /;
        FreeQ[{a,b,e,f},x] && IntegersQ[m,p] && (EqQ[n,4] || GtQ[p,0] || EqQ[p,-1] && IntegerQ[n])",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_17(symbols),
        with: [a__, b__, e__, f__, m_, n_, p_, x_],
        optional: [b__, e__, f__, m_, p_],
        when: {
            freeq!([a__, b__, e__, f__], x_)
                && integersq!([m_, p_])
                && (eqq!(n_, 4) || gtq!(p_, 0) || eqq!(p_, -1) && integerq!(n_))
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let payload = i_sin(&angle).pow(&m_) * (&a__ + &b__ * i_sin(&angle).pow(&n_)).pow(&p_);
            let expanded = rubi_expand_trig(&payload, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_3700(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3700,
        source: "Int[(d_.*sin[e_.+f_.*x_])^m_.*(a_+b_.*(c_.*sin[e_.+f_.*x_])^n_)^p_.,x_Symbol] :=
          Int[ExpandTrig[(d*sin[e+f*x])^m*(a+b*(c*sin[e+f*x])^n)^p,x],x] /;
        FreeQ[{a,b,c,d,e,f,m,n},x] && IGtQ[p,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [a__, b__, c__, d__, e__, f__, m_, n_, p_, x_],
        optional: [d__, b__, c__, e__, f__, m_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_], x_) && igtq!(p_, 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let payload =
                (&d__ * i_sin(&angle)).pow(&m_) * (&a__ + &b__ * (&c__ * i_sin(&angle)).pow(&n_)).pow(&p_);
            let expanded = rubi_expand_trig(&payload, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_3701(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3701,
        source: "Int[(d_.*sin[e_.+f_.*x_])^m_.*(a_+b_.*(c_.*sin[e_.+f_.*x_])^n_)^p_.,x_Symbol] :=
          Unintegrable[(d*Sin[e+f*x])^m*(a+b*(c*Sin[e+f*x])^n)^p,x] /;
        FreeQ[{a,b,c,d,e,f,m,n,p},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [a__, b__, c__, d__, e__, f__, m_, n_, p_, x_],
        optional: [d__, b__, c__, e__, f__, m_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_, p_], x_)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;

            rubi_unintegrable(
                (&d__ * i_sin(&angle)).pow(&m_)
                    * (&a__ + &b__ * (&c__ * i_sin(&angle)).pow(&n_)).pow(&p_),
                x_,
            )
        },
    ));
}

fn push_rules_rule_3702(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3702,
        source: "Int[cos[e_.+f_.*x_]^m_.*(a_+b_.*(c_.*sin[e_.+f_.*x_])^n_)^p_.,x_Symbol] :=
          With[{ff=FreeFactors[Sin[e+f*x],x]},
          ff/f \\[Star] Subst[Int[(1-ff^2*x^2)^((m-1)/2)*(a+b*(c*ff*x)^n)^p,x],x,Sin[e+f*x]/ff]] /;
        FreeQ[{a,b,c,e,f,n,p},x] && IntegerQ[(m-1)/2] && (EqQ[n,4] || GtQ[m,0] || IGtQ[p,0] || IntegersQ[m,p])",
        desc: "Integration by substitution",
        refs: [],
        pattern: i_cos(e__ + f__ * x_).pow(m_)
            * (a__ + b__ * (c__ * i_sin(e__ + f__ * x_)).pow(n_)).pow(p_),
        with: [a__, b__, c__, e__, f__, m_, n_, p_, x_],
        optional: [b__, c__, e__, f__, m_, p_],
        when: {
            freeq!([a__, b__, c__, e__, f__, n_, p_], x_)
                && integerq!((&m_ - 1) / 2)
                && (eqq!(n_, 4) || gtq!(m_, 0) || igtq!(p_, 0) || integersq!([m_, p_]))
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let z = Atom::var(sub);
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let ff = rubi_free_factors(&sin, x_);
            let transformed = (Atom::num(1) - ff.pow(2) * z.pow(2)).pow((&m_ - 1) / 2)
                * (&a__ + &b__ * (&c__ * &ff * &z).pow(&n_)).pow(&p_);
            let primitive = rubi_rhs_int(&transformed, sub);

            rubi_star(&ff / &f__, rubi_subst(&primitive, sub, sin / &ff))
        },
    ));
}

fn push_rules_rule_3703(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, e__, f__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 3703,
        source: "Int[cos[e_.+f_.*x_]^m_*(a_+b_.*sin[e_.+f_.*x_]^4)^p_.,x_Symbol] :=
          With[{ff=FreeFactors[Tan[e+f*x],x]},
          ff/f \\[Star] Subst[Int[(a+2*a*ff^2*x^2+(a+b)*ff^4*x^4)^p/(1+ff^2*x^2)^(m/2+2*p+1),x],x,Tan[e+f*x]/ff]] /;
        FreeQ[{a,b,e,f},x] && IntegerQ[m/2] && IntegerQ[p]",
        desc: "Integration by substitution",
        refs: [],
        pattern: i_cos(e__ + f__ * x_).pow(m_)
            * (a__ + b__ * i_sin(e__ + f__ * x_).pow(4)).pow(p_),
        with: [a__, b__, e__, f__, m_, p_, x_],
        optional: [b__, e__, f__, p_],
        when: {
            freeq!([a__, b__, e__, f__], x_)
                && integerq!(&m_ / 2)
                && integerq!(p_)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let z = Atom::var(sub);
            let angle = &e__ + &f__ * x_;
            let tan = angle.tan();
            let ff = rubi_free_factors(&tan, x_);
            let transformed = (&a__
                + Atom::num(2) * &a__ * ff.pow(2) * z.pow(2)
                + (&a__ + &b__) * ff.pow(4) * z.pow(4))
            .pow(&p_)
                / (Atom::num(1) + ff.pow(2) * z.pow(2)).pow(&m_ / 2 + Atom::num(2) * &p_ + 1);
            let primitive = rubi_rhs_int(&transformed, sub);

            rubi_star(&ff / &f__, rubi_subst(&primitive, sub, tan / &ff))
        },
    ));
}

fn push_rules_rule_3704(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3704,
        source: "Int[cos[e_.+f_.*x_]^m_*(a_+b_.*sin[e_.+f_.*x_]^n_)^p_.,x_Symbol] :=
          With[{ff=FreeFactors[Tan[e+f*x],x]},
          ff/f \\[Star] Subst[Int[(b*ff^n*x^n+a*(1+ff^2*x^2)^(n/2))^p/(1+ff^2*x^2)^(m/2+n*p/2+1),x],x,Tan[e+f*x]/ff]] /;
        FreeQ[{a,b,e,f},x] && IntegerQ[m/2] && IntegerQ[n/2] && IntegerQ[p]",
        desc: "Integration by substitution",
        refs: [],
        pattern: i_cos(e__ + f__ * x_).pow(m_)
            * (a__ + b__ * i_sin(e__ + f__ * x_).pow(n_)).pow(p_),
        with: [a__, b__, e__, f__, m_, n_, p_, x_],
        optional: [b__, e__, f__, p_],
        when: {
            freeq!([a__, b__, e__, f__], x_)
                && integerq!(&m_ / 2)
                && integerq!(&n_ / 2)
                && integerq!(p_)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let z = Atom::var(sub);
            let angle = &e__ + &f__ * x_;
            let tan = angle.tan();
            let ff = rubi_free_factors(&tan, x_);
            let transformed = (&b__ * ff.pow(&n_) * z.pow(&n_)
                + &a__ * (Atom::num(1) + ff.pow(2) * z.pow(2)).pow(&n_ / 2))
            .pow(&p_)
                / (Atom::num(1) + ff.pow(2) * z.pow(2)).pow(&m_ / 2 + &n_ * &p_ / 2 + 1);
            let primitive = rubi_rhs_int(&transformed, sub);

            rubi_star(&ff / &f__, rubi_subst(&primitive, sub, tan / &ff))
        },
    ));
}

fn push_rules_rule_3705(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 3705,
        source: "Int[cos[e_.+f_.*x_]^m_/(a_+b_.*sin[e_.+f_.*x_]^n_),x_Symbol] :=
          Int[Expand[(1-Sin[e+f*x]^2)^(m/2)/(a+b*Sin[e+f*x]^n),x],x] /;
        FreeQ[{a,b,e,f},x] && IGtQ[m/2,0] && IntegerQ[(n-1)/2]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: i_cos(e__ + f__ * x_).pow(m_) / (a__ + b__ * i_sin(e__ + f__ * x_).pow(n_)),
        with: [a__, b__, e__, f__, m_, n_, x_],
        optional: [b__, e__, f__],
        when: {
            freeq!([a__, b__, e__, f__], x_)
                && igtq!(&m_ / 2, 0)
                && integerq!((&n_ - 1) / 2)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let expanded = rubi_expand(
                &((Atom::num(1) - sin.pow(2)).pow(&m_ / 2)
                    / (&a__ + &b__ * sin.pow(&n_))),
                x_,
            );

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_3706(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3706,
        source: "Int[(d_.*cos[e_.+f_.*x_])^m_.*(a_+b_.*(c_.*sin[e_.+f_.*x_])^n_)^p_.,x_Symbol] :=
          Int[ExpandTrig[(d*cos[e+f*x])^m*(a+b*(c*sin[e+f*x])^n)^p,x],x] /;
        FreeQ[{a,b,c,d,e,f,m,n},x] && IGtQ[p,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [a__, b__, c__, d__, e__, f__, m_, n_, p_, x_],
        optional: [d__, b__, c__, e__, f__, m_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_], x_) && igtq!(p_, 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let payload =
                (&d__ * i_cos(&angle)).pow(&m_) * (&a__ + &b__ * (&c__ * i_sin(&angle)).pow(&n_)).pow(&p_);
            let expanded = rubi_expand_trig(&payload, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_3707(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3707,
        source: "Int[(d_.*cos[e_.+f_.*x_])^m_.*(a_+b_.*(c_.*sin[e_.+f_.*x_])^n_)^p_.,x_Symbol] :=
          Unintegrable[(d*Cos[e+f*x])^m*(a+b*(c*Sin[e+f*x])^n)^p,x] /;
        FreeQ[{a,b,c,d,e,f,m,n,p},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [a__, b__, c__, d__, e__, f__, m_, n_, p_, x_],
        optional: [d__, b__, c__, e__, f__, m_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_, p_], x_)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;

            rubi_unintegrable(
                (&d__ * i_cos(&angle)).pow(&m_)
                    * (&a__ + &b__ * (&c__ * i_sin(&angle)).pow(&n_)).pow(&p_),
                x_,
            )
        },
    ));
}

fn push_rules_rule_3708(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3708,
        source: "Int[tan[e_.+f_.*x_]^m_.*(a_+b_.*sin[e_.+f_.*x_]^n_)^p_.,x_Symbol] :=
          With[{ff=FreeFactors[Sin[e+f*x]^2,x]},
          ff^((m+1)/2)/(2*f) \\[Star] Subst[Int[x^((m-1)/2)*(a+b*ff^(n/2)*x^(n/2))^p/(1-ff*x)^((m+1)/2),x],x,Sin[e+f*x]^2/ff]] /;
        FreeQ[{a,b,e,f,p},x] && IntegerQ[(m-1)/2] && IntegerQ[n/2]",
        desc: "Integration by substitution",
        refs: [],
        pattern: i_tan(e__ + f__ * x_).pow(m_)
            * (a__ + b__ * i_sin(e__ + f__ * x_).pow(n_)).pow(p_),
        with: [a__, b__, e__, f__, m_, n_, p_, x_],
        optional: [b__, e__, f__, m_, p_],
        when: {
            freeq!([a__, b__, e__, f__, p_], x_)
                && integerq!((&m_ - 1) / 2)
                && integerq!(&n_ / 2)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let z = Atom::var(sub);
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let ff = rubi_free_factors(&sin.pow(2), x_);
            let transformed = z.pow((&m_ - 1) / 2)
                * (&a__ + &b__ * ff.pow(&n_ / 2) * z.pow(&n_ / 2)).pow(&p_)
                / (Atom::num(1) - &ff * &z).pow((&m_ + 1) / 2);
            let primitive = rubi_rhs_int(&transformed, sub);

            rubi_star(ff.pow((&m_ + 1) / 2) / (Atom::num(2) * &f__), rubi_subst(&primitive, sub, sin.pow(2) / &ff))
        },
    ));
}

fn push_rules_rule_3709(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3709,
        source: "Int[tan[e_.+f_.*x_]^m_.*(a_+b_.*(c_.*sin[e_.+f_.*x_])^n_)^p_.,x_Symbol] :=
          With[{ff=FreeFactors[Sin[e+f*x],x]},
          ff^(m+1)/f \\[Star] Subst[Int[x^m*(a+b*(c*ff*x)^n)^p/(1-ff^2*x^2)^((m+1)/2),x],x,Sin[e+f*x]/ff]] /;
        FreeQ[{a,b,c,e,f,n,p},x] && ILtQ[(m-1)/2,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: i_tan(e__ + f__ * x_).pow(m_)
            * (a__ + b__ * (c__ * i_sin(e__ + f__ * x_)).pow(n_)).pow(p_),
        with: [a__, b__, c__, e__, f__, m_, n_, p_, x_],
        optional: [b__, c__, e__, f__, m_, p_],
        when: {
            freeq!([a__, b__, c__, e__, f__, n_, p_], x_)
                && iltq!((&m_ - 1) / 2, 0)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let z = Atom::var(sub);
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let ff = rubi_free_factors(&sin, x_);
            let transformed = z.pow(&m_) * (&a__ + &b__ * (&c__ * &ff * &z).pow(&n_)).pow(&p_)
                / (Atom::num(1) - ff.pow(2) * z.pow(2)).pow((&m_ + 1) / 2);
            let primitive = rubi_rhs_int(&transformed, sub);

            rubi_star(ff.pow(&m_ + 1) / &f__, rubi_subst(&primitive, sub, sin / &ff))
        },
    ));
}

fn push_rules_rule_3710(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, e__, f__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 3710,
        source: "Int[(d_.*tan[e_.+f_.*x_])^m_*(a_+b_.*sin[e_.+f_.*x_]^4)^p_.,x_Symbol] :=
          With[{ff=FreeFactors[Tan[e+f*x],x]},
          ff/f \\[Star] Subst[Int[(d*ff*x)^m*ExpandToSum[a*(1+ff^2*x^2)^2+b*ff^4*x^4,x]^p/(1+ff^2*x^2)^(2*p+1),x],x,Tan[e+f*x]/ff]] /;
        FreeQ[{a,b,d,e,f,m},x] && IntegerQ[p]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_11(symbols),
        with: [a__, b__, d__, e__, f__, m_, p_, x_],
        optional: [d__, b__, e__, f__, p_],
        when: {
            freeq!([a__, b__, d__, e__, f__, m_], x_) && integerq!(p_)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let z = Atom::var(sub);
            let angle = &e__ + &f__ * x_;
            let tan = angle.tan();
            let ff = rubi_free_factors(&tan, x_);
            let expand_to_sum = rubi_expand_to_sum(
                &(&a__ * (Atom::num(1) + ff.pow(2) * z.pow(2)).pow(2)
                    + &b__ * ff.pow(4) * z.pow(4)),
                sub,
            );
            let transformed = (&d__ * &ff * &z).pow(&m_) * expand_to_sum.pow(&p_)
                / (Atom::num(1) + ff.pow(2) * z.pow(2)).pow(Atom::num(2) * &p_ + 1);
            let primitive = rubi_rhs_int(&transformed, sub);

            rubi_star(&ff / &f__, rubi_subst(&primitive, sub, tan / &ff))
        },
    ));
}

fn push_rules_rule_3711(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, e__, f__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 3711,
        source: "Int[(d_.*tan[e_.+f_.*x_])^m_*(a_+b_.*sin[e_.+f_.*x_]^4)^p_,x_Symbol] :=
          With[{ff=FreeFactors[Tan[e+f*x],x]},
          ff*(a+b*Sin[e+f*x]^4)^p*(Sec[e+f*x]^2)^(2*p)/(f*Apart[a*(1+Tan[e+f*x]^2)^2+b*Tan[e+f*x]^4]^p) \\[Star]
            Subst[Int[(d*ff*x)^m*ExpandToSum[a*(1+ff^2*x^2)^2+b*ff^4*x^4,x]^p/(1+ff^2*x^2)^(2*p+1),x],x,Tan[e+f*x]/ff]] /;
        FreeQ[{a,b,d,e,f,m},x] && IntegerQ[p-1/2]",
        desc: "Piecewise constant extraction and integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_11(symbols),
        with: [a__, b__, d__, e__, f__, m_, p_, x_],
        optional: [d__, b__, e__, f__],
        when: {
            freeq!([a__, b__, d__, e__, f__, m_], x_)
                && integerq!(&p_ - Atom::num(1) / Atom::num(2))
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let z = Atom::var(sub);
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let tan = angle.tan();
            let sec = angle.sec();
            let ff = rubi_free_factors(&tan, x_);
            let apart =
                (&a__ * (Atom::num(1) + tan.pow(2)).pow(2) + &b__ * tan.pow(4)).apart(x_);
            let expand_to_sum = rubi_expand_to_sum(
                &(&a__ * (Atom::num(1) + ff.pow(2) * z.pow(2)).pow(2)
                    + &b__ * ff.pow(4) * z.pow(4)),
                sub,
            );
            let transformed = (&d__ * &ff * &z).pow(&m_) * expand_to_sum.pow(&p_)
                / (Atom::num(1) + ff.pow(2) * z.pow(2)).pow(Atom::num(2) * &p_ + 1);
            let primitive = rubi_rhs_int(&transformed, sub);

            rubi_star(&ff
                    * (&a__ + &b__ * sin.pow(4)).pow(&p_)
                    * sec.pow(2).pow(Atom::num(2) * &p_)
                    / (&f__ * apart.pow(&p_)), rubi_subst(&primitive, sub, tan / &ff))
        },
    ));
}

fn push_rules_rule_3712(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3712,
        source: "Int[(d_.*tan[e_.+f_.*x_])^m_*(a_+b_.*sin[e_.+f_.*x_]^n_)^p_.,x_Symbol] :=
          With[{ff=FreeFactors[Tan[e+f*x],x]},
          ff^(m+1)/f \\[Star] Subst[Int[(d*x)^m*(b*ff^n*x^n+a*(1+ff^2*x^2)^(n/2))^p/(1+ff^2*x^2)^(n*p/2+1),x],x,Tan[e+f*x]/ff]] /;
        FreeQ[{a,b,d,e,f,m},x] && IntegerQ[n/2] && IGtQ[p,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (d__ * i_tan(e__ + f__ * x_)).pow(m_)
            * (a__ + b__ * i_sin(e__ + f__ * x_).pow(n_)).pow(p_),
        with: [a__, b__, d__, e__, f__, m_, n_, p_, x_],
        optional: [d__, b__, e__, f__, p_],
        when: {
            freeq!([a__, b__, d__, e__, f__, m_], x_)
                && integerq!(&n_ / 2)
                && igtq!(p_, 0)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let z = Atom::var(sub);
            let angle = &e__ + &f__ * x_;
            let tan = angle.tan();
            let ff = rubi_free_factors(&tan, x_);
            let transformed = (&d__ * &z).pow(&m_)
                * (&b__ * ff.pow(&n_) * z.pow(&n_)
                    + &a__ * (Atom::num(1) + ff.pow(2) * z.pow(2)).pow(&n_ / 2))
                .pow(&p_)
                / (Atom::num(1) + ff.pow(2) * z.pow(2)).pow(&n_ * &p_ / 2 + 1);
            let primitive = rubi_rhs_int(&transformed, sub);

            rubi_star(ff.pow(&m_ + 1) / &f__, rubi_subst(&primitive, sub, tan / &ff))
        },
    ));
}

fn push_rules_rule_3713(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3713,
        source: "Int[(d_.*tan[e_.+f_.*x_])^m_.*(a_+b_.*(c_.*sin[e_.+f_.*x_])^n_)^p_.,x_Symbol] :=
          Int[ExpandTrig[(d*tan[e+f*x])^m*(a+b*(c*sin[e+f*x])^n)^p,x],x] /;
        FreeQ[{a,b,c,d,e,f,m,n},x] && IGtQ[p,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [a__, b__, c__, d__, e__, f__, m_, n_, p_, x_],
        optional: [d__, b__, c__, e__, f__, m_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_], x_) && igtq!(p_, 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let payload =
                (&d__ * i_tan(&angle)).pow(&m_) * (&a__ + &b__ * (&c__ * i_sin(&angle)).pow(&n_)).pow(&p_);
            let expanded = rubi_expand_trig(&payload, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_3714(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3714,
        source: "Int[(d_.*tan[e_.+f_.*x_])^m_.*(a_+b_.*(c_.*sin[e_.+f_.*x_])^n_)^p_.,x_Symbol] :=
          Unintegrable[(d*Tan[e+f*x])^m*(a+b*(c*Sin[e+f*x])^n)^p,x] /;
        FreeQ[{a,b,c,d,e,f,m,n,p},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [a__, b__, c__, d__, e__, f__, m_, n_, p_, x_],
        optional: [d__, b__, c__, e__, f__, m_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_, p_], x_)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;

            rubi_unintegrable(
                (&d__ * i_tan(&angle)).pow(&m_)
                    * (&a__ + &b__ * (&c__ * i_sin(&angle)).pow(&n_)).pow(&p_),
                x_,
            )
        },
    ));
}

fn push_rules_rule_3715(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3715,
        source: "Int[(d_.*cot[e_.+f_.*x_])^m_*(a_+b_.*(c_.*sin[e_.+f_.*x_])^n_)^p_,x_Symbol] :=
          (d*Cot[e+f*x])^FracPart[m]*(Tan[e+f*x]/d)^FracPart[m] \\[Star] Int[(Tan[e+f*x]/d)^(-m)*(a+b*(c*Sin[e+f*x])^n)^p,x] /;
        FreeQ[{a,b,c,d,e,f,m,n,p},x] && Not[IntegerQ[m]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: (d__ * i_cot(e__ + f__ * x_)).pow(m_)
            * (a__ + b__ * (c__ * i_sin(e__ + f__ * x_)).pow(n_)).pow(p_),
        with: [a__, b__, c__, d__, e__, f__, m_, n_, p_, x_],
        optional: [d__, b__, c__, e__, f__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_, p_], x_)
                && !integerq!(m_)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let frac_part = rubi_frac_part(&m_);
            let recursive = rubi_rhs_int(
                &((angle.tan() / &d__).pow(-&m_)
                    * (&a__ + &b__ * (&c__ * angle.sin()).pow(&n_)).pow(&p_)),
                x_,
            );

            rubi_star((&d__ * angle.cot()).pow(&frac_part)
                    * (angle.tan() / &d__).pow(frac_part), recursive)
        },
    ));
}

fn push_rules_rule_3716(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3716,
        source: "Int[(d_.*sec[e_.+f_.*x_])^m_*(a_+b_.*(c_.*sin[e_.+f_.*x_])^n_)^p_,x_Symbol] :=
          (d*Sec[e+f*x])^FracPart[m]*(Cos[e+f*x]/d)^FracPart[m] \\[Star] Int[(Cos[e+f*x]/d)^(-m)*(a+b*(c*Sin[e+f*x])^n)^p,x] /;
        FreeQ[{a,b,c,d,e,f,m,n,p},x] && Not[IntegerQ[m]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: (d__ * i_sec(e__ + f__ * x_)).pow(m_)
            * (a__ + b__ * (c__ * i_sin(e__ + f__ * x_)).pow(n_)).pow(p_),
        with: [a__, b__, c__, d__, e__, f__, m_, n_, p_, x_],
        optional: [d__, b__, c__, e__, f__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_, p_], x_)
                && !integerq!(m_)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let frac_part = rubi_frac_part(&m_);
            let recursive = rubi_rhs_int(
                &((angle.cos() / &d__).pow(-&m_)
                    * (&a__ + &b__ * (&c__ * angle.sin()).pow(&n_)).pow(&p_)),
                x_,
            );

            rubi_star((&d__ * angle.sec()).pow(&frac_part)
                    * (angle.cos() / &d__).pow(frac_part), recursive)
        },
    ));
}

fn push_rules_rule_3717(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3717,
        source: "Int[(d_.*csc[e_.+f_.*x_])^m_*(a_+b_.*sin[e_.+f_.*x_]^n_.)^p_.,x_Symbol] :=
          d^(n*p) \\[Star] Int[(d*Csc[e+f*x])^(m-n*p)*(b+a*Csc[e+f*x]^n)^p,x] /;
        FreeQ[{a,b,d,e,f,m,n,p},x] && Not[IntegerQ[m]] && IntegersQ[n,p]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: (d__ * i_csc(e__ + f__ * x_)).pow(m_)
            * (a__ + b__ * i_sin(e__ + f__ * x_).pow(n_)).pow(p_),
        with: [a__, b__, d__, e__, f__, m_, n_, p_, x_],
        optional: [d__, b__, e__, f__, n_, p_],
        when: {
            freeq!([a__, b__, d__, e__, f__, m_, n_, p_], x_)
                && !integerq!(m_)
                && integersq!([n_, p_])
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let recursive = rubi_rhs_int(
                &((&d__ * angle.csc()).pow(&m_ - &n_ * &p_)
                    * (&b__ + &a__ * angle.csc().pow(&n_)).pow(&p_)),
                x_,
            );

            rubi_star(d__.pow(&n_ * &p_), recursive)
        },
    ));
}

fn push_rules_rule_3718(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3718,
        source: "Int[(d_.*csc[e_.+f_.*x_])^m_*(a_+b_.*(c_.*sin[e_.+f_.*x_])^n_)^p_,x_Symbol] :=
          (d*Csc[e+f*x])^FracPart[m]*(Sin[e+f*x]/d)^FracPart[m] \\[Star] Int[(Sin[e+f*x]/d)^(-m)*(a+b*(c*Sin[e+f*x])^n)^p,x] /;
        FreeQ[{a,b,c,d,e,f,m,n,p},x] && Not[IntegerQ[m]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: (d__ * i_csc(e__ + f__ * x_)).pow(m_)
            * (a__ + b__ * (c__ * i_sin(e__ + f__ * x_)).pow(n_)).pow(p_),
        with: [a__, b__, c__, d__, e__, f__, m_, n_, p_, x_],
        optional: [d__, b__, c__, e__, f__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_, p_], x_)
                && !integerq!(m_)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let frac_part = rubi_frac_part(&m_);
            let recursive = rubi_rhs_int(
                &((angle.sin() / &d__).pow(-&m_)
                    * (&a__ + &b__ * (&c__ * angle.sin()).pow(&n_)).pow(&p_)),
                x_,
            );

            rubi_star((&d__ * angle.csc()).pow(&frac_part)
                    * (angle.sin() / &d__).pow(frac_part), recursive)
        },
    ));
}

fn push_rules_rule_3719(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, p_, x_);
    rules.push(rubi_rule!(
        order: 3719,
        source: "Int[(a_+b_.*(c_.*sin[e_.+f_.*x_]+d_.*cos[e_.+f_.*x_])^2)^p_,x_Symbol] :=
          Int[(a+b*(Sqrt[c^2+d^2]*Sin[ArcTan[c,d]+e+f*x])^2)^p,x] /;
        FreeQ[{a,b,c,d,e,f},x] && EqQ[p^2,1/4] && GtQ[a,0]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, e__, f__, p_, x_],
        optional: [b__, c__, d__, e__, f__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_) && eqq!(p_.pow(2), Atom::num(1) / Atom::num(4)) && gtq!(a__, 0)
        },
        rhs: {
            let arc_tan = symbol!("ArcTan").call((&c__, &d__));
            let shifted_sin = (arc_tan + &e__ + &f__ * x_).sin();
            let payload =
                (&a__ + &b__ * ((c__.pow(2) + d__.pow(2)).sqrt() * shifted_sin).pow(2)).pow(&p_);

            rubi_rhs_int(&payload, x_)
        },
    ));
}

fn push_rules_rule_3720(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, p_, x_);
    rules.push(rubi_rule!(
        order: 3720,
        source: "Int[(a_+b_.*(c_.*sin[e_.+f_.*x_]+d_.*cos[e_.+f_.*x_])^2)^p_,x_Symbol] :=
          (a+b*(c*Sin[e+f*x]+d*Cos[e+f*x])^2)^p/(1+(b*(c*Sin[e+f*x]+d*Cos[e+f*x])^2)/a)^p \\[Star]
            Int[(1+(b*(c*Sin[e+f*x]+d*Cos[e+f*x])^2)/a)^p,x] /;
        FreeQ[{a,b,c,d,e,f},x] && EqQ[p^2,1/4] && Not[GtQ[a,0]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, e__, f__, p_, x_],
        optional: [b__, c__, d__, e__, f__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_) && eqq!(p_.pow(2), Atom::num(1) / Atom::num(4)) && !gtq!(a__, 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let linear_trig = &c__ * angle.sin() + &d__ * angle.cos();
            let base = &a__ + &b__ * linear_trig.pow(2);
            let normalized = Atom::num(1) + &b__ * linear_trig.pow(2) / &a__;
            let recursive = rubi_rhs_int(&normalized.pow(&p_), x_);

            rubi_star(base.pow(&p_) / normalized.pow(&p_), recursive)
        },
    ));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn downvalues_3648_through_3692_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .filter(|order| (3648..=3692).contains(order))
            .collect::<Vec<_>>();
        assert_eq!(orders, (3648..=3692).collect::<Vec<_>>());
    }

    #[test]
    fn downvalues_3693_through_3720_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .filter(|order| (3693..=3720).contains(order))
            .collect::<Vec<_>>();
        assert_eq!(orders, (3693..=3720).collect::<Vec<_>>());
    }
}

// Generated shared pattern builders.

#[inline(never)]
fn rubi_shared_pattern_0(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (a__ + b__ * (c__ * i_sin(e__ + f__ * x_)).pow(n_)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (a__ + b__ * (c__ * i_sin(e__ + f__ * x_) + d__ * i_cos(e__ + f__ * x_)).pow(2)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_2(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (a__ + b__ * i_sin(e__ + f__ * x_).pow(2)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_3(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let capital_a__ = symbols.capital_a__;
    let capital_b__ = symbols.capital_b__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (a__ + b__ * i_sin(e__ + f__ * x_).pow(2)).pow(p_)
        * (capital_a__ + capital_b__ * i_sin(e__ + f__ * x_).pow(2))
}

#[inline(never)]
fn rubi_shared_pattern_4(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let x_ = symbols.x_;
    (a__ + b__ * i_sin(e__ + f__ * x_).pow(2)).sqrt()
}

#[inline(never)]
fn rubi_shared_pattern_5(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (a__ + b__ * i_sin(e__ + f__ * x_).pow(4)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_6(symbols: &RubiSymbols) -> Atom {
    let b__ = symbols.b__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (b__ * i_sin(e__ + f__ * x_).pow(2)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_7(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (d__ * i_cos(e__ + f__ * x_)).pow(m_)
        * (a__ + b__ * (c__ * i_sin(e__ + f__ * x_)).pow(n_)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_8(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (d__ * i_sin(e__ + f__ * x_)).pow(m_)
        * (a__ + b__ * (c__ * i_sin(e__ + f__ * x_)).pow(n_)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_9(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (d__ * i_tan(e__ + f__ * x_)).pow(m_)
        * (a__ + b__ * (c__ * i_sin(e__ + f__ * x_)).pow(n_)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_10(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (d__ * i_tan(e__ + f__ * x_)).pow(m_) * (a__ + b__ * i_sin(e__ + f__ * x_).pow(2)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_11(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (d__ * i_tan(e__ + f__ * x_)).pow(m_) * (a__ + b__ * i_sin(e__ + f__ * x_).pow(4)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_12(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let x_ = symbols.x_;
    Atom::num(1) / (a__ + b__ * i_sin(e__ + f__ * x_).pow(2)).sqrt()
}

#[inline(never)]
fn rubi_shared_pattern_13(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    i_cos(e__ + f__ * x_).pow(m_) * (a__ + b__ * i_sin(e__ + f__ * x_).pow(2)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_14(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    i_cos(e__ + f__ * x_).pow(m_)
        * (d__ * i_sin(e__ + f__ * x_)).pow(n_)
        * (a__ + b__ * i_sin(e__ + f__ * x_).pow(2)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_15(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    i_sin(e__ + f__ * x_).pow(m_) * (a__ + b__ * i_sin(e__ + f__ * x_).pow(2)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_16(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    i_sin(e__ + f__ * x_).pow(m_) * (a__ + b__ * i_sin(e__ + f__ * x_).pow(4)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_17(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    i_sin(e__ + f__ * x_).pow(m_) * (a__ + b__ * i_sin(e__ + f__ * x_).pow(n_)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_18(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    i_tan(e__ + f__ * x_).pow(m_) * (a__ + b__ * i_sin(e__ + f__ * x_).pow(2)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_19(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let p_ = symbols.p_;
    let u__ = symbols.u__;
    let x_ = symbols.x_;
    u__ * (a__ + b__ * i_sin(e__ + f__ * x_).pow(2)).pow(p_)
}
