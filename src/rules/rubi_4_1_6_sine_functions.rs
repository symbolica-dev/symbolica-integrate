use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_3591(rules);
    push_rules_rule_3592(rules);
    push_rules_rule_3593(rules);
    push_rules_rule_3594(rules);
    push_rules_rule_3595(rules);
    push_rules_rule_3596(rules);
    push_rules_rule_3597(rules);
    push_rules_rule_3598(rules);
    push_rules_rule_3599(rules);
    push_rules_rule_3600(rules);
    push_rules_rule_3601(rules);
    push_rules_rule_3602(rules);
    push_rules_rule_3603(rules);
    push_rules_rule_3604(rules);
    push_rules_rule_3605(rules);
    push_rules_rule_3606(rules);
    push_rules_rule_3607(rules);
    push_rules_rule_3608(rules);
    push_rules_rule_3609(rules);
    push_rules_rule_3610(rules);
    push_rules_rule_3611(rules);
    push_rules_rule_3612(rules);
    push_rules_rule_3613(rules);
    push_rules_rule_3614(rules);
    push_rules_rule_3615(rules);
    push_rules_rule_3616(rules);
    push_rules_rule_3617(rules);
    push_rules_rule_3618(rules);
    push_rules_rule_3619(rules);
    push_rules_rule_3620(rules);
    push_rules_rule_3621(rules);
    push_rules_rule_3622(rules);
    push_rules_rule_3623(rules);
    push_rules_rule_3624(rules);
    push_rules_rule_3625(rules);
    push_rules_rule_3626(rules);
    push_rules_rule_3627(rules);
    push_rules_rule_3628(rules);
    push_rules_rule_3629(rules);
    push_rules_rule_3630(rules);
    push_rules_rule_3631(rules);
    push_rules_rule_3632(rules);
    push_rules_rule_3633(rules);
    push_rules_rule_3634(rules);
    push_rules_rule_3635(rules);
    push_rules_rule_3636(rules);
    push_rules_rule_3637(rules);
    push_rules_rule_3638(rules);
    push_rules_rule_3639(rules);
    push_rules_rule_3640(rules);
    push_rules_rule_3641(rules);
    push_rules_rule_3642(rules);
    push_rules_rule_3643(rules);
    push_rules_rule_3644(rules);
    push_rules_rule_3645(rules);
    push_rules_rule_3646(rules);
    push_rules_rule_3647(rules);
}

fn push_rules_rule_3591(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 3591,
        source: "Int[Sqrt[a_+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_]],x_Symbol] :=
          -2*(c*Cos[d+e*x]-b*Sin[d+e*x])/(e*Sqrt[a+b*Cos[d+e*x]+c*Sin[d+e*x]]) /;
        FreeQ[{a,b,c,d,e},x] && EqQ[a^2-b^2-c^2,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: ["G&R 2.558.1 inverted with n\\[Equal]12 and a2-b2-c2\\[Equal]0"],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, e__, x_],
        optional: [b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(a__.pow(2) - b__.pow(2) - c__.pow(2), 0)
        },
        rhs: {
            let angle = &d__ + &e__ * x_;
            let base = &a__ + &b__ * angle.cos() + &c__ * angle.sin();

            rubi_simp(&(-Atom::num(2) * (&c__ * angle.cos() - &b__ * angle.sin())
                    / (&e__ * base.sqrt())), x_)
        },
    ));
}

fn push_rules_rule_3592(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 3592,
        source: "Int[(a_+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_])^n_,x_Symbol] :=
          -(c*Cos[d+e*x]-b*Sin[d+e*x])*(a+b*Cos[d+e*x]+c*Sin[d+e*x])^(n-1)/(e*n) +
          a*(2*n-1)/n \\[Star] Int[(a+b*Cos[d+e*x]+c*Sin[d+e*x])^(n-1),x] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[a^2-b^2-c^2,0] && GtQ[n,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: ["G&R 2.558.1 inverted with a2-b2-c2\\[Equal]0"],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, e__, n_, x_],
        optional: [b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(a__.pow(2) - b__.pow(2) - c__.pow(2), 0)
                && gtq!(n_, 0)
        },
        rhs: {
            let angle = &d__ + &e__ * x_;
            let base = &a__ + &b__ * angle.cos() + &c__ * angle.sin();
            let recursive = rubi_rhs_int(&base.pow(&n_ - 1), x_);

            rubi_simp(&(-(&c__ * angle.cos() - &b__ * angle.sin()) * base.pow(&n_ - 1)
                    / (&e__ * &n_)), x_)
                    + rubi_star(&a__ * (Atom::num(2) * &n_ - 1) / &n_, recursive)
        },
    ));
}

fn push_rules_rule_3593(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 3593,
        source: "Int[1/(a_+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_]),x_Symbol] :=
          -(c-a*Sin[d+e*x])/(c*e*(c*Cos[d+e*x]-b*Sin[d+e*x])) /;
        FreeQ[{a,b,c,d,e},x] && EqQ[a^2-b^2-c^2,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: ["G&R 2.558.4d"],
        pattern:  rubi_shared_pattern_11(symbols),
        with: [a__, b__, c__, d__, e__, x_],
        optional: [b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(a__.pow(2) - b__.pow(2) - c__.pow(2), 0)
        },
        rhs: {
            let angle = &d__ + &e__ * x_;

            rubi_simp(&(-(&c__ - &a__ * angle.sin())
                    / (&c__ * &e__ * (&c__ * angle.cos() - &b__ * angle.sin()))), x_)
        },
    ));
}

fn push_rules_rule_3594(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 3594,
        source: "Int[1/Sqrt[a_+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_]],x_Symbol] :=
          Int[1/Sqrt[a+Sqrt[b^2+c^2]*Cos[d+e*x-ArcTan[b,c]]],x] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[a^2-b^2-c^2,0]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_12(symbols),
        with: [a__, b__, c__, d__, e__, x_],
        optional: [b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(a__.pow(2) - b__.pow(2) - c__.pow(2), 0)
        },
        rhs: {
            let angle = &d__ + &e__ * x_;
            let root = (b__.pow(2) + c__.pow(2)).sqrt();
            let arc_tan = symbol!("ArcTan").call((&b__, &c__));
            let recursive = rubi_rhs_int(
                &(Atom::num(1) / (&a__ + root * (angle - arc_tan).cos()).sqrt()),
                x_,
            );

            recursive
        },
    ));
}

fn push_rules_rule_3595(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 3595,
        source: "Int[(a_+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_])^n_,x_Symbol] :=
          (c*Cos[d+e*x]-b*Sin[d+e*x])*(a+b*Cos[d+e*x]+c*Sin[d+e*x])^n/(a*e*(2*n+1)) +
          (n+1)/(a*(2*n+1)) \\[Star] Int[(a+b*Cos[d+e*x]+c*Sin[d+e*x])^(n+1),x] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[a^2-b^2-c^2,0] && LtQ[n,-1]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: ["G&R 2.558.1 inverted with a2-b2-c2\\[Equal]0 inverted"],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, e__, n_, x_],
        optional: [b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(a__.pow(2) - b__.pow(2) - c__.pow(2), 0)
                && ltq!(n_, -1)
        },
        rhs: {
            let angle = &d__ + &e__ * x_;
            let base = &a__ + &b__ * angle.cos() + &c__ * angle.sin();
            let recursive = rubi_rhs_int(&base.pow(&n_ + 1), x_);
            let coefficient = (&n_ + 1) / (&a__ * (Atom::num(2) * &n_ + 1));

            rubi_simp(&((&c__ * angle.cos() - &b__ * angle.sin()) * base.pow(&n_)
                    / (&a__ * &e__ * (Atom::num(2) * &n_ + 1))), x_)
                    + rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_3596(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 3596,
        source: "Int[Sqrt[a_+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_]],x_Symbol] :=
          b/(c*e) \\[Star] Subst[Int[Sqrt[a+x]/x,x],x,b*Cos[d+e*x]+c*Sin[d+e*x]] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[b^2+c^2,0]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: ["Integration by substitution"],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, e__, x_],
        optional: [b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(b__.pow(2) + c__.pow(2), 0)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let angle = &d__ + &e__ * x_;
            let primitive = rubi_rhs_int(&((&a__ + &sub_atom).sqrt() / &sub_atom), sub);

            let substituted =
                rubi_subst(&primitive, sub, &b__ * angle.cos() + &c__ * angle.sin());
            rubi_star(&b__ / (&c__ * &e__), substituted)
        },
    ));
}

fn push_rules_rule_3597(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 3597,
        source: "Int[Sqrt[a_+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_]],x_Symbol] :=
          Int[Sqrt[a+Sqrt[b^2+c^2]*Cos[d+e*x-ArcTan[b,c]]],x] /;
        FreeQ[{a,b,c,d,e},x] && NeQ[b^2+c^2,0] && GtQ[a+Sqrt[b^2+c^2],0]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, e__, x_],
        optional: [b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && neq!(b__.pow(2) + c__.pow(2), 0)
                && gtq!(&a__ + (b__.pow(2) + c__.pow(2)).sqrt(), 0)
        },
        rhs: {
            let angle = &d__ + &e__ * x_;
            let root = (b__.pow(2) + c__.pow(2)).sqrt();
            let arc_tan = symbol!("ArcTan").call((&b__, &c__));
            let recursive = rubi_rhs_int(&(&a__ + root * (angle - arc_tan).cos()).sqrt(), x_);

            recursive
        },
    ));
}

fn push_rules_rule_3598(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 3598,
        source: "Int[Sqrt[a_+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_]],x_Symbol] :=
          Sqrt[a+b*Cos[d+e*x]+c*Sin[d+e*x]]/Sqrt[(a+b*Cos[d+e*x]+c*Sin[d+e*x])/(a+Sqrt[b^2+c^2])] \\[Star]
            Int[Sqrt[a/(a+Sqrt[b^2+c^2])+Sqrt[b^2+c^2]/(a+Sqrt[b^2+c^2])*Cos[d+e*x-ArcTan[b,c]]],x] /;
        FreeQ[{a,b,c,d,e},x] && NeQ[a^2-b^2-c^2,0] && NeQ[b^2+c^2,0] && Not[GtQ[a+Sqrt[b^2+c^2],0]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, e__, x_],
        optional: [b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && neq!(a__.pow(2) - b__.pow(2) - c__.pow(2), 0)
                && neq!(b__.pow(2) + c__.pow(2), 0)
                && !gtq!(&a__ + (b__.pow(2) + c__.pow(2)).sqrt(), 0)
        },
        rhs: {
            let angle = &d__ + &e__ * x_;
            let base = &a__ + &b__ * angle.cos() + &c__ * angle.sin();
            let root = (b__.pow(2) + c__.pow(2)).sqrt();
            let arc_tan = symbol!("ArcTan").call((&b__, &c__));
            let scale = &a__ + &root;
            let recursive = rubi_rhs_int(
                &(&a__ / &scale + &root / &scale * (angle - arc_tan).cos()).sqrt(),
                x_,
            );

            rubi_star(base.sqrt() / (base / scale).sqrt(), recursive)
        },
    ));
}

fn push_rules_rule_3599(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 3599,
        source: "Int[(a_+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_])^n_,x_Symbol] :=
          -(c*Cos[d+e*x]-b*Sin[d+e*x])*(a+b*Cos[d+e*x]+c*Sin[d+e*x])^(n-1)/(e*n) +
          1/n \\[Star] Int[Simp[n*a^2+(n-1)*(b^2+c^2)+a*b*(2*n-1)*Cos[d+e*x]+a*c*(2*n-1)*Sin[d+e*x],x]*
            (a+b*Cos[d+e*x]+c*Sin[d+e*x])^(n-2),x] /;
        FreeQ[{a,b,c,d,e},x] && NeQ[a^2-b^2-c^2,0] && GtQ[n,1]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: ["G&R 2.558.1 inverted"],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, e__, n_, x_],
        optional: [b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && neq!(a__.pow(2) - b__.pow(2) - c__.pow(2), 0)
                && gtq!(n_, 1)
        },
        rhs: {
            let angle = &d__ + &e__ * x_;
            let base = &a__ + &b__ * angle.cos() + &c__ * angle.sin();
            let simp = rubi_simp(
                &(&n_ * a__.pow(2)
                    + (&n_ - 1) * (b__.pow(2) + c__.pow(2))
                    + &a__ * &b__ * (Atom::num(2) * &n_ - 1) * angle.cos()
                    + &a__ * &c__ * (Atom::num(2) * &n_ - 1) * angle.sin()),
                x_,
            );
            let recursive = rubi_rhs_int(&(simp * base.pow(&n_ - 2)), x_);

            rubi_simp(&(-(&c__ * angle.cos() - &b__ * angle.sin()) * base.pow(&n_ - 1) / (&e__ * &n_)), x_)
                    + rubi_star(Atom::num(1) / &n_, recursive)
        },
    ));
}

fn push_rules_rule_3600(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 3600,
        source: "Int[1/(a_+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_]),x_Symbol] :=
          Module[{f=FreeFactors[Cot[(d+e*x)/2],x]},
          -f/e \\[Star] Subst[Int[1/(a+c*f*x),x],x,Cot[(d+e*x)/2]/f]] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[a+b,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_11(symbols),
        with: [a__, b__, c__, d__, e__, x_],
        optional: [b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_) && eqq!(&a__ + &b__, 0)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let z = Atom::var(sub);
            let angle = &d__ + &e__ * x_;
            let cot_half = (&angle / 2).cot();
            let f = rubi_free_factors(&cot_half, x_);
            let primitive = rubi_rhs_int(&(Atom::num(1) / (&a__ + &c__ * &f * z)), sub);

            let substituted = rubi_subst(&primitive, sub, cot_half / &f);
            rubi_star(-&f / &e__, substituted)
        },
    ));
}

fn push_rules_rule_3601(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 3601,
        source: "Int[1/(a_+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_]),x_Symbol] :=
          Module[{f=FreeFactors[Tan[(d+e*x)/2+Pi/4],x]},
          f/e \\[Star] Subst[Int[1/(a+b*f*x),x],x,Tan[(d+e*x)/2+Pi/4]/f]] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[a+c,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_11(symbols),
        with: [a__, b__, c__, d__, e__, x_],
        optional: [b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_) && eqq!(&a__ + &c__, 0)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let z = Atom::var(sub);
            let angle = &d__ + &e__ * x_;
            let tangent = (&angle / 2 + Atom::var(Symbol::PI) / 4).tan();
            let f = rubi_free_factors(&tangent, x_);
            let primitive = rubi_rhs_int(&(Atom::num(1) / (&a__ + &b__ * &f * z)), sub);

            let substituted = rubi_subst(&primitive, sub, tangent / &f);
            rubi_star(&f / &e__, substituted)
        },
    ));
}

fn push_rules_rule_3602(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 3602,
        source: "Int[1/(a_+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_]),x_Symbol] :=
          Module[{f=FreeFactors[Cot[(d+e*x)/2+Pi/4],x]},
          -f/e \\[Star] Subst[Int[1/(a+b*f*x),x],x,Cot[(d+e*x)/2+Pi/4]/f]] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[a-c,0] && NeQ[a-b,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_11(symbols),
        with: [a__, b__, c__, d__, e__, x_],
        optional: [b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(&a__ - &c__, 0)
                && neq!(&a__ - &b__, 0)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let z = Atom::var(sub);
            let angle = &d__ + &e__ * x_;
            let cotangent = (&angle / 2 + Atom::var(Symbol::PI) / 4).cot();
            let f = rubi_free_factors(&cotangent, x_);
            let primitive = rubi_rhs_int(&(Atom::num(1) / (&a__ + &b__ * &f * z)), sub);

            let substituted = rubi_subst(&primitive, sub, cotangent / &f);
            rubi_star(-&f / &e__, substituted)
        },
    ));
}

fn push_rules_rule_3603(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 3603,
        source: "Int[1/(a_+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_]),x_Symbol] :=
          Module[{f=FreeFactors[Tan[(d+e*x)/2],x]},
          2*f/e \\[Star] Subst[Int[1/(a+b+2*c*f*x+(a-b)*f^2*x^2),x],x,Tan[(d+e*x)/2]/f]] /;
        FreeQ[{a,b,c,d,e},x] && NeQ[a^2-b^2-c^2,0]",
        desc: "Integration by substitution",
        refs: ["G&R 2.558.4"],
        pattern:  rubi_shared_pattern_11(symbols),
        with: [a__, b__, c__, d__, e__, x_],
        optional: [b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && neq!(a__.pow(2) - b__.pow(2) - c__.pow(2), 0)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let z = Atom::var(sub);
            let angle = &d__ + &e__ * x_;
            let tangent = (&angle / 2).tan();
            let f = rubi_free_factors(&tangent, x_);
            let primitive = rubi_rhs_int(
                &(Atom::num(1)
                    / (&a__ + &b__ + Atom::num(2) * &c__ * &f * &z + (&a__ - &b__) * f.pow(2) * z.pow(2))),
                sub,
            );

            let substituted = rubi_subst(&primitive, sub, tangent / &f);
            rubi_star(Atom::num(2) * &f / &e__, substituted)
        },
    ));
}

fn push_rules_rule_3604(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 3604,
        source: "Int[1/Sqrt[a_+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_]],x_Symbol] :=
          b/(c*e) \\[Star] Subst[Int[1/(x*Sqrt[a+x]),x],x,b*Cos[d+e*x]+c*Sin[d+e*x]] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[b^2+c^2,0]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: ["Integration by substitution"],
        pattern:  rubi_shared_pattern_12(symbols),
        with: [a__, b__, c__, d__, e__, x_],
        optional: [b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(b__.pow(2) + c__.pow(2), 0)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let z = Atom::var(sub);
            let angle = &d__ + &e__ * x_;
            let primitive = rubi_rhs_int(&(Atom::num(1) / (&z * (&a__ + &z).sqrt())), sub);

            let substituted =
                rubi_subst(&primitive, sub, &b__ * angle.cos() + &c__ * angle.sin());
            rubi_star(&b__ / (&c__ * &e__), substituted)
        },
    ));
}

fn push_rules_rule_3605(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 3605,
        source: "Int[1/Sqrt[a_+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_]],x_Symbol] :=
          Int[1/Sqrt[a+Sqrt[b^2+c^2]*Cos[d+e*x-ArcTan[b,c]]],x] /;
        FreeQ[{a,b,c,d,e},x] && NeQ[b^2+c^2,0] && GtQ[a+Sqrt[b^2+c^2],0]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_12(symbols),
        with: [a__, b__, c__, d__, e__, x_],
        optional: [b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && neq!(b__.pow(2) + c__.pow(2), 0)
                && gtq!(&a__ + (b__.pow(2) + c__.pow(2)).sqrt(), 0)
        },
        rhs: {
            let angle = &d__ + &e__ * x_;
            let root = (b__.pow(2) + c__.pow(2)).sqrt();
            let arc_tan = symbol!("ArcTan").call((&b__, &c__));
            let recursive = rubi_rhs_int(
                &(Atom::num(1) / (&a__ + root * (angle - arc_tan).cos()).sqrt()),
                x_,
            );

            recursive
        },
    ));
}

fn push_rules_rule_3606(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 3606,
        source: "Int[1/Sqrt[a_+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_]],x_Symbol] :=
          Sqrt[(a+b*Cos[d+e*x]+c*Sin[d+e*x])/(a+Sqrt[b^2+c^2])]/Sqrt[a+b*Cos[d+e*x]+c*Sin[d+e*x]] \\[Star]
            Int[1/Sqrt[a/(a+Sqrt[b^2+c^2])+Sqrt[b^2+c^2]/(a+Sqrt[b^2+c^2])*Cos[d+e*x-ArcTan[b,c]]],x] /;
        FreeQ[{a,b,c,d,e},x] && NeQ[a^2-b^2-c^2,0] && NeQ[b^2+c^2,0] && Not[GtQ[a+Sqrt[b^2+c^2],0]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_12(symbols),
        with: [a__, b__, c__, d__, e__, x_],
        optional: [b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && neq!(a__.pow(2) - b__.pow(2) - c__.pow(2), 0)
                && neq!(b__.pow(2) + c__.pow(2), 0)
                && !gtq!(&a__ + (b__.pow(2) + c__.pow(2)).sqrt(), 0)
        },
        rhs: {
            let angle = &d__ + &e__ * x_;
            let base = &a__ + &b__ * angle.cos() + &c__ * angle.sin();
            let root = (b__.pow(2) + c__.pow(2)).sqrt();
            let arc_tan = symbol!("ArcTan").call((&b__, &c__));
            let scale = &a__ + &root;
            let recursive = rubi_rhs_int(
                &(Atom::num(1) / (&a__ / &scale + &root / &scale * (angle - arc_tan).cos()).sqrt()),
                x_,
            );

            rubi_star((&base / &scale).sqrt() / base.sqrt(), recursive)
        },
    ));
}

fn push_rules_rule_3607(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 3607,
        source: "Int[1/(a_+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_])^(3/2),x_Symbol] :=
          2*(c*Cos[d+e*x]-b*Sin[d+e*x])/(e*(a^2-b^2-c^2)*Sqrt[a+b*Cos[d+e*x]+c*Sin[d+e*x]]) +
          1/(a^2-b^2-c^2) \\[Star] Int[Sqrt[a+b*Cos[d+e*x]+c*Sin[d+e*x]],x] /;
        FreeQ[{a,b,c,d,e},x] && NeQ[a^2-b^2-c^2,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: ["G&R 2.558.1 with n=-32"],
        pattern: Atom::num(1)
            / (a__ + b__ * i_cos(d__ + e__ * x_) + c__ * i_sin(d__ + e__ * x_))
                .pow(Atom::num(3) / Atom::num(2)),
        with: [a__, b__, c__, d__, e__, x_],
        optional: [b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && neq!(a__.pow(2) - b__.pow(2) - c__.pow(2), 0)
        },
        rhs: {
            let angle = &d__ + &e__ * x_;
            let base = &a__ + &b__ * angle.cos() + &c__ * angle.sin();
            let disc = a__.pow(2) - b__.pow(2) - c__.pow(2);
            let recursive = rubi_rhs_int(&base.sqrt(), x_);

            rubi_simp(&(Atom::num(2) * (&c__ * angle.cos() - &b__ * angle.sin()) / (&e__ * &disc * base.sqrt())), x_)
                    + rubi_star(Atom::num(1) / &disc, recursive)
        },
    ));
}

fn push_rules_rule_3608(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 3608,
        source: "Int[(a_+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_])^n_,x_Symbol] :=
          (-c*Cos[d+e*x]+b*Sin[d+e*x])*(a+b*Cos[d+e*x]+c*Sin[d+e*x])^(n+1)/(e*(n+1)*(a^2-b^2-c^2)) +
          1/((n+1)*(a^2-b^2-c^2)) \\[Star]
            Int[(a*(n+1)-b*(n+2)*Cos[d+e*x]-c*(n+2)*Sin[d+e*x])*(a+b*Cos[d+e*x]+c*Sin[d+e*x])^(n+1),x] /;
        FreeQ[{a,b,c,d,e},x] && NeQ[a^2-b^2-c^2,0] && LtQ[n,-1] && NeQ[n,-3/2]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: ["G&R 2.558.1"],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, e__, n_, x_],
        optional: [b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && neq!(a__.pow(2) - b__.pow(2) - c__.pow(2), 0)
                && ltq!(n_, -1)
                && neq!(n_, -Atom::num(3) / Atom::num(2))
        },
        rhs: {
            let angle = &d__ + &e__ * x_;
            let base = &a__ + &b__ * angle.cos() + &c__ * angle.sin();
            let disc = a__.pow(2) - b__.pow(2) - c__.pow(2);
            let recursive = rubi_rhs_int(
                &((&a__ * (&n_ + 1) - &b__ * (&n_ + 2) * angle.cos() - &c__ * (&n_ + 2) * angle.sin())
                    * base.pow(&n_ + 1)),
                x_,
            );

            rubi_simp(&((-&c__ * angle.cos() + &b__ * angle.sin()) * base.pow(&n_ + 1) / (&e__ * (&n_ + 1) * &disc)), x_)
                    + rubi_star(Atom::num(1) / ((&n_ + 1) * disc), recursive)
        },
    ));
}

fn push_rules_rule_3609(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_a__,
        capital_b__,
        capital_c__,
        a__,
        b__,
        c__,
        d__,
        e__,
        x_
    );
    rules.push(rubi_rule!(
        order: 3609,
        source: "Int[(A_.+B_.*cos[d_.+e_.*x_]+C_.*sin[d_.+e_.*x_])/(a_+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_]),x_Symbol] :=
          (2*a*A-b*B-c*C)*x/(2*a^2) - (b*B+c*C)*(b*Cos[d+e*x]-c*Sin[d+e*x])/(2*a*b*c*e) +
          (a^2*(b*B-c*C)-2*a*A*b^2+b^2*(b*B+c*C))*Log[RemoveContent[a+b*Cos[d+e*x]+c*Sin[d+e*x],x]]/(2*a^2*b*c*e) /;
        FreeQ[{a,b,c,d,e,A,B,C},x] && EqQ[b^2+c^2,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [capital_a__, capital_b__, capital_c__, d__, e__, a__, b__, c__, x_],
        optional: [capital_a__, capital_b__, capital_c__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__, capital_a__, capital_b__, capital_c__], x_)
                && eqq!(b__.pow(2) + c__.pow(2), 0)
        },
        rhs: {
            let angle = &d__ + &e__ * x_;
            let base = &a__ + &b__ * angle.cos() + &c__ * angle.sin();

            rubi_simp(&((Atom::num(2) * &a__ * &capital_a__ - &b__ * &capital_b__ - &c__ * &capital_c__) * x_
                    / (Atom::num(2) * a__.pow(2))), x_)
                    - rubi_simp(&((&b__ * &capital_b__ + &c__ * &capital_c__) * (&b__ * angle.cos() - &c__ * angle.sin())
                        / (Atom::num(2) * &a__ * &b__ * &c__ * &e__)), x_)
                    + rubi_simp(&((a__.pow(2) * (&b__ * &capital_b__ - &c__ * &capital_c__)
                        - Atom::num(2) * &a__ * &capital_a__ * b__.pow(2)
                        + b__.pow(2) * (&b__ * &capital_b__ + &c__ * &capital_c__))
                        * rubi_remove_content(&base, x_).log()
                        / (Atom::num(2) * a__.pow(2) * &b__ * &c__ * &e__)), x_)
        },
    ));
}

fn push_rules_rule_3610(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_a__, capital_c__, a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 3610,
        source: "Int[(A_.+C_.*sin[d_.+e_.*x_])/(a_+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_]),x_Symbol] :=
          (2*a*A-c*C)*x/(2*a^2) - C*Cos[d+e*x]/(2*a*e) + c*C*Sin[d+e*x]/(2*a*b*e) +
          (-a^2*C+2*a*c*A+b^2*C)*Log[RemoveContent[a+b*Cos[d+e*x]+c*Sin[d+e*x],x]]/(2*a^2*b*e) /;
        FreeQ[{a,b,c,d,e,A,C},x] && EqQ[b^2+c^2,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [capital_a__, capital_c__, d__, e__, a__, b__, c__, x_],
        optional: [capital_a__, capital_c__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__, capital_a__, capital_c__], x_)
                && eqq!(b__.pow(2) + c__.pow(2), 0)
        },
        rhs: {
            let angle = &d__ + &e__ * x_;
            let base = &a__ + &b__ * angle.cos() + &c__ * angle.sin();

            rubi_simp(&((Atom::num(2) * &a__ * &capital_a__ - &c__ * &capital_c__) * x_
                    / (Atom::num(2) * a__.pow(2))), x_)
                    - rubi_simp(&(&capital_c__ * angle.cos() / (Atom::num(2) * &a__ * &e__)), x_)
                    + rubi_simp(&(&c__ * &capital_c__ * angle.sin() / (Atom::num(2) * &a__ * &b__ * &e__)), x_)
                    + rubi_simp(&((-a__.pow(2) * &capital_c__ + Atom::num(2) * &a__ * &c__ * &capital_a__ + b__.pow(2) * &capital_c__)
                        * rubi_remove_content(&base, x_).log()
                        / (Atom::num(2) * a__.pow(2) * &b__ * &e__)), x_)
        },
    ));
}

fn push_rules_rule_3611(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_a__, capital_b__, a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 3611,
        source: "Int[(A_.+B_.*cos[d_.+e_.*x_])/(a_+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_]),x_Symbol] :=
          (2*a*A-b*B)*x/(2*a^2) - b*B*Cos[d+e*x]/(2*a*c*e) + B*Sin[d+e*x]/(2*a*e) +
          (a^2*B-2*a*b*A+b^2*B)*Log[RemoveContent[a+b*Cos[d+e*x]+c*Sin[d+e*x],x]]/(2*a^2*c*e) /;
        FreeQ[{a,b,c,d,e,A,B},x] && EqQ[b^2+c^2,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [capital_a__, capital_b__, d__, e__, a__, b__, c__, x_],
        optional: [capital_a__, capital_b__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__, capital_a__, capital_b__], x_)
                && eqq!(b__.pow(2) + c__.pow(2), 0)
        },
        rhs: {
            let angle = &d__ + &e__ * x_;
            let base = &a__ + &b__ * angle.cos() + &c__ * angle.sin();

            rubi_simp(&((Atom::num(2) * &a__ * &capital_a__ - &b__ * &capital_b__) * x_
                    / (Atom::num(2) * a__.pow(2))), x_)
                    - rubi_simp(&(&b__ * &capital_b__ * angle.cos() / (Atom::num(2) * &a__ * &c__ * &e__)), x_)
                    + rubi_simp(&(&capital_b__ * angle.sin() / (Atom::num(2) * &a__ * &e__)), x_)
                    + rubi_simp(&((a__.pow(2) * &capital_b__ - Atom::num(2) * &a__ * &b__ * &capital_a__ + b__.pow(2) * &capital_b__)
                        * rubi_remove_content(&base, x_).log()
                        / (Atom::num(2) * a__.pow(2) * &c__ * &e__)), x_)
        },
    ));
}

fn push_rules_rule_3612(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_a__,
        capital_b__,
        capital_c__,
        a__,
        b__,
        c__,
        d__,
        e__,
        x_
    );
    rules.push(rubi_rule!(
        order: 3612,
        source: "Int[(A_.+B_.*cos[d_.+e_.*x_]+C_.*sin[d_.+e_.*x_])/(a_.+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_]),x_Symbol] :=
          (b*B+c*C)*x/(b^2+c^2) + (c*B-b*C)*Log[a+b*Cos[d+e*x]+c*Sin[d+e*x]]/(e*(b^2+c^2)) /;
        FreeQ[{a,b,c,d,e,A,B,C},x] && NeQ[b^2+c^2,0] && EqQ[A*(b^2+c^2)-a*(b*B+c*C),0]",
        desc: "Apply the direct antiderivative formula.",
        refs: ["G&R 2.558.2 with A(b2+c2)-a(b B+c C)\\[Equal]0"],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [capital_a__, capital_b__, capital_c__, d__, e__, a__, b__, c__, x_],
        optional: [capital_a__, capital_b__, capital_c__, a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__, capital_a__, capital_b__, capital_c__], x_)
                && neq!(b__.pow(2) + c__.pow(2), 0)
                && eqq!(&capital_a__ * (b__.pow(2) + c__.pow(2)) - &a__ * (&b__ * &capital_b__ + &c__ * &capital_c__), 0)
        },
        rhs: {
            let angle = &d__ + &e__ * x_;
            let base = &a__ + &b__ * angle.cos() + &c__ * angle.sin();
            let den = b__.pow(2) + c__.pow(2);

            rubi_simp(&((&b__ * &capital_b__ + &c__ * &capital_c__) * x_ / &den), x_)
                    + rubi_simp(&((&c__ * &capital_b__ - &b__ * &capital_c__) * base.log() / (&e__ * den)), x_)
        },
    ));
}

fn push_rules_rule_3613(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_a__, capital_c__, a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 3613,
        source: "Int[(A_.+C_.*sin[d_.+e_.*x_])/(a_.+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_]),x_Symbol] :=
          c*C*x/(b^2+c^2) - b*C*Log[a+b*Cos[d+e*x]+c*Sin[d+e*x]]/(e*(b^2+c^2)) /;
        FreeQ[{a,b,c,d,e,A,C},x] && NeQ[b^2+c^2,0] && EqQ[A*(b^2+c^2)-a*c*C,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: ["G&R 2.558.2 with A(b2+c2)-a(b B+c C)\\[Equal]0"],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [capital_a__, capital_c__, d__, e__, a__, b__, c__, x_],
        optional: [capital_a__, capital_c__, a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__, capital_a__, capital_c__], x_)
                && neq!(b__.pow(2) + c__.pow(2), 0)
                && eqq!(&capital_a__ * (b__.pow(2) + c__.pow(2)) - &a__ * &c__ * &capital_c__, 0)
        },
        rhs: {
            let angle = &d__ + &e__ * x_;
            let base = &a__ + &b__ * angle.cos() + &c__ * angle.sin();
            let den = b__.pow(2) + c__.pow(2);

            rubi_simp(&(&c__ * &capital_c__ * x_ / &den), x_) - rubi_simp(&(&b__ * &capital_c__ * base.log() / (&e__ * den)), x_)
        },
    ));
}

fn push_rules_rule_3614(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_a__, capital_b__, a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 3614,
        source: "Int[(A_.+B_.*cos[d_.+e_.*x_])/(a_.+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_]),x_Symbol] :=
          b*B*x/(b^2+c^2) + c*B*Log[a+b*Cos[d+e*x]+c*Sin[d+e*x]]/(e*(b^2+c^2)) /;
        FreeQ[{a,b,c,d,e,A,B},x] && NeQ[b^2+c^2,0] && EqQ[A*(b^2+c^2)-a*b*B,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: ["G&R 2.558.2 with A(b2+c2)-a(b B+c C)\\[Equal]0"],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [capital_a__, capital_b__, d__, e__, a__, b__, c__, x_],
        optional: [capital_a__, capital_b__, a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__, capital_a__, capital_b__], x_)
                && neq!(b__.pow(2) + c__.pow(2), 0)
                && eqq!(&capital_a__ * (b__.pow(2) + c__.pow(2)) - &a__ * &b__ * &capital_b__, 0)
        },
        rhs: {
            let angle = &d__ + &e__ * x_;
            let base = &a__ + &b__ * angle.cos() + &c__ * angle.sin();
            let den = b__.pow(2) + c__.pow(2);

            rubi_simp(&(&b__ * &capital_b__ * x_ / &den), x_) + rubi_simp(&(&c__ * &capital_b__ * base.log() / (&e__ * den)), x_)
        },
    ));
}

fn push_rules_rule_3615(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_a__,
        capital_b__,
        capital_c__,
        a__,
        b__,
        c__,
        d__,
        e__,
        x_
    );
    rules.push(rubi_rule!(
        order: 3615,
        source: "Int[(A_.+B_.*cos[d_.+e_.*x_]+C_.*sin[d_.+e_.*x_])/(a_.+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_]),x_Symbol] :=
          (b*B+c*C)*x/(b^2+c^2) + (c*B-b*C)*Log[a+b*Cos[d+e*x]+c*Sin[d+e*x]]/(e*(b^2+c^2)) +
          (A*(b^2+c^2)-a*(b*B+c*C))/(b^2+c^2) \\[Star] Int[1/(a+b*Cos[d+e*x]+c*Sin[d+e*x]),x] /;
        FreeQ[{a,b,c,d,e,A,B,C},x] && NeQ[b^2+c^2,0] && NeQ[A*(b^2+c^2)-a*(b*B+c*C),0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: ["G&R 2.558.2"],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [capital_a__, capital_b__, capital_c__, d__, e__, a__, b__, c__, x_],
        optional: [capital_a__, capital_b__, capital_c__, a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__, capital_a__, capital_b__, capital_c__], x_)
                && neq!(b__.pow(2) + c__.pow(2), 0)
                && neq!(&capital_a__ * (b__.pow(2) + c__.pow(2)) - &a__ * (&b__ * &capital_b__ + &c__ * &capital_c__), 0)
        },
        rhs: {
            let angle = &d__ + &e__ * x_;
            let base = &a__ + &b__ * angle.cos() + &c__ * angle.sin();
            let den = b__.pow(2) + c__.pow(2);
            let recursive = rubi_rhs_int(&(Atom::num(1) / &base), x_);

            rubi_simp(&((&b__ * &capital_b__ + &c__ * &capital_c__) * x_ / &den), x_)
                    + rubi_simp(&((&c__ * &capital_b__ - &b__ * &capital_c__) * base.log() / (&e__ * &den)), x_)
                    + rubi_star((&capital_a__ * &den
                            - &a__ * (&b__ * &capital_b__ + &c__ * &capital_c__))
                            / &den, recursive)
        },
    ));
}

fn push_rules_rule_3616(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_a__, capital_c__, a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 3616,
        source: "Int[(A_.+C_.*sin[d_.+e_.*x_])/(a_.+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_]),x_Symbol] :=
          c*C*(d+e*x)/(e*(b^2+c^2)) - b*C*Log[a+b*Cos[d+e*x]+c*Sin[d+e*x]]/(e*(b^2+c^2)) +
          (A*(b^2+c^2)-a*c*C)/(b^2+c^2) \\[Star] Int[1/(a+b*Cos[d+e*x]+c*Sin[d+e*x]),x] /;
        FreeQ[{a,b,c,d,e,A,C},x] && NeQ[b^2+c^2,0] && NeQ[A*(b^2+c^2)-a*c*C,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: ["G&R 2.558.2"],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [capital_a__, capital_c__, d__, e__, a__, b__, c__, x_],
        optional: [capital_a__, capital_c__, a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__, capital_a__, capital_c__], x_)
                && neq!(b__.pow(2) + c__.pow(2), 0)
                && neq!(&capital_a__ * (b__.pow(2) + c__.pow(2)) - &a__ * &c__ * &capital_c__, 0)
        },
        rhs: {
            let angle = &d__ + &e__ * x_;
            let base = &a__ + &b__ * angle.cos() + &c__ * angle.sin();
            let den = b__.pow(2) + c__.pow(2);
            let recursive = rubi_rhs_int(&(Atom::num(1) / &base), x_);

            rubi_simp(&(&c__ * &capital_c__ * (&d__ + &e__ * x_) / (&e__ * &den)), x_)
                    - rubi_simp(&(&b__ * &capital_c__ * base.log() / (&e__ * &den)), x_)
                    + rubi_star((&capital_a__ * &den - &a__ * &c__ * &capital_c__) / &den, recursive)
        },
    ));
}

fn push_rules_rule_3617(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_a__, capital_b__, a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 3617,
        source: "Int[(A_.+B_.*cos[d_.+e_.*x_])/(a_.+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_]),x_Symbol] :=
          b*B*(d+e*x)/(e*(b^2+c^2)) +
          c*B*Log[a+b*Cos[d+e*x]+c*Sin[d+e*x]]/(e*(b^2+c^2)) +
          (A*(b^2+c^2)-a*b*B)/(b^2+c^2) \\[Star] Int[1/(a+b*Cos[d+e*x]+c*Sin[d+e*x]),x] /;
        FreeQ[{a,b,c,d,e,A,B},x] && NeQ[b^2+c^2,0] && NeQ[A*(b^2+c^2)-a*b*B,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: ["G&R 2.558.2"],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [capital_a__, capital_b__, d__, e__, a__, b__, c__, x_],
        optional: [capital_a__, capital_b__, a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__, capital_a__, capital_b__], x_)
                && neq!(b__.pow(2) + c__.pow(2), 0)
                && neq!(&capital_a__ * (b__.pow(2) + c__.pow(2)) - &a__ * &b__ * &capital_b__, 0)
        },
        rhs: {
            let angle = &d__ + &e__ * x_;
            let base = &a__ + &b__ * angle.cos() + &c__ * angle.sin();
            let den = b__.pow(2) + c__.pow(2);
            let recursive = rubi_rhs_int(&(Atom::num(1) / &base), x_);

            rubi_simp(&(&b__ * &capital_b__ * (&d__ + &e__ * x_) / (&e__ * &den)), x_)
                    + rubi_simp(&(&c__ * &capital_b__ * base.log() / (&e__ * &den)), x_)
                    + rubi_star((&capital_a__ * &den - &a__ * &b__ * &capital_b__) / &den, recursive)
        },
    ));
}

fn push_rules_rule_3618(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_a__,
        capital_b__,
        capital_c__,
        a__,
        b__,
        c__,
        d__,
        e__,
        n_,
        x_
    );
    rules.push(rubi_rule!(
        order: 3618,
        source: "Int[(A_.+B_.*cos[d_.+e_.*x_]+C_.*sin[d_.+e_.*x_])*(a_+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_])^n_.,x_Symbol] :=
          (B*c-b*C-a*C*Cos[d+e*x]+a*B*Sin[d+e*x])*(a+b*Cos[d+e*x]+c*Sin[d+e*x])^n/(a*e*(n+1)) /;
        FreeQ[{a,b,c,d,e,A,B,C,n},x] && NeQ[n,-1] && EqQ[a^2-b^2-c^2,0] && EqQ[(b*B+c*C)*n+a*A*(n+1),0]",
        desc: "Apply the direct antiderivative formula.",
        refs: ["G&R 2.558.1b"],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [capital_a__, capital_b__, capital_c__, d__, e__, a__, b__, c__, n_, x_],
        optional: [capital_a__, capital_b__, capital_c__, b__, c__, d__, e__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, capital_a__, capital_b__, capital_c__, n_], x_)
                && neq!(n_, -1)
                && eqq!(a__.pow(2) - b__.pow(2) - c__.pow(2), 0)
                && eqq!((&b__ * &capital_b__ + &c__ * &capital_c__) * &n_ + &a__ * &capital_a__ * (&n_ + 1), 0)
        },
        rhs: {
            let angle = &d__ + &e__ * x_;
            let base = &a__ + &b__ * angle.cos() + &c__ * angle.sin();

            rubi_simp(&((&capital_b__ * &c__ - &b__ * &capital_c__ - &a__ * &capital_c__ * angle.cos()
                    + &a__ * &capital_b__ * angle.sin())
                    * base.pow(&n_)
                    / (&a__ * &e__ * (&n_ + 1))), x_)
        },
    ));
}

fn push_rules_rule_3619(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_a__, capital_c__, a__, b__, c__, d__, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 3619,
        source: "Int[(A_.+C_.*sin[d_.+e_.*x_])*(a_+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_])^n_.,x_Symbol] :=
          -(b*C+a*C*Cos[d+e*x])*(a+b*Cos[d+e*x]+c*Sin[d+e*x])^n/(a*e*(n+1)) /;
        FreeQ[{a,b,c,d,e,A,C,n},x] && NeQ[n,-1] && EqQ[a^2-b^2-c^2,0] && EqQ[c*C*n+a*A*(n+1),0]",
        desc: "Apply the direct antiderivative formula.",
        refs: ["G&R 2.558.1b"],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [capital_a__, capital_c__, d__, e__, a__, b__, c__, n_, x_],
        optional: [capital_a__, capital_c__, b__, c__, d__, e__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, capital_a__, capital_c__, n_], x_)
                && neq!(n_, -1)
                && eqq!(a__.pow(2) - b__.pow(2) - c__.pow(2), 0)
                && eqq!(&c__ * &capital_c__ * &n_ + &a__ * &capital_a__ * (&n_ + 1), 0)
        },
        rhs: {
            let angle = &d__ + &e__ * x_;
            let base = &a__ + &b__ * angle.cos() + &c__ * angle.sin();

            rubi_simp(&(-(&b__ * &capital_c__ + &a__ * &capital_c__ * angle.cos()) * base.pow(&n_) / (&a__ * &e__ * (&n_ + 1))), x_)
        },
    ));
}

fn push_rules_rule_3620(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_a__, capital_b__, a__, b__, c__, d__, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 3620,
        source: "Int[(A_.+B_.*cos[d_.+e_.*x_])*(a_+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_])^n_.,x_Symbol] :=
          (B*c+a*B*Sin[d+e*x])*(a+b*Cos[d+e*x]+c*Sin[d+e*x])^n/(a*e*(n+1)) /;
        FreeQ[{a,b,c,d,e,A,B,n},x] && NeQ[n,-1] && EqQ[a^2-b^2-c^2,0] && EqQ[b*B*n+a*A*(n+1),0]",
        desc: "Apply the direct antiderivative formula.",
        refs: ["G&R 2.558.1b"],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [capital_a__, capital_b__, d__, e__, a__, b__, c__, n_, x_],
        optional: [capital_a__, capital_b__, b__, c__, d__, e__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, capital_a__, capital_b__, n_], x_)
                && neq!(n_, -1)
                && eqq!(a__.pow(2) - b__.pow(2) - c__.pow(2), 0)
                && eqq!(&b__ * &capital_b__ * &n_ + &a__ * &capital_a__ * (&n_ + 1), 0)
        },
        rhs: {
            let angle = &d__ + &e__ * x_;
            let base = &a__ + &b__ * angle.cos() + &c__ * angle.sin();

            rubi_simp(&((&capital_b__ * &c__ + &a__ * &capital_b__ * angle.sin()) * base.pow(&n_) / (&a__ * &e__ * (&n_ + 1))), x_)
        },
    ));
}

fn push_rules_rule_3621(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_a__,
        capital_b__,
        capital_c__,
        a__,
        b__,
        c__,
        d__,
        e__,
        n_,
        x_
    );
    rules.push(rubi_rule!(
        order: 3621,
        source: "Int[(A_.+B_.*cos[d_.+e_.*x_]+C_.*sin[d_.+e_.*x_])*(a_+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_])^n_.,x_Symbol] :=
          (B*c-b*C-a*C*Cos[d+e*x]+a*B*Sin[d+e*x])*(a+b*Cos[d+e*x]+c*Sin[d+e*x])^n/(a*e*(n+1)) +
          ((b*B+c*C)*n+a*A*(n+1))/(a*(n+1)) \\[Star] Int[(a+b*Cos[d+e*x]+c*Sin[d+e*x])^n,x] /;
        FreeQ[{a,b,c,d,e,A,B,C,n},x] && NeQ[n,-1] && EqQ[a^2-b^2-c^2,0] && NeQ[(b*B+c*C)*n+a*A*(n+1),0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: ["G&R 2.558.1b"],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [capital_a__, capital_b__, capital_c__, d__, e__, a__, b__, c__, n_, x_],
        optional: [capital_a__, capital_b__, capital_c__, b__, c__, d__, e__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, capital_a__, capital_b__, capital_c__, n_], x_)
                && neq!(n_, -1)
                && eqq!(a__.pow(2) - b__.pow(2) - c__.pow(2), 0)
                && neq!((&b__ * &capital_b__ + &c__ * &capital_c__) * &n_ + &a__ * &capital_a__ * (&n_ + 1), 0)
        },
        rhs: {
            let angle = &d__ + &e__ * x_;
            let base = &a__ + &b__ * angle.cos() + &c__ * angle.sin();
            let recursive = rubi_rhs_int(&base.pow(&n_), x_);

            rubi_simp(&((&capital_b__ * &c__ - &b__ * &capital_c__ - &a__ * &capital_c__ * angle.cos()
                    + &a__ * &capital_b__ * angle.sin())
                    * base.pow(&n_)
                    / (&a__ * &e__ * (&n_ + 1))), x_)
                    + rubi_star(((&b__ * &capital_b__ + &c__ * &capital_c__) * &n_
                            + &a__ * &capital_a__ * (&n_ + 1))
                            / (&a__ * (&n_ + 1)), recursive)
        },
    ));
}

fn push_rules_rule_3622(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_a__, capital_c__, a__, b__, c__, d__, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 3622,
        source: "Int[(A_.+C_.*sin[d_.+e_.*x_])*(a_+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_])^n_.,x_Symbol] :=
          -(b*C+a*C*Cos[d+e*x])*(a+b*Cos[d+e*x]+c*Sin[d+e*x])^n/(a*e*(n+1)) +
          (c*C*n+a*A*(n+1))/(a*(n+1)) \\[Star] Int[(a+b*Cos[d+e*x]+c*Sin[d+e*x])^n,x] /;
        FreeQ[{a,b,c,d,e,A,C,n},x] && NeQ[n,-1] && EqQ[a^2-b^2-c^2,0] && NeQ[c*C*n+a*A*(n+1),0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: ["G&R 2.558.1b"],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [capital_a__, capital_c__, d__, e__, a__, b__, c__, n_, x_],
        optional: [capital_a__, capital_c__, b__, c__, d__, e__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, capital_a__, capital_c__, n_], x_)
                && neq!(n_, -1)
                && eqq!(a__.pow(2) - b__.pow(2) - c__.pow(2), 0)
                && neq!(&c__ * &capital_c__ * &n_ + &a__ * &capital_a__ * (&n_ + 1), 0)
        },
        rhs: {
            let angle = &d__ + &e__ * x_;
            let base = &a__ + &b__ * angle.cos() + &c__ * angle.sin();
            let recursive = rubi_rhs_int(&base.pow(&n_), x_);

            rubi_simp(&(-(&b__ * &capital_c__ + &a__ * &capital_c__ * angle.cos()) * base.pow(&n_) / (&a__ * &e__ * (&n_ + 1))), x_)
                    + rubi_star((&c__ * &capital_c__ * &n_
                            + &a__ * &capital_a__ * (&n_ + 1))
                            / (&a__ * (&n_ + 1)), recursive)
        },
    ));
}

fn push_rules_rule_3623(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_a__, capital_b__, a__, b__, c__, d__, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 3623,
        source: "Int[(A_.+B_.*cos[d_.+e_.*x_])*(a_+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_])^n_.,x_Symbol] :=
          (B*c+a*B*Sin[d+e*x])*(a+b*Cos[d+e*x]+c*Sin[d+e*x])^n/(a*e*(n+1)) +
          (b*B*n+a*A*(n+1))/(a*(n+1)) \\[Star] Int[(a+b*Cos[d+e*x]+c*Sin[d+e*x])^n,x] /;
        FreeQ[{a,b,c,d,e,A,B,n},x] && NeQ[n,-1] && EqQ[a^2-b^2-c^2,0] && NeQ[b*B*n+a*A*(n+1),0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: ["G&R 2.558.1b"],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [capital_a__, capital_b__, d__, e__, a__, b__, c__, n_, x_],
        optional: [capital_a__, capital_b__, b__, c__, d__, e__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, capital_a__, capital_b__, n_], x_)
                && neq!(n_, -1)
                && eqq!(a__.pow(2) - b__.pow(2) - c__.pow(2), 0)
                && neq!(&b__ * &capital_b__ * &n_ + &a__ * &capital_a__ * (&n_ + 1), 0)
        },
        rhs: {
            let angle = &d__ + &e__ * x_;
            let base = &a__ + &b__ * angle.cos() + &c__ * angle.sin();
            let recursive = rubi_rhs_int(&base.pow(&n_), x_);

            rubi_simp(&((&capital_b__ * &c__ + &a__ * &capital_b__ * angle.sin()) * base.pow(&n_) / (&a__ * &e__ * (&n_ + 1))), x_)
                    + rubi_star((&b__ * &capital_b__ * &n_
                            + &a__ * &capital_a__ * (&n_ + 1))
                            / (&a__ * (&n_ + 1)), recursive)
        },
    ));
}

fn push_rules_rule_3624(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_b__, capital_c__, b__, c__, d__, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 3624,
        source: "Int[(B_.*cos[d_.+e_.*x_]+C_.*sin[d_.+e_.*x_])*(b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_])^n_.,x_Symbol] :=
          (c*B-b*C)*(b*Cos[d+e*x]+c*Sin[d+e*x])^(n+1)/(e*(n+1)*(b^2+c^2)) /;
        FreeQ[{b,c,d,e,B,C},x] && NeQ[n,-1] && NeQ[b^2+c^2,0] && EqQ[b*B+c*C,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: ["G&R 2.558.1a with a=0, A=0 and b B+c C\\[Equal]0"],
        pattern: (capital_b__ * i_cos(d__ + e__ * x_) + capital_c__ * i_sin(d__ + e__ * x_))
            * (b__ * i_cos(d__ + e__ * x_) + c__ * i_sin(d__ + e__ * x_)).pow(n_),
        with: [capital_b__, capital_c__, d__, e__, b__, c__, n_, x_],
        optional: [capital_b__, capital_c__, b__, c__, d__, e__, n_],
        when: {
            freeq!([b__, c__, d__, e__, capital_b__, capital_c__], x_)
                && neq!(n_, -1)
                && neq!(b__.pow(2) + c__.pow(2), 0)
                && eqq!(&b__ * &capital_b__ + &c__ * &capital_c__, 0)
        },
        rhs: {
            let angle = &d__ + &e__ * x_;
            let base = &b__ * angle.cos() + &c__ * angle.sin();

            rubi_simp(&((&c__ * &capital_b__ - &b__ * &capital_c__) * base.pow(&n_ + 1) / (&e__ * (&n_ + 1) * (b__.pow(2) + c__.pow(2)))), x_)
        },
    ));
}

fn push_rules_rule_3625(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_a__,
        capital_b__,
        capital_c__,
        a__,
        b__,
        c__,
        d__,
        e__,
        n_,
        x_
    );
    rules.push(rubi_rule!(
        order: 3625,
        source: "Int[(A_.+B_.*cos[d_.+e_.*x_]+C_.*sin[d_.+e_.*x_])*(a_+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_])^n_.,x_Symbol] :=
          (B*c-b*C-a*C*Cos[d+e*x]+a*B*Sin[d+e*x])*(a+b*Cos[d+e*x]+c*Sin[d+e*x])^n/(a*e*(n+1)) +
          1/(a*(n+1)) \\[Star] Int[(a+b*Cos[d+e*x]+c*Sin[d+e*x])^(n-1)*
        \tSimp[a*(b*B+c*C)*n+a^2*A*(n+1)+
              (n*(a^2*B-B*c^2+b*c*C)+a*b*A*(n+1))*Cos[d+e*x]+
              (n*(b*B*c+a^2*C-b^2*C)+a*c*A*(n+1))*Sin[d+e*x],x],x] /;
        FreeQ[{a,b,c,d,e,A,B,C},x] && GtQ[n,0] && NeQ[a^2-b^2-c^2,0]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: ["G&R 2.558.1a inverted"],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [capital_a__, capital_b__, capital_c__, d__, e__, a__, b__, c__, n_, x_],
        optional: [capital_a__, capital_b__, capital_c__, b__, c__, d__, e__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, capital_a__, capital_b__, capital_c__], x_)
                && gtq!(n_, 0)
                && neq!(a__.pow(2) - b__.pow(2) - c__.pow(2), 0)
        },
        rhs: {
            let angle = &d__ + &e__ * x_;
            let cos = angle.cos();
            let sin = angle.sin();
            let base = &a__ + &b__ * &cos + &c__ * &sin;
            let simp = rubi_simp(
                &(&a__ * (&b__ * &capital_b__ + &c__ * &capital_c__) * &n_
                    + a__.pow(2) * &capital_a__ * (&n_ + 1)
                    + (&n_ * (a__.pow(2) * &capital_b__ - &capital_b__ * c__.pow(2) + &b__ * &c__ * &capital_c__)
                        + &a__ * &b__ * &capital_a__ * (&n_ + 1))
                        * &cos
                    + (&n_ * (&b__ * &capital_b__ * &c__ + a__.pow(2) * &capital_c__ - b__.pow(2) * &capital_c__)
                        + &a__ * &c__ * &capital_a__ * (&n_ + 1))
                        * &sin),
                x_,
            );
            let recursive = rubi_rhs_int(&(base.pow(&n_ - 1) * simp), x_);

            rubi_simp(&((&capital_b__ * &c__ - &b__ * &capital_c__ - &a__ * &capital_c__ * cos
                    + &a__ * &capital_b__ * sin)
                    * base.pow(&n_)
                    / (&a__ * &e__ * (&n_ + 1))), x_)
                    + rubi_star(Atom::num(1) / (&a__ * (&n_ + 1)), recursive)
        },
    ));
}

fn push_rules_rule_3626(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_a__, capital_c__, a__, b__, c__, d__, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 3626,
        source: "Int[(A_.+C_.*sin[d_.+e_.*x_])*(a_+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_])^n_.,x_Symbol] :=
          -(b*C+a*C*Cos[d+e*x])*(a+b*Cos[d+e*x]+c*Sin[d+e*x])^n/(a*e*(n+1)) +
          1/(a*(n+1)) \\[Star] Int[(a+b*Cos[d+e*x]+c*Sin[d+e*x])^(n-1)*
            Simp[a*c*C*n+a^2*A*(n+1)+(c*b*C*n+a*b*A*(n+1))*Cos[d+e*x]+(a^2*C*n-b^2*C*n+a*c*A*(n+1))*Sin[d+e*x],x],x] /;
        FreeQ[{a,b,c,d,e,A,C},x] && GtQ[n,0] && NeQ[a^2-b^2-c^2,0]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: ["G&R 2.558.1a inverted"],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [capital_a__, capital_c__, d__, e__, a__, b__, c__, n_, x_],
        optional: [capital_a__, capital_c__, b__, c__, d__, e__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, capital_a__, capital_c__], x_)
                && gtq!(n_, 0)
                && neq!(a__.pow(2) - b__.pow(2) - c__.pow(2), 0)
        },
        rhs: {
            let angle = &d__ + &e__ * x_;
            let cos = angle.cos();
            let sin = angle.sin();
            let base = &a__ + &b__ * &cos + &c__ * &sin;
            let simp = rubi_simp(
                &(&a__ * &c__ * &capital_c__ * &n_
                    + a__.pow(2) * &capital_a__ * (&n_ + 1)
                    + (&c__ * &b__ * &capital_c__ * &n_ + &a__ * &b__ * &capital_a__ * (&n_ + 1)) * &cos
                    + (a__.pow(2) * &capital_c__ * &n_ - b__.pow(2) * &capital_c__ * &n_
                        + &a__ * &c__ * &capital_a__ * (&n_ + 1))
                        * &sin),
                x_,
            );
            let recursive = rubi_rhs_int(&(base.pow(&n_ - 1) * simp), x_);

            rubi_simp(&(-(&b__ * &capital_c__ + &a__ * &capital_c__ * cos) * base.pow(&n_) / (&a__ * &e__ * (&n_ + 1))), x_)
                    + rubi_star(Atom::num(1) / (&a__ * (&n_ + 1)), recursive)
        },
    ));
}

fn push_rules_rule_3627(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_a__, capital_b__, a__, b__, c__, d__, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 3627,
        source: "Int[(A_.+B_.*cos[d_.+e_.*x_])*(a_+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_])^n_.,x_Symbol] :=
          (B*c+a*B*Sin[d+e*x])*(a+b*Cos[d+e*x]+c*Sin[d+e*x])^n/(a*e*(n+1)) +
          1/(a*(n+1)) \\[Star] Int[(a+b*Cos[d+e*x]+c*Sin[d+e*x])^(n-1)*
            Simp[a*b*B*n+a^2*A*(n+1)+(a^2*B*n-c^2*B*n+a*b*A*(n+1))*Cos[d+e*x]+(b*c*B*n+a*c*A*(n+1))*Sin[d+e*x],x],x] /;
        FreeQ[{a,b,c,d,e,A,B},x] && GtQ[n,0] && NeQ[a^2-b^2-c^2,0]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: ["G&R 2.558.1a inverted"],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [capital_a__, capital_b__, d__, e__, a__, b__, c__, n_, x_],
        optional: [capital_a__, capital_b__, b__, c__, d__, e__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, capital_a__, capital_b__], x_)
                && gtq!(n_, 0)
                && neq!(a__.pow(2) - b__.pow(2) - c__.pow(2), 0)
        },
        rhs: {
            let angle = &d__ + &e__ * x_;
            let cos = angle.cos();
            let sin = angle.sin();
            let base = &a__ + &b__ * &cos + &c__ * &sin;
            let simp = rubi_simp(
                &(&a__ * &b__ * &capital_b__ * &n_
                    + a__.pow(2) * &capital_a__ * (&n_ + 1)
                    + (a__.pow(2) * &capital_b__ * &n_ - c__.pow(2) * &capital_b__ * &n_
                        + &a__ * &b__ * &capital_a__ * (&n_ + 1))
                        * &cos
                    + (&b__ * &c__ * &capital_b__ * &n_ + &a__ * &c__ * &capital_a__ * (&n_ + 1)) * &sin),
                x_,
            );
            let recursive = rubi_rhs_int(&(base.pow(&n_ - 1) * simp), x_);

            rubi_simp(&((&capital_b__ * &c__ + &a__ * &capital_b__ * sin) * base.pow(&n_) / (&a__ * &e__ * (&n_ + 1))), x_)
                    + rubi_star(Atom::num(1) / (&a__ * (&n_ + 1)), recursive)
        },
    ));
}

fn push_rules_rule_3628(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        capital_a__,
        capital_b__,
        capital_c__,
        a__,
        b__,
        c__,
        d__,
        e__,
        x_
    );
    rules.push(rubi_rule!(
        order: 3628,
        source: "Int[(A_.+B_.*cos[d_.+e_.*x_]+C_.*sin[d_.+e_.*x_])/Sqrt[a_+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_]],x_Symbol] :=
          B/b \\[Star] Int[Sqrt[a+b*Cos[d+e*x]+c*Sin[d+e*x]],x] +
          (A*b-a*B)/b \\[Star] Int[1/Sqrt[a+b*Cos[d+e*x]+c*Sin[d+e*x]],x] /;
        FreeQ[{a,b,c,d,e,A,B,C},x] && EqQ[B*c-b*C,0] && NeQ[A*b-a*B,0]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: (capital_a__ + capital_b__ * i_cos(d__ + e__ * x_) + capital_c__ * i_sin(d__ + e__ * x_))
            / (a__ + b__ * i_cos(d__ + e__ * x_) + c__ * i_sin(d__ + e__ * x_)).sqrt(),
        with: [capital_a__, capital_b__, capital_c__, d__, e__, a__, b__, c__, x_],
        optional: [capital_a__, capital_b__, capital_c__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__, capital_a__, capital_b__, capital_c__], x_)
                && eqq!(&capital_b__ * &c__ - &b__ * &capital_c__, 0)
                && neq!(&capital_a__ * &b__ - &a__ * &capital_b__, 0)
        },
        rhs: {
            let angle = &d__ + &e__ * x_;
            let base = &a__ + &b__ * angle.cos() + &c__ * angle.sin();
            let recursive1 = rubi_rhs_int(&base.sqrt(), x_);
            let recursive2 = rubi_rhs_int(&(Atom::num(1) / base.sqrt()), x_);

            rubi_star(&capital_b__ / &b__, recursive1)
                    + rubi_star((&capital_a__ * &b__ - &a__ * &capital_b__) / &b__, recursive2)
        },
    ));
}

fn push_rules_rule_3629(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_a__,
        capital_b__,
        capital_c__,
        a__,
        b__,
        c__,
        d__,
        e__,
        x_
    );
    rules.push(rubi_rule!(
        order: 3629,
        source: "Int[(A_.+B_.*cos[d_.+e_.*x_]+C_.*sin[d_.+e_.*x_])/(a_.+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_])^2,x_Symbol] :=
          (c*B-b*C-(a*C-c*A)*Cos[d+e*x]+(a*B-b*A)*Sin[d+e*x])/
            (e*(a^2-b^2-c^2)*(a+b*Cos[d+e*x]+c*Sin[d+e*x])) /;
        FreeQ[{a,b,c,d,e,A,B,C},x] && NeQ[a^2-b^2-c^2,0] && EqQ[a*A-b*B-c*C,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: ["G&R 2.558.1a with n=-2 and a A-b B-c C=0"],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [capital_a__, capital_b__, capital_c__, d__, e__, a__, b__, c__, x_],
        optional: [capital_a__, capital_b__, capital_c__, a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__, capital_a__, capital_b__, capital_c__], x_)
                && neq!(a__.pow(2) - b__.pow(2) - c__.pow(2), 0)
                && eqq!(&a__ * &capital_a__ - &b__ * &capital_b__ - &c__ * &capital_c__, 0)
        },
        rhs: {
            let angle = &d__ + &e__ * x_;
            let cos = angle.cos();
            let sin = angle.sin();
            let base = &a__ + &b__ * &cos + &c__ * &sin;
            let disc = a__.pow(2) - b__.pow(2) - c__.pow(2);

            rubi_simp(&((&c__ * &capital_b__ - &b__ * &capital_c__ - (&a__ * &capital_c__ - &c__ * &capital_a__) * cos
                    + (&a__ * &capital_b__ - &b__ * &capital_a__) * sin)
                    / (&e__ * disc * base)), x_)
        },
    ));
}

fn push_rules_rule_3630(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_a__, capital_c__, a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 3630,
        source: "Int[(A_.+C_.*sin[d_.+e_.*x_])/(a_.+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_])^2,x_Symbol] :=
          -(b*C+(a*C-c*A)*Cos[d+e*x]+b*A*Sin[d+e*x])/(e*(a^2-b^2-c^2)*(a+b*Cos[d+e*x]+c*Sin[d+e*x])) /;
        FreeQ[{a,b,c,d,e,A,C},x] && NeQ[a^2-b^2-c^2,0] && EqQ[a*A-c*C,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: ["G&R 2.558.1a with n=-2 and a A-b B-c C=0"],
        pattern:  rubi_shared_pattern_10(symbols),
        with: [capital_a__, capital_c__, d__, e__, a__, b__, c__, x_],
        optional: [capital_a__, capital_c__, a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__, capital_a__, capital_c__], x_)
                && neq!(a__.pow(2) - b__.pow(2) - c__.pow(2), 0)
                && eqq!(&a__ * &capital_a__ - &c__ * &capital_c__, 0)
        },
        rhs: {
            let angle = &d__ + &e__ * x_;
            let cos = angle.cos();
            let sin = angle.sin();
            let base = &a__ + &b__ * &cos + &c__ * &sin;
            let disc = a__.pow(2) - b__.pow(2) - c__.pow(2);

            rubi_simp(&(-(&b__ * &capital_c__ + (&a__ * &capital_c__ - &c__ * &capital_a__) * cos + &b__ * &capital_a__ * sin)
                / (&e__ * disc * base)), x_)
        },
    ));
}

fn push_rules_rule_3631(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_a__, capital_b__, a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 3631,
        source: "Int[(A_.+B_.*cos[d_.+e_.*x_])/(a_.+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_])^2,x_Symbol] :=
          (c*B+c*A*Cos[d+e*x]+(a*B-b*A)*Sin[d+e*x])/(e*(a^2-b^2-c^2)*(a+b*Cos[d+e*x]+c*Sin[d+e*x])) /;
        FreeQ[{a,b,c,d,e,A,B},x] && NeQ[a^2-b^2-c^2,0] && EqQ[a*A-b*B,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: ["G&R 2.558.1a with n=-2 and a A-b B-c C=0"],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [capital_a__, capital_b__, d__, e__, a__, b__, c__, x_],
        optional: [capital_a__, capital_b__, a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__, capital_a__, capital_b__], x_)
                && neq!(a__.pow(2) - b__.pow(2) - c__.pow(2), 0)
                && eqq!(&a__ * &capital_a__ - &b__ * &capital_b__, 0)
        },
        rhs: {
            let angle = &d__ + &e__ * x_;
            let cos = angle.cos();
            let sin = angle.sin();
            let base = &a__ + &b__ * &cos + &c__ * &sin;
            let disc = a__.pow(2) - b__.pow(2) - c__.pow(2);

            rubi_simp(&((&c__ * &capital_b__ + &c__ * &capital_a__ * cos + (&a__ * &capital_b__ - &b__ * &capital_a__) * sin)
                / (&e__ * disc * base)), x_)
        },
    ));
}

fn push_rules_rule_3632(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_a__,
        capital_b__,
        capital_c__,
        a__,
        b__,
        c__,
        d__,
        e__,
        x_
    );
    rules.push(rubi_rule!(
        order: 3632,
        source: "Int[(A_.+B_.*cos[d_.+e_.*x_]+C_.*sin[d_.+e_.*x_])/(a_.+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_])^2,x_Symbol] :=
          (c*B-b*C-(a*C-c*A)*Cos[d+e*x]+(a*B-b*A)*Sin[d+e*x])/
            (e*(a^2-b^2-c^2)*(a+b*Cos[d+e*x]+c*Sin[d+e*x])) +
          (a*A-b*B-c*C)/(a^2-b^2-c^2) \\[Star] Int[1/(a+b*Cos[d+e*x]+c*Sin[d+e*x]),x] /;
        FreeQ[{a,b,c,d,e,A,B,C},x] && NeQ[a^2-b^2-c^2,0] && NeQ[a*A-b*B-c*C,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: ["G&R 2.558.1a with n=-2"],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [capital_a__, capital_b__, capital_c__, d__, e__, a__, b__, c__, x_],
        optional: [capital_a__, capital_b__, capital_c__, a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__, capital_a__, capital_b__, capital_c__], x_)
                && neq!(a__.pow(2) - b__.pow(2) - c__.pow(2), 0)
                && neq!(&a__ * &capital_a__ - &b__ * &capital_b__ - &c__ * &capital_c__, 0)
        },
        rhs: {
            let angle = &d__ + &e__ * x_;
            let cos = angle.cos();
            let sin = angle.sin();
            let base = &a__ + &b__ * &cos + &c__ * &sin;
            let disc = a__.pow(2) - b__.pow(2) - c__.pow(2);
            let recursive = rubi_rhs_int(&(Atom::num(1) / &base), x_);

            rubi_simp(&((&c__ * &capital_b__ - &b__ * &capital_c__ - (&a__ * &capital_c__ - &c__ * &capital_a__) * cos
                    + (&a__ * &capital_b__ - &b__ * &capital_a__) * sin)
                    / (&e__ * &disc * base)), x_)
                    + rubi_star((&a__ * &capital_a__
                            - &b__ * &capital_b__
                            - &c__ * &capital_c__)
                            / &disc, recursive)
        },
    ));
}

fn push_rules_rule_3633(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_a__, capital_c__, a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 3633,
        source: "Int[(A_.+C_.*sin[d_.+e_.*x_])/(a_.+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_])^2,x_Symbol] :=
          -(b*C+(a*C-c*A)*Cos[d+e*x]+b*A*Sin[d+e*x])/(e*(a^2-b^2-c^2)*(a+b*Cos[d+e*x]+c*Sin[d+e*x])) +
          (a*A-c*C)/(a^2-b^2-c^2) \\[Star] Int[1/(a+b*Cos[d+e*x]+c*Sin[d+e*x]),x] /;
        FreeQ[{a,b,c,d,e,A,C},x] && NeQ[a^2-b^2-c^2,0] && NeQ[a*A-c*C,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: ["G&R 2.558.1a with n=-2"],
        pattern:  rubi_shared_pattern_10(symbols),
        with: [capital_a__, capital_c__, d__, e__, a__, b__, c__, x_],
        optional: [capital_a__, capital_c__, a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__, capital_a__, capital_c__], x_)
                && neq!(a__.pow(2) - b__.pow(2) - c__.pow(2), 0)
                && neq!(&a__ * &capital_a__ - &c__ * &capital_c__, 0)
        },
        rhs: {
            let angle = &d__ + &e__ * x_;
            let cos = angle.cos();
            let sin = angle.sin();
            let base = &a__ + &b__ * &cos + &c__ * &sin;
            let disc = a__.pow(2) - b__.pow(2) - c__.pow(2);
            let recursive = rubi_rhs_int(&(Atom::num(1) / &base), x_);

            rubi_simp(&(-(&b__ * &capital_c__ + (&a__ * &capital_c__ - &c__ * &capital_a__) * cos + &b__ * &capital_a__ * sin)
                    / (&e__ * &disc * base)), x_)
                    + rubi_star((&a__ * &capital_a__ - &c__ * &capital_c__) / &disc, recursive)
        },
    ));
}

fn push_rules_rule_3634(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_a__, capital_b__, a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 3634,
        source: "Int[(A_.+B_.*cos[d_.+e_.*x_])/(a_.+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_])^2,x_Symbol] :=
          (c*B+c*A*Cos[d+e*x]+(a*B-b*A)*Sin[d+e*x])/(e*(a^2-b^2-c^2)*(a+b*Cos[d+e*x]+c*Sin[d+e*x])) +
          (a*A-b*B)/(a^2-b^2-c^2) \\[Star] Int[1/(a+b*Cos[d+e*x]+c*Sin[d+e*x]),x] /;
        FreeQ[{a,b,c,d,e,A,B},x] && NeQ[a^2-b^2-c^2,0] && NeQ[a*A-b*B,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: ["G&R 2.558.1a with n=-2"],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [capital_a__, capital_b__, d__, e__, a__, b__, c__, x_],
        optional: [capital_a__, capital_b__, a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__, capital_a__, capital_b__], x_)
                && neq!(a__.pow(2) - b__.pow(2) - c__.pow(2), 0)
                && neq!(&a__ * &capital_a__ - &b__ * &capital_b__, 0)
        },
        rhs: {
            let angle = &d__ + &e__ * x_;
            let cos = angle.cos();
            let sin = angle.sin();
            let base = &a__ + &b__ * &cos + &c__ * &sin;
            let disc = a__.pow(2) - b__.pow(2) - c__.pow(2);
            let recursive = rubi_rhs_int(&(Atom::num(1) / &base), x_);

            rubi_simp(&((&c__ * &capital_b__ + &c__ * &capital_a__ * cos + (&a__ * &capital_b__ - &b__ * &capital_a__) * sin)
                    / (&e__ * &disc * base)), x_)
                    + rubi_star((&a__ * &capital_a__ - &b__ * &capital_b__) / &disc, recursive)
        },
    ));
}

fn push_rules_rule_3635(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_a__,
        capital_b__,
        capital_c__,
        a__,
        b__,
        c__,
        d__,
        e__,
        n_,
        x_
    );
    rules.push(rubi_rule!(
        order: 3635,
        source: "Int[(A_.+B_.*cos[d_.+e_.*x_]+C_.*sin[d_.+e_.*x_])*(a_.+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_])^n_,x_Symbol] :=
          -(c*B-b*C-(a*C-c*A)*Cos[d+e*x]+(a*B-b*A)*Sin[d+e*x])*(a+b*Cos[d+e*x]+c*Sin[d+e*x])^(n+1)/
            (e*(n+1)*(a^2-b^2-c^2)) +
          1/((n+1)*(a^2-b^2-c^2)) \\[Star] Int[(a+b*Cos[d+e*x]+c*Sin[d+e*x])^(n+1)*
            Simp[(n+1)*(a*A-b*B-c*C)+(n+2)*(a*B-b*A)*Cos[d+e*x]+(n+2)*(a*C-c*A)*Sin[d+e*x],x],x] /;
        FreeQ[{a,b,c,d,e,A,B,C},x] && LtQ[n,-1] && NeQ[a^2-b^2-c^2,0] && NeQ[n,-2]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: ["G&R 2.558.1a"],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [capital_a__, capital_b__, capital_c__, d__, e__, a__, b__, c__, n_, x_],
        optional: [capital_a__, capital_b__, capital_c__, a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__, capital_a__, capital_b__, capital_c__], x_)
                && ltq!(n_, -1)
                && neq!(a__.pow(2) - b__.pow(2) - c__.pow(2), 0)
                && neq!(n_, -2)
        },
        rhs: {
            let angle = &d__ + &e__ * x_;
            let cos = angle.cos();
            let sin = angle.sin();
            let base = &a__ + &b__ * &cos + &c__ * &sin;
            let disc = a__.pow(2) - b__.pow(2) - c__.pow(2);
            let n1 = &n_ + 1;
            let n2 = &n_ + 2;
            let numerator = &c__ * &capital_b__ - &b__ * &capital_c__
                - (&a__ * &capital_c__ - &c__ * &capital_a__) * &cos
                + (&a__ * &capital_b__ - &b__ * &capital_a__) * &sin;
            let payload = rubi_simp(
                &(&n1 * (&a__ * &capital_a__ - &b__ * &capital_b__ - &c__ * &capital_c__)
                    + &n2 * (&a__ * &capital_b__ - &b__ * &capital_a__) * &cos
                    + &n2 * (&a__ * &capital_c__ - &c__ * &capital_a__) * &sin),
                x_,
            );
            let base_power = base.pow(&n1);
            let recursive = rubi_rhs_int(&(&base_power * payload), x_);

            rubi_simp(&(-numerator * &base_power / (&e__ * &n1 * &disc)), x_)
                    + rubi_star(Atom::num(1) / (&n1 * disc), recursive)
        },
    ));
}

fn push_rules_rule_3636(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_a__, capital_c__, a__, b__, c__, d__, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 3636,
        source: "Int[(A_.+C_.*sin[d_.+e_.*x_])*(a_.+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_])^n_,x_Symbol] :=
          (b*C+(a*C-c*A)*Cos[d+e*x]+b*A*Sin[d+e*x])*(a+b*Cos[d+e*x]+c*Sin[d+e*x])^(n+1)/
            (e*(n+1)*(a^2-b^2-c^2)) +
          1/((n+1)*(a^2-b^2-c^2)) \\[Star] Int[(a+b*Cos[d+e*x]+c*Sin[d+e*x])^(n+1)*
            Simp[(n+1)*(a*A-c*C)-(n+2)*b*A*Cos[d+e*x]+(n+2)*(a*C-c*A)*Sin[d+e*x],x],x] /;
        FreeQ[{a,b,c,d,e,A,C},x] && LtQ[n,-1] && NeQ[a^2-b^2-c^2,0] && NeQ[n,-2]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: ["G&R 2.558.1a"],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [capital_a__, capital_c__, d__, e__, a__, b__, c__, n_, x_],
        optional: [capital_a__, capital_c__, a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__, capital_a__, capital_c__], x_)
                && ltq!(n_, -1)
                && neq!(a__.pow(2) - b__.pow(2) - c__.pow(2), 0)
                && neq!(n_, -2)
        },
        rhs: {
            let angle = &d__ + &e__ * x_;
            let cos = angle.cos();
            let sin = angle.sin();
            let base = &a__ + &b__ * &cos + &c__ * &sin;
            let disc = a__.pow(2) - b__.pow(2) - c__.pow(2);
            let n1 = &n_ + 1;
            let n2 = &n_ + 2;
            let numerator = &b__ * &capital_c__
                + (&a__ * &capital_c__ - &c__ * &capital_a__) * &cos
                + &b__ * &capital_a__ * &sin;
            let payload = rubi_simp(
                &(&n1 * (&a__ * &capital_a__ - &c__ * &capital_c__)
                    - &n2 * &b__ * &capital_a__ * &cos
                    + &n2 * (&a__ * &capital_c__ - &c__ * &capital_a__) * &sin),
                x_,
            );
            let base_power = base.pow(&n1);
            let recursive = rubi_rhs_int(&(&base_power * payload), x_);

            rubi_simp(&(numerator * &base_power / (&e__ * &n1 * &disc)), x_)
                    + rubi_star(Atom::num(1) / (&n1 * disc), recursive)
        },
    ));
}

fn push_rules_rule_3637(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_a__, capital_b__, a__, b__, c__, d__, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 3637,
        source: "Int[(A_.+B_.*cos[d_.+e_.*x_])*(a_.+b_.*cos[d_.+e_.*x_]+c_.*sin[d_.+e_.*x_])^n_,x_Symbol] :=
          -(c*B+c*A*Cos[d+e*x]+(a*B-b*A)*Sin[d+e*x])*(a+b*Cos[d+e*x]+c*Sin[d+e*x])^(n+1)/
            (e*(n+1)*(a^2-b^2-c^2)) +
          1/((n+1)*(a^2-b^2-c^2)) \\[Star] Int[(a+b*Cos[d+e*x]+c*Sin[d+e*x])^(n+1)*
            Simp[(n+1)*(a*A-b*B)+(n+2)*(a*B-b*A)*Cos[d+e*x]-(n+2)*c*A*Sin[d+e*x],x],x] /;
        FreeQ[{a,b,c,d,e,A,B},x] && LtQ[n,-1] && NeQ[a^2-b^2-c^2,0] && NeQ[n,-2]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: ["G&R 2.558.1a"],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [capital_a__, capital_b__, d__, e__, a__, b__, c__, n_, x_],
        optional: [capital_a__, capital_b__, a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__, capital_a__, capital_b__], x_)
                && ltq!(n_, -1)
                && neq!(a__.pow(2) - b__.pow(2) - c__.pow(2), 0)
                && neq!(n_, -2)
        },
        rhs: {
            let angle = &d__ + &e__ * x_;
            let cos = angle.cos();
            let sin = angle.sin();
            let base = &a__ + &b__ * &cos + &c__ * &sin;
            let disc = a__.pow(2) - b__.pow(2) - c__.pow(2);
            let n1 = &n_ + 1;
            let n2 = &n_ + 2;
            let numerator = &c__ * &capital_b__
                + &c__ * &capital_a__ * &cos
                + (&a__ * &capital_b__ - &b__ * &capital_a__) * &sin;
            let payload = rubi_simp(
                &(&n1 * (&a__ * &capital_a__ - &b__ * &capital_b__)
                    + &n2 * (&a__ * &capital_b__ - &b__ * &capital_a__) * &cos
                    - &n2 * &c__ * &capital_a__ * &sin),
                x_,
            );
            let base_power = base.pow(&n1);
            let recursive = rubi_rhs_int(&(&base_power * payload), x_);

            rubi_simp(&(-numerator * &base_power / (&e__ * &n1 * &disc)), x_)
                    + rubi_star(Atom::num(1) / (&n1 * disc), recursive)
        },
    ));
}

fn push_rules_rule_3638(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 3638,
        source: "Int[1/(a_.+b_.*sec[d_.+e_.*x_]+c_.*tan[d_.+e_.*x_]),x_Symbol] :=
          Int[Cos[d+e*x]/(b+a*Cos[d+e*x]+c*Sin[d+e*x]),x] /;
        FreeQ[{a,b,c,d,e},x]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: Atom::num(1)
            / (a__ + b__ * i_sec(d__ + e__ * x_) + c__ * i_tan(d__ + e__ * x_)),
        with: [a__, b__, c__, d__, e__, x_],
        optional: [a__, b__, c__, d__, e__],
        when: { freeq!([a__, b__, c__, d__, e__], x_) },
        rhs: {
            let angle = &d__ + &e__ * x_;
            let payload = angle.cos() / (&b__ + &a__ * angle.cos() + &c__ * angle.sin());

            rubi_rhs_int(&payload, x_)
        },
    ));
}

fn push_rules_rule_3639(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 3639,
        source: "Int[1/(a_.+b_.*csc[d_.+e_.*x_]+c_.*cot[d_.+e_.*x_]),x_Symbol] :=
          Int[Sin[d+e*x]/(b+a*Sin[d+e*x]+c*Cos[d+e*x]),x] /;
        FreeQ[{a,b,c,d,e},x]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: Atom::num(1)
            / (a__ + b__ * i_csc(d__ + e__ * x_) + c__ * i_cot(d__ + e__ * x_)),
        with: [a__, b__, c__, d__, e__, x_],
        optional: [a__, b__, c__, d__, e__],
        when: { freeq!([a__, b__, c__, d__, e__], x_) },
        rhs: {
            let angle = &d__ + &e__ * x_;
            let payload = angle.sin() / (&b__ + &a__ * angle.sin() + &c__ * angle.cos());

            rubi_rhs_int(&payload, x_)
        },
    ));
}

fn push_rules_rule_3640(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 3640,
        source: "Int[cos[d_.+e_.*x_]^n_.*(a_.+b_.*sec[d_.+e_.*x_]+c_.*tan[d_.+e_.*x_])^n_.,x_Symbol] :=
          Int[(b+a*Cos[d+e*x]+c*Sin[d+e*x])^n,x] /;
        FreeQ[{a,b,c,d,e},x] && IntegerQ[n]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_13(symbols),
        with: [a__, b__, c__, d__, e__, n_, x_],
        optional: [a__, b__, c__, d__, e__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && integerq!(n_)
        },
        rhs: {
            let angle = &d__ + &e__ * x_;
            let payload = (&b__ + &a__ * angle.cos() + &c__ * angle.sin()).pow(n_);

            rubi_rhs_int(&payload, x_)
        },
    ));
}

fn push_rules_rule_3641(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 3641,
        source: "Int[sin[d_.+e_.*x_]^n_.*(a_.+b_.*csc[d_.+e_.*x_]+c_.*cot[d_.+e_.*x_])^n_.,x_Symbol] :=
          Int[(b+a*Sin[d+e*x]+c*Cos[d+e*x])^n,x] /;
        FreeQ[{a,b,c,d,e},x] && IntegerQ[n]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_16(symbols),
        with: [a__, b__, c__, d__, e__, n_, x_],
        optional: [a__, b__, c__, d__, e__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && integerq!(n_)
        },
        rhs: {
            let angle = &d__ + &e__ * x_;
            let payload = (&b__ + &a__ * angle.sin() + &c__ * angle.cos()).pow(n_);

            rubi_rhs_int(&payload, x_)
        },
    ));
}

fn push_rules_rule_3642(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 3642,
        source: "Int[cos[d_.+e_.*x_]^n_*(a_.+b_.*sec[d_.+e_.*x_]+c_.*tan[d_.+e_.*x_])^n_,x_Symbol] :=
          Cos[d+e*x]^n*(a+b*Sec[d+e*x]+c*Tan[d+e*x])^n/(b+a*Cos[d+e*x]+c*Sin[d+e*x])^n \\[Star] Int[(b+a*Cos[d+e*x]+c*Sin[d+e*x])^n,x] /;
        FreeQ[{a,b,c,d,e},x] && Not[IntegerQ[n]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_13(symbols),
        with: [a__, b__, c__, d__, e__, n_, x_],
        optional: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && !integerq!(n_)
        },
        rhs: {
            let angle = &d__ + &e__ * x_;
            let source_base = &a__ + &b__ * angle.sec() + &c__ * angle.tan();
            let transformed = &b__ + &a__ * angle.cos() + &c__ * angle.sin();
            let recursive = rubi_rhs_int(&transformed.pow(&n_), x_);

            rubi_star(angle.cos().pow(&n_) * source_base.pow(&n_) / transformed.pow(&n_), recursive)
        },
    ));
}

fn push_rules_rule_3643(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 3643,
        source: "Int[sin[d_.+e_.*x_]^n_*(a_.+b_.*csc[d_.+e_.*x_]+c_.*cot[d_.+e_.*x_])^n_,x_Symbol] :=
          Sin[d+e*x]^n*(a+b*Csc[d+e*x]+c*Cot[d+e*x])^n/(b+a*Sin[d+e*x]+c*Cos[d+e*x])^n \\[Star] Int[(b+a*Sin[d+e*x]+c*Cos[d+e*x])^n,x] /;
        FreeQ[{a,b,c,d,e},x] && Not[IntegerQ[n]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_16(symbols),
        with: [a__, b__, c__, d__, e__, n_, x_],
        optional: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && !integerq!(n_)
        },
        rhs: {
            let angle = &d__ + &e__ * x_;
            let source_base = &a__ + &b__ * angle.csc() + &c__ * angle.cot();
            let transformed = &b__ + &a__ * angle.sin() + &c__ * angle.cos();
            let recursive = rubi_rhs_int(&transformed.pow(&n_), x_);

            rubi_star(angle.sin().pow(&n_) * source_base.pow(&n_) / transformed.pow(&n_), recursive)
        },
    ));
}

fn push_rules_rule_3644(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 3644,
        source: "Int[sec[d_.+e_.*x_]^n_.*(a_.+b_.*sec[d_.+e_.*x_]+c_.*tan[d_.+e_.*x_])^m_,x_Symbol] :=
          Int[1/(b+a*Cos[d+e*x]+c*Sin[d+e*x])^n,x] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[m+n,0] && IntegerQ[n]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_15(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, x_],
        optional: [a__, b__, c__, d__, e__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(&m_ + &n_, 0)
                && integerq!(n_)
        },
        rhs: {
            let angle = &d__ + &e__ * x_;
            let transformed = &b__ + &a__ * angle.cos() + &c__ * angle.sin();
            let payload = Atom::num(1) / transformed.pow(n_);

            rubi_rhs_int(&payload, x_)
        },
    ));
}

fn push_rules_rule_3645(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 3645,
        source: "Int[csc[d_.+e_.*x_]^n_.*(a_.+b_.*csc[d_.+e_.*x_]+c_.*cot[d_.+e_.*x_])^m_,x_Symbol] :=
          Int[1/(b+a*Sin[d+e*x]+c*Cos[d+e*x])^n,x] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[m+n,0] && IntegerQ[n]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_14(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, x_],
        optional: [a__, b__, c__, d__, e__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(&m_ + &n_, 0)
                && integerq!(n_)
        },
        rhs: {
            let angle = &d__ + &e__ * x_;
            let transformed = &b__ + &a__ * angle.sin() + &c__ * angle.cos();
            let payload = Atom::num(1) / transformed.pow(n_);

            rubi_rhs_int(&payload, x_)
        },
    ));
}

fn push_rules_rule_3646(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 3646,
        source: "Int[sec[d_.+e_.*x_]^n_.*(a_.+b_.*sec[d_.+e_.*x_]+c_.*tan[d_.+e_.*x_])^m_,x_Symbol] :=
          Sec[d+e*x]^n*(b+a*Cos[d+e*x]+c*Sin[d+e*x])^n/(a+b*Sec[d+e*x]+c*Tan[d+e*x])^n \\[Star] Int[1/(b+a*Cos[d+e*x]+c*Sin[d+e*x])^n,x] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[m+n,0] && Not[IntegerQ[n]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_15(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, x_],
        optional: [a__, b__, c__, d__, e__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(&m_ + &n_, 0)
                && !integerq!(n_)
        },
        rhs: {
            let angle = &d__ + &e__ * x_;
            let source_base = &a__ + &b__ * angle.sec() + &c__ * angle.tan();
            let transformed = &b__ + &a__ * angle.cos() + &c__ * angle.sin();
            let recursive = rubi_rhs_int(&(Atom::num(1) / transformed.pow(&n_)), x_);

            rubi_star(angle.sec().pow(&n_) * transformed.pow(&n_) / source_base.pow(&n_), recursive)
        },
    ));
}

fn push_rules_rule_3647(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 3647,
        source: "Int[csc[d_.+e_.*x_]^n_.*(a_.+b_.*csc[d_.+e_.*x_]+c_.*cot[d_.+e_.*x_])^m_,x_Symbol] :=
          Csc[d+e*x]^n*(b+a*Sin[d+e*x]+c*Cos[d+e*x])^n/(a+b*Csc[d+e*x]+c*Cot[d+e*x])^n \\[Star] Int[1/(b+a*Sin[d+e*x]+c*Cos[d+e*x])^n,x] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[m+n,0] && Not[IntegerQ[n]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_14(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, x_],
        optional: [a__, b__, c__, d__, e__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(&m_ + &n_, 0)
                && !integerq!(n_)
        },
        rhs: {
            let angle = &d__ + &e__ * x_;
            let source_base = &a__ + &b__ * angle.csc() + &c__ * angle.cot();
            let transformed = &b__ + &a__ * angle.sin() + &c__ * angle.cos();
            let recursive = rubi_rhs_int(&(Atom::num(1) / transformed.pow(&n_)), x_);

            rubi_star(angle.csc().pow(&n_) * transformed.pow(&n_) / source_base.pow(&n_), recursive)
        },
    ));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn downvalues_3591_through_3592_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .filter(|order| (3591..=3592).contains(order))
            .collect::<Vec<_>>();
        assert_eq!(orders, (3591..=3592).collect::<Vec<_>>());
    }

    #[test]
    fn downvalues_3593_through_3642_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .filter(|order| (3593..=3642).contains(order))
            .collect::<Vec<_>>();
        assert_eq!(orders, (3593..=3642).collect::<Vec<_>>());
    }

    #[test]
    fn downvalues_3643_through_3647_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .filter(|order| (3643..=3647).contains(order))
            .collect::<Vec<_>>();
        assert_eq!(orders, (3643..=3647).collect::<Vec<_>>());
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
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    (a__ + b__ * i_cos(d__ + e__ * x_) + c__ * i_sin(d__ + e__ * x_)).pow(n_)
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let x_ = symbols.x_;
    (a__ + b__ * i_cos(d__ + e__ * x_) + c__ * i_sin(d__ + e__ * x_)).sqrt()
}

#[inline(never)]
fn rubi_shared_pattern_2(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let capital_a__ = symbols.capital_a__;
    let capital_b__ = symbols.capital_b__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    (capital_a__ + capital_b__ * i_cos(d__ + e__ * x_))
        * (a__ + b__ * i_cos(d__ + e__ * x_) + c__ * i_sin(d__ + e__ * x_)).pow(n_)
}

#[inline(never)]
fn rubi_shared_pattern_3(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let capital_a__ = symbols.capital_a__;
    let capital_b__ = symbols.capital_b__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let x_ = symbols.x_;
    (capital_a__ + capital_b__ * i_cos(d__ + e__ * x_))
        / (a__ + b__ * i_cos(d__ + e__ * x_) + c__ * i_sin(d__ + e__ * x_))
}

#[inline(never)]
fn rubi_shared_pattern_4(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let capital_a__ = symbols.capital_a__;
    let capital_b__ = symbols.capital_b__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let x_ = symbols.x_;
    (capital_a__ + capital_b__ * i_cos(d__ + e__ * x_))
        / (a__ + b__ * i_cos(d__ + e__ * x_) + c__ * i_sin(d__ + e__ * x_)).pow(2)
}

#[inline(never)]
fn rubi_shared_pattern_5(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let capital_a__ = symbols.capital_a__;
    let capital_b__ = symbols.capital_b__;
    let capital_c__ = symbols.capital_c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    (capital_a__ + capital_b__ * i_cos(d__ + e__ * x_) + capital_c__ * i_sin(d__ + e__ * x_))
        * (a__ + b__ * i_cos(d__ + e__ * x_) + c__ * i_sin(d__ + e__ * x_)).pow(n_)
}

#[inline(never)]
fn rubi_shared_pattern_6(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let capital_a__ = symbols.capital_a__;
    let capital_b__ = symbols.capital_b__;
    let capital_c__ = symbols.capital_c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let x_ = symbols.x_;
    (capital_a__ + capital_b__ * i_cos(d__ + e__ * x_) + capital_c__ * i_sin(d__ + e__ * x_))
        / (a__ + b__ * i_cos(d__ + e__ * x_) + c__ * i_sin(d__ + e__ * x_))
}

#[inline(never)]
fn rubi_shared_pattern_7(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let capital_a__ = symbols.capital_a__;
    let capital_b__ = symbols.capital_b__;
    let capital_c__ = symbols.capital_c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let x_ = symbols.x_;
    (capital_a__ + capital_b__ * i_cos(d__ + e__ * x_) + capital_c__ * i_sin(d__ + e__ * x_))
        / (a__ + b__ * i_cos(d__ + e__ * x_) + c__ * i_sin(d__ + e__ * x_)).pow(2)
}

#[inline(never)]
fn rubi_shared_pattern_8(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let capital_a__ = symbols.capital_a__;
    let capital_c__ = symbols.capital_c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    (capital_a__ + capital_c__ * i_sin(d__ + e__ * x_))
        * (a__ + b__ * i_cos(d__ + e__ * x_) + c__ * i_sin(d__ + e__ * x_)).pow(n_)
}

#[inline(never)]
fn rubi_shared_pattern_9(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let capital_a__ = symbols.capital_a__;
    let capital_c__ = symbols.capital_c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let x_ = symbols.x_;
    (capital_a__ + capital_c__ * i_sin(d__ + e__ * x_))
        / (a__ + b__ * i_cos(d__ + e__ * x_) + c__ * i_sin(d__ + e__ * x_))
}

#[inline(never)]
fn rubi_shared_pattern_10(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let capital_a__ = symbols.capital_a__;
    let capital_c__ = symbols.capital_c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let x_ = symbols.x_;
    (capital_a__ + capital_c__ * i_sin(d__ + e__ * x_))
        / (a__ + b__ * i_cos(d__ + e__ * x_) + c__ * i_sin(d__ + e__ * x_)).pow(2)
}

#[inline(never)]
fn rubi_shared_pattern_11(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let x_ = symbols.x_;
    Atom::num(1) / (a__ + b__ * i_cos(d__ + e__ * x_) + c__ * i_sin(d__ + e__ * x_))
}

#[inline(never)]
fn rubi_shared_pattern_12(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let x_ = symbols.x_;
    Atom::num(1) / (a__ + b__ * i_cos(d__ + e__ * x_) + c__ * i_sin(d__ + e__ * x_)).sqrt()
}

#[inline(never)]
fn rubi_shared_pattern_13(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    i_cos(d__ + e__ * x_).pow(n_)
        * (a__ + b__ * i_sec(d__ + e__ * x_) + c__ * i_tan(d__ + e__ * x_)).pow(n_)
}

#[inline(never)]
fn rubi_shared_pattern_14(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    i_csc(d__ + e__ * x_).pow(n_)
        * (a__ + b__ * i_csc(d__ + e__ * x_) + c__ * i_cot(d__ + e__ * x_)).pow(m_)
}

#[inline(never)]
fn rubi_shared_pattern_15(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    i_sec(d__ + e__ * x_).pow(n_)
        * (a__ + b__ * i_sec(d__ + e__ * x_) + c__ * i_tan(d__ + e__ * x_)).pow(m_)
}

#[inline(never)]
fn rubi_shared_pattern_16(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    i_sin(d__ + e__ * x_).pow(n_)
        * (a__ + b__ * i_csc(d__ + e__ * x_) + c__ * i_cot(d__ + e__ * x_)).pow(n_)
}
