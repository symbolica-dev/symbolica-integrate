use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_3550(rules);
    push_rules_rule_3551(rules);
    push_rules_rule_3552(rules);
    push_rules_rule_3553(rules);
    push_rules_rule_3554(rules);
    push_rules_rule_3555(rules);
    push_rules_rule_3556(rules);
    push_rules_rule_3557(rules);
    push_rules_rule_3558(rules);
    push_rules_rule_3559(rules);
    push_rules_rule_3560(rules);
    push_rules_rule_3561(rules);
    push_rules_rule_3562(rules);
    push_rules_rule_3563(rules);
    push_rules_rule_3564(rules);
    push_rules_rule_3565(rules);
    push_rules_rule_3566(rules);
    push_rules_rule_3567(rules);
    push_rules_rule_3568(rules);
    push_rules_rule_3569(rules);
    push_rules_rule_3570(rules);
    push_rules_rule_3571(rules);
    push_rules_rule_3572(rules);
    push_rules_rule_3573(rules);
    push_rules_rule_3574(rules);
    push_rules_rule_3575(rules);
    push_rules_rule_3576(rules);
    push_rules_rule_3577(rules);
    push_rules_rule_3578(rules);
    push_rules_rule_3579(rules);
    push_rules_rule_3580(rules);
    push_rules_rule_3581(rules);
    push_rules_rule_3582(rules);
    push_rules_rule_3583(rules);
    push_rules_rule_3584(rules);
    push_rules_rule_3585(rules);
    push_rules_rule_3586(rules);
    push_rules_rule_3587(rules);
    push_rules_rule_3588(rules);
    push_rules_rule_3589(rules);
    push_rules_rule_3590(rules);
}

fn push_rules_rule_3550(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 3550,
        source: "Int[(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
          a*(a*Cos[c+d*x]+b*Sin[c+d*x])^n/(b*d*n) /;
        FreeQ[{a,b,c,d,n},x] && EqQ[a^2+b^2,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: ["Integration by substitution"],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, c__, d__, b__, n_, x_],
        optional: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, n_], x_)
                && eqq!(a__.pow(2) + b__.pow(2), 0)
        },
        rhs: {
            let angle = &c__ + &d__ * x_;

            rubi_simp(&(&a__ * (&a__ * angle.cos() + &b__ * angle.sin()).pow(&n_)
                    / (&b__ * &d__ * &n_)), x_)
        },
    ));
}

fn push_rules_rule_3551(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 3551,
        source: "Int[(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
          -1/d \\[Star] Subst[Int[(a^2+b^2-x^2)^((n-1)/2),x],x,b*Cos[c+d*x]-a*Sin[c+d*x]] /;
        FreeQ[{a,b,c,d},x] && NeQ[a^2+b^2,0] && IGtQ[(n-1)/2,0]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, c__, d__, b__, n_, x_],
        optional: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && neq!(a__.pow(2) + b__.pow(2), 0)
                && igtq!((&n_ - 1) / 2, 0)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let angle = &c__ + &d__ * x_;
            let primitive = rubi_rhs_int(
                &((a__.pow(2) + b__.pow(2) - sub_atom.pow(2)).pow((&n_ - 1) / 2)),
                sub,
            );

            rubi_star(-(Atom::num(1) / &d__), rubi_subst(&primitive, sub, &b__ * angle.cos() - &a__ * angle.sin()))
        },
    ));
}

fn push_rules_rule_3552(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 3552,
        source: "Int[(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
          -(b*Cos[c+d*x]-a*Sin[c+d*x])*(a*Cos[c+d*x]+b*Sin[c+d*x])^(n-1)/(d*n) +
          (n-1)*(a^2+b^2)/n \\[Star] Int[(a*Cos[c+d*x]+b*Sin[c+d*x])^(n-2),x] /;
        FreeQ[{a,b,c,d},x] && NeQ[a^2+b^2,0] && Not[IntegerQ[(n-1)/2]] && GtQ[n,1]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, c__, d__, b__, n_, x_],
        optional: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && neq!(a__.pow(2) + b__.pow(2), 0)
                && !integerq!((&n_ - 1) / 2)
                && gtq!(n_, 1)
        },
        rhs: {
            let angle = &c__ + &d__ * x_;
            let linear = &a__ * angle.cos() + &b__ * angle.sin();
            let recursive = rubi_rhs_int(&linear.pow(&n_ - 2), x_);

            rubi_simp(&(-(&b__ * angle.cos() - &a__ * angle.sin()) * linear.pow(&n_ - 1)
                    / (&d__ * &n_)), x_)
                    + rubi_star((&n_ - 1) * (a__.pow(2) + b__.pow(2)) / &n_, recursive)
        },
    ));
}

fn push_rules_rule_3553(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 3553,
        source: "Int[1/(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_]),x_Symbol] :=
          -1/d \\[Star] Subst[Int[1/(a^2+b^2-x^2),x],x,b*Cos[c+d*x]-a*Sin[c+d*x]] /;
        FreeQ[{a,b,c,d},x] && NeQ[a^2+b^2,0]",
        desc: "Integration by substitution",
        refs: ["G&R 2.557'"],
        pattern: 1 / (a__ * i_cos(c__ + d__ * x_) + b__ * i_sin(c__ + d__ * x_)),
        with: [a__, c__, d__, b__, x_],
        optional: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && neq!(a__.pow(2) + b__.pow(2), 0)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let angle = &c__ + &d__ * x_;
            let primitive =
                rubi_rhs_int(&(1 / (a__.pow(2) + b__.pow(2) - sub_atom.pow(2))), sub);

            rubi_star(-(Atom::num(1) / &d__), rubi_subst(&primitive, sub, &b__ * angle.cos() - &a__ * angle.sin()))
        },
    ));
}

fn push_rules_rule_3554(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 3554,
        source: "Int[1/(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_])^2,x_Symbol] :=
          Sin[c+d*x]/(a*d*(a*Cos[c+d*x]+b*Sin[c+d*x])) /;
        FreeQ[{a,b,c,d},x] && NeQ[a^2+b^2,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: ["G&R 2.557.5b'"],
        pattern: 1 / (a__ * i_cos(c__ + d__ * x_) + b__ * i_sin(c__ + d__ * x_)).pow(2),
        with: [a__, c__, d__, b__, x_],
        optional: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && neq!(a__.pow(2) + b__.pow(2), 0)
        },
        rhs: {
            let angle = &c__ + &d__ * x_;

            rubi_simp(&(angle.sin() / (&a__ * &d__ * (&a__ * angle.cos() + &b__ * angle.sin()))), x_)
        },
    ));
}

fn push_rules_rule_3555(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 3555,
        source: "Int[(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
          (b*Cos[c+d*x]-a*Sin[c+d*x])*(a*Cos[c+d*x]+b*Sin[c+d*x])^(n+1)/(d*(n+1)*(a^2+b^2)) +
          (n+2)/((n+1)*(a^2+b^2)) \\[Star] Int[(a*Cos[c+d*x]+b*Sin[c+d*x])^(n+2),x] /;
        FreeQ[{a,b,c,d},x] && NeQ[a^2+b^2,0] && LtQ[n,-1] && NeQ[n,-2]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, c__, d__, b__, n_, x_],
        optional: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && neq!(a__.pow(2) + b__.pow(2), 0)
                && ltq!(n_, -1)
                && neq!(n_, -2)
        },
        rhs: {
            let angle = &c__ + &d__ * x_;
            let linear = &a__ * angle.cos() + &b__ * angle.sin();
            let recursive = rubi_rhs_int(&linear.pow(&n_ + 2), x_);
            let coefficient =
                (&n_ + 2) / ((&n_ + 1) * (a__.pow(2) + b__.pow(2)));

            rubi_simp(&((&b__ * angle.cos() - &a__ * angle.sin()) * linear.pow(&n_ + 1)
                    / (&d__ * (&n_ + 1) * (a__.pow(2) + b__.pow(2)))), x_)
                    + rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_3556(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 3556,
        source: "Int[(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
          (a^2+b^2)^(n/2) \\[Star] Int[(Cos[c+d*x-ArcTan[a,b]])^n,x] /;
        FreeQ[{a,b,c,d,n},x] && Not[GeQ[n,1] || LeQ[n,-1]] && GtQ[a^2+b^2,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, c__, d__, b__, n_, x_],
        optional: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, n_], x_)
                && !(geq!(n_, 1) || leq!(n_, -1))
                && gtq!(a__.pow(2) + b__.pow(2), 0)
        },
        rhs: {
            let angle = &c__ + &d__ * x_;
            let arc_tan = symbol!("ArcTan").call((&a__, &b__));
            let recursive = rubi_rhs_int(&(angle - arc_tan).cos().pow(&n_), x_);

            rubi_star((a__.pow(2) + b__.pow(2)).pow(&n_ / 2), recursive)
        },
    ));
}

fn push_rules_rule_3557(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 3557,
        source: "Int[(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
          (a*Cos[c+d*x]+b*Sin[c+d*x])^n/((a*Cos[c+d*x]+b*Sin[c+d*x])/Sqrt[a^2+b^2])^n \\[Star] Int[Cos[c+d*x-ArcTan[a,b]]^n,x] /;
        FreeQ[{a,b,c,d,n},x] && Not[GeQ[n,1] || LeQ[n,-1]] && Not[GtQ[a^2+b^2,0] || EqQ[a^2+b^2,0]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, c__, d__, b__, n_, x_],
        optional: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, n_], x_)
                && !(geq!(n_, 1) || leq!(n_, -1))
                && !(gtq!(a__.pow(2) + b__.pow(2), 0) || eqq!(a__.pow(2) + b__.pow(2), 0))
        },
        rhs: {
            let angle = &c__ + &d__ * x_;
            let linear = &a__ * angle.cos() + &b__ * angle.sin();
            let arc_tan = symbol!("ArcTan").call((&a__, &b__));
            let recursive = rubi_rhs_int(&(angle - arc_tan).cos().pow(&n_), x_);

            rubi_star(linear.pow(&n_)
                    / (linear / (a__.pow(2) + b__.pow(2)).sqrt()).pow(n_), recursive)
        },
    ));
}

fn push_rules_rule_3558(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 3558,
        source: "Int[sin[c_.+d_.*x_]^m_*(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
          -a*(a*Cos[c+d*x]+b*Sin[c+d*x])^(n-1)/(d*(n-1)*Sin[c+d*x]^(n-1)) +
          2*b \\[Star] Int[(a*Cos[c+d*x]+b*Sin[c+d*x])^(n-1)/Sin[c+d*x]^(n-1),x] /;
        FreeQ[{a,b,c,d},x] && EqQ[m+n,0] && EqQ[a^2+b^2,0] && GtQ[n,1]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [c__, d__, m_, a__, b__, n_, x_],
        optional: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && eqq!(&m_ + &n_, 0)
                && eqq!(a__.pow(2) + b__.pow(2), 0)
                && gtq!(n_, 1)
        },
        rhs: {
            let angle = &c__ + &d__ * x_;
            let sin = angle.sin();
            let linear = &a__ * angle.cos() + &b__ * &sin;
            let recursive = rubi_rhs_int(&(linear.pow(&n_ - 1) / sin.pow(&n_ - 1)), x_);

            rubi_simp(&(-&a__ * linear.pow(&n_ - 1) / (&d__ * (&n_ - 1) * sin.pow(&n_ - 1))), x_)
                    + rubi_star(Atom::num(2) * &b__, recursive)
        },
    ));
}

fn push_rules_rule_3559(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 3559,
        source: "Int[cos[c_.+d_.*x_]^m_*(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
          b*(a*Cos[c+d*x]+b*Sin[c+d*x])^(n-1)/(d*(n-1)*Cos[c+d*x]^(n-1)) +
          2*a \\[Star] Int[(a*Cos[c+d*x]+b*Sin[c+d*x])^(n-1)/Cos[c+d*x]^(n-1),x] /;
        FreeQ[{a,b,c,d},x] && EqQ[m+n,0] && EqQ[a^2+b^2,0] && GtQ[n,1]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [c__, d__, m_, a__, b__, n_, x_],
        optional: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && eqq!(&m_ + &n_, 0)
                && eqq!(a__.pow(2) + b__.pow(2), 0)
                && gtq!(n_, 1)
        },
        rhs: {
            let angle = &c__ + &d__ * x_;
            let cos = angle.cos();
            let linear = &a__ * &cos + &b__ * angle.sin();
            let recursive = rubi_rhs_int(&(linear.pow(&n_ - 1) / cos.pow(&n_ - 1)), x_);

            rubi_simp(&(&b__ * linear.pow(&n_ - 1) / (&d__ * (&n_ - 1) * cos.pow(&n_ - 1))), x_)
                    + rubi_star(Atom::num(2) * &a__, recursive)
        },
    ));
}

fn push_rules_rule_3560(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 3560,
        source: "Int[sin[c_.+d_.*x_]^m_.*(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
          a*(a*Cos[c+d*x]+b*Sin[c+d*x])^n/(2*b*d*n*Sin[c+d*x]^n) +
          1/(2*b) \\[Star] Int[(a*Cos[c+d*x]+b*Sin[c+d*x])^(n+1)/Sin[c+d*x]^(n+1),x] /;
        FreeQ[{a,b,c,d},x] && EqQ[m+n,0] && EqQ[a^2+b^2,0] && LtQ[n,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [c__, d__, m_, a__, b__, n_, x_],
        optional: [a__, b__, c__, d__, m_],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && eqq!(&m_ + &n_, 0)
                && eqq!(a__.pow(2) + b__.pow(2), 0)
                && ltq!(n_, 0)
        },
        rhs: {
            let angle = &c__ + &d__ * x_;
            let sin = angle.sin();
            let linear = &a__ * angle.cos() + &b__ * &sin;
            let recursive = rubi_rhs_int(&(linear.pow(&n_ + 1) / sin.pow(&n_ + 1)), x_);

            rubi_simp(&(&a__ * linear.pow(&n_) / (Atom::num(2) * &b__ * &d__ * &n_ * sin.pow(&n_))), x_)
                    + rubi_star(Atom::num(1) / (Atom::num(2) * &b__), recursive)
        },
    ));
}

fn push_rules_rule_3561(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 3561,
        source: "Int[cos[c_.+d_.*x_]^m_.*(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
          -b*(a*Cos[c+d*x]+b*Sin[c+d*x])^n/(2*a*d*n*Cos[c+d*x]^n) +
          1/(2*a) \\[Star] Int[(a*Cos[c+d*x]+b*Sin[c+d*x])^(n+1)/Cos[c+d*x]^(n+1),x] /;
        FreeQ[{a,b,c,d},x] && EqQ[m+n,0] && EqQ[a^2+b^2,0] && LtQ[n,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [c__, d__, m_, a__, b__, n_, x_],
        optional: [a__, b__, c__, d__, m_],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && eqq!(&m_ + &n_, 0)
                && eqq!(a__.pow(2) + b__.pow(2), 0)
                && ltq!(n_, 0)
        },
        rhs: {
            let angle = &c__ + &d__ * x_;
            let cos = angle.cos();
            let linear = &a__ * &cos + &b__ * angle.sin();
            let recursive = rubi_rhs_int(&(linear.pow(&n_ + 1) / cos.pow(&n_ + 1)), x_);

            rubi_simp(&(-&b__ * linear.pow(&n_) / (Atom::num(2) * &a__ * &d__ * &n_ * cos.pow(&n_))), x_)
                    + rubi_star(Atom::num(1) / (Atom::num(2) * &a__), recursive)
        },
    ));
}

fn push_rules_rule_3562(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 3562,
        source: "Int[sin[c_.+d_.*x_]^m_.*(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
          a*(a*Cos[c+d*x]+b*Sin[c+d*x])^n/(2*b*d*n*Sin[c+d*x]^n)*Hypergeometric2F1[1,n,n+1,(b+a*Cot[c+d*x])/(2*b)] /;
        FreeQ[{a,b,c,d,n},x] && EqQ[m+n,0] && EqQ[a^2+b^2,0] && Not[IntegerQ[n]]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [c__, d__, m_, a__, b__, n_, x_],
        optional: [a__, b__, c__, d__, m_],
        when: {
            freeq!([a__, b__, c__, d__, n_], x_)
                && eqq!(&m_ + &n_, 0)
                && eqq!(a__.pow(2) + b__.pow(2), 0)
                && !integerq!(n_)
        },
        rhs: {
            let angle = &c__ + &d__ * x_;
            let sin = angle.sin();
            let linear = &a__ * angle.cos() + &b__ * &sin;

            rubi_simp(&(&a__ * linear.pow(&n_)
                    * rubi_hypergeometric2f1(
                        Atom::num(1),
                        n_.to_owned(),
                        &n_ + 1,
                        (&b__ + &a__ * angle.cot()) / (Atom::num(2) * &b__),
                    )
                    / (Atom::num(2) * &b__ * &d__ * &n_ * sin.pow(&n_))), x_)
        },
    ));
}

fn push_rules_rule_3563(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 3563,
        source: "Int[cos[c_.+d_.*x_]^m_.*(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
          -b*(a*Cos[c+d*x]+b*Sin[c+d*x])^n/(2*a*d*n*Cos[c+d*x]^n)*Hypergeometric2F1[1,n,n+1,(a+b*Tan[c+d*x])/(2*a)] /;
        FreeQ[{a,b,c,d,n},x] && EqQ[m+n,0] && EqQ[a^2+b^2,0] && Not[IntegerQ[n]]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [c__, d__, m_, a__, b__, n_, x_],
        optional: [a__, b__, c__, d__, m_],
        when: {
            freeq!([a__, b__, c__, d__, n_], x_)
                && eqq!(&m_ + &n_, 0)
                && eqq!(a__.pow(2) + b__.pow(2), 0)
                && !integerq!(n_)
        },
        rhs: {
            let angle = &c__ + &d__ * x_;
            let cos = angle.cos();
            let linear = &a__ * &cos + &b__ * angle.sin();

            rubi_simp(&(-&b__ * linear.pow(&n_)
                    * rubi_hypergeometric2f1(
                        Atom::num(1),
                        n_.to_owned(),
                        &n_ + 1,
                        (&a__ + &b__ * angle.tan()) / (Atom::num(2) * &a__),
                    )
                    / (Atom::num(2) * &a__ * &d__ * &n_ * cos.pow(&n_))), x_)
        },
    ));
}

fn push_rules_rule_3564(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 3564,
        source: "Int[sin[c_.+d_.*x_]^m_*(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_])^n_.,x_Symbol] :=
          Int[(b+a*Cot[c+d*x])^n,x] /;
        FreeQ[{a,b,c,d},x] && EqQ[m+n,0] && IntegerQ[n] && NeQ[a^2+b^2,0]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [c__, d__, m_, a__, b__, n_, x_],
        optional: [a__, b__, c__, d__, n_],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && eqq!(&m_ + &n_, 0)
                && integerq!(n_)
                && neq!(a__.pow(2) + b__.pow(2), 0)
        },
        rhs: {
            let angle = &c__ + &d__ * x_;
            let recursive = rubi_rhs_int(&(&b__ + &a__ * angle.cot()).pow(&n_), x_);

            recursive
        },
    ));
}

fn push_rules_rule_3565(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 3565,
        source: "Int[cos[c_.+d_.*x_]^m_*(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_])^n_.,x_Symbol] :=
          Int[(a+b*Tan[c+d*x])^n,x] /;
        FreeQ[{a,b,c,d},x] && EqQ[m+n,0] && IntegerQ[n] && NeQ[a^2+b^2,0]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [c__, d__, m_, a__, b__, n_, x_],
        optional: [a__, b__, c__, d__, n_],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && eqq!(&m_ + &n_, 0)
                && integerq!(n_)
                && neq!(a__.pow(2) + b__.pow(2), 0)
        },
        rhs: {
            let angle = &c__ + &d__ * x_;
            let recursive = rubi_rhs_int(&(&a__ + &b__ * angle.tan()).pow(&n_), x_);

            recursive
        },
    ));
}

fn push_rules_rule_3566(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 3566,
        source: "Int[sin[c_.+d_.*x_]^m_.*(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
          1/d \\[Star] Subst[Int[x^m*(a+b*x)^n/(1+x^2)^((m+n+2)/2),x],x,Tan[c+d*x]] /;
        FreeQ[{a,b,c,d},x] && IntegerQ[n] && IntegerQ[(m+n)/2] && NeQ[n,-1] && Not[GtQ[n,0] && GtQ[m,1]]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [c__, d__, m_, a__, b__, n_, x_],
        optional: [a__, b__, c__, d__, m_],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && integerq!(n_)
                && integerq!((&m_ + &n_) / 2)
                && neq!(n_, -1)
                && !(gtq!(n_, 0) && gtq!(m_, 1))
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let angle = &c__ + &d__ * x_;
            let primitive = rubi_rhs_int(
                &(sub_atom.pow(&m_) * (&a__ + &b__ * &sub_atom).pow(&n_)
                    / (Atom::num(1) + sub_atom.pow(2)).pow((&m_ + &n_ + 2) / 2)),
                sub,
            );

            rubi_star(Atom::num(1) / &d__, rubi_subst(&primitive, sub, angle.tan()))
        },
    ));
}

fn push_rules_rule_3567(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 3567,
        source: "Int[cos[c_.+d_.*x_]^m_.*(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
          -1/d \\[Star] Subst[Int[x^m*(b+a*x)^n/(1+x^2)^((m+n+2)/2),x],x,Cot[c+d*x]] /;
        FreeQ[{a,b,c,d},x] && IntegerQ[n] && IntegerQ[(m+n)/2] && NeQ[n,-1] && Not[GtQ[n,0] && GtQ[m,1]]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [c__, d__, m_, a__, b__, n_, x_],
        optional: [a__, b__, c__, d__, m_],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && integerq!(n_)
                && integerq!((&m_ + &n_) / 2)
                && neq!(n_, -1)
                && !(gtq!(n_, 0) && gtq!(m_, 1))
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let angle = &c__ + &d__ * x_;
            let primitive = rubi_rhs_int(
                &(sub_atom.pow(&m_) * (&b__ + &a__ * &sub_atom).pow(&n_)
                    / (Atom::num(1) + sub_atom.pow(2)).pow((&m_ + &n_ + 2) / 2)),
                sub,
            );

            rubi_star(-(Atom::num(1) / &d__), rubi_subst(&primitive, sub, angle.cot()))
        },
    ));
}

fn push_rules_rule_3568(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 3568,
        source: "Int[sin[c_.+d_.*x_]^m_.*(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_])^n_.,x_Symbol] :=
          Int[ExpandTrig[sin[c+d*x]^m*(a*cos[c+d*x]+b*sin[c+d*x])^n,x],x] /;
        FreeQ[{a,b,c,d},x] && IntegerQ[m] && IGtQ[n,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [c__, d__, m_, a__, b__, n_, x_],
        optional: [a__, b__, c__, d__, m_, n_],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && integerq!(m_)
                && igtq!(n_, 0)
        },
        rhs: {
            let angle = &c__ + &d__ * x_;
            let payload = i_sin(&angle).pow(&m_) * (&a__ * i_cos(&angle) + &b__ * i_sin(&angle)).pow(&n_);
            let expanded = rubi_expand_trig(&payload, x_);
            let recursive = rubi_rhs_int(&expanded, x_);

            recursive
        },
    ));
}

fn push_rules_rule_3569(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 3569,
        source: "Int[cos[c_.+d_.*x_]^m_.*(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_])^n_.,x_Symbol] :=
          Int[ExpandTrig[cos[c+d*x]^m*(a*cos[c+d*x]+b*sin[c+d*x])^n,x],x] /;
        FreeQ[{a,b,c,d},x] && IntegerQ[m] && IGtQ[n,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [c__, d__, m_, a__, b__, n_, x_],
        optional: [a__, b__, c__, d__, m_, n_],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && integerq!(m_)
                && igtq!(n_, 0)
        },
        rhs: {
            let angle = &c__ + &d__ * x_;
            let payload = i_cos(&angle).pow(&m_) * (&a__ * i_cos(&angle) + &b__ * i_sin(&angle)).pow(&n_);
            let expanded = rubi_expand_trig(&payload, x_);
            let recursive = rubi_rhs_int(&expanded, x_);

            recursive
        },
    ));
}

fn push_rules_rule_3570(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 3570,
        source: "Int[sin[c_.+d_.*x_]^m_.*(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
          a^n*b^n \\[Star] Int[Sin[c+d*x]^m*(b*Cos[c+d*x]+a*Sin[c+d*x])^(-n),x] /;
        FreeQ[{a,b,c,d,m},x] && EqQ[a^2+b^2,0] && ILtQ[n,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [c__, d__, m_, a__, b__, n_, x_],
        optional: [a__, b__, c__, d__, m_],
        when: {
            freeq!([a__, b__, c__, d__, m_], x_)
                && eqq!(a__.pow(2) + b__.pow(2), 0)
                && iltq!(n_, 0)
        },
        rhs: {
            let angle = &c__ + &d__ * x_;
            let recursive = rubi_rhs_int(
                &(angle.sin().pow(&m_) * (&b__ * angle.cos() + &a__ * angle.sin()).pow(-&n_)),
                x_,
            );

            rubi_star(a__.pow(&n_) * b__.pow(&n_), recursive)
        },
    ));
}

fn push_rules_rule_3571(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 3571,
        source: "Int[cos[c_.+d_.*x_]^m_.*(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
          a^n*b^n \\[Star] Int[Cos[c+d*x]^m*(b*Cos[c+d*x]+a*Sin[c+d*x])^(-n),x] /;
        FreeQ[{a,b,c,d,m},x] && EqQ[a^2+b^2,0] && ILtQ[n,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [c__, d__, m_, a__, b__, n_, x_],
        optional: [a__, b__, c__, d__, m_],
        when: {
            freeq!([a__, b__, c__, d__, m_], x_)
                && eqq!(a__.pow(2) + b__.pow(2), 0)
                && iltq!(n_, 0)
        },
        rhs: {
            let angle = &c__ + &d__ * x_;
            let recursive = rubi_rhs_int(
                &(angle.cos().pow(&m_) * (&b__ * angle.cos() + &a__ * angle.sin()).pow(-&n_)),
                x_,
            );

            rubi_star(a__.pow(&n_) * b__.pow(&n_), recursive)
        },
    ));
}

fn push_rules_rule_3574(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 3574,
        source: "Int[sin[c_.+d_.*x_]^m_*(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
          -(a^2+b^2) \\[Star] Int[Sin[c+d*x]^(m+2)*(a*Cos[c+d*x]+b*Sin[c+d*x])^(n-2),x] +
          2*b \\[Star] Int[Sin[c+d*x]^(m+1)*(a*Cos[c+d*x]+b*Sin[c+d*x])^(n-1),x] +
          a^2 \\[Star] Int[Sin[c+d*x]^m*(a*Cos[c+d*x]+b*Sin[c+d*x])^(n-2),x] /;
        FreeQ[{a,b,c,d},x] && NeQ[a^2+b^2,0] && GtQ[n,1] && LtQ[m,-1]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [c__, d__, m_, a__, b__, n_, x_],
        optional: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && neq!(a__.pow(2) + b__.pow(2), 0)
                && gtq!(n_, 1)
                && ltq!(m_, -1)
        },
        rhs: {
            let angle = &c__ + &d__ * x_;
            let sin = angle.sin();
            let linear = &a__ * angle.cos() + &b__ * &sin;
            let recursive1 =
                rubi_rhs_int(&(sin.pow(&m_ + 2) * linear.pow(&n_ - 2)), x_);
            let recursive2 =
                rubi_rhs_int(&(sin.pow(&m_ + 1) * linear.pow(&n_ - 1)), x_);
            let recursive3 = rubi_rhs_int(&(sin.pow(&m_) * linear.pow(&n_ - 2)), x_);

            rubi_star(-(a__.pow(2) + b__.pow(2)), recursive1)
                    + rubi_star(Atom::num(2) * &b__, recursive2)
                    + rubi_star(a__.pow(2), recursive3)
        },
    ));
}

fn push_rules_rule_3575(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 3575,
        source: "Int[cos[c_.+d_.*x_]^m_*(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
          -(a^2+b^2) \\[Star] Int[Cos[c+d*x]^(m+2)*(a*Cos[c+d*x]+b*Sin[c+d*x])^(n-2),x] +
          2*a \\[Star] Int[Cos[c+d*x]^(m+1)*(a*Cos[c+d*x]+b*Sin[c+d*x])^(n-1),x] +
          b^2 \\[Star] Int[Cos[c+d*x]^m*(a*Cos[c+d*x]+b*Sin[c+d*x])^(n-2),x] /;
        FreeQ[{a,b,c,d},x] && NeQ[a^2+b^2,0] && GtQ[n,1] && LtQ[m,-1]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [c__, d__, m_, a__, b__, n_, x_],
        optional: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && neq!(a__.pow(2) + b__.pow(2), 0)
                && gtq!(n_, 1)
                && ltq!(m_, -1)
        },
        rhs: {
            let angle = &c__ + &d__ * x_;
            let cos = angle.cos();
            let linear = &a__ * &cos + &b__ * angle.sin();
            let recursive1 =
                rubi_rhs_int(&(cos.pow(&m_ + 2) * linear.pow(&n_ - 2)), x_);
            let recursive2 =
                rubi_rhs_int(&(cos.pow(&m_ + 1) * linear.pow(&n_ - 1)), x_);
            let recursive3 = rubi_rhs_int(&(cos.pow(&m_) * linear.pow(&n_ - 2)), x_);

            rubi_star(-(a__.pow(2) + b__.pow(2)), recursive1)
                    + rubi_star(Atom::num(2) * &a__, recursive2)
                    + rubi_star(b__.pow(2), recursive3)
        },
    ));
}

fn push_rules_rule_3576(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 3576,
        source: "Int[sin[c_.+d_.*x_]/(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_]),x_Symbol] :=
          b*x/(a^2+b^2) -
          a/(a^2+b^2) \\[Star] Int[(b*Cos[c+d*x]-a*Sin[c+d*x])/(a*Cos[c+d*x]+b*Sin[c+d*x]),x] /;
        FreeQ[{a,b,c,d},x] && NeQ[a^2+b^2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: i_sin(c__ + d__ * x_)
            / (a__ * i_cos(c__ + d__ * x_) + b__ * i_sin(c__ + d__ * x_)),
        with: [c__, d__, a__, b__, x_],
        optional: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && neq!(a__.pow(2) + b__.pow(2), 0)
        },
        rhs: {
            let angle = &c__ + &d__ * x_;
            let sin = angle.sin();
            let cos = angle.cos();
            let linear = &a__ * &cos + &b__ * &sin;
            let den = a__.pow(2) + b__.pow(2);
            let recursive = rubi_rhs_int(&((&b__ * cos - &a__ * sin) / linear), x_);

            rubi_simp(&(&b__ * x_ / &den), x_)
                    - rubi_star(&a__ / &den, recursive)
        },
    ));
}

fn push_rules_rule_3577(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 3577,
        source: "Int[cos[c_.+d_.*x_]/(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_]),x_Symbol] :=
          a*x/(a^2+b^2) +
          b/(a^2+b^2) \\[Star] Int[(b*Cos[c+d*x]-a*Sin[c+d*x])/(a*Cos[c+d*x]+b*Sin[c+d*x]),x] /;
        FreeQ[{a,b,c,d},x] && NeQ[a^2+b^2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: i_cos(c__ + d__ * x_)
            / (a__ * i_cos(c__ + d__ * x_) + b__ * i_sin(c__ + d__ * x_)),
        with: [c__, d__, a__, b__, x_],
        optional: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && neq!(a__.pow(2) + b__.pow(2), 0)
        },
        rhs: {
            let angle = &c__ + &d__ * x_;
            let sin = angle.sin();
            let cos = angle.cos();
            let linear = &a__ * &cos + &b__ * &sin;
            let den = a__.pow(2) + b__.pow(2);
            let recursive = rubi_rhs_int(&((&b__ * cos - &a__ * sin) / linear), x_);

            rubi_simp(&(&a__ * x_ / &den), x_)
                    + rubi_star(&b__ / &den, recursive)
        },
    ));
}

fn push_rules_rule_3578(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, x_);
    rules.push(rubi_rule!(
        order: 3578,
        source: "Int[sin[c_.+d_.*x_]^m_/(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_]),x_Symbol] :=
          -a*Sin[c+d*x]^(m-1)/(d*(a^2+b^2)*(m-1)) +
          b/(a^2+b^2) \\[Star] Int[Sin[c+d*x]^(m-1),x] +
          a^2/(a^2+b^2) \\[Star] Int[Sin[c+d*x]^(m-2)/(a*Cos[c+d*x]+b*Sin[c+d*x]),x] /;
        FreeQ[{a,b,c,d},x] && NeQ[a^2+b^2,0] && GtQ[m,1]",
        desc: "Algebraic expansion and power rule for integration",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [c__, d__, m_, a__, b__, x_],
        optional: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && neq!(a__.pow(2) + b__.pow(2), 0)
                && gtq!(m_, 1)
        },
        rhs: {
            let angle = &c__ + &d__ * x_;
            let sin = angle.sin();
            let linear = &a__ * angle.cos() + &b__ * &sin;
            let den = a__.pow(2) + b__.pow(2);
            let recursive1 = rubi_rhs_int(&sin.pow(&m_ - 1), x_);
            let recursive2 = rubi_rhs_int(&(sin.pow(&m_ - 2) / linear), x_);

            rubi_simp(&(-&a__ * sin.pow(&m_ - 1) / (&d__ * &den * (&m_ - 1))), x_)
                    + rubi_star(&b__ / &den, recursive1)
                    + rubi_star(a__.pow(2) / &den, recursive2)
        },
    ));
}

fn push_rules_rule_3579(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, x_);
    rules.push(rubi_rule!(
        order: 3579,
        source: "Int[cos[c_.+d_.*x_]^m_/(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_]),x_Symbol] :=
          b*Cos[c+d*x]^(m-1)/(d*(a^2+b^2)*(m-1)) +
          a/(a^2+b^2) \\[Star] Int[Cos[c+d*x]^(m-1),x] +
          b^2/(a^2+b^2) \\[Star] Int[Cos[c+d*x]^(m-2)/(a*Cos[c+d*x]+b*Sin[c+d*x]),x] /;
        FreeQ[{a,b,c,d},x] && NeQ[a^2+b^2,0] && GtQ[m,1]",
        desc: "Algebraic expansion and power rule for integration",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [c__, d__, m_, a__, b__, x_],
        optional: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && neq!(a__.pow(2) + b__.pow(2), 0)
                && gtq!(m_, 1)
        },
        rhs: {
            let angle = &c__ + &d__ * x_;
            let cos = angle.cos();
            let linear = &a__ * &cos + &b__ * angle.sin();
            let den = a__.pow(2) + b__.pow(2);
            let recursive1 = rubi_rhs_int(&cos.pow(&m_ - 1), x_);
            let recursive2 = rubi_rhs_int(&(cos.pow(&m_ - 2) / linear), x_);

            rubi_simp(&(&b__ * cos.pow(&m_ - 1) / (&d__ * &den * (&m_ - 1))), x_)
                    + rubi_star(&a__ / &den, recursive1)
                    + rubi_star(b__.pow(2) / &den, recursive2)
        },
    ));
}

fn push_rules_rule_3580(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 3580,
        source: "Int[1/(sin[c_.+d_.*x_]*(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_])),x_Symbol] :=
          1/a \\[Star] Int[Cot[c+d*x],x] -
          1/a \\[Star] Int[(b*Cos[c+d*x]-a*Sin[c+d*x])/(a*Cos[c+d*x]+b*Sin[c+d*x]),x] /;
        FreeQ[{a,b,c,d},x] && NeQ[a^2+b^2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: Atom::num(1)
            / (i_sin(c__ + d__ * x_)
                * (a__ * i_cos(c__ + d__ * x_) + b__ * i_sin(c__ + d__ * x_))),
        with: [c__, d__, a__, b__, x_],
        optional: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && neq!(a__.pow(2) + b__.pow(2), 0)
        },
        rhs: {
            let angle = &c__ + &d__ * x_;
            let sin = angle.sin();
            let cos = angle.cos();
            let linear = &a__ * &cos + &b__ * &sin;
            let recursive1 = rubi_rhs_int(&angle.cot(), x_);
            let recursive2 = rubi_rhs_int(&((&b__ * cos - &a__ * sin) / linear), x_);

            rubi_star(Atom::num(1) / &a__, recursive1)
                    - rubi_star(Atom::num(1) / &a__, recursive2)
        },
    ));
}

fn push_rules_rule_3581(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 3581,
        source: "Int[1/(cos[c_.+d_.*x_]*(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_])),x_Symbol] :=
          1/b \\[Star] Int[Tan[c+d*x],x] +
          1/b \\[Star] Int[(b*Cos[c+d*x]-a*Sin[c+d*x])/(a*Cos[c+d*x]+b*Sin[c+d*x]),x] /;
        FreeQ[{a,b,c,d},x] && NeQ[a^2+b^2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: Atom::num(1)
            / (i_cos(c__ + d__ * x_)
                * (a__ * i_cos(c__ + d__ * x_) + b__ * i_sin(c__ + d__ * x_))),
        with: [c__, d__, a__, b__, x_],
        optional: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && neq!(a__.pow(2) + b__.pow(2), 0)
        },
        rhs: {
            let angle = &c__ + &d__ * x_;
            let sin = angle.sin();
            let cos = angle.cos();
            let linear = &a__ * &cos + &b__ * &sin;
            let recursive1 = rubi_rhs_int(&angle.tan(), x_);
            let recursive2 = rubi_rhs_int(&((&b__ * cos - &a__ * sin) / linear), x_);

            rubi_star(Atom::num(1) / &b__, recursive1)
                    + rubi_star(Atom::num(1) / &b__, recursive2)
        },
    ));
}

fn push_rules_rule_3582(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, x_);
    rules.push(rubi_rule!(
        order: 3582,
        source: "Int[sin[c_.+d_.*x_]^m_/(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_]),x_Symbol] :=
          Sin[c+d*x]^(m+1)/(a*d*(m+1)) -
          b/a^2 \\[Star] Int[Sin[c+d*x]^(m+1),x] +
          (a^2+b^2)/a^2 \\[Star] Int[Sin[c+d*x]^(m+2)/(a*Cos[c+d*x]+b*Sin[c+d*x]),x] /;
        FreeQ[{a,b,c,d},x] && NeQ[a^2+b^2,0] && LtQ[m,-1]",
        desc: "Algebraic expansion and power rule for integration",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [c__, d__, m_, a__, b__, x_],
        optional: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && neq!(a__.pow(2) + b__.pow(2), 0)
                && ltq!(m_, -1)
        },
        rhs: {
            let angle = &c__ + &d__ * x_;
            let sin = angle.sin();
            let linear = &a__ * angle.cos() + &b__ * &sin;
            let den = a__.pow(2) + b__.pow(2);
            let recursive1 = rubi_rhs_int(&sin.pow(&m_ + 1), x_);
            let recursive2 = rubi_rhs_int(&(sin.pow(&m_ + 2) / linear), x_);

            rubi_simp(&(sin.pow(&m_ + 1) / (&a__ * &d__ * (&m_ + 1))), x_)
                    - rubi_star(&b__ / a__.pow(2), recursive1)
                    + rubi_star(den / a__.pow(2), recursive2)
        },
    ));
}

fn push_rules_rule_3583(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, x_);
    rules.push(rubi_rule!(
        order: 3583,
        source: "Int[cos[c_.+d_.*x_]^m_/(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_]),x_Symbol] :=
          -Cos[c+d*x]^(m+1)/(b*d*(m+1)) -
          a/b^2 \\[Star] Int[Cos[c+d*x]^(m+1),x] +
          (a^2+b^2)/b^2 \\[Star] Int[Cos[c+d*x]^(m+2)/(a*Cos[c+d*x]+b*Sin[c+d*x]),x] /;
        FreeQ[{a,b,c,d},x] && NeQ[a^2+b^2,0] && LtQ[m,-1]",
        desc: "Algebraic expansion and power rule for integration",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [c__, d__, m_, a__, b__, x_],
        optional: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && neq!(a__.pow(2) + b__.pow(2), 0)
                && ltq!(m_, -1)
        },
        rhs: {
            let angle = &c__ + &d__ * x_;
            let cos = angle.cos();
            let linear = &a__ * &cos + &b__ * angle.sin();
            let den = a__.pow(2) + b__.pow(2);
            let recursive1 = rubi_rhs_int(&cos.pow(&m_ + 1), x_);
            let recursive2 = rubi_rhs_int(&(cos.pow(&m_ + 2) / linear), x_);

            rubi_simp(&(-cos.pow(&m_ + 1) / (&b__ * &d__ * (&m_ + 1))), x_)
                    - rubi_star(&a__ / b__.pow(2), recursive1)
                    + rubi_star(den / b__.pow(2), recursive2)
        },
    ));
}

fn push_rules_rule_3572(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 3572,
        source: "Int[(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_])^n_/sin[c_.+d_.*x_],x_Symbol] :=
          -(a*Cos[c+d*x]+b*Sin[c+d*x])^(n+1)/(a*d*(n+1)) -
          b/a^2 \\[Star] Int[(a*Cos[c+d*x]+b*Sin[c+d*x])^(n+1),x] +
          1/a^2 \\[Star] Int[(a*Cos[c+d*x]+b*Sin[c+d*x])^(n+2)/Sin[c+d*x],x] /;
        FreeQ[{a,b,c,d},x] && NeQ[a^2+b^2,0] && LtQ[n,-1]",
        desc: "Algebraic expansion and power rule for integration",
        refs: [],
        pattern: (a__ * i_cos(c__ + d__ * x_) + b__ * i_sin(c__ + d__ * x_)).pow(n_)
            / i_sin(c__ + d__ * x_),
        with: [a__, b__, c__, d__, n_, x_],
        optional: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && neq!(a__.pow(2) + b__.pow(2), 0)
                && ltq!(n_, -1)
        },
        rhs: {
            let angle = &c__ + &d__ * x_;
            let sin = angle.sin();
            let linear = &a__ * angle.cos() + &b__ * &sin;
            let recursive1 = rubi_rhs_int(&linear.pow(&n_ + 1), x_);
            let recursive2 = rubi_rhs_int(&(linear.pow(&n_ + 2) / sin), x_);

            rubi_simp(&(-linear.pow(&n_ + 1) / (&a__ * &d__ * (&n_ + 1))), x_)
                    - rubi_star(&b__ / a__.pow(2), recursive1)
                    + rubi_star(Atom::num(1) / a__.pow(2), recursive2)
        },
    ));
}

fn push_rules_rule_3573(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 3573,
        source: "Int[(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_])^n_/cos[c_.+d_.*x_],x_Symbol] :=
          (a*Cos[c+d*x]+b*Sin[c+d*x])^(n+1)/(b*d*(n+1)) -
          a/b^2 \\[Star] Int[(a*Cos[c+d*x]+b*Sin[c+d*x])^(n+1),x] +
          1/b^2 \\[Star] Int[(a*Cos[c+d*x]+b*Sin[c+d*x])^(n+2)/Cos[c+d*x],x] /;
        FreeQ[{a,b,c,d},x] && NeQ[a^2+b^2,0] && LtQ[n,-1]",
        desc: "Algebraic expansion and power rule for integration",
        refs: [],
        pattern: (a__ * i_cos(c__ + d__ * x_) + b__ * i_sin(c__ + d__ * x_)).pow(n_)
            / i_cos(c__ + d__ * x_),
        with: [a__, b__, c__, d__, n_, x_],
        optional: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && neq!(a__.pow(2) + b__.pow(2), 0)
                && ltq!(n_, -1)
        },
        rhs: {
            let angle = &c__ + &d__ * x_;
            let cos = angle.cos();
            let linear = &a__ * &cos + &b__ * angle.sin();
            let recursive1 = rubi_rhs_int(&linear.pow(&n_ + 1), x_);
            let recursive2 = rubi_rhs_int(&(linear.pow(&n_ + 2) / cos), x_);

            rubi_simp(&(linear.pow(&n_ + 1) / (&b__ * &d__ * (&n_ + 1))), x_)
                    - rubi_star(&a__ / b__.pow(2), recursive1)
                    + rubi_star(Atom::num(1) / b__.pow(2), recursive2)
        },
    ));
}

fn push_rules_rule_3584(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 3584,
        source: "Int[sin[c_.+d_.*x_]^m_*(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
          (a^2+b^2)/a^2 \\[Star] Int[Sin[c+d*x]^(m+2)*(a*Cos[c+d*x]+b*Sin[c+d*x])^n,x] -
          2*b/a^2 \\[Star] Int[Sin[c+d*x]^(m+1)*(a*Cos[c+d*x]+b*Sin[c+d*x])^(n+1),x] +
          1/a^2 \\[Star] Int[Sin[c+d*x]^m*(a*Cos[c+d*x]+b*Sin[c+d*x])^(n+2),x] /;
        FreeQ[{a,b,c,d},x] && NeQ[a^2+b^2,0] && LtQ[n,-1] && LtQ[m,-1]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [c__, d__, m_, a__, b__, n_, x_],
        optional: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && neq!(a__.pow(2) + b__.pow(2), 0)
                && ltq!(n_, -1)
                && ltq!(m_, -1)
        },
        rhs: {
            let angle = &c__ + &d__ * x_;
            let sin = angle.sin();
            let linear = &a__ * angle.cos() + &b__ * &sin;
            let den = a__.pow(2) + b__.pow(2);
            let recursive1 = rubi_rhs_int(&(sin.pow(&m_ + 2) * linear.pow(&n_)), x_);
            let recursive2 =
                rubi_rhs_int(&(sin.pow(&m_ + 1) * linear.pow(&n_ + 1)), x_);
            let recursive3 = rubi_rhs_int(&(sin.pow(&m_) * linear.pow(&n_ + 2)), x_);

            rubi_star(den / a__.pow(2), recursive1)
                    - rubi_star(Atom::num(2) * &b__ / a__.pow(2), recursive2)
                    + rubi_star(Atom::num(1) / a__.pow(2), recursive3)
        },
    ));
}

fn push_rules_rule_3585(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 3585,
        source: "Int[cos[c_.+d_.*x_]^m_*(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
          (a^2+b^2)/b^2 \\[Star] Int[Cos[c+d*x]^(m+2)*(a*Cos[c+d*x]+b*Sin[c+d*x])^n,x] -
          2*a/b^2 \\[Star] Int[Cos[c+d*x]^(m+1)*(a*Cos[c+d*x]+b*Sin[c+d*x])^(n+1),x] +
          1/b^2 \\[Star] Int[Cos[c+d*x]^m*(a*Cos[c+d*x]+b*Sin[c+d*x])^(n+2),x] /;
        FreeQ[{a,b,c,d},x] && NeQ[a^2+b^2,0] && LtQ[n,-1] && LtQ[m,-1]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [c__, d__, m_, a__, b__, n_, x_],
        optional: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && neq!(a__.pow(2) + b__.pow(2), 0)
                && ltq!(n_, -1)
                && ltq!(m_, -1)
        },
        rhs: {
            let angle = &c__ + &d__ * x_;
            let cos = angle.cos();
            let linear = &a__ * &cos + &b__ * angle.sin();
            let den = a__.pow(2) + b__.pow(2);
            let recursive1 = rubi_rhs_int(&(cos.pow(&m_ + 2) * linear.pow(&n_)), x_);
            let recursive2 =
                rubi_rhs_int(&(cos.pow(&m_ + 1) * linear.pow(&n_ + 1)), x_);
            let recursive3 = rubi_rhs_int(&(cos.pow(&m_) * linear.pow(&n_ + 2)), x_);

            rubi_star(den / b__.pow(2), recursive1)
                    - rubi_star(Atom::num(2) * &a__ / b__.pow(2), recursive2)
                    + rubi_star(Atom::num(1) / b__.pow(2), recursive3)
        },
    ));
}

fn push_rules_rule_3586(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3586,
        source: "Int[cos[c_.+d_.*x_]^m_.*sin[c_.+d_.*x_]^n_.*(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_])^p_.,x_Symbol] :=
          Int[ExpandTrig[cos[c+d*x]^m*sin[c+d*x]^n*(a*cos[c+d*x]+b*sin[c+d*x])^p,x],x] /;
        FreeQ[{a,b,c,d,m,n},x] && IGtQ[p,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [c__, d__, m_, n_, a__, b__, p_, x_],
        optional: [a__, b__, c__, d__, m_, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, m_, n_], x_) && igtq!(p_, 0)
        },
        rhs: {
            let angle = &c__ + &d__ * x_;
            let payload = i_cos(&angle).pow(&m_)
                * i_sin(&angle).pow(&n_)
                * (&a__ * i_cos(&angle) + &b__ * i_sin(&angle)).pow(&p_);
            let expanded = rubi_expand_trig(&payload, x_);
            let recursive = rubi_rhs_int(&expanded, x_);

            recursive
        },
    ));
}

fn push_rules_rule_3587(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3587,
        source: "Int[cos[c_.+d_.*x_]^m_.*sin[c_.+d_.*x_]^n_.*(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
          a^p*b^p \\[Star] Int[Cos[c+d*x]^m*Sin[c+d*x]^n*(b*Cos[c+d*x]+a*Sin[c+d*x])^(-p),x] /;
        FreeQ[{a,b,c,d,m,n},x] && EqQ[a^2+b^2,0] && ILtQ[p,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [c__, d__, m_, n_, a__, b__, p_, x_],
        optional: [a__, b__, c__, d__, m_, n_],
        when: {
            freeq!([a__, b__, c__, d__, m_, n_], x_)
                && eqq!(a__.pow(2) + b__.pow(2), 0)
                && iltq!(p_, 0)
        },
        rhs: {
            let angle = &c__ + &d__ * x_;
            let recursive = rubi_rhs_int(
                &(angle.cos().pow(&m_)
                    * angle.sin().pow(&n_)
                    * (&b__ * angle.cos() + &a__ * angle.sin()).pow(-&p_)),
                x_,
            );

            rubi_star(a__.pow(&p_) * b__.pow(&p_), recursive)
        },
    ));
}

fn push_rules_rule_3588(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 3588,
        source: "Int[cos[c_.+d_.*x_]^m_.*sin[c_.+d_.*x_]^n_./(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_]),x_Symbol] :=
          b/(a^2+b^2) \\[Star] Int[Cos[c+d*x]^m*Sin[c+d*x]^(n-1),x] +
          a/(a^2+b^2) \\[Star] Int[Cos[c+d*x]^(m-1)*Sin[c+d*x]^n,x] -
          a*b/(a^2+b^2) \\[Star] Int[Cos[c+d*x]^(m-1)*Sin[c+d*x]^(n-1)/(a*Cos[c+d*x]+b*Sin[c+d*x]),x] /;
        FreeQ[{a,b,c,d},x] && NeQ[a^2+b^2,0] && IGtQ[m,0] && IGtQ[n,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [c__, d__, m_, n_, a__, b__, x_],
        optional: [a__, b__, c__, d__, m_, n_],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && neq!(a__.pow(2) + b__.pow(2), 0)
                && igtq!(m_, 0)
                && igtq!(n_, 0)
        },
        rhs: {
            let angle = &c__ + &d__ * x_;
            let cos = i_cos(&angle);
            let sin = i_sin(&angle);
            let linear = &a__ * &cos + &b__ * &sin;
            let den = a__.pow(2) + b__.pow(2);
            let recursive1 = rubi_rhs_int(&(cos.pow(&m_) * sin.pow(&n_ - 1)), x_);
            let recursive2 = rubi_rhs_int(&(cos.pow(&m_ - 1) * sin.pow(&n_)), x_);
            let recursive3 =
                rubi_rhs_int(&(cos.pow(&m_ - 1) * sin.pow(&n_ - 1) / linear), x_);

            rubi_star(&b__ / &den, recursive1)
                    + rubi_star(&a__ / &den, recursive2)
                    - rubi_star(&a__ * &b__ / &den, recursive3)
        },
    ));
}

fn push_rules_rule_3589(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 3589,
        source: "Int[cos[c_.+d_.*x_]^m_.*sin[c_.+d_.*x_]^n_./(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_]),x_Symbol] :=
          Int[ExpandTrig[cos[c+d*x]^m*sin[c+d*x]^n/(a*cos[c+d*x]+b*sin[c+d*x]),x],x] /;
        FreeQ[{a,b,c,d,m,n},x] && IntegersQ[m,n]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [c__, d__, m_, n_, a__, b__, x_],
        optional: [a__, b__, c__, d__, m_, n_],
        when: {
            freeq!([a__, b__, c__, d__, m_, n_], x_) && integersq!([m_, n_])
        },
        rhs: {
            let angle = &c__ + &d__ * x_;
            let payload = i_cos(&angle).pow(&m_) * i_sin(&angle).pow(&n_)
                / (&a__ * i_cos(&angle) + &b__ * i_sin(&angle));
            let expanded = rubi_expand_trig(&payload, x_);
            let recursive = rubi_rhs_int(&expanded, x_);

            recursive
        },
    ));
}

fn push_rules_rule_3590(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3590,
        source: "Int[cos[c_.+d_.*x_]^m_.*sin[c_.+d_.*x_]^n_.*(a_.*cos[c_.+d_.*x_]+b_.*sin[c_.+d_.*x_])^p_,x_Symbol] :=
          b/(a^2+b^2) \\[Star] Int[Cos[c+d*x]^m*Sin[c+d*x]^(n-1)*(a*Cos[c+d*x]+b*Sin[c+d*x])^(p+1),x] +
          a/(a^2+b^2) \\[Star] Int[Cos[c+d*x]^(m-1)*Sin[c+d*x]^n*(a*Cos[c+d*x]+b*Sin[c+d*x])^(p+1),x] -
          a*b/(a^2+b^2) \\[Star] Int[Cos[c+d*x]^(m-1)*Sin[c+d*x]^(n-1)*(a*Cos[c+d*x]+b*Sin[c+d*x])^p,x] /;
        FreeQ[{a,b,c,d},x] && NeQ[a^2+b^2,0] && IGtQ[m,0] && IGtQ[n,0] && ILtQ[p,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [c__, d__, m_, n_, a__, b__, p_, x_],
        optional: [a__, b__, c__, d__, m_, n_],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && neq!(a__.pow(2) + b__.pow(2), 0)
                && igtq!(m_, 0)
                && igtq!(n_, 0)
                && iltq!(p_, 0)
        },
        rhs: {
            let angle = &c__ + &d__ * x_;
            let cos = angle.cos();
            let sin = angle.sin();
            let linear = &a__ * &cos + &b__ * &sin;
            let den = a__.pow(2) + b__.pow(2);
            let recursive1 = rubi_rhs_int(
                &(cos.pow(&m_) * sin.pow(&n_ - 1) * linear.pow(&p_ + 1)),
                x_,
            );
            let recursive2 = rubi_rhs_int(
                &(cos.pow(&m_ - 1) * sin.pow(&n_) * linear.pow(&p_ + 1)),
                x_,
            );
            let recursive3 = rubi_rhs_int(
                &(cos.pow(&m_ - 1) * sin.pow(&n_ - 1) * linear.pow(&p_)),
                x_,
            );

            rubi_star(&b__ / &den, recursive1)
                    + rubi_star(&a__ / &den, recursive2)
                    - rubi_star(&a__ * &b__ / &den, recursive3)
        },
    ));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn downvalues_3550_through_3590_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .filter(|order| (3550..=3590).contains(order))
            .collect::<Vec<_>>();
        assert_eq!(orders, (3550..=3590).collect::<Vec<_>>());
    }
}

// Generated shared pattern builders.

#[inline(never)]
fn rubi_shared_pattern_0(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    (a__ * i_cos(c__ + d__ * x_) + b__ * i_sin(c__ + d__ * x_)).pow(n_)
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    i_cos(c__ + d__ * x_).pow(m_)
        * (a__ * i_cos(c__ + d__ * x_) + b__ * i_sin(c__ + d__ * x_)).pow(n_)
}

#[inline(never)]
fn rubi_shared_pattern_2(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    i_cos(c__ + d__ * x_).pow(m_)
        * i_sin(c__ + d__ * x_).pow(n_)
        * (a__ * i_cos(c__ + d__ * x_) + b__ * i_sin(c__ + d__ * x_)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_3(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    i_cos(c__ + d__ * x_).pow(m_) * i_sin(c__ + d__ * x_).pow(n_)
        / (a__ * i_cos(c__ + d__ * x_) + b__ * i_sin(c__ + d__ * x_))
}

#[inline(never)]
fn rubi_shared_pattern_4(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let m_ = symbols.m_;
    let x_ = symbols.x_;
    i_cos(c__ + d__ * x_).pow(m_) / (a__ * i_cos(c__ + d__ * x_) + b__ * i_sin(c__ + d__ * x_))
}

#[inline(never)]
fn rubi_shared_pattern_5(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    i_sin(c__ + d__ * x_).pow(m_)
        * (a__ * i_cos(c__ + d__ * x_) + b__ * i_sin(c__ + d__ * x_)).pow(n_)
}

#[inline(never)]
fn rubi_shared_pattern_6(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let m_ = symbols.m_;
    let x_ = symbols.x_;
    i_sin(c__ + d__ * x_).pow(m_) / (a__ * i_cos(c__ + d__ * x_) + b__ * i_sin(c__ + d__ * x_))
}
