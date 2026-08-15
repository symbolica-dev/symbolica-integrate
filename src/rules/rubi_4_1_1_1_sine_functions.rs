use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_3113(rules);
    push_rules_rule_3114(rules);
    push_rules_rule_3115(rules);
    push_rules_rule_3116(rules);
    push_rules_rule_3117(rules);
    push_rules_rule_3118(rules);
    push_rules_rule_3119(rules);
    push_rules_rule_3120(rules);
    push_rules_rule_3121(rules);
    push_rules_rule_3122(rules);
    push_rules_rule_3123(rules);
    push_rules_rule_3124(rules);
    push_rules_rule_3125(rules);
    push_rules_rule_3126(rules);
    push_rules_rule_3127(rules);
    push_rules_rule_3128(rules);
    push_rules_rule_3129(rules);
    push_rules_rule_3130(rules);
    push_rules_rule_3131(rules);
    push_rules_rule_3132(rules);
    push_rules_rule_3133(rules);
    push_rules_rule_3134(rules);
    push_rules_rule_3135(rules);
    push_rules_rule_3136(rules);
    push_rules_rule_3137(rules);
    push_rules_rule_3138(rules);
    push_rules_rule_3139(rules);
    push_rules_rule_3140(rules);
    push_rules_rule_3141(rules);
    push_rules_rule_3142(rules);
    push_rules_rule_3143(rules);
    push_rules_rule_3144(rules);
    push_rules_rule_3145(rules);
}

fn push_rules_rule_3113(rules: &mut Vec<RubiRule>) {
    rubi_symb!(c__, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 3113,
        source: "Int[sin[c_.+d_.*x_]^n_,x_Symbol] :=
          -1/d \\[Star] Subst[Int[Expand[(1-x^2)^((n-1)/2),x],x],x,Cos[c+d*x]] /;
        FreeQ[{c,d},x] && IGtQ[(n-1)/2,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: i_sin(c__ + d__ * x_).pow(n_),
        with: [c__, d__, n_, x_],
        optional: [c__, d__],
        when: {
            freeq!([c__, d__], x_) && igtq!((&n_ - 1) / 2, 0)
        },
        rhs: {
            let subst_guard = fresh_substitution_symbol().unwrap();
            let subst = subst_guard.symbol();
            let z = Atom::var(subst);
            let transformed = (Atom::num(1) - z.pow(2)).pow((&n_ - 1) / 2).expand();
            let primitive = rubi_rhs_int(&transformed, subst);
            let angle = &c__ + &d__ * x_;
            let substituted = rubi_subst(&primitive, subst, angle.cos());

            rubi_star(-(Atom::num(1) / &d__), substituted)
        },
    ));
}

fn push_rules_rule_3114(rules: &mut Vec<RubiRule>) {
    rubi_symb!(c__, d__, x_);
    rules.push(rubi_rule!(
        order: 3114,
        source: "Int[sin[c_.+d_.*x_/2]^2,x_Symbol] :=
          x/2 - Sin[2*c+d*x]/(2*d) /;
        FreeQ[{c,d},x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: i_sin(c__ + d__ * x_ / 2).pow(2),
        with: [c__, d__, x_],
        optional: [c__, d__],
        when: { freeq!([c__, d__], x_) },
        rhs: {
            rubi_simp(&(x_ / 2), x_)
                    - rubi_simp(
                        &((Atom::num(2) * &c__ + &d__ * x_).sin() / (2 * &d__)),
                        x_,
                    )
        },
    ));
}

fn push_rules_rule_3115(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; b__, c__, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 3115,
        source: "Int[(b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
          -b*Cos[c+d*x]*(b*Sin[c+d*x])^(n-1)/(d*n) + b^2*(n-1)/n \\[Star] Int[(b*Sin[c+d*x])^(n-2),x] /;
        FreeQ[{b,c,d},x] && GtQ[n,1] && IntegerQ[2*n]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [b__, c__, d__, n_, x_],
        optional: [b__, c__, d__],
        when: {
            freeq!([b__, c__, d__], x_)
                && gtq!(n_, 1)
                && integerq!(Atom::num(2) * &n_)
        },
        rhs: {
            let angle = &c__ + &d__ * x_;
            let scaled_sin = &b__ * angle.sin();
            let recursive_integrand = scaled_sin.pow(&n_ - 2);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(
                    &(-&b__ * angle.cos() * scaled_sin.pow(&n_ - 1) / (&d__ * &n_)),
                    x_,
                ) + rubi_simp(&(b__.pow(2) * (&n_ - 1) / &n_ * recursive), x_)
        },
    ));
}

fn push_rules_rule_3116(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; b__, c__, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 3116,
        source: "Int[(b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
          Cos[c+d*x]*(b*Sin[c+d*x])^(n+1)/(b*d*(n+1)) +
          (n+2)/(b^2*(n+1)) \\[Star] Int[(b*Sin[c+d*x])^(n+2),x] /;
        FreeQ[{b,c,d},x] && LtQ[n,-1] && IntegerQ[2*n]",
        desc: "Sine recurrence 2a with A\\[Rule]1,B\\[Rule]0,C\\[Rule]0,a\\[Rule]0,m\\[Rule]0",
        refs: ["G&R 2.510.3 with q\\[Rule]0, CRC 309", "G&R 2.510.6 with p\\[Rule]0, CRC 313", "G&R 2.552.3"],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [b__, c__, d__, n_, x_],
        optional: [b__, c__, d__],
        when: {
            freeq!([b__, c__, d__], x_)
                && ltq!(n_, -1)
                && integerq!(Atom::num(2) * &n_)
        },
        rhs: {
            let angle = &c__ + &d__ * x_;
            let scaled_sin = &b__ * angle.sin();
            let recursive_integrand = scaled_sin.pow(&n_ + 2);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(
                    &(angle.cos() * scaled_sin.pow(&n_ + 1)
                        / (&b__ * &d__ * (&n_ + 1))),
                    x_,
                ) + rubi_star((&n_ + 2) / (b__.pow(2) * (&n_ + 1)), recursive)
        },
    ));
}

fn push_rules_rule_3117(rules: &mut Vec<RubiRule>) {
    rubi_symb!(c__, d__, x_);
    rules.push(rubi_rule!(
        order: 3117,
        source: "Int[sin[c_.+Pi/2+d_.*x_],x_Symbol] :=
          Sin[c+d*x]/d /;
        FreeQ[{c,d},x]",
        desc: "Primitive rule",
        refs: ["G&R 2.01.5, CRC 290, A&S 4.3.113", "G&R 2.01.6, CRC 291, A&S 4.3.114"],
        pattern: i_sin(c__ + Atom::var(Symbol::PI) / 2 + d__ * x_),
        with: [c__, d__, x_],
        optional: [c__, d__],
        when: { freeq!([c__, d__], x_) },
        rhs: {
            rubi_simp(&((&c__ + &d__ * x_).sin() / &d__), x_)
        },
    ));
}

fn push_rules_rule_3118(rules: &mut Vec<RubiRule>) {
    rubi_symb!(c__, d__, x_);
    rules.push(rubi_rule!(
        order: 3118,
        source: "Int[sin[c_.+d_.*x_],x_Symbol] :=
          -Cos[c+d*x]/d /;
        FreeQ[{c,d},x]",
        desc: "Primitive rule",
        refs: ["G&R 2.01.5, CRC 290, A&S 4.3.113", "G&R 2.01.6, CRC 291, A&S 4.3.114"],
        pattern: i_sin(c__ + d__ * x_),
        with: [c__, d__, x_],
        optional: [c__, d__],
        when: { freeq!([c__, d__], x_) },
        rhs: {
            rubi_simp(&(-(&c__ + &d__ * x_).cos() / &d__), x_)
        },
    ));
}

fn push_rules_rule_3119(rules: &mut Vec<RubiRule>) {
    rubi_symb!(c__, d__, x_);
    rules.push(rubi_rule!(
        order: 3119,
        source: "Int[Sqrt[sin[c_.+d_.*x_]],x_Symbol] :=
          2/d*EllipticE[1/2*(c-Pi/2+d*x),2] /;
        FreeQ[{c,d},x]",
        desc: "Primitive rule",
        refs: [],
        pattern: i_sin(c__ + d__ * x_).sqrt(),
        with: [c__, d__, x_],
        optional: [c__, d__],
        when: { freeq!([c__, d__], x_) },
        rhs: {
            rubi_simp(
                &(Atom::num(2)
                    * rubi_elliptic_e(
                        (&c__ - Atom::var(Symbol::PI) / 2 + &d__ * x_) / 2,
                        Atom::num(2),
                    )
                    / &d__),
                x_,
            )
        },
    ));
}

fn push_rules_rule_3120(rules: &mut Vec<RubiRule>) {
    rubi_symb!(c__, d__, x_);
    rules.push(rubi_rule!(
        order: 3120,
        source: "Int[1/Sqrt[sin[c_.+d_.*x_]],x_Symbol] :=
          2/d*EllipticF[1/2*(c-Pi/2+d*x),2] /;
        FreeQ[{c,d},x]",
        desc: "Primitive rule",
        refs: [],
        pattern: Atom::num(1) / i_sin(c__ + d__ * x_).sqrt(),
        with: [c__, d__, x_],
        optional: [c__, d__],
        when: { freeq!([c__, d__], x_) },
        rhs: {
            rubi_simp(
                &(Atom::num(2)
                    * rubi_elliptic_f(
                        (&c__ - Atom::var(Symbol::PI) / 2 + &d__ * x_) / 2,
                        Atom::num(2),
                    )
                    / &d__),
                x_,
            )
        },
    ));
}

fn push_rules_rule_3121(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; b__, c__, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 3121,
        source: "Int[(b_*sin[c_.+d_.*x_])^n_,x_Symbol] :=
          (b*Sin[c+d*x])^n/Sin[c+d*x]^n \\[Star] Int[Sin[c+d*x]^n,x] /;
        FreeQ[{b,c,d},x] && LtQ[-1,n,1] && IntegerQ[2*n]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [b__, c__, d__, n_, x_],
        optional: [c__, d__],
        when: {
            freeq!([b__, c__, d__], x_)
                && ltq!(-1, n_, 1)
                && integerq!(Atom::num(2) * &n_)
        },
        rhs: {
            let angle = &c__ + &d__ * x_;
            let sin = angle.sin();
            let scaled_sin = &b__ * &sin;
            let recursive_integrand = sin.pow(&n_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(scaled_sin.pow(&n_) / sin.pow(&n_), recursive)
        },
    ));
}

fn push_rules_rule_3122(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; b__, c__, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 3122,
        source: "Int[(b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
          Cos[c+d*x]*(b*Sin[c+d*x])^(n+1)/(b*d*(n+1)*Sqrt[Cos[c+d*x]^2])*Hypergeometric2F1[1/2,(n+1)/2,(n+3)/2,Sin[c+d*x]^2] /;
        FreeQ[{b,c,d,n},x] && Not[IntegerQ[2*n]]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [b__, c__, d__, n_, x_],
        optional: [b__, c__, d__],
        when: {
            freeq!([b__, c__, d__, n_], x_)
                && !integerq!(Atom::num(2) * &n_)
        },
        rhs: {
            let angle = &c__ + &d__ * x_;
            let sin = angle.sin();
            let cos = angle.cos();
            let scaled_sin = &b__ * &sin;

            rubi_simp(
                &(&cos
                    * scaled_sin.pow(&n_ + 1)
                    * rubi_hypergeometric2f1(
                        Atom::num(1) / Atom::num(2),
                        (&n_ + 1) / 2,
                        (&n_ + 3) / 2,
                        sin.pow(2),
                    )
                    / (&b__ * &d__ * (&n_ + 1) * cos.pow(2).sqrt())),
                x_,
            )
        },
    ));
}

fn push_rules_rule_3123(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 3123,
        source: "Int[(a_+b_.*sin[c_.+d_.*x_])^2,x_Symbol] :=
          (2*a^2+b^2)*x/2 - 2*a*b*Cos[c+d*x]/d - b^2*Cos[c+d*x]*Sin[c+d*x]/(2*d) /;
        FreeQ[{a,b,c,d},x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (a__ + b__ * i_sin(c__ + d__ * x_)).pow(2),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, c__, d__],
        when: { freeq!([a__, b__, c__, d__], x_) },
        rhs: {
            let angle = &c__ + &d__ * x_;
            let sin = angle.sin();
            let cos = angle.cos();

            rubi_simp(
                    &((Atom::num(2) * a__.pow(2) + b__.pow(2)) * x_ / 2),
                    x_,
                ) - rubi_simp(&(Atom::num(2) * &a__ * &b__ * &cos / &d__), x_)
                    - rubi_simp(
                        &(b__.pow(2) * cos * sin / (Atom::num(2) * &d__)),
                        x_,
                    )
        },
    ));
}

fn push_rules_rule_3124(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 3124,
        source: "Int[(a_+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
          Int[ExpandTrig[(a+b*sin[c+d*x])^n,x],x] /;
        FreeQ[{a,b,c,d,n},x] && EqQ[a^2-b^2,0] && IGtQ[n,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, n_, x_],
        optional: [b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, n_], x_)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && igtq!(n_, 0)
        },
        rhs: {
            let angle = &c__ + &d__ * x_;
            let payload = (&a__ + &b__ * i_sin(&angle)).pow(&n_);
            let expanded = rubi_expand_trig(&payload, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_3125(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 3125,
        source: "Int[Sqrt[a_+b_.*sin[c_.+d_.*x_]],x_Symbol] :=
          -2*b*Cos[c+d*x]/(d*Sqrt[a+b*Sin[c+d*x]]) /;
        FreeQ[{a,b,c,d},x] && EqQ[a^2-b^2,0]",
        desc: "Singly degenerate sine recurrence 1b with A\\[Rule]c,B\\[Rule]d,m\\[Rule]12,n\\[Rule]-1,p\\[Rule]0",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
        },
        rhs: {
            let angle = &c__ + &d__ * x_;
            let base = &a__ + &b__ * angle.sin();

            rubi_simp(
                &(-Atom::num(2) * &b__ * angle.cos() / (&d__ * base.sqrt())),
                x_,
            )
        },
    ));
}

fn push_rules_rule_3126(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 3126,
        source: "Int[(a_+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
          -b*Cos[c+d*x]*(a+b*Sin[c+d*x])^(n-1)/(d*n) +
          a*(2*n-1)/n \\[Star] Int[(a+b*Sin[c+d*x])^(n-1),x] /;
        FreeQ[{a,b,c,d},x] && EqQ[a^2-b^2,0] && IGtQ[n-1/2,0]",
        desc: "Singly degenerate sine recurrence 1b with A\\[Rule]c,B\\[Rule]d,n\\[Rule]-1,p\\[Rule]0",
        refs: ["G&R 2.555.? inverted"],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, n_, x_],
        optional: [b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && igtq!(&n_ - Atom::num(1) / Atom::num(2), 0)
        },
        rhs: {
            let angle = &c__ + &d__ * x_;
            let base = &a__ + &b__ * i_sin(&angle);
            let recursive_integrand = base.pow(&n_ - 1);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(
                    &(-&b__ * angle.cos() * base.pow(&n_ - 1) / (&d__ * &n_)),
                    x_,
                ) + rubi_star(&a__ * (Atom::num(2) * &n_ - 1) / &n_, recursive)
        },
    ));
}

fn push_rules_rule_3127(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 3127,
        source: "Int[1/(a_+b_.*sin[c_.+d_.*x_]),x_Symbol] :=
          -Cos[c+d*x]/(d*(b+a*Sin[c+d*x])) /;
        FreeQ[{a,b,c,d},x] && EqQ[a^2-b^2,0]",
        desc: "Singly degenerate sine recurrence 2a with A\\[Rule]1,B\\[Rule]0,m\\[Rule]-1,n\\[Rule]0,p\\[Rule]0",
        refs: ["G&R 2.555.3', CRC 337', A&S 4.3.134'/5'"],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
        },
        rhs: {
            let angle = &c__ + &d__ * x_;

            rubi_simp(
                &(-angle.cos() / (&d__ * (&b__ + &a__ * angle.sin()))),
                x_,
            )
        },
    ));
}

fn push_rules_rule_3128(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 3128,
        source: "Int[1/Sqrt[a_+b_.*sin[c_.+d_.*x_]],x_Symbol] :=
          -2/d \\[Star] Subst[Int[1/(2*a-x^2),x],x,b*Cos[c+d*x]/Sqrt[a+b*Sin[c+d*x]]] /;
        FreeQ[{a,b,c,d},x] && EqQ[a^2-b^2,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
        },
        rhs: {
            let subst_guard = fresh_substitution_symbol().unwrap();
            let subst = subst_guard.symbol();
            let z = Atom::var(subst);
            let transformed = Atom::num(1) / (Atom::num(2) * &a__ - z.pow(2));
            let primitive = rubi_rhs_int(&transformed, subst);
            let angle = &c__ + &d__ * x_;
            let replacement = &b__ * angle.cos() / (&a__ + &b__ * angle.sin()).sqrt();
            let substituted = rubi_subst(&primitive, subst, replacement);

            rubi_star(-Atom::num(2) / &d__, substituted)
        },
    ));
}

fn push_rules_rule_3129(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 3129,
        source: "Int[(a_+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
          b*Cos[c+d*x]*(a+b*Sin[c+d*x])^n/(a*d*(2*n+1)) +
          (n+1)/(a*(2*n+1)) \\[Star] Int[(a+b*Sin[c+d*x])^(n+1),x] /;
        FreeQ[{a,b,c,d},x] && EqQ[a^2-b^2,0] && LtQ[n,-1] && IntegerQ[2*n]",
        desc: "Singly degenerate sine recurrence 2a with A\\[Rule]1,B\\[Rule]0,n\\[Rule]0,p\\[Rule]0",
        refs: ["G&R 2.555.?"],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, n_, x_],
        optional: [b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && ltq!(n_, -1)
                && integerq!(Atom::num(2) * &n_)
        },
        rhs: {
            let angle = &c__ + &d__ * x_;
            let base = &a__ + &b__ * i_sin(&angle);
            let recursive_integrand = base.pow(&n_ + 1);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(
                    &(&b__ * angle.cos() * base.pow(&n_)
                        / (&a__ * &d__ * (Atom::num(2) * &n_ + 1))),
                    x_,
                ) + rubi_star((&n_ + 1) / (&a__ * (Atom::num(2) * &n_ + 1)), recursive)
        },
    ));
}

fn push_rules_rule_3130(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 3130,
        source: "Int[(a_+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
          -2^(n+1/2)*a^(n-1/2)*b*Cos[c+d*x]/(d*Sqrt[a+b*Sin[c+d*x]])*Hypergeometric2F1[1/2,1/2-n,3/2,1/2*(1-b*Sin[c+d*x]/a)] /;
        FreeQ[{a,b,c,d,n},x] && EqQ[a^2-b^2,0] && Not[IntegerQ[2*n]] && GtQ[a,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, n_, x_],
        optional: [b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, n_], x_)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && !integerq!(Atom::num(2) * &n_)
                && gtq!(a__, 0)
        },
        rhs: {
            let angle = &c__ + &d__ * x_;
            let sin = i_sin(&angle);
            let base = &a__ + &b__ * &sin;

            rubi_simp(
                &(-Atom::num(2).pow(&n_ + Atom::num(1) / Atom::num(2))
                    * a__.pow(&n_ - Atom::num(1) / Atom::num(2))
                    * &b__
                    * angle.cos()
                    * rubi_hypergeometric2f1(
                        Atom::num(1) / Atom::num(2),
                        Atom::num(1) / Atom::num(2) - &n_,
                        Atom::num(3) / Atom::num(2),
                        Atom::num(1) / Atom::num(2) * (Atom::num(1) - &b__ * sin / &a__),
                    )
                    / (&d__ * base.sqrt())),
                x_,
            )
        },
    ));
}

fn push_rules_rule_3131(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 3131,
        source: "Int[(a_+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
          a^IntPart[n]*(a+b*Sin[c+d*x])^FracPart[n]/(1+b/a*Sin[c+d*x])^FracPart[n] \\[Star] Int[(1+b/a*Sin[c+d*x])^n,x] /;
        FreeQ[{a,b,c,d,n},x] && EqQ[a^2-b^2,0] && Not[IntegerQ[2*n]] && Not[GtQ[a,0]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, n_, x_],
        optional: [b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, n_], x_)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && !integerq!(Atom::num(2) * &n_)
                && !gtq!(a__, 0)
        },
        rhs: {
            let angle = &c__ + &d__ * x_;
            let sin = i_sin(&angle);
            let base = &a__ + &b__ * &sin;
            let normalized_base = Atom::num(1) + &b__ / &a__ * sin;
            let frac_n = rubi_frac_part(&n_);
            let recursive_integrand = normalized_base.pow(&n_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(a__.pow(rubi_int_part(&n_)) * base.pow(&frac_n) / normalized_base.pow(frac_n), recursive)
        },
    ));
}

fn push_rules_rule_3132(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 3132,
        source: "Int[Sqrt[a_+b_.*sin[c_.+d_.*x_]],x_Symbol] :=
          2*Sqrt[a+b]/d*EllipticE[1/2*(c-Pi/2+d*x),2*b/(a+b)] /;
        FreeQ[{a,b,c,d},x] && NeQ[a^2-b^2,0] && GtQ[a+b,0]",
        desc: "Primitive rule",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && gtq!(&a__ + &b__, 0)
        },
        rhs: {
            rubi_simp(
                &(Atom::num(2)
                    * (&a__ + &b__).sqrt()
                    * rubi_elliptic_e(
                        (&c__ - Atom::var(Symbol::PI) / 2 + &d__ * x_) / 2,
                        Atom::num(2) * &b__ / (&a__ + &b__),
                    )
                    / &d__),
                x_,
            )
        },
    ));
}

fn push_rules_rule_3133(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 3133,
        source: "Int[Sqrt[a_+b_.*sin[c_.+d_.*x_]],x_Symbol] :=
          2*Sqrt[a-b]/d*EllipticE[1/2*(c+Pi/2+d*x),-2*b/(a-b)] /;
        FreeQ[{a,b,c,d},x] && NeQ[a^2-b^2,0] && GtQ[a-b,0]",
        desc: "Primitive rule",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && gtq!(&a__ - &b__, 0)
        },
        rhs: {
            rubi_simp(
                &(Atom::num(2)
                    * (&a__ - &b__).sqrt()
                    * rubi_elliptic_e(
                        (&c__ + Atom::var(Symbol::PI) / 2 + &d__ * x_) / 2,
                        -Atom::num(2) * &b__ / (&a__ - &b__),
                    )
                    / &d__),
                x_,
            )
        },
    ));
}

fn push_rules_rule_3134(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 3134,
        source: "Int[Sqrt[a_+b_.*sin[c_.+d_.*x_]],x_Symbol] :=
          Sqrt[a+b*Sin[c+d*x]]/Sqrt[(a+b*Sin[c+d*x])/(a+b)] \\[Star] Int[Sqrt[a/(a+b)+b/(a+b)*Sin[c+d*x]],x] /;
        FreeQ[{a,b,c,d},x] && NeQ[a^2-b^2,0] && Not[GtQ[a+b,0]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && !gtq!(&a__ + &b__, 0)
        },
        rhs: {
            let angle = &c__ + &d__ * x_;
            let base = &a__ + &b__ * angle.sin();
            let normalized_base = &a__ / (&a__ + &b__) + &b__ / (&a__ + &b__) * angle.sin();
            let recursive = rubi_rhs_int(&normalized_base.sqrt(), x_);

            rubi_star(base.sqrt() / (base / (&a__ + &b__)).sqrt(), recursive)
        },
    ));
}

fn push_rules_rule_3135(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 3135,
        source: "Int[(a_+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
          -b*Cos[c+d*x]*(a+b*Sin[c+d*x])^(n-1)/(d*n) +
          1/n \\[Star] Int[(a+b*Sin[c+d*x])^(n-2)*Simp[a^2*n+b^2*(n-1)+a*b*(2*n-1)*Sin[c+d*x],x],x] /;
        FreeQ[{a,b,c,d},x] && NeQ[a^2-b^2,0] && GtQ[n,1] && IntegerQ[2*n]",
        desc: "Nondegenerate sine recurrence 1b with A\\[Rule]a c,B\\[Rule]b c+a d,C\\[Rule]b d,m\\[Rule]-1+m,n\\[Rule]-1,p\\[Rule]0",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, n_, x_],
        optional: [b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && gtq!(n_, 1)
                && integerq!(Atom::num(2) * &n_)
        },
        rhs: {
            let angle = &c__ + &d__ * x_;
            let sin = i_sin(&angle);
            let base = &a__ + &b__ * &sin;
            let simp = rubi_simp(
                &(a__.pow(2) * &n_
                    + b__.pow(2) * (&n_ - 1)
                    + &a__ * &b__ * (Atom::num(2) * &n_ - 1) * sin),
                x_,
            );
            let recursive_integrand = base.pow(&n_ - 2) * simp;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(
                    &(-&b__ * angle.cos() * base.pow(&n_ - 1) / (&d__ * &n_)),
                    x_,
                ) + rubi_star(Atom::num(1) / &n_, recursive)
        },
    ));
}

fn push_rules_rule_3136(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 3136,
        source: "Int[1/(a_+b_.*sin[c_.+d_.*x_]),x_Symbol] :=
          With[{q=Rt[a^2-b^2,2]},
          x/q + 2/(d*q)*ArcTan[b*Cos[c+d*x]/(a+q+b*Sin[c+d*x])]] /;
        FreeQ[{a,b,c,d},x] && GtQ[a^2-b^2,0] && PosQ[a]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && gtq!(a__.pow(2) - b__.pow(2), 0)
                && posq!(a__)
        },
        rhs: {
            let angle = &c__ + &d__ * x_;
            let q = rubi_rt(&(a__.pow(2) - b__.pow(2)), 2);

            rubi_simp(&(x_ / &q), x_)
                    + rubi_simp(
                        &(Atom::num(2) / (&d__ * &q)
                            * (&b__ * angle.cos() / (&a__ + &q + &b__ * angle.sin()))
                                .atan()),
                        x_,
                    )
        },
    ));
}

fn push_rules_rule_3137(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 3137,
        source: "Int[1/(a_+b_.*sin[c_.+d_.*x_]),x_Symbol] :=
          With[{q=Rt[a^2-b^2,2]},
          -x/q - 2/(d*q)*ArcTan[b*Cos[c+d*x]/(a-q+b*Sin[c+d*x])]] /;
        FreeQ[{a,b,c,d},x] && GtQ[a^2-b^2,0] && NegQ[a]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && gtq!(a__.pow(2) - b__.pow(2), 0)
                && negq!(a__)
        },
        rhs: {
            let angle = &c__ + &d__ * x_;
            let q = rubi_rt(&(a__.pow(2) - b__.pow(2)), 2);

            rubi_simp(&(Atom::num(-1) * x_ / &q), x_)
                    - rubi_simp(
                        &(Atom::num(2) / (&d__ * &q)
                            * (&b__ * angle.cos() / (&a__ - &q + &b__ * angle.sin()))
                                .atan()),
                        x_,
                    )
        },
    ));
}

fn push_rules_rule_3138(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 3138,
        source: "Int[1/(a_+b_.*sin[c_.+Pi/2+d_.*x_]),x_Symbol] :=
          With[{e=FreeFactors[Tan[(c+d*x)/2],x]},
          2*e/d \\[Star] Subst[Int[1/(a+b+(a-b)*e^2*x^2),x],x,Tan[(c+d*x)/2]/e]] /;
        FreeQ[{a,b,c,d},x] && NeQ[a^2-b^2,0]",
        desc: "Integration by substitution",
        refs: ["G&R 2.551.3, CRC 340, A&S 4.3.131", "G&R 2.553.3, CRC 341, A&S 4.3.133"],
        pattern: Atom::num(1) / (a__ + b__ * i_sin(c__ + Atom::var(Symbol::PI) / 2 + d__ * x_)),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && neq!(a__.pow(2) - b__.pow(2), 0)
        },
        rhs: {
            let subst_guard = fresh_substitution_symbol().unwrap();
            let subst = subst_guard.symbol();
            let z = Atom::var(subst);
            let tan_half = ((&c__ + &d__ * x_) / 2).tan();
            let e = rubi_free_factors(&tan_half, x_);
            let transformed =
                Atom::num(1) / (&a__ + &b__ + (&a__ - &b__) * e.pow(2) * z.pow(2));
            let primitive = rubi_rhs_int(&transformed, subst);
            let substituted = rubi_subst(&primitive, subst, tan_half / &e);

            rubi_star(Atom::num(2) * &e / &d__, substituted)
        },
    ));
}

fn push_rules_rule_3139(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 3139,
        source: "Int[1/(a_+b_.*sin[c_.+d_.*x_]),x_Symbol] :=
          With[{e=FreeFactors[Tan[(c+d*x)/2],x]},
          2*e/d \\[Star] Subst[Int[1/(a+2*b*e*x+a*e^2*x^2),x],x,Tan[(c+d*x)/2]/e]] /;
        FreeQ[{a,b,c,d},x] && NeQ[a^2-b^2,0]",
        desc: "Integration by substitution",
        refs: ["G&R 2.551.3, CRC 340, A&S 4.3.131", "G&R 2.553.3, CRC 341, A&S 4.3.133"],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && neq!(a__.pow(2) - b__.pow(2), 0)
        },
        rhs: {
            let subst_guard = fresh_substitution_symbol().unwrap();
            let subst = subst_guard.symbol();
            let z = Atom::var(subst);
            let tan_half = ((&c__ + &d__ * x_) / 2).tan();
            let e = rubi_free_factors(&tan_half, x_);
            let transformed = Atom::num(1)
                / (&a__ + Atom::num(2) * &b__ * &e * &z + &a__ * e.pow(2) * z.pow(2));
            let primitive = rubi_rhs_int(&transformed, subst);
            let substituted = rubi_subst(&primitive, subst, tan_half / &e);

            rubi_star(Atom::num(2) * &e / &d__, substituted)
        },
    ));
}

fn push_rules_rule_3140(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 3140,
        source: "Int[1/Sqrt[a_+b_.*sin[c_.+d_.*x_]],x_Symbol] :=
          2/(d*Sqrt[a+b])*EllipticF[1/2*(c-Pi/2+d*x),2*b/(a+b)] /;
        FreeQ[{a,b,c,d},x] && NeQ[a^2-b^2,0] && GtQ[a+b,0]",
        desc: "Primitive rule",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && gtq!(&a__ + &b__, 0)
        },
        rhs: {
            rubi_simp(
                &(Atom::num(2)
                    * rubi_elliptic_f(
                        (&c__ - Atom::var(Symbol::PI) / 2 + &d__ * x_) / 2,
                        Atom::num(2) * &b__ / (&a__ + &b__),
                    )
                    / (&d__ * (&a__ + &b__).sqrt())),
                x_,
            )
        },
    ));
}

fn push_rules_rule_3141(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 3141,
        source: "Int[1/Sqrt[a_+b_.*sin[c_.+d_.*x_]],x_Symbol] :=
          2/(d*Sqrt[a-b])*EllipticF[1/2*(c+Pi/2+d*x),-2*b/(a-b)] /;
        FreeQ[{a,b,c,d},x] && NeQ[a^2-b^2,0] && GtQ[a-b,0]",
        desc: "Primitive rule",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && gtq!(&a__ - &b__, 0)
        },
        rhs: {
            rubi_simp(
                &(Atom::num(2)
                    * rubi_elliptic_f(
                        (&c__ + Atom::var(Symbol::PI) / 2 + &d__ * x_) / 2,
                        -Atom::num(2) * &b__ / (&a__ - &b__),
                    )
                    / (&d__ * (&a__ - &b__).sqrt())),
                x_,
            )
        },
    ));
}

fn push_rules_rule_3142(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 3142,
        source: "Int[1/Sqrt[a_+b_.*sin[c_.+d_.*x_]],x_Symbol] :=
          Sqrt[(a+b*Sin[c+d*x])/(a+b)]/Sqrt[a+b*Sin[c+d*x]] \\[Star] Int[1/Sqrt[a/(a+b)+b/(a+b)*Sin[c+d*x]],x] /;
        FreeQ[{a,b,c,d},x] && NeQ[a^2-b^2,0] && Not[GtQ[a+b,0]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && !gtq!(&a__ + &b__, 0)
        },
        rhs: {
            let angle = &c__ + &d__ * x_;
            let base = &a__ + &b__ * angle.sin();
            let normalized_base = &a__ / (&a__ + &b__) + &b__ / (&a__ + &b__) * angle.sin();
            let recursive = rubi_rhs_int(&(Atom::num(1) / normalized_base.sqrt()), x_);

            rubi_star((&base / (&a__ + &b__)).sqrt() / base.sqrt(), recursive)
        },
    ));
}

fn push_rules_rule_3143(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 3143,
        source: "Int[(a_+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
          -b*Cos[c+d*x]*(a+b*Sin[c+d*x])^(n+1)/(d*(n+1)*(a^2-b^2)) +
          1/((n+1)*(a^2-b^2)) \\[Star] Int[(a+b*Sin[c+d*x])^(n+1)*Simp[a*(n+1)-b*(n+2)*Sin[c+d*x],x],x] /;
        FreeQ[{a,b,c,d},x] && NeQ[a^2-b^2,0] && LtQ[n,-1] && IntegerQ[2*n]",
        desc: "Nondegenerate sine recurrence 1a with A\\[Rule]1,B\\[Rule]0,C\\[Rule]0,m\\[Rule]0,p\\[Rule]0",
        refs: ["G&R 2.552.3"],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, n_, x_],
        optional: [b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && ltq!(n_, -1)
                && integerq!(Atom::num(2) * &n_)
        },
        rhs: {
            let angle = &c__ + &d__ * x_;
            let sin = i_sin(&angle);
            let base = &a__ + &b__ * &sin;
            let discriminant = a__.pow(2) - b__.pow(2);
            let simp = rubi_simp(&(&a__ * (&n_ + 1) - &b__ * (&n_ + 2) * sin), x_);
            let recursive_integrand = base.pow(&n_ + 1) * simp;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(
                    &(-&b__ * angle.cos() * base.pow(&n_ + 1)
                        / (&d__ * (&n_ + 1) * &discriminant)),
                    x_,
                ) + rubi_star(Atom::num(1) / ((&n_ + 1) * discriminant), recursive)
        },
    ));
}

fn push_rules_rule_3144(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 3144,
        source: "Int[(a_+b_.*sin[c_.+d_.*x_])^n_,x_Symbol] :=
          Cos[c+d*x]/(d*Sqrt[1+Sin[c+d*x]]*Sqrt[1-Sin[c+d*x]]) \\[Star] Subst[Int[(a+b*x)^n/(Sqrt[1+x]*Sqrt[1-x]),x],x,Sin[c+d*x]] /;
        FreeQ[{a,b,c,d,n},x] && NeQ[a^2-b^2,0] && Not[IntegerQ[2*n]]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, n_, x_],
        optional: [b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, n_], x_)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && !integerq!(Atom::num(2) * &n_)
        },
        rhs: {
            let subst_guard = fresh_substitution_symbol().unwrap();
            let subst = subst_guard.symbol();
            let z = Atom::var(subst);
            let transformed =
                (&a__ + &b__ * &z).pow(&n_) / ((Atom::num(1) + &z).sqrt() * (Atom::num(1) - &z).sqrt());
            let primitive = rubi_rhs_int(&transformed, subst);
            let angle = &c__ + &d__ * x_;
            let sin = i_sin(&angle);
            let substituted = rubi_subst(&primitive, subst, &sin);

            rubi_star(angle.cos()
                    / (&d__
                        * (Atom::num(1) + &sin).sqrt()
                        * (Atom::num(1) - sin).sqrt()), substituted)
        },
    ));
}

fn push_rules_rule_3145(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 3145,
        source: "Int[(a_+b_.*sin[c_.+d_.*x_]*cos[c_.+d_.*x_])^n_,x_Symbol] :=
          Int[(a+b*Sin[2*c+2*d*x]/2)^n,x] /;
        FreeQ[{a,b,c,d,n},x]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: (a__ + b__ * i_sin(c__ + d__ * x_) * i_cos(c__ + d__ * x_)).pow(n_),
        with: [a__, b__, c__, d__, n_, x_],
        optional: [b__, c__, d__],
        when: { freeq!([a__, b__, c__, d__, n_], x_) },
        rhs: {
            let recursive_integrand = (&a__ + &b__ * (Atom::num(2) * &c__ + Atom::num(2) * &d__ * x_).sin() / 2).pow(&n_);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn downvalues_3113_through_3142_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .filter(|order| (3113..=3142).contains(order))
            .collect::<Vec<_>>();

        assert_eq!(orders, (3113..=3142).collect::<Vec<_>>());
    }

    #[test]
    fn downvalues_3143_through_3145_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .filter(|order| (3143..=3145).contains(order))
            .collect::<Vec<_>>();

        assert_eq!(orders, (3143..=3145).collect::<Vec<_>>());
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
    (a__ + b__ * i_sin(c__ + d__ * x_)).pow(n_)
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let x_ = symbols.x_;
    (a__ + b__ * i_sin(c__ + d__ * x_)).sqrt()
}

#[inline(never)]
fn rubi_shared_pattern_2(symbols: &RubiSymbols) -> Atom {
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    (b__ * i_sin(c__ + d__ * x_)).pow(n_)
}

#[inline(never)]
fn rubi_shared_pattern_3(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let x_ = symbols.x_;
    Atom::num(1) / (a__ + b__ * i_sin(c__ + d__ * x_))
}

#[inline(never)]
fn rubi_shared_pattern_4(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let x_ = symbols.x_;
    Atom::num(1) / (a__ + b__ * i_sin(c__ + d__ * x_)).sqrt()
}
