use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_5150(rules);
    push_rules_rule_5151(rules);
    push_rules_rule_5152(rules);
    push_rules_rule_5153(rules);
    push_rules_rule_5154(rules);
    push_rules_rule_5155(rules);
    push_rules_rule_5156(rules);
    push_rules_rule_5157(rules);
    push_rules_rule_5158(rules);
    push_rules_rule_5159(rules);
    push_rules_rule_5160(rules);
    push_rules_rule_5161(rules);
    push_rules_rule_5162(rules);
    push_rules_rule_5163(rules);
    push_rules_rule_5164(rules);
    push_rules_rule_5165(rules);
    // Block 10 is disabled in the Rubi source embedded in docs/rubi_pdf_rules.md.

    push_rules_rule_5166(rules);
    push_rules_rule_5167(rules);
    push_rules_rule_5168(rules);
    push_rules_rule_5169(rules);
    push_rules_rule_5170(rules);
    push_rules_rule_5171(rules);
    push_rules_rule_5172(rules);
    push_rules_rule_5173(rules);
    push_rules_rule_5174(rules);
    push_rules_rule_5175(rules);
    push_rules_rule_5176(rules);
    push_rules_rule_5177(rules);
    push_rules_rule_5178(rules);
    push_rules_rule_5179(rules);
}

fn push_rules_rule_5150(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 5150,
        source: "Int[1/(Sqrt[d_+e_.*x_^2]*(a_.+b_.*ArcSin[c_.*x_])),x_Symbol] :=
          1/(b*c)*Simp[Sqrt[1-c^2*x^2]/Sqrt[d+e*x^2]]*Log[a+b*ArcSin[c*x]] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0]",
        desc: "Piecewise constant extraction and integration by substitution",
        refs: [],
        pattern: Atom::num(1) / ((d__ + e__ * x_.pow(2)).sqrt() * (a__ + b__ * (c__ * x_).asin())),
        with: [d__, e__, a__, b__, c__, x_],
        optional: [e__, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
        },
        rhs: {
            let ratio = (Atom::num(1) - c__.pow(2) * x_.pow(2)).sqrt()
                / (&d__ + &e__ * x_.pow(2)).sqrt();
            let argument = &a__ + &b__ * (&c__ * x_).asin();
            rubi_simp(&(rubi_simp(&ratio, x_) * argument.log() / (&b__ * &c__)), x_)
        },
    ));
}

fn push_rules_rule_5151(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 5151,
        source: "Int[1/(Sqrt[d_+e_.*x_^2]*(a_.+b_.*ArcCos[c_.*x_])),x_Symbol] :=
          -1/(b*c)*Simp[Sqrt[1-c^2*x^2]/Sqrt[d+e*x^2]]*Log[a+b*ArcCos[c*x]]/(b*c*Sqrt[d]) /;
        FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0]",
        desc: "Piecewise constant extraction and integration by substitution",
        refs: [],
        pattern: Atom::num(1) / ((d__ + e__ * x_.pow(2)).sqrt() * (a__ + b__ * (c__ * x_).acos())),
        with: [d__, e__, a__, b__, c__, x_],
        optional: [e__, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
        },
        rhs: {
            let ratio = (Atom::num(1) - c__.pow(2) * x_.pow(2)).sqrt()
                / (&d__ + &e__ * x_.pow(2)).sqrt();
            let argument = &a__ + &b__ * (&c__ * x_).acos();
            rubi_simp(&(-rubi_simp(&ratio, x_) * argument.log() / (&b__ * &c__)), x_)
        },
    ));
}

fn push_rules_rule_5152(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 5152,
        source: "Int[(a_.+b_.*ArcSin[c_.*x_])^n_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
          1/(b*c*(n+1))*Simp[Sqrt[1-c^2*x^2]/Sqrt[d+e*x^2]]*(a+b*ArcSin[c*x])^(n+1) /;
        FreeQ[{a,b,c,d,e,n},x] && EqQ[c^2*d+e,0] && NeQ[n,-1]",
        desc: "Piecewise constant extraction and integration by substitution",
        refs: [],
        pattern: (a__ + b__ * (c__ * x_).asin()).pow(n_) / (d__ + e__ * x_.pow(2)).sqrt(),
        with: [a__, b__, c__, n_, d__, e__, x_],
        optional: [a__, b__, c__, e__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, n_], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && neq!(n_, -1)
        },
        rhs: {
            let ratio = (Atom::num(1) - c__.pow(2) * x_.pow(2)).sqrt()
                / (&d__ + &e__ * x_.pow(2)).sqrt();
            let argument = &a__ + &b__ * (&c__ * x_).asin();
            rubi_simp(&(rubi_simp(&ratio, x_) * argument.pow(&n_ + Atom::num(1)) / (&b__ * &c__ * (&n_ + Atom::num(1)))), x_)
        },
    ));
}

fn push_rules_rule_5153(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 5153,
        source: "Int[(a_.+b_.*ArcCos[c_.*x_])^n_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
          -1/(b*c*(n+1))*Simp[Sqrt[1-c^2*x^2]/Sqrt[d+e*x^2]]*(a+b*ArcCos[c*x])^(n+1) /;
        FreeQ[{a,b,c,d,e,n},x] && EqQ[c^2*d+e,0] && NeQ[n,-1]",
        desc: "Piecewise constant extraction and integration by substitution",
        refs: [],
        pattern: (a__ + b__ * (c__ * x_).acos()).pow(n_) / (d__ + e__ * x_.pow(2)).sqrt(),
        with: [a__, b__, c__, n_, d__, e__, x_],
        optional: [a__, b__, c__, e__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, n_], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && neq!(n_, -1)
        },
        rhs: {
            let ratio = (Atom::num(1) - c__.pow(2) * x_.pow(2)).sqrt()
                / (&d__ + &e__ * x_.pow(2)).sqrt();
            let argument = &a__ + &b__ * (&c__ * x_).acos();
            rubi_simp(&(-rubi_simp(&ratio, x_) * argument.pow(&n_ + Atom::num(1)) / (&b__ * &c__ * (&n_ + Atom::num(1)))), x_)
        },
    ));
}

fn push_rules_rule_5154(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, p_, x_);
    rules.push(rubi_rule!(
        order: 5154,
        source: "Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_.*x_]),x_Symbol] :=
          With[{u=IntHide[(d+e*x^2)^p,x]},
          (a+b*ArcSin[c*x]) \\[Star] u - b*c \\[Star] Int[SimplifyIntegrand[u/Sqrt[1-c^2*x^2],x],x]] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && IGtQ[p,0]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [d__, e__, p_, a__, b__, c__, x_],
        optional: [e__, p_, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && igtq!(p_, 0)
        },
        rhs: {
            let argument = &a__ + &b__ * (&c__ * x_).asin();
            let u = rubi_int_hide(&(&d__ + &e__ * x_.pow(2)).pow(&p_), x_).rubi_rhs();
            let recursive = rubi_simplify_integrand(
                &(&u / (Atom::num(1) - c__.pow(2) * x_.pow(2)).sqrt()),
                x_,
            );
            rubi_star(argument, u)
                    + rubi_star(-&b__ * &c__, rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_5155(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, p_, x_);
    rules.push(rubi_rule!(
        order: 5155,
        source: "Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_.*x_]),x_Symbol] :=
          With[{u=IntHide[(d+e*x^2)^p,x]},
          (a+b*ArcCos[c*x]) \\[Star] u + b*c \\[Star] Int[SimplifyIntegrand[u/Sqrt[1-c^2*x^2],x],x]] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && IGtQ[p,0]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [d__, e__, p_, a__, b__, c__, x_],
        optional: [e__, p_, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && igtq!(p_, 0)
        },
        rhs: {
            let argument = &a__ + &b__ * (&c__ * x_).acos();
            let u = rubi_int_hide(&(&d__ + &e__ * x_.pow(2)).pow(&p_), x_).rubi_rhs();
            let recursive = rubi_simplify_integrand(
                &(&u / (Atom::num(1) - c__.pow(2) * x_.pow(2)).sqrt()),
                x_,
            );
            rubi_star(argument, u)
                    + rubi_star(&b__ * &c__, rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_5156(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 5156,
        source: "Int[Sqrt[d_+e_.*x_^2]*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
          x*Sqrt[d+e*x^2]*(a+b*ArcSin[c*x])^n/2 -
          b*c*n/2*Simp[Sqrt[d+e*x^2]/Sqrt[1-c^2*x^2]] \\[Star] Int[x*(a+b*ArcSin[c*x])^(n-1),x] +
          1/2*Simp[Sqrt[d+e*x^2]/Sqrt[1-c^2*x^2]] \\[Star] Int[(a+b*ArcSin[c*x])^n/Sqrt[1-c^2*x^2],x] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && GtQ[n,0]",
        desc: "Inverted integration by parts",
        refs: [],
        pattern: (d__ + e__ * x_.pow(2)).sqrt() * (a__ + b__ * (c__ * x_).asin()).pow(n_),
        with: [d__, e__, a__, b__, c__, n_, x_],
        optional: [e__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && gtq!(n_, 0)
        },
        rhs: {
            let quadratic = &d__ + &e__ * x_.pow(2);
            let denominator = Atom::num(1) - c__.pow(2) * x_.pow(2);
            let argument = &a__ + &b__ * (&c__ * x_).asin();
            let ratio = rubi_simp(&(quadratic.sqrt() / denominator.sqrt()), x_);
            rubi_simp(&(x_ * quadratic.sqrt() * argument.pow(&n_) / Atom::num(2)), x_)
                    + rubi_star(-&b__ * &c__ * &n_ * &ratio / Atom::num(2), rubi_rhs_int(&(x_ * argument.pow(&n_ - Atom::num(1))), x_))
                    + rubi_star(ratio / Atom::num(2), rubi_rhs_int(&(argument.pow(&n_) / denominator.sqrt()), x_))
        },
    ));
}

fn push_rules_rule_5157(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 5157,
        source: "Int[Sqrt[d_+e_.*x_^2]*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
          x*Sqrt[d+e*x^2]*(a+b*ArcCos[c*x])^n/2 +
          b*c*n/2*Simp[Sqrt[d+e*x^2]/Sqrt[1-c^2*x^2]] \\[Star] Int[x*(a+b*ArcCos[c*x])^(n-1),x] +
          1/2*Simp[Sqrt[d+e*x^2]/Sqrt[1-c^2*x^2]] \\[Star] Int[(a+b*ArcCos[c*x])^n/Sqrt[1-c^2*x^2],x] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && GtQ[n,0]",
        desc: "Inverted integration by parts",
        refs: [],
        pattern: (d__ + e__ * x_.pow(2)).sqrt() * (a__ + b__ * (c__ * x_).acos()).pow(n_),
        with: [d__, e__, a__, b__, c__, n_, x_],
        optional: [e__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && gtq!(n_, 0)
        },
        rhs: {
            let quadratic = &d__ + &e__ * x_.pow(2);
            let denominator = Atom::num(1) - c__.pow(2) * x_.pow(2);
            let argument = &a__ + &b__ * (&c__ * x_).acos();
            let ratio = rubi_simp(&(quadratic.sqrt() / denominator.sqrt()), x_);
            rubi_simp(&(x_ * quadratic.sqrt() * argument.pow(&n_) / Atom::num(2)), x_)
                    + rubi_star(&b__ * &c__ * &n_ * &ratio / Atom::num(2), rubi_rhs_int(&(x_ * argument.pow(&n_ - Atom::num(1))), x_))
                    + rubi_star(ratio / Atom::num(2), rubi_rhs_int(&(argument.pow(&n_) / denominator.sqrt()), x_))
        },
    ));
}

fn push_rules_rule_5158(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5158,
        source: "Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
          x*(d+e*x^2)^p*(a+b*ArcSin[c*x])^n/(2*p+1) +
          2*d*p/(2*p+1) \\[Star] Int[(d+e*x^2)^(p-1)*(a+b*ArcSin[c*x])^n,x] -
          b*c*n/(2*p+1)*Simp[(d+e*x^2)^p/(1-c^2*x^2)^p] \\[Star] Int[x*(1-c^2*x^2)^(p-1/2)*(a+b*ArcSin[c*x])^(n-1),x] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && GtQ[n,0] && GtQ[p,0]",
        desc: "Inverted integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [e__, p_, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && gtq!(n_, 0)
                && gtq!(p_, 0)
        },
        rhs: {
            let _half = Atom::num(1) / Atom::num(2);
            let quadratic = &d__ + &e__ * x_.pow(2);
            let denominator = Atom::num(1) - c__.pow(2) * x_.pow(2);
            let argument = &a__ + &b__ * (&c__ * x_).asin();
            let ratio = rubi_simp(&(quadratic.pow(&p_) / denominator.pow(&p_)), x_);
            rubi_simp(&(x_ * quadratic.pow(&p_) * argument.pow(&n_)
                    / (Atom::num(2) * &p_ + Atom::num(1))), x_)
                    + rubi_star(Atom::num(2) * &d__ * &p_ / (Atom::num(2) * &p_ + Atom::num(1)), rubi_rhs_int(&(quadratic.pow(&p_ - Atom::num(1)) * argument.pow(&n_)), x_))
                    + rubi_star(-&b__ * &c__ * &n_ * ratio / (Atom::num(2) * &p_ + Atom::num(1)), rubi_rhs_int(
                            &(x_ * denominator.pow(&p_ - &(Atom::num(1) / 2)) * argument.pow(&n_ - Atom::num(1))),
                            x_,
                        ))
        },
    ));
}

fn push_rules_rule_5159(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5159,
        source: "Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
          x*(d+e*x^2)^p*(a+b*ArcCos[c*x])^n/(2*p+1) +
          2*d*p/(2*p+1) \\[Star] Int[(d+e*x^2)^(p-1)*(a+b*ArcCos[c*x])^n,x] +
          b*c*n/(2*p+1)*Simp[(d+e*x^2)^p/(1-c^2*x^2)^p] \\[Star] Int[x*(1-c^2*x^2)^(p-1/2)*(a+b*ArcCos[c*x])^(n-1),x] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && GtQ[n,0] && GtQ[p,0]",
        desc: "Inverted integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [e__, p_, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && gtq!(n_, 0)
                && gtq!(p_, 0)
        },
        rhs: {
            let _half = Atom::num(1) / Atom::num(2);
            let quadratic = &d__ + &e__ * x_.pow(2);
            let denominator = Atom::num(1) - c__.pow(2) * x_.pow(2);
            let argument = &a__ + &b__ * (&c__ * x_).acos();
            let ratio = rubi_simp(&(quadratic.pow(&p_) / denominator.pow(&p_)), x_);
            rubi_simp(&(x_ * quadratic.pow(&p_) * argument.pow(&n_)
                    / (Atom::num(2) * &p_ + Atom::num(1))), x_)
                    + rubi_star(Atom::num(2) * &d__ * &p_ / (Atom::num(2) * &p_ + Atom::num(1)), rubi_rhs_int(&(quadratic.pow(&p_ - Atom::num(1)) * argument.pow(&n_)), x_))
                    + rubi_star(&b__ * &c__ * &n_ * ratio / (Atom::num(2) * &p_ + Atom::num(1)), rubi_rhs_int(
                            &(x_ * denominator.pow(&p_ - &(Atom::num(1) / 2)) * argument.pow(&n_ - Atom::num(1))),
                            x_,
                        ))
        },
    ));
}

fn push_rules_rule_5160(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 5160,
        source: "Int[(a_.+b_.*ArcSin[c_.*x_])^n_./(d_+e_.*x_^2)^(3/2),x_Symbol] :=
          x*(a+b*ArcSin[c*x])^n/(d*Sqrt[d+e*x^2]) -
          b*c*n/d*Simp[Sqrt[1-c^2*x^2]/Sqrt[d+e*x^2]] \\[Star] Int[x*(a+b*ArcSin[c*x])^(n-1)/(1-c^2*x^2),x] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && GtQ[n,0]",
        desc: "Integration by parts and piecewise constant extraction",
        refs: [],
        pattern: (a__ + b__ * (c__ * x_).asin()).pow(n_)
            / (d__ + e__ * x_.pow(2)).pow(Atom::num(3) / Atom::num(2)),
        with: [a__, b__, c__, n_, d__, e__, x_],
        optional: [e__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && gtq!(n_, 0)
        },
        rhs: {
            let quadratic = &d__ + &e__ * x_.pow(2);
            let denominator = Atom::num(1) - c__.pow(2) * x_.pow(2);
            let argument = &a__ + &b__ * (&c__ * x_).asin();
            let ratio = rubi_simp(&(denominator.sqrt() / quadratic.sqrt()), x_);
            rubi_simp(&(x_ * argument.pow(&n_) / (&d__ * quadratic.sqrt())), x_)
                    + rubi_star(-&b__ * &c__ * &n_ * ratio / &d__, rubi_rhs_int(&(x_ * argument.pow(&n_ - Atom::num(1)) / denominator), x_))
        },
    ));
}

fn push_rules_rule_5161(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 5161,
        source: "Int[(a_.+b_.*ArcCos[c_.*x_])^n_./(d_+e_.*x_^2)^(3/2),x_Symbol] :=
          x*(a+b*ArcCos[c*x])^n/(d*Sqrt[d+e*x^2]) +
          b*c*n/d*Simp[Sqrt[1-c^2*x^2]/Sqrt[d+e*x^2]] \\[Star] Int[x*(a+b*ArcCos[c*x])^(n-1)/(1-c^2*x^2),x] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && GtQ[n,0]",
        desc: "Integration by parts and piecewise constant extraction",
        refs: [],
        pattern: (a__ + b__ * (c__ * x_).acos()).pow(n_)
            / (d__ + e__ * x_.pow(2)).pow(Atom::num(3) / Atom::num(2)),
        with: [a__, b__, c__, n_, d__, e__, x_],
        optional: [e__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && gtq!(n_, 0)
        },
        rhs: {
            let quadratic = &d__ + &e__ * x_.pow(2);
            let denominator = Atom::num(1) - c__.pow(2) * x_.pow(2);
            let argument = &a__ + &b__ * (&c__ * x_).acos();
            let ratio = rubi_simp(&(denominator.sqrt() / quadratic.sqrt()), x_);
            rubi_simp(&(x_ * argument.pow(&n_) / (&d__ * quadratic.sqrt())), x_)
                    + rubi_star(&b__ * &c__ * &n_ * ratio / &d__, rubi_rhs_int(&(x_ * argument.pow(&n_ - Atom::num(1)) / denominator), x_))
        },
    ));
}

fn push_rules_rule_5162(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5162,
        source: "Int[(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
          -x*(d+e*x^2)^(p+1)*(a+b*ArcSin[c*x])^n/(2*d*(p+1)) +
          (2*p+3)/(2*d*(p+1)) \\[Star] Int[(d+e*x^2)^(p+1)*(a+b*ArcSin[c*x])^n,x] +
          b*c*n/(2*(p+1))*Simp[(d+e*x^2)^p/(1-c^2*x^2)^p] \\[Star] Int[x*(1-c^2*x^2)^(p+1/2)*(a+b*ArcSin[c*x])^(n-1),x] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && GtQ[n,0] && LtQ[p,-1] && NeQ[p,-3/2]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [e__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && gtq!(n_, 0)
                && ltq!(p_, -1)
                && neq!(p_, -Atom::num(3) / Atom::num(2))
        },
        rhs: {
            let _half = Atom::num(1) / Atom::num(2);
            let quadratic = &d__ + &e__ * x_.pow(2);
            let denominator = Atom::num(1) - c__.pow(2) * x_.pow(2);
            let argument = &a__ + &b__ * (&c__ * x_).asin();
            let ratio = rubi_simp(&(quadratic.pow(&p_) / denominator.pow(&p_)), x_);
            rubi_simp(&(Atom::num(-1) * x_ * quadratic.pow(&p_ + Atom::num(1)) * argument.pow(&n_)
                    / (Atom::num(2) * &d__ * (&p_ + Atom::num(1)))), x_)
                    + rubi_star((Atom::num(2) * &p_ + Atom::num(3))
                            / (Atom::num(2) * &d__ * (&p_ + Atom::num(1))), rubi_rhs_int(&(quadratic.pow(&p_ + Atom::num(1)) * argument.pow(&n_)), x_))
                    + rubi_star(&b__ * &c__ * &n_ * ratio / (Atom::num(2) * (&p_ + Atom::num(1))), rubi_rhs_int(
                            &(x_ * denominator.pow(&p_ + &(Atom::num(1) / 2)) * argument.pow(&n_ - Atom::num(1))),
                            x_,
                        ))
        },
    ));
}

fn push_rules_rule_5163(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5163,
        source: "Int[(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
          -x*(d+e*x^2)^(p+1)*(a+b*ArcCos[c*x])^n/(2*d*(p+1)) +
          (2*p+3)/(2*d*(p+1)) \\[Star] Int[(d+e*x^2)^(p+1)*(a+b*ArcCos[c*x])^n,x] -
          b*c*n/(2*(p+1))*Simp[(d+e*x^2)^p/(1-c^2*x^2)^p] \\[Star] Int[x*(1-c^2*x^2)^(p+1/2)*(a+b*ArcCos[c*x])^(n-1),x] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && GtQ[n,0] && LtQ[p,-1] && NeQ[p,-3/2]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [e__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && gtq!(n_, 0)
                && ltq!(p_, -1)
                && neq!(p_, -Atom::num(3) / Atom::num(2))
        },
        rhs: {
            let _half = Atom::num(1) / Atom::num(2);
            let quadratic = &d__ + &e__ * x_.pow(2);
            let denominator = Atom::num(1) - c__.pow(2) * x_.pow(2);
            let argument = &a__ + &b__ * (&c__ * x_).acos();
            let ratio = rubi_simp(&(quadratic.pow(&p_) / denominator.pow(&p_)), x_);
            rubi_simp(&(Atom::num(-1) * x_ * quadratic.pow(&p_ + Atom::num(1)) * argument.pow(&n_)
                    / (Atom::num(2) * &d__ * (&p_ + Atom::num(1)))), x_)
                    + rubi_star((Atom::num(2) * &p_ + Atom::num(3))
                            / (Atom::num(2) * &d__ * (&p_ + Atom::num(1))), rubi_rhs_int(&(quadratic.pow(&p_ + Atom::num(1)) * argument.pow(&n_)), x_))
                    + rubi_star(-&b__ * &c__ * &n_ * ratio / (Atom::num(2) * (&p_ + Atom::num(1))), rubi_rhs_int(
                            &(x_ * denominator.pow(&p_ + &(Atom::num(1) / 2)) * argument.pow(&n_ - Atom::num(1))),
                            x_,
                        ))
        },
    ));
}

fn push_rules_rule_5164(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 5164,
        source: "Int[(a_.+b_.*ArcSin[c_.*x_])^n_./(d_+e_.*x_^2),x_Symbol] :=
          1/(c*d) \\[Star] Subst[Int[(a+b*x)^n*Sec[x],x],x,ArcSin[c*x]] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && IGtQ[n,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (a__ + b__ * (c__ * x_).asin()).pow(n_) / (d__ + e__ * x_.pow(2)),
        with: [a__, b__, c__, n_, d__, e__, x_],
        optional: [a__, b__, c__, e__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && igtq!(n_, 0)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let payload = (&a__ + &b__ * &sub_atom).pow(&n_) * sub_atom.sec();
            let primitive = rubi_rhs_int(&payload, sub);
            let substituted = rubi_subst(&primitive, sub, (&c__ * x_).asin());
            rubi_star(Atom::num(1) / (&c__ * &d__), substituted)
        },
    ));
}

fn push_rules_rule_5165(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 5165,
        source: "Int[(a_.+b_.*ArcCos[c_.*x_])^n_./(d_+e_.*x_^2),x_Symbol] :=
          -1/(c*d) \\[Star] Subst[Int[(a+b*x)^n*Csc[x],x],x,ArcCos[c*x]] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && IGtQ[n,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (a__ + b__ * (c__ * x_).acos()).pow(n_) / (d__ + e__ * x_.pow(2)),
        with: [a__, b__, c__, n_, d__, e__, x_],
        optional: [a__, b__, c__, e__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && igtq!(n_, 0)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let payload = (&a__ + &b__ * &sub_atom).pow(&n_) * sub_atom.csc();
            let primitive = rubi_rhs_int(&payload, sub);
            let substituted = rubi_subst(&primitive, sub, (&c__ * x_).acos());
            rubi_star(-Atom::num(1) / (&c__ * &d__), substituted)
        },
    ));
}

fn push_rules_rule_5166(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5166,
        source: "Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_.*x_])^n_,x_Symbol] :=
          Sqrt[1-c^2*x^2]*(d+e*x^2)^p*(a+b*ArcSin[c*x])^(n+1)/(b*c*(n+1)) +
          c*(2*p+1)/(b*(n+1))*Simp[(d+e*x^2)^p/(1-c^2*x^2)^p] \\[Star] Int[x*(1-c^2*x^2)^(p-1/2)*(a+b*ArcSin[c*x])^(n+1),x] /;
        FreeQ[{a,b,c,d,e,p},x] && EqQ[c^2*d+e,0] && LtQ[n,-1]",
        desc: "Integration by parts and piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [e__, p_, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__, p_], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && ltq!(n_, -1)
        },
        rhs: {
            let quadratic = &d__ + &e__ * x_.pow(2);
            let denominator = Atom::num(1) - c__.pow(2) * x_.pow(2);
            let argument = &a__ + &b__ * (&c__ * x_).asin();
            let ratio = rubi_simp(&(quadratic.pow(&p_) / denominator.pow(&p_)), x_);
            rubi_simp(&(denominator.sqrt() * quadratic.pow(&p_) * argument.pow(&n_ + Atom::num(1))
                    / (&b__ * &c__ * (&n_ + Atom::num(1)))), x_)
                    + rubi_star(&c__ * (Atom::num(2) * &p_ + Atom::num(1)) * ratio
                            / (&b__ * (&n_ + Atom::num(1))), rubi_rhs_int(
                            &(x_
                                * denominator.pow(&p_ - half_integer_atom(1))
                                * argument.pow(&n_ + Atom::num(1))),
                            x_,
                        ))
        },
    ));
}

fn push_rules_rule_5167(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5167,
        source: "Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_.*x_])^n_,x_Symbol] :=
          -Sqrt[1-c^2*x^2]*(d+e*x^2)^p*(a+b*ArcCos[c*x])^(n+1)/(b*c*(n+1)) -
          c*(2*p+1)/(b*(n+1))*Simp[(d+e*x^2)^p/(1-c^2*x^2)^p] \\[Star] Int[x*(1-c^2*x^2)^(p-1/2)*(a+b*ArcCos[c*x])^(n+1),x] /;
        FreeQ[{a,b,c,d,e,p},x] && EqQ[c^2*d+e,0] && LtQ[n,-1]",
        desc: "Integration by parts and piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [e__, p_, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__, p_], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && ltq!(n_, -1)
        },
        rhs: {
            let quadratic = &d__ + &e__ * x_.pow(2);
            let denominator = Atom::num(1) - c__.pow(2) * x_.pow(2);
            let argument = &a__ + &b__ * (&c__ * x_).acos();
            let ratio = rubi_simp(&(quadratic.pow(&p_) / denominator.pow(&p_)), x_);
            rubi_simp(&(-denominator.sqrt() * quadratic.pow(&p_) * argument.pow(&n_ + Atom::num(1))
                    / (&b__ * &c__ * (&n_ + Atom::num(1)))), x_)
                    + rubi_star(-&c__ * (Atom::num(2) * &p_ + Atom::num(1)) * ratio
                            / (&b__ * (&n_ + Atom::num(1))), rubi_rhs_int(
                            &(x_
                                * denominator.pow(&p_ - half_integer_atom(1))
                                * argument.pow(&n_ + Atom::num(1))),
                            x_,
                        ))
        },
    ));
}

fn push_rules_rule_5168(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5168,
        source: "Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
          1/(b*c)*Simp[(d+e*x^2)^p/(1-c^2*x^2)^p] \\[Star] Subst[Int[x^n*Cos[-a/b+x/b]^(2*p+1),x],x,a+b*ArcSin[c*x]] /;
        FreeQ[{a,b,c,d,e,n},x] && EqQ[c^2*d+e,0] && IGtQ[2*p,0]",
        desc: "Piecewise constant extraction and integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [e__, p_, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, n_], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && igtq!(Atom::num(2) * &p_, 0)
        },
        rhs: {
            let quadratic = &d__ + &e__ * x_.pow(2);
            let denominator = Atom::num(1) - c__.pow(2) * x_.pow(2);
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let angle = -&a__ / &b__ + &sub_atom / &b__;
            let payload = sub_atom.pow(&n_) * angle.cos().pow(Atom::num(2) * &p_ + Atom::num(1));
            let primitive = rubi_rhs_int(&payload, sub);
            let ratio = rubi_simp(&(quadratic.pow(&p_) / denominator.pow(&p_)), x_);
            let substituted =
                rubi_subst(&primitive, sub, &a__ + &b__ * (&c__ * x_).asin());
            rubi_star(ratio / (&b__ * &c__), substituted)
        },
    ));
}

fn push_rules_rule_5169(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5169,
        source: "Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
          -1/(b*c)*Simp[(d+e*x^2)^p/(1-c^2*x^2)^p] \\[Star] Subst[Int[x^n*Sin[-a/b+x/b]^(2*p+1),x],x,a+b*ArcCos[c*x]] /;
        FreeQ[{a,b,c,d,e,n},x] && EqQ[c^2*d+e,0] && IGtQ[2*p,0]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [e__, p_, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, n_], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && igtq!(Atom::num(2) * &p_, 0)
        },
        rhs: {
            let quadratic = &d__ + &e__ * x_.pow(2);
            let denominator = Atom::num(1) - c__.pow(2) * x_.pow(2);
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let angle = -&a__ / &b__ + &sub_atom / &b__;
            let payload = sub_atom.pow(&n_) * angle.sin().pow(Atom::num(2) * &p_ + Atom::num(1));
            let primitive = rubi_rhs_int(&payload, sub);
            let ratio = rubi_simp(&(quadratic.pow(&p_) / denominator.pow(&p_)), x_);
            let substituted =
                rubi_subst(&primitive, sub, &a__ + &b__ * (&c__ * x_).acos());
            rubi_star(-ratio / (&b__ * &c__), substituted)
        },
    ));
}

fn push_rules_rule_5170(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, p_, x_);
    rules.push(rubi_rule!(
        order: 5170,
        source: "Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_.*x_]),x_Symbol] :=
          With[{u=IntHide[(d+e*x^2)^p,x]},
          (a+b*ArcSin[c*x]) \\[Star] u - b*c \\[Star] Int[SimplifyIntegrand[u/Sqrt[1-c^2*x^2],x],x]] /;
        FreeQ[{a,b,c,d,e},x] && NeQ[c^2*d+e,0] && (IGtQ[p,0] || ILtQ[p+1/2,0])",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [d__, e__, p_, a__, b__, c__, x_],
        optional: [e__, p_, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && neq!(c__.pow(2) * &d__ + &e__, 0)
                && (igtq!(p_, 0) || iltq!(&p_ + Atom::num(1) / 2, 0))
        },
        rhs: {
            let argument = &a__ + &b__ * (&c__ * x_).asin();
            let u = rubi_int_hide(&(&d__ + &e__ * x_.pow(2)).pow(&p_), x_).rubi_rhs();
            let recursive = rubi_simplify_integrand(
                &(&u / (Atom::num(1) - c__.pow(2) * x_.pow(2)).sqrt()),
                x_,
            );
            rubi_star(argument, u)
                    + rubi_star(-&b__ * &c__, rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_5171(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, p_, x_);
    rules.push(rubi_rule!(
        order: 5171,
        source: "Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_.*x_]),x_Symbol] :=
          With[{u=IntHide[(d+e*x^2)^p,x]},
          (a+b*ArcCos[c*x]) \\[Star] u + b*c \\[Star] Int[SimplifyIntegrand[u/Sqrt[1-c^2*x^2],x],x]] /;
        FreeQ[{a,b,c,d,e},x] && NeQ[c^2*d+e,0] && (IGtQ[p,0] || ILtQ[p+1/2,0])",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [d__, e__, p_, a__, b__, c__, x_],
        optional: [e__, p_, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && neq!(c__.pow(2) * &d__ + &e__, 0)
                && (igtq!(p_, 0) || iltq!(&p_ + Atom::num(1) / 2, 0))
        },
        rhs: {
            let argument = &a__ + &b__ * (&c__ * x_).acos();
            let u = rubi_int_hide(&(&d__ + &e__ * x_.pow(2)).pow(&p_), x_).rubi_rhs();
            let recursive = rubi_simplify_integrand(
                &(&u / (Atom::num(1) - c__.pow(2) * x_.pow(2)).sqrt()),
                x_,
            );
            rubi_star(argument, u)
                    + rubi_star(&b__ * &c__, rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_5172(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5172,
        source: "Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
          Int[ExpandIntegrand[(a+b*ArcSin[c*x])^n,(d+e*x^2)^p,x],x] /;
        FreeQ[{a,b,c,d,e,n},x] && NeQ[c^2*d+e,0] && IntegerQ[p] && (GtQ[p,0] || IGtQ[n,0])",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [e__, p_, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, n_], x_)
                && neq!(c__.pow(2) * &d__ + &e__, 0)
                && integerq!(p_)
                && (gtq!(p_, 0) || igtq!(n_, 0))
        },
        rhs: {
            let expanded = rubi_expand_integrand_product(
                &(&a__ + &b__ * (&c__ * x_).asin()).pow(&n_),
                &(&d__ + &e__ * x_.pow(2)).pow(&p_),
                x_,
            );
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_5173(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5173,
        source: "Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
          Int[ExpandIntegrand[(a+b*ArcCos[c*x])^n,(d+e*x^2)^p,x],x] /;
        FreeQ[{a,b,c,d,e,n},x] && NeQ[c^2*d+e,0] && IntegerQ[p] && (GtQ[p,0] || IGtQ[n,0])",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [e__, p_, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, n_], x_)
                && neq!(c__.pow(2) * &d__ + &e__, 0)
                && integerq!(p_)
                && (gtq!(p_, 0) || igtq!(n_, 0))
        },
        rhs: {
            let expanded = rubi_expand_integrand_product(
                &(&a__ + &b__ * (&c__ * x_).acos()).pow(&n_),
                &(&d__ + &e__ * x_.pow(2)).pow(&p_),
                x_,
            );
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_5174(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5174,
        source: "Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
          Unintegrable[(d+e*x^2)^p*(a+b*ArcSin[c*x])^n,x] /;
        FreeQ[{a,b,c,d,e,n,p},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [e__, p_, a__, b__, c__, n_],
        when: { freeq!([a__, b__, c__, d__, e__, n_, p_], x_) },
        rhs: {
            let integrand =
                (&d__ + &e__ * x_.pow(2)).pow(&p_) * (&a__ + &b__ * (&c__ * x_).asin()).pow(&n_);
            rubi_unintegrable(integrand, x_)
        },
    ));
}

fn push_rules_rule_5175(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5175,
        source: "Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
          Unintegrable[(d+e*x^2)^p*(a+b*ArcCos[c*x])^n,x] /;
        FreeQ[{a,b,c,d,e,n,p},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [e__, p_, a__, b__, c__, n_],
        when: { freeq!([a__, b__, c__, d__, e__, n_, p_], x_) },
        rhs: {
            let integrand =
                (&d__ + &e__ * x_.pow(2)).pow(&p_) * (&a__ + &b__ * (&c__ * x_).acos()).pow(&n_);
            rubi_unintegrable(integrand, x_)
        },
    ));
}

fn push_rules_rule_5176(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 5176,
        source: "Int[(d_+e_.*x_)^p_*(f_+g_.*x_)^q_*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
          (-d^2*g/e)^q \\[Star] Int[(d+e*x)^(p-q)*(1-c^2*x^2)^q*(a+b*ArcSin[c*x])^n,x] /;
        FreeQ[{a,b,c,d,e,f,g,n},x] && EqQ[e*f+d*g,0] && EqQ[c^2*d^2-e^2,0] && HalfIntegerQ[p,q] && GeQ[p-q,0] && GtQ[d,0] && LtQ[g/e,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [d__, e__, p_, f__, g__, q_, a__, b__, c__, n_, x_],
        optional: [e__, g__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, n_], x_)
                && eqq!(&e__ * &f__ + &d__ * &g__, 0)
                && eqq!(c__.pow(2) * d__.pow(2) - e__.pow(2), 0)
                && half_integer_numerator(&p_).is_some()
                && half_integer_numerator(&q_).is_some()
                && geq!(&p_ - &q_, 0)
                && gtq!(d__, 0)
                && ltq!(&g__ / &e__, 0)
        },
        rhs: {
            let argument = &a__ + &b__ * (&c__ * x_).asin();
            let transformed =
                (&d__ + &e__ * x_).pow(&p_ - &q_) * (Atom::num(1) - c__.pow(2) * x_.pow(2)).pow(&q_) * argument.pow(&n_);
            rubi_star((-d__.pow(2) * &g__ / &e__).pow(&q_), rubi_rhs_int(&transformed, x_))
        },
    ));
}

fn push_rules_rule_5177(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 5177,
        source: "Int[(d_+e_.*x_)^p_*(f_+g_.*x_)^q_*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
          (-d^2*g/e)^q \\[Star] Int[(d+e*x)^(p-q)*(1-c^2*x^2)^q*(a+b*ArcCos[c*x])^n,x] /;
        FreeQ[{a,b,c,d,e,f,g,n},x] && EqQ[e*f+d*g,0] && EqQ[c^2*d^2-e^2,0] && HalfIntegerQ[p,q] && GeQ[p-q,0] && GtQ[d,0] && LtQ[g/e,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [d__, e__, p_, f__, g__, q_, a__, b__, c__, n_, x_],
        optional: [e__, g__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, n_], x_)
                && eqq!(&e__ * &f__ + &d__ * &g__, 0)
                && eqq!(c__.pow(2) * d__.pow(2) - e__.pow(2), 0)
                && half_integer_numerator(&p_).is_some()
                && half_integer_numerator(&q_).is_some()
                && geq!(&p_ - &q_, 0)
                && gtq!(d__, 0)
                && ltq!(&g__ / &e__, 0)
        },
        rhs: {
            let argument = &a__ + &b__ * (&c__ * x_).acos();
            let transformed =
                (&d__ + &e__ * x_).pow(&p_ - &q_) * (Atom::num(1) - c__.pow(2) * x_.pow(2)).pow(&q_) * argument.pow(&n_);
            rubi_star((-d__.pow(2) * &g__ / &e__).pow(&q_), rubi_rhs_int(&transformed, x_))
        },
    ));
}

fn push_rules_rule_5178(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 5178,
        source: "Int[(d_+e_.*x_)^p_*(f_+g_.*x_)^q_*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
          (d+e*x)^q*(f+g*x)^q/(1-c^2*x^2)^q \\[Star] Int[(d+e*x)^(p-q)*(1-c^2*x^2)^q*(a+b*ArcSin[c*x])^n,x] /;
        FreeQ[{a,b,c,d,e,f,g,n},x] && EqQ[e*f+d*g,0] && EqQ[c^2*d^2-e^2,0] && HalfIntegerQ[p,q] && GeQ[p-q,0]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [d__, e__, p_, f__, g__, q_, a__, b__, c__, n_, x_],
        optional: [e__, g__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, n_], x_)
                && eqq!(&e__ * &f__ + &d__ * &g__, 0)
                && eqq!(c__.pow(2) * d__.pow(2) - e__.pow(2), 0)
                && half_integer_numerator(&p_).is_some()
                && half_integer_numerator(&q_).is_some()
                && geq!(&p_ - &q_, 0)
        },
        rhs: {
            let argument = &a__ + &b__ * (&c__ * x_).asin();
            let denominator = Atom::num(1) - c__.pow(2) * x_.pow(2);
            let transformed = (&d__ + &e__ * x_).pow(&p_ - &q_) * denominator.pow(&q_) * argument.pow(&n_);
            let coefficient = (&d__ + &e__ * x_).pow(&q_)
                * (&f__ + &g__ * x_).pow(&q_)
                / denominator.pow(&q_);
            rubi_star(coefficient, rubi_rhs_int(&transformed, x_))
        },
    ));
}

fn push_rules_rule_5179(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 5179,
        source: "Int[(d_+e_.*x_)^p_*(f_+g_.*x_)^q_*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
          (d+e*x)^q*(f+g*x)^q/(1-c^2*x^2)^q \\[Star] Int[(d+e*x)^(p-q)*(1-c^2*x^2)^q*(a+b*ArcCos[c*x])^n,x] /;
        FreeQ[{a,b,c,d,e,f,g,n},x] && EqQ[e*f+d*g,0] && EqQ[c^2*d^2-e^2,0] && HalfIntegerQ[p,q] && GeQ[p-q,0]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [d__, e__, p_, f__, g__, q_, a__, b__, c__, n_, x_],
        optional: [e__, g__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, n_], x_)
                && eqq!(&e__ * &f__ + &d__ * &g__, 0)
                && eqq!(c__.pow(2) * d__.pow(2) - e__.pow(2), 0)
                && half_integer_numerator(&p_).is_some()
                && half_integer_numerator(&q_).is_some()
                && geq!(&p_ - &q_, 0)
        },
        rhs: {
            let argument = &a__ + &b__ * (&c__ * x_).acos();
            let denominator = Atom::num(1) - c__.pow(2) * x_.pow(2);
            let transformed = (&d__ + &e__ * x_).pow(&p_ - &q_) * denominator.pow(&q_) * argument.pow(&n_);
            let coefficient = (&d__ + &e__ * x_).pow(&q_)
                * (&f__ + &g__ * x_).pow(&q_)
                / denominator.pow(&q_);
            rubi_star(coefficient, rubi_rhs_int(&transformed, x_))
        },
    ));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn downvalues_5150_through_5179_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .filter(|order| (5150..=5179).contains(order))
            .collect::<Vec<_>>();
        assert_eq!(orders, (5150..=5179).collect::<Vec<_>>());
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
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let q_ = symbols.q_;
    let x_ = symbols.x_;
    (d__ + e__ * x_).pow(p_) * (f__ + g__ * x_).pow(q_) * (a__ + b__ * (c__ * x_).acos()).pow(n_)
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
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let q_ = symbols.q_;
    let x_ = symbols.x_;
    (d__ + e__ * x_).pow(p_) * (f__ + g__ * x_).pow(q_) * (a__ + b__ * (c__ * x_).asin()).pow(n_)
}

#[inline(never)]
fn rubi_shared_pattern_2(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (d__ + e__ * x_.pow(2)).pow(p_) * (a__ + b__ * (c__ * x_).acos())
}

#[inline(never)]
fn rubi_shared_pattern_3(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (d__ + e__ * x_.pow(2)).pow(p_) * (a__ + b__ * (c__ * x_).acos()).pow(n_)
}

#[inline(never)]
fn rubi_shared_pattern_4(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (d__ + e__ * x_.pow(2)).pow(p_) * (a__ + b__ * (c__ * x_).asin())
}

#[inline(never)]
fn rubi_shared_pattern_5(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (d__ + e__ * x_.pow(2)).pow(p_) * (a__ + b__ * (c__ * x_).asin()).pow(n_)
}
