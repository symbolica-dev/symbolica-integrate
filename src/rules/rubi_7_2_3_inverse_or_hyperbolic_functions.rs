use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_6304(rules);
    // Block 2 is disabled in the Rubi source embedded in docs/rubi_pdf_rules.md.

    push_rules_rule_6305(rules);
    push_rules_rule_6306(rules);
    push_rules_rule_6307(rules);
    push_rules_rule_6308(rules);
    push_rules_rule_6309(rules);
    push_block_6_to_9(rules);
    push_block_10_to_16(rules);
}

fn push_rules_rule_6304(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d1__, e1__, d2__, e2__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6304,
        source: "Int[(d1_+e1_.*x_)^p_.*(d2_+e2_.*x_)^p_.*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
          Int[(d1*d2+e1*e2*x^2)^p*(a+b*ArcCosh[c*x])^n,x] /;
        FreeQ[{a,b,c,d1,e1,d2,e2,n},x] && EqQ[d2*e1+d1*e2,0] && IntegerQ[p]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [d1__, e1__, p_, d2__, e2__, a__, b__, c__, n_, x_],
        optional: [e1__, e2__, a__, b__, c__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d1__, e1__, d2__, e2__, n_], x_)
                && eqq!(&d2__ * &e1__ + &d1__ * &e2__, 0)
                && integerq!(p_)
        },
        rhs: {
            let transformed =
                (&d1__ * &d2__ + &e1__ * &e2__ * x_.pow(2)).pow(&p_) * (&a__ + &b__ * (&c__ * x_).acosh()).pow(&n_);
            rubi_rhs_int(&transformed, x_)
        },
    ));
}

fn push_rules_rule_6305(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 6305,
        source: "Int[1/(Sqrt[d_+e_.*x_^2]*(a_.+b_.*ArcCosh[c_.*x_])),x_Symbol] :=
          1/(b*c)*Simp[Sqrt[1+c*x]*Sqrt[-1+c*x]/Sqrt[d+e*x^2]]*Log[a+b*ArcCosh[c*x]] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0]",
        desc: "Piecewise constant extraction and integration by substitution",
        refs: [],
        pattern: Atom::num(1) / ((d__ + e__ * x_.pow(2)).sqrt() * (a__ + b__ * (c__ * x_).acosh())),
        with: [d__, e__, a__, b__, c__, x_],
        optional: [e__, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_) && eqq!(c__.pow(2) * &d__ + &e__, 0)
        },
        rhs: {
            let ratio = ((Atom::num(1) + &c__ * x_).sqrt() * (-Atom::num(1) + &c__ * x_).sqrt())
                / (&d__ + &e__ * x_.pow(2)).sqrt();
            let argument = &a__ + &b__ * (&c__ * x_).acosh();
            rubi_simp(&(rubi_simp(&ratio, x_) * argument.log() / (&b__ * &c__)), x_)
        },
    ));
}

fn push_rules_rule_6306(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d1__, e1__, d2__, e2__, x_);
    rules.push(rubi_rule!(
        order: 6306,
        source: "Int[1/(Sqrt[d1_+e1_.*x_]*Sqrt[d2_+e2_.*x_]*(a_.+b_.*ArcCosh[c_.*x_])),x_Symbol] :=
          1/(b*c)*Simp[Sqrt[1+c*x]/Sqrt[d1+e1*x]]*Simp[Sqrt[-1+c*x]/Sqrt[d2+e2*x]]*Log[a+b*ArcCosh[c*x]] /;
        FreeQ[{a,b,c,d1,e1,d2,e2},x] && EqQ[e1,c*d1] && EqQ[e2,-c*d2]",
        desc: "Piecewise constant extraction and integration by substitution",
        refs: [],
        pattern: Atom::num(1) / ((d1__ + e1__ * x_).sqrt() * (d2__ + e2__ * x_).sqrt() * (a__ + b__ * (c__ * x_).acosh())),
        with: [d1__, e1__, d2__, e2__, a__, b__, c__, x_],
        optional: [e1__, e2__, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d1__, e1__, d2__, e2__], x_)
                && eqq!(e1__, &c__ * &d1__)
                && eqq!(e2__, -&c__ * &d2__)
        },
        rhs: {
            let ratio1 = (Atom::num(1) + &c__ * x_).sqrt() / (&d1__ + &e1__ * x_).sqrt();
            let ratio2 = (-Atom::num(1) + &c__ * x_).sqrt() / (&d2__ + &e2__ * x_).sqrt();
            let argument = &a__ + &b__ * (&c__ * x_).acosh();
            rubi_simp(&(rubi_simp(&ratio1, x_) * rubi_simp(&ratio2, x_) * argument.log() / (&b__ * &c__)), x_)
        },
    ));
}

fn push_rules_rule_6307(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 6307,
        source: "Int[(a_.+b_.*ArcCosh[c_.*x_])^n_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
          1/(b*c*(n+1))*Simp[Sqrt[1+c*x]*Sqrt[-1+c*x]/Sqrt[d+e*x^2]]*(a+b*ArcCosh[c*x])^(n+1) /;
        FreeQ[{a,b,c,d,e,n},x] && EqQ[c^2*d+e,0] && NeQ[n,-1]",
        desc: "Piecewise constant extraction and integration by substitution",
        refs: [],
        pattern: (a__ + b__ * (c__ * x_).acosh()).pow(n_) / (d__ + e__ * x_.pow(2)).sqrt(),
        with: [a__, b__, c__, n_, d__, e__, x_],
        optional: [a__, b__, c__, e__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, n_], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && neq!(n_, -1)
        },
        rhs: {
            let ratio = ((Atom::num(1) + &c__ * x_).sqrt() * (-Atom::num(1) + &c__ * x_).sqrt())
                / (&d__ + &e__ * x_.pow(2)).sqrt();
            let argument = &a__ + &b__ * (&c__ * x_).acosh();
            rubi_simp(&(rubi_simp(&ratio, x_) * argument.pow(&n_ + Atom::num(1)) / (&b__ * &c__ * (&n_ + Atom::num(1)))), x_)
        },
    ));
}

fn push_rules_rule_6308(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d1__, e1__, d2__, e2__, n_, x_);
    rules.push(rubi_rule!(
        order: 6308,
        source: "Int[(a_.+b_.*ArcCosh[c_.*x_])^n_./(Sqrt[d1_+e1_.*x_]*Sqrt[d2_+e2_.*x_]),x_Symbol] :=
          1/(b*c*(n+1))*Simp[Sqrt[1+c*x]/Sqrt[d1+e1*x]]*Simp[Sqrt[-1+c*x]/Sqrt[d2+e2*x]]*(a+b*ArcCosh[c*x])^(n+1) /;
        FreeQ[{a,b,c,d1,e1,d2,e2,n},x] && EqQ[e1,c*d1] && EqQ[e2,-c*d2] && NeQ[n,-1]",
        desc: "Piecewise constant extraction and integration by substitution",
        refs: [],
        pattern: (a__ + b__ * (c__ * x_).acosh()).pow(n_) / ((d1__ + e1__ * x_).sqrt() * (d2__ + e2__ * x_).sqrt()),
        with: [a__, b__, c__, n_, d1__, e1__, d2__, e2__, x_],
        optional: [a__, b__, c__, e1__, e2__, n_],
        when: {
            freeq!([a__, b__, c__, d1__, e1__, d2__, e2__, n_], x_)
                && eqq!(e1__, &c__ * &d1__)
                && eqq!(e2__, -&c__ * &d2__)
                && neq!(n_, -1)
        },
        rhs: {
            let ratio1 = (Atom::num(1) + &c__ * x_).sqrt() / (&d1__ + &e1__ * x_).sqrt();
            let ratio2 = (-Atom::num(1) + &c__ * x_).sqrt() / (&d2__ + &e2__ * x_).sqrt();
            let argument = &a__ + &b__ * (&c__ * x_).acosh();
            rubi_simp(&(rubi_simp(&ratio1, x_) * rubi_simp(&ratio2, x_) * argument.pow(&n_ + Atom::num(1)) / (&b__ * &c__ * (&n_ + Atom::num(1)))), x_)
        },
    ));
}

fn push_rules_rule_6309(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, p_, x_);
    rules.push(rubi_rule!(
        order: 6309,
        source: "Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCosh[c_.*x_]),x_Symbol] :=
          With[{u=IntHide[(d+e*x^2)^p,x]},
          (a+b*ArcCosh[c*x]) \\[Star] u - b*c \\[Star] Int[SimplifyIntegrand[u/(Sqrt[1+c*x]*Sqrt[-1+c*x]),x],x]] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && IGtQ[p,0]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [d__, e__, p_, a__, b__, c__, x_],
        optional: [e__, p_, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && igtq!(p_, 0)
        },
        rhs: {
            let argument = &a__ + &b__ * (&c__ * x_).acosh();
            let u = rubi_int_hide(&(&d__ + &e__ * x_.pow(2)).pow(&p_), x_).rubi_rhs();
            let recursive = rubi_simplify_integrand(
                &(&u / ((Atom::num(1) + &c__ * x_).sqrt() * (-Atom::num(1) + &c__ * x_).sqrt())),
                x_,
            );
            rubi_star(argument, u)
                    - rubi_star(&b__ * &c__, rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_block_6_to_9(rules: &mut Vec<RubiRule>) {
    push_rules_rule_6310(rules);
    push_rules_rule_6311(rules);
    push_rules_rule_6312(rules);
    push_rules_rule_6313(rules);
    push_rules_rule_6314(rules);
    push_rules_rule_6315(rules);
    push_rules_rule_6316(rules);
}

fn push_rules_rule_6310(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 6310,
        source: "Int[Sqrt[d_+e_.*x_^2]*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
          x*Sqrt[d+e*x^2]*(a+b*ArcCosh[c*x])^n/2 -
          b*c*n/2*Simp[Sqrt[d+e*x^2]/(Sqrt[1+c*x]*Sqrt[-1+c*x])] \\[Star] Int[x*(a+b*ArcCosh[c*x])^(n-1),x] -
          1/2*Simp[Sqrt[d+e*x^2]/(Sqrt[1+c*x]*Sqrt[-1+c*x])] \\[Star] Int[(a+b*ArcCosh[c*x])^n/(Sqrt[1+c*x]*Sqrt[-1+c*x]),x] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && GtQ[n,0]",
        desc: "Inverted integration by parts",
        refs: [],
        pattern: (d__ + e__ * x_.pow(2)).sqrt() * (a__ + b__ * (c__ * x_).acosh()).pow(n_),
        with: [d__, e__, a__, b__, c__, n_, x_],
        optional: [e__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && gtq!(n_, 0)
        },
        rhs: {
            let quadratic_x = &d__ + &e__ * x_.pow(2);
            let sqrt_pair = (Atom::num(1) + &c__ * x_).sqrt() * (-Atom::num(1) + &c__ * x_).sqrt();
            let argument = &a__ + &b__ * (&c__ * x_).acosh();
            let ratio_1 = rubi_simp(&(&quadratic_x.sqrt() / &sqrt_pair), x_);
            let ratio_2 = rubi_simp(&(quadratic_x.sqrt() / &sqrt_pair), x_);
            let recursive_1 = x_ * argument.pow(&n_ - Atom::num(1));
            let recursive_2 = argument.pow(&n_) / sqrt_pair;
            rubi_simp(&(x_ * quadratic_x.sqrt() * argument.pow(&n_) / 2), x_)
                    - rubi_star(&b__ * &c__ * &n_ / 2 * ratio_1, rubi_rhs_int(&recursive_1, x_))
                    - rubi_star(ratio_2 / 2, rubi_rhs_int(&recursive_2, x_))
        },
    ));
}

fn push_rules_rule_6311(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d1__, e1__, d2__, e2__, n_, x_);
    rules.push(rubi_rule!(
        order: 6311,
        source: "Int[Sqrt[d1_+e1_.*x_]*Sqrt[d2_+e2_.*x_]*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
          x*Sqrt[d1+e1*x]*Sqrt[d2+e2*x]*(a+b*ArcCosh[c*x])^n/2 -
          b*c*n/2*Simp[Sqrt[d1+e1*x]/Sqrt[1+c*x]]*Simp[Sqrt[d2+e2*x]/Sqrt[-1+c*x]] \\[Star]
            Int[x*(a+b*ArcCosh[c*x])^(n-1),x] -
          1/2*Simp[Sqrt[d1+e1*x]/Sqrt[1+c*x]]*Simp[Sqrt[d2+e2*x]/Sqrt[-1+c*x]] \\[Star]
            Int[(a+b*ArcCosh[c*x])^n/(Sqrt[1+c*x]*Sqrt[-1+c*x]),x] /;
        FreeQ[{a,b,c,d1,e1,d2,e2},x] && EqQ[e1,c*d1] && EqQ[e2,-c*d2] && GtQ[n,0]",
        desc: "Inverted integration by parts",
        refs: [],
        pattern: (d1__ + e1__ * x_).sqrt() * (d2__ + e2__ * x_).sqrt() * (a__ + b__ * (c__ * x_).acosh()).pow(n_),
        with: [d1__, e1__, d2__, e2__, a__, b__, c__, n_, x_],
        optional: [e1__, e2__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d1__, e1__, d2__, e2__], x_)
                && eqq!(e1__, &c__ * &d1__)
                && eqq!(e2__, -&c__ * &d2__)
                && gtq!(n_, 0)
        },
        rhs: {
            let l1 = &d1__ + &e1__ * x_;
            let l2 = &d2__ + &e2__ * x_;
            let argument = &a__ + &b__ * (&c__ * x_).acosh();
            let ratio_1 =
                rubi_simp(&(l1.sqrt() / (Atom::num(1) + &c__ * x_).sqrt()), x_)
                    * rubi_simp(&(l2.sqrt() / (-Atom::num(1) + &c__ * x_).sqrt()), x_);
            let ratio_2 =
                rubi_simp(&(l1.sqrt() / (Atom::num(1) + &c__ * x_).sqrt()), x_)
                    * rubi_simp(&(l2.sqrt() / (-Atom::num(1) + &c__ * x_).sqrt()), x_);
            let recursive_1 = x_ * argument.pow(&n_ - Atom::num(1));
            let recursive_2 = argument.pow(&n_)
                / ((Atom::num(1) + &c__ * x_).sqrt() * (-Atom::num(1) + &c__ * x_).sqrt());
            rubi_simp(&(x_ * l1.sqrt() * l2.sqrt() * argument.pow(&n_) / 2), x_)
                    - rubi_star(&b__ * &c__ * &n_ / 2 * ratio_1, rubi_rhs_int(&recursive_1, x_))
                    - rubi_star(ratio_2 / 2, rubi_rhs_int(&recursive_2, x_))
        },
    ));
}

fn push_rules_rule_6312(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6312,
        source: "Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
          x*(d+e*x^2)^p*(a+b*ArcCosh[c*x])^n/(2*p+1) +
          2*d*p/(2*p+1) \\[Star] Int[(d+e*x^2)^(p-1)*(a+b*ArcCosh[c*x])^n,x] -
          b*c*n/(2*p+1)*Simp[(d+e*x^2)^p/((1+c*x)^p*(-1+c*x)^p)] \\[Star]
            Int[x*(1+c*x)^(p-1/2)*(-1+c*x)^(p-1/2)*(a+b*ArcCosh[c*x])^(n-1),x] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && GtQ[n,0] && GtQ[p,0]",
        desc: "Inverted integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [e__, p_, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && gtq!(n_, 0)
                && gtq!(p_, 0)
        },
        rhs: {
            let quadratic = &d__ + &e__ * x_.pow(2);
            let unit1 = Atom::num(1) + &c__ * x_;
            let unit2 = -Atom::num(1) + &c__ * x_;
            let argument = &a__ + &b__ * (&c__ * x_).acosh();
            let recursive_1 = quadratic.pow(&p_ - Atom::num(1))
                * argument.pow(&n_);
            let recursive_2 = x_
                * unit1

                    .pow(&p_ - Atom::num(1) / Atom::num(2))
                * unit2

                    .pow(&p_ - Atom::num(1) / Atom::num(2))
                * argument.pow(&n_ - Atom::num(1));
            let denominator = Atom::num(2) * &p_ + Atom::num(1);
            let ratio = rubi_simp(
                &(quadratic.pow(&p_) / (unit1.pow(&p_) * unit2.pow(&p_))),
                x_,
            );
            rubi_simp(&(x_ * quadratic.pow(&p_) * argument.pow(&n_) / &denominator), x_)
                    + rubi_star(Atom::num(2) * &d__ * &p_ / &denominator, rubi_rhs_int(&recursive_1, x_))
                    - rubi_star(&b__ * &c__ * &n_ / &denominator * ratio, rubi_rhs_int(&recursive_2, x_))
        },
    ));
}

fn push_rules_rule_6313(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d1__, e1__, d2__, e2__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6313,
        source: "Int[(d1_+e1_.*x_)^p_.*(d2_+e2_.*x_)^p_.*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
          x*(d1+e1*x)^p*(d2+e2*x)^p*(a+b*ArcCosh[c*x])^n/(2*p+1) +
          2*d1*d2*p/(2*p+1) \\[Star] Int[(d1+e1*x)^(p-1)*(d2+e2*x)^(p-1)*(a+b*ArcCosh[c*x])^n,x] -
          b*c*n/(2*p+1)*Simp[(d1+e1*x)^p/(1+c*x)^p]*Simp[(d2+e2*x)^p/(-1+c*x)^p] \\[Star]
            Int[x*(1+c*x)^(p-1/2)*(-1+c*x)^(p-1/2)*(a+b*ArcCosh[c*x])^(n-1),x] /;
        FreeQ[{a,b,c,d1,e1,d2,e2},x] && EqQ[e1,c*d1] && EqQ[e2,-c*d2] && GtQ[n,0] && GtQ[p,0]",
        desc: "Inverted integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [d1__, e1__, p_, d2__, e2__, a__, b__, c__, n_, x_],
        optional: [e1__, e2__, a__, b__, c__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d1__, e1__, d2__, e2__], x_)
                && eqq!(e1__, &c__ * &d1__)
                && eqq!(e2__, -&c__ * &d2__)
                && gtq!(n_, 0)
                && gtq!(p_, 0)
        },
        rhs: {
            let l1 = &d1__ + &e1__ * x_;
            let l2 = &d2__ + &e2__ * x_;
            let unit1 = Atom::num(1) + &c__ * x_;
            let unit2 = -Atom::num(1) + &c__ * x_;
            let argument = &a__ + &b__ * (&c__ * x_).acosh();
            let recursive_1 = l1.pow(&p_ - Atom::num(1))
                * l2.pow(&p_ - Atom::num(1))
                * argument.pow(&n_);
            let recursive_2 = x_
                * unit1

                    .pow(&p_ - Atom::num(1) / Atom::num(2))
                * unit2

                    .pow(&p_ - Atom::num(1) / Atom::num(2))
                * argument.pow(&n_ - Atom::num(1));
            let denominator = Atom::num(2) * &p_ + Atom::num(1);
            let ratio = rubi_simp(&(l1.pow(&p_) / unit1.pow(&p_)), x_)
                * rubi_simp(&(l2.pow(&p_) / unit2.pow(&p_)), x_);
            rubi_simp(&(x_ * l1.pow(&p_) * l2.pow(&p_) * argument.pow(&n_) / &denominator), x_)
                    + rubi_star(Atom::num(2) * &d1__ * &d2__ * &p_ / &denominator, rubi_rhs_int(&recursive_1, x_))
                    - rubi_star(&b__ * &c__ * &n_ / &denominator * ratio, rubi_rhs_int(&recursive_2, x_))
        },
    ));
}

fn push_rules_rule_6314(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 6314,
        source: "Int[(a_.+b_.*ArcCosh[c_.*x_])^n_./(d_+e_.*x_^2)^(3/2),x_Symbol] :=
          x*(a+b*ArcCosh[c*x])^n/(d*Sqrt[d+e*x^2]) +
          b*c*n/d*Simp[Sqrt[1+c*x]*Sqrt[-1+c*x]/Sqrt[d+e*x^2]] \\[Star] Int[x*(a+b*ArcCosh[c*x])^(n-1)/(1-c^2*x^2),x] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && GtQ[n,0]",
        desc: "Integration by parts and piecewise constant extraction",
        refs: [],
        pattern: (a__ + b__ * (c__ * x_).acosh()).pow(n_) / (d__ + e__ * x_.pow(2)).pow(Atom::num(3) / Atom::num(2)),
        with: [a__, b__, c__, n_, d__, e__, x_],
        optional: [a__, b__, c__, n_, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && gtq!(n_, 0)
        },
        rhs: {
            let quadratic_x = &d__ + &e__ * x_.pow(2);
            let sqrt_pair = (Atom::num(1) + &c__ * x_).sqrt() * (-Atom::num(1) + &c__ * x_).sqrt();
            let argument = &a__ + &b__ * (&c__ * x_).acosh();
            let recursive = x_ * argument.pow(&n_ - Atom::num(1)) / (Atom::num(1) - c__.pow(2) * x_.pow(2));
            rubi_simp(&(x_ * argument.pow(&n_) / (&d__ * quadratic_x.sqrt())), x_)
                    + rubi_star(&b__ * &c__ * &n_ / &d__
                            * rubi_simp(&(sqrt_pair / quadratic_x.sqrt()), x_), rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_6315(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d1__, e1__, d2__, e2__, n_, x_);
    rules.push(rubi_rule!(
        order: 6315,
        source: "Int[(a_.+b_.*ArcCosh[c_.*x_])^n_./((d1_+e1_.*x_)^(3/2)*(d2_+e2_.*x_)^(3/2)),x_Symbol] :=
          x*(a+b*ArcCosh[c*x])^n/(d1*d2*Sqrt[d1+e1*x]*Sqrt[d2+e2*x]) +
          b*c*n/(d1*d2)*Simp[Sqrt[1+c*x]/Sqrt[d1+e1*x]]*Simp[Sqrt[-1+c*x]/Sqrt[d2+e2*x]] \\[Star]
            Int[x*(a+b*ArcCosh[c*x])^(n-1)/(1-c^2*x^2),x] /;
        FreeQ[{a,b,c,d1,e1,d2,e2},x] && EqQ[e1,c*d1] && EqQ[e2,-c*d2] && GtQ[n,0]",
        desc: "Integration by parts and piecewise constant extraction",
        refs: [],
        pattern: (a__ + b__ * (c__ * x_).acosh()).pow(n_) / ((d1__ + e1__ * x_).pow(Atom::num(3) / Atom::num(2)) * (d2__ + e2__ * x_).pow(Atom::num(3) / Atom::num(2))),
        with: [a__, b__, c__, n_, d1__, e1__, d2__, e2__, x_],
        optional: [a__, b__, c__, n_, e1__, e2__],
        when: {
            freeq!([a__, b__, c__, d1__, e1__, d2__, e2__], x_)
                && eqq!(e1__, &c__ * &d1__)
                && eqq!(e2__, -&c__ * &d2__)
                && gtq!(n_, 0)
        },
        rhs: {
            let l1 = &d1__ + &e1__ * x_;
            let l2 = &d2__ + &e2__ * x_;
            let argument = &a__ + &b__ * (&c__ * x_).acosh();
            let ratio =
                rubi_simp(&((Atom::num(1) + &c__ * x_).sqrt() / l1.sqrt()), x_)
                    * rubi_simp(&((-Atom::num(1) + &c__ * x_).sqrt() / l2.sqrt()), x_);
            let recursive = x_ * argument.pow(&n_ - Atom::num(1)) / (Atom::num(1) - c__.pow(2) * x_.pow(2));
            rubi_simp(&(x_ * argument.pow(&n_) / (&d1__ * &d2__ * l1.sqrt() * l2.sqrt())), x_)
                    + rubi_star(&b__ * &c__ * &n_ / (&d1__ * &d2__) * ratio, rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_6316(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6316,
        source: "Int[(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
          -x*(d+e*x^2)^(p+1)*(a+b*ArcCosh[c*x])^n/(2*d*(p+1)) +
          (2*p+3)/(2*d*(p+1)) \\[Star] Int[(d+e*x^2)^(p+1)*(a+b*ArcCosh[c*x])^n,x] -
          b*c*n/(2*(p+1))*Simp[(d+e*x^2)^p/((1+c*x)^p*(-1+c*x)^p)] \\[Star]
            Int[x*(1+c*x)^(p+1/2)*(-1+c*x)^(p+1/2)*(a+b*ArcCosh[c*x])^(n-1),x] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && GtQ[n,0] && LtQ[p,-1] && NeQ[p,-3/2]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [e__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && gtq!(n_, 0)
                && ltq!(p_, -1)
                && neq!(p_, -(Atom::num(3) / Atom::num(2)))
        },
        rhs: {
            let quadratic = &d__ + &e__ * x_.pow(2);
            let unit1 = Atom::num(1) + &c__ * x_;
            let unit2 = -Atom::num(1) + &c__ * x_;
            let argument = &a__ + &b__ * (&c__ * x_).acosh();
            let recursive_1 = quadratic.pow(&p_ + Atom::num(1))
                * argument.pow(&n_);
            let recursive_2 = x_
                * unit1

                    .pow(&p_ + Atom::num(1) / Atom::num(2))
                * unit2

                    .pow(&p_ + Atom::num(1) / Atom::num(2))
                * argument.pow(&n_ - Atom::num(1));
            let ratio = rubi_simp(
                &(quadratic.pow(&p_) / (unit1.pow(&p_) * unit2.pow(&p_))),
                x_,
            );
            rubi_simp(&(Atom::num(-1) * x_
                    * quadratic.pow(&p_ + Atom::num(1))
                    * argument.pow(&n_)
                    / (Atom::num(2) * &d__ * (&p_ + Atom::num(1)))), x_)
                    + rubi_star((Atom::num(2) * &p_ + Atom::num(3))
                            / (Atom::num(2) * &d__ * (&p_ + Atom::num(1))), rubi_rhs_int(&recursive_1, x_))
                    - rubi_star(&b__ * &c__ * &n_ / (Atom::num(2) * (&p_ + Atom::num(1)))
                            * ratio, rubi_rhs_int(&recursive_2, x_))
        },
    ));
}

fn push_block_10_to_16(rules: &mut Vec<RubiRule>) {
    push_rules_rule_6317(rules);
    push_rules_rule_6318(rules);
    push_rules_rule_6319(rules);
    push_rules_rule_6320(rules);
    push_rules_rule_6321(rules);
    push_rules_rule_6322(rules);
    push_rules_rule_6323(rules);
    // Block 14 is disabled in the Rubi source embedded in docs/rubi_pdf_rules.md.

    push_rules_rule_6324(rules);
    push_rules_rule_6325(rules);
    push_rules_rule_6326(rules);
}

fn push_rules_rule_6317(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d1__, e1__, d2__, e2__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6317,
        source: "Int[(d1_+e1_.*x_)^p_*(d2_+e2_.*x_)^p_*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
          -x*(d1+e1*x)^(p+1)*(d2+e2*x)^(p+1)*(a+b*ArcCosh[c*x])^n/(2*d1*d2*(p+1)) +
          (2*p+3)/(2*d1*d2*(p+1)) \\[Star] Int[(d1+e1*x)^(p+1)*(d2+e2*x)^(p+1)*(a+b*ArcCosh[c*x])^n,x] -
          b*c*n/(2*(p+1))*Simp[(d1+e1*x)^p/(1+c*x)^p]*Simp[(d2+e2*x)^p/(-1+c*x)^p] \\[Star]
            Int[x*(1+c*x)^(p+1/2)*(-1+c*x)^(p+1/2)*(a+b*ArcCosh[c*x])^(n-1),x] /;
        FreeQ[{a,b,c,d1,e1,d2,e2},x] && EqQ[e1,c*d1] && EqQ[e2,-c*d2] && GtQ[n,0] && LtQ[p,-1] && NeQ[p,-3/2]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [d1__, e1__, p_, d2__, e2__, a__, b__, c__, n_, x_],
        optional: [e1__, e2__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d1__, e1__, d2__, e2__], x_)
                && eqq!(e1__, &c__ * &d1__)
                && eqq!(e2__, -&c__ * &d2__)
                && gtq!(n_, 0)
                && ltq!(p_, -1)
                && neq!(p_, -(Atom::num(3) / Atom::num(2)))
        },
        rhs: {
            let l1 = &d1__ + &e1__ * x_;
            let l2 = &d2__ + &e2__ * x_;
            let unit1 = Atom::num(1) + &c__ * x_;
            let unit2 = -Atom::num(1) + &c__ * x_;
            let argument = &a__ + &b__ * (&c__ * x_).acosh();
            let recursive_1 = l1.pow(&p_ + Atom::num(1))
                * l2.pow(&p_ + Atom::num(1))
                * argument.pow(&n_);
            let recursive_2 = x_
                * unit1

                    .pow(&p_ + Atom::num(1) / Atom::num(2))
                * unit2

                    .pow(&p_ + Atom::num(1) / Atom::num(2))
                * argument.pow(&n_ - Atom::num(1));
            let ratio = rubi_simp(&(l1.pow(&p_) / unit1.pow(&p_)), x_)
                * rubi_simp(&(l2.pow(&p_) / unit2.pow(&p_)), x_);
            rubi_simp(&(Atom::num(-1) * x_
                    * l1.pow(&p_ + Atom::num(1))
                    * l2.pow(&p_ + Atom::num(1))
                    * argument.pow(&n_)
                    / (Atom::num(2) * &d1__ * &d2__ * (&p_ + Atom::num(1)))), x_)
                    + rubi_star((Atom::num(2) * &p_ + Atom::num(3))
                            / (Atom::num(2) * &d1__ * &d2__ * (&p_ + Atom::num(1))), rubi_rhs_int(&recursive_1, x_))
                    - rubi_star(&b__ * &c__ * &n_ / (Atom::num(2) * (&p_ + Atom::num(1)))
                            * ratio, rubi_rhs_int(&recursive_2, x_))
        },
    ));
}

fn push_rules_rule_6318(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 6318,
        source: "Int[(a_.+b_.*ArcCosh[c_.*x_])^n_./(d_+e_.*x_^2),x_Symbol] :=
          -1/(c*d) \\[Star] Subst[Int[(a+b*x)^n*Csch[x],x],x,ArcCosh[c*x]] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && IGtQ[n,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (a__ + b__ * (c__ * x_).acosh()).pow(n_) / (d__ + e__ * x_.pow(2)),
        with: [a__, b__, c__, n_, d__, e__, x_],
        optional: [a__, b__, c__, n_, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && igtq!(n_, 0)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let payload = (&a__ + &b__ * &sub_atom).pow(&n_) * sub_atom.csch();
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            let substituted = rubi_subst(&primitive, substitution_symbol, (&c__ * x_).acosh());
            rubi_star(-Atom::num(1) / (&c__ * &d__), substituted)
        },
    ));
}

fn push_rules_rule_6319(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6319,
        source: "Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCosh[c_.*x_])^n_,x_Symbol] :=
          Simp[Sqrt[1+c*x]*Sqrt[-1+c*x]*(d+e*x^2)^p]*(a+b*ArcCosh[c*x])^(n+1)/(b*c*(n+1)) -
          c*(2*p+1)/(b*(n+1))*Simp[(d+e*x^2)^p/((1+c*x)^p*(-1+c*x)^p)] \\[Star]
            Int[x*(1+c*x)^(p-1/2)*(-1+c*x)^(p-1/2)*(a+b*ArcCosh[c*x])^(n+1),x] /;
        FreeQ[{a,b,c,d,e,p},x] && EqQ[c^2*d+e,0] && LtQ[n,-1] && IntegerQ[2*p]",
        desc: "Integration by parts and piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [e__, a__, b__, c__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, p_], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && ltq!(n_, -1)
                && integerq!(Atom::num(2) * &p_)
        },
        rhs: {
            let quadratic_x = &d__ + &e__ * x_.pow(2);
            let unit1 = Atom::num(1) + &c__ * x_;
            let unit2 = -Atom::num(1) + &c__ * x_;
            let argument = &a__ + &b__ * (&c__ * x_).acosh();
            let first = rubi_simp(&(unit1.sqrt() * unit2.sqrt() * quadratic_x.pow(&p_)), x_)
                * argument.pow(&n_ + Atom::num(1))
                / (&b__ * &c__ * (&n_ + Atom::num(1)));
            let recursive = x_ * unit1.pow(&p_ - Atom::num(1) / Atom::num(2))
                * unit2.pow(&p_ - Atom::num(1) / Atom::num(2))
                * argument.pow(&n_ + Atom::num(1));
            rubi_simp(&(first), x_)
                    - rubi_star(&c__ * (Atom::num(2) * &p_ + 1)
                            / (&b__ * (&n_ + Atom::num(1)))
                            * rubi_simp(
                                &(quadratic_x.pow(&p_)
                                    / (unit1.pow(&p_) * unit2.pow(&p_))),
                                x_,
                            ), rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_6320(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d1__, e1__, d2__, e2__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6320,
        source: "Int[(d1_+e1_.*x_)^p_.*(d2_+e2_.*x_)^p_.*(a_.+b_.*ArcCosh[c_.*x_])^n_,x_Symbol] :=
          Sqrt[1+c*x]*Sqrt[-1+c*x]*(d1+e1*x)^p*(d2+e2*x)^p*(a+b*ArcCosh[c*x])^(n+1)/(b*c*(n+1)) -
          c*(2*p+1)/(b*(n+1))*Simp[(d1+e1*x)^p/(1+c*x)^p]*Simp[(d2+e2*x)^p/(-1+c*x)^p] \\[Star]
            Int[x*(-1+c^2*x^2)^(p-1/2)*(a+b*ArcCosh[c*x])^(n+1),x] /;
        FreeQ[{a,b,c,d1,e1,d2,e2,p},x] && EqQ[e1,c*d1] && EqQ[e2,-c*d2] && LtQ[n,-1] && IntegerQ[p+1/2]",
        desc: "Integration by parts and piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [d1__, e1__, p_, d2__, e2__, a__, b__, c__, n_, x_],
        optional: [e1__, e2__, a__, b__, c__, p_],
        when: {
            freeq!([a__, b__, c__, d1__, e1__, d2__, e2__, p_], x_)
                && eqq!(e1__, &c__ * &d1__)
                && eqq!(e2__, -&c__ * &d2__)
                && ltq!(n_, -1)
                && integerq!(&p_ + Atom::num(1) / Atom::num(2))
        },
        rhs: {
            let l1 = &d1__ + &e1__ * x_;
            let l2 = &d2__ + &e2__ * x_;
            let unit1 = Atom::num(1) + &c__ * x_;
            let unit2 = -Atom::num(1) + &c__ * x_;
            let argument = &a__ + &b__ * (&c__ * x_).acosh();
            let first = unit1.sqrt()
                * unit2.sqrt()
                * l1.pow(&p_)
                * l2.pow(&p_)
                * argument.pow(&n_ + Atom::num(1))
                / (&b__ * &c__ * (&n_ + Atom::num(1)));
            let recursive = x_
                * (-Atom::num(1) + c__.pow(2) * x_.pow(2)).pow(&p_ - Atom::num(1) / Atom::num(2))
                * argument.pow(&n_ + Atom::num(1));
            rubi_simp(&(first), x_)
                    - rubi_star(&c__ * (Atom::num(2) * &p_ + 1)
                            / (&b__ * (&n_ + Atom::num(1)))
                            * rubi_simp(&(l1.pow(&p_) / unit1.pow(&p_)), x_)
                            * rubi_simp(&(l2.pow(&p_) / unit2.pow(&p_)), x_), rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_6321(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6321,
        source: "Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
          1/(b*c)*Simp[(d+e*x^2)^p/((1+c*x)^p*(-1+c*x)^p)] \\[Star] Subst[Int[x^n*Sinh[-a/b+x/b]^(2*p+1),x],x,a+b*ArcCosh[c*x]] /;
        FreeQ[{a,b,c,d,e,n},x] && EqQ[c^2*d+e,0] && IGtQ[2*p,0]",
        desc: "Piecewise constant extraction and integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [e__, a__, b__, c__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, n_], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && igtq!(Atom::num(2) * &p_, 0)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let hyperbolic_argument = -&a__ / &b__ + &sub_atom / &b__;
            let payload = sub_atom.pow(&n_)
                * hyperbolic_argument
                    .sinh()
                    .pow(Atom::num(2) * &p_ + Atom::num(1));
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            let substituted = rubi_subst(
                &primitive,
                substitution_symbol,
                &a__ + &b__ * (&c__ * x_).acosh(),
            );
            let quadratic = &d__ + &e__ * x_.pow(2);
            let unit1 = Atom::num(1) + &c__ * x_;
            let unit2 = -Atom::num(1) + &c__ * x_;
            let coefficient = Atom::num(1) / (&b__ * &c__)
                * rubi_simp(
                    &(quadratic.pow(&p_) / (unit1.pow(&p_) * unit2.pow(&p_))),
                    x_,
                );
            rubi_star(coefficient, substituted)
        },
    ));
}

fn push_rules_rule_6322(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d1__, e1__, d2__, e2__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6322,
        source: "Int[(d1_+e1_.*x_)^p_.*(d2_+e2_.*x_)^p_.*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
          1/(b*c)*Simp[(d1+e1*x)^p/(1+c*x)^p]*Simp[(d2+e2*x)^p/(-1+c*x)^p] \\[Star] Subst[Int[x^n*Sinh[-a/b+x/b]^(2*p+1),x],x,a+b*ArcCosh[c*x]] /;
        FreeQ[{a,b,c,d1,e1,d2,e2,n},x] && EqQ[e1,c*d1] && EqQ[e2,-c*d2] && IGtQ[2*p,0]",
        desc: "Piecewise constant extraction and integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [d1__, e1__, p_, d2__, e2__, a__, b__, c__, n_, x_],
        optional: [e1__, e2__, a__, b__, c__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d1__, e1__, d2__, e2__, n_], x_)
                && eqq!(e1__, &c__ * &d1__)
                && eqq!(e2__, -&c__ * &d2__)
                && igtq!(Atom::num(2) * &p_, 0)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let hyperbolic_argument = -&a__ / &b__ + &sub_atom / &b__;
            let payload = sub_atom.pow(&n_)
                * hyperbolic_argument
                    .sinh()
                    .pow(Atom::num(2) * &p_ + Atom::num(1));
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            let substituted = rubi_subst(
                &primitive,
                substitution_symbol,
                &a__ + &b__ * (&c__ * x_).acosh(),
            );
            let l1 = &d1__ + &e1__ * x_;
            let l2 = &d2__ + &e2__ * x_;
            let unit1 = Atom::num(1) + &c__ * x_;
            let unit2 = -Atom::num(1) + &c__ * x_;
            let coefficient = Atom::num(1) / (&b__ * &c__)
                * rubi_simp(&(l1.pow(&p_) / unit1.pow(&p_)), x_)
                * rubi_simp(&(l2.pow(&p_) / unit2.pow(&p_)), x_);
            rubi_star(coefficient, substituted)
        },
    ));
}

fn push_rules_rule_6323(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, p_, x_);
    rules.push(rubi_rule!(
        order: 6323,
        source: "Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCosh[c_.*x_]),x_Symbol] :=
          With[{u=IntHide[(d+e*x^2)^p,x]},
          (a+b*ArcCosh[c*x]) \\[Star] u - b*c \\[Star] Int[SimplifyIntegrand[u/(Sqrt[1+c*x]*Sqrt[-1+c*x]),x],x]] /;
        FreeQ[{a,b,c,d,e},x] && NeQ[c^2*d+e,0] && (IGtQ[p,0] || ILtQ[p+1/2,0])",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [d__, e__, p_, a__, b__, c__, x_],
        optional: [e__, p_, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && neq!(c__.pow(2) * &d__ + &e__, 0)
                && (igtq!(p_, 0) || iltq!(&p_ + Atom::num(1) / Atom::num(2), 0))
        },
        rhs: {
            let argument = &a__ + &b__ * (&c__ * x_).acosh();
            let u = rubi_int_hide(&(&d__ + &e__ * x_.pow(2)).pow(&p_), x_).rubi_rhs();
            let recursive = rubi_simplify_integrand(
                &(&u / ((Atom::num(1) + &c__ * x_).sqrt() * (-Atom::num(1) + &c__ * x_).sqrt())),
                x_,
            );
            rubi_star(argument, u)
                    - rubi_star(&b__ * &c__, rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_6324(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6324,
        source: "Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
          Int[ExpandIntegrand[(a+b*ArcCosh[c*x])^n,(d+e*x^2)^p,x],x] /;
        FreeQ[{a,b,c,d,e,n},x] && NeQ[c^2*d+e,0] && IntegerQ[p] && (p>0 || IGtQ[n,0])",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [e__, p_, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, n_], x_)
                && neq!(c__.pow(2) * &d__ + &e__, 0)
                && integerq!(p_)
                && (gtq!(p_, 0) || igtq!(n_, 0))
        },
        rhs: {
            let u = (&a__ + &b__ * (&c__ * x_).acosh()).pow(&n_);
            let v = (&d__ + &e__ * x_.pow(2)).pow(&p_);
            let expanded = rubi_expand_integrand_product(&u, &v, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_6325(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6325,
        source: "Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
          Unintegrable[(d+e*x^2)^p*(a+b*ArcCosh[c*x])^n,x] /;
        FreeQ[{a,b,c,d,e,n,p},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [e__, p_, a__, b__, c__, n_],
        when: { freeq!([a__, b__, c__, d__, e__, n_, p_], x_) },
        rhs: {
            let integrand = (&d__ + &e__ * x_.pow(2)).pow(&p_) * (&a__ + &b__ * (&c__ * x_).acosh()).pow(&n_);
            rubi_unintegrable(integrand, x_)
        },
    ));
}

fn push_rules_rule_6326(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d1__, e1__, d2__, e2__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6326,
        source: "Int[(d1_+e1_.*x_)^p_.*(d2_+e2_.*x_)^p_.*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
          Unintegrable[(d1+e1*x)^p*(d2+e2*x)^p*(a+b*ArcCosh[c*x])^n,x] /;
        FreeQ[{a,b,c,d1,e1,d2,e2,n,p},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [d1__, e1__, p_, d2__, e2__, a__, b__, c__, n_, x_],
        optional: [e1__, e2__, a__, b__, c__, n_, p_],
        when: { freeq!([a__, b__, c__, d1__, e1__, d2__, e2__, n_, p_], x_) },
        rhs: {
            let integrand = (&d1__ + &e1__ * x_).pow(&p_)
                * (&d2__ + &e2__ * x_).pow(&p_)
                * (&a__ + &b__ * (&c__ * x_).acosh()).pow(&n_);
            rubi_unintegrable(integrand, x_)
        },
    ));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn downvalues_6304_through_6326_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .collect::<Vec<_>>();
        assert_eq!(orders, (6304..=6326).collect::<Vec<_>>());
    }
}

// Generated shared pattern builders.

#[inline(never)]
fn rubi_shared_pattern_0(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d1__ = symbols.d1__;
    let d2__ = symbols.d2__;
    let e1__ = symbols.e1__;
    let e2__ = symbols.e2__;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (d1__ + e1__ * x_).pow(p_)
        * (d2__ + e2__ * x_).pow(p_)
        * (a__ + b__ * (c__ * x_).acosh()).pow(n_)
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (d__ + e__ * x_.pow(2)).pow(p_) * (a__ + b__ * (c__ * x_).acosh())
}

#[inline(never)]
fn rubi_shared_pattern_2(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (d__ + e__ * x_.pow(2)).pow(p_) * (a__ + b__ * (c__ * x_).acosh()).pow(n_)
}
