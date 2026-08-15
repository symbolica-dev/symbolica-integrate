use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_6197(rules);
    push_rules_rule_6198(rules);
    push_rules_rule_6199(rules);
    push_rules_rule_6200(rules);
    push_rules_rule_6201(rules);
    push_rules_rule_6202(rules);
    push_rules_rule_6203(rules);
    push_rules_rule_6204(rules);
    // Block 10 is disabled in the Rubi source embedded in docs/rubi_pdf_rules.md.

    push_rules_rule_6205(rules);
    push_rules_rule_6206(rules);
    push_rules_rule_6207(rules);
    push_rules_rule_6208(rules);
    push_rules_rule_6209(rules);
    push_rules_rule_6210(rules);
    push_rules_rule_6211(rules);
}

fn push_rules_rule_6197(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 6197,
        source: "Int[1/(Sqrt[d_+e_.*x_^2]*(a_.+b_.*ArcSinh[c_.*x_])),x_Symbol] :=
          1/(b*c)*Simp[Sqrt[1+c^2*x^2]/Sqrt[d+e*x^2]]*Log[a+b*ArcSinh[c*x]] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[e,c^2*d]",
        desc: "Piecewise constant extraction and integration by substitution",
        refs: [],
        pattern: Atom::num(1) / ((d__ + e__ * x_.pow(2)).sqrt() * (a__ + b__ * (c__ * x_).asinh())),
        with: [d__, e__, a__, b__, c__, x_],
        optional: [e__, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_) && eqq!(e__, c__.pow(2) * &d__)
        },
        rhs: {
            let ratio = (Atom::num(1) + c__.pow(2) * x_.pow(2)).sqrt()
                / (&d__ + &e__ * x_.pow(2)).sqrt();
            let argument = a__ + &b__ * (&c__ * x_).asinh();
            rubi_simp(&(rubi_simp(&ratio, x_) * argument.log() / (b__ * c__)), x_)
        },
    ));
}

fn push_rules_rule_6198(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 6198,
        source: "Int[(a_.+b_.*ArcSinh[c_.*x_])^n_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
          1/(b*c*(n+1))*Simp[Sqrt[1+c^2*x^2]/Sqrt[d+e*x^2]]*(a+b*ArcSinh[c*x])^(n+1) /;
        FreeQ[{a,b,c,d,e,n},x] && EqQ[e,c^2*d] && NeQ[n,-1]",
        desc: "Piecewise constant extraction and integration by substitution",
        refs: [],
        pattern: (a__ + b__ * (c__ * x_).asinh()).pow(n_) / (d__ + e__ * x_.pow(2)).sqrt(),
        with: [a__, b__, c__, n_, d__, e__, x_],
        optional: [a__, b__, c__, e__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, n_], x_)
                && eqq!(e__, c__.pow(2) * &d__)
                && neq!(n_, -1)
        },
        rhs: {
            let ratio = (Atom::num(1) + c__.pow(2) * x_.pow(2)).sqrt()
                / (&d__ + &e__ * x_.pow(2)).sqrt();
            let argument = a__ + &b__ * (&c__ * x_).asinh();
            rubi_simp(&(rubi_simp(&ratio, x_) * argument.pow(&n_ + Atom::num(1))
                    / (b__ * c__ * (n_ + Atom::num(1)))), x_)
        },
    ));
}

fn push_rules_rule_6199(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, p_, x_);
    rules.push(rubi_rule!(
        order: 6199,
        source: "Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSinh[c_.*x_]),x_Symbol] :=
          With[{u=IntHide[(d+e*x^2)^p,x]},
          (a+b*ArcSinh[c*x]) \\[Star] u - b*c \\[Star] Int[SimplifyIntegrand[u/Sqrt[1+c^2*x^2],x],x]] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[e,c^2*d] && IGtQ[p,0]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [d__, e__, p_, a__, b__, c__, x_],
        optional: [e__, a__, b__, c__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(e__, c__.pow(2) * &d__)
                && igtq!(p_, 0)
        },
        rhs: {
            let argument = &a__ + &b__ * (&c__ * x_).asinh();
            let u = rubi_int_hide(&(&d__ + &e__ * x_.pow(2)).pow(&p_), x_).rubi_rhs();
            let recursive_integrand = rubi_simplify_integrand(
                &(&u / (Atom::num(1) + c__.pow(2) * x_.pow(2)).sqrt()),
                x_,
            );
            rubi_star(argument, u)
                    - rubi_star(&b__ * &c__, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_6200(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 6200,
        source: "Int[Sqrt[d_+e_.*x_^2]*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
          x*Sqrt[d+e*x^2]*(a+b*ArcSinh[c*x])^n/2 -
          b*c*n/2*Simp[Sqrt[d+e*x^2]/Sqrt[1+c^2*x^2]] \\[Star] Int[x*(a+b*ArcSinh[c*x])^(n-1),x] +
          1/2*Simp[Sqrt[d+e*x^2]/Sqrt[1+c^2*x^2]] \\[Star] Int[(a+b*ArcSinh[c*x])^n/Sqrt[1+c^2*x^2],x] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[e,c^2*d] && GtQ[n,0]",
        desc: "Inverted integration by parts",
        refs: [],
        pattern: (d__ + e__ * x_.pow(2)).sqrt() * (a__ + b__ * (c__ * x_).asinh()).pow(n_),
        with: [d__, e__, a__, b__, c__, n_, x_],
        optional: [e__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(e__, c__.pow(2) * &d__)
                && gtq!(n_, 0)
        },
        rhs: {
            let quadratic = &d__ + &e__ * x_.pow(2);
            let denominator = Atom::num(1) + c__.pow(2) * x_.pow(2);
            let argument = a__ + &b__ * (&c__ * x_).asinh();
            let ratio_1 = rubi_simp(&(quadratic.sqrt() / denominator.sqrt()), x_);
            let ratio_2 = rubi_simp(&(quadratic.sqrt() / denominator.sqrt()), x_);
            let recursive_1 = rubi_rhs_int(
                &(x_ * argument.pow(&n_ - Atom::num(1))),
                x_,
            );
            let recursive_2 = rubi_rhs_int(&(argument.pow(&n_) / denominator.sqrt()), x_);
            rubi_simp(&(x_ * quadratic.sqrt() * argument.pow(&n_) / Atom::num(2)), x_)
                    - rubi_star(&b__ * &c__ * &n_ / Atom::num(2) * ratio_1, recursive_1)
                    + rubi_star(ratio_2 / Atom::num(2), recursive_2)
        },
    ));
}

fn push_rules_rule_6201(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6201,
        source: "Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
          x*(d+e*x^2)^p*(a+b*ArcSinh[c*x])^n/(2*p+1) +
          2*d*p/(2*p+1) \\[Star] Int[(d+e*x^2)^(p-1)*(a+b*ArcSinh[c*x])^n,x] -
          b*c*n/(2*p+1)*Simp[(d+e*x^2)^p/(1+c^2*x^2)^p] \\[Star] Int[x*(1+c^2*x^2)^(p-1/2)*(a+b*ArcSinh[c*x])^(n-1),x] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[e,c^2*d] && GtQ[n,0] && GtQ[p,0]",
        desc: "Inverted integration by parts and piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [e__, a__, b__, c__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(e__, c__.pow(2) * &d__)
                && gtq!(n_, 0)
                && gtq!(p_, 0)
        },
        rhs: {
            let _half = Atom::num(1) / Atom::num(2);
            let quadratic = &d__ + &e__ * x_.pow(2);
            let denominator = Atom::num(1) + c__.pow(2) * x_.pow(2);
            let argument = a__ + &b__ * (&c__ * x_).asinh();
            let ratio = rubi_simp(&(quadratic.pow(&p_) / denominator.pow(&p_)), x_);
            let recursive_1 = rubi_rhs_int(
                &(quadratic.pow(&p_ - Atom::num(1))
                    * argument.pow(&n_)),
                x_,
            );
            let recursive_2 = rubi_rhs_int(
                &(x_
                    * denominator.pow(&p_ - &(Atom::num(1) / 2))
                    * argument.pow(&n_ - Atom::num(1))),
                x_,
            );
            rubi_simp(&(x_ * quadratic.pow(&p_) * argument.pow(&n_)
                    / (Atom::num(2) * &p_ + Atom::num(1))), x_)
                    + rubi_star(Atom::num(2) * &d__ * &p_ / (Atom::num(2) * &p_ + Atom::num(1)), recursive_1)
                    - rubi_star(&b__ * &c__ * &n_ / (Atom::num(2) * &p_ + Atom::num(1)) * ratio, recursive_2)
        },
    ));
}

fn push_rules_rule_6202(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 6202,
        source: "Int[(a_.+b_.*ArcSinh[c_.*x_])^n_./(d_+e_.*x_^2)^(3/2),x_Symbol] :=
          x*(a+b*ArcSinh[c*x])^n/(d*Sqrt[d+e*x^2]) -
          b*c*n/d*Simp[Sqrt[1+c^2*x^2]/Sqrt[d+e*x^2]] \\[Star] Int[x*(a+b*ArcSinh[c*x])^(n-1)/(1+c^2*x^2),x] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[e,c^2*d] && GtQ[n,0]",
        desc: "Integration by parts and piecewise constant extraction",
        refs: [],
        pattern: (a__ + b__ * (c__ * x_).asinh()).pow(n_)
            / (d__ + e__ * x_.pow(2)).pow(Atom::num(3) / Atom::num(2)),
        with: [a__, b__, c__, n_, d__, e__, x_],
        optional: [a__, b__, c__, e__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(e__, c__.pow(2) * &d__)
                && gtq!(n_, 0)
        },
        rhs: {
            let quadratic = &d__ + &e__ * x_.pow(2);
            let denominator = Atom::num(1) + c__.pow(2) * x_.pow(2);
            let argument = a__ + &b__ * (&c__ * x_).asinh();
            let ratio = rubi_simp(&(denominator.sqrt() / quadratic.sqrt()), x_);
            let recursive = rubi_rhs_int(
                &(x_ * argument.pow(&n_ - Atom::num(1)) / denominator),
                x_,
            );
            rubi_simp(&(x_ * argument.pow(&n_) / (&d__ * quadratic.sqrt())), x_)
                    - rubi_star(&b__ * &c__ * &n_ / &d__ * ratio, recursive)
        },
    ));
}

fn push_rules_rule_6203(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6203,
        source: "Int[(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
          -x*(d+e*x^2)^(p+1)*(a+b*ArcSinh[c*x])^n/(2*d*(p+1)) +
          (2*p+3)/(2*d*(p+1)) \\[Star] Int[(d+e*x^2)^(p+1)*(a+b*ArcSinh[c*x])^n,x] +
          b*c*n/(2*(p+1))*Simp[(d+e*x^2)^p/(1+c^2*x^2)^p] \\[Star] Int[x*(1+c^2*x^2)^(p+1/2)*(a+b*ArcSinh[c*x])^(n-1),x] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[e,c^2*d] && GtQ[n,0] && LtQ[p,-1] && NeQ[p,-3/2]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [e__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(e__, c__.pow(2) * &d__)
                && gtq!(n_, 0)
                && ltq!(p_, -1)
                && neq!(p_, -Atom::num(3) / Atom::num(2))
        },
        rhs: {
            let _half = Atom::num(1) / Atom::num(2);
            let quadratic = &d__ + &e__ * x_.pow(2);
            let denominator = Atom::num(1) + c__.pow(2) * x_.pow(2);
            let argument = a__ + &b__ * (&c__ * x_).asinh();
            let ratio = rubi_simp(&(quadratic.pow(&p_) / denominator.pow(&p_)), x_);
            let recursive_1 = rubi_rhs_int(
                &(quadratic.pow(&p_ + Atom::num(1))
                    * argument.pow(&n_)),
                x_,
            );
            let recursive_2 = rubi_rhs_int(
                &(x_
                    * denominator.pow(&p_ + &(Atom::num(1) / 2))
                    * argument.pow(&n_ - Atom::num(1))),
                x_,
            );
            rubi_simp(&(Atom::num(-1) * x_
                    * quadratic.pow(&p_ + Atom::num(1))
                    * argument.pow(&n_)
                    / (Atom::num(2) * &d__ * (&p_ + Atom::num(1)))), x_)
                    + rubi_star((Atom::num(2) * &p_ + Atom::num(3))
                            / (Atom::num(2) * &d__ * (&p_ + Atom::num(1))), recursive_1)
                    + rubi_star(&b__ * &c__ * &n_ / (Atom::num(2) * (&p_ + Atom::num(1))) * ratio, recursive_2)
        },
    ));
}

fn push_rules_rule_6204(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 6204,
        source: "Int[(a_.+b_.*ArcSinh[c_.*x_])^n_./(d_+e_.*x_^2),x_Symbol] :=
          1/(c*d) \\[Star] Subst[Int[(a+b*x)^n*Sech[x],x],x,ArcSinh[c*x]] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[e,c^2*d] && IGtQ[n,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (a__ + b__ * (c__ * x_).asinh()).pow(n_) / (d__ + e__ * x_.pow(2)),
        with: [a__, b__, c__, n_, d__, e__, x_],
        optional: [a__, b__, c__, e__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(e__, c__.pow(2) * &d__)
                && igtq!(n_, 0)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let substitution_integrand = (a__ + b__ * &sub_atom).pow(&n_) * sub_atom.sech();
            let substitution_primitive =
                rubi_rhs_int(&substitution_integrand, substitution_symbol);
            let substitution = (&c__ * x_).asinh();
            let substituted =
                rubi_subst(&substitution_primitive, substitution_symbol, substitution);

            rubi_star(Atom::num(1) / (&c__ * &d__), substituted)
        },
    ));
}

fn push_rules_rule_6205(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6205,
        source: "Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSinh[c_.*x_])^n_,x_Symbol] :=
          Simp[Sqrt[1+c^2*x^2]*(d+e*x^2)^p]*(a+b*ArcSinh[c*x])^(n+1)/(b*c*(n+1)) -
          c*(2*p+1)/(b*(n+1))*Simp[(d+e*x^2)^p/(1+c^2*x^2)^p] \\[Star] Int[x*(1+c^2*x^2)^(p-1/2)*(a+b*ArcSinh[c*x])^(n+1),x] /;
        FreeQ[{a,b,c,d,e,p},x] && EqQ[e,c^2*d] && LtQ[n,-1]",
        desc: "Integration by parts and piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [e__, a__, b__, c__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, p_], x_)
                && eqq!(e__, c__.pow(2) * &d__)
                && ltq!(n_, -1)
        },
        rhs: {
            let quadratic = &d__ + &e__ * x_.pow(2);
            let denominator = Atom::num(1) + c__.pow(2) * x_.pow(2);
            let argument = a__ + &b__ * (&c__ * x_).asinh();
            let simp1 = rubi_simp(&(denominator.sqrt() * quadratic.pow(&p_)), x_);
            let simp2 = rubi_simp(&(quadratic.pow(&p_) / denominator.pow(&p_)), x_);
            let recursive = rubi_rhs_int(
                &(x_
                    * (Atom::num(1) + c__.pow(2) * x_.pow(2))
                        .pow(&p_ - half_integer_atom(1))
                    * argument.pow(&n_ + Atom::num(1))),
                x_,
            );
            rubi_simp(&(simp1 * argument.pow(&n_ + Atom::num(1))
                    / (&b__ * &c__ * (&n_ + Atom::num(1)))), x_)
                    - rubi_star(&c__ * (Atom::num(2) * &p_ + Atom::num(1))
                            / (&b__ * (&n_ + Atom::num(1)))
                            * simp2, recursive)
        },
    ));
}

fn push_rules_rule_6206(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6206,
        source: "Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
          1/(b*c)*Simp[(d+e*x^2)^p/(1+c^2*x^2)^p] \\[Star] Subst[Int[x^n*Cosh[-a/b+x/b]^(2*p+1),x],x,a+b*ArcSinh[c*x]] /;
        FreeQ[{a,b,c,d,e,n},x] && EqQ[e,c^2*d] && IGtQ[2*p,0]",
        desc: "Piecewise constant extraction and integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [e__, a__, b__, c__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, n_], x_)
                && eqq!(e__, c__.pow(2) * &d__)
                && igtq!(Atom::num(2) * &p_, 0)
        },
        rhs: {
            let quadratic = &d__ + &e__ * x_.pow(2);
            let denominator = Atom::num(1) + c__.pow(2) * x_.pow(2);
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let transformed_integrand = sub_atom.pow(&n_)
                * (-&a__ / &b__ + &sub_atom / &b__).cosh().pow(Atom::num(2) * &p_ + Atom::num(1));
            let transformed_primitive =
                rubi_rhs_int(&transformed_integrand, substitution_symbol);
            let substitution = &a__ + &b__ * (&c__ * x_).asinh();
            let simp = rubi_simp(&(quadratic.pow(&p_) / denominator.pow(&p_)), x_);
            let substituted =
                rubi_subst(&transformed_primitive, substitution_symbol, substitution);

            rubi_star(simp / (&b__ * &c__), substituted)
        },
    ));
}

fn push_rules_rule_6207(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, p_, x_);
    rules.push(rubi_rule!(
        order: 6207,
        source: "Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSinh[c_.*x_]),x_Symbol] :=
          With[{u=IntHide[(d+e*x^2)^p,x]},
          (a+b*ArcSinh[c*x]) \\[Star] u - b*c \\[Star] Int[SimplifyIntegrand[u/Sqrt[1+c^2*x^2],x],x]] /;
        FreeQ[{a,b,c,d,e},x] && NeQ[e,c^2*d] && (IGtQ[p,0] || ILtQ[p+1/2,0])",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [d__, e__, p_, a__, b__, c__, x_],
        optional: [e__, a__, b__, c__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && neq!(e__, c__.pow(2) * &d__)
                && (igtq!(p_, 0) || iltq!(&p_ + half_integer_atom(1), 0))
        },
        rhs: {
            let argument = &a__ + &b__ * (&c__ * x_).asinh();
            let u = rubi_int_hide(&(&d__ + &e__ * x_.pow(2)).pow(&p_), x_).rubi_rhs();
            let recursive_integrand = rubi_simplify_integrand(
                &(&u / (Atom::num(1) + c__.pow(2) * x_.pow(2)).sqrt()),
                x_,
            );
            rubi_star(argument, u)
                    - rubi_star(&b__ * &c__, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_6208(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6208,
        source: "Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
          Int[ExpandIntegrand[(a+b*ArcSinh[c*x])^n,(d+e*x^2)^p,x],x] /;
        FreeQ[{a,b,c,d,e,n},x] && NeQ[e,c^2*d] && IntegerQ[p] && (p>0 || IGtQ[n,0])",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [e__, a__, b__, c__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, n_], x_)
                && neq!(e__, c__.pow(2) * &d__)
                && integerq!(p_)
                && (gtq!(p_, 0) || igtq!(n_, 0))
        },
        rhs: {
            let expanded = rubi_expand_integrand_product(
                &(&a__ + &b__ * (&c__ * x_).asinh()).pow(&n_),
                &(&d__ + &e__ * x_.pow(2)).pow(&p_),
                x_,
            );
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_6209(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6209,
        source: "Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
          Unintegrable[(d+e*x^2)^p*(a+b*ArcSinh[c*x])^n,x] /;
        FreeQ[{a,b,c,d,e,n,p},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [e__, a__, b__, c__, n_, p_],
        when: { freeq!([a__, b__, c__, d__, e__, n_, p_], x_) },
        rhs: {
            let integrand =
                (&d__ + &e__ * x_.pow(2)).pow(&p_) * (a__ + b__ * (c__ * x_).asinh()).pow(&n_);
            rubi_unintegrable(integrand, x_)
        },
    ));
}

fn push_rules_rule_6210(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 6210,
        source: "Int[(d_+e_.*x_)^p_*(f_+g_.*x_)^q_*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
          (-d^2*g/e)^q \\[Star] Int[(d+e*x)^(p-q)*(1+c^2*x^2)^q*(a+b*ArcSinh[c*x])^n,x] /;
        FreeQ[{a,b,c,d,e,f,g,n},x] && EqQ[e*f+d*g,0] && EqQ[c^2*d^2+e^2,0] && HalfIntegerQ[p,q] && GeQ[p-q,0] && GtQ[d,0] && LtQ[g/e,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [d__, e__, p_, f__, g__, q_, a__, b__, c__, n_, x_],
        optional: [e__, g__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, n_], x_)
                && eqq!(&e__ * &f__ + &d__ * &g__, 0)
                && eqq!(c__.pow(2) * d__.pow(2) + e__.pow(2), 0)
                && half_integer_numerator(&p_).is_some()
                && half_integer_numerator(&q_).is_some()
                && geq!(&p_ - &q_, 0)
                && gtq!(d__, 0)
                && ltq!(&g__ / &e__, 0)
        },
        rhs: {
            let argument = &a__ + &b__ * (&c__ * x_).asinh();
            let transformed_integrand = (&d__ + &e__ * x_).pow(&p_ - &q_)
                * (Atom::num(1) + c__.pow(2) * x_.pow(2)).pow(&q_)
                * argument.pow(&n_);
            let primitive = rubi_rhs_int(&transformed_integrand, x_);

            rubi_star((-d__.pow(2) * g__ / e__).pow(q_), primitive)
        },
    ));
}

fn push_rules_rule_6211(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 6211,
        source: "Int[(d_+e_.*x_)^p_*(f_+g_.*x_)^q_*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
          (d+e*x)^q*(f+g*x)^q/(1+c^2*x^2)^q \\[Star] Int[(d+e*x)^(p-q)*(1+c^2*x^2)^q*(a+b*ArcSinh[c*x])^n,x] /;
        FreeQ[{a,b,c,d,e,f,g,n},x] && EqQ[e*f+d*g,0] && EqQ[c^2*d^2+e^2,0] && HalfIntegerQ[p,q] && GeQ[p-q,0]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [d__, e__, p_, f__, g__, q_, a__, b__, c__, n_, x_],
        optional: [e__, g__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, n_], x_)
                && eqq!(&e__ * &f__ + &d__ * &g__, 0)
                && eqq!(c__.pow(2) * d__.pow(2) + e__.pow(2), 0)
                && half_integer_numerator(&p_).is_some()
                && half_integer_numerator(&q_).is_some()
                && geq!(&p_ - &q_, 0)
        },
        rhs: {
            let argument = &a__ + &b__ * (&c__ * x_).asinh();
            let transformed_integrand = (&d__ + &e__ * x_).pow(&p_ - &q_)
                * (Atom::num(1) + c__.pow(2) * x_.pow(2)).pow(&q_)
                * argument.pow(&n_);
            let multiplier = (&d__ + &e__ * x_).pow(&q_)
                * (&f__ + &g__ * x_).pow(&q_)
                / (Atom::num(1) + c__.pow(2) * x_.pow(2)).pow(&q_);
            let primitive = rubi_rhs_int(&transformed_integrand, x_);

            rubi_star(multiplier, primitive)
        },
    ));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn downvalues_6197_through_6211_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .filter(|order| (6197..=6211).contains(order))
            .collect::<Vec<_>>();
        assert_eq!(orders, (6197..=6211).collect::<Vec<_>>());
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
    (d__ + e__ * x_).pow(p_) * (f__ + g__ * x_).pow(q_) * (a__ + b__ * (c__ * x_).asinh()).pow(n_)
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
    (d__ + e__ * x_.pow(2)).pow(p_) * (a__ + b__ * (c__ * x_).asinh())
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
    (d__ + e__ * x_.pow(2)).pow(p_) * (a__ + b__ * (c__ * x_).asinh()).pow(n_)
}
