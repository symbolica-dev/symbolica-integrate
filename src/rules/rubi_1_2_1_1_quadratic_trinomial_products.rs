use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_1077(rules);
    push_rules_rule_1078(rules);
    push_rules_rule_1079(rules);
    push_rules_rule_1080(rules);
    push_rules_rule_1081(rules);
    push_rules_rule_1082(rules);
    push_rules_rule_1083(rules);
    push_rules_rule_1084(rules);
    push_rules_rule_1085(rules);
    push_rules_rule_1086(rules);
    push_rules_rule_1087(rules);
    push_rules_rule_1088(rules);
    push_rules_rule_1089(rules);
    push_rules_rule_1090(rules);
    push_rules_rule_1091(rules);
    push_rules_rule_1092(rules);
    push_rules_rule_1093(rules);
    push_rules_rule_1094(rules);
    push_rules_rule_1095(rules);
    push_rules_rule_1096(rules);
    push_rules_rule_1097(rules);
}

fn push_rules_rule_1078(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, p_, x_);
    rules.push(rubi_rule!(
        order: 1078,
        source: "Int[(a_+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          2*(a+b*x+c*x^2)^(p+1)/((2*p+1)*(b+2*c*x)) /;
        FreeQ[{a,b,c,p},x] && EqQ[b^2-4*a*c,0] && LtQ[p,-1]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, p_, x_],
        optional: [b__, c__],
        when: {
            freeq!([a__, b__, c__, p_], x_)
                && eqq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && ltq!(p_, -1)
        },
        rhs: {
            rubi_simp(
                &(Atom::num(2)
                    * (&a__ + &b__ * x_ + &c__ * x_.pow(2)).pow(&p_ + 1)
                    / ((Atom::num(2) * &p_ + 1)
                        * (&b__ + Atom::num(2) * &c__ * x_))),
                x_,
            )
        },
    ));
}

fn push_rules_rule_1077(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, p_, x_);
    rules.push(rubi_rule!(
        order: 1077,
        source: "Int[(a_+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
          1/c^p \\[Star] Int[(b/2+c*x)^(2*p),x] /;
        FreeQ[{a,b,c},x] && EqQ[b^2-4*a*c,0] && IntegerQ[p]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, p_, x_],
        optional: [b__, c__, p_],
        when: {
            freeq!([a__, b__, c__], x_)
                && eqq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && integerq!(p_)
        },
        rhs: {
            let recursive_integrand = (&b__ / Atom::num(2) + &c__ * x_).pow(Atom::num(2) * &p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            rubi_star(Atom::num(1) / c__.pow(&p_), recursive)
        },
    ));
}

fn push_rules_rule_1080(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; b__, c__, p_, x_);
    rules.push(rubi_rule!(
        order: 1080,
        source: "Int[(b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          Int[ExpandIntegrand[x^p*(b+c*x)^p,x],x] /;
        FreeQ[{b,c},x] && IntegerQ[p]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [b__, c__, p_, x_],
        optional: [b__, c__],
        when: { freeq!([b__, c__], x_) && integerq!(p_) },
        rhs: {
            let expanded = rubi_expand_integrand(
                &(x_.pow(&p_) * (&b__ + &c__ * x_).pow(&p_)),
                x_,
            );
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_1079(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, p_, x_);
    rules.push(rubi_rule!(
        order: 1079,
        source: "Int[(a_+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          (a+b*x+c*x^2)^FracPart[p]/(c^IntPart[p]*(b/2+c*x)^(2*FracPart[p])) \\[Star] Int[(b/2+c*x)^(2*p),x] /;
        FreeQ[{a,b,c,p},x] && EqQ[b^2-4*a*c,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, p_, x_],
        optional: [b__, c__],
        when: {
            freeq!([a__, b__, c__, p_], x_)
                && eqq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
        },
        rhs: {
            let frac_p = rubi_frac_part(&p_);
            let recursive = rubi_rhs_int(
                &(&b__ / Atom::num(2) + &c__ * x_).pow(Atom::num(2) * &p_),
                x_,
            );
            rubi_star((&a__ + &b__ * x_ + &c__ * x_.pow(2)).pow(&frac_p)
                    / (c__.pow(rubi_int_part(&p_))
                        * (&b__ / Atom::num(2) + &c__ * x_)
                            .pow(Atom::num(2) * frac_p)), recursive)
        },
    ));
}

fn push_rules_rule_1084(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, p_, x_);
    rules.push(rubi_rule!(
        order: 1084,
        source: "Int[(a_+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          With[{q=Rt[b^2-4*a*c,2]}, 1/c^p \\[Star] Int[ExpandIntegrand[(b/2-q/2+c*x)^p*(b/2+q/2+c*x)^p,x],x] /;
         Not[FractionalPowerFactorQ[q]]] /;
        FreeQ[{a,b,c},x] && IntegerQ[p] && NiceSqrtQ[b^2-4*a*c]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, p_, x_],
        optional: [b__, c__],
        when: {
            let discriminant = b__.pow(2) - Atom::num(4) * &a__ * &c__;
            let q = rubi_rt(&discriminant, 2);
            freeq!([a__, b__, c__], x_)
                && integerq!(p_)
                && rubi_nice_sqrt_q(&discriminant)
                && !rubi_fractional_power_factor_q(&q)
        },
        rhs: {
            let q = rubi_rt(&(b__.pow(2) - Atom::num(4) * &a__ * &c__), 2);
            let expanded = rubi_expand_integrand(
                &((&b__ / Atom::num(2) - &q / Atom::num(2) + &c__ * x_).pow(&p_)
                    * (&b__ / Atom::num(2) + &q / Atom::num(2) + &c__ * x_)
                        .pow(&p_)),
                x_,
            );
            let recursive = rubi_rhs_int(&expanded, x_);

            rubi_star(Atom::num(1) / c__.pow(&p_), recursive)
        },
    ));
}

fn push_rules_rule_1085(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, p_, x_);
    rules.push(rubi_rule!(
        order: 1085,
        source: "Int[(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          Int[ExpandIntegrand[(a+b*x+c*x^2)^p,x],x] /;
        FreeQ[{a,b,c},x] && IntegerQ[p] && (GtQ[p,0] || EqQ[a,0])",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, p_, x_],
        optional: [a__, b__, c__],
        when: {
            freeq!([a__, b__, c__], x_)
                && integerq!(p_)
                && (gtq!(p_, 0) || eqq!(a__, 0))
        },
        rhs: {
            let payload = (&a__ + &b__ * x_ + &c__ * x_.pow(2)).pow(&p_);
            let expanded = rubi_expand_integrand(&payload, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_1087(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, p_, x_);
    rules.push(rubi_rule!(
        order: 1087,
        source: "Int[(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          (b+2*c*x)*(a+b*x+c*x^2)^p/(2*c*(2*p+1)) -
          p*(b^2-4*a*c)/(2*c*(2*p+1)) \\[Star] Int[(a+b*x+c*x^2)^(p-1),x] /;
        FreeQ[{a,b,c},x] && GtQ[p,0] && (IntegerQ[4*p] || IntegerQ[3*p])",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, p_, x_],
        optional: [a__, b__, c__],
        when: {
            freeq!([a__, b__, c__], x_)
                && gtq!(p_, 0)
                && (integerq!(Atom::num(4) * &p_)
                    || integerq!(Atom::num(3) * &p_))
        },
        rhs: {
            let denominator = Atom::num(2) * &c__ * (Atom::num(2) * &p_ + Atom::num(1));
            let discriminant = b__.pow(2) - Atom::num(4) * &a__ * &c__;
            let trinomial = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let direct = (&b__ + Atom::num(2) * &c__ * x_) * trinomial.pow(&p_) / &denominator;
            let recursive_integrand = trinomial.pow(&p_ - Atom::num(1));
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_)
                    - rubi_star(&p_ * discriminant / denominator, recursive)
        },
    ));
}

fn push_rules_rule_1088(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, x_);
    rules.push(rubi_rule!(
        order: 1088,
        source: "Int[1/(a_.+b_.*x_+c_.*x_^2)^(3/2),x_Symbol] :=
          -2*(b+2*c*x)/((b^2-4*a*c)*Sqrt[a+b*x+c*x^2]) /;
        FreeQ[{a,b,c},x] && NeQ[b^2-4*a*c,0]",
        desc: "Quadratic recurrence 2a with m=0, A=1, B=0 and p=-32",
        refs: ["G&R 2.264.5, CRC 239"],
        pattern: Atom::num(1)
            / (a__ + b__ * x_ + c__ * x_.pow(2)).pow(Atom::num(3) / Atom::num(2)),
        with: [a__, b__, c__, x_],
        optional: [a__, b__, c__],
        when: {
            let discriminant = b__.pow(2) - Atom::num(4) * &a__ * &c__;
            freeq!([a__, b__, c__], x_) && neq!(discriminant, 0)
        },
        rhs: {
            let discriminant = b__.pow(2) - Atom::num(4) * &a__ * &c__;
            rubi_simp(&(-Atom::num(2) * (&b__ + Atom::num(2) * &c__ * x_)
                    / (discriminant * (&a__ + &b__ * x_ + &c__ * x_.pow(2)).sqrt())), x_)
        },
    ));
}

fn push_rules_rule_1089(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, p_, x_);
    rules.push(rubi_rule!(
        order: 1089,
        source: "Int[(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          (b+2*c*x)*(a+b*x+c*x^2)^(p+1)/((p+1)*(b^2-4*a*c)) -
          2*c*(2*p+3)/((p+1)*(b^2-4*a*c)) \\[Star] Int[(a+b*x+c*x^2)^(p+1),x] /;
        FreeQ[{a,b,c},x] && LtQ[p,-1] && (IntegerQ[4*p] || IntegerQ[3*p])",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, p_, x_],
        optional: [a__, b__, c__],
        when: {
            freeq!([a__, b__, c__], x_)
                && ltq!(p_, -1)
                && (integerq!(Atom::num(4) * &p_)
                    || integerq!(Atom::num(3) * &p_))
        },
        rhs: {
            let denominator = (&p_ + Atom::num(1)) * (b__.pow(2) - Atom::num(4) * &a__ * &c__);
            let trinomial = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let direct = (&b__ + Atom::num(2) * &c__ * x_)
                * trinomial.pow(&p_ + Atom::num(1))
                / &denominator;
            let recursive_integrand = trinomial.pow(&p_ + Atom::num(1));
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_)
                    - rubi_star(Atom::num(2)
                            * &c__
                            * (Atom::num(2) * &p_ + Atom::num(3))
                            / denominator, recursive)
        },
    ));
}

fn push_rules_rule_1093(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; b__, c__, p_, x_);
    rules.push(rubi_rule!(
        order: 1093,
        source: "Int[(b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          (b*x+c*x^2)^p/(-c*(b*x+c*x^2)/(b^2))^p \\[Star] Int[(-c*x/b-c^2*x^2/b^2)^p,x] /;
        FreeQ[{b,c},x] && (IntegerQ[4*p] || IntegerQ[3*p])",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [b__, c__, p_, x_],
        optional: [b__, c__],
        when: {
            freeq!([b__, c__], x_)
                && (integerq!(Atom::num(4) * &p_)
                    || integerq!(Atom::num(3) * &p_))
        },
        rhs: {
            let base = &b__ * x_ + &c__ * x_.pow(2);
            let normalized_base = -&c__ * x_ / &b__
                - c__.pow(2) * x_.pow(2) / b__.pow(2);
            let recursive = rubi_rhs_int(&normalized_base.pow(&p_), x_);
            rubi_star(base.pow(&p_)
                    / (-&c__ * &base / b__.pow(2)).pow(&p_), recursive)
        },
    ));
}

fn push_rules_rule_1081(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, x_);
    rules.push(rubi_rule!(
        order: 1081,
        source: "Int[1/(a_+b_.*x_+c_.*x_^2),x_Symbol] :=
          With[{q=Rt[b^2-4*a*c,2]}, c \\[Star] Int[ExpandIntegrand[1/((b/2-q/2+c*x)*(b/2+q/2+c*x)),x],x]] /;
        FreeQ[{a,b,c},x] && NiceSqrtQ[b^2-4*a*c]",
        desc: "Integration by substitution",
        refs: ["G&R 2.172.4, CRC 109, A&S 3.3.16", "G&R 2.172.2, CRC 110a, A&S 3.3.17"],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, x_],
        optional: [b__, c__],
        when: {
            freeq!([a__, b__, c__], x_)
                && rubi_nice_sqrt_q(&(b__.pow(2) - Atom::num(4) * &a__ * &c__))
        },
        rhs: {
            let discriminant = b__.pow(2) - Atom::num(4) * &a__ * &c__;
            let q = rubi_rt(&discriminant, 2);
            let expanded = rubi_expand_integrand(
                &(Atom::num(1)
                    / ((&b__ / Atom::num(2) - &q / Atom::num(2) + &c__ * x_)
                        * (&b__ / Atom::num(2) + &q / Atom::num(2) + &c__ * x_))),
                x_,
            );
            let recursive = rubi_rhs_int(&expanded, x_);
            rubi_star(c__, recursive)
        },
    ));
}

fn push_rules_rule_1082(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, x_);
    rules.push(rubi_rule!(
        order: 1082,
        source: "Int[1/(a_+b_.*x_+c_.*x_^2),x_Symbol] :=
          With[{q=1-4*Simplify[a*c/b^2]},
          -2/b \\[Star] Subst[Int[1/(q-x^2),x],x,1+2*c*x/b] /;
         RationalQ[q] && (EqQ[q^2,1] || Not[RationalQ[b^2-4*a*c]])] /;
        FreeQ[{a,b,c},x]",
        desc: "Integration by substitution",
        refs: ["G&R 2.172.4, CRC 109, A&S 3.3.16", "G&R 2.172.2, CRC 110a, A&S 3.3.17"],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, x_],
        optional: [b__, c__],
        when: {
            let discriminant = b__.pow(2) - Atom::num(4) * &a__ * &c__;
            let q = Atom::num(1)
                - Atom::num(4) * rubi_simplify(&(&a__ * &c__ / b__.pow(2)));
            freeq!([a__, b__, c__], x_)
                && rational_q(&q)
                && (eqq!(&q * &q, 1) || !rational_q(&discriminant))
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub_symbol = sub_guard.symbol();
            let sub_atom = Atom::var(sub_symbol);
            let q = Atom::num(1)
                - Atom::num(4) * rubi_simplify(&(&a__ * &c__ / b__.pow(2)));
            let transformed_integrand = Atom::num(1) / (&q - sub_atom.pow(2));
            let transformed = rubi_rhs_int(&transformed_integrand, sub_symbol);
            let substituted = rubi_subst(
                &transformed,
                sub_symbol,
                Atom::num(1) + Atom::num(2) * &c__ * x_ / &b__,
            );
            rubi_star(-Atom::num(2) / &b__, substituted)
        },
    ));
}

fn push_rules_rule_1083(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, x_);
    rules.push(rubi_rule!(
        order: 1083,
        source: "Int[1/(a_+b_.*x_+c_.*x_^2),x_Symbol] :=
          -2 \\[Star] Subst[Int[1/Simp[b^2-4*a*c-x^2,x],x],x,b+2*c*x] /;
        FreeQ[{a,b,c},x]",
        desc: "Integration by substitution",
        refs: ["G&R 2.172.4, CRC 109, A&S 3.3.16", "G&R 2.172.2, CRC 110a, A&S 3.3.17"],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, x_],
        optional: [b__, c__],
        when: { freeq!([a__, b__, c__], x_) },
        rhs: {
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub_symbol = sub_guard.symbol();
            let sub_atom = Atom::var(sub_symbol);
            let transformed_integrand = Atom::num(1)
                / rubi_simp(
                    &(b__.pow(2)
                        - Atom::num(4) * &a__ * &c__
                        - sub_atom.pow(2)),
                    sub_symbol,
                );
            let transformed = rubi_rhs_int(&transformed_integrand, sub_symbol);
            let substituted = rubi_subst(
                &transformed,
                sub_symbol,
                &b__ + Atom::num(2) * &c__ * x_,
            );
            rubi_star(Atom::num(-2), substituted)
        },
    ));
}

fn push_rules_rule_1090(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, p_, x_);
    rules.push(rubi_rule!(
        order: 1090,
        source: "Int[(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          1/(2*c*(-4*c/(b^2-4*a*c))^p) \\[Star] Subst[Int[Simp[1-x^2/(b^2-4*a*c),x]^p,x],x,b+2*c*x] /;
        FreeQ[{a,b,c,p},x] && GtQ[4*a-b^2/c,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, p_, x_],
        optional: [a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, p_], x_)
                && gtq!(Atom::num(4) * &a__ - b__.pow(2) / &c__, 0)
        },
        rhs: {
            let discriminant = b__.pow(2) - Atom::num(4) * &a__ * &c__;
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub_symbol = sub_guard.symbol();
            let sub_atom = Atom::var(sub_symbol);
            let transformed_integrand =
                rubi_simp(&(Atom::num(1) - sub_atom.pow(2) / &discriminant), sub_symbol)
                    .pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, sub_symbol);
            let substituted = rubi_subst(
                &transformed,
                sub_symbol,
                &b__ + Atom::num(2) * &c__ * x_,
            );
            rubi_star(Atom::num(1)
                    / (Atom::num(2)
                        * &c__
                        * (-Atom::num(4) * &c__ / discriminant).pow(&p_)), substituted)
        },
    ));
}

fn push_rules_rule_1091(rules: &mut Vec<RubiRule>) {
    rubi_symb!(b__, c__, x_);
    rules.push(rubi_rule!(
        order: 1091,
        source: "Int[1/Sqrt[b_.*x_+c_.*x_^2],x_Symbol] :=
          2 \\[Star] Subst[Int[1/(1-c*x^2),x],x,x/Sqrt[b*x+c*x^2]] /;
        FreeQ[{b,c},x]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (b__ * x_ + c__ * x_.pow(2)).pow(-(Atom::num(1) / Atom::num(2))),
        with: [b__, c__, x_],
        optional: [b__, c__],
        when: { freeq!([b__, c__], x_) },
        rhs: {
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub_symbol = sub_guard.symbol();
            let sub_atom = Atom::var(sub_symbol);
            let transformed_integrand = Atom::num(1) / (Atom::num(1) - &c__ * sub_atom.pow(2));
            let transformed = rubi_rhs_int(&transformed_integrand, sub_symbol);
            let substituted = rubi_subst(
                &transformed,
                sub_symbol,
                x_ / (&b__ * x_ + &c__ * x_.pow(2)).sqrt(),
            );
            rubi_star(Atom::num(2), substituted)
        },
    ));
}

fn push_rules_rule_1092(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, x_);
    rules.push(rubi_rule!(
        order: 1092,
        source: "Int[1/Sqrt[a_+b_.*x_+c_.*x_^2],x_Symbol] :=
          2 \\[Star] Subst[Int[1/(4*c-x^2),x],x,(b+2*c*x)/Sqrt[a+b*x+c*x^2]] /;
        FreeQ[{a,b,c},x]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern: (a__ + b__ * x_ + c__ * x_.pow(2)).pow(-(Atom::num(1) / Atom::num(2))),
        with: [a__, b__, c__, x_],
        optional: [b__, c__],
        when: { freeq!([a__, b__, c__], x_) },
        rhs: {
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub_symbol = sub_guard.symbol();
            let sub_atom = Atom::var(sub_symbol);
            let transformed_integrand = Atom::num(1) / (Atom::num(4) * &c__ - sub_atom.pow(2));
            let transformed = rubi_rhs_int(&transformed_integrand, sub_symbol);
            let substituted = rubi_subst(
                &transformed,
                sub_symbol,
                (&b__ + Atom::num(2) * &c__ * x_)
                    / (&a__ + &b__ * x_ + &c__ * x_.pow(2)).sqrt(),
            );
            rubi_star(Atom::num(2), substituted)
        },
    ));
}

fn push_rules_rule_1094(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, p_, x_);
    rules.push(rubi_rule!(
        order: 1094,
        source: "Int[(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          4*Sqrt[(b+2*c*x)^2]/(b+2*c*x) \\[Star] Subst[Int[x^(4*(p+1)-1)/Sqrt[b^2-4*a*c+4*c*x^4],x],x,(a+b*x+c*x^2)^(1/4)] /;
        FreeQ[{a,b,c},x] && IntegerQ[4*p]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, p_, x_],
        optional: [a__, b__, c__],
        when: {
            freeq!([a__, b__, c__], x_)
                && integerq!(Atom::num(4) * &p_)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub_symbol = sub_guard.symbol();
            let sub_atom = Atom::var(sub_symbol);
            let linear = &b__ + Atom::num(2) * &c__ * x_;
            let discriminant = b__.pow(2) - Atom::num(4) * &a__ * &c__;
            let transformed_integrand = sub_atom
                .pow(Atom::num(4) * (&p_ + Atom::num(1)) - Atom::num(1))
                / (discriminant + Atom::num(4) * &c__ * sub_atom.pow(4)).sqrt();
            let transformed = rubi_rhs_int(&transformed_integrand, sub_symbol);
            let trinomial = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let substituted = rubi_subst(
                &transformed,
                sub_symbol,
                trinomial.pow((1, 4)),
            );
            rubi_star(Atom::num(4) * linear.pow(2).sqrt() / linear, substituted)
        },
    ));
}

fn push_rules_rule_1096(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, p_, x_);
    rules.push(rubi_rule!(
        order: 1096,
        source: "Int[(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          With[{q=Rt[b^2-4*a*c,2]},
          -(a+b*x+c*x^2)^(p+1)/(q*(p+1)*((q-b-2*c*x)/(2*q))^(p+1))*Hypergeometric2F1[-p,p+1,p+2,(b+q+2*c*x)/(2*q)]] /;
        FreeQ[{a,b,c,p},x] && Not[IntegerQ[4*p]] && Not[IntegerQ[3*p]]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, p_, x_],
        optional: [a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, p_], x_)
                && !integerq!(Atom::num(4) * &p_)
                && !integerq!(Atom::num(3) * &p_)
        },
        rhs: {
            let q = rubi_rt(&(b__.pow(2) - Atom::num(4) * &a__ * &c__), 2);
            let p1 = &p_ + Atom::num(1);
            let base = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let z_denominator = Atom::num(2) * &q;
            let scale = (&q - &b__ - Atom::num(2) * &c__ * x_) / &z_denominator;
            let denominator = &q * &p1 * scale.pow(&p1);
            rubi_simp(&(-base.pow(&p1)
                    * rubi_hypergeometric2f1(
                        -&p_,
                        &p1,
                        &p_ + Atom::num(2),
                        (&b__ + &q + Atom::num(2) * &c__ * x_) / z_denominator,
                    )
                    / denominator), x_)
        },
    ));
}

fn push_rules_rule_1097(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, p_, u__);
    rules.push(rubi_rule!(
        order: 1097,
        source: "Int[(a_.+b_.*u_+c_.*u_^2)^p_,x_Symbol] :=
          1/Coefficient[u,x,1] \\[Star] Subst[Int[(a+b*x+c*x^2)^p,x],x,u] /;
        FreeQ[{a,b,c,p},x] && LinearQ[u,x] && NeQ[u,x]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (a__ + b__ * u__ + c__ * u__.pow(2)).pow(p_),
        with: [a__, b__, c__, u__, p_, x_],
        optional: [a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, p_], x_)
                && rubi_linear_q(&u__, x_)
                && neq!(u__, x_)
        },
        rhs: {
            let slope = rubi_coefficient(&u__, x_, 1).rubi_rhs();
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub_symbol = sub_guard.symbol();
            let sub_atom = Atom::var(sub_symbol);
            let transformed_integrand = (&a__ + &b__ * &sub_atom + &c__ * sub_atom.pow(2)).pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, sub_symbol);
            let substituted = rubi_subst(&transformed, sub_symbol, u__);
            rubi_star(Atom::num(1) / slope, substituted)
        },
    ));
}

fn push_rules_rule_1086(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, p_, x_);
    rules.push(rubi_rule!(
        order: 1086,
        source: "Int[(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          (b+2*c*x)*(a+b*x+c*x^2)^(p+1)/((p+1)*(b^2-4*a*c)) -
          2*c*(2*p+3)/((p+1)*(b^2-4*a*c)) \\[Star] Int[(a+b*x+c*x^2)^(p+1),x] /;
        FreeQ[{a,b,c},x] && ILtQ[p,-1]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, p_, x_],
        optional: [a__, b__, c__],
        when: { freeq!([a__, b__, c__], x_) && iltq!(p_, -1) },
        rhs: {
            let trinomial = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let denominator = (&p_ + Atom::num(1))
                * (b__.pow(2) - Atom::num(4) * &a__ * &c__);
            let direct = (&b__ + Atom::num(2) * &c__ * x_)
                * trinomial.pow(&p_ + Atom::num(1))
                / &denominator;
            let recursive = rubi_rhs_int(&trinomial.pow(&p_ + Atom::num(1)), x_);
            rubi_simp(&(direct), x_)
                    - rubi_star(Atom::num(2)
                            * &c__
                            * (Atom::num(2) * &p_ + Atom::num(3))
                            / denominator, recursive)
        },
    ));
}

fn push_rules_rule_1095(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, p_, x_);
    rules.push(rubi_rule!(
        order: 1095,
        source: "Int[(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          3*Sqrt[(b+2*c*x)^2]/(b+2*c*x) \\[Star] Subst[Int[x^(3*(p+1)-1)/Sqrt[b^2-4*a*c+4*c*x^3],x],x,(a+b*x+c*x^2)^(1/3)] /;
        FreeQ[{a,b,c},x] && IntegerQ[3*p]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, p_, x_],
        optional: [a__, b__, c__],
        when: {
            freeq!([a__, b__, c__], x_)
                && integerq!(Atom::num(3) * &p_)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub_symbol = sub_guard.symbol();
            let sub_atom = Atom::var(sub_symbol);
            let linear = &b__ + Atom::num(2) * &c__ * x_;
            let discriminant = b__.pow(2) - Atom::num(4) * &a__ * &c__;
            let transformed_integrand = sub_atom
                .pow(Atom::num(3) * (&p_ + Atom::num(1)) - Atom::num(1))
                / (discriminant + Atom::num(4) * &c__ * sub_atom.pow(3)).sqrt();
            let transformed = rubi_rhs_int(&transformed_integrand, sub_symbol);
            let trinomial = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let substituted = rubi_subst(
                &transformed,
                sub_symbol,
                trinomial.pow((1, 3)),
            );
            rubi_star(Atom::num(3) * linear.pow(2).sqrt() / linear, substituted)
        },
    ));
}

// Generated shared pattern builders.

#[inline(never)]
fn rubi_shared_pattern_0(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (a__ + b__ * x_ + c__ * x_.pow(2)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (b__ * x_ + c__ * x_.pow(2)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_2(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let x_ = symbols.x_;
    Atom::num(1) / (a__ + b__ * x_ + c__ * x_.pow(2))
}
