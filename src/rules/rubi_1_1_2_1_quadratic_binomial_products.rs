use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_207(rules);
    push_rules_rule_208(rules);
    push_rules_rule_209(rules);
    push_rules_rule_210(rules);
    push_rules_rule_211(rules);
    push_rules_rule_233(rules);
    push_rules_rule_234(rules);
    push_rules_rule_235(rules);
    push_rules_rule_236(rules);
    push_rules_rule_237(rules);
    push_rules_rule_238(rules);
}

fn push_rules_rule_207(rules: &mut Vec<RubiRule>) {
    rubi_symb!(b__, p_, x_);
    rules.push(rubi_rule!(
        order: 207,
        source: "Int[(b_.*x_^2)^p_,x_Symbol] :=
          b^IntPart[p]*(b*x^2)^FracPart[p]/x^(2*FracPart[p]) \\[Star] Int[x^(2*p),x] /;
        FreeQ[{b,p},x]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern: (b__ * x_.pow(2)).pow(p_),
        with: [b__, p_, x_],
        optional: [b__],
        x_free: [b__, p_],
        when: { freeq!([b__, p_], x_) },
        rhs: {
            let frac_part = rubi_frac_part(&p_);
            let multiplier = b__.pow(rubi_int_part(&p_))
                * (b__ * x_.pow(2)).pow(&frac_part)
                / x_.pow(Atom::num(2) * frac_part);
            let primitive = rubi_rhs_int(x_.pow(Atom::num(2) * p_), x_);
            rubi_star(multiplier, primitive)
        },
    ));
}

fn push_rules_rule_208(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, x_);
    rules.push(rubi_rule!(
        order: 208,
        source: "Int[1/(a_+b_.*x_^2)^(3/2),x_Symbol] :=
          x/(a*Sqrt[a+b*x^2]) /;
        FreeQ[{a,b},x]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: Atom::num(1) / (a__ + b__ * x_.pow(2)).pow((3, 2)),
        with: [a__, b__, x_],
        optional: [b__],
        x_free: [a__, b__],
        when: { freeq!([a__, b__], x_) },
        rhs: {
            rubi_simp(&(x_
                    / (&a__ * (&a__ + &b__ * x_.pow(2)).sqrt())), x_)
        },
    ));
}

fn push_rules_rule_209(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, p_, x_);
    rules.push(rubi_rule!(
        order: 209,
        source: "Int[(a_+b_.*x_^2)^p_,x_Symbol] :=
          -x*(a+b*x^2)^(p+1)/(2*a*(p+1)) +
          (2*p+3)/(2*a*(p+1)) \\[Star] Int[(a+b*x^2)^(p+1),x] /;
        FreeQ[{a,b},x] && ILtQ[p+3/2,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, p_, x_],
        optional: [b__],
        x_free: [a__, b__],
        when: { freeq!([a__, b__], x_) && iltq!(&p_ + Atom::num((3, 2)), 0) },
        rhs: {
            let base = &a__ + &b__ * x_.pow(2);
            let denominator = Atom::num(2) * &a__ * (&p_ + 1);
            let direct = Atom::num(-1) * x_ * base.pow(&p_ + 1) / &denominator;
            let primitive = rubi_rhs_int(&base.pow(&p_ + 1), x_);
            let multiplier = (Atom::num(2) * &p_ + 3) / denominator;
            rubi_simp(&(direct), x_) + rubi_star(multiplier, primitive)
        },
    ));
}

fn push_rules_rule_210(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, p_, x_);
    rules.push(rubi_rule!(
        order: 210,
        source: "Int[(a_+b_.*x_^2)^p_,x_Symbol] :=
          Int[ExpandIntegrand[(a+b*x^2)^p,x],x] /;
        FreeQ[{a,b},x] && IGtQ[p,0]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, p_, x_],
        optional: [b__],
        x_free: [a__, b__],
        when: { freeq!([a__, b__], x_) && igtq!(p_, 0) },
        rhs: {
            let integrand = (a__ + b__ * x_.pow(2)).pow(p_);
            let expanded = rubi_expand_integrand(&integrand, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_211(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, p_, x_);
    rules.push(rubi_rule!(
        order: 211,
        source: "Int[(a_+b_.*x_^2)^p_,x_Symbol] :=
          x*(a+b*x^2)^p/(2*p+1) +
          2*a*p/(2*p+1) \\[Star] Int[(a+b*x^2)^(p-1),x] /;
        FreeQ[{a,b},x] && GtQ[p,0] && (IntegerQ[4*p] || IntegerQ[6*p])",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, p_, x_],
        optional: [b__],
        x_free: [a__, b__],
        when: {
            freeq!([a__, b__], x_)
                && gtq!(p_, 0)
                && (integerq!(Atom::num(4) * &p_) || integerq!(Atom::num(6) * &p_))
        },
        rhs: {
            let base = &a__ + &b__ * x_.pow(2);
            let denominator = Atom::num(2) * &p_ + 1;
            let direct = x_ * base.pow(&p_) / &denominator;
            let primitive = rubi_rhs_int(&base.pow(&p_ - 1), x_);
            let multiplier = Atom::num(2) * a__ * p_ / denominator;
            rubi_simp(&(direct), x_) + rubi_star(multiplier, primitive)
        },
    ));
}

fn push_rules_rule_233(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, x_);
    rules.push(rubi_rule!(
        order: 233,
        source: "Int[1/(a_+b_.*x_^2)^(1/3),x_Symbol] :=
          3*Sqrt[b*x^2]/(2*b*x) \\[Star] Subst[Int[x/Sqrt[-a+x^3],x],x,(a+b*x^2)^(1/3)] /;
        FreeQ[{a,b},x]",
        desc: "Integration by substitution and piecewise constant extraction",
        refs: [],
        pattern: Atom::num(1) / (a__ + b__ * x_.pow(2)).pow((1, 3)),
        with: [a__, b__, x_],
        optional: [b__],
        x_free: [a__, b__],
        when: { freeq!([a__, b__], x_) },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let primitive = rubi_rhs_int(
                &(&sub_atom / (-&a__ + sub_atom.pow(3)).sqrt()),
                sub,
            );
            let replacement = (&a__ + &b__ * x_.pow(2)).pow((1, 3));
            let multiplier = Atom::num(3) * (&b__ * x_.pow(2)).sqrt()
                / (Atom::num(2) * &b__ * x_);
            rubi_star(multiplier, rubi_subst(&primitive, sub, replacement))
        },
    ));
}

fn push_rules_rule_234(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, x_);
    rules.push(rubi_rule!(
        order: 234,
        source: "Int[1/(a_+b_.*x_^2)^(2/3),x_Symbol] :=
          3*Sqrt[b*x^2]/(2*b*x) \\[Star] Subst[Int[1/Sqrt[-a+x^3],x],x,(a+b*x^2)^(1/3)] /;
        FreeQ[{a,b},x]",
        desc: "Integration by substitution and piecewise constant extraction",
        refs: [],
        pattern: Atom::num(1) / (a__ + b__ * x_.pow(2)).pow((2, 3)),
        with: [a__, b__, x_],
        optional: [b__],
        x_free: [a__, b__],
        when: { freeq!([a__, b__], x_) },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let primitive = rubi_rhs_int(&(Atom::num(1) / (-&a__ + sub_atom.pow(3)).sqrt()), sub);
            let replacement = (&a__ + &b__ * x_.pow(2)).pow((1, 3));
            let multiplier = Atom::num(3) * (&b__ * x_.pow(2)).sqrt()
                / (Atom::num(2) * &b__ * x_);
            rubi_star(multiplier, rubi_subst(&primitive, sub, replacement))
        },
    ));
}

fn push_rules_rule_235(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, x_);
    rules.push(rubi_rule!(
        order: 235,
        source: "Int[1/(a_+b_.*x_^2)^(1/6),x_Symbol] :=
          3*x/(2*(a+b*x^2)^(1/6)) - a/2 \\[Star] Int[1/(a+b*x^2)^(7/6),x] /;
        FreeQ[{a,b},x]",
        desc: "Binomial recurrence 2b",
        refs: [],
        pattern: Atom::num(1) / (a__ + b__ * x_.pow(2)).pow((1, 6)),
        with: [a__, b__, x_],
        optional: [b__],
        x_free: [a__, b__],
        when: { freeq!([a__, b__], x_) },
        rhs: {
            let base = &a__ + &b__ * x_.pow(2);
            let direct = Atom::num(3) * x_ / (Atom::num(2) * base.pow((1, 6)));
            let primitive = rubi_rhs_int(&(Atom::num(1) / base.pow((7, 6))), x_);
            rubi_simp(&(direct), x_) - rubi_star(a__ / 2, primitive)
        },
    ));
}

fn push_rules_rule_236(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, x_);
    rules.push(rubi_rule!(
        order: 236,
        source: "Int[1/(a_+b_.*x_^2)^(5/6),x_Symbol] :=
          1/((a/(a+b*x^2))^(1/3)*(a+b*x^2)^(1/3)) \\[Star] Subst[Int[1/(1-b*x^2)^(2/3),x],x,x/Sqrt[a+b*x^2]] /;
        FreeQ[{a,b},x]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern: Atom::num(1) / (a__ + b__ * x_.pow(2)).pow((5, 6)),
        with: [a__, b__, x_],
        optional: [b__],
        x_free: [a__, b__],
        when: { freeq!([a__, b__], x_) },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let primitive = rubi_rhs_int(
                &(Atom::num(1) / (Atom::num(1) - &b__ * sub_atom.pow(2)).pow((2, 3))),
                sub,
            );
            let base = &a__ + &b__ * x_.pow(2);
            let multiplier =
                Atom::num(1) / ((&a__ / &base).pow((1, 3)) * base.pow((1, 3)));
            rubi_star(multiplier, rubi_subst(&primitive, sub, x_ / base.sqrt()))
        },
    ));
}

fn push_rules_rule_237(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, p_, x_);
    rules.push(rubi_rule!(
        order: 237,
        source: "Int[(a_+b_.*x_^2)^p_,x_Symbol] :=
          a^p*x*Hypergeometric2F1[-p,1/2,1/2+1,-b*x^2/a] /;
        FreeQ[{a,b,p},x] && Not[IntegerQ[2*p]] && GtQ[a,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, p_, x_],
        optional: [b__],
        x_free: [a__, b__, p_],
        when: {
            freeq!([a__, b__, p_], x_)
                && !integerq!(Atom::num(2) * &p_)
                && gtq!(a__, 0)
        },
        rhs: {
            rubi_simp(&(a__.pow(&p_)
                    * x_
                    * rubi_hypergeometric2f1(
                        -p_,
                        Atom::num((1, 2)),
                        Atom::num((3, 2)),
                        -b__ * x_.pow(2) / a__,
                    )), x_)
        },
    ));
}

fn push_rules_rule_238(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, p_, x_);
    rules.push(rubi_rule!(
        order: 238,
        source: "Int[(a_+b_.*x_^2)^p_,x_Symbol] :=
          a^IntPart[p]*(a+b*x^2)^FracPart[p]/(1+b*x^2/a)^FracPart[p] \\[Star] Int[(1+b*x^2/a)^p,x] /;
        FreeQ[{a,b,p},x] && Not[IntegerQ[2*p]] && Not[GtQ[a,0]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, p_, x_],
        optional: [b__],
        x_free: [a__, b__, p_],
        when: {
            freeq!([a__, b__, p_], x_)
                && !integerq!(Atom::num(2) * &p_)
                && !gtq!(a__, 0)
        },
        rhs: {
            let base = &a__ + &b__ * x_.pow(2);
            let normalized_base = Atom::num(1) + &b__ * x_.pow(2) / &a__;
            let primitive = rubi_rhs_int(&normalized_base.pow(&p_), x_);
            let multiplier = a__.pow(rubi_int_part(&p_))
                * base.pow(rubi_frac_part(&p_))
                / normalized_base.pow(rubi_frac_part(&p_));
            rubi_star(multiplier, primitive)
        },
    ));
}

// Generated shared pattern builders.

#[inline(never)]
fn rubi_shared_pattern_0(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (a__ + b__ * x_.pow(2)).pow(p_)
}
