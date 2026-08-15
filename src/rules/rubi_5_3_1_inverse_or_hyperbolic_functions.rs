use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_5345(rules);
    push_rules_rule_5346(rules);
    push_rules_rule_5347(rules);
    push_rules_rule_5348(rules);
    push_rules_rule_5349(rules);
    push_rules_rule_5350(rules);
    push_rules_rule_5351(rules);
    push_rules_rule_5352(rules);
    push_rules_rule_5353(rules);
    push_rules_rule_5354(rules);
}

fn push_rules_rule_5345(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5345,
        source: "Int[(a_.+b_.*ArcTan[c_.*x_^n_.])^p_.,x_Symbol] :=
          x*(a+b*ArcTan[c*x^n])^p -
          b*c*n*p \\[Star] Int[x^n*(a+b*ArcTan[c*x^n])^(p-1)/(1+c^2*x^(2*n)),x] /;
        FreeQ[{a,b,c,n},x] && IGtQ[p,0] && (EqQ[n,1] || EqQ[p,1])",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, n_, p_, x_],
        optional: [a__, b__, c__, n_, p_],
        when: {
            freeq!([a__, b__, c__, n_], x_)
                && igtq!(p_, 0)
                && (eqq!(n_, 1) || eqq!(p_, 1))
        },
        rhs: {
            let argument = &a__ + &b__ * (&c__ * x_.pow(&n_)).atan();
            let recursive = x_.pow(&n_) * argument.pow(&p_ - Atom::num(1))
                / (Atom::num(1) + c__.pow(2) * x_.pow(Atom::num(2) * &n_));
            rubi_simp(&(x_ * argument.pow(&p_)), x_)
                    - rubi_star(&b__ * &c__ * &n_ * &p_, rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_5346(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5346,
        source: "Int[(a_.+b_.*ArcCot[c_.*x_^n_.])^p_.,x_Symbol] :=
          x*(a+b*ArcCot[c*x^n])^p +
          b*c*n*p \\[Star] Int[x^n*(a+b*ArcCot[c*x^n])^(p-1)/(1+c^2*x^(2*n)),x] /;
        FreeQ[{a,b,c,n},x] && IGtQ[p,0] && (EqQ[n,1] || EqQ[p,1])",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, n_, p_, x_],
        optional: [a__, b__, c__, n_, p_],
        when: {
            freeq!([a__, b__, c__, n_], x_)
                && igtq!(p_, 0)
                && (eqq!(n_, 1) || eqq!(p_, 1))
        },
        rhs: {
            let argument = &a__ + &b__ * (&c__ * x_.pow(&n_)).acot();
            let recursive = x_.pow(&n_) * argument.pow(&p_ - Atom::num(1))
                / (Atom::num(1) + c__.pow(2) * x_.pow(Atom::num(2) * &n_));
            rubi_simp(&(x_ * argument.pow(&p_)), x_)
                    + rubi_star(&b__ * &c__ * &n_ * &p_, rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_5347(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5347,
        source: "Int[(a_.+b_.*ArcTan[c_.*x_^n_])^p_,x_Symbol] :=
          Int[ExpandIntegrand[(a+(I*b*Log[1-I*c*x^n])/2-(I*b*Log[1+I*c*x^n])/2)^p,x],x] /;
        FreeQ[{a,b,c},x] && IGtQ[p,1] && IGtQ[n,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, n_, p_, x_],
        optional: [a__, b__, c__],
        when: {
            freeq!([a__, b__, c__], x_)
                && igtq!(p_, 1)
                && igtq!(n_, 0)
        },
        rhs: {
            let i = Atom::i();
            let power = x_.pow(&n_);
            let payload = (&a__ + &i * &b__ * (Atom::num(1) - &i * &c__ * &power).log() / Atom::num(2)
                - &i * &b__ * (Atom::num(1) + &i * &c__ * power).log() / Atom::num(2))
                .pow(&p_);
            let expanded = rubi_expand_integrand(&payload, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_5348(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5348,
        source: "Int[(a_.+b_.*ArcCot[c_.*x_^n_])^p_,x_Symbol] :=
          Int[ExpandIntegrand[(a+(I*b*Log[1-I*x^(-n)/c])/2-(I*b*Log[1+I*x^(-n)/c])/2)^p,x],x] /;
        FreeQ[{a,b,c},x] && IGtQ[p,1] && IGtQ[n,0]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, n_, p_, x_],
        optional: [a__, b__, c__],
        when: {
            freeq!([a__, b__, c__], x_)
                && igtq!(p_, 1)
                && igtq!(n_, 0)
        },
        rhs: {
            let i = Atom::i();
            let reciprocal_power = x_.pow(-&n_) / &c__;
            let payload = (&a__ + &i * &b__ * (Atom::num(1) - &i * &reciprocal_power).log() / Atom::num(2)
                - &i * &b__ * (Atom::num(1) + &i * reciprocal_power).log() / Atom::num(2))
                .pow(&p_);
            let expanded = rubi_expand_integrand(&payload, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_5349(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5349,
        source: "Int[(a_.+b_.*ArcTan[c_.*x_^n_])^p_,x_Symbol] :=
          Int[(a+b*ArcCot[x^(-n)/c])^p,x] /;
        FreeQ[{a,b,c},x] && IGtQ[p,1] && ILtQ[n,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, n_, p_, x_],
        optional: [a__, b__, c__],
        when: {
            freeq!([a__, b__, c__], x_)
                && igtq!(p_, 1)
                && iltq!(n_, 0)
        },
        rhs: {
            let transformed = (&a__ + &b__ * (x_.pow(-&n_) / &c__).acot()).pow(&p_);
            rubi_rhs_int(&transformed, x_)
        },
    ));
}

fn push_rules_rule_5350(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5350,
        source: "Int[(a_.+b_.*ArcCot[c_.*x_^n_])^p_,x_Symbol] :=
          Int[(a+b*ArcTan[x^(-n)/c])^p,x] /;
        FreeQ[{a,b,c},x] && IGtQ[p,1] && ILtQ[n,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, n_, p_, x_],
        optional: [a__, b__, c__],
        when: {
            freeq!([a__, b__, c__], x_)
                && igtq!(p_, 1)
                && iltq!(n_, 0)
        },
        rhs: {
            let transformed = (&a__ + &b__ * (x_.pow(-&n_) / &c__).atan()).pow(&p_);
            rubi_rhs_int(&transformed, x_)
        },
    ));
}

fn push_rules_rule_5351(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5351,
        source: "Int[(a_.+b_.*ArcTan[c_.*x_^n_])^p_,x_Symbol] :=
          With[{k=Denominator[n]},
          k \\[Star] Subst[Int[x^(k-1)*(a+b*ArcTan[c*x^(k*n)])^p,x],x,x^(1/k)]] /;
        FreeQ[{a,b,c},x] && IGtQ[p,1] && FractionQ[n]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, n_, p_, x_],
        optional: [a__, b__, c__],
        when: {
            freeq!([a__, b__, c__], x_)
                && igtq!(p_, 1)
                && fractionq!(n_)
        },
        rhs: {
            let k_i = rubi_denominator(&n_).rubi_rhs();
            let k = Atom::num(k_i);
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let transformed_integrand = sub_atom.pow(&k - Atom::num(1))
                * (&a__ + &b__ * (&c__ * sub_atom.pow(&k * &n_)).atan()).pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);
            rubi_star(k, rubi_subst(&transformed, substitution_symbol, x_.pow(Atom::num(1) / k_i)))
        },
    ));
}

fn push_rules_rule_5352(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5352,
        source: "Int[(a_.+b_.*ArcCot[c_.*x_^n_])^p_,x_Symbol] :=
          With[{k=Denominator[n]},
          k \\[Star] Subst[Int[x^(k-1)*(a+b*ArcCot[c*x^(k*n)])^p,x],x,x^(1/k)]] /;
        FreeQ[{a,b,c},x] && IGtQ[p,1] && FractionQ[n]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, n_, p_, x_],
        optional: [a__, b__, c__],
        when: {
            freeq!([a__, b__, c__], x_)
                && igtq!(p_, 1)
                && fractionq!(n_)
        },
        rhs: {
            let k_i = rubi_denominator(&n_).rubi_rhs();
            let k = Atom::num(k_i);
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let transformed_integrand = sub_atom.pow(&k - Atom::num(1))
                * (&a__ + &b__ * (&c__ * sub_atom.pow(&k * &n_)).acot()).pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);
            rubi_star(k, rubi_subst(&transformed, substitution_symbol, x_.pow(Atom::num(1) / k_i)))
        },
    ));
}

fn push_rules_rule_5353(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5353,
        source: "Int[(a_.+b_.*ArcTan[c_.*x_^n_.])^p_,x_Symbol] :=
          Unintegrable[(a+b*ArcTan[c*x^n])^p,x] /;
        FreeQ[{a,b,c,n,p},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, n_, p_, x_],
        optional: [a__, b__, c__, n_],
        when: { freeq!([a__, b__, c__, n_, p_], x_) },
        rhs: {
            let integrand = (&a__ + &b__ * (&c__ * x_.pow(&n_)).atan()).pow(&p_);
            rubi_unintegrable(integrand, x_)
        },
    ));
}

fn push_rules_rule_5354(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5354,
        source: "Int[(a_.+b_.*ArcCot[c_.*x_^n_.])^p_,x_Symbol] :=
          Unintegrable[(a+b*ArcCot[c*x^n])^p,x] /;
        FreeQ[{a,b,c,n,p},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, n_, p_, x_],
        optional: [a__, b__, c__, n_],
        when: { freeq!([a__, b__, c__, n_, p_], x_) },
        rhs: {
            let integrand = (&a__ + &b__ * (&c__ * x_.pow(&n_)).acot()).pow(&p_);
            rubi_unintegrable(integrand, x_)
        },
    ));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn downvalues_5345_through_5354_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .filter(|order| (5345..=5354).contains(order))
            .collect::<Vec<_>>();
        assert_eq!(orders, (5345..=5354).collect::<Vec<_>>());
    }
}

// Generated shared pattern builders.

#[inline(never)]
fn rubi_shared_pattern_0(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (a__ + b__ * (c__ * x_.pow(n_)).acot()).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (a__ + b__ * (c__ * x_.pow(n_)).atan()).pow(p_)
}
