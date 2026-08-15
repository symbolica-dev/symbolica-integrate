use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_6436(rules);
    push_rules_rule_6437(rules);
    push_rules_rule_6438(rules);
    push_rules_rule_6439(rules);
    push_rules_rule_6440(rules);
    push_rules_rule_6441(rules);
    push_rules_rule_6442(rules);
    push_rules_rule_6443(rules);
    push_rules_rule_6444(rules);
    push_rules_rule_6445(rules);
}

fn push_rules_rule_6436(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6436,
        source: "Int[(a_.+b_.*ArcTanh[c_.*x_^n_.])^p_.,x_Symbol] :=
          x*(a+b*ArcTanh[c*x^n])^p -
          b*c*n*p \\[Star] Int[x^n*(a+b*ArcTanh[c*x^n])^(p-1)/(1-c^2*x^(2*n)),x] /;
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
            let argument = &a__ + &b__ * (&c__ * x_.pow(&n_)).atanh();
            let recursive = x_.pow(&n_) * argument.pow(&p_ - Atom::num(1))
                / (Atom::num(1) - c__.pow(2) * x_.pow(Atom::num(2) * &n_));
            let coefficient = &b__ * &c__ * &n_ * &p_;
            rubi_simp(&(x_ * argument.pow(&p_)), x_)
                    - rubi_star(coefficient, rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_6437(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6437,
        source: "Int[(a_.+b_.*ArcCoth[c_.*x_^n_.])^p_.,x_Symbol] :=
          x*(a+b*ArcCoth[c*x^n])^p -
          b*c*n*p \\[Star] Int[x^n*(a+b*ArcCoth[c*x^n])^(p-1)/(1-c^2*x^(2*n)),x] /;
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
            let argument = &a__ + &b__ * (&c__ * x_.pow(&n_)).acoth();
            let recursive = x_.pow(&n_) * argument.pow(&p_ - Atom::num(1))
                / (Atom::num(1) - c__.pow(2) * x_.pow(Atom::num(2) * &n_));
            let coefficient = &b__ * &c__ * &n_ * &p_;
            rubi_simp(&(x_ * argument.pow(&p_)), x_)
                    - rubi_star(coefficient, rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_6438(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6438,
        source: "Int[(a_.+b_.*ArcTanh[c_.*x_^n_])^p_,x_Symbol] :=
          Int[ExpandIntegrand[(a+b*Log[1+c*x^n]/2-b*Log[1-c*x^n]/2)^p,x],x] /;
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
            let payload = (&a__ + &b__ * (Atom::num(1) + &c__ * x_.pow(&n_)).log() / Atom::num(2)
                - &b__ * (Atom::num(1) - &c__ * x_.pow(&n_)).log() / Atom::num(2))
                .pow(&p_);
            let expanded = rubi_expand_integrand(&payload, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_6439(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6439,
        source: "Int[(a_.+b_.*ArcCoth[c_.*x_^n_])^p_,x_Symbol] :=
          Int[ExpandIntegrand[(a+b*Log[1+x^(-n)/c]/2-b*Log[1-x^(-n)/c]/2)^p,x],x] /;
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
            let reciprocal_power = x_.pow(-&n_) / &c__;
            let payload = (&a__ + &b__ * (Atom::num(1) + &reciprocal_power).log() / Atom::num(2)
                - &b__ * (Atom::num(1) - reciprocal_power).log() / Atom::num(2))
                .pow(&p_);
            let expanded = rubi_expand_integrand(&payload, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_6440(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6440,
        source: "Int[(a_.+b_.*ArcTanh[c_.*x_^n_])^p_,x_Symbol] :=
          Int[(a+b*ArcCoth[x^(-n)/c])^p,x] /;
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
            let transformed = (&a__ + &b__ * (x_.pow(-&n_) / &c__).acoth()).pow(&p_);
            rubi_rhs_int(&transformed, x_)
        },
    ));
}

fn push_rules_rule_6441(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6441,
        source: "Int[(a_.+b_.*ArcCoth[c_.*x_^n_])^p_,x_Symbol] :=
          Int[(a+b*ArcTanh[x^(-n)/c])^p,x] /;
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
            let transformed = (&a__ + &b__ * (x_.pow(-&n_) / &c__).atanh()).pow(&p_);
            rubi_rhs_int(&transformed, x_)
        },
    ));
}

fn push_rules_rule_6442(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6442,
        source: "Int[(a_.+b_.*ArcTanh[c_.*x_^n_])^p_,x_Symbol] :=
          With[{k=Denominator[n]},
          k \\[Star] Subst[Int[x^(k-1)*(a+b*ArcTanh[c*x^(k*n)])^p,x],x,x^(1/k)]] /;
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
            let substitution_guard = fresh_substitution_symbol().rubi_rhs();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let transformed_integrand = sub_atom.pow(&k - Atom::num(1))
                * (&a__ + &b__ * (&c__ * sub_atom.pow(&k * &n_)).atanh()).pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);
            let substituted = rubi_subst(
                &transformed,
                substitution_symbol,
                x_.pow(Atom::num(1) / k_i),
            );
            rubi_star(k, substituted)
        },
    ));
}

fn push_rules_rule_6443(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6443,
        source: "Int[(a_.+b_.*ArcCoth[c_.*x_^n_])^p_,x_Symbol] :=
          With[{k=Denominator[n]},
          k \\[Star] Subst[Int[x^(k-1)*(a+b*ArcCoth[c*x^(k*n)])^p,x],x,x^(1/k)]] /;
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
            let substitution_guard = fresh_substitution_symbol().rubi_rhs();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let transformed_integrand = sub_atom.pow(&k - Atom::num(1))
                * (&a__ + &b__ * (&c__ * sub_atom.pow(&k * &n_)).acoth()).pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);
            let substituted = rubi_subst(
                &transformed,
                substitution_symbol,
                x_.pow(Atom::num(1) / k_i),
            );
            rubi_star(k, substituted)
        },
    ));
}

fn push_rules_rule_6444(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6444,
        source: "Int[(a_.+b_.*ArcTanh[c_.*x_^n_.])^p_,x_Symbol] :=
          Unintegrable[(a+b*ArcTanh[c*x^n])^p,x] /;
        FreeQ[{a,b,c,n,p},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, n_, p_, x_],
        optional: [a__, b__, c__, n_],
        when: { freeq!([a__, b__, c__, n_, p_], x_) },
        rhs: {
            let integrand = (&a__ + &b__ * (&c__ * x_.pow(&n_)).atanh()).pow(&p_);
            rubi_unintegrable(integrand, x_)
        },
    ));
}

fn push_rules_rule_6445(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6445,
        source: "Int[(a_.+b_.*ArcCoth[c_.*x_^n_.])^p_,x_Symbol] :=
          Unintegrable[(a+b*ArcCoth[c*x^n])^p,x] /;
        FreeQ[{a,b,c,n,p},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, n_, p_, x_],
        optional: [a__, b__, c__, n_],
        when: { freeq!([a__, b__, c__, n_, p_], x_) },
        rhs: {
            let integrand = (&a__ + &b__ * (&c__ * x_.pow(&n_)).acoth()).pow(&p_);
            rubi_unintegrable(integrand, x_)
        },
    ));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn downvalues_6436_through_6445_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .filter(|order| (6436..=6445).contains(order))
            .collect::<Vec<_>>();
        assert_eq!(orders, (6436..=6445).collect::<Vec<_>>());
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
    (a__ + b__ * (c__ * x_.pow(n_)).acoth()).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (a__ + b__ * (c__ * x_.pow(n_)).atanh()).pow(p_)
}
