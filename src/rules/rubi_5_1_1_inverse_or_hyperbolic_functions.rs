use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_5130(rules);
    push_rules_rule_5131(rules);
    push_rules_rule_5132(rules);
    push_rules_rule_5133(rules);
    push_rules_rule_5134(rules);
    push_rules_rule_5135(rules);
}

fn push_rules_rule_5130(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, n_, x_);
    rules.push(rubi_rule!(
        order: 5130,
        source: "Int[(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
          x*(a+b*ArcSin[c*x])^n -
          b*c*n \\[Star] Int[x*(a+b*ArcSin[c*x])^(n-1)/Sqrt[1-c^2*x^2],x] /;
        FreeQ[{a,b,c},x] && GtQ[n,0]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, n_, x_],
        optional: [a__, b__, c__, n_],
        when: { freeq!([a__, b__, c__], x_) && gtq!(n_, 0) },
        rhs: {
            let argument = &a__ + &b__ * (&c__ * x_).asin();
            let radical = (Atom::num(1) - c__.pow(2) * x_.pow(2)).sqrt();
            let recursive_integrand = x_ * argument.pow(&n_ - Atom::num(1)) / radical;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            rubi_simp(&(x_ * argument.pow(&n_)), x_)
                    + rubi_star(-&b__ * &c__ * &n_, recursive)
        },
    ));
}

fn push_rules_rule_5131(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, n_, x_);
    rules.push(rubi_rule!(
        order: 5131,
        source: "Int[(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
          x*(a+b*ArcCos[c*x])^n +
          b*c*n \\[Star] Int[x*(a+b*ArcCos[c*x])^(n-1)/Sqrt[1-c^2*x^2],x] /;
        FreeQ[{a,b,c},x] && GtQ[n,0]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, n_, x_],
        optional: [a__, b__, c__, n_],
        when: { freeq!([a__, b__, c__], x_) && gtq!(n_, 0) },
        rhs: {
            let argument = &a__ + &b__ * (&c__ * x_).acos();
            let radical = (Atom::num(1) - c__.pow(2) * x_.pow(2)).sqrt();
            let recursive_integrand = x_ * argument.pow(&n_ - Atom::num(1)) / radical;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            rubi_simp(&(x_ * argument.pow(&n_)), x_)
                    + rubi_star(&b__ * &c__ * &n_, recursive)
        },
    ));
}

fn push_rules_rule_5132(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, n_, x_);
    rules.push(rubi_rule!(
        order: 5132,
        source: "Int[(a_.+b_.*ArcSin[c_.*x_])^n_,x_Symbol] :=
          Sqrt[1-c^2*x^2]*(a+b*ArcSin[c*x])^(n+1)/(b*c*(n+1)) +
          c/(b*(n+1)) \\[Star] Int[x*(a+b*ArcSin[c*x])^(n+1)/Sqrt[1-c^2*x^2],x] /;
        FreeQ[{a,b,c},x] && LtQ[n,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, n_, x_],
        optional: [a__, b__, c__],
        when: { freeq!([a__, b__, c__], x_) && ltq!(n_, -1) },
        rhs: {
            let argument = &a__ + &b__ * (&c__ * x_).asin();
            let radical = (Atom::num(1) - c__.pow(2) * x_.pow(2)).sqrt();
            let recursive_integrand =
                x_ * argument.pow(&n_ + Atom::num(1)) / &radical;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            rubi_simp(&(radical * argument.pow(&n_ + Atom::num(1)) / (&b__ * &c__ * (&n_ + Atom::num(1)))), x_)
                    + rubi_star(&c__ / (&b__ * (&n_ + Atom::num(1))), recursive)
        },
    ));
}

fn push_rules_rule_5133(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, n_, x_);
    rules.push(rubi_rule!(
        order: 5133,
        source: "Int[(a_.+b_.*ArcCos[c_.*x_])^n_,x_Symbol] :=
          -Sqrt[1-c^2*x^2]*(a+b*ArcCos[c*x])^(n+1)/(b*c*(n+1)) -
          c/(b*(n+1)) \\[Star] Int[x*(a+b*ArcCos[c*x])^(n+1)/Sqrt[1-c^2*x^2],x] /;
        FreeQ[{a,b,c},x] && LtQ[n,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, n_, x_],
        optional: [a__, b__, c__],
        when: { freeq!([a__, b__, c__], x_) && ltq!(n_, -1) },
        rhs: {
            let argument = &a__ + &b__ * (&c__ * x_).acos();
            let radical = (Atom::num(1) - c__.pow(2) * x_.pow(2)).sqrt();
            let recursive_integrand =
                x_ * argument.pow(&n_ + Atom::num(1)) / &radical;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            rubi_simp(&(-radical * argument.pow(&n_ + Atom::num(1)) / (&b__ * &c__ * (&n_ + Atom::num(1)))), x_)
                    + rubi_star(-&c__ / (&b__ * (&n_ + Atom::num(1))), recursive)
        },
    ));
}

fn push_rules_rule_5134(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, n_, x_);
    rules.push(rubi_rule!(
        order: 5134,
        source: "Int[(a_.+b_.*ArcSin[c_.*x_])^n_,x_Symbol] :=
          1/(b*c) \\[Star] Subst[Int[x^n*Cos[-a/b+x/b],x],x,a+b*ArcSin[c*x]] /;
        FreeQ[{a,b,c,n},x]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, n_, x_],
        optional: [a__, b__, c__],
        when: { freeq!([a__, b__, c__, n_], x_) },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let payload = sub_atom.pow(&n_) * ((-&a__ / &b__) + &sub_atom / &b__).cos();
            let primitive = rubi_rhs_int(&payload, sub);
            let substituted = rubi_subst(&primitive, sub, &a__ + &b__ * (&c__ * x_).asin());
            rubi_star(Atom::num(1) / (&b__ * &c__), substituted)
        },
    ));
}

fn push_rules_rule_5135(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, n_, x_);
    rules.push(rubi_rule!(
        order: 5135,
        source: "Int[(a_.+b_.*ArcCos[c_.*x_])^n_,x_Symbol] :=
          -1/(b*c) \\[Star] Subst[Int[x^n*Sin[-a/b+x/b],x],x,a+b*ArcCos[c*x]] /;
        FreeQ[{a,b,c,n},x]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, n_, x_],
        optional: [a__, b__, c__],
        when: { freeq!([a__, b__, c__, n_], x_) },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let payload = sub_atom.pow(&n_) * ((-&a__ / &b__) + &sub_atom / &b__).sin();
            let primitive = rubi_rhs_int(&payload, sub);
            let substituted = rubi_subst(&primitive, sub, &a__ + &b__ * (&c__ * x_).acos());
            rubi_star(-Atom::num(1) / (&b__ * &c__), substituted)
        },
    ));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn downvalues_5130_through_5135_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .filter(|order| (5130..=5135).contains(order))
            .collect::<Vec<_>>();
        assert_eq!(orders, (5130..=5135).collect::<Vec<_>>());
    }
}

// Generated shared pattern builders.

#[inline(never)]
fn rubi_shared_pattern_0(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    (a__ + b__ * (c__ * x_).acos()).pow(n_)
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    (a__ + b__ * (c__ * x_).asin()).pow(n_)
}
