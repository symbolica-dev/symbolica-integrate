use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_6187(rules);
    push_rules_rule_6188(rules);
    push_rules_rule_6189(rules);
}

fn push_rules_rule_6187(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, n_, x_);
    rules.push(rubi_rule!(
        order: 6187,
        source: "Int[(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
          x*(a+b*ArcSinh[c*x])^n -
          b*c*n \\[Star] Int[x*(a+b*ArcSinh[c*x])^(n-1)/Sqrt[1+c^2*x^2],x] /;
        FreeQ[{a,b,c},x] && GtQ[n,0]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, n_, x_],
        optional: [a__, b__, c__, n_],
        when: { freeq!([a__, b__, c__], x_) && gtq!(n_, 0) },
        rhs: {
            let argument = &a__ + &b__ * (&c__ * x_).asinh();
            let recursive_integrand =
                x_ * argument.pow(&n_ - Atom::num(1))
                    / (Atom::num(1) + c__.pow(2) * x_.pow(2)).sqrt();
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            rubi_simp(&(x_ * argument.pow(&n_)), x_)
                    - rubi_star(b__ * c__ * n_, recursive)
        },
    ));
}

fn push_rules_rule_6188(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, n_, x_);
    rules.push(rubi_rule!(
        order: 6188,
        source: "Int[(a_.+b_.*ArcSinh[c_.*x_])^n_,x_Symbol] :=
          Sqrt[1+c^2*x^2]*(a+b*ArcSinh[c*x])^(n+1)/(b*c*(n+1)) -
          c/(b*(n+1)) \\[Star] Int[x*(a+b*ArcSinh[c*x])^(n+1)/Sqrt[1+c^2*x^2],x] /;
        FreeQ[{a,b,c},x] && LtQ[n,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, n_, x_],
        optional: [a__, b__, c__],
        when: { freeq!([a__, b__, c__], x_) && ltq!(n_, -1) },
        rhs: {
            let radical = (Atom::num(1) + c__.pow(2) * x_.pow(2)).sqrt();
            let argument = &a__ + &b__ * (&c__ * x_).asinh();
            let recursive_integrand =
                x_ * argument.pow(&n_ + Atom::num(1)) / &radical;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            rubi_simp(&(radical * argument.pow(&n_ + Atom::num(1))
                    / (&b__ * &c__ * (&n_ + Atom::num(1)))), x_)
                    - rubi_star(c__ / (&b__ * (n_ + Atom::num(1))), recursive)
        },
    ));
}

fn push_rules_rule_6189(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, n_, x_);
    rules.push(rubi_rule!(
        order: 6189,
        source: "Int[(a_.+b_.*ArcSinh[c_.*x_])^n_,x_Symbol] :=
          1/(b*c) \\[Star] Subst[Int[x^n*Cosh[-a/b+x/b],x],x,a+b*ArcSinh[c*x]] /;
        FreeQ[{a,b,c,n},x]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, n_, x_],
        optional: [a__, b__, c__],
        when: { freeq!([a__, b__, c__, n_], x_) },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let substitution_integrand =
                sub_atom.pow(&n_) * (-&a__ / &b__ + &sub_atom / &b__).cosh();
            let substitution_primitive =
                rubi_rhs_int(&substitution_integrand, substitution_symbol);
            let substitution = a__ + &b__ * (&c__ * x_).asinh();

            let substituted =
                rubi_subst(&substitution_primitive, substitution_symbol, substitution);
            rubi_star(Atom::num(1) / (b__ * c__), substituted)
        },
    ));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn downvalues_6187_through_6189_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .filter(|order| (6187..=6189).contains(order))
            .collect::<Vec<_>>();
        assert_eq!(orders, (6187..=6189).collect::<Vec<_>>());
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
    (a__ + b__ * (c__ * x_).asinh()).pow(n_)
}
