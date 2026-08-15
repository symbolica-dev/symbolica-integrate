use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_6294(rules);
    push_rules_rule_6295(rules);
    push_rules_rule_6296(rules);
}

fn push_rules_rule_6294(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, n_, x_);
    rules.push(rubi_rule!(
        order: 6294,
        source: "Int[(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
          x*(a+b*ArcCosh[c*x])^n -
          b*c*n \\[Star] Int[x*(a+b*ArcCosh[c*x])^(n-1)/(Sqrt[1+c*x]*Sqrt[-1+c*x]),x] /;
        FreeQ[{a,b,c},x] && GtQ[n,0]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, n_, x_],
        optional: [a__, b__, c__, n_],
        when: { freeq!([a__, b__, c__], x_) && gtq!(n_, 0) },
        rhs: {
            let argument = &a__ + &b__ * (&c__ * x_).acosh();
            let recursive = x_ * argument.pow(&n_ - Atom::num(1))
                / ((Atom::num(1) + &c__ * x_).sqrt() * (-Atom::num(1) + &c__ * x_).sqrt());
            rubi_simp(&(x_ * argument.pow(&n_)), x_)
                    - rubi_star(&b__ * &c__ * &n_, rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_6295(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, n_, x_);
    rules.push(rubi_rule!(
        order: 6295,
        source: "Int[(a_.+b_.*ArcCosh[c_.*x_])^n_,x_Symbol] :=
          Sqrt[1+c*x]*Sqrt[-1+c*x]*(a+b*ArcCosh[c*x])^(n+1)/(b*c*(n+1)) -
          c/(b*(n+1)) \\[Star] Int[x*(a+b*ArcCosh[c*x])^(n+1)/(Sqrt[1+c*x]*Sqrt[-1+c*x]),x] /;
        FreeQ[{a,b,c},x] && LtQ[n,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, n_, x_],
        optional: [a__, b__, c__],
        when: { freeq!([a__, b__, c__], x_) && ltq!(n_, -1) },
        rhs: {
            let argument = &a__ + &b__ * (&c__ * x_).acosh();
            let sqrt_product =
                (Atom::num(1) + &c__ * x_).sqrt() * (-Atom::num(1) + &c__ * x_).sqrt();
            let recursive = x_ * argument.pow(&n_ + Atom::num(1)) / &sqrt_product;
            rubi_simp(&(sqrt_product * argument.pow(&n_ + Atom::num(1)) / (&b__ * &c__ * (&n_ + Atom::num(1)))), x_)
                    - rubi_star(&c__ / (&b__ * (&n_ + Atom::num(1))), rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_6296(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, n_, x_);
    rules.push(rubi_rule!(
        order: 6296,
        source: "Int[(a_.+b_.*ArcCosh[c_.*x_])^n_,x_Symbol] :=
          1/(b*c) \\[Star] Subst[Int[x^n*Sinh[-a/b+x/b],x],x,a+b*ArcCosh[c*x]] /;
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
            let payload = sub_atom.pow(&n_) * (-&a__ / &b__ + &sub_atom / &b__).sinh();
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            let substituted = rubi_subst(
                &primitive,
                substitution_symbol,
                &a__ + &b__ * (&c__ * x_).acosh(),
            );
            rubi_star(Atom::num(1) / (&b__ * &c__), substituted)
        },
    ));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn downvalues_6294_through_6296_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .collect::<Vec<_>>();
        assert_eq!(orders, (6294..=6296).collect::<Vec<_>>());
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
    (a__ + b__ * (c__ * x_).acosh()).pow(n_)
}
