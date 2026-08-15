use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_6297(rules);
    push_rules_rule_6298(rules);
    push_rules_rule_6299(rules);
    push_rules_rule_6300(rules);
    push_rules_rule_6301(rules);
    push_rules_rule_6302(rules);
    push_rules_rule_6303(rules);
}

fn push_rules_rule_6297(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, n_, x_);
    rules.push(rubi_rule!(
        order: 6297,
        source: "Int[(a_.+b_.*ArcCosh[c_.*x_])^n_./x_,x_Symbol] :=
          1/b \\[Star] Subst[Int[x^n*Tanh[-a/b+x/b],x],x,a+b*ArcCosh[c*x]] /;
        FreeQ[{a,b,c},x] && IGtQ[n,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (a__ + b__ * (c__ * x_).acosh()).pow(n_) / x_,
        with: [a__, b__, c__, n_, x_],
        optional: [a__, b__, c__, n_],
        when: { freeq!([a__, b__, c__], x_) && igtq!(n_, 0) },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let payload = sub_atom.pow(&n_) * (-&a__ / &b__ + &sub_atom / &b__).tanh();
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            let substituted = rubi_subst(
                &primitive,
                substitution_symbol,
                &a__ + &b__ * (&c__ * x_).acosh(),
            );
            rubi_star(Atom::num(1) / &b__, substituted)
        },
    ));
}

fn push_rules_rule_6298(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 6298,
        source: "Int[(d_.*x_)^m_.*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
          (d*x)^(m+1)*(a+b*ArcCosh[c*x])^n/(d*(m+1)) -
          b*c*n/(d*(m+1)) \\[Star] Int[(d*x)^(m+1)*(a+b*ArcCosh[c*x])^(n-1)/(Sqrt[1+c*x]*Sqrt[-1+c*x]),x] /;
        FreeQ[{a,b,c,d,m},x] && IGtQ[n,0] && NeQ[m,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [d__, m_, a__, b__, c__, n_, x_],
        optional: [d__, m_, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, m_], x_)
                && igtq!(n_, 0)
                && neq!(m_, -1)
        },
        rhs: {
            let scaled = &d__ * x_;
            let argument = &a__ + &b__ * (&c__ * x_).acosh();
            let denominator = (Atom::num(1) + &c__ * x_).sqrt() * (-Atom::num(1) + &c__ * x_).sqrt();
            let recursive = scaled.pow(&m_ + Atom::num(1)) * argument.pow(&n_ - Atom::num(1)) / denominator;
            rubi_simp(&(scaled.pow(&m_ + Atom::num(1)) * argument.pow(&n_) / (&d__ * (&m_ + Atom::num(1)))), x_)
                    - rubi_star(&b__ * &c__ * &n_ / (&d__ * (&m_ + Atom::num(1))), rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_6299(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 6299,
        source: "Int[x_^m_.*(a_.+b_.*ArcCosh[c_.*x_])^n_,x_Symbol] :=
          x^(m+1)*(a+b*ArcCosh[c*x])^n/(m+1) -
          b*c*n/(m+1) \\[Star] Int[x^(m+1)*(a+b*ArcCosh[c*x])^(n-1)/(Sqrt[1+c*x]*Sqrt[-1+c*x]),x] /;
        FreeQ[{a,b,c},x] && IGtQ[m,0] && GtQ[n,0]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [m_, a__, b__, c__, n_, x_],
        optional: [m_, a__, b__, c__],
        when: { freeq!([a__, b__, c__], x_) && igtq!(m_, 0) && gtq!(n_, 0) },
        rhs: {
            let argument = &a__ + &b__ * (&c__ * x_).acosh();
            let denominator = (Atom::num(1) + &c__ * x_).sqrt() * (-Atom::num(1) + &c__ * x_).sqrt();
            let recursive = x_.pow(&m_ + Atom::num(1)) * argument.pow(&n_ - Atom::num(1)) / denominator;
            rubi_simp(&(x_.pow(&m_ + Atom::num(1)) * argument.pow(&n_) / (&m_ + Atom::num(1))), x_)
                    - rubi_star(&b__ * &c__ * &n_ / (&m_ + Atom::num(1)), rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_6300(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 6300,
        source: "Int[x_^m_.*(a_.+b_.*ArcCosh[c_.*x_])^n_,x_Symbol] :=
          x^m*Sqrt[1+c*x]*Sqrt[-1+c*x]*(a+b*ArcCosh[c*x])^(n+1)/(b*c*(n+1)) +
          1/(b^2*c^(m+1)*(n+1)) \\[Star]
            Subst[Int[ExpandTrigReduce[x^(n+1),Cosh[-a/b+x/b]^(m-1)*(m-(m+1)*Cosh[-a/b+x/b]^2),x],x],x,a+b*ArcCosh[c*x]] /;
        FreeQ[{a,b,c},x] && IGtQ[m,0] && GeQ[n,-2] && LtQ[n,-1]",
        desc: "Integration by parts and integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [m_, a__, b__, c__, n_, x_],
        optional: [m_, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__], x_)
                && igtq!(m_, 0)
                && geq!(n_, -2)
                && ltq!(n_, -1)
        },
        rhs: {
            let argument = &a__ + &b__ * (&c__ * x_).acosh();
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let hyperbolic_argument = -&a__ / &b__ + &sub_atom / &b__;
            let payload = sub_atom.pow(&n_ + Atom::num(1))
                * &hyperbolic_argument.cosh().pow(&m_ - Atom::num(1))
                * (&m_ - (&m_ + Atom::num(1)) * hyperbolic_argument.cosh().pow(2));
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            let substituted = rubi_subst(
                &primitive,
                substitution_symbol,
                &a__ + &b__ * (&c__ * x_).acosh(),
            );
            rubi_simp(&(x_.pow(&m_)
                    * (Atom::num(1) + &c__ * x_).sqrt()
                    * (-Atom::num(1) + &c__ * x_).sqrt()
                    * argument.pow(&n_ + Atom::num(1))
                    / (&b__ * &c__ * (&n_ + Atom::num(1)))), x_)
                    + rubi_star(Atom::num(1)
                            / (b__.pow(2)
                                * c__.pow(&m_ + Atom::num(1))
                                * (&n_ + Atom::num(1))), substituted)
        },
    ));
}

fn push_rules_rule_6301(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 6301,
        source: "Int[x_^m_.*(a_.+b_.*ArcCosh[c_.*x_])^n_,x_Symbol] :=
          x^m*Sqrt[1+c*x]*Sqrt[-1+c*x]*(a+b*ArcCosh[c*x])^(n+1)/(b*c*(n+1)) +
          m/(b*c*(n+1)) \\[Star] Int[x^(m-1)*(a+b*ArcCosh[c*x])^(n+1)/(Sqrt[1+c*x]*Sqrt[-1+c*x]),x] -
          c*(m+1)/(b*(n+1)) \\[Star] Int[x^(m+1)*(a+b*ArcCosh[c*x])^(n+1)/(Sqrt[1+c*x]*Sqrt[-1+c*x]),x] /;
        FreeQ[{a,b,c},x] && IGtQ[m,0] && LtQ[n,-2]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [m_, a__, b__, c__, n_, x_],
        optional: [m_, a__, b__, c__],
        when: { freeq!([a__, b__, c__], x_) && igtq!(m_, 0) && ltq!(n_, -2) },
        rhs: {
            let argument = &a__ + &b__ * (&c__ * x_).acosh();
            let denominator = (Atom::num(1) + &c__ * x_).sqrt() * (-Atom::num(1) + &c__ * x_).sqrt();
            let recursive_1 = x_.pow(&m_ - Atom::num(1)) * argument.pow(&n_ + Atom::num(1)) / &denominator;
            let recursive_2 = x_.pow(&m_ + Atom::num(1)) * argument.pow(&n_ + Atom::num(1)) / &denominator;
            rubi_simp(&(x_.pow(&m_) * denominator * argument.pow(&n_ + Atom::num(1)) / (&b__ * &c__ * (&n_ + Atom::num(1)))), x_)
                    + rubi_star(&m_ / (&b__ * &c__ * (&n_ + Atom::num(1))), rubi_rhs_int(&recursive_1, x_))
                    - rubi_star(&c__ * (&m_ + Atom::num(1))
                            / (&b__ * (&n_ + Atom::num(1))), rubi_rhs_int(&recursive_2, x_))
        },
    ));
}

fn push_rules_rule_6302(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 6302,
        source: "Int[x_^m_.*(a_.+b_.*ArcCosh[c_.*x_])^n_,x_Symbol] :=
          1/(b*c^(m+1)) \\[Star] Subst[Int[x^n*Cosh[-a/b+x/b]^m*Sinh[-a/b+x/b],x],x,a+b*ArcCosh[c*x]] /;
        FreeQ[{a,b,c,n},x] && IGtQ[m,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [m_, a__, b__, c__, n_, x_],
        optional: [m_, a__, b__, c__],
        when: { freeq!([a__, b__, c__, n_], x_) && igtq!(m_, 0) },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let hyperbolic_argument = -&a__ / &b__ + &sub_atom / &b__;
            let payload = sub_atom.pow(&n_) * &hyperbolic_argument.cosh().pow(&m_) * hyperbolic_argument.sinh();
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            let substituted = rubi_subst(
                &primitive,
                substitution_symbol,
                &a__ + &b__ * (&c__ * x_).acosh(),
            );
            rubi_star(Atom::num(1) / (&b__ * c__.pow(&m_ + Atom::num(1))), substituted)
        },
    ));
}

fn push_rules_rule_6303(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 6303,
        source: "Int[(d_.*x_)^m_.*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
          Unintegrable[(d*x)^m*(a+b*ArcCosh[c*x])^n,x] /;
        FreeQ[{a,b,c,d,m,n},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [d__, m_, a__, b__, c__, n_, x_],
        optional: [d__, m_, a__, b__, c__, n_],
        when: { freeq!([a__, b__, c__, d__, m_, n_], x_) },
        rhs: {
            let integrand = (&d__ * x_).pow(&m_) * (&a__ + &b__ * (&c__ * x_).acosh()).pow(&n_);
            rubi_unintegrable(integrand, x_)
        },
    ));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn downvalues_6297_through_6303_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .collect::<Vec<_>>();
        assert_eq!(orders, (6297..=6303).collect::<Vec<_>>());
    }
}

// Generated shared pattern builders.

#[inline(never)]
fn rubi_shared_pattern_0(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    (d__ * x_).pow(m_) * (a__ + b__ * (c__ * x_).acosh()).pow(n_)
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    x_.pow(m_) * (a__ + b__ * (c__ * x_).acosh()).pow(n_)
}
