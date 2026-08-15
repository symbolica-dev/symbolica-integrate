use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_6190(rules);
    push_rules_rule_6191(rules);
    push_rules_rule_6192(rules);
    push_rules_rule_6193(rules);
    push_rules_rule_6194(rules);
    push_rules_rule_6195(rules);
    push_rules_rule_6196(rules);
}

fn push_rules_rule_6190(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, n_, x_);
    rules.push(rubi_rule!(
        order: 6190,
        source: "Int[(a_.+b_.*ArcSinh[c_.*x_])^n_./x_,x_Symbol] :=
          1/b \\[Star] Subst[Int[x^n*Coth[-a/b+x/b],x],x,a+b*ArcSinh[c*x]] /;
        FreeQ[{a,b,c},x] && IGtQ[n,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (a__ + b__ * (c__ * x_).asinh()).pow(n_) / x_,
        with: [a__, b__, c__, n_, x_],
        optional: [a__, b__, c__, n_],
        when: { freeq!([a__, b__, c__], x_) && igtq!(n_, 0) },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let substitution_integrand =
                sub_atom.pow(&n_) * (-&a__ / &b__ + &sub_atom / &b__).coth();
            let substitution_primitive =
                rubi_rhs_int(&substitution_integrand, substitution_symbol);
            let substitution = a__ + &b__ * (c__ * x_).asinh();

            let substituted =
                rubi_subst(&substitution_primitive, substitution_symbol, substitution);
            rubi_star(Atom::num(1) / b__, substituted)
        },
    ));
}

fn push_rules_rule_6191(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 6191,
        source: "Int[(d_.*x_)^m_.*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
          (d*x)^(m+1)*(a+b*ArcSinh[c*x])^n/(d*(m+1)) -
          b*c*n/(d*(m+1)) \\[Star] Int[(d*x)^(m+1)*(a+b*ArcSinh[c*x])^(n-1)/Sqrt[1+c^2*x^2],x] /;
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
            let argument = &a__ + &b__ * (&c__ * x_).asinh();
            let scaled_next = (&d__ * x_).pow(&m_ + Atom::num(1));
            let recursive_integrand =
                &scaled_next * argument.pow(&n_ - Atom::num(1))
                    / (Atom::num(1) + c__.pow(2) * x_.pow(2)).sqrt();
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            rubi_simp(&(scaled_next * argument.pow(&n_) / (&d__ * (&m_ + Atom::num(1)))), x_)
                    - rubi_star(&b__ * &c__ * n_ / (&d__ * (m_ + Atom::num(1))), recursive)
        },
    ));
}

fn push_rules_rule_6192(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 6192,
        source: "Int[x_^m_.*(a_.+b_.*ArcSinh[c_.*x_])^n_,x_Symbol] :=
          x^(m+1)*(a+b*ArcSinh[c*x])^n/(m+1) -
          b*c*n/(m+1) \\[Star] Int[x^(m+1)*(a+b*ArcSinh[c*x])^(n-1)/Sqrt[1+c^2*x^2],x] /;
        FreeQ[{a,b,c},x] && IGtQ[m,0] && GtQ[n,0]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [m_, a__, b__, c__, n_, x_],
        optional: [a__, b__, c__, m_],
        when: { freeq!([a__, b__, c__], x_) && igtq!(m_, 0) && gtq!(n_, 0) },
        rhs: {
            let argument = &a__ + &b__ * (&c__ * x_).asinh();
            let recursive_integrand =
                x_.pow(&m_ + Atom::num(1)) * argument.pow(&n_ - Atom::num(1))
                    / (Atom::num(1) + c__.pow(2) * x_.pow(2)).sqrt();
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            rubi_simp(&(x_.pow(&m_ + Atom::num(1)) * argument.pow(&n_)
                    / (&m_ + Atom::num(1))), x_)
                    - rubi_star(&b__ * &c__ * n_ / (m_ + Atom::num(1)), recursive)
        },
    ));
}

fn push_rules_rule_6193(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 6193,
        source: "Int[x_^m_.*(a_.+b_.*ArcSinh[c_.*x_])^n_,x_Symbol] :=
          x^m*Sqrt[1+c^2*x^2]*(a+b*ArcSinh[c*x])^(n+1)/(b*c*(n+1)) -
          1/(b^2*c^(m+1)*(n+1)) \\[Star]
            Subst[Int[ExpandTrigReduce[x^(n+1),Sinh[-a/b+x/b]^(m-1)*(m+(m+1)*Sinh[-a/b+x/b]^2),x],x],x,a+b*ArcSinh[c*x]] /;
        FreeQ[{a,b,c},x] && IGtQ[m,0] && GeQ[n,-2] && LtQ[n,-1]",
        desc: "Integration by parts and integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [m_, a__, b__, c__, n_, x_],
        optional: [a__, b__, c__, m_],
        when: {
            freeq!([a__, b__, c__], x_)
                && igtq!(m_, 0)
                && geq!(n_, -2)
                && ltq!(n_, -1)
        },
        rhs: {
            let argument = &a__ + &b__ * (&c__ * x_).asinh();
            let radical = (Atom::num(1) + c__.pow(2) * x_.pow(2)).sqrt();
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let hyperbolic_argument = -&a__ / &b__ + &sub_atom / &b__;
            let sinh_power = &hyperbolic_argument.sinh().pow(&m_ - Atom::num(1));
            let substitution_integrand = sub_atom.pow(&n_ + Atom::num(1))
                * sinh_power
                * (&m_ + (&m_ + Atom::num(1)) * hyperbolic_argument.sinh().pow(2));
            let substitution_primitive =
                rubi_rhs_int(&substitution_integrand, substitution_symbol);
            let substitution = a__ + &b__ * (&c__ * x_).asinh();
            let substituted =
                rubi_subst(&substitution_primitive, substitution_symbol, substitution);
            let coefficient = Atom::num(1)
                / (b__.pow(2) * c__.pow(&m_ + Atom::num(1)) * (&n_ + Atom::num(1)));

            rubi_simp(&(x_.pow(&m_) * radical * argument.pow(&n_ + Atom::num(1))
                    / (&b__ * &c__ * (&n_ + Atom::num(1)))), x_)
                    - rubi_star(coefficient, substituted)
        },
    ));
}

fn push_rules_rule_6194(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 6194,
        source: "Int[x_^m_.*(a_.+b_.*ArcSinh[c_.*x_])^n_,x_Symbol] :=
          x^m*Sqrt[1+c^2*x^2]*(a+b*ArcSinh[c*x])^(n+1)/(b*c*(n+1)) -
          m/(b*c*(n+1)) \\[Star] Int[x^(m-1)*(a+b*ArcSinh[c*x])^(n+1)/Sqrt[1+c^2*x^2],x] -
          c*(m+1)/(b*(n+1)) \\[Star] Int[x^(m+1)*(a+b*ArcSinh[c*x])^(n+1)/Sqrt[1+c^2*x^2],x] /;
        FreeQ[{a,b,c},x] && IGtQ[m,0] && LtQ[n,-2]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [m_, a__, b__, c__, n_, x_],
        optional: [a__, b__, c__, m_],
        when: { freeq!([a__, b__, c__], x_) && igtq!(m_, 0) && ltq!(n_, -2) },
        rhs: {
            let argument = &a__ + &b__ * (&c__ * x_).asinh();
            let radical = (Atom::num(1) + c__.pow(2) * x_.pow(2)).sqrt();
            let recursive_1 = rubi_rhs_int(
                &(x_.pow(&m_ - Atom::num(1))
                    * argument.pow(&n_ + Atom::num(1))
                    / &radical),
                x_,
            );
            let recursive_2 = rubi_rhs_int(
                &(x_.pow(&m_ + Atom::num(1))
                    * argument.pow(&n_ + Atom::num(1))
                    / &radical),
                x_,
            );
            rubi_simp(&(x_.pow(&m_) * &radical * argument.pow(&n_ + Atom::num(1))
                    / (&b__ * &c__ * (&n_ + Atom::num(1)))), x_)
                    - rubi_star(&m_ / (&b__ * &c__ * (&n_ + Atom::num(1))), recursive_1)
                    - rubi_star(&c__ * (&m_ + Atom::num(1)) / (&b__ * (&n_ + Atom::num(1))), recursive_2)
        },
    ));
}

fn push_rules_rule_6195(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 6195,
        source: "Int[x_^m_.*(a_.+b_.*ArcSinh[c_.*x_])^n_,x_Symbol] :=
          1/(b*c^(m+1)) \\[Star] Subst[Int[x^n*Sinh[-a/b+x/b]^m*Cosh[-a/b+x/b],x],x,a+b*ArcSinh[c*x]] /;
        FreeQ[{a,b,c,n},x] && IGtQ[m,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [m_, a__, b__, c__, n_, x_],
        optional: [a__, b__, c__, m_],
        when: { freeq!([a__, b__, c__, n_], x_) && igtq!(m_, 0) },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let hyperbolic_argument = -&a__ / &b__ + &sub_atom / &b__;
            let substitution_integrand = sub_atom.pow(&n_)
                * &hyperbolic_argument.sinh().pow(&m_)
                * hyperbolic_argument.cosh();
            let substitution_primitive =
                rubi_rhs_int(&substitution_integrand, substitution_symbol);
            let substitution = a__ + &b__ * (&c__ * x_).asinh();
            let substituted =
                rubi_subst(&substitution_primitive, substitution_symbol, substitution);

            rubi_star(Atom::num(1) / (&b__ * c__.pow(&m_ + Atom::num(1))), substituted)
        },
    ));
}

fn push_rules_rule_6196(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 6196,
        source: "Int[(d_.*x_)^m_.*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
          Unintegrable[(d*x)^m*(a+b*ArcSinh[c*x])^n,x] /;
        FreeQ[{a,b,c,d,m,n},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [d__, m_, a__, b__, c__, n_, x_],
        optional: [d__, m_, a__, b__, c__, n_],
        when: { freeq!([a__, b__, c__, d__, m_, n_], x_) },
        rhs: {
            let integrand =
                (d__ * x_).pow(&m_) * (a__ + b__ * (c__ * x_).asinh()).pow(&n_);
            rubi_unintegrable(integrand, x_)
        },
    ));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn downvalues_6190_through_6196_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .filter(|order| (6190..=6196).contains(order))
            .collect::<Vec<_>>();
        assert_eq!(orders, (6190..=6196).collect::<Vec<_>>());
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
    (d__ * x_).pow(m_) * (a__ + b__ * (c__ * x_).asinh()).pow(n_)
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    x_.pow(m_) * (a__ + b__ * (c__ * x_).asinh()).pow(n_)
}
