use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_5943(rules);
    push_rules_rule_5944(rules);
    push_rules_rule_5945(rules);
    push_rules_rule_5946(rules);
    push_rules_rule_5947(rules);
    push_rules_rule_5948(rules);
}

fn push_rules_rule_5943(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, n_, x_);
    rules.push(rubi_rule!(
        order: 5943,
        source: "Int[Tanh[a_.+b_.*x_+c_.*x_^2]^n_.,x_Symbol] :=
          Integral[Tanh[a+b*x+c*x^2]^n,x] /;
        FreeQ[{a,b,c,n},x]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: (a__ + b__ * x_ + c__ * x_.pow(2)).tanh().pow(n_),
        with: [a__, b__, c__, n_, x_],
        optional: [a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, n_], x_)
        },
        rhs: {
            rubi_simp(&(rubi_deferred_integral(
                &(&a__ + &b__ * x_ + &c__ * x_.pow(2)).tanh().pow(&n_),
                x_,
            )), x_)
        },
    ));
}

fn push_rules_rule_5944(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, n_, x_);
    rules.push(rubi_rule!(
        order: 5944,
        source: "Int[Coth[a_.+b_.*x_+c_.*x_^2]^n_.,x_Symbol] :=
          Integral[Coth[a+b*x+c*x^2]^n,x] /;
        FreeQ[{a,b,c,n},x]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: (a__ + b__ * x_ + c__ * x_.pow(2)).coth().pow(n_),
        with: [a__, b__, c__, n_, x_],
        optional: [a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, n_], x_)
        },
        rhs: {
            rubi_simp(&(rubi_deferred_integral(
                &(&a__ + &b__ * x_ + &c__ * x_.pow(2)).coth().pow(&n_),
                x_,
            )), x_)
        },
    ));
}

fn push_rules_rule_5945(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 5945,
        source: "Int[(d_.+e_.*x_)*Tanh[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
          e*Log[Cosh[a+b*x+c*x^2]]/(2*c) +
          (2*c*d-b*e)/(2*c) \\[Star] Int[Tanh[a+b*x+c*x^2],x] /;
        FreeQ[{a,b,c,d,e},x]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern: (d__ + e__ * x_) * (a__ + b__ * x_ + c__ * x_.pow(2)).tanh(),
        with: [d__, e__, a__, b__, c__, x_],
        optional: [d__, e__, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
        },
        rhs: {
            let angle = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let recursive = rubi_rhs_int(&angle.tanh(), x_);

            rubi_simp(&(&e__ * angle.cosh().log() / (Atom::num(2) * &c__)), x_)
                    + rubi_star((Atom::num(2) * &c__ * &d__ - &b__ * &e__)
                            / (Atom::num(2) * &c__), recursive)
        },
    ));
}

fn push_rules_rule_5946(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 5946,
        source: "Int[(d_.+e_.*x_)*Coth[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
          e*Log[Sinh[a+b*x+c*x^2]]/(2*c) +
          (2*c*d-b*e)/(2*c) \\[Star] Int[Coth[a+b*x+c*x^2],x] /;
        FreeQ[{a,b,c,d,e},x]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern: (d__ + e__ * x_) * (a__ + b__ * x_ + c__ * x_.pow(2)).coth(),
        with: [d__, e__, a__, b__, c__, x_],
        optional: [d__, e__, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
        },
        rhs: {
            let angle = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let recursive = rubi_rhs_int(&angle.coth(), x_);

            rubi_simp(&(&e__ * angle.sinh().log() / (Atom::num(2) * &c__)), x_)
                    + rubi_star((Atom::num(2) * &c__ * &d__ - &b__ * &e__)
                            / (Atom::num(2) * &c__), recursive)
        },
    ));
}

fn push_rules_rule_5947(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5947,
        source: "Int[(d_.+e_.*x_)^m_.*Tanh[a_.+b_.*x_+c_.*x_^2]^n_.,x_Symbol] :=
          Integral[(d+e*x)^m*Tanh[a+b*x+c*x^2]^n,x] /;
        FreeQ[{a,b,c,d,e,m,n},x]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: (d__ + e__ * x_).pow(m_) * (a__ + b__ * x_ + c__ * x_.pow(2)).tanh().pow(n_),
        with: [d__, e__, m_, a__, b__, c__, n_, x_],
        optional: [d__, e__, m_, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_], x_)
        },
        rhs: {
            rubi_simp(&(rubi_deferred_integral(
                &((&d__ + &e__ * x_).pow(&m_)
                    * (&a__ + &b__ * x_ + &c__ * x_.pow(2)).tanh().pow(&n_)),
                x_,
            )), x_)
        },
    ));
}

fn push_rules_rule_5948(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5948,
        source: "Int[(d_.+e_.*x_)^m_.*Coth[a_.+b_.*x_+c_.*x_^2]^n_.,x_Symbol] :=
          Integral[(d+e*x)^m*Coth[a+b*x+c*x^2]^n,x] /;
        FreeQ[{a,b,c,d,e,m,n},x]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: (d__ + e__ * x_).pow(m_) * (a__ + b__ * x_ + c__ * x_.pow(2)).coth().pow(n_),
        with: [d__, e__, m_, a__, b__, c__, n_, x_],
        optional: [d__, e__, m_, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_], x_)
        },
        rhs: {
            rubi_simp(&(rubi_deferred_integral(
                &((&d__ + &e__ * x_).pow(&m_)
                    * (&a__ + &b__ * x_ + &c__ * x_.pow(2)).coth().pow(&n_)),
                x_,
            )), x_)
        },
    ));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn downvalues_5943_through_5948_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .collect::<Vec<_>>();
        assert_eq!(orders, (5943..=5948).collect::<Vec<_>>());
    }
}
