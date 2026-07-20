use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_5797(rules);
    push_rules_rule_5798(rules);
}

fn push_rules_rule_5797(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, m_, n_, u_, v_);
    rules.push(rubi_rule!(
        order: 5797,
        source: "Int[u_^m_.*(a_.+b_.*Sinh[v_])^n_.,x_Symbol] :=
          Int[ExpandToSum[u,x]^m*(a+b*Sinh[ExpandToSum[v,x]])^n,x] /;
        FreeQ[{a,b,m,n},x] && LinearQ[{u,v},x] && Not[LinearMatchQ[{u,v},x]]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: Atom::var(u_).pow(m_) * (a__ + b__ * Atom::var(v_).sinh()).pow(n_),
        with: [u_, m_, a__, b__, v_, n_, x_],
        optional: [m_, a__, b__, n_],
        when: {
            freeq!([a__, b__, m_, n_], x_)
                && rubi_linear_q_list(&[&u_, &v_], x_)
                && !rubi_linear_match_q_list(&[&u_, &v_], x_)
        },
        rhs: {
            let expanded_u = rubi_expand_to_sum(&u_, x_);
            let expanded_v = rubi_expand_to_sum(&v_, x_);
            rubi_rhs_int(
                &(expanded_u.pow(&m_) * (&a__ + &b__ * expanded_v.sinh()).pow(&n_)),
                x_,
            )
        },
    ));
}

fn push_rules_rule_5798(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, m_, n_, u_, v_);
    rules.push(rubi_rule!(
        order: 5798,
        source: "Int[u_^m_.*(a_.+b_.*Cosh[v_])^n_.,x_Symbol] :=
          Int[ExpandToSum[u,x]^m*(a+b*Cosh[ExpandToSum[v,x]])^n,x] /;
        FreeQ[{a,b,m,n},x] && LinearQ[{u,v},x] && Not[LinearMatchQ[{u,v},x]]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: Atom::var(u_).pow(m_) * (a__ + b__ * Atom::var(v_).cosh()).pow(n_),
        with: [u_, m_, a__, b__, v_, n_, x_],
        optional: [m_, a__, b__, n_],
        when: {
            freeq!([a__, b__, m_, n_], x_)
                && rubi_linear_q_list(&[&u_, &v_], x_)
                && !rubi_linear_match_q_list(&[&u_, &v_], x_)
        },
        rhs: {
            let expanded_u = rubi_expand_to_sum(&u_, x_);
            let expanded_v = rubi_expand_to_sum(&v_, x_);
            rubi_rhs_int(
                &(expanded_u.pow(&m_) * (&a__ + &b__ * expanded_v.cosh()).pow(&n_)),
                x_,
            )
        },
    ));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn downvalues_5797_through_5798_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .collect::<Vec<_>>();
        assert_eq!(orders, (5797..=5798).collect::<Vec<_>>());
    }
}
