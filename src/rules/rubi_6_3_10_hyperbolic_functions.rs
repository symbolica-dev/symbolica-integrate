use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_5921(rules);
    push_rules_rule_5922(rules);
}

fn push_rules_rule_5921(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, m_, n_, u_, v_);
    rules.push(rubi_rule!(
        order: 5921,
        source: "Int[u_^m_.*(a_.+b_.*Tanh[v_])^n_.,x_Symbol] :=
          Int[ExpandToSum[u,x]^m*(a+b*Tanh[ExpandToSum[v,x]])^n,x] /;
        FreeQ[{a,b,m,n},x] && LinearQ[{u,v},x] && Not[LinearMatchQ[{u,v},x]]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: Atom::var(u_).pow(m_) * (a__ + b__ * Atom::var(v_).tanh()).pow(n_),
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
                &(expanded_u.pow(&m_) * (&a__ + &b__ * expanded_v.tanh()).pow(&n_)),
                x_,
            )
        },
    ));
}

fn push_rules_rule_5922(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, m_, n_, u_, v_);
    rules.push(rubi_rule!(
        order: 5922,
        source: "Int[u_^m_.*(a_.+b_.*Coth[v_])^n_.,x_Symbol] :=
          Int[ExpandToSum[u,x]^m*(a+b*Coth[ExpandToSum[v,x]])^n,x] /;
        FreeQ[{a,b,m,n},x] && LinearQ[{u,v},x] && Not[LinearMatchQ[{u,v},x]]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: Atom::var(u_).pow(m_) * (a__ + b__ * Atom::var(v_).coth()).pow(n_),
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
                &(expanded_u.pow(&m_) * (&a__ + &b__ * expanded_v.coth()).pow(&n_)),
                x_,
            )
        },
    ));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn downvalues_5921_through_5922_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .collect::<Vec<_>>();
        assert_eq!(orders, (5921..=5922).collect::<Vec<_>>());
    }
}
