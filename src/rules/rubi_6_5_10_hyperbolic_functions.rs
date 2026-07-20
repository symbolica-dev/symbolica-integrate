use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_5949(rules);
    push_rules_rule_5950(rules);
}

fn push_rules_rule_5949(rules: &mut Vec<RubiRule>) {
    rubi_symb!(m_, n_, u_, v_);
    rules.push(rubi_rule!(
        order: 5949,
        source: "Int[u_^m_.*Sech[v_]^n_.,x_Symbol] :=
          Int[ExpandToSum[u,x]^m*Sech[ExpandToSum[v,x]]^n,x] /;
        FreeQ[{m,n},x] && LinearQ[{u,v},x] && Not[LinearMatchQ[{u,v},x]]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: Atom::var(u_).pow(m_) * Atom::var(v_).sech().pow(n_),
        with: [u_, m_, v_, n_, x_],
        optional: [m_, n_],
        when: {
            freeq!([m_, n_], x_)
                && rubi_linear_q_list(&[&u_, &v_], x_)
                && !rubi_linear_match_q_list(&[&u_, &v_], x_)
        },
        rhs: {
            let expanded_u = rubi_expand_to_sum(&u_, x_);
            let expanded_v = rubi_expand_to_sum(&v_, x_);
            rubi_rhs_int(
                &(expanded_u.pow(&m_) * expanded_v.sech().pow(&n_)),
                x_,
            )
        },
    ));
}

fn push_rules_rule_5950(rules: &mut Vec<RubiRule>) {
    rubi_symb!(m_, n_, u_, v_);
    rules.push(rubi_rule!(
        order: 5950,
        source: "Int[u_^m_.*Csch[v_]^n_.,x_Symbol] :=
          Int[ExpandToSum[u,x]^m*Csch[ExpandToSum[v,x]]^n,x] /;
        FreeQ[{m,n},x] && LinearQ[{u,v},x] && Not[LinearMatchQ[{u,v},x]]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: Atom::var(u_).pow(m_) * Atom::var(v_).csch().pow(n_),
        with: [u_, m_, v_, n_, x_],
        optional: [m_, n_],
        when: {
            freeq!([m_, n_], x_)
                && rubi_linear_q_list(&[&u_, &v_], x_)
                && !rubi_linear_match_q_list(&[&u_, &v_], x_)
        },
        rhs: {
            let expanded_u = rubi_expand_to_sum(&u_, x_);
            let expanded_v = rubi_expand_to_sum(&v_, x_);
            rubi_rhs_int(
                &(expanded_u.pow(&m_) * expanded_v.csch().pow(&n_)),
                x_,
            )
        },
    ));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn downvalues_5949_through_5950_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .collect::<Vec<_>>();
        assert_eq!(orders, (5949..=5950).collect::<Vec<_>>());
    }
}
