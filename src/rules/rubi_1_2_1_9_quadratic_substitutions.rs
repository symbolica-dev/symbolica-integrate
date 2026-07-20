use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_2146(rules);
    push_rules_rule_2147(rules);
    push_rules_rule_2148(rules);
    push_rules_rule_2149(rules);
    push_rules_rule_2150(rules);
    push_rules_rule_2151(rules);
}

fn push_rules_rule_2146(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        a__,
        b__,
        c__,
        d__,
        e__,
        f__,
        p_,
        q_,
        u__,
        capital_a__,
        capital_b__,
        capital_c__
    );
    rules.push(rubi_rule!(
        order: 2146,
        source: "Int[(a_.+b_.*u_+c_.*u_^2)^p_.*(d_.+e_.*u_+f_.*u_^2)^q_.*(A_.+B_.*u_+C_.*u_^2),x_Symbol] :=
          1/Coefficient[u,x,1] \\[Star] Subst[Int[(a+b*x+c*x^2)^p*(d+e*x+f*x^2)^q*(A+B*x+C*x^2),x],x,u] /;
        FreeQ[{a,b,c,d,e,f,A,B,C,p,q},x] && LinearQ[u,x] && NeQ[u,x]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (a__ + b__ * u__ + c__ * u__.pow(2)).pow(p_)
            * (d__ + e__ * u__ + f__ * u__.pow(2)).pow(q_)
            * (capital_a__ + capital_b__ * u__ + capital_c__ * u__.pow(2)),
        with: [a__, b__, c__, d__, e__, f__, capital_a__, capital_b__, capital_c__, u__, p_, q_, x_],
        optional: [a__, b__, c__, d__, e__, f__, capital_a__, capital_b__, capital_c__, p_, q_],
        x_free: [a__, b__, c__, d__, e__, f__, capital_a__, capital_b__, capital_c__, p_, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, capital_a__, capital_b__, capital_c__, p_, q_], x_)
                && rubi_linear_q(&u__, x_)
                && neq!(u__, x_)
        },
        rhs: {
            let u1 = rubi_coefficient(&u__, x_, 1).rubi_rhs();
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = (&a__ + &b__ * &sub_atom + &c__ * sub_atom.pow(2)).pow(&p_)
                * (&d__ + &e__ * &sub_atom + &f__ * sub_atom.pow(2)).pow(&q_)
                * (&capital_a__ + &capital_b__ * &sub_atom + &capital_c__ * sub_atom.pow(2));
            let transformed = rubi_rhs_int(&transformed_integrand, sub);
            let substituted = rubi_subst(&transformed, sub, u__);

            rubi_star(Atom::num(1) / u1, substituted)
        },
    ));
}

fn push_rules_rule_2147(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        a__,
        b__,
        c__,
        d__,
        e__,
        f__,
        p_,
        q_,
        u__,
        capital_a__,
        capital_b__
    );
    rules.push(rubi_rule!(
        order: 2147,
        source: "Int[(a_.+b_.*u_+c_.*u_^2)^p_.*(d_.+e_.*u_+f_.*u_^2)^q_.*(A_.+B_.*u_),x_Symbol] :=
          1/Coefficient[u,x,1] \\[Star] Subst[Int[(a+b*x+c*x^2)^p*(d+e*x+f*x^2)^q*(A+B*x),x],x,u] /;
        FreeQ[{a,b,c,d,e,f,A,B,C,p,q},x] && LinearQ[u,x] && NeQ[u,x]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (a__ + b__ * u__ + c__ * u__.pow(2)).pow(p_)
            * (d__ + e__ * u__ + f__ * u__.pow(2)).pow(q_)
            * (capital_a__ + capital_b__ * u__),
        with: [a__, b__, c__, d__, e__, f__, capital_a__, capital_b__, u__, p_, q_, x_],
        optional: [a__, b__, c__, d__, e__, f__, capital_a__, capital_b__, p_, q_],
        x_free: [a__, b__, c__, d__, e__, f__, capital_a__, capital_b__, p_, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, capital_a__, capital_b__, p_, q_], x_)
                && rubi_linear_q(&u__, x_)
                && neq!(u__, x_)
        },
        rhs: {
            let u1 = rubi_coefficient(&u__, x_, 1).rubi_rhs();
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = (&a__ + &b__ * &sub_atom + &c__ * sub_atom.pow(2)).pow(&p_)
                * (&d__ + &e__ * &sub_atom + &f__ * sub_atom.pow(2)).pow(&q_)
                * (&capital_a__ + &capital_b__ * &sub_atom);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);
            let substituted = rubi_subst(&transformed, sub, u__);

            rubi_star(Atom::num(1) / u1, substituted)
        },
    ));
}

fn push_rules_rule_2148(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        a__,
        b__,
        c__,
        d__,
        e__,
        f__,
        p_,
        q_,
        u__,
        capital_a__,
        capital_c__
    );
    rules.push(rubi_rule!(
        order: 2148,
        source: "Int[(a_.+b_.*u_+c_.*u_^2)^p_.*(d_.+e_.*u_+f_.*u_^2)^q_.*(A_.+C_.*u_^2),x_Symbol] :=
          1/Coefficient[u,x,1] \\[Star] Subst[Int[(a+b*x+c*x^2)^p*(d+e*x+f*x^2)^q*(A+C*x^2),x],x,u] /;
        FreeQ[{a,b,c,d,e,f,A,C,p,q},x] && LinearQ[u,x] && NeQ[u,x]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (a__ + b__ * u__ + c__ * u__.pow(2)).pow(p_)
            * (d__ + e__ * u__ + f__ * u__.pow(2)).pow(q_)
            * (capital_a__ + capital_c__ * u__.pow(2)),
        with: [a__, b__, c__, d__, e__, f__, capital_a__, capital_c__, u__, p_, q_, x_],
        optional: [a__, b__, c__, d__, e__, f__, capital_a__, capital_c__, p_, q_],
        x_free: [a__, b__, c__, d__, e__, f__, capital_a__, capital_c__, p_, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, capital_a__, capital_c__, p_, q_], x_)
                && rubi_linear_q(&u__, x_)
                && neq!(u__, x_)
        },
        rhs: {
            let u1 = rubi_coefficient(&u__, x_, 1).rubi_rhs();
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = (&a__ + &b__ * &sub_atom + &c__ * sub_atom.pow(2)).pow(&p_)
                * (&d__ + &e__ * &sub_atom + &f__ * sub_atom.pow(2)).pow(&q_)
                * (&capital_a__ + &capital_c__ * sub_atom.pow(2));
            let transformed = rubi_rhs_int(&transformed_integrand, sub);
            let substituted = rubi_subst(&transformed, sub, u__);

            rubi_star(Atom::num(1) / u1, substituted)
        },
    ));
}

fn push_rules_rule_2149(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        a__,
        c__,
        d__,
        e__,
        f__,
        p_,
        q_,
        u__,
        capital_a__,
        capital_b__,
        capital_c__
    );
    rules.push(rubi_rule!(
        order: 2149,
        source: "Int[(a_.+c_.*u_^2)^p_.*(d_.+e_.*u_+f_.*u_^2)^q_.*(A_.+B_.*u_+C_.*u_^2),x_Symbol] :=
          1/Coefficient[u,x,1] \\[Star] Subst[Int[(a+c*x^2)^p*(d+e*x+f*x^2)^q*(A+B*x+C*x^2),x],x,u] /;
        FreeQ[{a,c,d,e,f,A,B,C,p,q},x] && LinearQ[u,x] && NeQ[u,x]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (a__ + c__ * u__.pow(2)).pow(p_)
            * (d__ + e__ * u__ + f__ * u__.pow(2)).pow(q_)
            * (capital_a__ + capital_b__ * u__ + capital_c__ * u__.pow(2)),
        with: [a__, c__, d__, e__, f__, capital_a__, capital_b__, capital_c__, u__, p_, q_, x_],
        optional: [a__, c__, d__, e__, f__, capital_a__, capital_b__, capital_c__, p_, q_],
        x_free: [a__, c__, d__, e__, f__, capital_a__, capital_b__, capital_c__, p_, q_],
        when: {
            freeq!([a__, c__, d__, e__, f__, capital_a__, capital_b__, capital_c__, p_, q_], x_)
                && rubi_linear_q(&u__, x_)
                && neq!(u__, x_)
        },
        rhs: {
            let u1 = rubi_coefficient(&u__, x_, 1).rubi_rhs();
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = (&a__ + &c__ * sub_atom.pow(2)).pow(&p_)
                * (&d__ + &e__ * &sub_atom + &f__ * sub_atom.pow(2)).pow(&q_)
                * (&capital_a__ + &capital_b__ * &sub_atom + &capital_c__ * sub_atom.pow(2));
            let transformed = rubi_rhs_int(&transformed_integrand, sub);
            let substituted = rubi_subst(&transformed, sub, u__);

            rubi_star(Atom::num(1) / u1, substituted)
        },
    ));
}

fn push_rules_rule_2150(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        a__,
        c__,
        d__,
        e__,
        f__,
        p_,
        q_,
        u__,
        capital_a__,
        capital_b__
    );
    rules.push(rubi_rule!(
        order: 2150,
        source: "Int[(a_.+c_.*u_^2)^p_.*(d_.+e_.*u_+f_.*u_^2)^q_.*(A_.+B_.*u_),x_Symbol] :=
          1/Coefficient[u,x,1] \\[Star] Subst[Int[(a+c*x^2)^p*(d+e*x+f*x^2)^q*(A+B*x),x],x,u] /;
        FreeQ[{a,c,d,e,f,A,B,C,p,q},x] && LinearQ[u,x] && NeQ[u,x]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (a__ + c__ * u__.pow(2)).pow(p_)
            * (d__ + e__ * u__ + f__ * u__.pow(2)).pow(q_)
            * (capital_a__ + capital_b__ * u__),
        with: [a__, c__, d__, e__, f__, capital_a__, capital_b__, u__, p_, q_, x_],
        optional: [a__, c__, d__, e__, f__, capital_a__, capital_b__, p_, q_],
        x_free: [a__, c__, d__, e__, f__, capital_a__, capital_b__, p_, q_],
        when: {
            freeq!([a__, c__, d__, e__, f__, capital_a__, capital_b__, p_, q_], x_)
                && rubi_linear_q(&u__, x_)
                && neq!(u__, x_)
        },
        rhs: {
            let u1 = rubi_coefficient(&u__, x_, 1).rubi_rhs();
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = (&a__ + &c__ * sub_atom.pow(2)).pow(&p_)
                * (&d__ + &e__ * &sub_atom + &f__ * sub_atom.pow(2)).pow(&q_)
                * (&capital_a__ + &capital_b__ * &sub_atom);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);
            let substituted = rubi_subst(&transformed, sub, u__);

            rubi_star(Atom::num(1) / u1, substituted)
        },
    ));
}

fn push_rules_rule_2151(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        a__,
        c__,
        d__,
        e__,
        f__,
        p_,
        q_,
        u__,
        capital_a__,
        capital_c__
    );
    rules.push(rubi_rule!(
        order: 2151,
        source: "Int[(a_.+c_.*u_^2)^p_.*(d_.+e_.*u_+f_.*u_^2)^q_.*(A_.+C_.*u_^2),x_Symbol] :=
          1/Coefficient[u,x,1] \\[Star] Subst[Int[(a+c*x^2)^p*(d+e*x+f*x^2)^q*(A+C*x^2),x],x,u] /;
        FreeQ[{a,c,d,e,f,A,C,p,q},x] && LinearQ[u,x] && NeQ[u,x]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (a__ + c__ * u__.pow(2)).pow(p_)
            * (d__ + e__ * u__ + f__ * u__.pow(2)).pow(q_)
            * (capital_a__ + capital_c__ * u__.pow(2)),
        with: [a__, c__, d__, e__, f__, capital_a__, capital_c__, u__, p_, q_, x_],
        optional: [a__, c__, d__, e__, f__, capital_a__, capital_c__, p_, q_],
        x_free: [a__, c__, d__, e__, f__, capital_a__, capital_c__, p_, q_],
        when: {
            freeq!([a__, c__, d__, e__, f__, capital_a__, capital_c__, p_, q_], x_)
                && rubi_linear_q(&u__, x_)
                && neq!(u__, x_)
        },
        rhs: {
            let u1 = rubi_coefficient(&u__, x_, 1).rubi_rhs();
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = (&a__ + &c__ * sub_atom.pow(2)).pow(&p_)
                * (&d__ + &e__ * &sub_atom + &f__ * sub_atom.pow(2)).pow(&q_)
                * (&capital_a__ + &capital_c__ * sub_atom.pow(2));
            let transformed = rubi_rhs_int(&transformed_integrand, sub);
            let substituted = rubi_subst(&transformed, sub, u__);

            rubi_star(Atom::num(1) / u1, substituted)
        },
    ));
}
