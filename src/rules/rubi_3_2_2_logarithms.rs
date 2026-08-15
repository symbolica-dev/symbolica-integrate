use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_2959(rules);
    push_rules_rule_2960(rules);
    push_rules_rule_2961(rules);
    push_rules_rule_2962(rules);
    push_rules_rule_2963(rules);
    push_rules_rule_2964(rules);
    push_rules_rule_2965(rules);
    push_rules_rule_2966(rules);
    push_rules_rule_2967(rules);
    push_rules_rule_2968(rules);
    push_rules_rule_2969(rules);
    push_rules_rule_2970(rules);
    push_rules_rule_2971(rules);
    push_rules_rule_2972(rules);
    push_rules_rule_2973(rules);
    push_rules_rule_2974(rules);
    push_rules_rule_2975(rules);
    push_rules_rule_2976(rules);
    push_rules_rule_2977(rules);
}

fn push_rules_rule_2959(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        capital_a__,
        capital_b__,
        a__,
        b__,
        c__,
        d__,
        e__,
        f__,
        g__,
        h__,
        i__,
        m_,
        n_,
        x_
    );
    rules.push(rubi_rule!(
        order: 2959,
        source: "Int[(f_.+g_.*x_)^m_.*(h_.+i_.*x_)*(A_.+B_.*Log[e_.*((a_.+b_.*x_)/(c_.+d_.*x_))^n_.]),x_Symbol] :=
          (f+g*x)^(m+1)*(h+i*x)*(A+B*Log[e*((a+b*x)/(c+d*x))^n])/(g*(m+2)) +
          i*(b*c-a*d)/(b*d*(m+2)) \\[Star] Int[(f+g*x)^m*(A-B*n+B*Log[e*((a+b*x)/(c+d*x))^n]),x] /;
        FreeQ[{a,b,c,d,e,f,g,h,i,A,B,m,n},x] && NeQ[b*c-a*d,0] && EqQ[b*f-a*g,0] && EqQ[d*h-c*i,0] && IGtQ[m,-2]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern: (f__ + g__ * x_).pow(m_)
            * (h__ + i__ * x_)
            * (capital_a__
                + capital_b__ * (e__ * ((a__ + b__ * x_) / (c__ + d__ * x_)).pow(n_)).log()),
        with: [f__, g__, m_, h__, i__, capital_a__, capital_b__, e__, a__, b__, c__, d__, n_, x_],
        optional: [f__, g__, m_, h__, i__, capital_a__, capital_b__, e__, a__, b__, c__, d__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__, i__, capital_a__, capital_b__, m_, n_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(&b__ * &f__ - &a__ * &g__, 0)
                && eqq!(&d__ * &h__ - &c__ * &i__, 0)
                && igtq!(m_, -2)
        },
        rhs: {
            let lhs = &a__ + &b__ * x_;
            let rhs = &c__ + &d__ * x_;
            let multiplier = &f__ + &g__ * x_;
            let linear = &h__ + &i__ * x_;
            let determinant = &b__ * &c__ - &a__ * &d__;
            let m2 = &m_ + 2;
            let logarithmic =
                &capital_a__ + &capital_b__ * (&e__ * (&lhs / &rhs).pow(&n_)).log();
            let recursive_integrand = multiplier.pow(&m_)
                * (&capital_a__ - &capital_b__ * &n_
                    + &capital_b__ * (&e__ * (&lhs / &rhs).pow(&n_)).log());
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(
                    &(multiplier.pow(&m_ + 1) * linear * logarithmic / (&g__ * &m2)),
                    x_,
                ) + rubi_star(&i__ * determinant / (&b__ * &d__ * &m2), recursive)
        },
    ));
}

fn push_rules_rule_2960(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        capital_a__,
        capital_b__,
        a__,
        b__,
        c__,
        d__,
        e__,
        f__,
        g__,
        h__,
        i__,
        m_,
        mn_,
        n_,
        x_
    );
    rules.push(rubi_rule!(
        order: 2960,
        source: "Int[(f_.+g_.*x_)^m_.*(h_.+i_.*x_)*(A_.+B_.*Log[e_.*(a_.+b_.*x_)^n_.*(c_.+d_.*x_)^mn_]),x_Symbol] :=
          (f+g*x)^(m+1)*(h+i*x)*(A+B*Log[e*(a+b*x)^n/(c+d*x)^n])/(g*(m+2)) +
          i*(b*c-a*d)/(b*d*(m+2)) \\[Star] Int[(f+g*x)^m*(A-B*n+B*Log[e*(a+b*x)^n/(c+d*x)^n]),x] /;
        FreeQ[{a,b,c,d,e,f,g,h,i,A,B,m,n},x] && EqQ[n+mn,0] && IGtQ[n,0] && NeQ[b*c-a*d,0] && EqQ[b*f-a*g,0] && EqQ[d*h-c*i,0] && IGtQ[m,-2]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern: (f__ + g__ * x_).pow(m_)
            * (h__ + i__ * x_)
            * (capital_a__
                + capital_b__
                    * (e__ * (a__ + b__ * x_).pow(n_) * (c__ + d__ * x_).pow(mn_)).log()),
        with: [f__, g__, m_, h__, i__, capital_a__, capital_b__, e__, a__, b__, n_, c__, d__, mn_, x_],
        optional: [f__, g__, m_, h__, i__, capital_a__, capital_b__, e__, a__, b__, c__, d__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__, i__, capital_a__, capital_b__, m_, n_], x_)
                && eqq!(&n_ + &mn_, 0)
                && igtq!(n_, 0)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(&b__ * &f__ - &a__ * &g__, 0)
                && eqq!(&d__ * &h__ - &c__ * &i__, 0)
                && igtq!(m_, -2)
        },
        rhs: {
            let lhs = &a__ + &b__ * x_;
            let rhs = &c__ + &d__ * x_;
            let multiplier = &f__ + &g__ * x_;
            let linear = &h__ + &i__ * x_;
            let determinant = &b__ * &c__ - &a__ * &d__;
            let m2 = &m_ + 2;
            let logarithmic =
                &capital_a__ + &capital_b__ * (&e__ * lhs.pow(&n_) / rhs.pow(&n_)).log();
            let recursive_integrand = multiplier.pow(&m_)
                * (&capital_a__ - &capital_b__ * &n_
                    + &capital_b__ * (&e__ * lhs.pow(&n_) / rhs.pow(&n_)).log());
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(
                    &(multiplier.pow(&m_ + 1) * linear * logarithmic / (&g__ * &m2)),
                    x_,
                ) + rubi_star(&i__ * determinant / (&b__ * &d__ * &m2), recursive)
        },
    ));
}

fn push_rules_rule_2961(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_a__,
        capital_b__,
        a__,
        b__,
        c__,
        d__,
        e__,
        f__,
        g__,
        h__,
        i__,
        m_,
        n_,
        p_,
        q_,
        x_
    );
    rules.push(rubi_rule!(
        order: 2961,
        source: "Int[(f_.+g_.*x_)^m_.*(h_.+i_.*x_)^q_.*(A_.+B_.*Log[e_.*((a_.+b_.*x_)/(c_.+d_.*x_))^n_.])^p_.,x_Symbol] :=
          (b*c-a*d)^(m+q+1)*(g/b)^m*(i/d)^q \\[Star] Subst[Int[x^m*(A+B*Log[e*x^n])^p/(b-d*x)^(m+q+2),x],x,(a+b*x)/(c+d*x)] /;
        FreeQ[{a,b,c,d,e,f,g,h,i,A,B,n,p},x] && NeQ[b*c-a*d,0] && EqQ[b*f-a*g,0] && EqQ[d*h-c*i,0] && IntegersQ[m,q]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [f__, g__, m_, h__, i__, q_, capital_a__, capital_b__, e__, a__, b__, c__, d__, n_, p_, x_],
        optional: [f__, g__, m_, h__, i__, q_, capital_a__, capital_b__, e__, a__, b__, c__, d__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__, i__, capital_a__, capital_b__, n_, p_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(&b__ * &f__ - &a__ * &g__, 0)
                && eqq!(&d__ * &h__ - &c__ * &i__, 0)
                && integersq!([m_, q_])
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let substitution_integrand = sub_atom.pow(&m_)
                * (&capital_a__ + &capital_b__ * (&e__ * sub_atom.pow(&n_)).log()).pow(&p_)
                / (&b__ - &d__ * &sub_atom).pow(&m_ + &q_ + 2);
            let substitution_primitive = rubi_rhs_int(&substitution_integrand, substitution_symbol);
            let substitution = (&a__ + &b__ * x_) / (&c__ + &d__ * x_);
            let coefficient = (&b__ * &c__ - &a__ * &d__).pow(&m_ + &q_ + 1)
                * (&g__ / &b__).pow(&m_)
                * (&i__ / &d__).pow(&q_);
            let substituted =
                rubi_subst(&substitution_primitive, substitution_symbol, substitution);

            rubi_star(coefficient, substituted)
        },
    ));
}

fn push_rules_rule_2962(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_a__,
        capital_b__,
        a__,
        b__,
        c__,
        d__,
        e__,
        f__,
        g__,
        h__,
        i__,
        m_,
        mn_,
        n_,
        p_,
        q_,
        x_
    );
    rules.push(rubi_rule!(
        order: 2962,
        source: "Int[(f_.+g_.*x_)^m_.*(h_.+i_.*x_)^q_.*(A_.+B_.*Log[e_.*(a_.+b_.*x_)^n_.*(c_.+d_.*x_)^mn_])^p_.,x_Symbol] :=
          (b*c-a*d)^(m+q+1)*(g/b)^m*(i/d)^q \\[Star] Subst[Int[x^m*(A+B*Log[e*x^n])^p/(b-d*x)^(m+q+2),x],x,(a+b*x)/(c+d*x)] /;
        FreeQ[{a,b,c,d,e,f,g,h,i,A,B,n,p},x] && EqQ[n+mn,0] && IGtQ[n,0] && NeQ[b*c-a*d,0] && EqQ[b*f-a*g,0] && EqQ[d*h-c*i,0] && IntegersQ[m,q]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [f__, g__, m_, h__, i__, q_, capital_a__, capital_b__, e__, a__, b__, n_, c__, d__, mn_, p_, x_],
        optional: [f__, g__, m_, h__, i__, q_, capital_a__, capital_b__, e__, a__, b__, c__, d__, p_, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__, i__, capital_a__, capital_b__, n_, p_], x_)
                && eqq!(&n_ + &mn_, 0)
                && igtq!(n_, 0)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(&b__ * &f__ - &a__ * &g__, 0)
                && eqq!(&d__ * &h__ - &c__ * &i__, 0)
                && integersq!([m_, q_])
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let substitution_integrand = sub_atom.pow(&m_)
                * (&capital_a__ + &capital_b__ * (&e__ * sub_atom.pow(&n_)).log()).pow(&p_)
                / (&b__ - &d__ * &sub_atom).pow(&m_ + &q_ + 2);
            let substitution_primitive = rubi_rhs_int(&substitution_integrand, substitution_symbol);
            let substitution = (&a__ + &b__ * x_) / (&c__ + &d__ * x_);
            let coefficient = (&b__ * &c__ - &a__ * &d__).pow(&m_ + &q_ + 1)
                * (&g__ / &b__).pow(&m_)
                * (&i__ / &d__).pow(&q_);
            let substituted =
                rubi_subst(&substitution_primitive, substitution_symbol, substitution);

            rubi_star(coefficient, substituted)
        },
    ));
}

fn push_rules_rule_2963(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_a__,
        capital_b__,
        a__,
        b__,
        c__,
        d__,
        e__,
        f__,
        g__,
        h__,
        i__,
        m_,
        n_,
        p_,
        q_,
        x_
    );
    rules.push(rubi_rule!(
        order: 2963,
        source: "Int[(f_.+g_.*x_)^m_.*(h_.+i_.*x_)^q_.*(A_.+B_.*Log[e_.*((a_.+b_.*x_)/(c_.+d_.*x_))^n_.])^p_.,x_Symbol] :=
          d^2*(g*(a+b*x)/b)^m/(i^2*(b*c-a*d)*(i*(c+d*x)/d)^m*((a+b*x)/(c+d*x))^m) \\[Star]
            Subst[Int[x^m*(A+B*Log[e*x^n])^p,x],x,(a+b*x)/(c+d*x)] /;
        FreeQ[{a,b,c,d,e,f,g,h,i,A,B,m,n,p,q},x] && NeQ[b*c-a*d,0] && EqQ[b*f-a*g,0] && EqQ[d*h-c*i,0] && EqQ[m+q+2,0]",
        desc: "Integration by substitution and partial fraction expansion",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [f__, g__, m_, h__, i__, q_, capital_a__, capital_b__, e__, a__, b__, c__, d__, n_, p_, x_],
        optional: [f__, g__, m_, h__, i__, q_, capital_a__, capital_b__, e__, a__, b__, c__, d__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__, i__, capital_a__, capital_b__], x_)
                && freeq!([m_, n_, p_, q_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(&b__ * &f__ - &a__ * &g__, 0)
                && eqq!(&d__ * &h__ - &c__ * &i__, 0)
                && eqq!(&m_ + &q_ + 2, 0)
        },
        rhs: {
            let lhs = &a__ + &b__ * x_;
            let rhs = &c__ + &d__ * x_;
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let substitution_integrand = sub_atom.pow(&m_)
                * (&capital_a__ + &capital_b__ * (&e__ * sub_atom.pow(&n_)).log()).pow(&p_);
            let substitution_primitive = rubi_rhs_int(&substitution_integrand, substitution_symbol);
            let substitution = &lhs / &rhs;
            let coefficient = d__.pow(2) * (&g__ * &lhs / &b__).pow(&m_)
                / (i__.pow(2)
                    * (&b__ * &c__ - &a__ * &d__)
                    * (&i__ * &rhs / &d__).pow(&m_)
                    * (&lhs / &rhs).pow(&m_));
            let substituted =
                rubi_subst(&substitution_primitive, substitution_symbol, substitution);

            rubi_star(coefficient, substituted)
        },
    ));
}

fn push_rules_rule_2964(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_a__,
        capital_b__,
        a__,
        b__,
        c__,
        d__,
        e__,
        f__,
        g__,
        h__,
        i__,
        m_,
        mn_,
        n_,
        p_,
        q_,
        x_
    );
    rules.push(rubi_rule!(
        order: 2964,
        source: "Int[(f_.+g_.*x_)^m_.*(h_.+i_.*x_)^q_.*(A_.+B_.*Log[e_.*(a_.+b_.*x_)^n_.*(c_.+d_.*x_)^mn_])^p_.,x_Symbol] :=
          d^2*(g*(a+b*x)/b)^m/(i^2*(b*c-a*d)*(i*(c+d*x)/d)^m*((a+b*x)/(c+d*x))^m) \\[Star]
            Subst[Int[x^m*(A+B*Log[e*x^n])^p,x],x,(a+b*x)/(c+d*x)] /;
        FreeQ[{a,b,c,d,e,f,g,h,i,A,B,m,n,p,q},x] && EqQ[n+mn,0] && IGtQ[n,0] && NeQ[b*c-a*d,0] && EqQ[b*f-a*g,0] && EqQ[d*h-c*i,0] && EqQ[m+q+2,0]",
        desc: "Integration by substitution and partial fraction expansion",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [f__, g__, m_, h__, i__, q_, capital_a__, capital_b__, e__, a__, b__, n_, c__, d__, mn_, p_, x_],
        optional: [f__, g__, m_, h__, i__, q_, capital_a__, capital_b__, e__, a__, b__, c__, d__, p_, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__, i__, capital_a__, capital_b__], x_)
                && freeq!([m_, n_, p_, q_], x_)
                && eqq!(&n_ + &mn_, 0)
                && igtq!(n_, 0)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(&b__ * &f__ - &a__ * &g__, 0)
                && eqq!(&d__ * &h__ - &c__ * &i__, 0)
                && eqq!(&m_ + &q_ + 2, 0)
        },
        rhs: {
            let lhs = &a__ + &b__ * x_;
            let rhs = &c__ + &d__ * x_;
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let substitution_integrand = sub_atom.pow(&m_)
                * (&capital_a__ + &capital_b__ * (&e__ * sub_atom.pow(&n_)).log()).pow(&p_);
            let substitution_primitive = rubi_rhs_int(&substitution_integrand, substitution_symbol);
            let substitution = &lhs / &rhs;
            let coefficient = d__.pow(2) * (&g__ * &lhs / &b__).pow(&m_)
                / (i__.pow(2)
                    * (&b__ * &c__ - &a__ * &d__)
                    * (&i__ * &rhs / &d__).pow(&m_)
                    * (&lhs / &rhs).pow(&m_));
            let substituted =
                rubi_subst(&substitution_primitive, substitution_symbol, substitution);

            rubi_star(coefficient, substituted)
        },
    ));
}

fn push_rules_rule_2965(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_a__,
        capital_b__,
        a__,
        b__,
        c__,
        d__,
        e__,
        f__,
        g__,
        h__,
        i__,
        m_,
        n_,
        p_,
        q_,
        x_
    );
    rules.push(rubi_rule!(
        order: 2965,
        source: "Int[(f_.+g_.*x_)^m_.*(h_.+i_.*x_)^q_.*(A_.+B_.*Log[e_.*((a_.+b_.*x_)/(c_.+d_.*x_))^n_.])^p_.,x_Symbol] :=
          (b*c-a*d)^(q+1)*(i/d)^q \\[Star] Subst[Int[(b*f-a*g-(d*f-c*g)*x)^m*(A+B*Log[e*x^n])^p/(b-d*x)^(m+q+2),x],x,(a+b*x)/(c+d*x)] /;
        FreeQ[{a,b,c,d,e,f,g,h,i,A,B,n},x] && NeQ[b*c-a*d,0] && IntegersQ[m,q] && IGtQ[p,0] && EqQ[d*h-c*i,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [f__, g__, m_, h__, i__, q_, capital_a__, capital_b__, e__, a__, b__, c__, d__, n_, p_, x_],
        optional: [f__, g__, m_, h__, i__, q_, capital_a__, capital_b__, e__, a__, b__, c__, d__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__, i__, capital_a__, capital_b__, n_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && integersq!([m_, q_])
                && igtq!(p_, 0)
                && eqq!(&d__ * &h__ - &c__ * &i__, 0)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let transformed_linear =
                &b__ * &f__ - &a__ * &g__ - (&d__ * &f__ - &c__ * &g__) * &sub_atom;
            let substitution_integrand = transformed_linear.pow(&m_)
                * (&capital_a__ + &capital_b__ * (&e__ * sub_atom.pow(&n_)).log()).pow(&p_)
                / (&b__ - &d__ * &sub_atom).pow(&m_ + &q_ + 2);
            let substitution_primitive = rubi_rhs_int(&substitution_integrand, substitution_symbol);
            let substitution = (&a__ + &b__ * x_) / (&c__ + &d__ * x_);
            let coefficient =
                (&b__ * &c__ - &a__ * &d__).pow(&q_ + 1) * (&i__ / &d__).pow(&q_);
            let substituted =
                rubi_subst(&substitution_primitive, substitution_symbol, substitution);

            rubi_star(coefficient, substituted)
        },
    ));
}

fn push_rules_rule_2966(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_a__,
        capital_b__,
        a__,
        b__,
        c__,
        d__,
        e__,
        f__,
        g__,
        h__,
        i__,
        m_,
        mn_,
        n_,
        p_,
        q_,
        x_
    );
    rules.push(rubi_rule!(
        order: 2966,
        source: "Int[(f_.+g_.*x_)^m_.*(h_.+i_.*x_)^q_.*(A_.+B_.*Log[e_.*(a_.+b_.*x_)^n_.*(c_.+d_.*x_)^mn_])^p_.,x_Symbol] :=
          (b*c-a*d)^(q+1)*(i/d)^q \\[Star] Subst[Int[(b*f-a*g-(d*f-c*g)*x)^m*(A+B*Log[e*x^n])^p/(b-d*x)^(m+q+2),x],x,(a+b*x)/(c+d*x)] /;
        FreeQ[{a,b,c,d,e,f,g,h,i,A,B,n},x] && EqQ[n+mn,0] && IGtQ[n,0] && NeQ[b*c-a*d,0] && IntegersQ[m,q] && IGtQ[p,0] && EqQ[d*h-c*i,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [f__, g__, m_, h__, i__, q_, capital_a__, capital_b__, e__, a__, b__, n_, c__, d__, mn_, p_, x_],
        optional: [f__, g__, m_, h__, i__, q_, capital_a__, capital_b__, e__, a__, b__, c__, d__, p_, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__, i__, capital_a__, capital_b__, n_], x_)
                && eqq!(&n_ + &mn_, 0)
                && igtq!(n_, 0)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && integersq!([m_, q_])
                && igtq!(p_, 0)
                && eqq!(&d__ * &h__ - &c__ * &i__, 0)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let transformed_linear =
                &b__ * &f__ - &a__ * &g__ - (&d__ * &f__ - &c__ * &g__) * &sub_atom;
            let substitution_integrand = transformed_linear.pow(&m_)
                * (&capital_a__ + &capital_b__ * (&e__ * sub_atom.pow(&n_)).log()).pow(&p_)
                / (&b__ - &d__ * &sub_atom).pow(&m_ + &q_ + 2);
            let substitution_primitive = rubi_rhs_int(&substitution_integrand, substitution_symbol);
            let substitution = (&a__ + &b__ * x_) / (&c__ + &d__ * x_);
            let coefficient =
                (&b__ * &c__ - &a__ * &d__).pow(&q_ + 1) * (&i__ / &d__).pow(&q_);
            let substituted =
                rubi_subst(&substitution_primitive, substitution_symbol, substitution);

            rubi_star(coefficient, substituted)
        },
    ));
}

fn push_rules_rule_2967(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_a__,
        capital_b__,
        a__,
        b__,
        c__,
        d__,
        e__,
        f__,
        g__,
        h__,
        i__,
        m_,
        n_,
        p_,
        q_,
        x_
    );
    rules.push(rubi_rule!(
        order: 2967,
        source: "Int[(f_.+g_.*x_)^m_.*(h_.+i_.*x_)^q_.*(A_.+B_.*Log[e_.*((a_.+b_.*x_)/(c_.+d_.*x_))^n_.])^p_.,x_Symbol] :=
          (b*c-a*d) \\[Star] Subst[Int[(b*f-a*g-(d*f-c*g)*x)^m*(b*h-a*i-(d*h-c*i)*x)^q*(A+B*Log[e*x^n])^p/(b-d*x)^(m+q+2),x],x,(a+b*x)/(c+d*x)] /;
        FreeQ[{a,b,c,d,e,f,g,h,i,A,B,n},x] && NeQ[b*c-a*d,0] && IntegersQ[m,q] && IGtQ[p,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [f__, g__, m_, h__, i__, q_, capital_a__, capital_b__, e__, a__, b__, c__, d__, n_, p_, x_],
        optional: [f__, g__, m_, h__, i__, q_, capital_a__, capital_b__, e__, a__, b__, c__, d__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__, i__, capital_a__, capital_b__, n_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && integersq!([m_, q_])
                && igtq!(p_, 0)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let first_linear =
                &b__ * &f__ - &a__ * &g__ - (&d__ * &f__ - &c__ * &g__) * &sub_atom;
            let second_linear =
                &b__ * &h__ - &a__ * &i__ - (&d__ * &h__ - &c__ * &i__) * &sub_atom;
            let substitution_integrand = first_linear.pow(&m_)
                * second_linear.pow(&q_)
                * (&capital_a__ + &capital_b__ * (&e__ * sub_atom.pow(&n_)).log()).pow(&p_)
                / (&b__ - &d__ * &sub_atom).pow(&m_ + &q_ + 2);
            let substitution_primitive = rubi_rhs_int(&substitution_integrand, substitution_symbol);
            let substitution = (&a__ + &b__ * x_) / (&c__ + &d__ * x_);
            let substituted =
                rubi_subst(&substitution_primitive, substitution_symbol, substitution);

            rubi_star(&b__ * &c__ - &a__ * &d__, substituted)
        },
    ));
}

fn push_rules_rule_2968(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_a__,
        capital_b__,
        a__,
        b__,
        c__,
        d__,
        e__,
        f__,
        g__,
        h__,
        i__,
        m_,
        mn_,
        n_,
        p_,
        q_,
        x_
    );
    rules.push(rubi_rule!(
        order: 2968,
        source: "Int[(f_.+g_.*x_)^m_.*(h_.+i_.*x_)^q_.*(A_.+B_.*Log[e_.*(a_.+b_.*x_)^n_.*(c_.+d_.*x_)^mn_])^p_.,x_Symbol] :=
          (b*c-a*d) \\[Star] Subst[Int[(b*f-a*g-(d*f-c*g)*x)^m*(b*h-a*i-(d*h-c*i)*x)^q*(A+B*Log[e*x^n])^p/(b-d*x)^(m+q+2),x],x,(a+b*x)/(c+d*x)] /;
        FreeQ[{a,b,c,d,e,f,g,h,i,A,B,n},x] && EqQ[n+mn,0] && IGtQ[n,0] && NeQ[b*c-a*d,0] && IntegersQ[m,q] && IGtQ[p,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [f__, g__, m_, h__, i__, q_, capital_a__, capital_b__, e__, a__, b__, n_, c__, d__, mn_, p_, x_],
        optional: [f__, g__, m_, h__, i__, q_, capital_a__, capital_b__, e__, a__, b__, c__, d__, p_, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__, i__, capital_a__, capital_b__, n_], x_)
                && eqq!(&n_ + &mn_, 0)
                && igtq!(n_, 0)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && integersq!([m_, q_])
                && igtq!(p_, 0)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let first_linear =
                &b__ * &f__ - &a__ * &g__ - (&d__ * &f__ - &c__ * &g__) * &sub_atom;
            let second_linear =
                &b__ * &h__ - &a__ * &i__ - (&d__ * &h__ - &c__ * &i__) * &sub_atom;
            let substitution_integrand = first_linear.pow(&m_)
                * second_linear.pow(&q_)
                * (&capital_a__ + &capital_b__ * (&e__ * sub_atom.pow(&n_)).log()).pow(&p_)
                / (&b__ - &d__ * &sub_atom).pow(&m_ + &q_ + 2);
            let substitution_primitive = rubi_rhs_int(&substitution_integrand, substitution_symbol);
            let substitution = (&a__ + &b__ * x_) / (&c__ + &d__ * x_);
            let substituted =
                rubi_subst(&substitution_primitive, substitution_symbol, substitution);

            rubi_star(&b__ * &c__ - &a__ * &d__, substituted)
        },
    ));
}

fn push_rules_rule_2969(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_a__,
        capital_b__,
        a__,
        b__,
        c__,
        d__,
        e__,
        f__,
        g__,
        h__,
        i__,
        m_,
        n_,
        p_,
        q_,
        x_
    );
    rules.push(rubi_rule!(
        order: 2969,
        source: "Int[(f_.+g_.*x_)^m_.*(h_.+i_.*x_)^q_.*(A_.+B_.*Log[e_.*((a_.+b_.*x_)/(c_.+d_.*x_))^n_.])^p_.,x_Symbol] :=
          Unintegrable[(f+g*x)^m*(h+i*x)^q*(A+B*Log[e*((a+b*x)/(c+d*x))^n])^p,x] /;
        FreeQ[{a,b,c,d,e,f,g,h,i,A,B,m,n,p,q},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [f__, g__, m_, h__, i__, q_, capital_a__, capital_b__, e__, a__, b__, c__, d__, n_, p_, x_],
        optional: [f__, g__, m_, h__, i__, q_, capital_a__, capital_b__, e__, a__, b__, c__, d__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__, i__, capital_a__, capital_b__], x_)
                && freeq!([m_, n_, p_, q_], x_)
        },
        rhs: {
            let integrand = (&f__ + &g__ * x_).pow(&m_)
                * (&h__ + &i__ * x_).pow(&q_)
                * (&capital_a__
                    + &capital_b__
                        * (&e__ * ((&a__ + &b__ * x_) / (&c__ + &d__ * x_)).pow(&n_))
                            .log())
                .pow(&p_);

            rubi_unintegrable(integrand, x_)
        },
    ));
}

fn push_rules_rule_2970(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_a__,
        capital_b__,
        a__,
        b__,
        c__,
        d__,
        e__,
        f__,
        g__,
        h__,
        i__,
        m_,
        mn_,
        n_,
        p_,
        q_,
        x_
    );
    rules.push(rubi_rule!(
        order: 2970,
        source: "Int[(f_.+g_.*x_)^m_.*(h_.+i_.*x_)^q_.*(A_.+B_.*Log[e_.*(a_.+b_.*x_)^n_.*(c_.+d_.*x_)^mn_])^p_.,x_Symbol] :=
          Unintegrable[(f+g*x)^m*(h+i*x)^q*(A+B*Log[e*(a+b*x)^n/(c+d*x)^n])^p,x] /;
        FreeQ[{a,b,c,d,e,f,g,h,i,A,B,m,n,p,q},x] && EqQ[n+mn,0] && IntegerQ[n]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [f__, g__, m_, h__, i__, q_, capital_a__, capital_b__, e__, a__, b__, n_, c__, d__, mn_, p_, x_],
        optional: [f__, g__, m_, h__, i__, q_, capital_a__, capital_b__, e__, a__, b__, c__, d__, p_, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__, i__, capital_a__, capital_b__], x_)
                && freeq!([m_, n_, p_, q_], x_)
                && eqq!(&n_ + &mn_, 0)
                && integerq!(n_)
        },
        rhs: {
            let lhs = &a__ + &b__ * x_;
            let rhs = &c__ + &d__ * x_;
            let integrand = (&f__ + &g__ * x_).pow(&m_)
                * (&h__ + &i__ * x_).pow(&q_)
                * (&capital_a__ + &capital_b__ * (&e__ * lhs.pow(&n_) / rhs.pow(&n_)).log())
                    .pow(&p_);

            rubi_unintegrable(integrand, x_)
        },
    ));
}

fn push_rules_rule_2971(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        capital_a__,
        capital_b__,
        e__,
        m_,
        n_,
        p_,
        q_,
        u__,
        v__,
        w__,
        y__
    );
    rules.push(rubi_rule!(
        order: 2971,
        source: "Int[w_^m_.*y_^q_.*(A_.+B_.*Log[e_.*(u_/v_)^n_.])^p_.,x_Symbol] :=
          Int[ExpandToSum[w,x]^m*ExpandToSum[y,x]^q*(A+B*Log[e*(ExpandToSum[u,x]/ExpandToSum[v,x])^n])^p,x] /;
        FreeQ[{e,A,B,m,n,p,q},x] && LinearQ[{u,v,w,y},x] && Not[LinearMatchQ[{u,v,w,y},x]]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: w__.pow(m_)
            * y__.pow(q_)
            * (capital_a__ + capital_b__ * (e__ * (u__ / v__).pow(n_)).log()).pow(p_),
        with: [w__, m_, y__, q_, capital_a__, capital_b__, e__, u__, v__, n_, p_, x_],
        optional: [m_, q_, capital_a__, capital_b__, e__, n_, p_],
        when: {
            freeq!([e__, capital_a__, capital_b__, m_, n_, p_, q_], x_)
                && rubi_linear_q_list(&[&u__, &v__, &w__, &y__], x_)
                && !rubi_linear_match_q_list(&[&u__, &v__, &w__, &y__], x_)
        },
        rhs: {
            let expanded_w = rubi_expand_to_sum(&w__, x_);
            let expanded_y = rubi_expand_to_sum(&y__, x_);
            let expanded_u = rubi_expand_to_sum(&u__, x_);
            let expanded_v = rubi_expand_to_sum(&v__, x_);
            let recursive_integrand = expanded_w.pow(&m_)
                * expanded_y.pow(&q_)
                * (&capital_a__
                    + &capital_b__ * (&e__ * (&expanded_u / &expanded_v).pow(&n_)).log())
                .pow(&p_);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_2972(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        capital_a__,
        capital_b__,
        e__,
        m_,
        mn_,
        n_,
        p_,
        q_,
        u__,
        v__,
        w__,
        y__
    );
    rules.push(rubi_rule!(
        order: 2972,
        source: "Int[w_^m_.*y_^q_.*(A_.+B_.*Log[e_.*u_^n_.*v_^mn_])^p_.,x_Symbol] :=
          Int[ExpandToSum[w,x]^m*ExpandToSum[y,x]^q*(A+B*Log[e*ExpandToSum[u,x]^n/ExpandToSum[v,x]^n])^p,x] /;
        FreeQ[{e,A,B,m,n,p,q},x] && EqQ[n+mn,0] && IGtQ[n,0] && LinearQ[{u,v,w,y},x] && Not[LinearMatchQ[{u,v,w,y},x]]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: w__.pow(m_)
            * y__.pow(q_)
            * (capital_a__ + capital_b__ * (e__ * u__.pow(n_) * v__.pow(mn_)).log()).pow(p_),
        with: [w__, m_, y__, q_, capital_a__, capital_b__, e__, u__, n_, v__, mn_, p_, x_],
        optional: [m_, q_, capital_a__, capital_b__, e__, p_, n_],
        when: {
            freeq!([e__, capital_a__, capital_b__, m_, n_, p_, q_], x_)
                && eqq!(&n_ + &mn_, 0)
                && igtq!(n_, 0)
                && rubi_linear_q_list(&[&u__, &v__, &w__, &y__], x_)
                && !rubi_linear_match_q_list(&[&u__, &v__, &w__, &y__], x_)
        },
        rhs: {
            let expanded_w = rubi_expand_to_sum(&w__, x_);
            let expanded_y = rubi_expand_to_sum(&y__, x_);
            let expanded_u = rubi_expand_to_sum(&u__, x_);
            let expanded_v = rubi_expand_to_sum(&v__, x_);
            let recursive_integrand = expanded_w.pow(&m_)
                * expanded_y.pow(&q_)
                * (&capital_a__ + &capital_b__ * (&e__ * expanded_u.pow(&n_) / expanded_v.pow(&n_)).log())
                    .pow(&p_);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_2973(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_a__, capital_b__, e__, mn_, n_, p_, u__, v__, w__);
    rules.push(rubi_rule!(
        order: 2973,
        source: "Int[w_.*(A_.+B_.*Log[e_.*u_^n_.*v_^mn_])^p_.,x_Symbol] :=
          Subst[Int[w*(A+B*Log[e*(u/v)^n])^p,x],e*(u/v)^n,e*u^n/v^n] /;
        FreeQ[{e,A,B,n,p},x] && EqQ[n+mn,0] && LinearQ[{u,v},x] && Not[IntegerQ[n]]",
        desc: "Integration by substitution",
        refs: [],
        pattern: w__
            * (capital_a__ + capital_b__ * (e__ * u__.pow(n_) * v__.pow(mn_)).log()).pow(p_),
        with: [w__, capital_a__, capital_b__, e__, u__, n_, v__, mn_, p_, x_],
        optional: [w__, capital_a__, capital_b__, e__, p_, n_],
        when: {
            freeq!([e__, capital_a__, capital_b__, n_, p_], x_)
                && eqq!(&n_ + &mn_, 0)
                && rubi_linear_q_list(&[&u__, &v__], x_)
                && !integerq!(n_)
        },
        rhs: {
            let quotient_log_arg = &e__ * (&u__ / &v__).pow(&n_);
            let replacement_log_arg = &e__ * u__.pow(&n_) / v__.pow(&n_);
            let transformed_integrand = &w__
                * (&capital_a__ + &capital_b__ * quotient_log_arg.log()).pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, x_);

            rubi_subst_expression(
                &transformed,
                &quotient_log_arg,
                replacement_log_arg,
            )
        },
    ));
}

fn push_rules_rule_2974(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        capital_a__,
        capital_b__,
        a__,
        b__,
        c__,
        d__,
        e__,
        f__,
        g__,
        h__,
        m_,
        n_,
        p_,
        x_
    );
    rules.push(rubi_rule!(
        order: 2974,
        source: "Int[(f_.+g_.*x_+h_.*x_^2)^m_.*(A_.+B_.*Log[e_.*((a_.+b_.*x_)/(c_.+d_.*x_))^n_.])^p_.,x_Symbol] :=
          h^m/(b^m*d^m) \\[Star] Int[(a+b*x)^m*(c+d*x)^m*(A+B*Log[e*((a+b*x)/(c+d*x))^n])^p,x] /;
        FreeQ[{a,b,c,d,e,f,g,h,A,B,n,p},x] && EqQ[b*d*f-a*c*h,0] && EqQ[b*d*g-h*(b*c+a*d),0] && IntegerQ[m]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: (f__ + g__ * x_ + h__ * x_.pow(2)).pow(m_)
            * (capital_a__
                + capital_b__ * (e__ * ((a__ + b__ * x_) / (c__ + d__ * x_)).pow(n_)).log())
            .pow(p_),
        with: [f__, g__, h__, m_, capital_a__, capital_b__, e__, a__, b__, c__, d__, n_, p_, x_],
        optional: [f__, g__, h__, m_, capital_a__, capital_b__, e__, a__, b__, c__, d__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__, capital_a__, capital_b__, n_, p_], x_)
                && eqq!(&b__ * &d__ * &f__ - &a__ * &c__ * &h__, 0)
                && eqq!(&b__ * &d__ * &g__ - &h__ * (&b__ * &c__ + &a__ * &d__), 0)
                && integerq!(m_)
        },
        rhs: {
            let lhs = &a__ + &b__ * x_;
            let rhs = &c__ + &d__ * x_;
            let logarithmic =
                &capital_a__ + &capital_b__ * (&e__ * (&lhs / &rhs).pow(&n_)).log();
            let recursive_integrand = lhs.pow(&m_) * rhs.pow(&m_) * logarithmic.pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(h__.pow(&m_), recursive / (b__.pow(&m_) * d__.pow(&m_)))
        },
    ));
}

fn push_rules_rule_2975(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        capital_a__,
        capital_b__,
        a__,
        b__,
        c__,
        d__,
        e__,
        f__,
        g__,
        h__,
        m_,
        mn_,
        n_,
        p_,
        x_
    );
    rules.push(rubi_rule!(
        order: 2975,
        source: "Int[(f_.+g_.*x_+h_.*x_^2)^m_.*(A_.+B_.*Log[e_.*(a_.+b_.*x_)^n_.*(c_.+d_.*x_)^mn_])^p_.,x_Symbol] :=
          h^m/(b^m*d^m) \\[Star] Int[(a+b*x)^m*(c+d*x)^m*(A+B*Log[e*(a+b*x)^n/(c+d*x)^n])^p,x] /;
        FreeQ[{a,b,c,d,e,f,g,h,A,B,n,p},x] && EqQ[n+mn,0] && IGtQ[n,0] && EqQ[b*d*f-a*c*h,0] && EqQ[b*d*g-h*(b*c+a*d),0] && IntegerQ[m]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: (f__ + g__ * x_ + h__ * x_.pow(2)).pow(m_)
            * (capital_a__
                + capital_b__
                    * (e__ * (a__ + b__ * x_).pow(n_) * (c__ + d__ * x_).pow(mn_)).log())
            .pow(p_),
        with: [f__, g__, h__, m_, capital_a__, capital_b__, e__, a__, b__, n_, c__, d__, mn_, p_, x_],
        optional: [f__, g__, h__, m_, capital_a__, capital_b__, e__, a__, b__, c__, d__, p_, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__, capital_a__, capital_b__, n_, p_], x_)
                && eqq!(&n_ + &mn_, 0)
                && igtq!(n_, 0)
                && eqq!(&b__ * &d__ * &f__ - &a__ * &c__ * &h__, 0)
                && eqq!(&b__ * &d__ * &g__ - &h__ * (&b__ * &c__ + &a__ * &d__), 0)
                && integerq!(m_)
        },
        rhs: {
            let lhs = &a__ + &b__ * x_;
            let rhs = &c__ + &d__ * x_;
            let logarithmic =
                &capital_a__ + &capital_b__ * (&e__ * lhs.pow(&n_) / rhs.pow(&n_)).log();
            let recursive_integrand = lhs.pow(&m_) * rhs.pow(&m_) * logarithmic.pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(h__.pow(&m_), recursive / (b__.pow(&m_) * d__.pow(&m_)))
        },
    ));
}

fn push_rules_rule_2976(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        capital_a__,
        capital_b__,
        a__,
        b__,
        c__,
        d__,
        e__,
        m_,
        n_,
        p_,
        p2x__,
        x_
    );
    rules.push(rubi_rule!(
        order: 2976,
        source: "Int[P2x_^m_.*(A_.+B_.*Log[e_.*((a_.+b_.*x_)/(c_.+d_.*x_))^n_.])^p_.,x_Symbol] :=
          With[{f=Coeff[P2x,x,0],g=Coeff[P2x,x,1],h=Coeff[P2x,x,2]},
          (b*c-a*d) \\[Star]
            Subst[Int[(b^2*f-a*b*g+a^2*h-(2*b*d*f-b*c*g-a*d*g+2*a*c*h)*x+(d^2*f-c*d*g+c^2*h)*x^2)^m*(A+B*Log[e*x^n])^p/
              (b-d*x)^(2*(m+1)),x],x,(a+b*x)/(c+d*x)]] /;
        FreeQ[{a,b,c,d,e,A,B,n},x] && PolyQ[P2x,x,2] && NeQ[b*c-a*d,0] && IntegerQ[m] && IGtQ[p,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: p2x__.pow(m_)
            * (capital_a__
                + capital_b__ * (e__ * ((a__ + b__ * x_) / (c__ + d__ * x_)).pow(n_)).log())
            .pow(p_),
        with: [p2x__, m_, capital_a__, capital_b__, e__, a__, b__, c__, d__, n_, p_, x_],
        optional: [m_, capital_a__, capital_b__, e__, a__, b__, c__, d__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, capital_a__, capital_b__, n_], x_)
                && rubi_poly_q_degree(&p2x__, x_, 2)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && integerq!(m_)
                && igtq!(p_, 0)
        },
        rhs: {
            let f = rubi_coeff(&p2x__, x_, 0).rubi_rhs();
            let g = rubi_coeff(&p2x__, x_, 1).rubi_rhs();
            let h = rubi_coeff(&p2x__, x_, 2).rubi_rhs();
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let transformed_quadratic = b__.pow(2) * &f - &a__ * &b__ * &g + a__.pow(2) * &h
                - (Atom::num(2) * &b__ * &d__ * &f
                    - &b__ * &c__ * &g
                    - &a__ * &d__ * &g
                    + Atom::num(2) * &a__ * &c__ * &h)
                    * &sub_atom
                + (d__.pow(2) * &f - &c__ * &d__ * &g + c__.pow(2) * &h)
                    * sub_atom.pow(2);
            let substitution_integrand = transformed_quadratic.pow(&m_)
                * (&capital_a__ + &capital_b__ * (&e__ * sub_atom.pow(&n_)).log()).pow(&p_)
                / (&b__ - &d__ * &sub_atom).pow(Atom::num(2) * (&m_ + 1));
            let substitution_primitive = rubi_rhs_int(&substitution_integrand, substitution_symbol);
            let substitution = (&a__ + &b__ * x_) / (&c__ + &d__ * x_);
            let substituted =
                rubi_subst(&substitution_primitive, substitution_symbol, substitution);

            rubi_star(&b__ * &c__ - &a__ * &d__, substituted)
        },
    ));
}

fn push_rules_rule_2977(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        capital_a__,
        capital_b__,
        a__,
        b__,
        c__,
        d__,
        e__,
        m_,
        mn_,
        n_,
        p_,
        p2x__,
        x_
    );
    rules.push(rubi_rule!(
        order: 2977,
        source: "Int[P2x_^m_.*(A_.+B_.*Log[e_.*(a_.+b_.*x_)^n_.*(c_.+d_.*x_)^mn_])^p_.,x_Symbol] :=
          With[{f=Coeff[P2x,x,0],g=Coeff[P2x,x,1],h=Coeff[P2x,x,2]},
          (b*c-a*d) \\[Star]
            Subst[Int[(b^2*f-a*b*g+a^2*h-(2*b*d*f-b*c*g-a*d*g+2*a*c*h)*x+(d^2*f-c*d*g+c^2*h)*x^2)^m*(A+B*Log[e*x^n])^p/
              (b-d*x)^(2*(m+1)),x],x,(a+b*x)/(c+d*x)]] /;
        FreeQ[{a,b,c,d,e,A,B,n},x] && PolyQ[P2x,x,2] && EqQ[n+mn,0] && IGtQ[n,0] && NeQ[b*c-a*d,0] && IntegerQ[m] && IGtQ[p,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: p2x__.pow(m_)
            * (capital_a__
                + capital_b__
                    * (e__ * (a__ + b__ * x_).pow(n_) * (c__ + d__ * x_).pow(mn_)).log())
            .pow(p_),
        with: [p2x__, m_, capital_a__, capital_b__, e__, a__, b__, n_, c__, d__, mn_, p_, x_],
        optional: [m_, capital_a__, capital_b__, e__, a__, b__, c__, d__, p_, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, capital_a__, capital_b__, n_], x_)
                && rubi_poly_q_degree(&p2x__, x_, 2)
                && eqq!(&n_ + &mn_, 0)
                && igtq!(n_, 0)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && integerq!(m_)
                && igtq!(p_, 0)
        },
        rhs: {
            let f = rubi_coeff(&p2x__, x_, 0).rubi_rhs();
            let g = rubi_coeff(&p2x__, x_, 1).rubi_rhs();
            let h = rubi_coeff(&p2x__, x_, 2).rubi_rhs();
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let transformed_quadratic = b__.pow(2) * &f - &a__ * &b__ * &g + a__.pow(2) * &h
                - (Atom::num(2) * &b__ * &d__ * &f
                    - &b__ * &c__ * &g
                    - &a__ * &d__ * &g
                    + Atom::num(2) * &a__ * &c__ * &h)
                    * &sub_atom
                + (d__.pow(2) * &f - &c__ * &d__ * &g + c__.pow(2) * &h)
                    * sub_atom.pow(2);
            let substitution_integrand = transformed_quadratic.pow(&m_)
                * (&capital_a__ + &capital_b__ * (&e__ * sub_atom.pow(&n_)).log()).pow(&p_)
                / (&b__ - &d__ * &sub_atom).pow(Atom::num(2) * (&m_ + 1));
            let substitution_primitive = rubi_rhs_int(&substitution_integrand, substitution_symbol);
            let substitution = (&a__ + &b__ * x_) / (&c__ + &d__ * x_);
            let substituted =
                rubi_subst(&substitution_primitive, substitution_symbol, substitution);

            rubi_star(&b__ * &c__ - &a__ * &d__, substituted)
        },
    ));
}

// Generated shared pattern builders.

#[inline(never)]
fn rubi_shared_pattern_0(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let capital_a__ = symbols.capital_a__;
    let capital_b__ = symbols.capital_b__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let g__ = symbols.g__;
    let h__ = symbols.h__;
    let i__ = symbols.i__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let q_ = symbols.q_;
    let x_ = symbols.x_;
    (f__ + g__ * x_).pow(m_)
        * (h__ + i__ * x_).pow(q_)
        * (capital_a__ + capital_b__ * (e__ * ((a__ + b__ * x_) / (c__ + d__ * x_)).pow(n_)).log())
            .pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let capital_a__ = symbols.capital_a__;
    let capital_b__ = symbols.capital_b__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let g__ = symbols.g__;
    let h__ = symbols.h__;
    let i__ = symbols.i__;
    let m_ = symbols.m_;
    let mn_ = symbols.mn_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let q_ = symbols.q_;
    let x_ = symbols.x_;
    (f__ + g__ * x_).pow(m_)
        * (h__ + i__ * x_).pow(q_)
        * (capital_a__
            + capital_b__ * (e__ * (a__ + b__ * x_).pow(n_) * (c__ + d__ * x_).pow(mn_)).log())
        .pow(p_)
}
