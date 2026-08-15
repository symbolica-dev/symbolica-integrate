use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_2935(rules);
    push_rules_rule_2936(rules);
    push_rules_rule_2937(rules);
    push_rules_rule_2938(rules);
    push_rules_rule_2939(rules);
    push_rules_rule_2940(rules);
    push_rules_rule_2941(rules);
    push_rules_rule_2942(rules);
    push_rules_rule_2943(rules);
    push_rules_rule_2944(rules);
    push_rules_rule_2945(rules);
    push_rules_rule_2946(rules);
    push_rules_rule_2947(rules);
    push_rules_rule_2948(rules);
    push_rules_rule_2949(rules);
    push_rules_rule_2950(rules);
    push_rules_rule_2951(rules);
    push_rules_rule_2952(rules);
    push_rules_rule_2953(rules);
    push_rules_rule_2954(rules);
    push_rules_rule_2955(rules);
    push_rules_rule_2956(rules);
    push_rules_rule_2957(rules);
    push_rules_rule_2958(rules);
}

fn push_rules_rule_2935(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_a__,
        capital_b__,
        a__,
        b__,
        c__,
        d__,
        e__,
        n_,
        p_,
        x_
    );
    rules.push(rubi_rule!(
        order: 2935,
        source: "Int[(A_.+B_.*Log[e_.*((a_.+b_.*x_)/(c_.+d_.*x_))^n_.])^p_.,x_Symbol] :=
          (a+b*x)*(A+B*Log[e*((a+b*x)/(c+d*x))^n])^p/b -
          B*n*p*(b*c-a*d)/b \\[Star] Int[(A+B*Log[e*((a+b*x)/(c+d*x))^n])^(p-1)/(c+d*x),x] /;
        FreeQ[{a,b,c,d,e,A,B,n},x] && NeQ[b*c-a*d,0] && IGtQ[p,0]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [capital_a__, capital_b__, e__, a__, b__, c__, d__, n_, p_, x_],
        optional: [capital_a__, capital_b__, e__, a__, b__, c__, d__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, capital_a__, capital_b__, n_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && igtq!(p_, 0)
        },
        rhs: {
            let lhs = &a__ + &b__ * x_;
            let rhs = &c__ + &d__ * x_;
            let determinant = &b__ * &c__ - &a__ * &d__;
            let logarithmic =
                &capital_a__ + &capital_b__ * (&e__ * (&lhs / &rhs).pow(&n_)).log();
            let recursive_integrand = logarithmic.pow(&p_ - 1) / &rhs;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(lhs * logarithmic.pow(&p_) / &b__), x_)
                    - rubi_star(&capital_b__ * &n_ * &p_ * determinant / &b__, recursive)
        },
    ));
}

fn push_rules_rule_2936(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_a__,
        capital_b__,
        a__,
        b__,
        c__,
        d__,
        e__,
        mn_,
        n_,
        p_,
        x_
    );
    rules.push(rubi_rule!(
        order: 2936,
        source: "Int[(A_.+B_.*Log[e_.*(a_.+b_.*x_)^n_.*(c_.+d_.*x_)^mn_])^p_.,x_Symbol] :=
          (a+b*x)*(A+B*Log[e*(a+b*x)^n/(c+d*x)^n])^p/b -
          B*n*p*(b*c-a*d)/b \\[Star] Int[(A+B*Log[e*(a+b*x)^n/(c+d*x)^n])^(p-1)/(c+d*x),x] /;
        FreeQ[{a,b,c,d,e,A,B,n},x] && EqQ[n+mn,0] && NeQ[b*c-a*d,0] && IGtQ[p,0]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [capital_a__, capital_b__, e__, a__, b__, n_, c__, d__, mn_, p_, x_],
        optional: [capital_a__, capital_b__, e__, a__, b__, c__, d__, p_, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, capital_a__, capital_b__, n_], x_)
                && eqq!(&n_ + &mn_, 0)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && igtq!(p_, 0)
        },
        rhs: {
            let lhs = &a__ + &b__ * x_;
            let rhs = &c__ + &d__ * x_;
            let determinant = &b__ * &c__ - &a__ * &d__;
            let logarithmic = &capital_a__
                + &capital_b__ * (&e__ * lhs.pow(&n_) / rhs.pow(&n_)).log();
            let recursive_integrand = logarithmic.pow(&p_ - 1) / &rhs;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(lhs * logarithmic.pow(&p_) / &b__), x_)
                    - rubi_star(&capital_b__ * &n_ * &p_ * determinant / &b__, recursive)
        },
    ));
}

fn push_rules_rule_2937(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_a__,
        capital_b__,
        a__,
        b__,
        c__,
        d__,
        e__,
        n_,
        p_,
        x_
    );
    rules.push(rubi_rule!(
        order: 2937,
        source: "Int[(A_.+B_.*Log[e_.*((a_.+b_.*x_)/(c_.+d_.*x_))^n_.])^p_,x_Symbol] :=
          Unintegrable[(A+B*Log[e*((a+b*x)/(c+d*x))^n])^p,x] /;
        FreeQ[{a,b,c,d,e,A,B,n,p},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [capital_a__, capital_b__, e__, a__, b__, c__, d__, n_, p_, x_],
        optional: [capital_a__, capital_b__, e__, a__, b__, c__, d__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, capital_a__, capital_b__, n_, p_], x_)
        },
        rhs: {
            let lhs = &a__ + &b__ * x_;
            let rhs = &c__ + &d__ * x_;
            let integrand =
                (&capital_a__ + &capital_b__ * (&e__ * (&lhs / &rhs).pow(&n_)).log()).pow(&p_);

            rubi_unintegrable(integrand, x_)
        },
    ));
}

fn push_rules_rule_2938(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_a__,
        capital_b__,
        a__,
        b__,
        c__,
        d__,
        e__,
        mn_,
        n_,
        p_,
        x_
    );
    rules.push(rubi_rule!(
        order: 2938,
        source: "Int[(A_.+B_.*Log[e_.*(a_.+b_.*x_)^n_.*(c_.+d_.*x_)^mn_])^p_,x_Symbol] :=
          Unintegrable[(A+B*Log[e*(a+b*x)^n/(c+d*x)^n])^p,x] /;
        FreeQ[{a,b,c,d,e,A,B,n,p},x] && EqQ[n+mn,0]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [capital_a__, capital_b__, e__, a__, b__, n_, c__, d__, mn_, p_, x_],
        optional: [capital_a__, capital_b__, e__, a__, b__, c__, d__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, capital_a__, capital_b__, n_, p_], x_)
                && eqq!(&n_ + &mn_, 0)
        },
        rhs: {
            let lhs = &a__ + &b__ * x_;
            let rhs = &c__ + &d__ * x_;
            let integrand =
                (&capital_a__ + &capital_b__ * (&e__ * lhs.pow(&n_) / rhs.pow(&n_)).log()).pow(&p_);

            rubi_unintegrable(integrand, x_)
        },
    ));
}

fn push_rules_rule_2939(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_a__, capital_b__, e__, n_, p_, u__, v__);
    rules.push(rubi_rule!(
        order: 2939,
        source: "Int[(A_.+B_.*Log[e_.*(u_/v_)^n_.])^p_.,x_Symbol] :=
          Int[(A+B*Log[e*(ExpandToSum[u,x]/ExpandToSum[v,x])^n])^p,x] /;
        FreeQ[{e,A,B,n,p},x] && LinearQ[{u,v},x] && Not[LinearMatchQ[{u,v},x]]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: (capital_a__ + capital_b__ * (e__ * (u__ / v__).pow(n_)).log()).pow(p_),
        with: [capital_a__, capital_b__, e__, u__, v__, n_, p_, x_],
        optional: [capital_a__, capital_b__, e__, n_, p_],
        when: {
            freeq!([e__, capital_a__, capital_b__, n_, p_], x_)
                && rubi_linear_q_list(&[&u__, &v__], x_)
                && !rubi_linear_match_q_list(&[&u__, &v__], x_)
        },
        rhs: {
            let expanded_u = rubi_expand_to_sum(&u__, x_);
            let expanded_v = rubi_expand_to_sum(&v__, x_);
            let recursive_integrand = (&capital_a__
                + &capital_b__ * (&e__ * (&expanded_u / &expanded_v).pow(&n_)).log())
            .pow(&p_);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_2940(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_a__, capital_b__, e__, mn_, n_, p_, u__, v__);
    rules.push(rubi_rule!(
        order: 2940,
        source: "Int[(A_.+B_.*Log[e_.*u_^n_.*v_^mn_])^p_.,x_Symbol] :=
          Int[(A+B*Log[e*ExpandToSum[u,x]^n/ExpandToSum[v,x]^n])^p,x] /;
        FreeQ[{e,A,B,n,p},x] && EqQ[n+mn,0] && IGtQ[n,0] && LinearQ[{u,v},x] && Not[LinearMatchQ[{u,v},x]]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: (capital_a__ + capital_b__ * (e__ * u__.pow(n_) * v__.pow(mn_)).log()).pow(p_),
        with: [capital_a__, capital_b__, e__, u__, n_, v__, mn_, p_, x_],
        optional: [capital_a__, capital_b__, e__, p_, n_],
        when: {
            freeq!([e__, capital_a__, capital_b__, n_, p_], x_)
                && eqq!(&n_ + &mn_, 0)
                && igtq!(n_, 0)
                && rubi_linear_q_list(&[&u__, &v__], x_)
                && !rubi_linear_match_q_list(&[&u__, &v__], x_)
        },
        rhs: {
            let expanded_u = rubi_expand_to_sum(&u__, x_);
            let expanded_v = rubi_expand_to_sum(&v__, x_);
            let recursive_integrand = (&capital_a__
                + &capital_b__ * (&e__ * expanded_u.pow(&n_) / expanded_v.pow(&n_)).log())
            .pow(&p_);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_2941(rules: &mut Vec<RubiRule>) {
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
        n_,
        x_
    );
    rules.push(rubi_rule!(
        order: 2941,
        source: "Int[(A_.+B_.*Log[e_.*((a_.+b_.*x_)/(c_.+d_.*x_))^n_.])/(f_.+g_.*x_),x_Symbol] :=
          -Log[-(b*c-a*d)/(d*(a+b*x))]*(A+B*Log[e*((a+b*x)/(c+d*x))^n])/g +
          B*n*(b*c-a*d)/g \\[Star] Int[Log[-(b*c-a*d)/(d*(a+b*x))]/((a+b*x)*(c+d*x)),x] /;
        FreeQ[{a,b,c,d,e,f,g,A,B,n},x] && NeQ[b*c-a*d,0] && EqQ[b*f-a*g,0]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [capital_a__, capital_b__, e__, a__, b__, c__, d__, n_, f__, g__, x_],
        optional: [capital_a__, capital_b__, e__, a__, b__, c__, d__, n_, f__, g__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, capital_a__, capital_b__, n_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(&b__ * &f__ - &a__ * &g__, 0)
        },
        rhs: {
            let lhs = &a__ + &b__ * x_;
            let rhs = &c__ + &d__ * x_;
            let determinant = &b__ * &c__ - &a__ * &d__;
            let logarithmic =
                &capital_a__ + &capital_b__ * (&e__ * (&lhs / &rhs).pow(&n_)).log();
            let log_factor = (-&determinant / (&d__ * &lhs)).log();
            let recursive_integrand = &log_factor / (&lhs * &rhs);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            rubi_simp(&(-&log_factor * logarithmic / &g__), x_)
                    + rubi_star(&capital_b__ * &n_ * determinant / &g__, recursive)
        },
    ));
}

fn push_rules_rule_2942(rules: &mut Vec<RubiRule>) {
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
        mn_,
        n_,
        x_
    );
    rules.push(rubi_rule!(
        order: 2942,
        source: "Int[(A_.+B_.*Log[e_.*(a_.+b_.*x_)^n_.*(c_.+d_.*x_)^mn_])/(f_.+g_.*x_),x_Symbol] :=
          -Log[-(b*c-a*d)/(d*(a+b*x))]*(A+B*Log[e*(a+b*x)^n/(c+d*x)^n])/g +
          B*n*(b*c-a*d)/g \\[Star] Int[Log[-(b*c-a*d)/(d*(a+b*x))]/((a+b*x)*(c+d*x)),x] /;
        FreeQ[{a,b,c,d,e,f,g,A,B,n},x] && EqQ[n+mn,0] && NeQ[b*c-a*d,0] && EqQ[b*f-a*g,0]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [capital_a__, capital_b__, e__, a__, b__, n_, c__, d__, mn_, f__, g__, x_],
        optional: [capital_a__, capital_b__, e__, a__, b__, c__, d__, f__, g__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, capital_a__, capital_b__, n_], x_)
                && eqq!(&n_ + &mn_, 0)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(&b__ * &f__ - &a__ * &g__, 0)
        },
        rhs: {
            let lhs = &a__ + &b__ * x_;
            let rhs = &c__ + &d__ * x_;
            let determinant = &b__ * &c__ - &a__ * &d__;
            let logarithmic =
                &capital_a__ + &capital_b__ * (&e__ * lhs.pow(&n_) / rhs.pow(&n_)).log();
            let log_factor = (-&determinant / (&d__ * &lhs)).log();
            let recursive_integrand = &log_factor / (&lhs * &rhs);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            rubi_simp(&(-&log_factor * logarithmic / &g__), x_)
                    + rubi_star(&capital_b__ * &n_ * determinant / &g__, recursive)
        },
    ));
}

fn push_rules_rule_2943(rules: &mut Vec<RubiRule>) {
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
        n_,
        x_
    );
    rules.push(rubi_rule!(
        order: 2943,
        source: "Int[(A_.+B_.*Log[e_.*((a_.+b_.*x_)/(c_.+d_.*x_))^n_.])/(f_.+g_.*x_),x_Symbol] :=
          -Log[(b*c-a*d)/(b*(c+d*x))]*(A+B*Log[e*((a+b*x)/(c+d*x))^n])/g +
          B*n*(b*c-a*d)/g \\[Star] Int[Log[(b*c-a*d)/(b*(c+d*x))]/((a+b*x)*(c+d*x)),x] /;
        FreeQ[{a,b,c,d,e,f,g,A,B,n},x] && NeQ[b*c-a*d,0] && EqQ[d*f-c*g,0]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [capital_a__, capital_b__, e__, a__, b__, c__, d__, n_, f__, g__, x_],
        optional: [capital_a__, capital_b__, e__, a__, b__, c__, d__, n_, f__, g__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, capital_a__, capital_b__, n_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(&d__ * &f__ - &c__ * &g__, 0)
        },
        rhs: {
            let lhs = &a__ + &b__ * x_;
            let rhs = &c__ + &d__ * x_;
            let determinant = &b__ * &c__ - &a__ * &d__;
            let logarithmic =
                &capital_a__ + &capital_b__ * (&e__ * (&lhs / &rhs).pow(&n_)).log();
            let log_factor = (&determinant / (&b__ * &rhs)).log();
            let recursive_integrand = &log_factor / (&lhs * &rhs);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            rubi_simp(&(-&log_factor * logarithmic / &g__), x_)
                    + rubi_star(&capital_b__ * &n_ * determinant / &g__, recursive)
        },
    ));
}

fn push_rules_rule_2944(rules: &mut Vec<RubiRule>) {
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
        mn_,
        n_,
        x_
    );
    rules.push(rubi_rule!(
        order: 2944,
        source: "Int[(A_.+B_.*Log[e_.*(a_.+b_.*x_)^n_.*(c_.+d_.*x_)^mn_])/(f_.+g_.*x_),x_Symbol] :=
          -Log[(b*c-a*d)/(b*(c+d*x))]*(A+B*Log[e*(a+b*x)^n/(c+d*x)^n])/g +
          B*n*(b*c-a*d)/g \\[Star] Int[Log[(b*c-a*d)/(b*(c+d*x))]/((a+b*x)*(c+d*x)),x] /;
        FreeQ[{a,b,c,d,e,f,g,A,B,n},x] && EqQ[n+mn,0] && NeQ[b*c-a*d,0] && EqQ[d*f-c*g,0]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [capital_a__, capital_b__, e__, a__, b__, n_, c__, d__, mn_, f__, g__, x_],
        optional: [capital_a__, capital_b__, e__, a__, b__, c__, d__, f__, g__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, capital_a__, capital_b__, n_], x_)
                && eqq!(&n_ + &mn_, 0)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(&d__ * &f__ - &c__ * &g__, 0)
        },
        rhs: {
            let lhs = &a__ + &b__ * x_;
            let rhs = &c__ + &d__ * x_;
            let determinant = &b__ * &c__ - &a__ * &d__;
            let logarithmic =
                &capital_a__ + &capital_b__ * (&e__ * lhs.pow(&n_) / rhs.pow(&n_)).log();
            let log_factor = (&determinant / (&b__ * &rhs)).log();
            let recursive_integrand = &log_factor / (&lhs * &rhs);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            rubi_simp(&(-&log_factor * logarithmic / &g__), x_)
                    + rubi_star(&capital_b__ * &n_ * determinant / &g__, recursive)
        },
    ));
}

fn push_rules_rule_2945(rules: &mut Vec<RubiRule>) {
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
        n_,
        x_
    );
    rules.push(rubi_rule!(
        order: 2945,
        source: "Int[(A_.+B_.*Log[e_.*((a_.+b_.*x_)/(c_.+d_.*x_))^n_.])/(f_.+g_.*x_),x_Symbol] :=
          Log[f+g*x]*(A+B*Log[e*((a+b*x)/(c+d*x))^n])/g -
          b*B*n/g \\[Star] Int[Log[f+g*x]/(a+b*x),x] +
          B*d*n/g \\[Star] Int[Log[f+g*x]/(c+d*x),x] /;
        FreeQ[{a,b,c,d,e,f,g,A,B,n},x] && NeQ[b*c-a*d,0]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [capital_a__, capital_b__, e__, a__, b__, c__, d__, n_, f__, g__, x_],
        optional: [capital_a__, capital_b__, e__, a__, b__, c__, d__, n_, f__, g__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, capital_a__, capital_b__, n_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
        },
        rhs: {
            let lhs = &a__ + &b__ * x_;
            let rhs = &c__ + &d__ * x_;
            let linear_denominator = &f__ + &g__ * x_;
            let linear_log = linear_denominator.log();
            let logarithmic =
                &capital_a__ + &capital_b__ * (&e__ * (&lhs / &rhs).pow(&n_)).log();
            let first_recursive = rubi_rhs_int(&(&linear_log / &lhs), x_);
            let second_recursive = rubi_rhs_int(&(&linear_log / &rhs), x_);

            rubi_simp(&(&linear_log * logarithmic / &g__), x_)
                    - rubi_star(&b__ * &capital_b__ * &n_ / &g__, first_recursive)
                    + rubi_star(&capital_b__ * &d__ * &n_ / &g__, second_recursive)
        },
    ));
}

fn push_rules_rule_2946(rules: &mut Vec<RubiRule>) {
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
        mn_,
        n_,
        x_
    );
    rules.push(rubi_rule!(
        order: 2946,
        source: "Int[(A_.+B_.*Log[e_.*(a_.+b_.*x_)^n_.*(c_.+d_.*x_)^mn_])/(f_.+g_.*x_),x_Symbol] :=
          Log[f+g*x]*(A+B*Log[e*(a+b*x)^n/(c+d*x)^n])/g -
          b*B*n/g \\[Star] Int[Log[f+g*x]/(a+b*x),x] +
          B*d*n/g \\[Star] Int[Log[f+g*x]/(c+d*x),x] /;
        FreeQ[{a,b,c,d,e,f,g,A,B,n},x] && EqQ[n+mn,0] && NeQ[b*c-a*d,0]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [capital_a__, capital_b__, e__, a__, b__, n_, c__, d__, mn_, f__, g__, x_],
        optional: [capital_a__, capital_b__, e__, a__, b__, c__, d__, f__, g__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, capital_a__, capital_b__, n_], x_)
                && eqq!(&n_ + &mn_, 0)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
        },
        rhs: {
            let lhs = &a__ + &b__ * x_;
            let rhs = &c__ + &d__ * x_;
            let linear_denominator = &f__ + &g__ * x_;
            let linear_log = linear_denominator.log();
            let logarithmic =
                &capital_a__ + &capital_b__ * (&e__ * lhs.pow(&n_) / rhs.pow(&n_)).log();
            let first_recursive = rubi_rhs_int(&(&linear_log / &lhs), x_);
            let second_recursive = rubi_rhs_int(&(&linear_log / &rhs), x_);

            rubi_simp(&(&linear_log * logarithmic / &g__), x_)
                    - rubi_star(&b__ * &capital_b__ * &n_ / &g__, first_recursive)
                    + rubi_star(&capital_b__ * &d__ * &n_ / &g__, second_recursive)
        },
    ));
}

fn push_rules_rule_2947(rules: &mut Vec<RubiRule>) {
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
        m_,
        n_,
        x_
    );
    rules.push(rubi_rule!(
        order: 2947,
        source: "Int[(f_.+g_.*x_)^m_.*(A_.+B_.*Log[e_.*((a_.+b_.*x_)/(c_.+d_.*x_))^n_.]),x_Symbol] :=
          (f+g*x)^(m+1)*(A+B*Log[e*((a+b*x)/(c+d*x))^n])/(g*(m+1)) -
          B*n*(b*c-a*d)/(g*(m+1)) \\[Star] Int[(f+g*x)^(m+1)/((a+b*x)*(c+d*x)),x] /;
        FreeQ[{a,b,c,d,e,f,g,A,B,m,n},x] && NeQ[b*c-a*d,0] && NeQ[m,-1] && NeQ[m,-2]",
        desc: "Integration by parts",
        refs: [],
        pattern: (f__ + g__ * x_).pow(m_)
            * (capital_a__
                + capital_b__ * (e__ * ((a__ + b__ * x_) / (c__ + d__ * x_)).pow(n_)).log()),
        with: [f__, g__, m_, capital_a__, capital_b__, e__, a__, b__, c__, d__, n_, x_],
        optional: [f__, g__, m_, capital_a__, capital_b__, e__, a__, b__, c__, d__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, capital_a__, capital_b__, m_, n_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && neq!(m_, -1)
                && neq!(m_, -2)
        },
        rhs: {
            let lhs = &a__ + &b__ * x_;
            let rhs = &c__ + &d__ * x_;
            let determinant = &b__ * &c__ - &a__ * &d__;
            let m1 = &m_ + 1;
            let linear_denominator = &f__ + &g__ * x_;
            let raised_linear = linear_denominator.pow(&m1);
            let logarithmic =
                &capital_a__ + &capital_b__ * (&e__ * (&lhs / &rhs).pow(&n_)).log();
            let recursive_integrand = &raised_linear / (&lhs * &rhs);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let denominator = &g__ * &m1;

            rubi_simp(&(&raised_linear * logarithmic / &denominator), x_)
                    - rubi_star(&capital_b__ * &n_ * determinant / &denominator, recursive)
        },
    ));
}

fn push_rules_rule_2948(rules: &mut Vec<RubiRule>) {
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
        m_,
        mn_,
        n_,
        x_
    );
    rules.push(rubi_rule!(
        order: 2948,
        source: "Int[(f_.+g_.*x_)^m_.*(A_.+B_.*Log[e_.*(a_.+b_.*x_)^n_.*(c_.+d_.*x_)^mn_]),x_Symbol] :=
          (f+g*x)^(m+1)*(A+B*Log[e*(a+b*x)^n/(c+d*x)^n])/(g*(m+1)) -
          B*n*(b*c-a*d)/(g*(m+1)) \\[Star] Int[(f+g*x)^(m+1)/((a+b*x)*(c+d*x)),x] /;
        FreeQ[{a,b,c,d,e,f,g,A,B,m,n},x] && EqQ[n+mn,0] && NeQ[b*c-a*d,0] && NeQ[m,-1] && Not[EqQ[m,-2] && IntegerQ[n]]",
        desc: "Integration by parts",
        refs: [],
        pattern: (f__ + g__ * x_).pow(m_)
            * (capital_a__
                + capital_b__
                    * (e__ * (a__ + b__ * x_).pow(n_) * (c__ + d__ * x_).pow(mn_)).log()),
        with: [f__, g__, m_, capital_a__, capital_b__, e__, a__, b__, n_, c__, d__, mn_, x_],
        optional: [f__, g__, m_, capital_a__, capital_b__, e__, a__, b__, c__, d__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, capital_a__, capital_b__, m_, n_], x_)
                && eqq!(&n_ + &mn_, 0)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && neq!(m_, -1)
                && !(eqq!(m_, -2) && integerq!(n_))
        },
        rhs: {
            let lhs = &a__ + &b__ * x_;
            let rhs = &c__ + &d__ * x_;
            let determinant = &b__ * &c__ - &a__ * &d__;
            let m1 = &m_ + 1;
            let linear_denominator = &f__ + &g__ * x_;
            let raised_linear = linear_denominator.pow(&m1);
            let logarithmic =
                &capital_a__ + &capital_b__ * (&e__ * lhs.pow(&n_) / rhs.pow(&n_)).log();
            let recursive_integrand = &raised_linear / (&lhs * &rhs);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let denominator = &g__ * &m1;

            rubi_simp(&(&raised_linear * logarithmic / &denominator), x_)
                    - rubi_star(&capital_b__ * &n_ * determinant / &denominator, recursive)
        },
    ));
}

fn push_rules_rule_2949(rules: &mut Vec<RubiRule>) {
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
        m_,
        n_,
        p_,
        x_
    );
    rules.push(rubi_rule!(
        order: 2949,
        source: "Int[(f_.+g_.*x_)^m_.*(A_.+B_.*Log[e_.*((a_.+b_.*x_)/(c_.+d_.*x_))^n_.])^p_.,x_Symbol] :=
          (b*c-a*d)^(m+1)*(g/b)^m \\[Star] Subst[Int[x^m*(A+B*Log[e*x^n])^p/(b-d*x)^(m+2),x],x,(a+b*x)/(c+d*x)] /;
        FreeQ[{a,b,c,d,e,f,g,A,B,n},x] && NeQ[b*c-a*d,0] && IntegersQ[m,p] && EqQ[b*f-a*g,0] && (GtQ[p,0] || LtQ[m,-1])",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [f__, g__, m_, capital_a__, capital_b__, e__, a__, b__, c__, d__, n_, p_, x_],
        optional: [f__, g__, m_, capital_a__, capital_b__, e__, a__, b__, c__, d__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, capital_a__, capital_b__, n_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && integersq!([m_, p_])
                && eqq!(&b__ * &f__ - &a__ * &g__, 0)
                && (gtq!(p_, 0) || ltq!(m_, -1))
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let substitution_integrand = sub_atom.pow(&m_)
                * (&capital_a__ + &capital_b__ * (&e__ * sub_atom.pow(&n_)).log()).pow(&p_)
                / (&b__ - &d__ * &sub_atom).pow(&m_ + 2);
            let substitution_primitive = rubi_rhs_int(&substitution_integrand, substitution_symbol);
            let substitution = (&a__ + &b__ * x_) / (&c__ + &d__ * x_);
            let coefficient =
                (&b__ * &c__ - &a__ * &d__).pow(&m_ + 1) * (&g__ / &b__).pow(&m_);
            let substituted =
                rubi_subst(&substitution_primitive, substitution_symbol, substitution);

            rubi_star(coefficient, substituted)
        },
    ));
}

fn push_rules_rule_2950(rules: &mut Vec<RubiRule>) {
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
        m_,
        mn_,
        n_,
        p_,
        x_
    );
    rules.push(rubi_rule!(
        order: 2950,
        source: "Int[(f_.+g_.*x_)^m_.*(A_.+B_.*Log[e_.*(a_.+b_.*x_)^n_.*(c_.+d_.*x_)^mn_])^p_.,x_Symbol] :=
          (b*c-a*d)^(m+1)*(g/b)^m \\[Star] Subst[Int[x^m*(A+B*Log[e*x^n])^p/(b-d*x)^(m+2),x],x,(a+b*x)/(c+d*x)] /;
        FreeQ[{a,b,c,d,e,f,g,A,B,n},x] && EqQ[n+mn,0] && IGtQ[n,0] && NeQ[b*c-a*d,0] && IntegersQ[m,p] && EqQ[b*f-a*g,0] && (GtQ[p,0] || LtQ[m,-1])",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [f__, g__, m_, capital_a__, capital_b__, e__, a__, b__, n_, c__, d__, mn_, p_, x_],
        optional: [f__, g__, m_, capital_a__, capital_b__, e__, a__, b__, c__, d__, p_, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, capital_a__, capital_b__, n_], x_)
                && eqq!(&n_ + &mn_, 0)
                && igtq!(n_, 0)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && integersq!([m_, p_])
                && eqq!(&b__ * &f__ - &a__ * &g__, 0)
                && (gtq!(p_, 0) || ltq!(m_, -1))
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let substitution_integrand = sub_atom.pow(&m_)
                * (&capital_a__ + &capital_b__ * (&e__ * sub_atom.pow(&n_)).log()).pow(&p_)
                / (&b__ - &d__ * &sub_atom).pow(&m_ + 2);
            let substitution_primitive = rubi_rhs_int(&substitution_integrand, substitution_symbol);
            let substitution = (&a__ + &b__ * x_) / (&c__ + &d__ * x_);
            let coefficient =
                (&b__ * &c__ - &a__ * &d__).pow(&m_ + 1) * (&g__ / &b__).pow(&m_);
            let substituted =
                rubi_subst(&substitution_primitive, substitution_symbol, substitution);

            rubi_star(coefficient, substituted)
        },
    ));
}

fn push_rules_rule_2951(rules: &mut Vec<RubiRule>) {
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
        m_,
        n_,
        p_,
        x_
    );
    rules.push(rubi_rule!(
        order: 2951,
        source: "Int[(f_.+g_.*x_)^m_.*(A_.+B_.*Log[e_.*((a_.+b_.*x_)/(c_.+d_.*x_))^n_.])^p_.,x_Symbol] :=
          (b*c-a*d)^(m+1)*(g/d)^m \\[Star] Subst[Int[(A+B*Log[e*x^n])^p/(b-d*x)^(m+2),x],x,(a+b*x)/(c+d*x)] /;
        FreeQ[{a,b,c,d,e,f,g,A,B,n},x] && NeQ[b*c-a*d,0] && IntegersQ[m,p] && EqQ[d*f-c*g,0] && (GtQ[p,0] || LtQ[m,-1])",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [f__, g__, m_, capital_a__, capital_b__, e__, a__, b__, c__, d__, n_, p_, x_],
        optional: [f__, g__, m_, capital_a__, capital_b__, e__, a__, b__, c__, d__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, capital_a__, capital_b__, n_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && integersq!([m_, p_])
                && eqq!(&d__ * &f__ - &c__ * &g__, 0)
                && (gtq!(p_, 0) || ltq!(m_, -1))
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let substitution_integrand =
                (&capital_a__ + &capital_b__ * (&e__ * sub_atom.pow(&n_)).log()).pow(&p_)
                    / (&b__ - &d__ * &sub_atom).pow(&m_ + 2);
            let substitution_primitive = rubi_rhs_int(&substitution_integrand, substitution_symbol);
            let substitution = (&a__ + &b__ * x_) / (&c__ + &d__ * x_);
            let coefficient =
                (&b__ * &c__ - &a__ * &d__).pow(&m_ + 1) * (&g__ / &d__).pow(&m_);
            let substituted =
                rubi_subst(&substitution_primitive, substitution_symbol, substitution);

            rubi_star(coefficient, substituted)
        },
    ));
}

fn push_rules_rule_2952(rules: &mut Vec<RubiRule>) {
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
        m_,
        mn_,
        n_,
        p_,
        x_
    );
    rules.push(rubi_rule!(
        order: 2952,
        source: "Int[(f_.+g_.*x_)^m_.*(A_.+B_.*Log[e_.*(a_.+b_.*x_)^n_.*(c_.+d_.*x_)^mn_])^p_.,x_Symbol] :=
          (b*c-a*d)^(m+1)*(g/d)^m \\[Star] Subst[Int[(A+B*Log[e*x^n])^p/(b-d*x)^(m+2),x],x,(a+b*x)/(c+d*x)] /;
        FreeQ[{a,b,c,d,e,f,g,A,B,n},x] && EqQ[n+mn,0] && IGtQ[n,0] && NeQ[b*c-a*d,0] && IntegersQ[m,p] && EqQ[d*f-c*g,0] && (GtQ[p,0] || LtQ[m,-1])",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [f__, g__, m_, capital_a__, capital_b__, e__, a__, b__, n_, c__, d__, mn_, p_, x_],
        optional: [f__, g__, m_, capital_a__, capital_b__, e__, a__, b__, c__, d__, p_, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, capital_a__, capital_b__, n_], x_)
                && eqq!(&n_ + &mn_, 0)
                && igtq!(n_, 0)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && integersq!([m_, p_])
                && eqq!(&d__ * &f__ - &c__ * &g__, 0)
                && (gtq!(p_, 0) || ltq!(m_, -1))
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let substitution_integrand =
                (&capital_a__ + &capital_b__ * (&e__ * sub_atom.pow(&n_)).log()).pow(&p_)
                    / (&b__ - &d__ * &sub_atom).pow(&m_ + 2);
            let substitution_primitive = rubi_rhs_int(&substitution_integrand, substitution_symbol);
            let substitution = (&a__ + &b__ * x_) / (&c__ + &d__ * x_);
            let coefficient =
                (&b__ * &c__ - &a__ * &d__).pow(&m_ + 1) * (&g__ / &d__).pow(&m_);
            let substituted =
                rubi_subst(&substitution_primitive, substitution_symbol, substitution);

            rubi_star(coefficient, substituted)
        },
    ));
}

fn push_rules_rule_2953(rules: &mut Vec<RubiRule>) {
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
        m_,
        n_,
        p_,
        x_
    );
    rules.push(rubi_rule!(
        order: 2953,
        source: "Int[(f_.+g_.*x_)^m_.*(A_.+B_.*Log[e_.*((a_.+b_.*x_)/(c_.+d_.*x_))^n_.])^p_.,x_Symbol] :=
          (b*c-a*d) \\[Star] Subst[Int[(b*f-a*g-(d*f-c*g)*x)^m*(A+B*Log[e*x^n])^p/(b-d*x)^(m+2),x],x,(a+b*x)/(c+d*x)] /;
        FreeQ[{a,b,c,d,e,f,g,A,B,n},x] && NeQ[b*c-a*d,0] && IntegerQ[m] && IGtQ[p,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [f__, g__, m_, capital_a__, capital_b__, e__, a__, b__, c__, d__, n_, p_, x_],
        optional: [f__, g__, m_, capital_a__, capital_b__, e__, a__, b__, c__, d__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, capital_a__, capital_b__, n_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && integerq!(m_)
                && igtq!(p_, 0)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let transformed_linear =
                &b__ * &f__ - &a__ * &g__ - (&d__ * &f__ - &c__ * &g__) * &sub_atom;
            let log_power =
                (&capital_a__ + &capital_b__ * (&e__ * sub_atom.pow(&n_)).log()).pow(&p_);
            let substitution_integrand =
                transformed_linear.pow(&m_) * log_power / (&b__ - &d__ * &sub_atom).pow(&m_ + 2);
            let substitution_primitive = rubi_rhs_int(&substitution_integrand, substitution_symbol);
            let substitution = (&a__ + &b__ * x_) / (&c__ + &d__ * x_);
            let substituted =
                rubi_subst(&substitution_primitive, substitution_symbol, substitution);

            rubi_star(&b__ * &c__ - &a__ * &d__, substituted)
        },
    ));
}

fn push_rules_rule_2954(rules: &mut Vec<RubiRule>) {
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
        m_,
        mn_,
        n_,
        p_,
        x_
    );
    rules.push(rubi_rule!(
        order: 2954,
        source: "Int[(f_.+g_.*x_)^m_.*(A_.+B_.*Log[e_.*(a_.+b_.*x_)^n_.*(c_.+d_.*x_)^mn_])^p_.,x_Symbol] :=
          (b*c-a*d) \\[Star] Subst[Int[(b*f-a*g-(d*f-c*g)*x)^m*(A+B*Log[e*x^n])^p/(b-d*x)^(m+2),x],x,(a+b*x)/(c+d*x)] /;
        FreeQ[{a,b,c,d,e,f,g,A,B,n},x] && EqQ[n+mn,0] && IGtQ[n,0] && NeQ[b*c-a*d,0] && IntegerQ[m] && IGtQ[p,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [f__, g__, m_, capital_a__, capital_b__, e__, a__, b__, n_, c__, d__, mn_, p_, x_],
        optional: [f__, g__, m_, capital_a__, capital_b__, e__, a__, b__, c__, d__, p_, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, capital_a__, capital_b__, n_], x_)
                && eqq!(&n_ + &mn_, 0)
                && igtq!(n_, 0)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && integerq!(m_)
                && igtq!(p_, 0)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let transformed_linear =
                &b__ * &f__ - &a__ * &g__ - (&d__ * &f__ - &c__ * &g__) * &sub_atom;
            let log_power =
                (&capital_a__ + &capital_b__ * (&e__ * sub_atom.pow(&n_)).log()).pow(&p_);
            let substitution_integrand =
                transformed_linear.pow(&m_) * log_power / (&b__ - &d__ * &sub_atom).pow(&m_ + 2);
            let substitution_primitive = rubi_rhs_int(&substitution_integrand, substitution_symbol);
            let substitution = (&a__ + &b__ * x_) / (&c__ + &d__ * x_);
            let substituted =
                rubi_subst(&substitution_primitive, substitution_symbol, substitution);

            rubi_star(&b__ * &c__ - &a__ * &d__, substituted)
        },
    ));
}

fn push_rules_rule_2955(rules: &mut Vec<RubiRule>) {
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
        m_,
        n_,
        p_,
        x_
    );
    rules.push(rubi_rule!(
        order: 2955,
        source: "Int[(f_.+g_.*x_)^m_.*(A_.+B_.*Log[e_.*((a_.+b_.*x_)/(c_.+d_.*x_))^n_.])^p_.,x_Symbol] :=
          Unintegrable[(f+g*x)^m*(A+B*Log[e*((a+b*x)/(c+d*x))^n])^p,x] /;
        FreeQ[{a,b,c,d,e,f,g,A,B,m,n,p},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [f__, g__, m_, capital_a__, capital_b__, e__, a__, b__, c__, d__, n_, p_, x_],
        optional: [f__, g__, m_, capital_a__, capital_b__, e__, a__, b__, c__, d__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, capital_a__, capital_b__, m_, n_, p_], x_)
        },
        rhs: {
            let integrand = (&f__ + &g__ * x_).pow(&m_)
                * (&capital_a__
                    + &capital_b__
                        * (&e__ * ((&a__ + &b__ * x_) / (&c__ + &d__ * x_)).pow(&n_))
                            .log())
                .pow(&p_);

            rubi_unintegrable(integrand, x_)
        },
    ));
}

fn push_rules_rule_2956(rules: &mut Vec<RubiRule>) {
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
        m_,
        mn_,
        n_,
        p_,
        x_
    );
    rules.push(rubi_rule!(
        order: 2956,
        source: "Int[(f_.+g_.*x_)^m_.*(A_.+B_.*Log[e_.*(a_.+b_.*x_)^n_.*(c_.+d_.*x_)^mn_])^p_.,x_Symbol] :=
          Unintegrable[(f+g*x)^m*(A+B*Log[e*(a+b*x)^n/(c+d*x)^n])^p,x] /;
        FreeQ[{a,b,c,d,e,f,g,A,B,m,n,p},x] && EqQ[n+mn,0] && IntegerQ[n]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [f__, g__, m_, capital_a__, capital_b__, e__, a__, b__, n_, c__, d__, mn_, p_, x_],
        optional: [f__, g__, m_, capital_a__, capital_b__, e__, a__, b__, c__, d__, p_, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, capital_a__, capital_b__, m_, n_, p_], x_)
                && eqq!(&n_ + &mn_, 0)
                && integerq!(n_)
        },
        rhs: {
            let lhs = &a__ + &b__ * x_;
            let rhs = &c__ + &d__ * x_;
            let integrand = (&f__ + &g__ * x_).pow(&m_)
                * (&capital_a__ + &capital_b__ * (&e__ * lhs.pow(&n_) / rhs.pow(&n_)).log())
                    .pow(&p_);

            rubi_unintegrable(integrand, x_)
        },
    ));
}

fn push_rules_rule_2957(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_a__, capital_b__, e__, m_, n_, p_, u__, v__, w__);
    rules.push(rubi_rule!(
        order: 2957,
        source: "Int[w_^m_.*(A_.+B_.*Log[e_.*(u_/v_)^n_.])^p_.,x_Symbol] :=
          Int[ExpandToSum[w,x]^m*(A+B*Log[e*(ExpandToSum[u,x]/ExpandToSum[v,x])^n])^p,x] /;
        FreeQ[{e,A,B,m,n,p},x] && LinearQ[{u,v,w},x] && Not[LinearMatchQ[{u,v,w},x]]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: w__.pow(m_) * (capital_a__ + capital_b__ * (e__ * (u__ / v__).pow(n_)).log()).pow(p_),
        with: [w__, m_, capital_a__, capital_b__, e__, u__, v__, n_, p_, x_],
        optional: [m_, capital_a__, capital_b__, e__, n_, p_],
        when: {
            freeq!([e__, capital_a__, capital_b__, m_, n_, p_], x_)
                && rubi_linear_q_list(&[&u__, &v__, &w__], x_)
                && !rubi_linear_match_q_list(&[&u__, &v__, &w__], x_)
        },
        rhs: {
            let expanded_w = rubi_expand_to_sum(&w__, x_);
            let expanded_u = rubi_expand_to_sum(&u__, x_);
            let expanded_v = rubi_expand_to_sum(&v__, x_);
            let recursive_integrand = expanded_w.pow(&m_)
                * (&capital_a__
                    + &capital_b__ * (&e__ * (&expanded_u / &expanded_v).pow(&n_)).log())
                .pow(&p_);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_2958(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        capital_a__,
        capital_b__,
        e__,
        m_,
        mn_,
        n_,
        p_,
        u__,
        v__,
        w__
    );
    rules.push(rubi_rule!(
        order: 2958,
        source: "Int[w_^m_.*(A_.+B_.*Log[e_.*u_^n_.*v_^mn_])^p_.,x_Symbol] :=
          Int[ExpandToSum[w,x]^m*(A+B*Log[e*ExpandToSum[u,x]^n/ExpandToSum[v,x]^n])^p,x] /;
        FreeQ[{e,A,B,m,n,p},x] && EqQ[n+mn,0] && IGtQ[n,0] && LinearQ[{u,v,w},x] && Not[LinearMatchQ[{u,v,w},x]]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: w__.pow(m_) * (capital_a__ + capital_b__ * (e__ * u__.pow(n_) * v__.pow(mn_)).log()).pow(p_),
        with: [w__, m_, capital_a__, capital_b__, e__, u__, n_, v__, mn_, p_, x_],
        optional: [m_, capital_a__, capital_b__, e__, p_, n_],
        when: {
            freeq!([e__, capital_a__, capital_b__, m_, n_, p_], x_)
                && eqq!(&n_ + &mn_, 0)
                && igtq!(n_, 0)
                && rubi_linear_q_list(&[&u__, &v__, &w__], x_)
                && !rubi_linear_match_q_list(&[&u__, &v__, &w__], x_)
        },
        rhs: {
            let expanded_w = rubi_expand_to_sum(&w__, x_);
            let expanded_u = rubi_expand_to_sum(&u__, x_);
            let expanded_v = rubi_expand_to_sum(&v__, x_);
            let recursive_integrand = expanded_w.pow(&m_)
                * (&capital_a__
                    + &capital_b__ * (&e__ * expanded_u.pow(&n_) / expanded_v.pow(&n_)).log())
                .pow(&p_);

            rubi_rhs_int(&recursive_integrand, x_)
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
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (capital_a__ + capital_b__ * (e__ * ((a__ + b__ * x_) / (c__ + d__ * x_)).pow(n_)).log())
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
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    (capital_a__ + capital_b__ * (e__ * ((a__ + b__ * x_) / (c__ + d__ * x_)).pow(n_)).log())
        / (f__ + g__ * x_)
}

#[inline(never)]
fn rubi_shared_pattern_2(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let capital_a__ = symbols.capital_a__;
    let capital_b__ = symbols.capital_b__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let mn_ = symbols.mn_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (capital_a__ + capital_b__ * (e__ * (a__ + b__ * x_).pow(n_) * (c__ + d__ * x_).pow(mn_)).log())
        .pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_3(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let capital_a__ = symbols.capital_a__;
    let capital_b__ = symbols.capital_b__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let g__ = symbols.g__;
    let mn_ = symbols.mn_;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    (capital_a__ + capital_b__ * (e__ * (a__ + b__ * x_).pow(n_) * (c__ + d__ * x_).pow(mn_)).log())
        / (f__ + g__ * x_)
}

#[inline(never)]
fn rubi_shared_pattern_4(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let capital_a__ = symbols.capital_a__;
    let capital_b__ = symbols.capital_b__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let g__ = symbols.g__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (f__ + g__ * x_).pow(m_)
        * (capital_a__ + capital_b__ * (e__ * ((a__ + b__ * x_) / (c__ + d__ * x_)).pow(n_)).log())
            .pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_5(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let capital_a__ = symbols.capital_a__;
    let capital_b__ = symbols.capital_b__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let g__ = symbols.g__;
    let m_ = symbols.m_;
    let mn_ = symbols.mn_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (f__ + g__ * x_).pow(m_)
        * (capital_a__
            + capital_b__ * (e__ * (a__ + b__ * x_).pow(n_) * (c__ + d__ * x_).pow(mn_)).log())
        .pow(p_)
}
