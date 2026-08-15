use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_2836(rules);
    push_rules_rule_2837(rules);
    push_rules_rule_2838(rules);
    push_rules_rule_2839(rules);
    push_rules_rule_2840(rules);
    push_rules_rule_2841(rules);
    push_rules_rule_2842(rules);
    push_rules_rule_2843(rules);
    push_rules_rule_2844(rules);
    push_rules_rule_2845(rules);
    push_rules_rule_2846(rules);
    push_rules_rule_2847(rules);
    push_rules_rule_2848(rules);
    push_rules_rule_2849(rules);
    push_rules_rule_2850(rules);
    push_rules_rule_2851(rules);
    push_rules_rule_2852(rules);
    push_rules_rule_2853(rules);
    push_rules_rule_2854(rules);
    push_rules_rule_2855(rules);
    push_rules_rule_2856(rules);
    push_rules_rule_2857(rules);
    push_rules_rule_2858(rules);
    push_rules_rule_2859(rules);
    push_rules_rule_2860(rules);
    push_rules_rule_2861(rules);
    push_rules_rule_2862(rules);
    push_rules_rule_2863(rules);
    push_rules_rule_2864(rules);
    push_rules_rule_2865(rules);
    push_rules_rule_2866(rules);
    push_rules_rule_2867(rules);
    push_rules_rule_2868(rules);
    push_rules_rule_2869(rules);
    push_rules_rule_2870(rules);
    push_rules_rule_2871(rules);
    push_rules_rule_2872(rules);
    push_rules_rule_2873(rules);
    push_rules_rule_2874(rules);
    push_rules_rule_2875(rules);
    push_rules_rule_2876(rules);
    push_rules_rule_2877(rules);
    push_rules_rule_2878(rules);
    push_rules_rule_2879(rules);
    push_rules_rule_2880(rules);
    push_rules_rule_2881(rules);
    push_rules_rule_2882(rules);
    push_rules_rule_2883(rules);
    push_rules_rule_2884(rules);
    push_rules_rule_2885(rules);
    push_rules_rule_2886(rules);
    push_rules_rule_2887(rules);
    push_rules_rule_2888(rules);
    push_rules_rule_2889(rules);
    push_rules_rule_2890(rules);
    push_rules_rule_2891(rules);
    push_rules_rule_2892(rules);
    push_rules_rule_2893(rules);
    push_rules_rule_2894(rules);
    push_rules_rule_2895(rules);
    push_rules_rule_2896(rules);
}

fn push_rules_rule_2836(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 2836,
        source: "Int[(a_.+b_.*Log[c_.*(d_+e_.*x_)^n_.])^p_.,x_Symbol] :=
          1/e \\[Star] Subst[Int[(a+b*Log[c*x^n])^p,x],x,d+e*x] /;
        FreeQ[{a,b,c,d,e,n,p},x]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (a__ + b__ * (c__ * (d__ + e__ * x_).pow(n_)).log()).pow(p_),
        with: [a__, b__, c__, d__, e__, n_, p_, x_],
        optional: [a__, b__, c__, e__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, n_, p_], x_)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let transformed_integrand =
                (&a__ + &b__ * (&c__ * sub_atom.pow(&n_)).log()).pow(&p_);
            let transformed_primitive = rubi_rhs_int(&transformed_integrand, substitution_symbol);
            let substitution = &d__ + &e__ * x_;

            rubi_star(Atom::num(1) / &e__, rubi_subst(&transformed_primitive, substitution_symbol, substitution))
        },
    ));
}

fn push_rules_rule_2837(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 2837,
        source: "Int[(f_+g_. x_)^q_.*(a_.+b_.*Log[c_.*(d_+e_.*x_)^n_.])^p_.,x_Symbol] :=
          1/e \\[Star] Subst[Int[(f*x/d)^q*(a+b*Log[c*x^n])^p,x],x,d+e*x] /;
        FreeQ[{a,b,c,d,e,f,g,n,p,q},x] && EqQ[e*f-d*g,0]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [f__, g__, q_, a__, b__, c__, d__, e__, n_, p_, x_],
        optional: [g__, q_, a__, b__, c__, e__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, n_, p_, q_], x_)
                && eqq!(&e__ * &f__ - &d__ * &g__, 0)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let transformed_integrand = (&f__ * &sub_atom / &d__).pow(&q_)
                * (&a__ + &b__ * (&c__ * sub_atom.pow(&n_)).log()).pow(&p_);
            let transformed_primitive = rubi_rhs_int(&transformed_integrand, substitution_symbol);
            let substitution = &d__ + &e__ * x_;

            rubi_star(Atom::num(1) / &e__, rubi_subst(&transformed_primitive, substitution_symbol, substitution))
        },
    ));
}

fn push_rules_rule_2838(rules: &mut Vec<RubiRule>) {
    rubi_symb!(c__, d__, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 2838,
        source: "Int[Log[c_.*(d_+e_.*x_^n_.)]/x_,x_Symbol] :=
          -PolyLog[2,-c*e*x^n]/n /;
        FreeQ[{c,d,e,n},x] && EqQ[c*d,1]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: (c__ * (d__ + e__ * x_.pow(n_))).log() / x_,
        with: [c__, d__, e__, n_, x_],
        optional: [c__, e__, n_],
        when: {
            freeq!([c__, d__, e__, n_], x_)
                && eqq!(&c__ * &d__, 1)
        },
        rhs: {
            rubi_simp(
                &(-(-&c__ * &e__ * x_.pow(&n_)).polylog(2) / &n_),
                x_,
            )
        },
    ));
}

fn push_rules_rule_2839(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 2839,
        source: "Int[(a_.+b_.*Log[c_.*(d_+e_.*x_)])/x_,x_Symbol] :=
          (a+b*Log[c*d])*Log[x] + b \\[Star] Int[Log[1+e*x/d]/x,x] /;
        FreeQ[{a,b,c,d,e},x] && GtQ[c*d,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (a__ + b__ * (c__ * (d__ + e__ * x_)).log()) / x_,
        with: [a__, b__, c__, d__, e__, x_],
        optional: [a__, b__, c__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && gtq!(&c__ * &d__, 0)
        },
        rhs: {
            let recursive_integrand = (Atom::num(1) + &e__ * x_ / &d__).log() / x_;
            let recursive_primitive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&((&a__ + &b__ * (&c__ * &d__).log()) * x_.log()), x_)
                    + rubi_star(b__, recursive_primitive)
        },
    ));
}

fn push_rules_rule_2840(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, x_);
    rules.push(rubi_rule!(
        order: 2840,
        source: "Int[(a_.+b_.*Log[c_.*(d_+e_.*x_)])/(f_.+g_. x_),x_Symbol] :=
          1/g \\[Star] Subst[Int[(a+b*Log[1+c*e*x/g])/x,x],x,f+g*x] /;
        FreeQ[{a,b,c,d,e,f,g},x] && NeQ[e*f-d*g,0] && EqQ[g+c*(e*f-d*g),0]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern: (a__ + b__ * (c__ * (d__ + e__ * x_)).log()) / (f__ + g__ * x_),
        with: [a__, b__, c__, d__, e__, f__, g__, x_],
        optional: [a__, b__, c__, e__, f__, g__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__], x_)
                && neq!(&e__ * &f__ - &d__ * &g__, 0)
                && eqq!(&g__ + &c__ * (&e__ * &f__ - &d__ * &g__), 0)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let transformed_integrand =
                (&a__ + &b__ * (Atom::num(1) + &c__ * &e__ * &sub_atom / &g__).log())
                    / &sub_atom;
            let transformed_primitive = rubi_rhs_int(&transformed_integrand, substitution_symbol);
            let substitution = &f__ + &g__ * x_;

            rubi_star(Atom::num(1) / &g__, rubi_subst(&transformed_primitive, substitution_symbol, substitution))
        },
    ));
}

fn push_rules_rule_2841(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, n_, x_);
    rules.push(rubi_rule!(
        order: 2841,
        source: "Int[(a_.+b_.*Log[c_.*(d_+e_.*x_)^n_.])/(f_.+g_. x_),x_Symbol] :=
          Log[e*(f+g*x)/(e*f-d*g)]*(a+b*Log[c*(d+e*x)^n])/g - b*e*n/g \\[Star] Int[Log[(e*(f+g*x))/(e*f-d*g)]/(d+e*x),x] /;
        FreeQ[{a,b,c,d,e,f,g,n},x] && NeQ[e*f-d*g,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern: (a__ + b__ * (c__ * (d__ + e__ * x_).pow(n_)).log()) / (f__ + g__ * x_),
        with: [a__, b__, c__, d__, e__, n_, f__, g__, x_],
        optional: [a__, b__, c__, e__, n_, f__, g__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, n_], x_)
                && neq!(&e__ * &f__ - &d__ * &g__, 0)
        },
        rhs: {
            let determinant = &e__ * &f__ - &d__ * &g__;
            let affine = &f__ + &g__ * x_;
            let shifted = &d__ + &e__ * x_;
            let affine_log = (&e__ * &affine / &determinant).log();
            let logarithmic = &a__ + &b__ * (&c__ * shifted.pow(&n_)).log();
            let recursive_primitive = rubi_rhs_int(&(&affine_log / &shifted), x_);

            rubi_simp(&(&affine_log * logarithmic / &g__), x_)
                    - rubi_star(&b__ * &e__ * &n_ / &g__, recursive_primitive)
        },
    ));
}

fn push_rules_rule_2842(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, n_, q_, x_);
    rules.push(rubi_rule!(
        order: 2842,
        source: "Int[(f_.+g_.*x_)^q_.*(a_.+b_.*Log[c_.*(d_+e_.*x_)^n_.]),x_Symbol] :=
          (f+g*x)^(q+1)*(a+b*Log[c*(d+e*x)^n])/(g*(q+1)) -
          b*e*n/(g*(q+1)) \\[Star] Int[(f+g*x)^(q+1)/(d+e*x),x] /;
        FreeQ[{a,b,c,d,e,f,g,n,q},x] && NeQ[e*f-d*g,0] && NeQ[q,-1]",
        desc: "Integration by parts",
        refs: ["G&R 2.728.1, CRC 501, A&S 4.1.50'"],
        pattern: (f__ + g__ * x_).pow(q_)
            * (a__ + b__ * (c__ * (d__ + e__ * x_).pow(n_)).log()),
        with: [f__, g__, q_, a__, b__, c__, d__, e__, n_, x_],
        optional: [f__, g__, a__, b__, c__, e__, n_, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, n_, q_], x_)
                && neq!(&e__ * &f__ - &d__ * &g__, 0)
                && neq!(q_, -1)
        },
        rhs: {
            let denominator = &g__ * (&q_ + 1);
            let affine = &f__ + &g__ * x_;
            let shifted = &d__ + &e__ * x_;
            let logarithmic = &a__ + &b__ * (&c__ * shifted.pow(&n_)).log();
            let recursive_integrand = affine.pow(&q_ + 1) / &shifted;
            let recursive_primitive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(affine.pow(&q_ + 1) * logarithmic / &denominator), x_)
                    - rubi_star(&b__ * &e__ * &n_ / denominator, recursive_primitive)
        },
    ));
}

fn push_rules_rule_2843(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 2843,
        source: "Int[(a_.+b_.*Log[c_.*(d_+e_.*x_)^n_.])^p_/(f_.+g_. x_),x_Symbol] :=
          Log[e*(f+g*x)/(e*f-d*g)]*(a+b*Log[c*(d+e*x)^n])^p/g -
          b*e*n*p/g \\[Star] Int[Log[(e*(f+g*x))/(e*f-d*g)]*(a+b*Log[c*(d+e*x)^n])^(p-1)/(d+e*x),x] /;
        FreeQ[{a,b,c,d,e,f,g,n,p},x] && NeQ[e*f-d*g,0] && IGtQ[p,1]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern: (a__ + b__ * (c__ * (d__ + e__ * x_).pow(n_)).log()).pow(p_)
            / (f__ + g__ * x_),
        with: [a__, b__, c__, d__, e__, n_, p_, f__, g__, x_],
        optional: [a__, b__, c__, e__, n_, f__, g__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, n_, p_], x_)
                && neq!(&e__ * &f__ - &d__ * &g__, 0)
                && igtq!(p_, 1)
        },
        rhs: {
            let determinant = &e__ * &f__ - &d__ * &g__;
            let affine = &f__ + &g__ * x_;
            let shifted = &d__ + &e__ * x_;
            let affine_log = (&e__ * &affine / &determinant).log();
            let logarithmic = &a__ + &b__ * (&c__ * shifted.pow(&n_)).log();
            let recursive_integrand =
                &affine_log * logarithmic.pow(&p_ - 1) / &shifted;
            let recursive_primitive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(&affine_log * logarithmic.pow(&p_) / &g__), x_)
                    - rubi_star(&b__ * &e__ * &n_ * &p_ / &g__, recursive_primitive)
        },
    ));
}

fn push_rules_rule_2844(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 2844,
        source: "Int[(a_.+b_.*Log[c_.*(d_+e_.*x_)^n_.])^p_/(f_.+g_.*x_)^2,x_Symbol] :=
          (d+e*x)*(a+b*Log[c*(d+e*x)^n])^p/((e*f-d*g)*(f+g*x)) -
          b*e*n*p/(e*f-d*g) \\[Star] Int[(a+b*Log[c*(d+e*x)^n])^(p-1)/(f+g*x),x] /;
        FreeQ[{a,b,c,d,e,f,g,n},x] && NeQ[e*f-d*g,0] && GtQ[p,0]",
        desc: "Integration by parts",
        refs: [],
        pattern: (a__ + b__ * (c__ * (d__ + e__ * x_).pow(n_)).log()).pow(p_)
            / (f__ + g__ * x_).pow(2),
        with: [a__, b__, c__, d__, e__, n_, p_, f__, g__, x_],
        optional: [a__, b__, c__, e__, n_, f__, g__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, n_], x_)
                && neq!(&e__ * &f__ - &d__ * &g__, 0)
                && gtq!(p_, 0)
        },
        rhs: {
            let determinant = &e__ * &f__ - &d__ * &g__;
            let affine = &f__ + &g__ * x_;
            let shifted = &d__ + &e__ * x_;
            let logarithmic = &a__ + &b__ * (&c__ * shifted.pow(&n_)).log();
            let recursive_integrand = logarithmic.pow(&p_ - 1) / &affine;
            let recursive_primitive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(
                    &(shifted * logarithmic.pow(&p_) / (&determinant * affine)),
                    x_,
                ) - rubi_star(&b__ * &e__ * &n_ * &p_ / determinant, recursive_primitive)
        },
    ));
}

fn push_rules_rule_2845(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 2845,
        source: "Int[(f_.+g_.*x_)^q_.*(a_.+b_.*Log[c_.*(d_+e_.*x_)^n_.])^p_,x_Symbol] :=
          (f+g*x)^(q+1)*(a+b*Log[c*(d+e*x)^n])^p/(g*(q+1)) -
          b*e*n*p/(g*(q+1)) \\[Star] Int[(f+g*x)^(q+1)*(a+b*Log[c*(d+e*x)^n])^(p-1)/(d+e*x),x] /;
        FreeQ[{a,b,c,d,e,f,g,n,q},x] && NeQ[e*f-d*g,0] && GtQ[p,0] && NeQ[q,-1] && IntegersQ[2*p,2*q] &&
          (Not[IGtQ[q,0]] || EqQ[p,2] && NeQ[q,1])",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [f__, g__, q_, a__, b__, c__, d__, e__, n_, p_, x_],
        optional: [f__, g__, q_, a__, b__, c__, e__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, n_, q_], x_)
                && neq!(&e__ * &f__ - &d__ * &g__, 0)
                && gtq!(p_, 0)
                && neq!(q_, -1)
                && integersq!([Atom::num(2) * &p_, Atom::num(2) * &q_])
                && (!igtq!(q_, 0) || eqq!(p_, 2) && neq!(q_, 1))
        },
        rhs: {
            let denominator = &g__ * (&q_ + 1);
            let affine = &f__ + &g__ * x_;
            let shifted = &d__ + &e__ * x_;
            let logarithmic = &a__ + &b__ * (&c__ * shifted.pow(&n_)).log();
            let recursive_integrand =
                affine.pow(&q_ + 1) * logarithmic.pow(&p_ - 1) / &shifted;
            let recursive_primitive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(
                    &(affine.pow(&q_ + 1) * logarithmic.pow(&p_) / &denominator),
                    x_,
                ) - rubi_star(&b__ * &e__ * &n_ * &p_ / denominator, recursive_primitive)
        },
    ));
}

fn push_rules_rule_2846(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, n_, q_, x_);
    rules.push(rubi_rule!(
        order: 2846,
        source: "Int[(f_.+g_.*x_)^q_./(a_.+b_.*Log[c_.*(d_+e_.*x_)^n_.]),x_Symbol] :=
          Int[ExpandIntegrand[(f+g*x)^q/(a+b*Log[c*(d+e*x)^n]),x],x] /;
        FreeQ[{a,b,c,d,e,f,g,n},x] && NeQ[e*f-d*g,0] && IGtQ[q,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (f__ + g__ * x_).pow(q_)
            / (a__ + b__ * (c__ * (d__ + e__ * x_).pow(n_)).log()),
        with: [f__, g__, q_, a__, b__, c__, d__, e__, n_, x_],
        optional: [f__, g__, q_, a__, b__, c__, e__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, n_], x_)
                && neq!(&e__ * &f__ - &d__ * &g__, 0)
                && igtq!(q_, 0)
        },
        rhs: {
            let shifted = &d__ + &e__ * x_;
            let expand_integrand_payload =
                (&f__ + &g__ * x_).pow(&q_)
                    / (&a__ + &b__ * (&c__ * shifted.pow(&n_)).log());
            let expanded = rubi_expand_integrand(&expand_integrand_payload, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_2847(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 2847,
        source: "Int[(f_.+g_.*x_)^q_.*(a_.+b_.*Log[c_.*(d_+e_.*x_)^n_.])^p_,x_Symbol] :=
          (d+e*x)*(f+g*x)^q*(a+b*Log[c*(d+e*x)^n])^(p+1)/(b*e*n*(p+1)) +
          q*(e*f-d*g)/(b*e*n*(p+1)) \\[Star] Int[(f+g*x)^(q-1)*(a+b*Log[c*(d+e*x)^n])^(p+1),x] -
          (q+1)/(b*n*(p+1)) \\[Star] Int[(f+g*x)^q*(a+b*Log[c*(d+e*x)^n])^(p+1),x] /;
        FreeQ[{a,b,c,d,e,f,g,n},x] && NeQ[e*f-d*g,0] && LtQ[p,-1] && GtQ[q,0]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [f__, g__, q_, a__, b__, c__, d__, e__, n_, p_, x_],
        optional: [f__, g__, q_, a__, b__, c__, e__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, n_], x_)
                && neq!(&e__ * &f__ - &d__ * &g__, 0)
                && ltq!(p_, -1)
                && gtq!(q_, 0)
        },
        rhs: {
            let determinant = &e__ * &f__ - &d__ * &g__;
            let affine = &f__ + &g__ * x_;
            let shifted = &d__ + &e__ * x_;
            let logarithmic = &a__ + &b__ * (&c__ * shifted.pow(&n_)).log();
            let p_plus_1 = &p_ + 1;
            let first_denominator = &b__ * &e__ * &n_ * &p_plus_1;
            let second_integrand = affine.pow(&q_ - 1) * logarithmic.pow(&p_plus_1);
            let second_primitive = rubi_rhs_int(&second_integrand, x_);
            let third_integrand = affine.pow(&q_) * logarithmic.pow(&p_plus_1);
            let third_primitive = rubi_rhs_int(&third_integrand, x_);

            rubi_simp(
                    &(shifted * affine.pow(&q_) * logarithmic.pow(&p_plus_1)
                        / &first_denominator),
                    x_,
                ) - rubi_star(&q_ + 1, third_primitive / (&b__ * &n_ * &p_plus_1)) + rubi_star(&q_ * determinant / first_denominator, second_primitive)
        },
    ));
}

fn push_rules_rule_2848(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 2848,
        source: "Int[(f_.+g_.*x_)^q_.*(a_.+b_.*Log[c_.*(d_+e_.*x_)^n_.])^p_,x_Symbol] :=
          Int[ExpandIntegrand[(f+g*x)^q*(a+b*Log[c*(d+e*x)^n])^p,x],x] /;
        FreeQ[{a,b,c,d,e,f,g,n,p},x] && NeQ[e*f-d*g,0] && IGtQ[q,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [f__, g__, q_, a__, b__, c__, d__, e__, n_, p_, x_],
        optional: [f__, g__, q_, a__, b__, c__, e__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, n_, p_], x_)
                && neq!(&e__ * &f__ - &d__ * &g__, 0)
                && igtq!(q_, 0)
        },
        rhs: {
            let shifted = &d__ + &e__ * x_;
            let expand_integrand_payload = (&f__ + &g__ * x_).pow(&q_)
                * (&a__ + &b__ * (&c__ * shifted.pow(&n_)).log()).pow(&p_);
            let expanded = rubi_expand_integrand(&expand_integrand_payload, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_2849(rules: &mut Vec<RubiRule>) {
    rubi_symb!(c__, d__, e__, f__, g__, x_);
    rules.push(rubi_rule!(
        order: 2849,
        source: "Int[Log[c_./(d_+e_.*x_)]/(f_+g_.*x_^2),x_Symbol] :=
          -e/g \\[Star] Subst[Int[Log[2*d*x]/(1-2*d*x),x],x,1/(d+e*x)] /;
        FreeQ[{c,d,e,f,g},x] && EqQ[c,2*d] && EqQ[e^2*f+d^2*g,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (c__ / (d__ + e__ * x_)).log() / (f__ + g__ * x_.pow(2)),
        with: [c__, d__, e__, f__, g__, x_],
        optional: [c__, e__, g__],
        when: {
            freeq!([c__, d__, e__, f__, g__], x_)
                && eqq!(c__, Atom::num(2) * &d__)
                && eqq!(&e__ * &e__ * &f__ + &d__ * &d__ * &g__, 0)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let transformed_integrand = (Atom::num(2) * &d__ * &sub_atom).log()
                / (Atom::num(1) - Atom::num(2) * &d__ * &sub_atom);
            let transformed_primitive = rubi_rhs_int(&transformed_integrand, substitution_symbol);
            let substitution = Atom::num(1) / (&d__ + &e__ * x_);

            rubi_star(-&e__, rubi_subst(&transformed_primitive, substitution_symbol, substitution)
                    / &g__)
        },
    ));
}

fn push_rules_rule_2850(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, x_);
    rules.push(rubi_rule!(
        order: 2850,
        source: "Int[(a_.+b_.*Log[c_./(d_+e_.*x_)])/(f_+g_.*x_^2),x_Symbol] :=
          (a+b*Log[c/(2*d)]) \\[Star] Int[1/(f+g*x^2),x] + b \\[Star] Int[Log[2*d/(d+e*x)]/(f+g*x^2),x] /;
        FreeQ[{a,b,c,d,e,f,g},x] && EqQ[e^2*f+d^2*g,0] && GtQ[c/(2*d),0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (a__ + b__ * (c__ / (d__ + e__ * x_)).log()) / (f__ + g__ * x_.pow(2)),
        with: [a__, b__, c__, d__, e__, f__, g__, x_],
        optional: [a__, b__, c__, e__, g__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__], x_)
                && eqq!(&e__ * &e__ * &f__ + &d__ * &d__ * &g__, 0)
                && gtq!(&c__ / (Atom::num(2) * &d__), 0)
        },
        rhs: {
            let quadratic_denominator = &f__ + &g__ * x_.pow(2);
            let first_integrand = Atom::num(1) / &quadratic_denominator;
            let first_primitive = rubi_rhs_int(&first_integrand, x_);
            let second_integrand =
                (Atom::num(2) * &d__ / (&d__ + &e__ * x_)).log() / quadratic_denominator;
            let second_primitive = rubi_rhs_int(&second_integrand, x_);

            rubi_star(&a__ + &b__ * (&c__ / (Atom::num(2) * &d__)).log(), first_primitive) + rubi_star(b__, second_primitive)
        },
    ));
}

fn push_rules_rule_2851(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, n_, x_);
    rules.push(rubi_rule!(
        order: 2851,
        source: "Int[(a_.+b_.*Log[c_.*(d_+e_.*x_)^n_.])/Sqrt[f_+g_.*x_^2],x_Symbol] :=
          With[{u=IntHide[1/Sqrt[f+g*x^2],x]},
          u*(a+b*Log[c*(d+e*x)^n]) - b*e*n \\[Star] Int[SimplifyIntegrand[u/(d+e*x),x],x]] /;
        FreeQ[{a,b,c,d,e,f,g,n},x] && GtQ[f,0]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, e__, n_, f__, g__, x_],
        optional: [a__, b__, c__, e__, n_, g__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, n_], x_)
                && gtq!(f__, 0)
        },
        rhs: {
            let shifted = &d__ + &e__ * x_;
            let quadratic = &f__ + &g__ * x_.pow(2);
            let logarithmic = &a__ + &b__ * (&c__ * shifted.pow(&n_)).log();
            let u = rubi_int_hide(&(Atom::num(1) / quadratic.sqrt()), x_).rubi_rhs();
            let recursive_integrand = rubi_simplify_integrand(&(&u / &shifted), x_);
            let recursive_primitive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(&u * logarithmic), x_)
                    - rubi_star(&b__ * &e__ * &n_, recursive_primitive)
        },
    ));
}

fn push_rules_rule_2852(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f1__, f2__, g1__, g2__, n_, x_);
    rules.push(rubi_rule!(
        order: 2852,
        source: "Int[(a_.+b_.*Log[c_.*(d_+e_.*x_)^n_.])/(Sqrt[f1_+g1_.*x_]*Sqrt[f2_+g2_.*x_]),x_Symbol] :=
          With[{u=IntHide[1/Sqrt[f1*f2+g1*g2*x^2],x]},
          u*(a+b*Log[c*(d+e*x)^n]) - b*e*n \\[Star] Int[SimplifyIntegrand[u/(d+e*x),x],x]] /;
        FreeQ[{a,b,c,d,e,f1,g1,f2,g2,n},x] && EqQ[f2*g1+f1*g2,0] && GtQ[f1,0] && GtQ[f2,0]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, e__, n_, f1__, g1__, f2__, g2__, x_],
        optional: [a__, b__, c__, e__, n_, g1__, g2__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f1__, g1__, f2__, g2__, n_], x_)
                && eqq!(&f2__ * &g1__ + &f1__ * &g2__, 0)
                && gtq!(f1__, 0)
                && gtq!(f2__, 0)
        },
        rhs: {
            let shifted = &d__ + &e__ * x_;
            let hidden_denominator = (&f1__ * &f2__ + &g1__ * &g2__ * x_.pow(2)).sqrt();
            let logarithmic = &a__ + &b__ * (&c__ * shifted.pow(&n_)).log();
            let u = rubi_int_hide(&(Atom::num(1) / hidden_denominator), x_).rubi_rhs();
            let recursive_integrand = rubi_simplify_integrand(&(&u / &shifted), x_);
            let recursive_primitive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(&u * logarithmic), x_)
                    - rubi_star(&b__ * &e__ * &n_, recursive_primitive)
        },
    ));
}

fn push_rules_rule_2853(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, n_, x_);
    rules.push(rubi_rule!(
        order: 2853,
        source: "Int[(a_.+b_.*Log[c_.*(d_+e_.*x_)^n_.])/Sqrt[f_+g_.*x_^2],x_Symbol] :=
          Sqrt[1+g/f*x^2]/Sqrt[f+g*x^2] \\[Star] Int[(a+b*Log[c*(d+e*x)^n])/Sqrt[1+g/f*x^2],x] /;
        FreeQ[{a,b,c,d,e,f,g,n},x] && Not[GtQ[f,0]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, e__, n_, f__, g__, x_],
        optional: [a__, b__, c__, e__, n_, g__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, n_], x_)
                && !gtq!(f__, 0)
        },
        rhs: {
            let shifted = &d__ + &e__ * x_;
            let normalizer = (Atom::num(1) + &g__ / &f__ * x_.pow(2)).sqrt();
            let denominator = (&f__ + &g__ * x_.pow(2)).sqrt();
            let logarithmic = &a__ + &b__ * (&c__ * shifted.pow(&n_)).log();
            let recursive_integrand = logarithmic / &normalizer;
            let recursive_primitive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(normalizer, recursive_primitive / denominator)
        },
    ));
}

fn push_rules_rule_2854(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f1__, f2__, g1__, g2__, n_, x_);
    rules.push(rubi_rule!(
        order: 2854,
        source: "Int[(a_.+b_.*Log[c_.*(d_+e_.*x_)^n_.])/(Sqrt[f1_+g1_.*x_]*Sqrt[f2_+g2_.*x_]),x_Symbol] :=
          Sqrt[1+g1*g2/(f1*f2)*x^2]/(Sqrt[f1+g1*x]*Sqrt[f2+g2*x]) \\[Star] Int[(a+b*Log[c*(d+e*x)^n])/Sqrt[1+g1*g2/(f1*f2)*x^2],x] /;
        FreeQ[{a,b,c,d,e,f1,g1,f2,g2,n},x] && EqQ[f2*g1+f1*g2,0]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, e__, n_, f1__, g1__, f2__, g2__, x_],
        optional: [a__, b__, c__, e__, n_, g1__, g2__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f1__, g1__, f2__, g2__, n_], x_)
                && eqq!(&f2__ * &g1__ + &f1__ * &g2__, 0)
        },
        rhs: {
            let shifted = &d__ + &e__ * x_;
            let ratio = &g1__ * &g2__ / (&f1__ * &f2__);
            let normalizer = (Atom::num(1) + &ratio * x_.pow(2)).sqrt();
            let denominator = (f1__ + g1__ * x_).sqrt() * (f2__ + g2__ * x_).sqrt();
            let logarithmic = &a__ + &b__ * (&c__ * shifted.pow(&n_)).log();
            let recursive_integrand = logarithmic / &normalizer;
            let recursive_primitive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(normalizer, recursive_primitive / denominator)
        },
    ));
}

fn push_rules_rule_2855(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, n_, p_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 2855,
        source: "Int[(f_.+g_.*x_^r_)^q_.*(a_.+b_.*Log[c_.*(d_+e_.*x_)^n_.])^p_.,x_Symbol] :=
          With[{k=Denominator[r]},
          k \\[Star] Subst[Int[x^(k-1)*(f+g*x^(k*r))^q*(a+b*Log[c*(d+e*x^k)^n])^p,x],x,x^(1/k)]] /;
        FreeQ[{a,b,c,d,e,f,g,n,p,q},x] && FractionQ[r] && IGtQ[p,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [f__, g__, r_, q_, a__, b__, c__, d__, e__, n_, p_, x_],
        optional: [f__, g__, a__, b__, c__, e__, n_, p_, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, n_, p_, q_], x_)
                && fractionq!(r_)
                && igtq!(p_, 0)
        },
        rhs: {
            let k_i = rubi_denominator(&r_).expect("FractionQ guard ensures a denominator");
            let k = Atom::num(k_i);
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let transformed_integrand = sub_atom.pow(&k - 1)
                * (&f__ + &g__ * sub_atom.pow(&k * &r_)).pow(&q_)
                * (&a__ + &b__ * (&c__ * (&d__ + &e__ * sub_atom.pow(&k)).pow(&n_)).log()).pow(&p_);
            let transformed_primitive = rubi_rhs_int(&transformed_integrand, substitution_symbol);
            let substitution = x_.pow(Atom::num(1) / &k);

            rubi_star(k, rubi_subst(&transformed_primitive, substitution_symbol, substitution))
        },
    ));
}

fn push_rules_rule_2856(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, n_, p_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 2856,
        source: "Int[(f_+g_.*x_^r_)^q_.*(a_.+b_.*Log[c_.*(d_+e_.*x_)^n_.])^p_.,x_Symbol] :=
          Int[ExpandIntegrand[(a+b*Log[c*(d+e*x)^n])^p,(f+g*x^r)^q,x],x] /;
        FreeQ[{a,b,c,d,e,f,g,n,r},x] && IGtQ[p,0] && IntegerQ[q] && (GtQ[q,0] || IntegerQ[r] && NeQ[r,1])",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [f__, g__, r_, q_, a__, b__, c__, d__, e__, n_, p_, x_],
        optional: [g__, a__, b__, c__, e__, n_, p_, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, n_, r_], x_)
                && igtq!(p_, 0)
                && integerq!(q_)
                && (gtq!(q_, 0) || integerq!(r_) && neq!(r_, 1))
        },
        rhs: {
            let u = (&a__ + &b__ * (&c__ * (&d__ + &e__ * x_).pow(&n_)).log()).pow(&p_);
            let v = (&f__ + &g__ * x_.pow(&r_)).pow(&q_);
            let expanded = rubi_expand_integrand_product(&u, &v, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_2857(rules: &mut Vec<RubiRule>) {
    rubi_symb!(c__, d__, e__, f__, g__, m_, x_);
    rules.push(rubi_rule!(
        order: 2857,
        source: "Int[x_^m_.*Log[c_.*(d_+e_.*x_)]/(f_+g_. x_),x_Symbol] :=
          Int[ExpandIntegrand[Log[c*(d+e*x)],x^m/(f+g*x),x],x] /;
        FreeQ[{c,d,e,f,g},x] && EqQ[e*f-d*g,0] && EqQ[c*d,1] && IntegerQ[m]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern: x_.pow(m_) * (c__ * (d__ + e__ * x_)).log() / (f__ + g__ * x_),
        with: [m_, c__, d__, e__, f__, g__, x_],
        optional: [m_, c__, e__, g__],
        when: {
            freeq!([c__, d__, e__, f__, g__], x_)
                && eqq!(&e__ * &f__ - &d__ * &g__, 0)
                && eqq!(&c__ * &d__, 1)
                && integerq!(m_)
        },
        rhs: {
            let u = (&c__ * (&d__ + &e__ * x_)).log();
            let v = x_.pow(&m_) / (&f__ + &g__ * x_);
            let expanded = rubi_expand_integrand_product(&u, &v, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_2858(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        a__, b__, c__, d__, e__, f__, g__, h__, i__, n_, p_, q_, r_, x_
    );
    rules.push(rubi_rule!(
        order: 2858,
        source: "Int[(f_.+g_. x_)^q_.*(h_.+i_. x_)^r_.*(a_.+b_.*Log[c_.*(d_+e_.*x_)^n_.])^p_.,x_Symbol] :=
          1/e \\[Star] Subst[Int[(g*x/e)^q*((e*h-d*i)/e+i*x/e)^r*(a+b*Log[c*x^n])^p,x],x,d+e*x] /;
        FreeQ[{a,b,c,d,e,f,g,h,i,n,p,q,r},x] && EqQ[e*f-d*g,0] && (IGtQ[p,0] || IGtQ[r,0]) && IntegerQ[2*r]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern: (f__ + g__ * x_).pow(q_)
            * (h__ + i__ * x_).pow(r_)
            * (a__ + b__ * (c__ * (d__ + e__ * x_).pow(n_)).log()).pow(p_),
        with: [f__, g__, q_, h__, i__, r_, a__, b__, c__, d__, e__, n_, p_, x_],
        optional: [f__, g__, q_, h__, i__, r_, a__, b__, c__, e__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__, i__, n_, p_, q_, r_], x_)
                && eqq!(&e__ * &f__ - &d__ * &g__, 0)
                && (igtq!(p_, 0) || igtq!(r_, 0))
                && integerq!(Atom::num(2) * &r_)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let transformed_integrand = (&g__ * &sub_atom / &e__).pow(&q_)
                * ((&e__ * &h__ - &d__ * &i__) / &e__ + &i__ * &sub_atom / &e__).pow(&r_)
                * (&a__ + &b__ * (&c__ * sub_atom.pow(&n_)).log()).pow(&p_);
            let transformed_primitive = rubi_rhs_int(&transformed_integrand, substitution_symbol);
            let substitution = &d__ + &e__ * x_;

            rubi_star(Atom::num(1) / &e__, rubi_subst(&transformed_primitive, substitution_symbol, substitution))
        },
    ));
}

fn push_rules_rule_2859(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 2859,
        source: "Int[x_^m_.*(f_+g_./x_)^q_.*(a_.+b_.*Log[c_.*(d_+e_.*x_)^n_.])^p_.,x_Symbol] :=
          Int[(g+f*x)^q*(a+b*Log[c*(d+e*x)^n])^p,x] /;
        FreeQ[{a,b,c,d,e,f,g,m,n,p,q},x] && EqQ[m,q] && IntegerQ[q]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: x_.pow(m_)
            * (f__ + g__ / x_).pow(q_)
            * (a__ + b__ * (c__ * (d__ + e__ * x_).pow(n_)).log()).pow(p_),
        with: [m_, f__, g__, q_, a__, b__, c__, d__, e__, n_, p_, x_],
        optional: [m_, g__, q_, a__, b__, c__, e__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, q_], x_)
                && eqq!(m_, q_)
                && integerq!(q_)
        },
        rhs: {
            let transformed_integrand = (&g__ + &f__ * x_).pow(&q_)
                * (&a__ + &b__ * (&c__ * (&d__ + &e__ * x_).pow(&n_)).log()).pow(&p_);

            rubi_rhs_int(&transformed_integrand, x_)
        },
    ));
}

fn push_rules_rule_2860(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 2860,
        source: "Int[x_^m_.*(f_.+g_.*x_^r_.)^q_.*(a_.+b_.*Log[c_.*(d_+e_.*x_)^n_.])^p_.,x_Symbol] :=
          (f+g*x^r)^(q+1)*(a+b*Log[c*(d+e*x)^n])^p/(g*r*(q+1)) -
          b*e*n*p/(g*r*(q+1)) \\[Star] Int[(f+g*x^r)^(q+1)*(a+b*Log[c*(d+e*x)^n])^(p-1)/(d+e*x),x] /;
        FreeQ[{a,b,c,d,e,f,g,m,n,q,r},x] && EqQ[m,r-1] && NeQ[q,-1] && IGtQ[p,0]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [m_, f__, g__, r_, q_, a__, b__, c__, d__, e__, n_, p_, x_],
        optional: [m_, f__, g__, r_, q_, a__, b__, c__, e__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, m_, n_, q_, r_], x_)
                && eqq!(m_, &r_ - 1)
                && neq!(q_, -1)
                && igtq!(p_, 0)
        },
        rhs: {
            let affine_power = (&f__ + &g__ * x_.pow(&r_)).pow(&q_ + 1);
            let logarithmic = &a__ + &b__ * (&c__ * (&d__ + &e__ * x_).pow(&n_)).log();
            let denominator = &g__ * &r_ * (&q_ + 1);
            let recursive_integrand =
                &affine_power * logarithmic.pow(&p_ - 1) / (&d__ + &e__ * x_);
            let recursive_primitive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(&affine_power * logarithmic.pow(&p_) / &denominator), x_)
                    - rubi_star(&b__ * &e__ * &n_ * &p_ / denominator, recursive_primitive)
        },
    ));
}

fn push_rules_rule_2861(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, m_, n_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 2861,
        source: "Int[x_^m_.*(f_+g_.*x_^r_.)^q_.*(a_.+b_.*Log[c_.*(d_+e_.*x_)^n_.]),x_Symbol] :=
          With[{u=IntHide[x^m*(f+g*x^r)^q,x]},
          (a+b*Log[c*(d+e*x)^n]) \\[Star] u - b*e*n \\[Star] Int[SimplifyIntegrand[u/(d+e*x),x],x] /;
         InverseFunctionFreeQ[u,x]] /;
        FreeQ[{a,b,c,d,e,f,g,m,n,q,r},x] && IntegerQ[m] && IntegerQ[q] && IntegerQ[r]",
        desc: "Integration by parts",
        refs: [],
        pattern: x_.pow(m_)
            * (f__ + g__ * x_.pow(r_)).pow(q_)
            * (a__ + b__ * (c__ * (d__ + e__ * x_).pow(n_)).log()),
        with: [m_, f__, g__, r_, q_, a__, b__, c__, d__, e__, n_, x_],
        optional: [m_, g__, r_, q_, a__, b__, c__, e__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, m_, n_, q_, r_], x_)
                && integerq!(m_)
                && integerq!(q_)
                && integerq!(r_)
                && rubi_int_hide_inverse_function_free_q(
                    &(x_.pow(&m_) * (&f__ + &g__ * x_.pow(&r_)).pow(&q_)),
                    x_,
                )
        },
        rhs: {
            let u =
                rubi_int_hide(&(x_.pow(&m_) * (&f__ + &g__ * x_.pow(&r_)).pow(&q_)), x_).rubi_rhs();

            let logarithmic = &a__ + &b__ * (&c__ * (&d__ + &e__ * x_).pow(&n_)).log();
            let recursive_integrand =
                rubi_simplify_integrand(&(&u / (&d__ + &e__ * x_)), x_);
            let recursive_primitive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(logarithmic, u)
                    - rubi_star(&b__ * &e__ * &n_, recursive_primitive)
        },
    ));
}

fn push_rules_rule_2862(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 2862,
        source: "Int[x_^m_.*(f_.+g_.*x_^r_)^q_.*(a_.+b_.*Log[c_.*(d_+e_.*x_)^n_.])^p_.,x_Symbol] :=
          With[{k=Denominator[r]},
          k \\[Star] Subst[Int[x^(k*(m+1)-1)*(f+g*x^(k*r))^q*(a+b*Log[c*(d+e*x^k)^n])^p,x],x,x^(1/k)]] /;
        FreeQ[{a,b,c,d,e,f,g,n,p,q},x] && FractionQ[r] && IGtQ[p,0] && IntegerQ[m]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [m_, f__, g__, r_, q_, a__, b__, c__, d__, e__, n_, p_, x_],
        optional: [m_, f__, g__, q_, a__, b__, c__, e__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, n_, p_, q_], x_)
                && fractionq!(r_)
                && igtq!(p_, 0)
                && integerq!(m_)
        },
        rhs: {
            let k_i = rubi_denominator(&r_).expect("FractionQ guard ensures a denominator");
            let k = Atom::num(k_i);
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let transformed_integrand = sub_atom.pow(&k * (&m_ + 1) - 1)
                * (&f__ + &g__ * sub_atom.pow(&k * &r_)).pow(&q_)
                * (&a__ + &b__ * (&c__ * (&d__ + &e__ * sub_atom.pow(&k)).pow(&n_)).log()).pow(&p_);
            let transformed_primitive = rubi_rhs_int(&transformed_integrand, substitution_symbol);
            let substitution = x_.pow(Atom::num(1) / &k);

            rubi_star(k, rubi_subst(&transformed_primitive, substitution_symbol, substitution))
        },
    ));
}

fn push_rules_rule_2863(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        a__, b__, c__, d__, e__, f__, g__, h__, m_, n_, p_, q_, r_, x_
    );
    rules.push(rubi_rule!(
        order: 2863,
        source: "Int[(h_.*x_)^m_.*(f_+g_.*x_^r_.)^q_.*(a_.+b_.*Log[c_.*(d_+e_.*x_)^n_.])^p_.,x_Symbol] :=
          Int[ExpandIntegrand[(a+b*Log[c*(d+e*x)^n])^p,(h*x)^m*(f+g*x^r)^q,x],x] /;
        FreeQ[{a,b,c,d,e,f,g,h,m,n,p,q,r},x] && IntegerQ[m] && IntegerQ[q]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (h__ * x_).pow(m_)
            * (f__ + g__ * x_.pow(r_)).pow(q_)
            * (a__ + b__ * (c__ * (d__ + e__ * x_).pow(n_)).log()).pow(p_),
        with: [h__, m_, f__, g__, r_, q_, a__, b__, c__, d__, e__, n_, p_, x_],
        optional: [h__, m_, g__, r_, q_, a__, b__, c__, e__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__, m_, n_, p_, q_, r_], x_)
                && integerq!(m_)
                && integerq!(q_)
        },
        rhs: {
            let u = (&a__ + &b__ * (&c__ * (&d__ + &e__ * x_).pow(&n_)).log()).pow(&p_);
            let v = (&h__ * x_).pow(&m_) * (&f__ + &g__ * x_.pow(&r_)).pow(&q_);
            let expanded = rubi_expand_integrand_product(&u, &v, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_2864(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, n_, p_, polyx__, x_);
    rules.push(rubi_rule!(
        order: 2864,
        source: "Int[Polyx_*(a_.+b_.*Log[c_.*(d_+e_.*x_)^n_.])^p_.,x_Symbol] :=
          Int[ExpandIntegrand[Polyx*(a+b*Log[c*(d+e*x)^n])^p,x],x] /;
        FreeQ[{a,b,c,d,e,n,p},x] && PolynomialQ[Polyx,x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: polyx__ * (a__ + b__ * (c__ * (d__ + e__ * x_).pow(n_)).log()).pow(p_),
        with: [polyx__, a__, b__, c__, d__, e__, n_, p_, x_],
        optional: [a__, b__, c__, e__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, n_, p_], x_)
                && rubi_polynomial_q(&polyx__, x_)
        },
        rhs: {
            let expand_integrand_payload =
                &polyx__ * (&a__ + &b__ * (&c__ * (&d__ + &e__ * x_).pow(&n_)).log()).pow(&p_);
            let expanded = rubi_expand_integrand(&expand_integrand_payload, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_2865(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, p_, rfx__, x_);
    rules.push(rubi_rule!(
        order: 2865,
        source: "Int[RFx_*(a_.+b_.*Log[c_.*(d_+e_.*x_)^n_.])^p_.,x_Symbol] :=
          With[{u=ExpandIntegrand[(a+b*Log[c*(d+e*x)^n])^p,RFx,x]},
          Int[u,x] /;
         SumQ[u]] /;
        FreeQ[{a,b,c,d,e,n},x] && RationalFunctionQ[RFx,x] && IntegerQ[p]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [rfx__, a__, b__, c__, d__, e__, n_, p_, x_],
        optional: [a__, b__, c__, e__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, n_], x_)
                && rubi_rational_function_q(&rfx__, x_)
                && integerq!(p_)
                && {
                    let log_power =
                        (&a__ + &b__ * (&c__ * (&d__ + &e__ * x_).pow(&n_)).log()).pow(&p_);
                    rubi_expand_integrand_product_sum(&log_power, &rfx__, x_).is_some()
                }
        },
        rhs: {
            let log_power =
                (&a__ + &b__ * (&c__ * (&d__ + &e__ * x_).pow(&n_)).log()).pow(&p_);
            let u = rubi_expand_integrand_product_sum(&log_power, &rfx__, x_)
                .expect("when clause should ensure expanded integrand is a sum");

            rubi_rhs_int(&u, x_)
        },
    ));
}

fn push_rules_rule_2866(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, p_, rfx__, x_);
    rules.push(rubi_rule!(
        order: 2866,
        source: "Int[RFx_*(a_.+b_.*Log[c_.*(d_+e_.*x_)^n_.])^p_.,x_Symbol] :=
          With[{u=ExpandIntegrand[RFx*(a+b*Log[c*(d+e*x)^n])^p,x]},
          Int[u,x] /;
         SumQ[u]] /;
        FreeQ[{a,b,c,d,e,n},x] && RationalFunctionQ[RFx,x] && IntegerQ[p]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [rfx__, a__, b__, c__, d__, e__, n_, p_, x_],
        optional: [a__, b__, c__, e__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, n_], x_)
                && rubi_rational_function_q(&rfx__, x_)
                && integerq!(p_)
                && {
                    rubi_expand_integrand_sum(
                        &(&rfx__
                            * (&a__ + &b__ * (&c__ * (&d__ + &e__ * x_).pow(&n_)).log()).pow(&p_)),
                        x_,
                    )
                    .is_some()
                }
        },
        rhs: {
            let u = rubi_expand_integrand_sum(
                &(&rfx__ * (&a__ + &b__ * (&c__ * (&d__ + &e__ * x_).pow(&n_)).log()).pow(&p_)),
                x_,
            )
            .expect("when clause should ensure expanded integrand is a sum");

            rubi_rhs_int(&u, x_)
        },
    ));
}

fn push_rules_rule_2867(rules: &mut Vec<RubiRule>) {
    rubi_symb!(afx__, a__, b__, c__, d__, e__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 2867,
        source: "Int[AFx_*(a_.+b_.*Log[c_.*(d_+e_.*x_)^n_.])^p_.,x_Symbol] :=
          Unintegrable[AFx*(a+b*Log[c*(d+e*x)^n])^p,x] /;
        FreeQ[{a,b,c,d,e,n,p},x] && AlgebraicFunctionQ[AFx,x,True]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern: afx__ * (a__ + b__ * (c__ * (d__ + e__ * x_).pow(n_)).log()).pow(p_),
        with: [afx__, a__, b__, c__, d__, e__, n_, p_, x_],
        optional: [a__, b__, c__, e__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, n_, p_], x_)
                && rubi_algebraic_function_q(&afx__, x_, true)
        },
        rhs: {
            let integrand =
                &afx__ * (&a__ + &b__ * (&c__ * (&d__ + &e__ * x_).pow(&n_)).log()).pow(&p_);

            rubi_unintegrable(integrand, x_)
        },
    ));
}

fn push_rules_rule_2868(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, n_, p_, q_, u__, v__);
    let rule = rubi_rule!(
        order: 2868,
        source: "Int[u_^q_.*(a_.+b_.*Log[c_.*v_^n_.])^p_.,x_Symbol] :=
          Int[ExpandToSum[u,x]^q*(a+b*Log[c*ExpandToSum[v,x]^n])^p,x] /;
        FreeQ[{a,b,c,n,p,q},x] && BinomialQ[u,x] && LinearQ[v,x] && Not[BinomialMatchQ[u,x] && LinearMatchQ[v,x]]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: u__.pow(q_) * (a__ + b__ * (c__ * v__.pow(n_)).log()).pow(p_),
        with: [u__, q_, a__, b__, c__, v__, n_, p_, x_],
        optional: [q_, a__, b__, c__, n_, p_],
        when: {
            freeq!([a__, b__, c__, n_, p_, q_], x_)
                && rubi_binomial_q(&u__, x_)
                && rubi_linear_q(&v__, x_)
                && !(rubi_binomial_match_q(&u__, x_) && rubi_linear_match_q(&v__, x_))
        },
        rhs: {
            let expanded_u = rubi_expand_to_sum(&u__, x_);
            let expanded_v = rubi_expand_to_sum(&v__, x_);
            let recursive_integrand =
                expanded_u.pow(&q_) * (&a__ + &b__ * (&c__ * expanded_v.pow(&n_)).log()).pow(&p_);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    );
    rules.push(rule.with_early_x_dependent(u__).with_early_x_dependent(v__));
}

fn push_rules_rule_2869(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 2869,
        source: "Int[Log[f_.*x_^m_.]*(a_.+b_.*Log[c_.*(d_+e_.*x_)^n_.]),x_Symbol] :=
          -x*(m-Log[f*x^m])*(a+b*Log[c*(d+e*x)^n]) + b*e*m*n \\[Star] Int[x/(d+e*x),x] - b*e*n \\[Star] Int[(x*Log[f*x^m])/(d+e*x),x] /;
        FreeQ[{a,b,c,d,e,f,m,n},x]",
        desc: "Integration by parts",
        refs: [],
        pattern: (f__ * x_.pow(m_)).log()
            * (a__ + b__ * (c__ * (d__ + e__ * x_).pow(n_)).log()),
        with: [f__, m_, a__, b__, c__, d__, e__, n_, x_],
        optional: [f__, m_, a__, b__, c__, e__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_], x_)
        },
        rhs: {
            let affine = &d__ + &e__ * x_;
            let x_log = (&f__ * x_.pow(&m_)).log();
            let logarithmic = &a__ + &b__ * (&c__ * affine.pow(&n_)).log();
            let first_recursive_integrand = x_ / &affine;
            let second_recursive_integrand = x_ * &x_log / &affine;
            let first_recursive_primitive = rubi_rhs_int(&first_recursive_integrand, x_);
            let second_recursive_primitive = rubi_rhs_int(&second_recursive_integrand, x_);

            rubi_simp(&(Atom::num(-1) * x_ * (&m_ - &x_log) * logarithmic), x_)
                    - rubi_star(&b__ * &e__ * &n_, second_recursive_primitive)
                    + rubi_star(&b__ * &e__ * &m_ * &n_, first_recursive_primitive)
        },
    ));
}

fn push_rules_rule_2870(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 2870,
        source: "Int[Log[f_.*x_^m_.]*(a_.+b_.*Log[c_.*(d_+e_.*x_)^n_.])^p_,x_Symbol] :=
          With[{u=IntHide[(a+b*Log[c*(d+e*x)^n])^p,x]},
          Log[f*x^m] \\[Star] u - m \\[Star] Int[1/x \\[Star] u,x]] /;
        FreeQ[{a,b,c,d,e,f,m,n},x] && IGtQ[p,1]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [f__, m_, a__, b__, c__, d__, e__, n_, p_, x_],
        optional: [f__, m_, a__, b__, c__, e__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_], x_)
                && igtq!(p_, 1)
        },
        rhs: {
            let x_log = (&f__ * x_.pow(&m_)).log();
            let logarithmic =
                &a__ + &b__ * (&c__ * (&d__ + &e__ * x_).pow(&n_)).log();
            let u = rubi_int_hide(&logarithmic.pow(&p_), x_).rubi_rhs();
            let recursive_integrand =
                rubi_star(Atom::num(1) / x_, &u);
            let recursive_primitive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(&x_log, u)
                    - rubi_star(m_, recursive_primitive)
        },
    ));
}

fn push_rules_rule_2871(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 2871,
        source: "Int[Log[f_.*x_^m_.]*(a_.+b_.*Log[c_.*(d_+e_.*x_)^n_.])^p_.,x_Symbol] :=
          Unintegrable[Log[f*x^m]*(a+b*Log[c*(d+e*x)^n])^p,x] /;
        FreeQ[{a,b,c,d,e,f,m,n,p},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [f__, m_, a__, b__, c__, d__, e__, n_, p_, x_],
        optional: [f__, m_, a__, b__, c__, e__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_, p_], x_)
        },
        rhs: {
            let integrand = (&f__ * x_.pow(&m_)).log()
                * (&a__ + &b__ * (&c__ * (&d__ + &e__ * x_).pow(&n_)).log()).pow(&p_);

            rubi_unintegrable(integrand, x_)
        },
    ));
}

fn push_rules_rule_2872(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 2872,
        source: "Int[Log[f_.*x_^m_.]*(a_.+b_.*Log[c_.*(d_+e_.*x_)^n_.])/x_,x_Symbol] :=
          Log[f*x^m]^2*(a+b*Log[c*(d+e*x)^n])/(2*m) - b*e*n/(2*m) \\[Star] Int[Log[f*x^m]^2/(d+e*x),x] /;
        FreeQ[{a,b,c,d,e,f,m,n},x]",
        desc: "Integration by parts",
        refs: [],
        pattern: (f__ * x_.pow(m_)).log()
            * (a__ + b__ * (c__ * (d__ + e__ * x_).pow(n_)).log())
            / x_,
        with: [f__, m_, a__, b__, c__, d__, e__, n_, x_],
        optional: [f__, m_, a__, b__, c__, e__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_], x_)
        },
        rhs: {
            let affine = &d__ + &e__ * x_;
            let x_log = (&f__ * x_.pow(&m_)).log();
            let logarithmic = &a__ + &b__ * (&c__ * affine.pow(&n_)).log();
            let denominator = Atom::num(2) * &m_;
            let recursive_integrand = &x_log.pow(2) / &affine;
            let recursive_primitive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(&x_log.pow(2) * logarithmic / &denominator), x_)
                    - rubi_star(&b__ * &e__ * &n_ / denominator, recursive_primitive)
        },
    ));
}

fn push_rules_rule_2873(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, m_, n_, q_, x_);
    rules.push(rubi_rule!(
        order: 2873,
        source: "Int[(g_.*x_)^q_.*Log[f_.*x_^m_.]*(a_.+b_.*Log[c_.*(d_+e_.*x_)^n_.]),x_Symbol] :=
          -1/(g*(q+1))*(m*(g*x)^(q+1)/(q+1)-(g*x)^(q+1)*Log[f*x^m])*(a+b*Log[c*(d+e*x)^n]) +
          b*e*m*n/(g*(q+1)^2) \\[Star] Int[(g*x)^(q+1)/(d+e*x),x] -
          b*e*n/(g*(q+1)) \\[Star] Int[(g*x)^(q+1)*Log[f*x^m]/(d+e*x),x] /;
        FreeQ[{a,b,c,d,e,f,g,m,n,q},x] && NeQ[q,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern: (g__ * x_).pow(q_)
            * (f__ * x_.pow(m_)).log()
            * (a__ + b__ * (c__ * (d__ + e__ * x_).pow(n_)).log()),
        with: [g__, q_, f__, m_, a__, b__, c__, d__, e__, n_, x_],
        optional: [g__, q_, f__, m_, a__, b__, c__, e__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, m_, n_, q_], x_)
                && neq!(q_, -1)
        },
        rhs: {
            let affine = &d__ + &e__ * x_;
            let q_plus_one = &q_ + 1;
            let gx_power = (&g__ * x_).pow(&q_plus_one);
            let x_log = (&f__ * x_.pow(&m_)).log();
            let logarithmic = &a__ + &b__ * (&c__ * affine.pow(&n_)).log();
            let denominator = &g__ * &q_plus_one;
            let square_denominator = &g__ * q_plus_one.pow(2);
            let leading_factor = &m_ * &gx_power / &q_plus_one - &gx_power * &x_log;
            let first_recursive_integrand = &gx_power / &affine;
            let second_recursive_integrand = &gx_power * &x_log / &affine;
            let first_recursive_primitive = rubi_rhs_int(&first_recursive_integrand, x_);
            let second_recursive_primitive = rubi_rhs_int(&second_recursive_integrand, x_);

            rubi_simp(&(-leading_factor * logarithmic / &denominator), x_)
                    - rubi_star(&b__ * &e__ * &n_ / denominator, second_recursive_primitive)
                    + rubi_star(&b__ * &e__ * &m_ * &n_ / square_denominator, first_recursive_primitive)
        },
    ));
}

fn push_rules_rule_2874(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 2874,
        source: "Int[Log[f_.*x_^m_.]*(a_.+b_.*Log[c_.*(d_+e_.*x_)^n_.])^p_./x_,x_Symbol] :=
          Log[f*x^m]^2*(a+b*Log[c*(d+e*x)^n])^p/(2*m) - b*e*n*p/(2*m) \\[Star] Int[Log[f*x^m]^2*(a+b*Log[c*(d+e*x)^n])^(p-1)/(d+e*x),x] /;
        FreeQ[{a,b,c,d,e,f,m,n},x] && IGtQ[p,0]",
        desc: "Integration by parts",
        refs: [],
        pattern: (f__ * x_.pow(m_)).log()
            * (a__ + b__ * (c__ * (d__ + e__ * x_).pow(n_)).log()).pow(p_)
            / x_,
        with: [f__, m_, a__, b__, c__, d__, e__, n_, p_, x_],
        optional: [f__, m_, a__, b__, c__, e__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_], x_)
                && igtq!(p_, 0)
        },
        rhs: {
            let affine = &d__ + &e__ * x_;
            let x_log = (&f__ * x_.pow(&m_)).log();
            let logarithmic = &a__ + &b__ * (&c__ * affine.pow(&n_)).log();
            let denominator = Atom::num(2) * &m_;
            let recursive_integrand = &x_log.pow(2) * logarithmic.pow(&p_ - 1) / &affine;
            let recursive_primitive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(
                    &(&x_log.pow(2) * logarithmic.pow(&p_) / &denominator),
                    x_,
                ) - rubi_star(&b__ * &e__ * &n_ * &p_ / denominator, recursive_primitive)
        },
    ));
}

fn push_rules_rule_2875(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 2875,
        source: "Int[(g_.*x_)^q_.*Log[f_.*x_^m_.]*(a_.+b_.*Log[c_.*(d_+e_.*x_)^n_.])^p_,x_Symbol] :=
          With[{u=IntHide[(g*x)^q*(a+b*Log[c*(d+e*x)^n])^p,x]},
          Log[f*x^m] \\[Star] u - m \\[Star] Int[1/x \\[Star] u,x]] /;
        FreeQ[{a,b,c,d,e,f,g,m,n,q},x] && IGtQ[p,1] && IGtQ[q,0]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [g__, q_, f__, m_, a__, b__, c__, d__, e__, n_, p_, x_],
        optional: [g__, q_, f__, m_, a__, b__, c__, e__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, m_, n_, q_], x_)
                && igtq!(p_, 1)
                && igtq!(q_, 0)
        },
        rhs: {
            let x_log = (&f__ * x_.pow(&m_)).log();
            let logarithmic = &a__ + &b__ * (&c__ * (&d__ + &e__ * x_).pow(&n_)).log();
            let hidden_integrand = (&g__ * x_).pow(&q_) * logarithmic.pow(&p_);
            let u = rubi_int_hide(&hidden_integrand, x_).rubi_rhs();
            let recursive_integrand =
                rubi_star(Atom::num(1) / x_, &u);
            let recursive_primitive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(&x_log, u)
                    - rubi_star(m_, recursive_primitive)
        },
    ));
}

fn push_rules_rule_2876(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 2876,
        source: "Int[(g_.*x_)^q_.*Log[f_.*x_^m_.]*(a_.+b_.*Log[c_.*(d_+e_.*x_)^n_.])^p_.,x_Symbol] :=
          Unintegrable[(g*x)^q*Log[f*x^m]*(a+b*Log[c*(d+e*x)^n])^p,x] /;
        FreeQ[{a,b,c,d,e,f,g,m,n,p,q},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [g__, q_, f__, m_, a__, b__, c__, d__, e__, n_, p_, x_],
        optional: [g__, q_, f__, m_, a__, b__, c__, e__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, q_], x_)
        },
        rhs: {
            let integrand = (&g__ * x_).pow(&q_)
                * (&f__ * x_.pow(&m_)).log()
                * (&a__ + &b__ * (&c__ * (&d__ + &e__ * x_).pow(&n_)).log()).pow(&p_);

            rubi_unintegrable(integrand, x_)
        },
    ));
}

fn push_rules_rule_2877(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, h__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 2877,
        source: "Int[Log[f_.*(g_.+h_.*x_)^m_.]*(a_.+b_.*Log[c_.*(d_+e_.*x_)^n_.])^p_.,x_Symbol] :=
          1/e \\[Star] Subst[Int[Log[f*(g*x/d)^m]*(a+b*Log[c*x^n])^p,x],x,d+e*x] /;
        FreeQ[{a,b,c,d,e,f,g,h,m,n,p},x] && EqQ[e*f-d*g,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (f__ * (g__ + h__ * x_).pow(m_)).log()
            * (a__ + b__ * (c__ * (d__ + e__ * x_).pow(n_)).log()).pow(p_),
        with: [f__, g__, h__, m_, a__, b__, c__, d__, e__, n_, p_, x_],
        optional: [f__, g__, h__, m_, a__, b__, c__, e__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__, m_, n_, p_], x_)
                && eqq!(&e__ * &f__ - &d__ * &g__, 0)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let transformed_integrand = (&f__ * (&g__ * &sub_atom / &d__).pow(&m_)).log()
                * (&a__ + &b__ * (&c__ * sub_atom.pow(&n_)).log()).pow(&p_);
            let transformed_primitive = rubi_rhs_int(&transformed_integrand, substitution_symbol);
            let substitution = &d__ + &e__ * x_;

            rubi_star(Atom::num(1) / &e__, rubi_subst(&transformed_primitive, substitution_symbol, substitution))
        },
    ));
}

fn push_rules_rule_2878(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, n_, x_);
    rules.push(rubi_rule!(
        order: 2878,
        source: "Int[(a_.+b_.*Log[c_.*(d_+e_.*x_)^n_.])*(f_.+g_.*Log[c_.*(d_+e_.*x_)^n_.]),x_Symbol] :=
          x*(a+b*Log[c*(d+e*x)^n])*(f+g*Log[c*(d+e*x)^n]) -
          e*n \\[Star] Int[(x*(b*f+a*g+2*b*g*Log[c*(d+e*x)^n]))/(d+e*x),x] /;
        FreeQ[{a,b,c,d,e,f,g,n},x]",
        desc: "Integration by parts",
        refs: [],
        pattern: (a__ + b__ * (c__ * (d__ + e__ * x_).pow(n_)).log())
            * (f__ + g__ * (c__ * (d__ + e__ * x_).pow(n_)).log()),
        with: [a__, b__, c__, d__, e__, n_, f__, g__, x_],
        optional: [a__, b__, c__, e__, n_, f__, g__],
        when: { freeq!([a__, b__, c__, d__, e__, f__, g__, n_], x_) },
        rhs: {
            let logarithm = (&c__ * (&d__ + &e__ * x_).pow(&n_)).log();
            let first = &a__ + &b__ * &logarithm;
            let second = &f__ + &g__ * &logarithm;
            let recursive_integrand = x_
                * (&b__ * &f__ + &a__ * &g__ + 2 * &b__ * &g__ * &logarithm)
                / (&d__ + &e__ * x_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            rubi_simp(&(x_ * first * second), x_)
                    - rubi_star(&e__ * &n_, recursive)
        },
    ));
}

fn push_rules_rule_2879(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        a__, b__, c__, d__, e__, f__, g__, h__, i__, j__, m_, n_, p_, x_
    );
    rules.push(rubi_rule!(
        order: 2879,
        source: "Int[(a_.+b_.*Log[c_.*(d_+e_.*x_)^n_.])^p_.*(f_.+g_.*Log[h_.*(i_.+j_.*x_)^m_.]),x_Symbol] :=
          x*(a+b*Log[c*(d+e*x)^n])^p*(f+g*Log[h*(i+j*x)^m]) -
          g*j*m \\[Star] Int[x*(a+b*Log[c*(d+e*x)^n])^p/(i+j*x),x] -
          b*e*n*p \\[Star] Int[x*(a+b*Log[c*(d+e*x)^n])^(p-1)*(f+g*Log[h*(i+j*x)^m])/(d+e*x),x] /;
        FreeQ[{a,b,c,d,e,f,g,h,i,j,m,n},x] && IGtQ[p,0]",
        desc: "Integration by parts",
        refs: [],
        pattern: (a__ + b__ * (c__ * (d__ + e__ * x_).pow(n_)).log()).pow(p_)
            * (f__ + g__ * (h__ * (i__ + j__ * x_).pow(m_)).log()),
        with: [a__, b__, c__, d__, e__, n_, p_, f__, g__, h__, i__, j__, m_, x_],
        optional: [a__, b__, c__, e__, n_, p_, f__, g__, h__, i__, j__, m_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__, i__, j__, m_, n_], x_)
                && igtq!(p_, 0)
        },
        rhs: {
            let first_affine = &d__ + &e__ * x_;
            let second_affine = &i__ + &j__ * x_;
            let first_logarithmic = &a__ + &b__ * (&c__ * first_affine.pow(&n_)).log();
            let second_logarithmic = &f__ + &g__ * (&h__ * second_affine.pow(&m_)).log();
            let first_recursive_integrand = x_ * first_logarithmic.pow(&p_) / &second_affine;
            let second_recursive_integrand =
                x_ * first_logarithmic.pow(&p_ - 1) * &second_logarithmic / &first_affine;
            let first_recursive_primitive = rubi_rhs_int(&first_recursive_integrand, x_);
            let second_recursive_primitive = rubi_rhs_int(&second_recursive_integrand, x_);

            rubi_simp(
                    &(x_ * first_logarithmic.pow(&p_) * second_logarithmic),
                    x_,
                ) - rubi_star(&g__ * &j__ * &m_, first_recursive_primitive) - rubi_star(&b__ * &e__ * &n_ * &p_, second_recursive_primitive)
        },
    ));
}

fn push_rules_rule_2880(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        a__, b__, c__, d__, e__, f__, g__, h__, i__, j__, m_, n_, p_, q_, x_
    );
    rules.push(rubi_rule!(
        order: 2880,
        source: "Int[(a_.+b_.*Log[c_.*(d_+e_.*x_)^n_.])^p_.*(f_.+g_.*Log[h_.*(i_.+j_.*x_)^m_.])^q_.,x_Symbol] :=
          Unintegrable[(a+b*Log[c*(d+e*x)^n])^p*(f+g*Log[h*(i+j*x)^m])^q,x] /;
        FreeQ[{a,b,c,d,e,f,g,h,i,j,m,n,p},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern: (a__ + b__ * (c__ * (d__ + e__ * x_).pow(n_)).log()).pow(p_)
            * (f__ + g__ * (h__ * (i__ + j__ * x_).pow(m_)).log()).pow(q_),
        with: [a__, b__, c__, d__, e__, n_, p_, f__, g__, h__, i__, j__, m_, q_, x_],
        optional: [a__, b__, c__, e__, n_, p_, f__, g__, h__, i__, j__, m_, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__, i__, j__, m_, n_, p_], x_)
        },
        rhs: {
            let first_logarithmic =
                &a__ + &b__ * (&c__ * (&d__ + &e__ * x_).pow(&n_)).log();
            let second_logarithmic =
                &f__ + &g__ * (&h__ * (&i__ + &j__ * x_).pow(&m_)).log();
            let integrand = first_logarithmic.pow(&p_) * second_logarithmic.pow(&q_);

            rubi_unintegrable(integrand, x_)
        },
    ));
}

fn push_rules_rule_2881(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        a__, b__, c__, d__, e__, f__, g__, h__, i__, j__, k__, l__, m_, n_, p_, r_, x_
    );
    rules.push(rubi_rule!(
        order: 2881,
        source: "Int[(k_.+l_.*x_)^r_.*(a_.+b_.*Log[c_.*(d_+e_.*x_)^n_.])^p_.*(f_.+g_.*Log[h_.*(i_.+j_.*x_)^m_.]),x_Symbol] :=
          1/e \\[Star] Subst[Int[(k*x/d)^r*(a+b*Log[c*x^n])^p*(f+g*Log[h*((e*i-d*j)/e+j*x/e)^m]),x],x,d+e*x] /;
        FreeQ[{a,b,c,d,e,f,g,h,i,j,k,l,n,p,r},x] && EqQ[e*k-d*l,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (k__ + l__ * x_).pow(r_)
            * (a__ + b__ * (c__ * (d__ + e__ * x_).pow(n_)).log()).pow(p_)
            * (f__ + g__ * (h__ * (i__ + j__ * x_).pow(m_)).log()),
        with: [k__, l__, r_, a__, b__, c__, d__, e__, n_, p_, f__, g__, h__, i__, j__, m_, x_],
        optional: [k__, l__, r_, a__, b__, c__, e__, n_, p_, f__, g__, h__, i__, j__, m_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__, i__, j__], x_)
                && freeq!([k__, l__, n_, p_, r_], x_)
                && eqq!(&e__ * &k__ - &d__ * &l__, 0)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let shifted_second_affine =
                (&e__ * &i__ - &d__ * &j__) / &e__ + &j__ * &sub_atom / &e__;
            let transformed_integrand = (&k__ * &sub_atom / &d__).pow(&r_)
                * (&a__ + &b__ * (&c__ * sub_atom.pow(&n_)).log()).pow(&p_)
                * (&f__ + &g__ * (&h__ * shifted_second_affine.pow(&m_)).log());
            let transformed_primitive = rubi_rhs_int(&transformed_integrand, substitution_symbol);
            let substitution = &d__ + &e__ * x_;

            rubi_star(Atom::num(1) / &e__, rubi_subst(&transformed_primitive, substitution_symbol, substitution))
        },
    ));
}

fn push_rules_rule_2882(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, n_, x_);
    rules.push(rubi_rule!(
        order: 2882,
        source: "Int[(a_.+b_.*Log[c_.*(d_+e_.*x_)^n_.])*(f_.+g_.*Log[c_.*(d_+e_.*x_)^n_.])/x_,x_Symbol] :=
          Log[x]*(a+b*Log[c*(d+e*x)^n])*(f+g*Log[c*(d+e*x)^n]) -
          e*n \\[Star] Int[(Log[x]*(b*f+a*g+2*b*g*Log[c*(d+e*x)^n]))/(d+e*x),x] /;
        FreeQ[{a,b,c,d,e,f,g,n},x]",
        desc: "Integration by parts",
        refs: [],
        pattern: (a__ + b__ * (c__ * (d__ + e__ * x_).pow(n_)).log())
            * (f__ + g__ * (c__ * (d__ + e__ * x_).pow(n_)).log())
            / x_,
        with: [a__, b__, c__, d__, e__, n_, f__, g__, x_],
        optional: [a__, b__, c__, e__, n_, f__, g__],
        when: { freeq!([a__, b__, c__, d__, e__, f__, g__, n_], x_) },
        rhs: {
            let x_logarithm = x_.log();
            let logarithm = (&c__ * (&d__ + &e__ * x_).pow(&n_)).log();
            let first = &a__ + &b__ * &logarithm;
            let second = &f__ + &g__ * &logarithm;
            let recursive_integrand = &x_logarithm
                * (&b__ * &f__ + &a__ * &g__ + 2 * &b__ * &g__ * &logarithm)
                / (&d__ + &e__ * x_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            rubi_simp(&(&x_logarithm * first * second), x_)
                    - rubi_star(&e__ * &n_, recursive)
        },
    ));
}

fn push_rules_rule_2883(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 2883,
        source: "Int[x_^m_.*(a_.+b_.*Log[c_.*(d_+e_.*x_)^n_.])*(f_.+g_.*Log[c_.*(d_+e_.*x_)^n_.]),x_Symbol] :=
          x^(m+1)*(a+b*Log[c*(d+e*x)^n])*(f+g*Log[c*(d+e*x)^n])/(m+1) -
          e*n/(m+1) \\[Star] Int[(x^(m+1)*(b*f+a*g+2*b*g*Log[c*(d+e*x)^n]))/(d+e*x),x] /;
        FreeQ[{a,b,c,d,e,f,g,n,m},x] && NeQ[m,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern: x_.pow(m_)
            * (a__ + b__ * (c__ * (d__ + e__ * x_).pow(n_)).log())
            * (f__ + g__ * (c__ * (d__ + e__ * x_).pow(n_)).log()),
        with: [m_, a__, b__, c__, d__, e__, n_, f__, g__, x_],
        optional: [m_, a__, b__, c__, e__, n_, f__, g__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, n_, m_], x_) && neq!(m_, -1)
        },
        rhs: {
            let logarithm = (&c__ * (&d__ + &e__ * x_).pow(&n_)).log();
            let first = &a__ + &b__ * &logarithm;
            let second = &f__ + &g__ * &logarithm;
            let m1 = &m_ + 1;
            let recursive_integrand = x_.pow(&m1)
                * (&b__ * &f__ + &a__ * &g__ + 2 * &b__ * &g__ * &logarithm)
                / (&d__ + &e__ * x_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            rubi_simp(&(x_.pow(&m1) * first * second / &m1), x_)
                    - rubi_star(&e__ * &n_ / &m1, recursive)
        },
    ));
}

fn push_rules_rule_2884(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, h__, i__, j__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 2884,
        source: "Int[(a_.+b_.*Log[c_.*(d_+e_.*x_)^n_.])*(f_.+g_.*Log[h_.*(i_.+j_.*x_)^m_.])/x_,x_Symbol] :=
          Log[x]*(a+b*Log[c*(d+e*x)^n])*(f+g*Log[h*(i+j*x)^m]) -
          e*g*m \\[Star] Int[Log[x]*(a+b*Log[c*(d+e*x)^n])/(d+e*x),x] -
          b*j*n \\[Star] Int[Log[x]*(f+g*Log[h*(i+j*x)^m])/(i+j*x),x]/;
        FreeQ[{a,b,c,d,e,f,g,h,i,j,m,n},x] && EqQ[e*i-d*j,0]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, e__, n_, f__, g__, h__, i__, j__, m_, x_],
        optional: [a__, b__, c__, e__, n_, f__, g__, h__, i__, j__, m_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__, i__, j__, m_, n_], x_)
                && eqq!(&e__ * &i__ - &d__ * &j__, 0)
        },
        rhs: {
            let first_affine = &d__ + &e__ * x_;
            let second_affine = &i__ + &j__ * x_;
            let x_log = x_.log();
            let first_logarithmic = &a__ + &b__ * (&c__ * first_affine.pow(&n_)).log();
            let second_logarithmic = &f__ + &g__ * (&h__ * second_affine.pow(&m_)).log();
            let first_recursive_integrand = &x_log * &first_logarithmic / &first_affine;
            let second_recursive_integrand = &x_log * &second_logarithmic / &second_affine;
            let first_recursive_primitive = rubi_rhs_int(&first_recursive_integrand, x_);
            let second_recursive_primitive = rubi_rhs_int(&second_recursive_integrand, x_);

            rubi_simp(&(&x_log * first_logarithmic * second_logarithmic), x_)
                    - rubi_star(&e__ * &g__ * &m_, first_recursive_primitive)
                    - rubi_star(&b__ * &j__ * &n_, second_recursive_primitive)
        },
    ));
}

fn push_rules_rule_2885(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 2885,
        source: "Int[Log[a_+b_.*x_]*Log[c_+d_.*x_]/x_,x_Symbol] :=
          Log[-b*x/a]*Log[a+b*x]*Log[c+d*x] -
          1/2*(Log[-b*x/a]-Log[-d*x/c])*(Log[a+b*x]+Log[a*(c+d*x)/(c*(a+b*x))])^2 +
          1/2*(Log[-b*x/a]-Log[-(b*c-a*d)*x/(a*(c+d*x))]+Log[(b*c-a*d)/(b*(c+d*x))])*Log[a*(c+d*x)/(c*(a+b*x))]^2 +
          (Log[c+d*x]-Log[a*(c+d*x)/(c*(a+b*x))])*PolyLog[2,1+b*x/a] +
          (Log[a+b*x]+Log[a*(c+d*x)/(c*(a+b*x))])*PolyLog[2,1+d*x/c] -
          Log[a*(c+d*x)/(c*(a+b*x))]*PolyLog[2,d*(a+b*x)/(b*(c+d*x))] +
          Log[a*(c+d*x)/(c*(a+b*x))]*PolyLog[2,c*(a+b*x)/(a*(c+d*x))] -
          PolyLog[3,1+b*x/a] - PolyLog[3,1+d*x/c] - PolyLog[3,d*(a+b*x)/(b*(c+d*x))] + PolyLog[3,c*(a+b*x)/(a*(c+d*x))]/;
        FreeQ[{a,b,c,d},x] && NeQ[b*c-a*d,0]",
        desc: "Integration by parts and ???",
        refs: [],
        pattern: (a__ + b__ * x_).log() * (c__ + d__ * x_).log() / x_,
        with: [a__, b__, c__, d__, x_],
        optional: [b__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
        },
        rhs: {
            let ax = &a__ + &b__ * x_;
            let cx = &c__ + &d__ * x_;
            let ratio = &a__ * &cx / (&c__ * &ax);
            let determinant = &b__ * &c__ - &a__ * &d__;
            let bx = Atom::num(1) + &b__ * x_ / &a__;
            let dx = Atom::num(1) + &d__ * x_ / &c__;
            let cross_c = &c__ * &ax / (&a__ * &cx);
            let cross_d = &d__ * &ax / (&b__ * &cx);

            rubi_simp(
                    &((-&b__ * x_ / &a__).log() * ax.log() * cx.log()),
                    x_,
                ) + rubi_simp(
                    &((Atom::num(1) / 2)
                        * ((-&b__ * x_ / &a__).log()
                            - (-&determinant * x_ / (&a__ * &cx)).log()
                            + (&determinant / (&b__ * &cx)).log())
                        * ratio.log().pow(2)),
                    x_,
                ) - rubi_simp(
                    &((Atom::num(1) / 2)
                        * ((-&b__ * x_ / &a__).log()
                            - (-&d__ * x_ / &c__).log())
                        * (ax.log() + ratio.log()).pow(2)),
                    x_,
                ) + rubi_simp(&((cx.log() - ratio.log()) * bx.polylog(2)), x_)
                    + rubi_simp(&((ax.log() + ratio.log()) * dx.polylog(2)), x_)
                    + rubi_simp(&(ratio.log() * cross_c.polylog(2)), x_)
                    - rubi_simp(&(ratio.log() * cross_d.polylog(2)), x_)
                    - rubi_simp(&bx.polylog(3), x_)
                    - rubi_simp(&dx.polylog(3), x_)
                    + rubi_simp(&cross_c.polylog(3), x_)
                    - rubi_simp(&cross_d.polylog(3), x_)
        },
    ));
}

fn push_rules_rule_2886(rules: &mut Vec<RubiRule>) {
    rubi_symb!(v__, w__, x_);
    rules.push(rubi_rule!(
        order: 2886,
        source: "Int[Log[v_]*Log[w_]/x_,x_Symbol] :=
          Int[Log[ExpandToSum[v,x]]*Log[ExpandToSum[w,x]]/x,x] /;
        LinearQ[{v,w},x] && Not[LinearMatchQ[{v,w},x]]",
        desc: "Integration by parts and ???",
        refs: [],
        pattern: Atom::var(v__).log() * Atom::var(w__).log() / x_,
        with: [v__, w__, x_],
        when: {
            rubi_linear_q_list(&[&v__, &w__], x_)
                && !rubi_linear_match_q_list(&[&v__, &w__], x_)
        },
        rhs: {
            let expanded_v = rubi_expand_to_sum(&v__, x_);
            let expanded_w = rubi_expand_to_sum(&w__, x_);
            let recursive_integrand = expanded_v.log() * expanded_w.log() / x_;

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_2887(rules: &mut Vec<RubiRule>) {
    rubi_symb!(c__, d__, e__, h__, i__, j__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 2887,
        source: "Int[Log[c_.*(d_+e_.*x_)^n_.]*Log[h_.*(i_.+j_.*x_)^m_.]/x_,x_Symbol] :=
          m \\[Star] Int[Log[i+j*x]*Log[c*(d+e*x)^n]/x,x] - (m*Log[i+j*x]-Log[h*(i+j*x)^m]) \\[Star] Int[Log[c*(d+e*x)^n]/x,x]/;
        FreeQ[{c,d,e,h,i,j,m,n},x] && NeQ[e*i-d*j,0] && NeQ[i+j*x,h*(i+j*x)^m]",
        desc: "Algebraic expansion and piecewise constant extraction",
        refs: [],
        pattern: (c__ * (d__ + e__ * x_).pow(n_)).log()
            * (h__ * (i__ + j__ * x_).pow(m_)).log()
            / x_,
        with: [c__, d__, e__, n_, h__, i__, j__, m_, x_],
        optional: [c__, e__, n_, h__, i__, j__, m_],
        when: {
            freeq!([c__, d__, e__, h__, i__, j__, m_, n_], x_)
                && neq!(&e__ * &i__ - &d__ * &j__, 0)
                && neq!(
                    &i__ + &j__ * x_,
                    &h__ * (&i__ + &j__ * x_).pow(&m_)
                )
        },
        rhs: {
            let first_logarithm = (&c__ * (&d__ + &e__ * x_).pow(&n_)).log();
            let second_affine_logarithm = (&i__ + &j__ * x_).log();
            let second_logarithm = (&h__ * (&i__ + &j__ * x_).pow(&m_)).log();
            let first_recursive = rubi_rhs_int(
                &(&second_affine_logarithm * &first_logarithm / x_),
                x_,
            );
            let second_recursive = rubi_rhs_int(&(&first_logarithm / x_), x_);

            rubi_star(&m_, first_recursive)
                    - rubi_star(&m_ * second_affine_logarithm - second_logarithm, second_recursive)
        },
    ));
}

fn push_rules_rule_2888(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, h__, i__, j__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 2888,
        source: "Int[(a_.+b_.*Log[c_.*(d_+e_.*x_)^n_.])*(f_+g_.*Log[h_.*(i_.+j_.*x_)^m_.])/x_,x_Symbol] :=
          f \\[Star] Int[(a+b*Log[c*(d+e*x)^n])/x,x] + g \\[Star] Int[Log[h*(i+j*x)^m]*(a+b*Log[c*(d+e*x)^n])/x,x]/;
        FreeQ[{a,b,c,d,e,f,g,h,i,j,m,n},x] && NeQ[e*i-d*j,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, e__, n_, f__, g__, h__, i__, j__, m_, x_],
        optional: [a__, b__, c__, e__, n_, g__, h__, i__, j__, m_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__, i__, j__, m_, n_], x_)
                && neq!(&e__ * &i__ - &d__ * &j__, 0)
        },
        rhs: {
            let first_logarithmic =
                &a__ + &b__ * (&c__ * (&d__ + &e__ * x_).pow(&n_)).log();
            let second_log = (&h__ * (&i__ + &j__ * x_).pow(&m_)).log();
            let first_recursive_integrand = &first_logarithmic / x_;
            let second_recursive_integrand = second_log * &first_logarithmic / x_;
            let first_recursive_primitive = rubi_rhs_int(&first_recursive_integrand, x_);
            let second_recursive_primitive = rubi_rhs_int(&second_recursive_integrand, x_);

            rubi_star(f__, first_recursive_primitive)
                    + rubi_star(g__, second_recursive_primitive)
        },
    ));
}

fn push_rules_rule_2889(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        a__, b__, c__, d__, e__, f__, g__, h__, i__, j__, m_, n_, p_, r_, x_
    );
    rules.push(rubi_rule!(
        order: 2889,
        source: "Int[x_^r_.*(a_.+b_.*Log[c_.*(d_+e_.*x_)^n_.])^p_.*(f_.+g_.*Log[h_.*(i_.+j_.*x_)^m_.]),x_Symbol] :=
          x^(r+1)*(a+b*Log[c*(d+e*x)^n])^p*(f+g*Log[h*(i+j*x)^m])/(r+1) -
          g*j*m/(r+1) \\[Star] Int[x^(r+1)*(a+b*Log[c*(d+e*x)^n])^p/(i+j*x),x] -
          b*e*n*p/(r+1) \\[Star] Int[x^(r+1)*(a+b*Log[c*(d+e*x)^n])^(p-1)*(f+g*Log[h*(i+j*x)^m])/(d+e*x),x] /;
        FreeQ[{a,b,c,d,e,f,g,h,i,j,m,n},x] && IGtQ[p,0] && IntegerQ[r] && (EqQ[p,1] || GtQ[r,0]) && NeQ[r,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern: x_.pow(r_)
            * (a__ + b__ * (c__ * (d__ + e__ * x_).pow(n_)).log()).pow(p_)
            * (f__ + g__ * (h__ * (i__ + j__ * x_).pow(m_)).log()),
        with: [r_, a__, b__, c__, d__, e__, n_, p_, f__, g__, h__, i__, j__, m_, x_],
        optional: [r_, a__, b__, c__, e__, n_, p_, f__, g__, h__, i__, j__, m_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__, i__, j__, m_, n_], x_)
                && igtq!(p_, 0)
                && integerq!(r_)
                && (eqq!(p_, 1) || gtq!(r_, 0))
                && neq!(r_, -1)
        },
        rhs: {
            let r_plus_one = &r_ + 1;
            let first_affine = &d__ + &e__ * x_;
            let second_affine = &i__ + &j__ * x_;
            let first_logarithmic = &a__ + &b__ * (&c__ * first_affine.pow(&n_)).log();
            let second_logarithmic = &f__ + &g__ * (&h__ * second_affine.pow(&m_)).log();
            let x_power = x_.pow(&r_plus_one);
            let first_recursive_integrand = &x_power * first_logarithmic.pow(&p_) / &second_affine;
            let second_recursive_integrand =
                &x_power * first_logarithmic.pow(&p_ - 1) * &second_logarithmic / &first_affine;
            let first_recursive_primitive = rubi_rhs_int(&first_recursive_integrand, x_);
            let second_recursive_primitive = rubi_rhs_int(&second_recursive_integrand, x_);

            rubi_simp(
                    &(&x_power * first_logarithmic.pow(&p_) * second_logarithmic
                        / &r_plus_one),
                    x_,
                ) - rubi_star(&g__ * &j__ * &m_ / &r_plus_one, first_recursive_primitive) - rubi_star(&b__ * &e__ * &n_ * &p_ / r_plus_one, second_recursive_primitive)
        },
    ));
}

fn push_rules_rule_2890(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        a__, b__, c__, d__, e__, f__, g__, h__, i__, j__, k__, l__, m_, n_, r_, x_
    );
    rules.push(rubi_rule!(
        order: 2890,
        source: "Int[(k_+l_.*x_)^r_.*(a_.+b_.*Log[c_.*(d_+e_.*x_)^n_.])*(f_.+g_.*Log[h_.*(i_.+j_.*x_)^m_.]),x_Symbol] :=
          1/l \\[Star] Subst[Int[x^r*(a+b*Log[c*(-(e*k-d*l)/l+e*x/l)^n])*(f+g*Log[h*(-(j*k-i*l)/l+j*x/l)^m]),x],x,k+l*x]/;
        FreeQ[{a,b,c,d,e,f,g,h,i,j,k,l,m,n},x] && IntegerQ[r]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (k__ + l__ * x_).pow(r_)
            * (a__ + b__ * (c__ * (d__ + e__ * x_).pow(n_)).log())
            * (f__ + g__ * (h__ * (i__ + j__ * x_).pow(m_)).log()),
        with: [k__, l__, r_, a__, b__, c__, d__, e__, n_, f__, g__, h__, i__, j__, m_, x_],
        optional: [l__, r_, a__, b__, c__, e__, n_, f__, g__, h__, i__, j__, m_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__, i__, j__], x_)
                && freeq!([k__, l__, m_, n_], x_)
                && integerq!(r_)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let first_affine =
                -(&e__ * &k__ - &d__ * &l__) / &l__ + &e__ * &sub_atom / &l__;
            let second_affine =
                -(&j__ * &k__ - &i__ * &l__) / &l__ + &j__ * &sub_atom / &l__;
            let transformed_integrand = sub_atom.pow(&r_)
                * (&a__ + &b__ * (&c__ * first_affine.pow(&n_)).log())
                * (&f__ + &g__ * (&h__ * second_affine.pow(&m_)).log());
            let transformed_primitive = rubi_rhs_int(&transformed_integrand, substitution_symbol);
            let substitution = &k__ + &l__ * x_;

            rubi_star(Atom::num(1) / &l__, rubi_subst(&transformed_primitive, substitution_symbol, substitution))
        },
    ));
}

fn push_rules_rule_2891(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        a__, b__, c__, d__, e__, f__, g__, h__, i__, j__, k__, l__, m_, n_, p_, q_, r_, x_
    );
    rules.push(rubi_rule!(
        order: 2891,
        source: "Int[(k_.+l_.*x_)^r_.*(a_.+b_.*Log[c_.*(d_+e_.*x_)^n_.])^p_.*(f_.+g_.*Log[h_.*(i_.+j_.*x_)^m_.])^q_.,x_Symbol] :=
          Unintegrable[(k+l*x)^r*(a+b*Log[c*(d+e*x)^n])^p*(f+g*Log[h*(i+j*x)^m])^q,x] /;
        FreeQ[{a,b,c,d,e,f,g,h,i,j,k,l,m,n,p,q,r},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern: (k__ + l__ * x_).pow(r_)
            * (a__ + b__ * (c__ * (d__ + e__ * x_).pow(n_)).log()).pow(p_)
            * (f__ + g__ * (h__ * (i__ + j__ * x_).pow(m_)).log()).pow(q_),
        with: [k__, l__, r_, a__, b__, c__, d__, e__, n_, p_, f__, g__, h__, i__, j__, m_, q_, x_],
        optional: [k__, l__, r_, a__, b__, c__, e__, n_, p_, f__, g__, h__, i__, j__, m_, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__, i__, j__], x_)
                && freeq!([k__, l__, m_, n_, p_, q_, r_], x_)
        },
        rhs: {
            let integrand = (&k__ + &l__ * x_).pow(&r_)
                * (&a__ + &b__ * (&c__ * (&d__ + &e__ * x_).pow(&n_)).log()).pow(&p_)
                * (&f__ + &g__ * (&h__ * (&i__ + &j__ * x_).pow(&m_)).log()).pow(&q_);

            rubi_unintegrable(integrand, x_)
        },
    ));
}

fn push_rules_rule_2892(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, h__, i__, k_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 2892,
        source: "Int[PolyLog[k_,h_+i_.*x_]*(a_.+b_.*Log[c_.*(d_+e_.*x_)^n_.])^p_./(f_+g_.*x_),x_Symbol] :=
          1/g \\[Star] Subst[Int[PolyLog[k,h*x/d]*(a+b*Log[c*x^n])^p/x,x],x,d+e*x] /;
        FreeQ[{a,b,c,d,e,f,g,h,i,k,n},x] && EqQ[e*f-d*g,0] && EqQ[g*h-f*i,0] && IGtQ[p,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (h__ + i__ * x_).polylog(k_)
            * (a__ + b__ * (c__ * (d__ + e__ * x_).pow(n_)).log()).pow(p_)
            / (f__ + g__ * x_),
        with: [k_, h__, i__, a__, b__, c__, d__, e__, n_, p_, f__, g__, x_],
        optional: [i__, a__, b__, c__, e__, n_, p_, g__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__, i__, n_], x_)
                && is_free_of(&k_, x_)
                && eqq!(&e__ * &f__ - &d__ * &g__, 0)
                && eqq!(&g__ * &h__ - &f__ * &i__, 0)
                && igtq!(p_, 0)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let transformed_integrand = (&h__ * &sub_atom / &d__).polylog(&k_)
                * (&a__ + &b__ * (&c__ * sub_atom.pow(&n_)).log()).pow(&p_)
                / &sub_atom;
            let transformed_primitive = rubi_rhs_int(&transformed_integrand, substitution_symbol);
            let substitution = &d__ + &e__ * x_;

            rubi_star(Atom::num(1) / &g__, rubi_subst(&transformed_primitive, substitution_symbol, substitution))
        },
    ));
}

fn push_rules_rule_2893(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        capital_f_, a__, b__, c__, d__, e__, f__, g__, h__, n_, px__, x_
    );
    rules.push(rubi_rule!(
        order: 2893,
        source: "Int[Px_.*F_[f_.*(g_.+h_.*x_)]*(a_.+b_.*Log[c_.*(d_+e_.*x_)^n_.]),x_Symbol] :=
          With[{u=IntHide[Px*F[f*(g+h*x)],x]},
          (a+b*Log[c*(d+e*x)^n]) \\[Star] u - b*e*n \\[Star] Int[SimplifyIntegrand[u/(d+e*x),x],x]] /;
        FreeQ[{a,b,c,d,e,f,g,h,n},x] && PolynomialQ[Px,x] &&
          MemberQ[{ArcSin, ArcCos, ArcTan, ArcCot, ArcSinh, ArcCosh, ArcTanh, ArcCoth},F]",
        desc: "Integration by parts",
        refs: [],
        pattern: px__ * capital_f_.call(f__ * (g__ + h__ * x_))
            * (a__ + b__ * (c__ * (d__ + e__ * x_).pow(n_)).log()),
        with: [px__, capital_f_, f__, g__, h__, a__, b__, c__, d__, e__, n_, x_],
        optional: [px__, f__, g__, h__, a__, b__, c__, e__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__, n_], x_)
                && rubi_polynomial_q(&px__, x_)
                && rubi_function_head_member_q(
                    &capital_f_,
                    &[
                        symbol!("asin"),
                        symbol!("acos"),
                        symbol!("atan"),
                        symbol!("acot"),
                        symbol!("asinh"),
                        symbol!("acosh"),
                        symbol!("atanh"),
                        symbol!("acoth"),
                    ],
                )
        },
        rhs: {
            let inverse =
                rubi_function_head_symbol(&capital_f_).rubi_rhs().call(&f__ * (&g__ + &h__ * x_));
            let hidden_integrand = &px__ * inverse;
            let u = rubi_int_hide(&hidden_integrand, x_).rubi_rhs();
            let logarithmic = &a__ + &b__ * (&c__ * (&d__ + &e__ * x_).pow(&n_)).log();
            let recursive_integrand =
                rubi_simplify_integrand(&(&u / (&d__ + &e__ * x_)), x_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(logarithmic, u)
                    - rubi_star(&b__ * &e__ * &n_, recursive)
        },
    ));
}

fn push_rules_rule_2894(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, n_, p_, u__, v__);
    let rule = rubi_rule!(
        order: 2894,
        source: "Int[u_.*(a_.+b_.*Log[c_.*v_^n_.])^p_.,x_Symbol] :=
          Int[u*(a+b*Log[c*ExpandToSum[v,x]^n])^p,x] /;
        FreeQ[{a,b,c,n,p},x] && LinearQ[v,x] && Not[LinearMatchQ[v,x]] && Not[EqQ[n,1] && MatchQ[c*v,e_.*(f_+g_.*x) /; FreeQ[{e,f,g},x]]]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: u__ * (a__ + b__ * (c__ * v__.pow(n_)).log()).pow(p_),
        with: [u__, a__, b__, c__, v__, n_, p_, x_],
        optional: [u__, a__, b__, c__, n_, p_],
        when: {
            freeq!([a__, b__, c__, n_, p_], x_)
                && rubi_linear_q(&v__, x_)
                && !rubi_linear_match_q(&v__, x_)
                && !(eqq!(n_, 1) && rubi_match_optional_multiplier_linear_q(&(&c__ * &v__), x_))
        },
        rhs: {
            let expanded_v = rubi_expand_to_sum(&v__, x_);
            let recursive_integrand =
                &u__ * (&a__ + &b__ * (&c__ * expanded_v.pow(&n_)).log()).pow(&p_);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    );
    rules.push(rule.with_early_x_dependent(v__));
}

fn push_rules_rule_2895(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, n_, p_, u__, x_);
    rules.push(rubi_rule!(
        order: 2895,
        source: "Int[u_.*(a_.+b_.*Log[c_.*(d_.*(e_.+f_. x_)^m_.)^n_])^p_.,x_Symbol] :=
          Subst[Int[u*(a+b*Log[c*d^n*(e+f*x)^(m*n)])^p,x],c*d^n*(e+f*x)^(m*n),c*(d*(e+f*x)^m)^n] /;
        FreeQ[{a,b,c,d,e,f,m,n,p},x] && Not[IntegerQ[n]] && Not[EqQ[d,1] && EqQ[m,1]] &&
          IntegralFreeQ[IntHide[u*(a+b*Log[c*d^n*(e+f*x)^(m*n)])^p,x]]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern: u__
            * (a__ + b__ * (c__ * (d__ * (e__ + f__ * x_).pow(m_)).pow(n_)).log()).pow(p_),
        with: [u__, a__, b__, c__, d__, e__, f__, m_, n_, p_, x_],
        optional: [u__, a__, b__, c__, d__, e__, f__, m_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_, p_], x_)
                && !integerq!(n_)
                && !(eqq!(d__, 1) && eqq!(m_, 1))
                && {
                    let hidden_integrand = &u__
                        * (&a__
                            + &b__
                                * (&c__
                                    * d__.pow(&n_)
                                    * (&e__ + &f__ * x_).pow(&m_ * &n_))
                                .log())
                        .pow(&p_);
                    rubi_int_hide(&hidden_integrand, x_)
                        .is_some_and(|u| rubi_integral_free_q(&u))
                }
        },
        rhs: {
            let transformed_integrand = &u__
                * (&a__
                    + &b__
                        * (&c__ * d__.pow(&n_) * (&e__ + &f__ * x_).pow(&m_ * &n_))
                            .log())
                .pow(&p_);
            let transformed_primitive = rubi_rhs_int(&transformed_integrand, x_);
            let target = &c__ * d__.pow(&n_) * (&e__ + &f__ * x_).pow(&m_ * &n_);
            let replacement = &c__ * (&d__ * (&e__ + &f__ * x_).pow(&m_)).pow(&n_);

            rubi_subst_expression(&transformed_primitive, &target, replacement)
        },
    ));
}

fn push_rules_rule_2896(rules: &mut Vec<RubiRule>) {
    rubi_symb!(afx__, a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 2896,
        source: "Int[AFx_*(a_.+b_.*Log[c_.*(d_.*(e_.+f_. x_)^m_.)^n_])^p_.,x_Symbol] :=
          Unintegrable[AFx*(a+b*Log[c*(d*(e+f*x)^m)^n])^p,x] /;
        FreeQ[{a,b,c,d,e,f,m,n,p},x] && AlgebraicFunctionQ[AFx,x,True]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern: afx__
            * (a__ + b__ * (c__ * (d__ * (e__ + f__ * x_).pow(m_)).pow(n_)).log()).pow(p_),
        with: [afx__, a__, b__, c__, d__, e__, f__, m_, n_, p_, x_],
        optional: [a__, b__, c__, d__, e__, f__, m_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_, p_], x_)
                && rubi_algebraic_function_q(&afx__, x_, true)
        },
        rhs: {
            let integrand = &afx__
                * (&a__
                    + &b__
                        * (&c__ * (&d__ * (&e__ + &f__ * x_).pow(&m_)).pow(&n_)).log())
                .pow(&p_);

            rubi_unintegrable(integrand, x_)
        },
    ));
}

// Generated shared pattern builders.

#[inline(never)]
fn rubi_shared_pattern_0(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let g__ = symbols.g__;
    let h__ = symbols.h__;
    let i__ = symbols.i__;
    let j__ = symbols.j__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    (a__ + b__ * (c__ * (d__ + e__ * x_).pow(n_)).log())
        * (f__ + g__ * (h__ * (i__ + j__ * x_).pow(m_)).log())
        / x_
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f1__ = symbols.f1__;
    let f2__ = symbols.f2__;
    let g1__ = symbols.g1__;
    let g2__ = symbols.g2__;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    (a__ + b__ * (c__ * (d__ + e__ * x_).pow(n_)).log())
        / ((f1__ + g1__ * x_).sqrt() * (f2__ + g2__ * x_).sqrt())
}

#[inline(never)]
fn rubi_shared_pattern_2(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let g__ = symbols.g__;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    (a__ + b__ * (c__ * (d__ + e__ * x_).pow(n_)).log()) / (f__ + g__ * x_.pow(2)).sqrt()
}

#[inline(never)]
fn rubi_shared_pattern_3(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (f__ * x_.pow(m_)).log() * (a__ + b__ * (c__ * (d__ + e__ * x_).pow(n_)).log()).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_4(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let g__ = symbols.g__;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let q_ = symbols.q_;
    let x_ = symbols.x_;
    (f__ + g__ * x_).pow(q_) * (a__ + b__ * (c__ * (d__ + e__ * x_).pow(n_)).log()).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_5(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let g__ = symbols.g__;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let q_ = symbols.q_;
    let r_ = symbols.r_;
    let x_ = symbols.x_;
    (f__ + g__ * x_.pow(r_)).pow(q_) * (a__ + b__ * (c__ * (d__ + e__ * x_).pow(n_)).log()).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_6(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let g__ = symbols.g__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let q_ = symbols.q_;
    let x_ = symbols.x_;
    (g__ * x_).pow(q_)
        * (f__ * x_.pow(m_)).log()
        * (a__ + b__ * (c__ * (d__ + e__ * x_).pow(n_)).log()).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_7(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let rfx__ = symbols.rfx__;
    let x_ = symbols.x_;
    rfx__ * (a__ + b__ * (c__ * (d__ + e__ * x_).pow(n_)).log()).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_8(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let g__ = symbols.g__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let q_ = symbols.q_;
    let r_ = symbols.r_;
    let x_ = symbols.x_;
    x_.pow(m_)
        * (f__ + g__ * x_.pow(r_)).pow(q_)
        * (a__ + b__ * (c__ * (d__ + e__ * x_).pow(n_)).log()).pow(p_)
}
