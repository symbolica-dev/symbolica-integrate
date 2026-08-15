use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_2897(rules);
    push_rules_rule_2898(rules);
    push_rules_rule_2899(rules);
    push_rules_rule_2900(rules);
    push_rules_rule_2901(rules);
    push_rules_rule_2902(rules);
    push_rules_rule_2903(rules);
    push_rules_rule_2904(rules);
    push_rules_rule_2905(rules);
    push_rules_rule_2906(rules);
    push_rules_rule_2907(rules);
    push_rules_rule_2908(rules);
    push_rules_rule_2909(rules);
    push_rules_rule_2910(rules);
    push_rules_rule_2911(rules);
    push_rules_rule_2912(rules);
    push_rules_rule_2913(rules);
    push_rules_rule_2914(rules);
    push_rules_rule_2915(rules);
    push_rules_rule_2916(rules);
    push_rules_rule_2917(rules);
    push_rules_rule_2918(rules);
    push_rules_rule_2919(rules);
    push_rules_rule_2920(rules);
    push_rules_rule_2921(rules);
    push_rules_rule_2922(rules);
    push_rules_rule_2923(rules);
    push_rules_rule_2924(rules);
    push_rules_rule_2925(rules);
    push_rules_rule_2926(rules);
    push_rules_rule_2927(rules);
    push_rules_rule_2928(rules);
    push_rules_rule_2929(rules);
    push_rules_rule_2930(rules);
    push_rules_rule_2931(rules);
    push_rules_rule_2932(rules);
    push_rules_rule_2933(rules);
    push_rules_rule_2934(rules);
}

fn push_rules_rule_2897(rules: &mut Vec<RubiRule>) {
    rubi_symb!(m_, pq_, u__);
    rules.push(rubi_rule!(
        order: 2897,
        source: "Int[Pq_^m_.*Log[u_],x_Symbol] :=
          With[{C=FullSimplify[Pq^m*(1-u)/D[u,x]]},
          C*PolyLog[2,1-u] /;
         FreeQ[C,x]] /;
        IntegerQ[m] && PolyQ[Pq,x] && RationalFunctionQ[u,x] && LeQ[RationalFunctionExponents[u,x][[2]],Expon[Pq,x]]",
        desc: "Integration by substitution",
        refs: [],
        pattern: pq_.pow(m_) * Atom::var(u__).log(),
        with: [pq_, m_, u__, x_],
        optional: [m_],
        when: {
            integerq!(m_)
                && rubi_poly_q(&pq_, x_)
                && rubi_rational_function_q(&u__, x_)
                && rubi_rational_function_exponents(&u__, x_)
                    .is_some_and(|(_, denominator_exponent)| {
                        rubi_expon(&pq_, x_).is_some_and(|pq_exponent| {
                            leq!(Atom::num(denominator_exponent), Atom::num(pq_exponent))
                        })
                    })
                && {
                    let du = u__.derivative(x_);
                    let C = rubi_full_simplify(&(pq_.pow(&m_) * (Atom::num(1) - &u__) / du));
                    freeq!(C, x_)
                }
        },
        rhs: {
            let du = u__.derivative(x_);
            let C = rubi_full_simplify(&(pq_.pow(&m_) * (Atom::num(1) - &u__) / du));

            rubi_simp(&(C * (Atom::num(1) - &u__).polylog(2)), x_)
        },
    ));
}

fn push_rules_rule_2898(rules: &mut Vec<RubiRule>) {
    rubi_symb!(n_, p_, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 2898,
        source: "Int[Log[c_.*(d_+e_.*x_^n_)^p_.],x_Symbol] :=
          x*Log[c*(d+e*x^n)^p] - e*n*p \\[Star] Int[x^n/(d+e*x^n),x] /;
        FreeQ[{c,d,e,n,p},x]",
        desc: "Integration by parts",
        refs: [],
        pattern: (c__ * (d__ + e__ * x_.pow(n_)).pow(p_)).log(),
        with: [c__, d__, e__, n_, p_, x_],
        optional: [c__, e__, p_],
        when: { freeq!([c__, d__, e__, n_, p_], x_) },
        rhs: {
            let logarithmic = (&c__ * (&d__ + &e__ * x_.pow(&n_)).pow(&p_)).log();
            let recursive_integrand = x_.pow(&n_) / (&d__ + &e__ * x_.pow(&n_));
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(x_ * logarithmic), x_)
                    - rubi_star(&e__ * &n_ * &p_, recursive)
        },
    ));
}

fn push_rules_rule_2899(rules: &mut Vec<RubiRule>) {
    rubi_symb!(p_, q_, a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 2899,
        source: "Int[(a_.+b_.*Log[c_.*(d_+e_./x_)^p_.])^q_,x_Symbol] :=
          (e+d*x)*(a+b*Log[c*(d+e/x)^p])^q/d + b*e*p*q/d \\[Star] Int[(a+b*Log[c*(d+e/x)^p])^(q-1)/x,x] /;
        FreeQ[{a,b,c,d,e,p},x] && IGtQ[q,0]",
        desc: "Integration by parts",
        refs: [],
        pattern: (a__ + b__ * (c__ * (d__ + e__ / x_).pow(p_)).log()).pow(q_),
        with: [a__, b__, c__, d__, e__, p_, q_, x_],
        optional: [a__, b__, c__, e__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, p_], x_)
                && igtq!(q_, 0)
        },
        rhs: {
            let logarithmic = &a__ + &b__ * (&c__ * (&d__ + &e__ / x_).pow(&p_)).log();
            let recursive_integrand = logarithmic.pow(&q_ - 1) / x_;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(
                    &((&e__ + &d__ * x_) * logarithmic.pow(&q_) / &d__),
                    x_,
                ) + rubi_star(&b__ * &e__ * &p_ * &q_ / &d__, recursive)
        },
    ));
}

fn push_rules_rule_2900(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; n_, p_, q_, a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 2900,
        source: "Int[(a_.+b_.*Log[c_.*(d_+e_.*x_^n_)^p_.])^q_,x_Symbol] :=
          x*(a+b*Log[c*(d+e*x^n)^p])^q - b*e*n*p*q \\[Star] Int[x^n*(a+b*Log[c*(d+e*x^n)^p])^(q-1)/(d+e*x^n),x] /;
        FreeQ[{a,b,c,d,e,n,p},x] && IGtQ[q,0] && (EqQ[q,1] || IntegerQ[n])",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, e__, n_, p_, q_, x_],
        optional: [a__, b__, c__, e__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, n_, p_], x_)
                && igtq!(q_, 0)
                && (eqq!(q_, 1) || integerq!(n_))
        },
        rhs: {
            let logarithmic =
                &a__ + &b__ * (&c__ * (&d__ + &e__ * x_.pow(&n_)).pow(&p_)).log();
            let recursive_integrand =
                x_.pow(&n_) * logarithmic.pow(&q_ - 1) / (&d__ + &e__ * x_.pow(&n_));
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(x_ * logarithmic.pow(&q_)), x_)
                    - rubi_star(&b__ * &e__ * &n_ * &p_ * &q_, recursive)
        },
    ));
}

fn push_rules_rule_2901(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; n_, p_, q_, a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 2901,
        source: "Int[(a_.+b_.*Log[c_.*(d_+e_.*x_^n_)^p_.])^q_,x_Symbol] :=
          With[{k=Denominator[n]},
          k \\[Star] Subst[Int[x^(k-1)*(a+b*Log[c*(d+e*x^(k*n))^p])^q,x],x,x^(1/k)]] /;
        FreeQ[{a,b,c,d,e,p,q},x] && FractionQ[n]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, e__, n_, p_, q_, x_],
        optional: [a__, b__, c__, e__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, p_, q_], x_) && fractionq!(n_)
        },
        rhs: {
            let k_i = rubi_denominator(&n_).expect("FractionQ guard ensures a denominator");
            let k = Atom::num(k_i);
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let transformed_integrand = sub_atom.pow(&k - 1)
                * (&a__
                    + &b__
                        * (&c__ * (&d__ + &e__ * sub_atom.pow(&k * &n_)).pow(&p_)).log())
                .pow(&q_);
            let transformed_primitive = rubi_rhs_int(&transformed_integrand, substitution_symbol);
            let substitution = x_.pow(Atom::num(1) / &k);

            rubi_star(k, rubi_subst(&transformed_primitive, substitution_symbol, substitution))
        },
    ));
}

fn push_rules_rule_2902(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; n_, p_, q_, a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 2902,
        source: "Int[(a_.+b_.*Log[c_.*(d_+e_.*x_^n_)^p_.])^q_,x_Symbol] :=
          Unintegrable[(a+b*Log[c*(d+e*x^n)^p])^q,x] /;
        FreeQ[{a,b,c,d,e,n,p,q},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, e__, n_, p_, q_, x_],
        optional: [a__, b__, c__, e__, p_],
        when: { freeq!([a__, b__, c__, d__, e__, n_, p_, q_], x_) },
        rhs: {
            let integrand =
                (&a__ + &b__ * (&c__ * (&d__ + &e__ * x_.pow(&n_)).pow(&p_)).log()).pow(&q_);

            rubi_unintegrable(integrand, x_)
        },
    ));
}

fn push_rules_rule_2903(rules: &mut Vec<RubiRule>) {
    rubi_symb!(p_, q_, a__, b__, c__, v__);
    let rule = rubi_rule!(
        order: 2903,
        source: "Int[(a_.+b_.*Log[c_.*v_^p_.])^q_.,x_Symbol] :=
          Int[(a+b*Log[c*ExpandToSum[v,x]^p])^q,x] /;
        FreeQ[{a,b,c,p,q},x] && BinomialQ[v,x] && Not[BinomialMatchQ[v,x]]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: (a__ + b__ * (c__ * v__.pow(p_)).log()).pow(q_),
        with: [a__, b__, c__, v__, p_, q_, x_],
        optional: [a__, b__, c__, p_, q_],
        when: {
            freeq!([a__, b__, c__, p_, q_], x_)
                && rubi_binomial_q(&v__, x_)
                && !rubi_binomial_match_q(&v__, x_)
        },
        rhs: {
            let expanded_v = rubi_expand_to_sum(&v__, x_);
            let recursive_integrand =
                (&a__ + &b__ * (&c__ * expanded_v.pow(&p_)).log()).pow(&q_);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    );
    rules.push(rule.with_early_x_dependent(v__));
}

fn push_rules_rule_2904(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; m_, n_, p_, q_, a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 2904,
        source: "Int[x_^m_.*(a_.+b_.*Log[c_.*(d_+e_.*x_^n_)^p_.])^q_.,x_Symbol] :=
          1/n \\[Star] Subst[Int[x^(Simplify[(m+1)/n]-1)*(a+b*Log[c*(d+e*x)^p])^q,x],x,x^n] /;
        FreeQ[{a,b,c,d,e,m,n,p,q},x] && IntegerQ[Simplify[(m+1)/n]] && (GtQ[(m+1)/n,0] || IGtQ[q,0]) && Not[EqQ[q,1] && ILtQ[n,0] && IGtQ[m,0]]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [m_, a__, b__, c__, d__, e__, n_, p_, q_, x_],
        optional: [m_, a__, b__, c__, e__, p_, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_, p_, q_], x_)
                && {
                    let s = rubi_simplify(&((&m_ + 1) / &n_));
                    integerq!(s)
                        && (gtq!((&m_ + 1) / &n_, 0) || igtq!(q_, 0))
                        && !(eqq!(q_, 1) && iltq!(n_, 0) && igtq!(m_, 0))
                }
        },
        rhs: {
            let s = rubi_simplify(&((&m_ + 1) / &n_));
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let transformed_integrand = sub_atom.pow(&s - 1)
                * (&a__ + &b__ * (&c__ * (&d__ + &e__ * &sub_atom).pow(&p_)).log()).pow(&q_);
            let transformed_primitive = rubi_rhs_int(&transformed_integrand, substitution_symbol);
            let substitution = x_.pow(&n_);
            let substituted = rubi_subst(&transformed_primitive, substitution_symbol, substitution);

            rubi_star(Atom::num(1) / &n_, substituted)
        },
    ));
}

fn push_rules_rule_2905(rules: &mut Vec<RubiRule>) {
    rubi_symb!(m_, n_, p_, a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 2905,
        source: "Int[(f_.*x_)^m_.*(a_.+b_.*Log[c_.*(d_+e_.*x_^n_)^p_.]),x_Symbol] :=
          (f*x)^(m+1)*(a+b*Log[c*(d+e*x^n)^p])/(f*(m+1)) -
          b*e*n*p/(f*(m+1)) \\[Star] Int[x^(n-1)*(f*x)^(m+1)/(d+e*x^n),x] /;
        FreeQ[{a,b,c,d,e,f,m,n,p},x] && NeQ[m,-1]",
        desc: "Integration by parts and piecewise constant extraction",
        refs: ["G&R 2.728.1, CRC 501, A&S 4.1.50'"],
        pattern: (f__ * x_).pow(m_) * (a__ + b__ * (c__ * (d__ + e__ * x_.pow(n_)).pow(p_)).log()),
        with: [f__, m_, a__, b__, c__, d__, e__, n_, p_, x_],
        optional: [f__, m_, a__, b__, c__, e__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_, p_], x_)
                && neq!(m_, -1)
        },
        rhs: {
            let logarithmic = &a__ + &b__ * (&c__ * (&d__ + &e__ * x_.pow(&n_)).pow(&p_)).log();
            let denominator = &f__ * (&m_ + 1);
            let recursive_integrand =
                x_.pow(&n_ - 1) * (&f__ * x_).pow(&m_ + 1)
                    / (&d__ + &e__ * x_.pow(&n_));
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(
                    &((&f__ * x_).pow(&m_ + 1) * logarithmic / &denominator),
                    x_,
                ) - rubi_star(&b__ * &e__ * &n_ * &p_ / denominator, recursive)
        },
    ));
}

fn push_rules_rule_2906(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; m_, n_, p_, q_, a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 2906,
        source: "Int[(f_*x_)^m_*(a_.+b_.*Log[c_.*(d_+e_.*x_^n_)^p_.])^q_.,x_Symbol] :=
          (f*x)^m/x^m \\[Star] Int[x^m*(a+b*Log[c*(d+e*x^n)^p])^q,x] /;
        FreeQ[{a,b,c,d,e,f,m,n,p,q},x] && IntegerQ[Simplify[(m+1)/n]] && (GtQ[(m+1)/n,0] || IGtQ[q,0])",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [f__, m_, a__, b__, c__, d__, e__, n_, p_, q_, x_],
        optional: [a__, b__, c__, e__, p_, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_, p_, q_], x_)
                && {
                    let s = rubi_simplify(&((&m_ + 1) / &n_));
                    integerq!(s) && (gtq!((&m_ + 1) / &n_, 0) || igtq!(q_, 0))
                }
        },
        rhs: {
            let logarithmic =
                &a__ + &b__ * (&c__ * (&d__ + &e__ * x_.pow(&n_)).pow(&p_)).log();
            let recursive_integrand = x_.pow(&m_) * logarithmic.pow(&q_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star((&f__ * x_).pow(&m_), recursive / x_.pow(&m_))
        },
    ));
}

fn push_rules_rule_2907(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; m_, n_, p_, q_, a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 2907,
        source: "Int[(f_.*x_)^m_.*(a_.+b_.*Log[c_.*(d_+e_.*x_^n_)^p_.])^q_,x_Symbol] :=
          (f*x)^(m+1)*(a+b*Log[c*(d+e*x^n)^p])^q/(f*(m+1)) -
          b*e*n*p*q/(f^n*(m+1)) \\[Star] Int[(f*x)^(m+n)*(a+b*Log[c*(d+e*x^n)^p])^(q-1)/(d+e*x^n),x] /;
        FreeQ[{a,b,c,d,e,f,m,p},x] && IGtQ[q,1] && IntegerQ[n] && NeQ[m,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [f__, m_, a__, b__, c__, d__, e__, n_, p_, q_, x_],
        optional: [f__, m_, a__, b__, c__, e__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, p_], x_)
                && igtq!(q_, 1)
                && integerq!(n_)
                && neq!(m_, -1)
        },
        rhs: {
            let logarithmic =
                &a__ + &b__ * (&c__ * (&d__ + &e__ * x_.pow(&n_)).pow(&p_)).log();
            let recursive_integrand = (&f__ * x_).pow(&m_ + &n_)
                * logarithmic.pow(&q_ - 1)
                / (&d__ + &e__ * x_.pow(&n_));
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(
                    &((&f__ * x_).pow(&m_ + 1) * logarithmic.pow(&q_)
                        / (&f__ * (&m_ + 1))),
                    x_,
                ) - rubi_star(&b__ * &e__ * &n_ * &p_ * &q_ / (f__.pow(&n_) * (&m_ + 1)), recursive)
        },
    ));
}

fn push_rules_rule_2908(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; m_, n_, p_, q_, a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 2908,
        source: "Int[x_^m_.*(a_.+b_.*Log[c_.*(d_+e_.*x_^n_)^p_.])^q_,x_Symbol] :=
          With[{k=Denominator[n]},
          k \\[Star] Subst[Int[x^(k*(m+1)-1)*(a+b*Log[c*(d+e*x^(k*n))^p])^q,x],x,x^(1/k)]] /;
        FreeQ[{a,b,c,d,e,m,p,q},x] && FractionQ[n]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [m_, a__, b__, c__, d__, e__, n_, p_, q_, x_],
        optional: [m_, a__, b__, c__, e__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, p_, q_], x_) && fractionq!(n_)
        },
        rhs: {
            let k_i = rubi_denominator(&n_).expect("FractionQ guard ensures a denominator");
            let k = Atom::num(k_i);
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let transformed_integrand = sub_atom.pow(&k * (&m_ + 1) - 1)
                * (&a__
                    + &b__
                        * (&c__ * (&d__ + &e__ * sub_atom.pow(&k * &n_)).pow(&p_)).log())
                .pow(&q_);
            let transformed_primitive = rubi_rhs_int(&transformed_integrand, substitution_symbol);
            let substitution = x_.pow(Atom::num(1) / &k);

            rubi_star(k, rubi_subst(&transformed_primitive, substitution_symbol, substitution))
        },
    ));
}

fn push_rules_rule_2909(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; m_, n_, p_, q_, a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 2909,
        source: "Int[(f_*x_)^m_*(a_.+b_.*Log[c_.*(d_+e_.*x_^n_)^p_.])^q_.,x_Symbol] :=
          (f*x)^m/x^m \\[Star] Int[x^m*(a+b*Log[c*(d+e*x^n)^p])^q,x] /;
        FreeQ[{a,b,c,d,e,f,m,p,q},x] && FractionQ[n]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [f__, m_, a__, b__, c__, d__, e__, n_, p_, q_, x_],
        optional: [a__, b__, c__, e__, p_, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, p_, q_], x_)
                && fractionq!(n_)
        },
        rhs: {
            let logarithmic =
                &a__ + &b__ * (&c__ * (&d__ + &e__ * x_.pow(&n_)).pow(&p_)).log();
            let recursive_integrand = x_.pow(&m_) * logarithmic.pow(&q_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star((&f__ * x_).pow(&m_), recursive / x_.pow(&m_))
        },
    ));
}

fn push_rules_rule_2910(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; m_, n_, p_, q_, a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 2910,
        source: "Int[(f_.*x_)^m_.*(a_.+b_.*Log[c_.*(d_+e_.*x_^n_)^p_.])^q_.,x_Symbol] :=
          Unintegrable[(f*x)^m*(a+b*Log[c*(d+e*x^n)^p])^q,x] /;
        FreeQ[{a,b,c,d,e,f,m,n,p,q},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [f__, m_, a__, b__, c__, d__, e__, n_, p_, q_, x_],
        optional: [f__, m_, a__, b__, c__, e__, p_, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_, p_, q_], x_)
        },
        rhs: {
            let integrand =
                (&f__ * x_).pow(&m_)
                    * (&a__ + &b__ * (&c__ * (&d__ + &e__ * x_.pow(&n_)).pow(&p_)).log())
                        .pow(&q_);

            rubi_unintegrable(integrand, x_)
        },
    ));
}

fn push_rules_rule_2911(rules: &mut Vec<RubiRule>) {
    rubi_symb!(m_, p_, q_, a__, b__, c__, f__, v__, x_);
    let rule = rubi_rule!(
        order: 2911,
        source: "Int[(f_.*x_)^m_.*(a_.+b_.*Log[c_.*v_^p_.])^q_.,x_Symbol] :=
          Int[(f*x)^m*(a+b*Log[c*ExpandToSum[v,x]^p])^q,x] /;
        FreeQ[{a,b,c,f,m,p,q},x] && BinomialQ[v,x] && Not[BinomialMatchQ[v,x]]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: (f__ * x_).pow(m_) * (a__ + b__ * (c__ * v__.pow(p_)).log()).pow(q_),
        with: [f__, m_, a__, b__, c__, v__, p_, q_, x_],
        optional: [f__, m_, a__, b__, c__, p_, q_],
        when: {
            freeq!([a__, b__, c__, f__, m_, p_, q_], x_)
                && rubi_binomial_q(&v__, x_)
                && !rubi_binomial_match_q(&v__, x_)
        },
        rhs: {
            let expanded_v = rubi_expand_to_sum(&v__, x_);
            let recursive_integrand =
                (&f__ * x_).pow(&m_)
                    * (&a__ + &b__ * (&c__ * expanded_v.pow(&p_)).log()).pow(&q_);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    );
    rules.push(rule.with_early_x_dependent(v__));
}

fn push_rules_rule_2912(rules: &mut Vec<RubiRule>) {
    rubi_symb!(n_, p_, a__, b__, c__, d__, e__, f__, g__, x_);
    rules.push(rubi_rule!(
        order: 2912,
        source: "Int[(a_.+b_.*Log[c_.*(d_+e_.*x_^n_)^p_.])/(f_.+g_.*x_),x_Symbol] :=
          Log[f+g*x]*(a+b*Log[c*(d+e*x^n)^p])/g -
          b*e*n*p/g \\[Star] Int[x^(n-1)*Log[f+g*x]/(d+e*x^n),x] /;
        FreeQ[{a,b,c,d,e,f,g,n,p},x] && RationalQ[n]",
        desc: "Integration by parts",
        refs: [],
        pattern: (a__ + b__ * (c__ * (d__ + e__ * x_.pow(n_)).pow(p_)).log()) / (f__ + g__ * x_),
        with: [a__, b__, c__, d__, e__, n_, p_, f__, g__, x_],
        optional: [a__, b__, c__, e__, p_, f__, g__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, n_, p_], x_)
                && rationalq!(n_)
        },
        rhs: {
            let affine = &f__ + &g__ * x_;
            let logarithmic =
                &a__ + &b__ * (&c__ * (&d__ + &e__ * x_.pow(&n_)).pow(&p_)).log();
            let recursive_integrand =
                x_.pow(&n_ - 1) * affine.log() / (&d__ + &e__ * x_.pow(&n_));
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(affine.log() * logarithmic / &g__), x_)
                    - rubi_star(&b__ * &e__ * &n_ * &p_ / &g__, recursive)
        },
    ));
}

fn push_rules_rule_2913(rules: &mut Vec<RubiRule>) {
    rubi_symb!(n_, p_, a__, b__, c__, d__, e__, f__, g__, x_, r_);
    rules.push(rubi_rule!(
        order: 2913,
        source: "Int[(f_.+g_.*x_)^r_.*(a_.+b_.*Log[c_.*(d_+e_.*x_^n_)^p_.]),x_Symbol] :=
          (f+g*x)^(r+1)*(a+b*Log[c*(d+e*x^n)^p])/(g*(r+1)) -
          b*e*n*p/(g*(r+1)) \\[Star] Int[x^(n-1)*(f+g*x)^(r+1)/(d+e*x^n),x] /;
        FreeQ[{a,b,c,d,e,f,g,n,p,r},x] && (IGtQ[r,0] || RationalQ[n]) && NeQ[r,-1]",
        desc: "Integration by parts",
        refs: ["G&R 2.728.1, CRC 501, A&S 4.1.50'"],
        pattern: (f__ + g__ * x_).pow(r_) * (a__ + b__ * (c__ * (d__ + e__ * x_.pow(n_)).pow(p_)).log()),
        with: [f__, g__, r_, a__, b__, c__, d__, e__, n_, p_, x_],
        optional: [f__, g__, r_, a__, b__, c__, e__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, n_, p_, r_], x_)
                && (igtq!(r_, 0) || rationalq!(n_))
                && neq!(r_, -1)
        },
        rhs: {
            let affine = &f__ + &g__ * x_;
            let logarithmic =
                &a__ + &b__ * (&c__ * (&d__ + &e__ * x_.pow(&n_)).pow(&p_)).log();
            let denominator = &g__ * (&r_ + 1);
            let recursive_integrand =
                x_.pow(&n_ - 1) * affine.pow(&r_ + 1) / (&d__ + &e__ * x_.pow(&n_));
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(affine.pow(&r_ + 1) * logarithmic / &denominator), x_)
                    - rubi_star(&b__ * &e__ * &n_ * &p_ / denominator, recursive)
        },
    ));
}

fn push_rules_rule_2914(rules: &mut Vec<RubiRule>) {
    rubi_symb!(n_, p_, q_, a__, b__, c__, d__, e__, f__, g__, x_, r_);
    rules.push(rubi_rule!(
        order: 2914,
        source: "Int[(f_.+g_.*x_)^r_.*(a_.+b_.*Log[c_.*(d_+e_.*x_^n_)^p_.])^q_.,x_Symbol] :=
          Unintegrable[(f+g*x)^r*(a+b*Log[c*(d+e*x^n)^p])^q,x] /;
        FreeQ[{a,b,c,d,e,f,g,n,p,q,r},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern: (f__ + g__ * x_).pow(r_) * (a__ + b__ * (c__ * (d__ + e__ * x_.pow(n_)).pow(p_)).log()).pow(q_),
        with: [f__, g__, r_, a__, b__, c__, d__, e__, n_, p_, q_, x_],
        optional: [f__, g__, r_, a__, b__, c__, e__, p_, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, n_, p_, q_, r_], x_)
        },
        rhs: {
            let integrand = (&f__ + &g__ * x_).pow(&r_)
                * (&a__ + &b__ * (&c__ * (&d__ + &e__ * x_.pow(&n_)).pow(&p_)).log()).pow(&q_);

            rubi_unintegrable(integrand, x_)
        },
    ));
}

fn push_rules_rule_2915(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; p_, q_, a__, b__, c__, u__, v__, r_);
    let rule = rubi_rule!(
        order: 2915,
        source: "Int[u_^r_.*(a_.+b_.*Log[c_.*v_^p_.])^q_.,x_Symbol] :=
          Int[ExpandToSum[u,x]^r*(a+b*Log[c*ExpandToSum[v,x]^p])^q,x] /;
        FreeQ[{a,b,c,p,q,r},x] && LinearQ[u,x] && BinomialQ[v,x] && Not[LinearMatchQ[u,x] && BinomialMatchQ[v,x]]",
        desc: "Algebraic normalization",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [u__, r_, a__, b__, c__, v__, p_, q_, x_],
        optional: [r_, a__, b__, c__, p_, q_],
        when: {
            freeq!([a__, b__, c__, p_, q_, r_], x_)
                && rubi_linear_q(&u__, x_)
                && rubi_binomial_q(&v__, x_)
                && !(rubi_linear_match_q(&u__, x_) && rubi_binomial_match_q(&v__, x_))
        },
        rhs: {
            let expanded_u = rubi_expand_to_sum(&u__, x_);
            let expanded_v = rubi_expand_to_sum(&v__, x_);
            let recursive_integrand =
                expanded_u.pow(&r_) * (&a__ + &b__ * (&c__ * expanded_v.pow(&p_)).log()).pow(&q_);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    );
    rules.push(rule.with_early_x_dependent(u__).with_early_x_dependent(v__));
}

fn push_rules_rule_2916(rules: &mut Vec<RubiRule>) {
    rubi_symb!(m_, n_, p_, q_, a__, b__, c__, d__, e__, f__, g__, x_, r_);
    rules.push(rubi_rule!(
        order: 2916,
        source: "Int[x_^m_.*(f_.+g_.*x_)^r_.*(a_.+b_.*Log[c_.*(d_+e_.*x_^n_)^p_.])^q_.,x_Symbol] :=
          Int[ExpandIntegrand[(a+b*Log[c*(d+e*x^n)^p])^q,x^m*(f+g*x)^r,x],x] /;
        FreeQ[{a,b,c,d,e,f,g,n,p,q},x] && IntegerQ[m] && IntegerQ[r]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: x_.pow(m_) * (f__ + g__ * x_).pow(r_) * (a__ + b__ * (c__ * (d__ + e__ * x_.pow(n_)).pow(p_)).log()).pow(q_),
        with: [m_, f__, g__, r_, a__, b__, c__, d__, e__, n_, p_, q_, x_],
        optional: [m_, f__, g__, r_, a__, b__, c__, e__, p_, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, n_, p_, q_], x_)
                && integerq!(m_)
                && integerq!(r_)
        },
        rhs: {
            let log_power =
                (&a__ + &b__ * (&c__ * (&d__ + &e__ * x_.pow(&n_)).pow(&p_)).log()).pow(&q_);
            let multiplier = x_.pow(&m_) * (&f__ + &g__ * x_).pow(&r_);
            let expanded = rubi_expand_integrand_product(&log_power, &multiplier, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_2917(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        m_, n_, p_, q_, a__, b__, c__, d__, e__, f__, g__, h__, x_, r_
    );
    rules.push(rubi_rule!(
        order: 2917,
        source: "Int[(h_.*x_)^m_*(f_.+g_.*x_)^r_.*(a_.+b_.*Log[c_.*(d_+e_.*x_^n_.)^p_.])^q_.,x_Symbol] :=
          With[{k=Denominator[m]},
          k/h \\[Star] Subst[Int[x^(k*(m+1)-1)*(f+g*x^k/h)^r*(a+b*Log[c*(d+e*x^(k*n)/h^n)^p])^q,x],x,(h*x)^(1/k)]] /;
        FreeQ[{a,b,c,d,e,f,g,h,p,r},x] && FractionQ[m] && IntegerQ[n] && IntegerQ[r]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [h__, m_, f__, g__, r_, a__, b__, c__, d__, e__, n_, p_, q_, x_],
        optional: [h__, f__, g__, r_, a__, b__, c__, e__, n_, p_, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__, p_, r_], x_)
                && fractionq!(m_)
                && integerq!(n_)
                && integerq!(r_)
        },
        rhs: {
            let k_i = rubi_denominator(&m_).expect("FractionQ guard ensures a denominator");
            let k = Atom::num(k_i);
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let transformed_integrand = sub_atom.pow(&k * (&m_ + 1) - 1)
                * (&f__ + &g__ * sub_atom.pow(&k) / &h__).pow(&r_)
                * (&a__
                    + &b__
                        * (&c__
                            * (&d__
                                + &e__ * sub_atom.pow(&k * &n_) / h__.pow(&n_))
                            .pow(&p_))
                        .log())
                .pow(&q_);
            let transformed_primitive = rubi_rhs_int(&transformed_integrand, substitution_symbol);
            let substitution = (&h__ * x_).pow(Atom::num(1) / &k);

            rubi_star(k, rubi_subst(&transformed_primitive, substitution_symbol, substitution) / &h__)
        },
    ));
}

fn push_rules_rule_2918(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        m_, n_, p_, q_, a__, b__, c__, d__, e__, f__, g__, h__, x_, r_
    );
    rules.push(rubi_rule!(
        order: 2918,
        source: "Int[(h_.*x_)^m_.*(f_.+g_.*x_)^r_.*(a_.+b_.*Log[c_.*(d_+e_.*x_^n_)^p_.])^q_.,x_Symbol] :=
          Unintegrable[(h*x)^m*(f+g*x)^r*(a+b*Log[c*(d+e*x^n)^p])^q,x] /;
        FreeQ[{a,b,c,d,e,f,g,h,m,n,p,q,r},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [h__, m_, f__, g__, r_, a__, b__, c__, d__, e__, n_, p_, q_, x_],
        optional: [h__, m_, f__, g__, r_, a__, b__, c__, e__, p_, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__, m_, n_, p_, q_, r_], x_)
        },
        rhs: {
            let integrand = (&h__ * x_).pow(&m_)
                * (&f__ + &g__ * x_).pow(&r_)
                * (&a__ + &b__ * (&c__ * (&d__ + &e__ * x_.pow(&n_)).pow(&p_)).log()).pow(&q_);

            rubi_unintegrable(integrand, x_)
        },
    ));
}

fn push_rules_rule_2919(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; m_, p_, q_, a__, b__, c__, h__, u__, v__, x_, r_);
    let rule = rubi_rule!(
        order: 2919,
        source: "Int[(h_.*x_)^m_.*u_^r_.*(a_.+b_.*Log[c_.*v_^p_.])^q_.,x_Symbol] :=
          Int[(h*x)^m*ExpandToSum[u,x]^r*(a+b*Log[c*ExpandToSum[v,x]^p])^q,x] /;
        FreeQ[{a,b,c,h,m,p,q,r},x] && LinearQ[u,x] && BinomialQ[v,x] && Not[LinearMatchQ[u,x] && BinomialMatchQ[v,x]]",
        desc: "Algebraic normalization",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [h__, m_, u__, r_, a__, b__, c__, v__, p_, q_, x_],
        optional: [h__, m_, r_, a__, b__, c__, p_, q_],
        when: {
            freeq!([a__, b__, c__, h__, m_, p_, q_, r_], x_)
                && rubi_linear_q(&u__, x_)
                && rubi_binomial_q(&v__, x_)
                && !(rubi_linear_match_q(&u__, x_) && rubi_binomial_match_q(&v__, x_))
        },
        rhs: {
            let expanded_u = rubi_expand_to_sum(&u__, x_);
            let expanded_v = rubi_expand_to_sum(&v__, x_);
            let recursive_integrand =
                (&h__ * x_).pow(&m_)
                    * expanded_u.pow(&r_)
                    * (&a__ + &b__ * (&c__ * expanded_v.pow(&p_)).log()).pow(&q_);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    );
    rules.push(rule.with_early_x_dependent(u__).with_early_x_dependent(v__));
}

fn push_rules_rule_2920(rules: &mut Vec<RubiRule>) {
    rubi_symb!(n_, p_, a__, b__, c__, d__, e__, f__, g__, x_);
    rules.push(rubi_rule!(
        order: 2920,
        source: "Int[(a_.+b_.*Log[c_.*(d_+e_.*x_^n_)^p_.])/(f_+g_.*x_^2),x_Symbol] :=
          With[{u=IntHide[1/(f+g*x^2),x]},
          u*(a+b*Log[c*(d+e*x^n)^p]) - b*e*n*p \\[Star] Int[u*x^(n-1)/(d+e*x^n),x]] /;
        FreeQ[{a,b,c,d,e,f,g,n,p},x] && IntegerQ[n]",
        desc: "Integration by parts",
        refs: [],
        pattern: (a__ + b__ * (c__ * (d__ + e__ * x_.pow(n_)).pow(p_)).log()) / (f__ + g__ * x_.pow(2)),
        with: [a__, b__, c__, d__, e__, n_, p_, f__, g__, x_],
        optional: [a__, b__, c__, e__, p_, g__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, n_, p_], x_)
                && integerq!(n_)
        },
        rhs: {
            let u = rubi_int_hide(&(Atom::num(1) / (&f__ + &g__ * x_.pow(2))), x_).rubi_rhs();
            let logarithmic =
                &a__ + &b__ * (&c__ * (&d__ + &e__ * x_.pow(&n_)).pow(&p_)).log();
            let recursive_integrand = &u * x_.pow(&n_ - 1) / (&d__ + &e__ * x_.pow(&n_));
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(u * logarithmic), x_)
                    - rubi_star(&b__ * &e__ * &n_ * &p_, recursive)
        },
    ));
}

fn push_rules_rule_2921(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; n_, p_, q_, a__, b__, c__, d__, e__, f__, g__, x_, r_, s_);
    rules.push(rubi_rule!(
        order: 2921,
        source: "Int[(f_+g_.*x_^s_)^r_.*(a_.+b_.*Log[c_.*(d_+e_.*x_^n_)^p_.])^q_.,x_Symbol] :=
          With[{t=ExpandIntegrand[(a+b*Log[c*(d+e*x^n)^p])^q,(f+g*x^s)^r,x]},
          Int[t,x] /;
         SumQ[t]] /;
        FreeQ[{a,b,c,d,e,f,g,n,p,q,r,s},x] && IntegerQ[n] && IGtQ[q,0] && IntegerQ[r] && IntegerQ[s] &&
          (EqQ[q,1] || GtQ[r,0] && GtQ[s,1] || LtQ[s,0] && LtQ[r,0])",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [f__, g__, s_, r_, a__, b__, c__, d__, e__, n_, p_, q_, x_],
        optional: [g__, r_, a__, b__, c__, e__, p_, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, n_, p_, q_, r_, s_], x_)
                && integerq!(n_)
                && igtq!(q_, 0)
                && integerq!(r_)
                && integerq!(s_)
                && (eqq!(q_, 1)
                    || (gtq!(r_, 0) && gtq!(s_, 1))
                    || (ltq!(s_, 0) && ltq!(r_, 0)))
                && {
                    let log_power = (&a__
                        + &b__ * (&c__ * (&d__ + &e__ * x_.pow(&n_)).pow(&p_)).log())
                    .pow(&q_);
                    let multiplier = (&f__ + &g__ * x_.pow(&s_)).pow(&r_);
                    rubi_expand_integrand_product_sum(&log_power, &multiplier, x_).is_some()
                }
        },
        rhs: {
            let log_power =
                (&a__ + &b__ * (&c__ * (&d__ + &e__ * x_.pow(&n_)).pow(&p_)).log()).pow(&q_);
            let multiplier = (&f__ + &g__ * x_.pow(&s_)).pow(&r_);
            let t = rubi_expand_integrand_product_sum(&log_power, &multiplier, x_)
                .expect("when clause should ensure expanded integrand is a sum");

            rubi_rhs_int(&t, x_)
        },
    ));
}

fn push_rules_rule_2922(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; n_, p_, q_, a__, b__, c__, d__, e__, f__, g__, x_, r_, s_);
    rules.push(rubi_rule!(
        order: 2922,
        source: "Int[(f_+g_.*x_^s_)^r_.*(a_.+b_.*Log[c_.*(d_+e_.*x_^n_)^p_.])^q_.,x_Symbol] :=
          With[{k=Denominator[n]},
          k \\[Star] Subst[Int[x^(k-1)*(f+g*x^(k*s))^r*(a+b*Log[c*(d+e*x^(k*n))^p])^q,x],x,x^(1/k)] /;
         IntegerQ[k*s]] /;
        FreeQ[{a,b,c,d,e,f,g,n,p,q,r,s},x] && FractionQ[n]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [f__, g__, s_, r_, a__, b__, c__, d__, e__, n_, p_, q_, x_],
        optional: [g__, r_, a__, b__, c__, e__, p_, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, n_, p_, q_, r_, s_], x_)
                && fractionq!(n_)
                && rubi_denominator(&n_).is_some_and(|k_i| integerq!(Atom::num(k_i) * &s_))
        },
        rhs: {
            let k_i = rubi_denominator(&n_).expect("FractionQ guard ensures a denominator");
            let k = Atom::num(k_i);
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let transformed_integrand = sub_atom.pow(&k - 1)
                * (&f__ + &g__ * sub_atom.pow(&k * &s_)).pow(&r_)
                * (&a__
                    + &b__
                        * (&c__ * (&d__ + &e__ * sub_atom.pow(&k * &n_)).pow(&p_)).log())
                .pow(&q_);
            let transformed_primitive = rubi_rhs_int(&transformed_integrand, substitution_symbol);
            let substitution = x_.pow(Atom::num(1) / &k);

            rubi_star(k, rubi_subst(&transformed_primitive, substitution_symbol, substitution))
        },
    ));
}

fn push_rules_rule_2923(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; n_, p_, q_, a__, b__, c__, d__, e__, f__, g__, x_, r_, s_);
    rules.push(rubi_rule!(
        order: 2923,
        source: "Int[(f_+g_.*x_^s_)^r_.(a_.+b_.*Log[c_.*(d_+e_.*x_^n_)^p_.])^q_.,x_Symbol] :=
          Unintegrable[(f+g*x^s)^r*(a+b*Log[c*(d+e*x^n)^p])^q,x] /;
        FreeQ[{a,b,c,d,e,f,g,n,p,q,r,s},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [f__, g__, s_, r_, a__, b__, c__, d__, e__, n_, p_, q_, x_],
        optional: [g__, r_, a__, b__, c__, e__, p_, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, n_, p_, q_, r_, s_], x_)
        },
        rhs: {
            let integrand = (&f__ + &g__ * x_.pow(&s_)).pow(&r_)
                * (&a__ + &b__ * (&c__ * (&d__ + &e__ * x_.pow(&n_)).pow(&p_)).log()).pow(&q_);

            rubi_unintegrable(integrand, x_)
        },
    ));
}

fn push_rules_rule_2924(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; p_, q_, a__, b__, c__, u__, v__, r_);
    rules.push(rubi_rule!(
        order: 2924,
        source: "Int[u_^r_.*(a_.+b_.*Log[c_.*v_^p_.])^q_.,x_Symbol] :=
          Int[ExpandToSum[u,x]^r*(a+b*Log[c*ExpandToSum[v,x]^p])^q,x] /;
        FreeQ[{a,b,c,p,q,r},x] && BinomialQ[{u,v},x] && Not[BinomialMatchQ[{u,v},x]]",
        desc: "Algebraic normalization",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [u__, r_, a__, b__, c__, v__, p_, q_, x_],
        optional: [r_, a__, b__, c__, p_, q_],
        when: {
            freeq!([a__, b__, c__, p_, q_, r_], x_)
                && rubi_binomial_q_list(&[&u__, &v__], x_)
                && !rubi_binomial_match_q_list(&[&u__, &v__], x_)
        },
        rhs: {
            let expanded_u = rubi_expand_to_sum(&u__, x_);
            let expanded_v = rubi_expand_to_sum(&v__, x_);
            let recursive_integrand =
                expanded_u.pow(&r_) * (&a__ + &b__ * (&c__ * expanded_v.pow(&p_)).log()).pow(&q_);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_2925(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        m_, n_, p_, q_, a__, b__, c__, d__, e__, f__, g__, x_, r_, s_
    );
    rules.push(rubi_rule!(
        order: 2925,
        source: "Int[x_^m_.*(f_+g_.*x_^s_)^r_.*(a_.+b_.*Log[c_.*(d_+e_.*x_^n_)^p_.])^q_.,x_Symbol] :=
          1/n \\[Star] Subst[Int[x^(Simplify[(m+1)/n]-1)*(f+g*x^(s/n))^r*(a+b*Log[c*(d+e*x)^p])^q,x],x,x^n] /;
        FreeQ[{a,b,c,d,e,f,g,m,n,p,q,r,s},x] && IntegerQ[r] && IntegerQ[s/n] && IntegerQ[Simplify[(m+1)/n]] && (GtQ[(m+1)/n,0] || IGtQ[q,0])",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [m_, f__, g__, s_, r_, a__, b__, c__, d__, e__, n_, p_, q_, x_],
        optional: [m_, g__, r_, a__, b__, c__, e__, p_, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, q_, r_, s_], x_)
                && integerq!(r_)
                && integerq!(&s_ / &n_)
                && {
                    let simplified = rubi_simplify(&((&m_ + 1) / &n_));
                    integerq!(simplified) && (gtq!((&m_ + 1) / &n_, 0) || igtq!(q_, 0))
                }
        },
        rhs: {
            let simplified = rubi_simplify(&((&m_ + 1) / &n_));
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let transformed_integrand = sub_atom.pow(&simplified - 1)
                * (&f__ + &g__ * sub_atom.pow(&s_ / &n_)).pow(&r_)
                * (&a__ + &b__ * (&c__ * (&d__ + &e__ * &sub_atom).pow(&p_)).log()).pow(&q_);
            let transformed_primitive = rubi_rhs_int(&transformed_integrand, substitution_symbol);
            let substitution = x_.pow(&n_);

            rubi_star(Atom::num(1) / &n_, rubi_subst(&transformed_primitive, substitution_symbol, substitution))
        },
    ));
}

fn push_rules_rule_2926(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        m_, n_, p_, q_, a__, b__, c__, d__, e__, f__, g__, x_, r_, s_
    );
    rules.push(rubi_rule!(
        order: 2926,
        source: "Int[x_^m_.*(f_+g_.*x_^s_)^r_.*(a_.+b_.*Log[c_.*(d_+e_.*x_^n_)^p_.])^q_.,x_Symbol] :=
          Int[ExpandIntegrand[(a+b*Log[c*(d+e*x^n)^p])^q,x^m*(f+g*x^s)^r,x],x] /;
        FreeQ[{a,b,c,d,e,f,g,m,n,p,q,r,s},x] && IGtQ[q,0] && IntegerQ[m] && IntegerQ[r] && IntegerQ[s]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [m_, f__, g__, s_, r_, a__, b__, c__, d__, e__, n_, p_, q_, x_],
        optional: [m_, g__, r_, a__, b__, c__, e__, p_, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, q_, r_, s_], x_)
                && igtq!(q_, 0)
                && integerq!(m_)
                && integerq!(r_)
                && integerq!(s_)
        },
        rhs: {
            let log_power =
                (&a__ + &b__ * (&c__ * (&d__ + &e__ * x_.pow(&n_)).pow(&p_)).log()).pow(&q_);
            let multiplier = x_.pow(&m_) * (&f__ + &g__ * x_.pow(&s_)).pow(&r_);
            let expanded = rubi_expand_integrand_product(&log_power, &multiplier, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_2927(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        m_, n_, p_, q_, a__, b__, c__, d__, e__, f__, g__, x_, r_, s_
    );
    rules.push(rubi_rule!(
        order: 2927,
        source: "Int[x_^m_.*(f_+g_.*x_^s_)^r_.*(a_.+b_.*Log[c_.*(d_+e_.*x_^n_)^p_.])^q_.,x_Symbol] :=
          1/n \\[Star] Subst[Int[x^(m+1/n-1)*(f+g*x^(s/n))^r*(a+b*Log[c*(d+e*x)^p])^q,x],x,x^n] /;
        FreeQ[{a,b,c,d,e,f,g,m,n,p,q,r,s},x] && FractionQ[n] && IntegerQ[1/n] && IntegerQ[s/n]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [m_, f__, g__, s_, r_, a__, b__, c__, d__, e__, n_, p_, q_, x_],
        optional: [m_, g__, r_, a__, b__, c__, e__, p_, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, q_, r_, s_], x_)
                && fractionq!(n_)
                && integerq!(Atom::num(1) / &n_)
                && integerq!(&s_ / &n_)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let transformed_integrand = sub_atom.pow(&m_ + Atom::num(1) / &n_ - 1)
                * (&f__ + &g__ * sub_atom.pow(&s_ / &n_)).pow(&r_)
                * (&a__ + &b__ * (&c__ * (&d__ + &e__ * &sub_atom).pow(&p_)).log()).pow(&q_);
            let transformed_primitive = rubi_rhs_int(&transformed_integrand, substitution_symbol);
            let substitution = x_.pow(&n_);

            rubi_star(Atom::num(1) / &n_, rubi_subst(&transformed_primitive, substitution_symbol, substitution))
        },
    ));
}

fn push_rules_rule_2928(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        m_, n_, p_, q_, a__, b__, c__, d__, e__, f__, g__, h__, x_, r_, s_
    );
    rules.push(rubi_rule!(
        order: 2928,
        source: "Int[(h_.*x_)^m_*(f_.+g_.*x_^s_.)^r_.*(a_.+b_.*Log[c_.*(d_+e_.*x_^n_.)^p_.])^q_.,x_Symbol] :=
          With[{k=Denominator[m]},
          k/h \\[Star] Subst[Int[x^(k*(m+1)-1)*(f+g*x^(k*s)/h^s)^r*(a+b*Log[c*(d+e*x^(k*n)/h^n)^p])^q,x],x,(h*x)^(1/k)]] /;
        FreeQ[{a,b,c,d,e,f,g,h,p,r},x] && FractionQ[m] && IntegerQ[n] && IntegerQ[s]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [h__, m_, f__, g__, s_, r_, a__, b__, c__, d__, e__, n_, p_, q_, x_],
        optional: [h__, f__, g__, s_, r_, a__, b__, c__, e__, n_, p_, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__, p_, r_], x_)
                && fractionq!(m_)
                && integerq!(n_)
                && integerq!(s_)
        },
        rhs: {
            let k_i = rubi_denominator(&m_).expect("FractionQ guard ensures a denominator");
            let k = Atom::num(k_i);
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let transformed_integrand = sub_atom.pow(&k * (&m_ + 1) - 1)
                * (&f__ + &g__ * sub_atom.pow(&k * &s_) / h__.pow(&s_)).pow(&r_)
                * (&a__
                    + &b__
                        * (&c__ * (&d__ + &e__ * sub_atom.pow(&k * &n_) / h__.pow(&n_)).pow(&p_))
                            .log())
                .pow(&q_);
            let transformed_primitive = rubi_rhs_int(&transformed_integrand, substitution_symbol);
            let substitution = (&h__ * x_).pow(Atom::num(1) / &k);

            rubi_star(k, rubi_subst(&transformed_primitive, substitution_symbol, substitution) / &h__)
        },
    ));
}

fn push_rules_rule_2929(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        m_, n_, p_, q_, a__, b__, c__, d__, e__, f__, g__, h__, x_, r_, s_
    );
    rules.push(rubi_rule!(
        order: 2929,
        source: "Int[(h_.*x_)^m_.*(f_+g_.*x_^s_)^r_.(a_.+b_.*Log[c_.*(d_+e_.*x_^n_)^p_.])^q_.,x_Symbol] :=
          Unintegrable[(h*x)^m*(f+g*x^s)^r*(a+b*Log[c*(d+e*x^n)^p])^q,x] /;
        FreeQ[{a,b,c,d,e,f,g,h,m,n,p,q,r,s},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [h__, m_, f__, g__, s_, r_, a__, b__, c__, d__, e__, n_, p_, q_, x_],
        optional: [h__, m_, g__, r_, a__, b__, c__, e__, p_, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__, m_, n_, p_, q_, r_, s_], x_)
        },
        rhs: {
            let integrand = (&h__ * x_).pow(&m_)
                * (&f__ + &g__ * x_.pow(&s_)).pow(&r_)
                * (&a__ + &b__ * (&c__ * (&d__ + &e__ * x_.pow(&n_)).pow(&p_)).log()).pow(&q_);

            rubi_unintegrable(integrand, x_)
        },
    ));
}

fn push_rules_rule_2930(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; m_, p_, q_, a__, b__, c__, h__, u__, v__, x_, r_);
    rules.push(rubi_rule!(
        order: 2930,
        source: "Int[(h_.*x_)^m_.*u_^r_.*(a_.+b_.*Log[c_.*v_^p_.])^q_.,x_Symbol] :=
          Int[(h*x)^m*ExpandToSum[u,x]^r*(a+b*Log[c*ExpandToSum[v,x]^p])^q,x] /;
        FreeQ[{a,b,c,h,m,p,q,r},x] && BinomialQ[{u,v},x] && Not[BinomialMatchQ[{u,v},x]]",
        desc: "Algebraic normalization",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [h__, m_, u__, r_, a__, b__, c__, v__, p_, q_, x_],
        optional: [h__, m_, r_, a__, b__, c__, p_, q_],
        when: {
            freeq!([a__, b__, c__, h__, m_, p_, q_, r_], x_)
                && rubi_binomial_q_list(&[&u__, &v__], x_)
                && !rubi_binomial_match_q_list(&[&u__, &v__], x_)
        },
        rhs: {
            let expanded_u = rubi_expand_to_sum(&u__, x_);
            let expanded_v = rubi_expand_to_sum(&v__, x_);
            let recursive_integrand =
                (&h__ * x_).pow(&m_)
                    * expanded_u.pow(&r_)
                    * (&a__ + &b__ * (&c__ * expanded_v.pow(&p_)).log()).pow(&q_);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_2931(rules: &mut Vec<RubiRule>) {
    rubi_symb!(m_, n_, p_, q_, a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 2931,
        source: "Int[Log[f_.*x_^q_.]^m_.*(a_.+b_.*Log[c_.*(d_+e_.*x_^n_)^p_.])/x_,x_Symbol] :=
          Log[f*x^q]^(m+1)*(a+b*Log[c*(d+e*x^n)^p])/(q*(m+1)) -
          b*e*n*p/(q*(m+1)) \\[Star] Int[x^(n-1)*Log[f*x^q]^(m+1)/(d+e*x^n),x] /;
        FreeQ[{a,b,c,d,e,f,m,n,p,q},x] && NeQ[m,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern: (f__ * x_.pow(q_)).log().pow(m_)
            * (a__ + b__ * (c__ * (d__ + e__ * x_.pow(n_)).pow(p_)).log())
            / x_,
        with: [f__, q_, m_, a__, b__, c__, d__, e__, n_, p_, x_],
        optional: [f__, q_, m_, a__, b__, c__, e__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_, p_, q_], x_)
                && neq!(m_, -1)
        },
        rhs: {
            let x_log = (&f__ * x_.pow(&q_)).log();
            let logarithmic =
                &a__ + &b__ * (&c__ * (&d__ + &e__ * x_.pow(&n_)).pow(&p_)).log();
            let recursive_integrand =
                x_.pow(&n_ - 1) * x_log.pow(&m_ + 1) / (&d__ + &e__ * x_.pow(&n_));
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(
                    &(x_log.pow(&m_ + 1) * logarithmic / (&q_ * (&m_ + 1))),
                    x_,
                ) - rubi_star(&b__ * &e__ * &n_ * &p_ / (&q_ * (&m_ + 1)), recursive)
        },
    ));
}

fn push_rules_rule_2932(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_f_, m_, n_, p_, a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 2932,
        source: "Int[F_[f_.*x_]^m_.*(a_.+b_.*Log[c_.*(d_+e_.*x_^n_)^p_.]),x_Symbol] :=
          With[{u=IntHide[F[f*x]^m,x]},
          (a+b*Log[c*(d+e*x^n)^p]) \\[Star] u - b*e*n*p \\[Star] Int[SimplifyIntegrand[u*x^(n-1)/(d+e*x^n),x],x]] /;
        FreeQ[{a,b,c,d,e,f,p},x] && MemberQ[{ArcSin,ArcCos,ArcSinh,ArcCosh},F] && IGtQ[m,0] && IGtQ[n,1]",
        desc: "Integration by parts",
        refs: [],
        pattern: capital_f_.call(f__ * x_).pow(m_)
            * (a__ + b__ * (c__ * (d__ + e__ * x_.pow(n_)).pow(p_)).log()),
        with: [capital_f_, f__, m_, a__, b__, c__, d__, e__, n_, p_, x_],
        optional: [f__, m_, a__, b__, c__, e__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, p_], x_)
                && rubi_function_head_member_q(
                    &capital_f_,
                    &[
                        symbol!("asin"),
                        symbol!("acos"),
                        symbol!("asinh"),
                        symbol!("acosh"),
                    ],
                )
                && igtq!(m_, 0)
                && igtq!(n_, 1)
        },
        rhs: {
            let inverse = rubi_function_head_symbol(&capital_f_).rubi_rhs().call(&f__ * x_);
            let u = rubi_int_hide(&inverse.pow(&m_), x_).rubi_rhs();
            let logarithmic =
                &a__ + &b__ * (&c__ * (&d__ + &e__ * x_.pow(&n_)).pow(&p_)).log();
            let recursive_integrand =
                rubi_simplify_integrand(&(&u * x_.pow(&n_ - 1) / (&d__ + &e__ * x_.pow(&n_))), x_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(logarithmic, u)
                    - rubi_star(&b__ * &e__ * &n_ * &p_, recursive)
        },
    ));
}

fn push_rules_rule_2933(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; n_, p_, q_, a__, b__, c__, d__, e__, f__, g__, x_);
    rules.push(rubi_rule!(
        order: 2933,
        source: "Int[(a_.+b_.*Log[c_.*(d_+e_.*(f_.+g_.*x_)^n_)^p_.])^q_.,x_Symbol] :=
          1/g \\[Star] Subst[Int[(a+b*Log[c*(d+e*x^n)^p])^q,x],x,f+g*x] /;
        FreeQ[{a,b,c,d,e,f,g,n,p},x] && IGtQ[q,0] && (EqQ[q,1] || IntegerQ[n])",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, n_, p_, q_, x_],
        optional: [a__, b__, c__, e__, f__, g__, p_, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, n_, p_], x_)
                && igtq!(q_, 0)
                && (eqq!(q_, 1) || integerq!(n_))
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let transformed_integrand =
                (&a__ + &b__ * (&c__ * (&d__ + &e__ * sub_atom.pow(&n_)).pow(&p_)).log()).pow(&q_);
            let transformed_primitive = rubi_rhs_int(&transformed_integrand, substitution_symbol);
            let substitution = &f__ + &g__ * x_;

            rubi_star(Atom::num(1) / &g__, rubi_subst(&transformed_primitive, substitution_symbol, substitution))
        },
    ));
}

fn push_rules_rule_2934(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; n_, p_, q_, a__, b__, c__, d__, e__, f__, g__, x_);
    rules.push(rubi_rule!(
        order: 2934,
        source: "Int[(a_.+b_.*Log[c_.*(d_+e_.*(f_.+g_.*x_)^n_)^p_.])^q_.,x_Symbol] :=
          Unintegrable[(a+b*Log[c*(d+e*(f+g*x)^n)^p])^q,x] /;
        FreeQ[{a,b,c,d,e,f,g,n,p,q},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, n_, p_, q_, x_],
        optional: [a__, b__, c__, e__, f__, g__, p_, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, n_, p_, q_], x_)
        },
        rhs: {
            let integrand =
                (&a__
                    + &b__
                        * (&c__ * (&d__ + &e__ * (&f__ + &g__ * x_).pow(&n_)).pow(&p_))
                            .log())
                .pow(&q_);

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
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let q_ = symbols.q_;
    let x_ = symbols.x_;
    (a__ + b__ * (c__ * (d__ + e__ * (f__ + g__ * x_).pow(n_)).pow(p_)).log()).pow(q_)
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let q_ = symbols.q_;
    let x_ = symbols.x_;
    (a__ + b__ * (c__ * (d__ + e__ * x_.pow(n_)).pow(p_)).log()).pow(q_)
}

#[inline(never)]
fn rubi_shared_pattern_2(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let q_ = symbols.q_;
    let x_ = symbols.x_;
    (f__ * x_).pow(m_) * (a__ + b__ * (c__ * (d__ + e__ * x_.pow(n_)).pow(p_)).log()).pow(q_)
}

#[inline(never)]
fn rubi_shared_pattern_3(symbols: &RubiSymbols) -> Atom {
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
    let s_ = symbols.s_;
    let x_ = symbols.x_;
    (f__ + g__ * x_.pow(s_)).pow(r_)
        * (a__ + b__ * (c__ * (d__ + e__ * x_.pow(n_)).pow(p_)).log()).pow(q_)
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
    let h__ = symbols.h__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let q_ = symbols.q_;
    let r_ = symbols.r_;
    let x_ = symbols.x_;
    (h__ * x_).pow(m_)
        * (f__ + g__ * x_).pow(r_)
        * (a__ + b__ * (c__ * (d__ + e__ * x_.pow(n_)).pow(p_)).log()).pow(q_)
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
    let h__ = symbols.h__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let q_ = symbols.q_;
    let r_ = symbols.r_;
    let s_ = symbols.s_;
    let x_ = symbols.x_;
    (h__ * x_).pow(m_)
        * (f__ + g__ * x_.pow(s_)).pow(r_)
        * (a__ + b__ * (c__ * (d__ + e__ * x_.pow(n_)).pow(p_)).log()).pow(q_)
}

#[inline(never)]
fn rubi_shared_pattern_6(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let h__ = symbols.h__;
    let m_ = symbols.m_;
    let p_ = symbols.p_;
    let q_ = symbols.q_;
    let r_ = symbols.r_;
    let u__ = symbols.u__;
    let v__ = symbols.v__;
    let x_ = symbols.x_;
    (h__ * x_).pow(m_) * u__.pow(r_) * (a__ + b__ * (c__ * v__.pow(p_)).log()).pow(q_)
}

#[inline(never)]
fn rubi_shared_pattern_7(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let p_ = symbols.p_;
    let q_ = symbols.q_;
    let r_ = symbols.r_;
    let u__ = symbols.u__;
    let v__ = symbols.v__;
    u__.pow(r_) * (a__ + b__ * (c__ * v__.pow(p_)).log()).pow(q_)
}

#[inline(never)]
fn rubi_shared_pattern_8(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let q_ = symbols.q_;
    let x_ = symbols.x_;
    x_.pow(m_) * (a__ + b__ * (c__ * (d__ + e__ * x_.pow(n_)).pow(p_)).log()).pow(q_)
}

#[inline(never)]
fn rubi_shared_pattern_9(symbols: &RubiSymbols) -> Atom {
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
    let s_ = symbols.s_;
    let x_ = symbols.x_;
    x_.pow(m_)
        * (f__ + g__ * x_.pow(s_)).pow(r_)
        * (a__ + b__ * (c__ * (d__ + e__ * x_.pow(n_)).pow(p_)).log()).pow(q_)
}
