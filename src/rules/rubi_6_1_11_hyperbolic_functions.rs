use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_5799(rules);
    push_rules_rule_5800(rules);
    push_rules_rule_5801(rules);
    push_rules_rule_5802(rules);
    push_rules_rule_5803(rules);
    push_rules_rule_5804(rules);
    push_rules_rule_5805(rules);
    push_rules_rule_5806(rules);
    push_rules_rule_5807(rules);
    push_rules_rule_5808(rules);
    push_rules_rule_5809(rules);
    push_rules_rule_5810(rules);
    push_rules_rule_5811(rules);
    push_rules_rule_5812(rules);
    push_rules_rule_5813(rules);
    push_rules_rule_5814(rules);
    push_rules_rule_5815(rules);
    push_rules_rule_5816(rules);
    push_rules_rule_5817(rules);
    push_rules_rule_5818(rules);
    push_rules_rule_5819(rules);
    push_rules_rule_5820(rules);
}

fn push_rules_rule_5799(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5799,
        source: "Int[(a_+b_.*x_^n_)^p_.*Sinh[c_.+d_.*x_],x_Symbol] :=
          Int[ExpandIntegrand[Sinh[c+d*x],(a+b*x^n)^p,x],x] /;
        FreeQ[{a,b,c,d,n},x] && IGtQ[p,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, n_, p_, c__, d__, x_],
        optional: [b__, p_, c__, d__],
        when: { freeq!([a__, b__, c__, d__, n_], x_) && igtq!(p_, 0) },
        rhs: {
            let expanded = rubi_expand_integrand(
                &((&c__ + &d__ * x_).sinh()
                    * (&a__ + &b__ * x_.pow(&n_)).pow(&p_)),
                x_,
            );
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_5800(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5800,
        source: "Int[(a_+b_.*x_^n_)^p_.*Cosh[c_.+d_.*x_],x_Symbol] :=
          Int[ExpandIntegrand[Cosh[c+d*x],(a+b*x^n)^p,x],x] /;
        FreeQ[{a,b,c,d,n},x] && IGtQ[p,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, n_, p_, c__, d__, x_],
        optional: [b__, p_, c__, d__],
        when: { freeq!([a__, b__, c__, d__, n_], x_) && igtq!(p_, 0) },
        rhs: {
            let expanded = rubi_expand_integrand(
                &((&c__ + &d__ * x_).cosh()
                    * (&a__ + &b__ * x_.pow(&n_)).pow(&p_)),
                x_,
            );
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_5801(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5801,
        source: "Int[(a_+b_.*x_^n_)^p_*Sinh[c_.+d_.*x_],x_Symbol] :=
          x^(-n+1)*(a+b*x^n)^(p+1)*Sinh[c+d*x]/(b*n*(p+1)) -
          (-n+1)/(b*n*(p+1)) \\[Star] Int[x^(-n)*(a+b*x^n)^(p+1)*Sinh[c+d*x],x] -
          d/(b*n*(p+1)) \\[Star] Int[x^(-n+1)*(a+b*x^n)^(p+1)*Cosh[c+d*x],x] /;
        FreeQ[{a,b,c,d},x] && IntegerQ[p] && IGtQ[n,0] && LtQ[p,-1] && GtQ[n,2]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, n_, p_, c__, d__, x_],
        optional: [b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && integerq!(p_)
                && igtq!(n_, 0)
                && ltq!(p_, -1)
                && gtq!(n_, 2)
        },
        rhs: {
            let binomial = &a__ + &b__ * x_.pow(&n_);
            let angle = &c__ + &d__ * x_;
            let denominator = &b__ * &n_ * (&p_ + 1);
            let recursive_1 = x_.pow(-&n_) * binomial.pow(&p_ + 1) * &angle.sinh();
            let recursive_2 =
                x_.pow(Atom::num(1) - &n_) * binomial.pow(&p_ + 1) * &angle.cosh();
            rubi_simp(&(x_.pow(Atom::num(1) - &n_) * binomial.pow(&p_ + 1) * angle.sinh()
                    / &denominator), x_)
                    - rubi_star((Atom::num(1) - &n_) / &denominator, rubi_rhs_int(&recursive_1, x_))
                    - rubi_star(&d__ / &denominator, rubi_rhs_int(&recursive_2, x_))
        },
    ));
}

fn push_rules_rule_5802(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5802,
        source: "Int[(a_+b_.*x_^n_)^p_*Cosh[c_.+d_.*x_],x_Symbol] :=
          x^(-n+1)*(a+b*x^n)^(p+1)*Cosh[c+d*x]/(b*n*(p+1)) -
          (-n+1)/(b*n*(p+1)) \\[Star] Int[x^(-n)*(a+b*x^n)^(p+1)*Cosh[c+d*x],x] -
          d/(b*n*(p+1)) \\[Star] Int[x^(-n+1)*(a+b*x^n)^(p+1)*Sinh[c+d*x],x] /;
        FreeQ[{a,b,c,d},x] && IntegerQ[p] && IGtQ[n,0] && LtQ[p,-1] && GtQ[n,2]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, n_, p_, c__, d__, x_],
        optional: [b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && integerq!(p_)
                && igtq!(n_, 0)
                && ltq!(p_, -1)
                && gtq!(n_, 2)
        },
        rhs: {
            let binomial = &a__ + &b__ * x_.pow(&n_);
            let angle = &c__ + &d__ * x_;
            let denominator = &b__ * &n_ * (&p_ + 1);
            let recursive_1 = x_.pow(-&n_) * binomial.pow(&p_ + 1) * &angle.cosh();
            let recursive_2 =
                x_.pow(Atom::num(1) - &n_) * binomial.pow(&p_ + 1) * &angle.sinh();
            rubi_simp(&(x_.pow(Atom::num(1) - &n_) * binomial.pow(&p_ + 1) * angle.cosh()
                    / &denominator), x_)
                    - rubi_star((Atom::num(1) - &n_) / &denominator, rubi_rhs_int(&recursive_1, x_))
                    - rubi_star(&d__ / &denominator, rubi_rhs_int(&recursive_2, x_))
        },
    ));
}

fn push_rules_rule_5803(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5803,
        source: "Int[(a_+b_.*x_^n_)^p_*Sinh[c_.+d_.*x_],x_Symbol] :=
          Int[ExpandIntegrand[Sinh[c+d*x],(a+b*x^n)^p,x],x] /;
        FreeQ[{a,b,c,d},x] && ILtQ[p,0] && IGtQ[n,0] && (EqQ[n,2] || EqQ[p,-1])",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, n_, p_, c__, d__, x_],
        optional: [b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && iltq!(p_, 0)
                && igtq!(n_, 0)
                && (eqq!(n_, 2) || eqq!(p_, -1))
        },
        rhs: {
            let expanded = rubi_expand_integrand_product(
                &(&c__ + &d__ * x_).sinh(),
                &(&a__ + &b__ * x_.pow(&n_)).pow(&p_),
                x_,
            );
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_5804(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5804,
        source: "Int[(a_+b_.*x_^n_)^p_*Cosh[c_.+d_.*x_],x_Symbol] :=
          Int[ExpandIntegrand[Cosh[c+d*x],(a+b*x^n)^p,x],x] /;
        FreeQ[{a,b,c,d},x] && ILtQ[p,0] && IGtQ[n,0] && (EqQ[n,2] || EqQ[p,-1])",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, n_, p_, c__, d__, x_],
        optional: [b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && iltq!(p_, 0)
                && igtq!(n_, 0)
                && (eqq!(n_, 2) || eqq!(p_, -1))
        },
        rhs: {
            let expanded = rubi_expand_integrand_product(
                &(&c__ + &d__ * x_).cosh(),
                &(&a__ + &b__ * x_.pow(&n_)).pow(&p_),
                x_,
            );
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_5805(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5805,
        source: "Int[(a_+b_.*x_^n_)^p_*Sinh[c_.+d_.*x_],x_Symbol] :=
          Int[x^(n*p)*(b+a*x^(-n))^p*Sinh[c+d*x],x] /;
        FreeQ[{a,b,c,d},x] && ILtQ[p,0] && ILtQ[n,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, n_, p_, c__, d__, x_],
        optional: [b__, c__, d__],
        when: { freeq!([a__, b__, c__, d__], x_) && iltq!(p_, 0) && iltq!(n_, 0) },
        rhs: {
            rubi_rhs_int(
                &(x_.pow(&n_ * &p_)
                    * (&b__ + &a__ / x_.pow(&n_)).pow(&p_)
                    * (&c__ + &d__ * x_).sinh()),
                x_,
            )
        },
    ));
}

fn push_rules_rule_5806(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5806,
        source: "Int[(a_+b_.*x_^n_)^p_*Cosh[c_.+d_.*x_],x_Symbol] :=
          Int[x^(n*p)*(b+a*x^(-n))^p*Cosh[c+d*x],x] /;
        FreeQ[{a,b,c,d},x] && ILtQ[p,0] && ILtQ[n,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, n_, p_, c__, d__, x_],
        optional: [b__, c__, d__],
        when: { freeq!([a__, b__, c__, d__], x_) && iltq!(p_, 0) && iltq!(n_, 0) },
        rhs: {
            rubi_rhs_int(
                &(x_.pow(&n_ * &p_)
                    * (&b__ + &a__ / x_.pow(&n_)).pow(&p_)
                    * (&c__ + &d__ * x_).cosh()),
                x_,
            )
        },
    ));
}

fn push_rules_rule_5807(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5807,
        source: "Int[(a_+b_.*x_^n_)^p_*Sinh[c_.+d_.*x_],x_Symbol] :=
          Unintegrable[(a+b*x^n)^p*Sinh[c+d*x],x] /;
        FreeQ[{a,b,c,d,n,p},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, n_, p_, c__, d__, x_],
        optional: [b__, c__, d__],
        when: { freeq!([a__, b__, c__, d__, n_, p_], x_) },
        rhs: {
            rubi_unintegrable(
                (&a__ + &b__ * x_.pow(&n_)).pow(&p_) * (&c__ + &d__ * x_).sinh(),
                x_,
            )
        },
    ));
}

fn push_rules_rule_5808(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5808,
        source: "Int[(a_+b_.*x_^n_)^p_*Cosh[c_.+d_.*x_],x_Symbol] :=
          Unintegrable[(a+b*x^n)^p*Cosh[c+d*x],x] /;
        FreeQ[{a,b,c,d,n,p},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, n_, p_, c__, d__, x_],
        optional: [b__, c__, d__],
        when: { freeq!([a__, b__, c__, d__, n_, p_], x_) },
        rhs: {
            rubi_unintegrable(
                (&a__ + &b__ * x_.pow(&n_)).pow(&p_) * (&c__ + &d__ * x_).cosh(),
                x_,
            )
        },
    ));
}

fn push_rules_rule_5809(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5809,
        source: "Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_.*Sinh[c_.+d_.*x_],x_Symbol] :=
          Int[ExpandIntegrand[Sinh[c+d*x],(e*x)^m*(a+b*x^n)^p,x],x] /;
        FreeQ[{a,b,c,d,e,m,n},x] && IGtQ[p,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [e__, m_, a__, b__, n_, p_, c__, d__, x_],
        optional: [e__, m_, b__, p_, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_], x_) && igtq!(p_, 0)
        },
        rhs: {
            let expanded = rubi_expand_integrand(
                &((&c__ + &d__ * x_).sinh()
                    * (&e__ * x_).pow(&m_)
                    * (&a__ + &b__ * x_.pow(&n_)).pow(&p_)),
                x_,
            );
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_5810(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5810,
        source: "Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_.*Cosh[c_.+d_.*x_],x_Symbol] :=
          Int[ExpandIntegrand[Cosh[c+d*x],(e*x)^m*(a+b*x^n)^p,x],x] /;
        FreeQ[{a,b,c,d,e,m,n},x] && IGtQ[p,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [e__, m_, a__, b__, n_, p_, c__, d__, x_],
        optional: [e__, m_, b__, p_, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_], x_) && igtq!(p_, 0)
        },
        rhs: {
            let expanded = rubi_expand_integrand(
                &((&c__ + &d__ * x_).cosh()
                    * (&e__ * x_).pow(&m_)
                    * (&a__ + &b__ * x_.pow(&n_)).pow(&p_)),
                x_,
            );
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_5811(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5811,
        source: "Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_*Sinh[c_.+d_.*x_],x_Symbol] :=
          e^m*(a+b*x^n)^(p+1)*Sinh[c+d*x]/(b*n*(p+1)) -
          d*e^m/(b*n*(p+1)) \\[Star] Int[(a+b*x^n)^(p+1)*Cosh[c+d*x],x] /;
        FreeQ[{a,b,c,d,e,m,n},x] && IntegerQ[p] && EqQ[m-n+1,0] && LtQ[p,-1] && (IntegerQ[n] || GtQ[e,0])",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [e__, m_, a__, b__, n_, p_, c__, d__, x_],
        optional: [e__, m_, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_], x_)
                && integerq!(p_)
                && eqq!(&m_ - &n_ + 1, 0)
                && ltq!(p_, -1)
                && (integerq!(n_) || gtq!(e__, 0))
        },
        rhs: {
            let binomial = &a__ + &b__ * x_.pow(&n_);
            let angle = &c__ + &d__ * x_;
            let scale = e__.pow(&m_);
            let denominator = &b__ * &n_ * (&p_ + 1);
            rubi_simp(&(&scale * binomial.pow(&p_ + 1) * angle.sinh() / &denominator), x_)
                    - rubi_star(&d__ * &scale / &denominator, rubi_rhs_int(&(binomial.pow(&p_ + 1) * angle.cosh()), x_))
        },
    ));
}

fn push_rules_rule_5812(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5812,
        source: "Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_*Cosh[c_.+d_.*x_],x_Symbol] :=
          e^m*(a+b*x^n)^(p+1)*Cosh[c+d*x]/(b*n*(p+1)) -
          d*e^m/(b*n*(p+1)) \\[Star] Int[(a+b*x^n)^(p+1)*Sinh[c+d*x],x] /;
        FreeQ[{a,b,c,d,e,m,n},x] && IntegerQ[p] && EqQ[m-n+1,0] && LtQ[p,-1] && (IntegerQ[n] || GtQ[e,0])",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [e__, m_, a__, b__, n_, p_, c__, d__, x_],
        optional: [e__, m_, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_], x_)
                && integerq!(p_)
                && eqq!(&m_ - &n_ + 1, 0)
                && ltq!(p_, -1)
                && (integerq!(n_) || gtq!(e__, 0))
        },
        rhs: {
            let binomial = &a__ + &b__ * x_.pow(&n_);
            let angle = &c__ + &d__ * x_;
            let scale = e__.pow(&m_);
            let denominator = &b__ * &n_ * (&p_ + 1);
            rubi_simp(&(&scale * binomial.pow(&p_ + 1) * angle.cosh() / &denominator), x_)
                    - rubi_star(&d__ * &scale / &denominator, rubi_rhs_int(&(binomial.pow(&p_ + 1) * angle.sinh()), x_))
        },
    ));
}

fn push_rules_rule_5813(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5813,
        source: "Int[x_^m_.*(a_+b_.*x_^n_)^p_*Sinh[c_.+d_.*x_],x_Symbol] :=
          x^(m-n+1)*(a+b*x^n)^(p+1)*Sinh[c+d*x]/(b*n*(p+1)) -
          (m-n+1)/(b*n*(p+1)) \\[Star] Int[x^(m-n)*(a+b*x^n)^(p+1)*Sinh[c+d*x],x] -
          d/(b*n*(p+1)) \\[Star] Int[x^(m-n+1)*(a+b*x^n)^(p+1)*Cosh[c+d*x],x] /;
        FreeQ[{a,b,c,d},x] && ILtQ[p,-1] && IGtQ[n,0] && RationalQ[m] && (GtQ[m-n+1,0] || GtQ[n,2])",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [m_, a__, b__, n_, p_, c__, d__, x_],
        optional: [m_, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && iltq!(p_, -1)
                && igtq!(n_, 0)
                && rationalq!(m_)
                && (gtq!(&m_ - &n_ + 1, 0) || gtq!(n_, 2))
        },
        rhs: {
            let binomial = &a__ + &b__ * x_.pow(&n_);
            let angle = &c__ + &d__ * x_;
            let denominator = &b__ * &n_ * (&p_ + 1);
            let degree = &m_ - &n_ + 1;
            let recursive_1 = x_.pow(&m_ - &n_) * binomial.pow(&p_ + 1) * &angle.sinh();
            let recursive_2 = x_.pow(&degree) * binomial.pow(&p_ + 1) * &angle.cosh();
            rubi_simp(&(x_.pow(&degree) * binomial.pow(&p_ + 1) * angle.sinh() / &denominator), x_)
                    - rubi_star(&degree / &denominator, rubi_rhs_int(&recursive_1, x_))
                    - rubi_star(&d__ / &denominator, rubi_rhs_int(&recursive_2, x_))
        },
    ));
}

fn push_rules_rule_5814(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5814,
        source: "Int[x_^m_.*(a_+b_.*x_^n_)^p_*Cosh[c_.+d_.*x_],x_Symbol] :=
          x^(m-n+1)*(a+b*x^n)^(p+1)*Cosh[c+d*x]/(b*n*(p+1)) -
          (m-n+1)/(b*n*(p+1)) \\[Star] Int[x^(m-n)*(a+b*x^n)^(p+1)*Cosh[c+d*x],x] -
          d/(b*n*(p+1)) \\[Star] Int[x^(m-n+1)*(a+b*x^n)^(p+1)*Sinh[c+d*x],x] /;
        FreeQ[{a,b,c,d},x] && ILtQ[p,-1] && IGtQ[n,0] && RationalQ[m] && (GtQ[m-n+1,0] || GtQ[n,2])",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [m_, a__, b__, n_, p_, c__, d__, x_],
        optional: [m_, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && iltq!(p_, -1)
                && igtq!(n_, 0)
                && rationalq!(m_)
                && (gtq!(&m_ - &n_ + 1, 0) || gtq!(n_, 2))
        },
        rhs: {
            let binomial = &a__ + &b__ * x_.pow(&n_);
            let angle = &c__ + &d__ * x_;
            let denominator = &b__ * &n_ * (&p_ + 1);
            let degree = &m_ - &n_ + 1;
            let recursive_1 = x_.pow(&m_ - &n_) * binomial.pow(&p_ + 1) * &angle.cosh();
            let recursive_2 = x_.pow(&degree) * binomial.pow(&p_ + 1) * &angle.sinh();
            rubi_simp(&(x_.pow(&degree) * binomial.pow(&p_ + 1) * angle.cosh() / &denominator), x_)
                    - rubi_star(&degree / &denominator, rubi_rhs_int(&recursive_1, x_))
                    - rubi_star(&d__ / &denominator, rubi_rhs_int(&recursive_2, x_))
        },
    ));
}

fn push_rules_rule_5815(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5815,
        source: "Int[x_^m_.*(a_+b_.*x_^n_)^p_*Sinh[c_.+d_.*x_],x_Symbol] :=
          Int[ExpandIntegrand[Sinh[c+d*x],x^m*(a+b*x^n)^p,x],x] /;
        FreeQ[{a,b,c,d},x] && ILtQ[p,0] && IntegerQ[m] && IGtQ[n,0] && (EqQ[n,2] || EqQ[p,-1])",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [m_, a__, b__, n_, p_, c__, d__, x_],
        optional: [m_, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && iltq!(p_, 0)
                && integerq!(m_)
                && igtq!(n_, 0)
                && (eqq!(n_, 2) || eqq!(p_, -1))
        },
        rhs: {
            let expanded = rubi_expand_integrand_product(
                &(&c__ + &d__ * x_).sinh(),
                &(x_.pow(&m_) * (&a__ + &b__ * x_.pow(&n_)).pow(&p_)),
                x_,
            );
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_5816(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5816,
        source: "Int[x_^m_.*(a_+b_.*x_^n_)^p_*Cosh[c_.+d_.*x_],x_Symbol] :=
          Int[ExpandIntegrand[Cosh[c+d*x],x^m*(a+b*x^n)^p,x],x] /;
        FreeQ[{a,b,c,d},x] && ILtQ[p,0] && IntegerQ[m] && IGtQ[n,0] && (EqQ[n,2] || EqQ[p,-1])",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [m_, a__, b__, n_, p_, c__, d__, x_],
        optional: [m_, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && iltq!(p_, 0)
                && integerq!(m_)
                && igtq!(n_, 0)
                && (eqq!(n_, 2) || eqq!(p_, -1))
        },
        rhs: {
            let expanded = rubi_expand_integrand_product(
                &(&c__ + &d__ * x_).cosh(),
                &(x_.pow(&m_) * (&a__ + &b__ * x_.pow(&n_)).pow(&p_)),
                x_,
            );
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_5817(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5817,
        source: "Int[x_^m_.*(a_+b_.*x_^n_)^p_*Sinh[c_.+d_.*x_],x_Symbol] :=
          Int[x^(m+n*p)*(b+a*x^(-n))^p*Sinh[c+d*x],x] /;
        FreeQ[{a,b,c,d,m},x] && ILtQ[p,0] && ILtQ[n,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [m_, a__, b__, n_, p_, c__, d__, x_],
        optional: [m_, b__, c__, d__],
        when: { freeq!([a__, b__, c__, d__, m_], x_) && iltq!(p_, 0) && iltq!(n_, 0) },
        rhs: {
            rubi_rhs_int(
                &(x_.pow(&m_ + &n_ * &p_)
                    * (&b__ + &a__ / x_.pow(&n_)).pow(&p_)
                    * (&c__ + &d__ * x_).sinh()),
                x_,
            )
        },
    ));
}

fn push_rules_rule_5818(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5818,
        source: "Int[x_^m_.*(a_+b_.*x_^n_)^p_*Cosh[c_.+d_.*x_],x_Symbol] :=
          Int[x^(m+n*p)*(b+a*x^(-n))^p*Cosh[c+d*x],x] /;
        FreeQ[{a,b,c,d,m},x] && ILtQ[p,0] && ILtQ[n,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [m_, a__, b__, n_, p_, c__, d__, x_],
        optional: [m_, b__, c__, d__],
        when: { freeq!([a__, b__, c__, d__, m_], x_) && iltq!(p_, 0) && iltq!(n_, 0) },
        rhs: {
            rubi_rhs_int(
                &(x_.pow(&m_ + &n_ * &p_)
                    * (&b__ + &a__ / x_.pow(&n_)).pow(&p_)
                    * (&c__ + &d__ * x_).cosh()),
                x_,
            )
        },
    ));
}

fn push_rules_rule_5819(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5819,
        source: "Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_.*Sinh[c_.+d_.*x_],x_Symbol] :=
          Unintegrable[(e*x)^m*(a+b*x^n)^p*Sinh[c+d*x],x] /;
        FreeQ[{a,b,c,d,e,m,n,p},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [e__, m_, a__, b__, n_, p_, c__, d__, x_],
        optional: [e__, m_, b__, c__, d__, p_],
        when: { freeq!([a__, b__, c__, d__, e__, m_, n_, p_], x_) },
        rhs: {
            rubi_unintegrable(
                (&e__ * x_).pow(&m_) * (&a__ + &b__ * x_.pow(&n_)).pow(&p_) * (&c__ + &d__ * x_).sinh(),
                x_,
            )
        },
    ));
}

fn push_rules_rule_5820(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5820,
        source: "Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_.*Cosh[c_.+d_.*x_],x_Symbol] :=
          Unintegrable[(e*x)^m*(a+b*x^n)^p*Cosh[c+d*x],x] /;
        FreeQ[{a,b,c,d,e,m,n,p},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [e__, m_, a__, b__, n_, p_, c__, d__, x_],
        optional: [e__, m_, b__, c__, d__, p_],
        when: { freeq!([a__, b__, c__, d__, e__, m_, n_, p_], x_) },
        rhs: {
            rubi_unintegrable(
                (&e__ * x_).pow(&m_) * (&a__ + &b__ * x_.pow(&n_)).pow(&p_) * (&c__ + &d__ * x_).cosh(),
                x_,
            )
        },
    ));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn downvalues_5799_through_5820_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .collect::<Vec<_>>();
        assert_eq!(orders, (5799..=5820).collect::<Vec<_>>());
    }
}

// Generated shared pattern builders.

#[inline(never)]
fn rubi_shared_pattern_0(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (a__ + b__ * x_.pow(n_)).pow(p_) * (c__ + d__ * x_).cosh()
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (a__ + b__ * x_.pow(n_)).pow(p_) * (c__ + d__ * x_).sinh()
}

#[inline(never)]
fn rubi_shared_pattern_2(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (e__ * x_).pow(m_) * (a__ + b__ * x_.pow(n_)).pow(p_) * (c__ + d__ * x_).cosh()
}

#[inline(never)]
fn rubi_shared_pattern_3(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (e__ * x_).pow(m_) * (a__ + b__ * x_.pow(n_)).pow(p_) * (c__ + d__ * x_).sinh()
}

#[inline(never)]
fn rubi_shared_pattern_4(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    x_.pow(m_) * (a__ + b__ * x_.pow(n_)).pow(p_) * (c__ + d__ * x_).cosh()
}

#[inline(never)]
fn rubi_shared_pattern_5(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    x_.pow(m_) * (a__ + b__ * x_.pow(n_)).pow(p_) * (c__ + d__ * x_).sinh()
}
