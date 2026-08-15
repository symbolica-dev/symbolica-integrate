use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_3810(rules);
    push_rules_rule_3811(rules);
    push_rules_rule_3812(rules);
    push_rules_rule_3813(rules);
    push_rules_rule_3814(rules);
    push_rules_rule_3815(rules);
    push_rules_rule_3816(rules);
    push_rules_rule_3817(rules);
    push_rules_rule_3818(rules);
    push_rules_rule_3819(rules);
    push_rules_rule_3820(rules);
    push_rules_rule_3821(rules);
    push_rules_rule_3822(rules);
    push_rules_rule_3823(rules);
    push_rules_rule_3824(rules);
    push_rules_rule_3825(rules);
    push_rules_rule_3826(rules);
    push_rules_rule_3827(rules);
    push_rules_rule_3828(rules);
    push_rules_rule_3829(rules);
    push_rules_rule_3830(rules);
    push_rules_rule_3831(rules);
    push_rules_rule_3832(rules);
    push_rules_rule_3833(rules);
    push_rules_rule_3834(rules);
    push_rules_rule_3835(rules);
    push_rules_rule_3836(rules);
    push_rules_rule_3837(rules);
    push_rules_rule_3838(rules);
    push_rules_rule_3839(rules);
    push_rules_rule_3840(rules);
    push_rules_rule_3841(rules);
    push_rules_rule_3842(rules);
    push_rules_rule_3843(rules);
    push_rules_rule_3844(rules);
    push_rules_rule_3845(rules);
    push_rules_rule_3846(rules);
    push_rules_rule_3847(rules);
    push_rules_rule_3848(rules);
    push_rules_rule_3849(rules);
    push_rules_rule_3850(rules);
    push_rules_rule_3851(rules);
    push_rules_rule_3852(rules);
    push_rules_rule_3853(rules);
    push_rules_rule_3854(rules);
    push_rules_rule_3855(rules);
    push_rules_rule_3856(rules);
    push_rules_rule_3857(rules);
    push_rules_rule_3858(rules);
    push_rules_rule_3859(rules);
    push_rules_rule_3860(rules);
    push_rules_rule_3861(rules);
    push_rules_rule_3862(rules);
    push_rules_rule_3863(rules);
    push_rules_rule_3864(rules);
    push_rules_rule_3865(rules);
    push_rules_rule_3866(rules);
    push_rules_rule_3867(rules);
    push_rules_rule_3868(rules);
    push_rules_rule_3869(rules);
    push_rules_rule_3870(rules);
    push_rules_rule_3871(rules);
    push_rules_rule_3872(rules);
    push_rules_rule_3873(rules);
    push_rules_rule_3874(rules);
    push_rules_rule_3875(rules);
    push_rules_rule_3876(rules);
    push_rules_rule_3877(rules);
    push_rules_rule_3878(rules);
    push_rules_rule_3879(rules);
    push_rules_rule_3880(rules);
    push_rules_rule_3881(rules);
    push_rules_rule_3882(rules);
    push_rules_rule_3883(rules);
    push_rules_rule_3884(rules);
    push_rules_rule_3885(rules);
    push_rules_rule_3886(rules);
    push_rules_rule_3887(rules);
    push_rules_rule_3888(rules);
    push_rules_rule_3889(rules);
    push_rules_rule_3890(rules);
    push_rules_rule_3891(rules);
    push_rules_rule_3892(rules);
    push_rules_rule_3893(rules);
    push_rules_rule_3894(rules);
    push_rules_rule_3895(rules);
    push_rules_rule_3896(rules);
    push_rules_rule_3897(rules);
    push_rules_rule_3898(rules);
    push_rules_rule_3899(rules);
    push_rules_rule_3900(rules);
    push_rules_rule_3901(rules);
    push_rules_rule_3902(rules);
    push_rules_rule_3903(rules);
    push_rules_rule_3904(rules);
    push_rules_rule_3905(rules);
    push_rules_rule_3906(rules);
    push_rules_rule_3907(rules);
    push_rules_rule_3908(rules);
    push_rules_rule_3909(rules);
    push_rules_rule_3910(rules);
    push_rules_rule_3911(rules);
    push_rules_rule_3912(rules);
    push_rules_rule_3913(rules);
    push_rules_rule_3914(rules);
    push_rules_rule_3915(rules);
    push_rules_rule_3916(rules);
    push_rules_rule_3917(rules);
    push_rules_rule_3918(rules);
    push_rules_rule_3919(rules);
    push_rules_rule_3920(rules);
    push_rules_rule_3921(rules);
    push_rules_rule_3922(rules);
    push_rules_rule_3923(rules);
    push_rules_rule_3924(rules);
    push_rules_rule_3925(rules);
}

fn push_rules_rule_3810(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3810,
        source: "Int[(a_+b_.*x_^n_)^p_.*Sin[c_.+d_.*x_],x_Symbol] :=
          Int[ExpandIntegrand[Sin[c+d*x],(a+b*x^n)^p,x],x] /;
        FreeQ[{a,b,c,d,n},x] && IGtQ[p,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, n_, p_, c__, d__, x_],
        optional: [b__, p_, c__, d__],
        when: { freeq!([a__, b__, c__, d__, n_], x_) && igtq!(p_, 0) },
        rhs: {
            let expanded = rubi_expand_integrand_product(
                &(&c__ + &d__ * x_).sin(),
                &(&a__ + &b__ * x_.pow(&n_)).pow(&p_),
                x_,
            );
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_3811(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3811,
        source: "Int[(a_+b_.*x_^n_)^p_.*Cos[c_.+d_.*x_],x_Symbol] :=
          Int[ExpandIntegrand[Cos[c+d*x],(a+b*x^n)^p,x],x] /;
        FreeQ[{a,b,c,d,n},x] && IGtQ[p,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [c__, d__, a__, b__, n_, p_, x_],
        optional: [c__, d__, b__, p_],
        when: { freeq!([a__, b__, c__, d__, n_], x_) && igtq!(p_, 0) },
        rhs: {
            let expanded = rubi_expand_integrand_product(
                &(&c__ + &d__ * x_).cos(),
                &(&a__ + &b__ * x_.pow(&n_)).pow(&p_),
                x_,
            );
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_3812(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3812,
        source: "Int[(a_+b_.*x_^n_)^p_*Sin[c_.+d_.*x_],x_Symbol] :=
          x^(-n+1)*(a+b*x^n)^(p+1)*Sin[c+d*x]/(b*n*(p+1)) -
          (-n+1)/(b*n*(p+1)) \\[Star] Int[x^(-n)*(a+b*x^n)^(p+1)*Sin[c+d*x],x] -
          d/(b*n*(p+1)) \\[Star] Int[x^(-n+1)*(a+b*x^n)^(p+1)*Cos[c+d*x],x] /;
        FreeQ[{a,b,c,d},x] && ILtQ[p,-1] && IGtQ[n,2]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, n_, p_, c__, d__, x_],
        optional: [b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_) && iltq!(p_, -1) && igtq!(n_, 2)
        },
        rhs: {
            let binomial = &a__ + &b__ * x_.pow(&n_);
            let angle = &c__ + &d__ * x_;
            let denominator = &b__ * &n_ * (&p_ + 1);
            let recursive1 = rubi_rhs_int(
                &(binomial.pow(&p_ + 1) * angle.sin() / x_.pow(&n_)),
                x_,
            );
            let recursive2 = rubi_rhs_int(
                &(x_.pow(-&n_ + 1) * binomial.pow(&p_ + 1) * angle.cos()),
                x_,
            );
            rubi_simp(&(x_.pow(-&n_ + 1) * binomial.pow(&p_ + 1) * angle.sin() / &denominator), x_)
                    + rubi_star((&n_ - 1) / &denominator, recursive1)
                    + rubi_star(-&d__ / denominator, recursive2)
        },
    ));
}

fn push_rules_rule_3813(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3813,
        source: "Int[(a_+b_.*x_^n_)^p_*Cos[c_.+d_.*x_],x_Symbol] :=
          x^(-n+1)*(a+b*x^n)^(p+1)*Cos[c+d*x]/(b*n*(p+1)) -
          (-n+1)/(b*n*(p+1)) \\[Star] Int[x^(-n)*(a+b*x^n)^(p+1)*Cos[c+d*x],x] +
          d/(b*n*(p+1)) \\[Star] Int[x^(-n+1)*(a+b*x^n)^(p+1)*Sin[c+d*x],x] /;
        FreeQ[{a,b,c,d},x] && ILtQ[p,-1] && IGtQ[n,2]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [c__, d__, a__, b__, n_, p_, x_],
        optional: [c__, d__, b__],
        when: {
            freeq!([a__, b__, c__, d__], x_) && iltq!(p_, -1) && igtq!(n_, 2)
        },
        rhs: {
            let binomial = &a__ + &b__ * x_.pow(&n_);
            let angle = &c__ + &d__ * x_;
            let denominator = &b__ * &n_ * (&p_ + 1);
            let recursive1 = rubi_rhs_int(
                &(binomial.pow(&p_ + 1) * angle.cos() / x_.pow(&n_)),
                x_,
            );
            let recursive2 = rubi_rhs_int(
                &(x_.pow(-&n_ + 1) * binomial.pow(&p_ + 1) * angle.sin()),
                x_,
            );
            rubi_simp(&(x_.pow(-&n_ + 1) * binomial.pow(&p_ + 1) * angle.cos() / &denominator), x_)
                    + rubi_star((&n_ - 1) / &denominator, recursive1)
                    + rubi_star(&d__ / denominator, recursive2)
        },
    ));
}

fn push_rules_rule_3814(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3814,
        source: "Int[(a_+b_.*x_^n_)^p_*Sin[c_.+d_.*x_],x_Symbol] :=
          Int[ExpandIntegrand[Sin[c+d*x],(a+b*x^n)^p,x],x] /;
        FreeQ[{a,b,c,d},x] && ILtQ[p,0] && IGtQ[n,0] && (EqQ[n,2] || EqQ[p,-1])",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
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
                &(&c__ + &d__ * x_).sin(),
                &(&a__ + &b__ * x_.pow(&n_)).pow(&p_),
                x_,
            );
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_3815(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3815,
        source: "Int[(a_+b_.*x_^n_)^p_*Cos[c_.+d_.*x_],x_Symbol] :=
          Int[ExpandIntegrand[Cos[c+d*x],(a+b*x^n)^p,x],x] /;
        FreeQ[{a,b,c,d},x] && ILtQ[p,0] && IGtQ[n,0] && (EqQ[n,2] || EqQ[p,-1])",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [c__, d__, a__, b__, n_, p_, x_],
        optional: [c__, d__, b__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && iltq!(p_, 0)
                && igtq!(n_, 0)
                && (eqq!(n_, 2) || eqq!(p_, -1))
        },
        rhs: {
            let expanded = rubi_expand_integrand_product(
                &(&c__ + &d__ * x_).cos(),
                &(&a__ + &b__ * x_.pow(&n_)).pow(&p_),
                x_,
            );
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_3816(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3816,
        source: "Int[(a_+b_.*x_^n_)^p_*Sin[c_.+d_.*x_],x_Symbol] :=
          Int[x^(n*p)*(b+a*x^(-n))^p*Sin[c+d*x],x] /;
        FreeQ[{a,b,c,d},x] && ILtQ[p,0] && ILtQ[n,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, n_, p_, c__, d__, x_],
        optional: [b__, c__, d__],
        when: { freeq!([a__, b__, c__, d__], x_) && iltq!(p_, 0) && iltq!(n_, 0) },
        rhs: {
            rubi_rhs_int(
                &(x_.pow(&n_ * &p_)
                    * (&b__ + &a__ / x_.pow(&n_)).pow(&p_)
                    * (&c__ + &d__ * x_).sin()),
                x_,
            )
        },
    ));
}

fn push_rules_rule_3817(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3817,
        source: "Int[(a_+b_.*x_^n_)^p_*Cos[c_.+d_.*x_],x_Symbol] :=
          Int[x^(n*p)*(b+a*x^(-n))^p*Cos[c+d*x],x] /;
        FreeQ[{a,b,c,d},x] && ILtQ[p,0] && ILtQ[n,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [c__, d__, a__, b__, n_, p_, x_],
        optional: [c__, d__, b__],
        when: { freeq!([a__, b__, c__, d__], x_) && iltq!(p_, 0) && iltq!(n_, 0) },
        rhs: {
            rubi_rhs_int(
                &(x_.pow(&n_ * &p_)
                    * (&b__ + &a__ / x_.pow(&n_)).pow(&p_)
                    * (&c__ + &d__ * x_).cos()),
                x_,
            )
        },
    ));
}

fn push_rules_rule_3818(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3818,
        source: "Int[(a_+b_.*x_^n_)^p_*Sin[c_.+d_.*x_],x_Symbol] :=
          Unintegrable[(a+b*x^n)^p*Sin[c+d*x],x] /;
        FreeQ[{a,b,c,d,n,p},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, n_, p_, c__, d__, x_],
        optional: [b__, c__, d__],
        when: { freeq!([a__, b__, c__, d__, n_, p_], x_) },
        rhs: {
            rubi_unintegrable(
                (&a__ + &b__ * x_.pow(&n_)).pow(&p_)
                    * (&c__ + &d__ * x_).sin(),
                x_,
            )
        },
    ));
}

fn push_rules_rule_3819(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3819,
        source: "Int[(a_+b_.*x_^n_)^p_*Cos[c_.+d_.*x_],x_Symbol] :=
          Unintegrable[(a+b*x^n)^p*Cos[c+d*x],x] /;
        FreeQ[{a,b,c,d,n,p},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [c__, d__, a__, b__, n_, p_, x_],
        optional: [c__, d__, b__],
        when: { freeq!([a__, b__, c__, d__, n_, p_], x_) },
        rhs: {
            rubi_unintegrable(
                (&a__ + &b__ * x_.pow(&n_)).pow(&p_)
                    * (&c__ + &d__ * x_).cos(),
                x_,
            )
        },
    ));
}

fn push_rules_rule_3820(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3820,
        source: "Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_.*Sin[c_.+d_.*x_],x_Symbol] :=
          Int[ExpandIntegrand[Sin[c+d*x],(e*x)^m*(a+b*x^n)^p,x],x] /;
        FreeQ[{a,b,c,d,e,m,n},x] && IGtQ[p,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_10(symbols),
        with: [e__, m_, a__, b__, n_, p_, c__, d__, x_],
        optional: [e__, m_, b__, p_, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_], x_) && igtq!(p_, 0)
        },
        rhs: {
            let product = (&e__ * x_).pow(&m_)
                * (&a__ + &b__ * x_.pow(&n_)).pow(&p_);
            let expanded = rubi_expand_integrand_product(
                &(&c__ + &d__ * x_).sin(),
                &product,
                x_,
            );
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_3821(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3821,
        source: "Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_.*Cos[c_.+d_.*x_],x_Symbol] :=
          Int[ExpandIntegrand[Cos[c+d*x],(e*x)^m*(a+b*x^n)^p,x],x] /;
        FreeQ[{a,b,c,d,e,m,n},x] && IGtQ[p,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [c__, d__, e__, m_, a__, b__, n_, p_, x_],
        optional: [c__, d__, e__, m_, b__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_], x_) && igtq!(p_, 0)
        },
        rhs: {
            let product = (&e__ * x_).pow(&m_)
                * (&a__ + &b__ * x_.pow(&n_)).pow(&p_);
            let expanded = rubi_expand_integrand_product(
                &(&c__ + &d__ * x_).cos(),
                &product,
                x_,
            );
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_3822(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3822,
        source: "Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_*Sin[c_.+d_.*x_],x_Symbol] :=
          e^m*(a+b*x^n)^(p+1)*Sin[c+d*x]/(b*n*(p+1)) -
          d*e^m/(b*n*(p+1)) \\[Star] Int[(a+b*x^n)^(p+1)*Cos[c+d*x],x] /;
        FreeQ[{a,b,c,d,e,m,n},x] && ILtQ[p,-1] && EqQ[m,n-1] && (IntegerQ[n] || GtQ[e,0])",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_10(symbols),
        with: [e__, m_, a__, b__, n_, p_, c__, d__, x_],
        optional: [e__, m_, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_], x_)
                && iltq!(p_, -1)
                && eqq!(m_, &n_ - 1)
                && (integerq!(n_) || gtq!(e__, 0))
        },
        rhs: {
            let binomial = &a__ + &b__ * x_.pow(&n_);
            let angle = &c__ + &d__ * x_;
            let denominator = &b__ * &n_ * (&p_ + 1);
            let recursive = rubi_rhs_int(&(binomial.pow(&p_ + 1) * angle.cos()), x_);
            rubi_simp(&(e__.pow(&m_) * binomial.pow(&p_ + 1) * angle.sin() / &denominator), x_)
                    + rubi_star(-&d__ * e__.pow(&m_) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_3823(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3823,
        source: "Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_*Cos[c_.+d_.*x_],x_Symbol] :=
          e^m*(a+b*x^n)^(p+1)*Cos[c+d*x]/(b*n*(p+1)) +
          d*e^m/(b*n*(p+1)) \\[Star] Int[(a+b*x^n)^(p+1)*Sin[c+d*x],x] /;
        FreeQ[{a,b,c,d,e,m,n},x] && ILtQ[p,-1] && EqQ[m,n-1] && (IntegerQ[n] || GtQ[e,0])",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [c__, d__, e__, m_, a__, b__, n_, p_, x_],
        optional: [c__, d__, e__, m_, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_], x_)
                && iltq!(p_, -1)
                && eqq!(m_, &n_ - 1)
                && (integerq!(n_) || gtq!(e__, 0))
        },
        rhs: {
            let binomial = &a__ + &b__ * x_.pow(&n_);
            let angle = &c__ + &d__ * x_;
            let denominator = &b__ * &n_ * (&p_ + 1);
            let recursive = rubi_rhs_int(&(binomial.pow(&p_ + 1) * angle.sin()), x_);
            rubi_simp(&(e__.pow(&m_) * binomial.pow(&p_ + 1) * angle.cos() / &denominator), x_)
                    + rubi_star(&d__ * e__.pow(&m_) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_3824(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3824,
        source: "Int[x_^m_.*(a_+b_.*x_^n_)^p_*Sin[c_.+d_.*x_],x_Symbol] :=
          x^(m-n+1)*(a+b*x^n)^(p+1)*Sin[c+d*x]/(b*n*(p+1)) -
          (m-n+1)/(b*n*(p+1)) \\[Star] Int[x^(m-n)*(a+b*x^n)^(p+1)*Sin[c+d*x],x] -
          d/(b*n*(p+1)) \\[Star] Int[x^(m-n+1)*(a+b*x^n)^(p+1)*Cos[c+d*x],x] /;
        FreeQ[{a,b,c,d,m},x] && ILtQ[p,-1] && IGtQ[n,0] && (GtQ[m-n+1,0] || GtQ[n,2]) && RationalQ[m]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_19(symbols),
        with: [m_, a__, b__, n_, p_, c__, d__, x_],
        optional: [m_, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, m_], x_)
                && iltq!(p_, -1)
                && igtq!(n_, 0)
                && (gtq!(&m_ - &n_ + 1, 0) || gtq!(n_, 2))
                && rationalq!(m_)
        },
        rhs: {
            let binomial = &a__ + &b__ * x_.pow(&n_);
            let angle = &c__ + &d__ * x_;
            let denominator = &b__ * &n_ * (&p_ + 1);
            let recursive1 = rubi_rhs_int(
                &(x_.pow(&m_ - &n_) * binomial.pow(&p_ + 1) * angle.sin()),
                x_,
            );
            let recursive2 = rubi_rhs_int(
                &(x_.pow(&m_ - &n_ + 1) * binomial.pow(&p_ + 1) * angle.cos()),
                x_,
            );
            rubi_simp(&(x_.pow(&m_ - &n_ + 1) * binomial.pow(&p_ + 1) * angle.sin()
                    / &denominator), x_)
                    + rubi_star(-(&m_ - &n_ + 1) / &denominator, recursive1)
                    + rubi_star(-&d__ / denominator, recursive2)
        },
    ));
}

fn push_rules_rule_3825(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3825,
        source: "Int[x_^m_.*(a_+b_.*x_^n_)^p_*Cos[c_.+d_.*x_],x_Symbol] :=
          x^(m-n+1)*(a+b*x^n)^(p+1)*Cos[c+d*x]/(b*n*(p+1)) -
          (m-n+1)/(b*n*(p+1)) \\[Star] Int[x^(m-n)*(a+b*x^n)^(p+1)*Cos[c+d*x],x] +
          d/(b*n*(p+1)) \\[Star] Int[x^(m-n+1)*(a+b*x^n)^(p+1)*Sin[c+d*x],x] /;
        FreeQ[{a,b,c,d,m},x] && ILtQ[p,-1] && IGtQ[n,0] && (GtQ[m-n+1,0] || GtQ[n,2]) && RationalQ[m]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [c__, d__, m_, a__, b__, n_, p_, x_],
        optional: [c__, d__, m_, b__],
        when: {
            freeq!([a__, b__, c__, d__, m_], x_)
                && iltq!(p_, -1)
                && igtq!(n_, 0)
                && (gtq!(&m_ - &n_ + 1, 0) || gtq!(n_, 2))
                && rationalq!(m_)
        },
        rhs: {
            let binomial = &a__ + &b__ * x_.pow(&n_);
            let angle = &c__ + &d__ * x_;
            let denominator = &b__ * &n_ * (&p_ + 1);
            let recursive1 = rubi_rhs_int(
                &(x_.pow(&m_ - &n_) * binomial.pow(&p_ + 1) * angle.cos()),
                x_,
            );
            let recursive2 = rubi_rhs_int(
                &(x_.pow(&m_ - &n_ + 1) * binomial.pow(&p_ + 1) * angle.sin()),
                x_,
            );
            rubi_simp(&(x_.pow(&m_ - &n_ + 1) * binomial.pow(&p_ + 1) * angle.cos()
                    / &denominator), x_)
                    + rubi_star(-(&m_ - &n_ + 1) / &denominator, recursive1)
                    + rubi_star(&d__ / denominator, recursive2)
        },
    ));
}

fn push_rules_rule_3826(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3826,
        source: "Int[x_^m_.*(a_+b_.*x_^n_)^p_*Sin[c_.+d_.*x_],x_Symbol] :=
          Int[ExpandIntegrand[Sin[c+d*x],x^m*(a+b*x^n)^p,x],x] /;
        FreeQ[{a,b,c,d,m},x] && ILtQ[p,0] && IGtQ[n,0] && (EqQ[n,2] || EqQ[p,-1]) && IntegerQ[m]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_19(symbols),
        with: [m_, a__, b__, n_, p_, c__, d__, x_],
        optional: [m_, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, m_], x_)
                && iltq!(p_, 0)
                && igtq!(n_, 0)
                && (eqq!(n_, 2) || eqq!(p_, -1))
                && integerq!(m_)
        },
        rhs: {
            let product = x_.pow(&m_)
                * (&a__ + &b__ * x_.pow(&n_)).pow(&p_);
            let expanded = rubi_expand_integrand_product(
                &(&c__ + &d__ * x_).sin(),
                &product,
                x_,
            );
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_3827(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3827,
        source: "Int[x_^m_.*(a_+b_.*x_^n_)^p_*Cos[c_.+d_.*x_],x_Symbol] :=
          Int[ExpandIntegrand[Cos[c+d*x],x^m*(a+b*x^n)^p,x],x] /;
        FreeQ[{a,b,c,d,m},x] && ILtQ[p,0] && IGtQ[n,0] && (EqQ[n,2] || EqQ[p,-1]) && IntegerQ[m]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [c__, d__, m_, a__, b__, n_, p_, x_],
        optional: [c__, d__, m_, b__],
        when: {
            freeq!([a__, b__, c__, d__, m_], x_)
                && iltq!(p_, 0)
                && igtq!(n_, 0)
                && (eqq!(n_, 2) || eqq!(p_, -1))
                && integerq!(m_)
        },
        rhs: {
            let product = x_.pow(&m_)
                * (&a__ + &b__ * x_.pow(&n_)).pow(&p_);
            let expanded = rubi_expand_integrand_product(
                &(&c__ + &d__ * x_).cos(),
                &product,
                x_,
            );
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_3828(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3828,
        source: "Int[x_^m_.*(a_+b_.*x_^n_)^p_*Sin[c_.+d_.*x_],x_Symbol] :=
          Int[x^(m+n*p)*(b+a*x^(-n))^p*Sin[c+d*x],x] /;
        FreeQ[{a,b,c,d,m},x] && ILtQ[p,0] && ILtQ[n,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_19(symbols),
        with: [m_, a__, b__, n_, p_, c__, d__, x_],
        optional: [m_, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, m_], x_) && iltq!(p_, 0) && iltq!(n_, 0)
        },
        rhs: {
            rubi_rhs_int(
                &(x_.pow(&m_ + &n_ * &p_)
                    * (&b__ + &a__ / x_.pow(&n_)).pow(&p_)
                    * (&c__ + &d__ * x_).sin()),
                x_,
            )
        },
    ));
}

fn push_rules_rule_3829(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3829,
        source: "Int[x_^m_.*(a_+b_.*x_^n_)^p_*Cos[c_.+d_.*x_],x_Symbol] :=
          Int[x^(m+n*p)*(b+a*x^(-n))^p*Cos[c+d*x],x] /;
        FreeQ[{a,b,c,d,m},x] && ILtQ[p,0] && ILtQ[n,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [c__, d__, m_, a__, b__, n_, p_, x_],
        optional: [c__, d__, m_, b__],
        when: {
            freeq!([a__, b__, c__, d__, m_], x_) && iltq!(p_, 0) && iltq!(n_, 0)
        },
        rhs: {
            rubi_rhs_int(
                &(x_.pow(&m_ + &n_ * &p_)
                    * (&b__ + &a__ / x_.pow(&n_)).pow(&p_)
                    * (&c__ + &d__ * x_).cos()),
                x_,
            )
        },
    ));
}

fn push_rules_rule_3830(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3830,
        source: "Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_.*Sin[c_.+d_.*x_],x_Symbol] :=
          Unintegrable[(e*x)^m*(a+b*x^n)^p*Sin[c+d*x],x] /;
        FreeQ[{a,b,c,d,e,m,n,p},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_10(symbols),
        with: [e__, m_, a__, b__, n_, p_, c__, d__, x_],
        optional: [e__, m_, b__, p_, c__, d__],
        when: { freeq!([a__, b__, c__, d__, e__, m_, n_, p_], x_) },
        rhs: {
            rubi_unintegrable(
                (&e__ * x_).pow(&m_)
                    * (&a__ + &b__ * x_.pow(&n_)).pow(&p_)
                    * (&c__ + &d__ * x_).sin(),
                x_,
            )
        },
    ));
}

fn push_rules_rule_3831(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3831,
        source: "Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_.*Cos[c_.+d_.*x_],x_Symbol] :=
          Unintegrable[(e*x)^m*(a+b*x^n)^p*Cos[c+d*x],x] /;
        FreeQ[{a,b,c,d,e,m,n,p},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [c__, d__, e__, m_, a__, b__, n_, p_, x_],
        optional: [c__, d__, e__, m_, b__, p_],
        when: { freeq!([a__, b__, c__, d__, e__, m_, n_, p_], x_) },
        rhs: {
            rubi_unintegrable(
                (&e__ * x_).pow(&m_)
                    * (&a__ + &b__ * x_.pow(&n_)).pow(&p_)
                    * (&c__ + &d__ * x_).cos(),
                x_,
            )
        },
    ));
}

fn push_rules_rule_3832(rules: &mut Vec<RubiRule>) {
    rubi_symb!(d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 3832,
        source: "Int[Sin[d_.*(e_.+f_.*x_)^2],x_Symbol] :=
          Sqrt[Pi/2]/(f*Rt[d,2])*FresnelS[Sqrt[2/Pi]*Rt[d,2]*(e+f*x)] /;
        FreeQ[{d,e,f},x]",
        desc: "Primitive rule",
        refs: [],
        pattern: (d__ * (e__ + f__ * x_).pow(2)).sin(),
        with: [d__, e__, f__, x_],
        optional: [d__, e__, f__],
        when: {
            freeq!([d__, e__, f__], x_)
        },
        rhs: {
            let pi = Atom::var(Symbol::PI);
            let rt = rubi_rt(&d__, 2);
            let argument = (Atom::num(2) / &pi).sqrt() * &rt * (&e__ + &f__ * x_);

            rubi_simp(&((&pi / 2).sqrt() * rubi_fresnel_s(argument) / (&f__ * rt)), x_)
        },
    ));
}

fn push_rules_rule_3833(rules: &mut Vec<RubiRule>) {
    rubi_symb!(d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 3833,
        source: "Int[Cos[d_.*(e_.+f_.*x_)^2],x_Symbol] :=
          Sqrt[Pi/2]/(f*Rt[d,2])*FresnelC[Sqrt[2/Pi]*Rt[d,2]*(e+f*x)] /;
        FreeQ[{d,e,f},x]",
        desc: "Primitive rule",
        refs: [],
        pattern: (d__ * (e__ + f__ * x_).pow(2)).cos(),
        with: [d__, e__, f__, x_],
        optional: [d__, e__, f__],
        when: {
            freeq!([d__, e__, f__], x_)
        },
        rhs: {
            let pi = Atom::var(Symbol::PI);
            let rt = rubi_rt(&d__, 2);
            let argument = (Atom::num(2) / &pi).sqrt() * &rt * (&e__ + &f__ * x_);

            rubi_simp(&((&pi / 2).sqrt() * rubi_fresnel_c(argument) / (&f__ * rt)), x_)
        },
    ));
}

fn push_rules_rule_3834(rules: &mut Vec<RubiRule>) {
    rubi_symb!(c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 3834,
        source: "Int[Sin[c_+d_.*(e_.+f_.*x_)^2],x_Symbol] :=
          Sin[c] \\[Star] Int[Cos[d*(e+f*x)^2],x] + Cos[c] \\[Star] Int[Sin[d*(e+f*x)^2],x] /;
        FreeQ[{c,d,e,f},x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (c__ + d__ * (e__ + f__ * x_).pow(2)).sin(),
        with: [c__, d__, e__, f__, x_],
        optional: [d__, e__, f__],
        when: {
            freeq!([c__, d__, e__, f__], x_)
        },
        rhs: {
            let quadratic = &d__ * (&e__ + &f__ * x_).pow(2);
            let recursive1 = rubi_rhs_int(&quadratic.cos(), x_);
            let recursive2 = rubi_rhs_int(&quadratic.sin(), x_);

            rubi_star(c__.sin(), recursive1)
                    + rubi_star(c__.cos(), recursive2)
        },
    ));
}

fn push_rules_rule_3835(rules: &mut Vec<RubiRule>) {
    rubi_symb!(c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 3835,
        source: "Int[Cos[c_+d_.*(e_.+f_.*x_)^2],x_Symbol] :=
          Cos[c] \\[Star] Int[Cos[d*(e+f*x)^2],x] - Sin[c] \\[Star] Int[Sin[d*(e+f*x)^2],x] /;
        FreeQ[{c,d,e,f},x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (c__ + d__ * (e__ + f__ * x_).pow(2)).cos(),
        with: [c__, d__, e__, f__, x_],
        optional: [d__, e__, f__],
        when: {
            freeq!([c__, d__, e__, f__], x_)
        },
        rhs: {
            let quadratic = &d__ * (&e__ + &f__ * x_).pow(2);
            let recursive1 = rubi_rhs_int(&quadratic.cos(), x_);
            let recursive2 = rubi_rhs_int(&quadratic.sin(), x_);

            rubi_star(c__.cos(), recursive1)
                    + rubi_star(-c__.sin(), recursive2)
        },
    ));
}

fn push_rules_rule_3836(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; c__, d__, e__, f__, n_, x_);
    rules.push(rubi_rule!(
        order: 3836,
        source: "Int[Sin[c_.+d_.*(e_.+f_.*x_)^n_],x_Symbol] :=
          I/2 \\[Star] Int[E^(-c*I-d*I*(e+f*x)^n),x] - I/2 \\[Star] Int[E^(c*I+d*I*(e+f*x)^n),x] /;
        FreeQ[{c,d,e,f},x] && IGtQ[n,2]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [c__, d__, e__, f__, n_, x_],
        optional: [c__, d__, e__, f__],
        when: {
            freeq!([c__, d__, e__, f__], x_) && igtq!(n_, 2)
        },
        rhs: {
            let i = rubi_i();
            let affine_power = (&e__ + &f__ * x_).pow(&n_);
            let recursive1 =
                rubi_rhs_int(&(-&c__ * &i - &d__ * &i * &affine_power).exp(), x_);
            let recursive2 =
                rubi_rhs_int(&(&c__ * &i + &d__ * &i * affine_power).exp(), x_);

            rubi_star(&i / 2, recursive1)
                    + rubi_star(-i / 2, recursive2)
        },
    ));
}

fn push_rules_rule_3837(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; c__, d__, e__, f__, n_, x_);
    rules.push(rubi_rule!(
        order: 3837,
        source: "Int[Cos[c_.+d_.*(e_.+f_.*x_)^n_],x_Symbol] :=
          1/2 \\[Star] Int[E^(-c*I-d*I*(e+f*x)^n),x] + 1/2 \\[Star] Int[E^(c*I+d*I*(e+f*x)^n),x] /;
        FreeQ[{c,d,e,f},x] && IGtQ[n,2]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [c__, d__, e__, f__, n_, x_],
        optional: [c__, d__, e__, f__],
        when: {
            freeq!([c__, d__, e__, f__], x_) && igtq!(n_, 2)
        },
        rhs: {
            let i = rubi_i();
            let affine_power = (&e__ + &f__ * x_).pow(&n_);
            let recursive1 =
                rubi_rhs_int(&(-&c__ * &i - &d__ * &i * &affine_power).exp(), x_);
            let recursive2 =
                rubi_rhs_int(&(&c__ * &i + &d__ * &i * affine_power).exp(), x_);

            rubi_star(Atom::num(1) / 2, recursive1)
                    + rubi_star(Atom::num(1) / 2, recursive2)
        },
    ));
}

fn push_rules_rule_3838(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3838,
        source: "Int[(a_.+b_.*Sin[c_.+d_.*(e_.+f_.*x_)^n_])^p_,x_Symbol] :=
          Int[ExpandTrigReduce[(a+b*Sin[c+d*(e+f*x)^n])^p,x],x] /;
        FreeQ[{a,b,c,d,e,f},x] && IGtQ[p,1] && IGtQ[n,1]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, e__, f__, n_, p_, x_],
        optional: [a__, b__, c__, d__, e__, f__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && igtq!(p_, 1)
                && igtq!(n_, 1)
        },
        rhs: {
            let integrand = (&a__ + &b__ * (&c__ + &d__ * (&e__ + &f__ * x_).pow(&n_)).sin()).pow(&p_);
            let expanded = rubi_expand_trig_reduce_one(&integrand, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_3839(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3839,
        source: "Int[(a_.+b_.*Cos[c_.+d_.*(e_.+f_.*x_)^n_])^p_,x_Symbol] :=
          Int[ExpandTrigReduce[(a+b*Cos[c+d*(e+f*x)^n])^p,x],x] /;
        FreeQ[{a,b,c,d,e,f},x] && IGtQ[p,1] && IGtQ[n,1]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, e__, f__, n_, p_, x_],
        optional: [a__, b__, c__, d__, e__, f__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && igtq!(p_, 1)
                && igtq!(n_, 1)
        },
        rhs: {
            let integrand = (&a__ + &b__ * (&c__ + &d__ * (&e__ + &f__ * x_).pow(&n_)).cos()).pow(&p_);
            let expanded = rubi_expand_trig_reduce_one(&integrand, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_3840(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3840,
        source: "Int[(a_.+b_.*Sin[c_.+d_.*(e_.+f_.*x_)^n_])^p_.,x_Symbol] :=
          -1/f \\[Star] Subst[Int[(a+b*Sin[c+d*x^(-n)])^p/x^2,x],x,1/(e+f*x)] /;
        FreeQ[{a,b,c,d,e,f},x] && IGtQ[p,0] && ILtQ[n,0] && EqQ[n,-2]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, e__, f__, n_, p_, x_],
        optional: [a__, b__, c__, d__, e__, f__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && igtq!(p_, 0)
                && iltq!(n_, 0)
                && eqq!(n_, -2)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub = Atom::var(substitution_symbol);
            let transformed_integrand =
                (&a__ + &b__ * (&c__ + &d__ * sub.pow(-&n_)).sin()).pow(&p_) / sub.pow(2);
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);
            rubi_star(-f__.pow(-1), rubi_subst(
                    &transformed,
                    substitution_symbol,
                    Atom::num(1) / (&e__ + &f__ * x_),
                ))
        },
    ));
}

fn push_rules_rule_3841(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3841,
        source: "Int[(a_.+b_.*Cos[c_.+d_.*(e_.+f_.*x_)^n_])^p_.,x_Symbol] :=
          -1/f \\[Star] Subst[Int[(a+b*Cos[c+d*x^(-n)])^p/x^2,x],x,1/(e+f*x)] /;
        FreeQ[{a,b,c,d,e,f},x] && IGtQ[p,0] && ILtQ[n,0] && EqQ[n,-2]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, e__, f__, n_, p_, x_],
        optional: [a__, b__, c__, d__, e__, f__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && igtq!(p_, 0)
                && iltq!(n_, 0)
                && eqq!(n_, -2)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub = Atom::var(substitution_symbol);
            let transformed_integrand =
                (&a__ + &b__ * (&c__ + &d__ * sub.pow(-&n_)).cos()).pow(&p_) / sub.pow(2);
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);
            rubi_star(-f__.pow(-1), rubi_subst(
                    &transformed,
                    substitution_symbol,
                    Atom::num(1) / (&e__ + &f__ * x_),
                ))
        },
    ));
}

fn push_rules_rule_3842(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3842,
        source: "Int[(a_.+b_.*Sin[c_.+d_.*(e_.+f_.*x_)^n_])^p_.,x_Symbol] :=
          1/(n*f) \\[Star] Subst[Int[x^(1/n-1)*(a+b*Sin[c+d*x])^p,x],x,(e+f*x)^n] /;
        FreeQ[{a,b,c,d,e,f},x] && IGtQ[p,0] && IntegerQ[1/n]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, e__, f__, n_, p_, x_],
        optional: [a__, b__, c__, d__, e__, f__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && igtq!(p_, 0)
                && integerq!(Atom::num(1) / &n_)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub = Atom::var(substitution_symbol);
            let transformed_integrand = sub.pow(Atom::num(1) / &n_ - 1)
                * (&a__ + &b__ * (&c__ + &d__ * &sub).sin()).pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);
            rubi_star(Atom::num(1) / (&n_ * &f__), rubi_subst(
                    &transformed,
                    substitution_symbol,
                    (&e__ + &f__ * x_).pow(&n_),
                ))
        },
    ));
}

fn push_rules_rule_3843(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3843,
        source: "Int[(a_.+b_.*Cos[c_.+d_.*(e_.+f_.*x_)^n_])^p_.,x_Symbol] :=
          1/(n*f) \\[Star] Subst[Int[x^(1/n-1)*(a+b*Cos[c+d*x])^p,x],x,(e+f*x)^n] /;
        FreeQ[{a,b,c,d,e,f},x] && IGtQ[p,0] && IntegerQ[1/n]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, e__, f__, n_, p_, x_],
        optional: [a__, b__, c__, d__, e__, f__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && igtq!(p_, 0)
                && integerq!(Atom::num(1) / &n_)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub = Atom::var(substitution_symbol);
            let transformed_integrand = sub.pow(Atom::num(1) / &n_ - 1)
                * (&a__ + &b__ * (&c__ + &d__ * &sub).cos()).pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);
            rubi_star(Atom::num(1) / (&n_ * &f__), rubi_subst(
                    &transformed,
                    substitution_symbol,
                    (&e__ + &f__ * x_).pow(&n_),
                ))
        },
    ));
}

fn push_rules_rule_3844(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3844,
        source: "Int[(a_.+b_.*Sin[c_.+d_.*(e_.+f_.*x_)^n_])^p_.,x_Symbol] :=
          Module[{k=Denominator[n]},
          k/f \\[Star] Subst[Int[x^(k-1)*(a+b*Sin[c+d*x^(k*n)])^p,x],x,(e+f*x)^(1/k)]] /;
        FreeQ[{a,b,c,d,e,f},x] && IGtQ[p,0] && FractionQ[n]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, e__, f__, n_, p_, x_],
        optional: [a__, b__, c__, d__, e__, f__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && igtq!(p_, 0)
                && fractionq!(n_)
        },
        rhs: {
            let k_i = rubi_denominator(&n_).rubi_rhs();
            let k = Atom::num(k_i);
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub = Atom::var(substitution_symbol);
            let transformed_integrand = sub.pow(&k - 1)
                * (&a__ + &b__ * (&c__ + &d__ * sub.pow(&k * &n_)).sin()).pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);
            rubi_star(&k / &f__, rubi_subst(
                    &transformed,
                    substitution_symbol,
                    (&e__ + &f__ * x_).pow(Atom::num(1) / k_i),
                ))
        },
    ));
}

fn push_rules_rule_3845(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3845,
        source: "Int[(a_.+b_.*Cos[c_.+d_.*(e_.+f_.*x_)^n_])^p_.,x_Symbol] :=
          Module[{k=Denominator[n]},
          k/f \\[Star] Subst[Int[x^(k-1)*(a+b*Cos[c+d*x^(k*n)])^p,x],x,(e+f*x)^(1/k)]] /;
        FreeQ[{a,b,c,d,e,f},x] && IGtQ[p,0] && FractionQ[n]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, e__, f__, n_, p_, x_],
        optional: [a__, b__, c__, d__, e__, f__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && igtq!(p_, 0)
                && fractionq!(n_)
        },
        rhs: {
            let k_i = rubi_denominator(&n_).rubi_rhs();
            let k = Atom::num(k_i);
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub = Atom::var(substitution_symbol);
            let transformed_integrand = sub.pow(&k - 1)
                * (&a__ + &b__ * (&c__ + &d__ * sub.pow(&k * &n_)).cos()).pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);
            rubi_star(&k / &f__, rubi_subst(
                    &transformed,
                    substitution_symbol,
                    (&e__ + &f__ * x_).pow(Atom::num(1) / k_i),
                ))
        },
    ));
}

fn push_rules_rule_3846(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; c__, d__, e__, f__, n_, x_);
    rules.push(rubi_rule!(
        order: 3846,
        source: "Int[Sin[c_.+d_.*(e_.+f_.*x_)^n_],x_Symbol] :=
          I/2 \\[Star] Int[E^(-c*I-d*I*(e+f*x)^n),x] - I/2 \\[Star] Int[E^(c*I+d*I*(e+f*x)^n),x] /;
        FreeQ[{c,d,e,f,n},x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [c__, d__, e__, f__, n_, x_],
        optional: [c__, d__, e__, f__],
        when: { freeq!([c__, d__, e__, f__, n_], x_) },
        rhs: {
            let i = rubi_i();
            let affine_power = (&e__ + &f__ * x_).pow(&n_);
            let recursive1 =
                rubi_rhs_int(&(-&c__ * &i - &d__ * &i * &affine_power).exp(), x_);
            let recursive2 =
                rubi_rhs_int(&(&c__ * &i + &d__ * &i * affine_power).exp(), x_);

            rubi_star(&i / 2, recursive1)
                    + rubi_star(-i / 2, recursive2)
        },
    ));
}

fn push_rules_rule_3847(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; c__, d__, e__, f__, n_, x_);
    rules.push(rubi_rule!(
        order: 3847,
        source: "Int[Cos[c_.+d_.*(e_.+f_.*x_)^n_],x_Symbol] :=
          1/2 \\[Star] Int[E^(-c*I-d*I*(e+f*x)^n),x] + 1/2 \\[Star] Int[E^(c*I+d*I*(e+f*x)^n),x] /;
        FreeQ[{c,d,e,f,n},x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [c__, d__, e__, f__, n_, x_],
        optional: [c__, d__, e__, f__],
        when: { freeq!([c__, d__, e__, f__, n_], x_) },
        rhs: {
            let i = rubi_i();
            let affine_power = (&e__ + &f__ * x_).pow(&n_);
            let recursive1 =
                rubi_rhs_int(&(-&c__ * &i - &d__ * &i * &affine_power).exp(), x_);
            let recursive2 =
                rubi_rhs_int(&(&c__ * &i + &d__ * &i * affine_power).exp(), x_);

            rubi_star(Atom::num(1) / 2, recursive1)
                    + rubi_star(Atom::num(1) / 2, recursive2)
        },
    ));
}

fn push_rules_rule_3848(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3848,
        source: "Int[(a_.+b_.*Sin[c_.+d_.*(e_.+f_.*x_)^n_])^p_,x_Symbol] :=
          Int[ExpandTrigReduce[(a+b*Sin[c+d*(e+f*x)^n])^p,x],x] /;
        FreeQ[{a,b,c,d,e,f,n},x] && IGtQ[p,1]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, e__, f__, n_, p_, x_],
        optional: [a__, b__, c__, d__, e__, f__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, n_], x_)
                && igtq!(p_, 1)
        },
        rhs: {
            let integrand = (&a__ + &b__ * (&c__ + &d__ * (&e__ + &f__ * x_).pow(&n_)).sin()).pow(&p_);
            let expanded = rubi_expand_trig_reduce_one(&integrand, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_3849(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3849,
        source: "Int[(a_.+b_.*Cos[c_.+d_.*(e_.+f_.*x_)^n_])^p_,x_Symbol] :=
          Int[ExpandTrigReduce[(a+b*Cos[c+d*(e+f*x)^n])^p,x],x] /;
        FreeQ[{a,b,c,d,e,f,n},x] && IGtQ[p,1]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, e__, f__, n_, p_, x_],
        optional: [a__, b__, c__, d__, e__, f__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, n_], x_)
                && igtq!(p_, 1)
        },
        rhs: {
            let integrand = (&a__ + &b__ * (&c__ + &d__ * (&e__ + &f__ * x_).pow(&n_)).cos()).pow(&p_);
            let expanded = rubi_expand_trig_reduce_one(&integrand, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_3850(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3850,
        source: "Int[(a_.+b_.*Sin[c_.+d_.*(e_.+f_.*x_)^n_])^p_,x_Symbol] :=
          Unintegrable[(a+b*Sin[c+d*(e+f*x)^n])^p,x] /;
        FreeQ[{a,b,c,d,e,f,n,p},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, e__, f__, n_, p_, x_],
        optional: [a__, b__, c__, d__, e__, f__],
        when: { freeq!([a__, b__, c__, d__, e__, f__, n_, p_], x_) },
        rhs: {
            let integrand = (&a__ + &b__ * (&c__ + &d__ * (&e__ + &f__ * x_).pow(&n_)).sin()).pow(&p_);
            rubi_unintegrable(integrand, x_)
        },
    ));
}

fn push_rules_rule_3851(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 3851,
        source: "Int[(a_.+b_.*Cos[c_.+d_.*(e_.+f_.*x_)^n_])^p_,x_Symbol] :=
          Unintegrable[(a+b*Cos[c+d*(e+f*x)^n])^p,x] /;
        FreeQ[{a,b,c,d,e,f,n,p},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, e__, f__, n_, p_, x_],
        optional: [a__, b__, c__, d__, e__, f__],
        when: { freeq!([a__, b__, c__, d__, e__, f__, n_, p_], x_) },
        rhs: {
            let integrand = (&a__ + &b__ * (&c__ + &d__ * (&e__ + &f__ * x_).pow(&n_)).cos()).pow(&p_);
            rubi_unintegrable(integrand, x_)
        },
    ));
}

fn push_rules_rule_3852(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, n_, p_, u_);
    rules.push(rubi_rule!(
        order: 3852,
        source: "Int[(a_.+b_.*Sin[c_.+d_.*u_^n_])^p_.,x_Symbol] :=
          Int[(a+b*Sin[c+d*ExpandToSum[u,x]^n])^p,x] /;
        FreeQ[{a,b,c,d,n,p},x] && LinearQ[u,x] && Not[LinearMatchQ[u,x]]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: (a__ + b__ * (c__ + d__ * u_.pow(n_)).sin()).pow(p_),
        with: [a__, b__, c__, d__, u_, n_, p_, x_],
        optional: [a__, b__, c__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__, n_, p_], x_)
                && rubi_linear_q(&u_, x_)
                && !rubi_linear_match_q(&u_, x_)
        },
        rhs: {
            let expanded_u = rubi_expand_to_sum(&u_, x_);
            let integrand =
                (&a__ + &b__ * (&c__ + &d__ * expanded_u.pow(&n_)).sin()).pow(&p_);
            rubi_rhs_int(&integrand, x_)
        },
    ));
}

fn push_rules_rule_3853(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, n_, p_, u_);
    rules.push(rubi_rule!(
        order: 3853,
        source: "Int[(a_.+b_.*Cos[c_.+d_.*u_^n_])^p_.,x_Symbol] :=
          Int[(a+b*Cos[c+d*ExpandToSum[u,x]^n])^p,x] /;
        FreeQ[{a,b,c,d,n,p},x] && LinearQ[u,x] && Not[LinearMatchQ[u,x]]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: (a__ + b__ * (c__ + d__ * u_.pow(n_)).cos()).pow(p_),
        with: [a__, b__, c__, d__, u_, n_, p_, x_],
        optional: [a__, b__, c__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__, n_, p_], x_)
                && rubi_linear_q(&u_, x_)
                && !rubi_linear_match_q(&u_, x_)
        },
        rhs: {
            let expanded_u = rubi_expand_to_sum(&u_, x_);
            let integrand =
                (&a__ + &b__ * (&c__ + &d__ * expanded_u.pow(&n_)).cos()).pow(&p_);
            rubi_rhs_int(&integrand, x_)
        },
    ));
}

fn push_rules_rule_3854(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, p_, u_);
    rules.push(rubi_rule!(
        order: 3854,
        source: "Int[(a_.+b_.*Sin[u_])^p_.,x_Symbol] :=
          Int[(a+b*Sin[ExpandToSum[u,x]])^p,x] /;
        FreeQ[{a,b,p},x] && BinomialQ[u,x] && Not[BinomialMatchQ[u,x]]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: (a__ + b__ * (Atom::var(u_)).sin()).pow(p_),
        with: [a__, b__, u_, p_, x_],
        optional: [a__, b__, p_],
        when: {
            freeq!([a__, b__, p_], x_)
                && rubi_binomial_q(&u_, x_)
                && !rubi_binomial_match_q(&u_, x_)
        },
        rhs: {
            let integrand = (&a__ + &b__ * rubi_expand_to_sum(&u_, x_).sin()).pow(&p_);
            rubi_rhs_int(&integrand, x_)
        },
    ));
}

fn push_rules_rule_3855(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, p_, u_);
    rules.push(rubi_rule!(
        order: 3855,
        source: "Int[(a_.+b_.*Cos[u_])^p_.,x_Symbol] :=
          Int[(a+b*Cos[ExpandToSum[u,x]])^p,x] /;
        FreeQ[{a,b,p},x] && BinomialQ[u,x] && Not[BinomialMatchQ[u,x]]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: (a__ + b__ * (Atom::var(u_)).cos()).pow(p_),
        with: [a__, b__, u_, p_, x_],
        optional: [a__, b__, p_],
        when: {
            freeq!([a__, b__, p_], x_)
                && rubi_binomial_q(&u_, x_)
                && !rubi_binomial_match_q(&u_, x_)
        },
        rhs: {
            let integrand = (&a__ + &b__ * rubi_expand_to_sum(&u_, x_).cos()).pow(&p_);
            rubi_rhs_int(&integrand, x_)
        },
    ));
}

fn push_rules_rule_3856(rules: &mut Vec<RubiRule>) {
    rubi_symb!(d__, n_, x_);
    rules.push(rubi_rule!(
        order: 3856,
        source: "Int[Sin[d_.*x_^n_]/x_,x_Symbol] :=
          SinIntegral[d*x^n]/n /;
        FreeQ[{d,n},x]",
        desc: "Primitive rule",
        refs: [],
        pattern: (d__ * x_.pow(n_)).sin() / x_,
        with: [d__, n_, x_],
        optional: [d__],
        when: { freeq!([d__, n_], x_) },
        rhs: {
            rubi_simp(&(rubi_sin_integral(&d__ * x_.pow(&n_)) / &n_), x_)
        },
    ));
}

fn push_rules_rule_3857(rules: &mut Vec<RubiRule>) {
    rubi_symb!(d__, n_, x_);
    rules.push(rubi_rule!(
        order: 3857,
        source: "Int[Cos[d_.*x_^n_]/x_,x_Symbol] :=
          CosIntegral[d*x^n]/n /;
        FreeQ[{d,n},x]",
        desc: "Primitive rule",
        refs: [],
        pattern: (d__ * x_.pow(n_)).cos() / x_,
        with: [d__, n_, x_],
        optional: [d__],
        when: { freeq!([d__, n_], x_) },
        rhs: {
            rubi_simp(&(rubi_cos_integral(&d__ * x_.pow(&n_)) / &n_), x_)
        },
    ));
}

fn push_rules_rule_3858(rules: &mut Vec<RubiRule>) {
    rubi_symb!(c__, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 3858,
        source: "Int[Sin[c_+d_.*x_^n_]/x_,x_Symbol] :=
          Sin[c] \\[Star] Int[Cos[d*x^n]/x,x] + Cos[c] \\[Star] Int[Sin[d*x^n]/x,x] /;
        FreeQ[{c,d,n},x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (c__ + d__ * x_.pow(n_)).sin() / x_,
        with: [c__, d__, n_, x_],
        optional: [d__],
        when: { freeq!([c__, d__, n_], x_) },
        rhs: {
            let power = x_.pow(&n_);
            let recursive_integrand1 = (&d__ * &power).cos() / x_;
            let recursive_integrand2 = (&d__ * power).sin() / x_;
            let recursive1 = rubi_rhs_int(&recursive_integrand1, x_);
            let recursive2 = rubi_rhs_int(&recursive_integrand2, x_);
            rubi_star(c__.sin(), recursive1)
                    + rubi_star(c__.cos(), recursive2)
        },
    ));
}

fn push_rules_rule_3859(rules: &mut Vec<RubiRule>) {
    rubi_symb!(c__, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 3859,
        source: "Int[Cos[c_+d_.*x_^n_]/x_,x_Symbol] :=
          Cos[c] \\[Star] Int[Cos[d*x^n]/x,x] - Sin[c] \\[Star] Int[Sin[d*x^n]/x,x] /;
        FreeQ[{c,d,n},x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (c__ + d__ * x_.pow(n_)).cos() / x_,
        with: [c__, d__, n_, x_],
        optional: [d__],
        when: { freeq!([c__, d__, n_], x_) },
        rhs: {
            let power = x_.pow(&n_);
            let recursive_integrand1 = (&d__ * &power).cos() / x_;
            let recursive_integrand2 = (&d__ * power).sin() / x_;
            let recursive1 = rubi_rhs_int(&recursive_integrand1, x_);
            let recursive2 = rubi_rhs_int(&recursive_integrand2, x_);
            rubi_star(c__.cos(), recursive1)
                    + rubi_star(-c__.sin(), recursive2)
        },
    ));
}

fn push_rules_rule_3860(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, m_, x_);
    rules.push(rubi_rule!(
        order: 3860,
        source: "Int[x_^m_.*(a_.+b_.*Sin[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
          1/n \\[Star] Subst[Int[x^(Simplify[(m+1)/n]-1)*(a+b*Sin[c+d*x])^p,x],x,x^n] /;
        FreeQ[{a,b,c,d,m,n,p},x] && IntegerQ[Simplify[(m+1)/n]] && (EqQ[p,1] || EqQ[m,n-1] || IntegerQ[p] && GtQ[Simplify[(m+1)/n],0])",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_16(symbols),
        with: [m_, a__, b__, c__, d__, n_, p_, x_],
        optional: [m_, a__, b__, c__, d__, p_],
        when: {
            let s = rubi_simplify(&((&m_ + 1) / &n_));
            freeq!([a__, b__, c__, d__, m_, n_, p_], x_)
                && integerq!(s)
                && (eqq!(p_, 1)
                    || eqq!(m_, &n_ - 1)
                    || integerq!(p_) && gtq!(rubi_simplify(&((&m_ + 1) / &n_)), 0))
        },
        rhs: {
            let s = rubi_simplify(&((&m_ + 1) / &n_));
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub = Atom::var(substitution_symbol);
            let transformed_integrand =
                sub.pow(&s - 1) * (&a__ + &b__ * (&c__ + &d__ * &sub).sin()).pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);
            rubi_star(Atom::num(1) / &n_, rubi_subst(&transformed, substitution_symbol, x_.pow(&n_)))
        },
    ));
}

fn push_rules_rule_3861(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, m_, x_);
    rules.push(rubi_rule!(
        order: 3861,
        source: "Int[x_^m_.*(a_.+b_.*Cos[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
          1/n \\[Star] Subst[Int[x^(Simplify[(m+1)/n]-1)*(a+b*Cos[c+d*x])^p,x],x,x^n] /;
        FreeQ[{a,b,c,d,m,n,p},x] && IntegerQ[Simplify[(m+1)/n]] && (EqQ[p,1] || EqQ[m,n-1] || IntegerQ[p] && GtQ[Simplify[(m+1)/n],0])",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_15(symbols),
        with: [m_, a__, b__, c__, d__, n_, p_, x_],
        optional: [m_, a__, b__, c__, d__, p_],
        when: {
            let s = rubi_simplify(&((&m_ + 1) / &n_));
            freeq!([a__, b__, c__, d__, m_, n_, p_], x_)
                && integerq!(s)
                && (eqq!(p_, 1)
                    || eqq!(m_, &n_ - 1)
                    || integerq!(p_) && gtq!(rubi_simplify(&((&m_ + 1) / &n_)), 0))
        },
        rhs: {
            let s = rubi_simplify(&((&m_ + 1) / &n_));
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub = Atom::var(substitution_symbol);
            let transformed_integrand =
                sub.pow(&s - 1) * (&a__ + &b__ * (&c__ + &d__ * &sub).cos()).pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);
            rubi_star(Atom::num(1) / &n_, rubi_subst(&transformed, substitution_symbol, x_.pow(&n_)))
        },
    ));
}

fn push_rules_rule_3862(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, p_, m_, x_);
    rules.push(rubi_rule!(
        order: 3862,
        source: "Int[(e_*x_)^m_*(a_.+b_.*Sin[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
          e^IntPart[m]*(e*x)^FracPart[m]/x^FracPart[m] \\[Star] Int[x^m*(a+b*Sin[c+d*x^n])^p,x] /;
        FreeQ[{a,b,c,d,e,m,n,p},x] && IntegerQ[Simplify[(m+1)/n]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [e__, m_, a__, b__, c__, d__, n_, p_, x_],
        optional: [a__, b__, c__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_, p_], x_)
                && integerq!(rubi_simplify(&((&m_ + 1) / &n_)))
        },
        rhs: {
            let frac_m = rubi_frac_part(&m_);
            let recursive_integrand =
                x_.pow(&m_) * (&a__ + &b__ * (&c__ + &d__ * x_.pow(&n_)).sin()).pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            rubi_star(e__.pow(rubi_int_part(&m_)) * (&e__ * x_).pow(&frac_m)
                    / x_.pow(frac_m), recursive)
        },
    ));
}

fn push_rules_rule_3863(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, p_, m_, x_);
    rules.push(rubi_rule!(
        order: 3863,
        source: "Int[(e_*x_)^m_*(a_.+b_.*Cos[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
          e^IntPart[m]*(e*x)^FracPart[m]/x^FracPart[m] \\[Star] Int[x^m*(a+b*Cos[c+d*x^n])^p,x] /;
        FreeQ[{a,b,c,d,e,m,n,p},x] && IntegerQ[Simplify[(m+1)/n]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [e__, m_, a__, b__, c__, d__, n_, p_, x_],
        optional: [a__, b__, c__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_, p_], x_)
                && integerq!(rubi_simplify(&((&m_ + 1) / &n_)))
        },
        rhs: {
            let frac_m = rubi_frac_part(&m_);
            let recursive_integrand =
                x_.pow(&m_) * (&a__ + &b__ * (&c__ + &d__ * x_.pow(&n_)).cos()).pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            rubi_star(e__.pow(rubi_int_part(&m_)) * (&e__ * x_).pow(&frac_m)
                    / x_.pow(frac_m), recursive)
        },
    ));
}

fn push_rules_rule_3864(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, n_, m_, x_);
    rules.push(rubi_rule!(
        order: 3864,
        source: "Int[x_^m_.*Sin[a_.+b_.*x_^n_],x_Symbol] :=
          2/n \\[Star] Subst[Int[Sin[a+b*x^2],x],x,x^(n/2)] /;
        FreeQ[{a,b,m,n},x] && EqQ[m,n/2-1]",
        desc: "Integration by substitution",
        refs: [],
        pattern: x_.pow(m_) * (a__ + b__ * x_.pow(n_)).sin(),
        with: [m_, a__, b__, n_, x_],
        optional: [m_, a__, b__],
        when: {
            freeq!([a__, b__, m_, n_], x_) && eqq!(m_, &n_ / 2 - 1)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub = Atom::var(substitution_symbol);
            let primitive =
                rubi_rhs_int(&(&a__ + &b__ * sub.pow(2)).sin(), substitution_symbol);
            rubi_star(Atom::num(2) / &n_, rubi_subst(
                    &primitive,
                    substitution_symbol,
                    x_.pow(&n_ / 2),
                ))
        },
    ));
}

fn push_rules_rule_3865(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, n_, m_, x_);
    rules.push(rubi_rule!(
        order: 3865,
        source: "Int[x_^m_.*Cos[a_.+b_.*x_^n_],x_Symbol] :=
          2/n \\[Star] Subst[Int[Cos[a+b*x^2],x],x,x^(n/2)] /;
        FreeQ[{a,b,m,n},x] && EqQ[m,n/2-1]",
        desc: "Integration by substitution",
        refs: [],
        pattern: x_.pow(m_) * (a__ + b__ * x_.pow(n_)).cos(),
        with: [m_, a__, b__, n_, x_],
        optional: [m_, a__, b__],
        when: {
            freeq!([a__, b__, m_, n_], x_) && eqq!(m_, &n_ / 2 - 1)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub = Atom::var(substitution_symbol);
            let primitive =
                rubi_rhs_int(&(&a__ + &b__ * sub.pow(2)).cos(), substitution_symbol);
            rubi_star(Atom::num(2) / &n_, rubi_subst(
                    &primitive,
                    substitution_symbol,
                    x_.pow(&n_ / 2),
                ))
        },
    ));
}

fn push_rules_rule_3866(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; c__, d__, e__, n_, m_, x_);
    rules.push(rubi_rule!(
        order: 3866,
        source: "Int[(e_.*x_)^m_.*Sin[c_.+d_.*x_^n_],x_Symbol] :=
          -e^(n-1)*(e*x)^(m-n+1)*Cos[c+d*x^n]/(d*n) +
          e^n*(m-n+1)/(d*n) \\[Star] Int[(e*x)^(m-n)*Cos[c+d*x^n],x] /;
        FreeQ[{c,d,e},x] && IGtQ[n,0] && LtQ[n,m+1]",
        desc: "Integration by parts",
        refs: ["CRC 392, A&S 4.3.119", "CRC 396, A&S 4.3.123"],
        pattern:  rubi_shared_pattern_12(symbols),
        with: [e__, m_, c__, d__, n_, x_],
        optional: [e__, m_, c__, d__],
        when: {
            freeq!([c__, d__, e__], x_) && igtq!(n_, 0) && ltq!(n_, &m_ + 1)
        },
        rhs: {
            let angle = &c__ + &d__ * x_.pow(&n_);
            let recursive_integrand = (&e__ * x_).pow(&m_ - &n_) * angle.cos();
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            rubi_simp(&(-e__.pow(&n_ - 1) * (&e__ * x_).pow(&m_ - &n_ + 1) * angle.cos() / (&d__ * &n_)), x_)
                    + rubi_star(e__.pow(&n_) * (&m_ - &n_ + 1) / (&d__ * &n_), recursive)
        },
    ));
}

fn push_rules_rule_3867(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; c__, d__, e__, n_, m_, x_);
    rules.push(rubi_rule!(
        order: 3867,
        source: "Int[(e_.*x_)^m_.*Cos[c_.+d_.*x_^n_],x_Symbol] :=
          e^(n-1)*(e*x)^(m-n+1)*Sin[c+d*x^n]/(d*n) -
          e^n*(m-n+1)/(d*n) \\[Star] Int[(e*x)^(m-n)*Sin[c+d*x^n],x] /;
        FreeQ[{c,d,e},x] && IGtQ[n,0] && LtQ[n,m+1]",
        desc: "Integration by parts",
        refs: ["CRC 392, A&S 4.3.119", "CRC 396, A&S 4.3.123"],
        pattern:  rubi_shared_pattern_11(symbols),
        with: [e__, m_, c__, d__, n_, x_],
        optional: [e__, m_, c__, d__],
        when: {
            freeq!([c__, d__, e__], x_) && igtq!(n_, 0) && ltq!(n_, &m_ + 1)
        },
        rhs: {
            let angle = &c__ + &d__ * x_.pow(&n_);
            let recursive_integrand = (&e__ * x_).pow(&m_ - &n_) * angle.sin();
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            rubi_simp(&(e__.pow(&n_ - 1) * (&e__ * x_).pow(&m_ - &n_ + 1) * angle.sin() / (&d__ * &n_)), x_)
                    + rubi_star(-e__.pow(&n_) * (&m_ - &n_ + 1) / (&d__ * &n_), recursive)
        },
    ));
}

fn push_rules_rule_3868(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; c__, d__, e__, n_, m_, x_);
    rules.push(rubi_rule!(
        order: 3868,
        source: "Int[(e_.*x_)^m_*Sin[c_.+d_.*x_^n_],x_Symbol] :=
          (e*x)^(m+1)*Sin[c+d*x^n]/(e*(m+1)) -
          d*n/(e^n*(m+1)) \\[Star] Int[(e*x)^(m+n)*Cos[c+d*x^n],x] /;
        FreeQ[{c,d,e},x] && IGtQ[n,0] && LtQ[m,-1]",
        desc: "Integration by parts",
        refs: ["CRC 405, A&S 4.3.120", "CRC 406, A&S 4.3.124"],
        pattern:  rubi_shared_pattern_12(symbols),
        with: [e__, m_, c__, d__, n_, x_],
        optional: [e__, c__, d__],
        when: {
            freeq!([c__, d__, e__], x_) && igtq!(n_, 0) && ltq!(m_, -1)
        },
        rhs: {
            let angle = &c__ + &d__ * x_.pow(&n_);
            let recursive_integrand = (&e__ * x_).pow(&m_ + &n_) * angle.cos();
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            rubi_simp(&((&e__ * x_).pow(&m_ + 1) * angle.sin() / (&e__ * (&m_ + 1))), x_)
                    + rubi_star(-&d__ * &n_ / (e__.pow(&n_) * (&m_ + 1)), recursive)
        },
    ));
}

fn push_rules_rule_3869(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; c__, d__, e__, n_, m_, x_);
    rules.push(rubi_rule!(
        order: 3869,
        source: "Int[(e_.*x_)^m_*Cos[c_.+d_.*x_^n_],x_Symbol] :=
          (e*x)^(m+1)*Cos[c+d*x^n]/(e*(m+1)) +
          d*n/(e^n*(m+1)) \\[Star] Int[(e*x)^(m+n)*Sin[c+d*x^n],x] /;
        FreeQ[{c,d,e},x] && IGtQ[n,0] && LtQ[m,-1]",
        desc: "Integration by parts",
        refs: ["CRC 405, A&S 4.3.120", "CRC 406, A&S 4.3.124"],
        pattern:  rubi_shared_pattern_11(symbols),
        with: [e__, m_, c__, d__, n_, x_],
        optional: [e__, c__, d__],
        when: {
            freeq!([c__, d__, e__], x_) && igtq!(n_, 0) && ltq!(m_, -1)
        },
        rhs: {
            let angle = &c__ + &d__ * x_.pow(&n_);
            let recursive_integrand = (&e__ * x_).pow(&m_ + &n_) * angle.sin();
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            rubi_simp(&((&e__ * x_).pow(&m_ + 1) * angle.cos() / (&e__ * (&m_ + 1))), x_)
                    + rubi_star(&d__ * &n_ / (e__.pow(&n_) * (&m_ + 1)), recursive)
        },
    ));
}

fn push_rules_rule_3870(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; c__, d__, e__, n_, m_, x_);
    rules.push(rubi_rule!(
        order: 3870,
        source: "Int[(e_.*x_)^m_.*Sin[c_.+d_.*x_^n_],x_Symbol] :=
          I/2 \\[Star] Int[(e*x)^m*E^(-c*I-d*I*x^n),x] - I/2 \\[Star] Int[(e*x)^m*E^(c*I+d*I*x^n),x] /;
        FreeQ[{c,d,e,m},x] && IGtQ[n,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_12(symbols),
        with: [e__, m_, c__, d__, n_, x_],
        optional: [e__, m_, c__, d__],
        when: {
            freeq!([c__, d__, e__, m_], x_) && igtq!(n_, 0)
        },
        rhs: {
            let i = rubi_i();
            let scaled_power = (&e__ * x_).pow(&m_);
            let recursive1 = rubi_rhs_int(
                &(&scaled_power * (-&c__ * &i - &d__ * &i * x_.pow(&n_)).exp()),
                x_,
            );
            let recursive2 = rubi_rhs_int(
                &(&scaled_power * (&c__ * &i + &d__ * &i * x_.pow(&n_)).exp()),
                x_,
            );
            rubi_star(&i / 2, recursive1)
                    + rubi_star(-i / 2, recursive2)
        },
    ));
}

fn push_rules_rule_3871(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; c__, d__, e__, n_, m_, x_);
    rules.push(rubi_rule!(
        order: 3871,
        source: "Int[(e_.*x_)^m_.*Cos[c_.+d_.*x_^n_],x_Symbol] :=
          1/2 \\[Star] Int[(e*x)^m*E^(-c*I-d*I*x^n),x] + 1/2 \\[Star] Int[(e*x)^m*E^(c*I+d*I*x^n),x] /;
        FreeQ[{c,d,e,m},x] && IGtQ[n,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_11(symbols),
        with: [e__, m_, c__, d__, n_, x_],
        optional: [e__, m_, c__, d__],
        when: {
            freeq!([c__, d__, e__, m_], x_) && igtq!(n_, 0)
        },
        rhs: {
            let i = rubi_i();
            let scaled_power = (&e__ * x_).pow(&m_);
            let recursive1 = rubi_rhs_int(
                &(&scaled_power * (-&c__ * &i - &d__ * &i * x_.pow(&n_)).exp()),
                x_,
            );
            let recursive2 = rubi_rhs_int(
                &(&scaled_power * (&c__ * &i + &d__ * &i * x_.pow(&n_)).exp()),
                x_,
            );
            rubi_star(Atom::num(1) / 2, recursive1)
                    + rubi_star(Atom::num(1) / 2, recursive2)
        },
    ));
}

fn push_rules_rule_3872(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, n_, m_, x_);
    rules.push(rubi_rule!(
        order: 3872,
        source: "Int[x_^m_.*Sin[a_.+b_.*x_^n_/2]^2,x_Symbol] :=
          1/2 \\[Star] Int[x^m,x] - 1/2 \\[Star] Int[x^m*Cos[2*a+b*x^n],x] /;
        FreeQ[{a,b,m,n},x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: x_.pow(m_) * (a__ + b__ * x_.pow(n_) / 2).sin().pow(2),
        with: [m_, a__, b__, n_, x_],
        optional: [m_, a__, b__],
        when: { freeq!([a__, b__, m_, n_], x_) },
        rhs: {
            let recursive1 = rubi_rhs_int(x_.pow(&m_), x_);
            let recursive_integrand =
                x_.pow(&m_) * (Atom::num(2) * &a__ + &b__ * x_.pow(&n_)).cos();
            let recursive2 = rubi_rhs_int(&recursive_integrand, x_);
            rubi_star(Atom::num(1) / 2, recursive1)
                    + rubi_star(Atom::num(-1) / 2, recursive2)
        },
    ));
}

fn push_rules_rule_3873(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, n_, m_, x_);
    rules.push(rubi_rule!(
        order: 3873,
        source: "Int[x_^m_.*Cos[a_.+b_.*x_^n_/2]^2,x_Symbol] :=
          1/2 \\[Star] Int[x^m,x] + 1/2 \\[Star] Int[x^m*Cos[2*a+b*x^n],x] /;
        FreeQ[{a,b,m,n},x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: x_.pow(m_) * (a__ + b__ * x_.pow(n_) / 2).cos().pow(2),
        with: [m_, a__, b__, n_, x_],
        optional: [m_, a__, b__],
        when: { freeq!([a__, b__, m_, n_], x_) },
        rhs: {
            let recursive1 = rubi_rhs_int(x_.pow(&m_), x_);
            let recursive_integrand =
                x_.pow(&m_) * (Atom::num(2) * &a__ + &b__ * x_.pow(&n_)).cos();
            let recursive2 = rubi_rhs_int(&recursive_integrand, x_);
            rubi_star(Atom::num(1) / 2, recursive1)
                    + rubi_star(Atom::num(1) / 2, recursive2)
        },
    ));
}

fn push_rules_rule_3874(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, n_, p_, m_, x_);
    rules.push(rubi_rule!(
        order: 3874,
        source: "Int[x_^m_.*Sin[a_.+b_.*x_^n_]^p_,x_Symbol] :=
          x^(m+1)*Sin[a+b*x^n]^p/(m+1) -
          b*n*p/(m+1) \\[Star] Int[Sin[a+b*x^n]^(p-1)*Cos[a+b*x^n],x] /;
        FreeQ[{a,b},x] && IGtQ[p,1] && EqQ[m+n,0] && NeQ[n,1] && IntegerQ[n]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_20(symbols),
        with: [m_, a__, b__, n_, p_, x_],
        optional: [m_, a__, b__],
        when: {
            freeq!([a__, b__], x_)
                && igtq!(p_, 1)
                && eqq!(&m_ + &n_, 0)
                && neq!(n_, 1)
                && integerq!(n_)
        },
        rhs: {
            let angle = &a__ + &b__ * x_.pow(&n_);
            let recursive_integrand = angle.sin().pow(&p_ - 1) * angle.cos();
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            rubi_simp(&(x_.pow(&m_ + 1) * angle.sin().pow(&p_) / (&m_ + 1)), x_)
                    + rubi_star(-&b__ * &n_ * &p_ / (&m_ + 1), recursive)
        },
    ));
}

fn push_rules_rule_3875(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, n_, p_, m_, x_);
    rules.push(rubi_rule!(
        order: 3875,
        source: "Int[x_^m_.*Cos[a_.+b_.*x_^n_]^p_,x_Symbol] :=
          x^(m+1)*Cos[a+b*x^n]^p/(m+1) +
          b*n*p/(m+1) \\[Star] Int[Cos[a+b*x^n]^(p-1)*Sin[a+b*x^n],x] /;
        FreeQ[{a,b},x] && IGtQ[p,1] && EqQ[m+n,0] && NeQ[n,1] && IntegerQ[n]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_17(symbols),
        with: [m_, a__, b__, n_, p_, x_],
        optional: [m_, a__, b__],
        when: {
            freeq!([a__, b__], x_)
                && igtq!(p_, 1)
                && eqq!(&m_ + &n_, 0)
                && neq!(n_, 1)
                && integerq!(n_)
        },
        rhs: {
            let angle = &a__ + &b__ * x_.pow(&n_);
            let recursive_integrand = angle.cos().pow(&p_ - 1) * angle.sin();
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            rubi_simp(&(x_.pow(&m_ + 1) * angle.cos().pow(&p_) / (&m_ + 1)), x_)
                    + rubi_star(&b__ * &n_ * &p_ / (&m_ + 1), recursive)
        },
    ));
}

fn push_rules_rule_3876(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, n_, p_, m_, x_);
    rules.push(rubi_rule!(
        order: 3876,
        source: "Int[x_^m_.*Sin[a_.+b_.*x_^n_]^p_,x_Symbol] :=
          n*Sin[a+b*x^n]^p/(b^2*n^2*p^2) -
          x^n*Cos[a+b*x^n]*Sin[a+b*x^n]^(p-1)/(b*n*p) +
          (p-1)/p \\[Star] Int[x^m*Sin[a+b*x^n]^(p-2),x] /;
        FreeQ[{a,b,m,n},x] && EqQ[m-2*n+1,0] && GtQ[p,1]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: ["G&R 2.631.2' special case when m-2n+1\\[Equal]0", "G&R 2.631.3' special case when m-2n+1\\[Equal]0"],
        pattern:  rubi_shared_pattern_20(symbols),
        with: [m_, a__, b__, n_, p_, x_],
        optional: [m_, a__, b__],
        when: {
            freeq!([a__, b__, m_, n_], x_)
                && eqq!(&m_ - Atom::num(2) * &n_ + 1, 0)
                && gtq!(p_, 1)
        },
        rhs: {
            let angle = &a__ + &b__ * x_.pow(&n_);
            let recursive_integrand = x_.pow(&m_) * angle.sin().pow(&p_ - 2);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            rubi_simp(&(&n_ * angle.sin().pow(&p_) / (b__.pow(2) * n_.pow(2) * p_.pow(2))), x_)
                    - rubi_simp(&(x_.pow(&n_) * angle.cos() * angle.sin().pow(&p_ - 1) / (&b__ * &n_ * &p_)), x_)
                    + rubi_star((&p_ - 1) / &p_, recursive)
        },
    ));
}

fn push_rules_rule_3877(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, n_, p_, m_, x_);
    rules.push(rubi_rule!(
        order: 3877,
        source: "Int[x_^m_.*Cos[a_.+b_.*x_^n_]^p_,x_Symbol] :=
          n*Cos[a+b*x^n]^p/(b^2*n^2*p^2) +
          x^n*Sin[a+b*x^n]*Cos[a+b*x^n]^(p-1)/(b*n*p) +
          (p-1)/p \\[Star] Int[x^m*Cos[a+b*x^n]^(p-2),x] /;
        FreeQ[{a,b,m,n},x] && EqQ[m-2*n+1,0] && GtQ[p,1]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: ["G&R 2.631.2' special case when m-2n+1\\[Equal]0", "G&R 2.631.3' special case when m-2n+1\\[Equal]0"],
        pattern:  rubi_shared_pattern_17(symbols),
        with: [m_, a__, b__, n_, p_, x_],
        optional: [m_, a__, b__],
        when: {
            freeq!([a__, b__, m_, n_], x_)
                && eqq!(&m_ - Atom::num(2) * &n_ + 1, 0)
                && gtq!(p_, 1)
        },
        rhs: {
            let angle = &a__ + &b__ * x_.pow(&n_);
            let recursive_integrand = x_.pow(&m_) * angle.cos().pow(&p_ - 2);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            rubi_simp(&(&n_ * angle.cos().pow(&p_) / (b__.pow(2) * n_.pow(2) * p_.pow(2))), x_)
                    + rubi_simp(&(x_.pow(&n_) * angle.sin() * angle.cos().pow(&p_ - 1) / (&b__ * &n_ * &p_)), x_)
                    + rubi_star((&p_ - 1) / &p_, recursive)
        },
    ));
}

fn push_rules_rule_3878(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, n_, p_, m_, x_);
    rules.push(rubi_rule!(
        order: 3878,
        source: "Int[x_^m_.*Sin[a_.+b_.*x_^n_]^p_,x_Symbol] :=
          (m-n+1)*x^(m-2*n+1)*Sin[a+b*x^n]^p/(b^2*n^2*p^2) -
          x^(m-n+1)*Cos[a+b*x^n]*Sin[a+b*x^n]^(p-1)/(b*n*p) +
          (p-1)/p \\[Star] Int[x^m*Sin[a+b*x^n]^(p-2),x] -
          (m-n+1)*(m-2*n+1)/(b^2*n^2*p^2) \\[Star] Int[x^(m-2*n)*Sin[a+b*x^n]^p,x] /;
        FreeQ[{a,b},x] && GtQ[p,1] && IGtQ[n,0] && IGtQ[m,2*n-1]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: ["G&R 2.631.2'", "G&R 2.631.3'"],
        pattern:  rubi_shared_pattern_20(symbols),
        with: [m_, a__, b__, n_, p_, x_],
        optional: [m_, a__, b__],
        when: {
            freeq!([a__, b__], x_)
                && gtq!(p_, 1)
                && igtq!(n_, 0)
                && integerq!(m_)
                && gtq!(m_, Atom::num(2) * &n_ - 1)
        },
        rhs: {
            let angle = &a__ + &b__ * x_.pow(&n_);
            let recursive1 = rubi_rhs_int(&(x_.pow(&m_) * angle.sin().pow(&p_ - 2)), x_);
            let recursive2 = rubi_rhs_int(&(x_.pow(&m_ - Atom::num(2) * &n_) * angle.sin().pow(&p_)), x_);
            rubi_simp(&((&m_ - &n_ + 1) * x_.pow(&m_ - Atom::num(2) * &n_ + 1) * angle.sin().pow(&p_)
                    / (b__.pow(2) * n_.pow(2) * p_.pow(2))), x_)
                    - rubi_simp(&(x_.pow(&m_ - &n_ + 1) * angle.cos() * angle.sin().pow(&p_ - 1)
                        / (&b__ * &n_ * &p_)), x_)
                    + rubi_star((&p_ - 1) / &p_, recursive1)
                    + rubi_star(-(&m_ - &n_ + 1) * (&m_ - Atom::num(2) * &n_ + 1)
                            / (b__.pow(2) * n_.pow(2) * p_.pow(2)), recursive2)
        },
    ));
}

fn push_rules_rule_3879(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, n_, p_, m_, x_);
    rules.push(rubi_rule!(
        order: 3879,
        source: "Int[x_^m_.*Cos[a_.+b_.*x_^n_]^p_,x_Symbol] :=
          (m-n+1)*x^(m-2*n+1)*Cos[a+b*x^n]^p/(b^2*n^2*p^2) +
          x^(m-n+1)*Sin[a+b*x^n]*Cos[a+b*x^n]^(p-1)/(b*n*p) +
          (p-1)/p \\[Star] Int[x^m*Cos[a+b*x^n]^(p-2),x] -
          (m-n+1)*(m-2*n+1)/(b^2*n^2*p^2) \\[Star] Int[x^(m-2*n)*Cos[a+b*x^n]^p,x] /;
        FreeQ[{a,b},x] && GtQ[p,1] && IGtQ[n,0] && IGtQ[m,2*n-1]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: ["G&R 2.631.2'", "G&R 2.631.3'"],
        pattern:  rubi_shared_pattern_17(symbols),
        with: [m_, a__, b__, n_, p_, x_],
        optional: [m_, a__, b__],
        when: {
            freeq!([a__, b__], x_)
                && gtq!(p_, 1)
                && igtq!(n_, 0)
                && integerq!(m_)
                && gtq!(m_, Atom::num(2) * &n_ - 1)
        },
        rhs: {
            let angle = &a__ + &b__ * x_.pow(&n_);
            let recursive1 = rubi_rhs_int(&(x_.pow(&m_) * angle.cos().pow(&p_ - 2)), x_);
            let recursive2 = rubi_rhs_int(&(x_.pow(&m_ - Atom::num(2) * &n_) * angle.cos().pow(&p_)), x_);
            rubi_simp(&((&m_ - &n_ + 1) * x_.pow(&m_ - Atom::num(2) * &n_ + 1) * angle.cos().pow(&p_)
                    / (b__.pow(2) * n_.pow(2) * p_.pow(2))), x_)
                    + rubi_simp(&(x_.pow(&m_ - &n_ + 1) * angle.sin() * angle.cos().pow(&p_ - 1)
                        / (&b__ * &n_ * &p_)), x_)
                    + rubi_star((&p_ - 1) / &p_, recursive1)
                    + rubi_star(-(&m_ - &n_ + 1) * (&m_ - Atom::num(2) * &n_ + 1)
                            / (b__.pow(2) * n_.pow(2) * p_.pow(2)), recursive2)
        },
    ));
}

fn push_rules_rule_3880(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, n_, p_, m_, x_);
    rules.push(rubi_rule!(
        order: 3880,
        source: "Int[x_^m_.*Sin[a_.+b_.*x_^n_]^p_,x_Symbol] :=
          x^(m+1)*Sin[a+b*x^n]^p/(m+1) -
          b*n*p*x^(m+n+1)*Cos[a+b*x^n]*Sin[a+b*x^n]^(p-1)/((m+1)*(m+n+1)) -
          b^2*n^2*p^2/((m+1)*(m+n+1)) \\[Star] Int[x^(m+2*n)*Sin[a+b*x^n]^p,x] +
          b^2*n^2*p*(p-1)/((m+1)*(m+n+1)) \\[Star] Int[x^(m+2*n)*Sin[a+b*x^n]^(p-2),x] /;
        FreeQ[{a,b},x] && GtQ[p,1] && IGtQ[n,0] && ILtQ[m,-2*n+1] && NeQ[m+n+1,0]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: ["G&R 2.638.1'", "G&R 2.638.2'"],
        pattern:  rubi_shared_pattern_20(symbols),
        with: [m_, a__, b__, n_, p_, x_],
        optional: [m_, a__, b__],
        when: {
            freeq!([a__, b__], x_)
                && gtq!(p_, 1)
                && igtq!(n_, 0)
                && integerq!(m_)
                && ltq!(m_, (-Atom::num(2) * &n_ + 1))
                && neq!(&m_ + &n_ + 1, 0)
        },
        rhs: {
            let angle = &a__ + &b__ * x_.pow(&n_);
            let recursive1 = rubi_rhs_int(&(x_.pow(&m_ + Atom::num(2) * &n_) * angle.sin().pow(&p_)), x_);
            let recursive2 = rubi_rhs_int(&(x_.pow(&m_ + Atom::num(2) * &n_) * angle.sin().pow(&p_ - 2)), x_);
            rubi_simp(&(x_.pow(&m_ + 1) * angle.sin().pow(&p_) / (&m_ + 1)), x_)
                    - rubi_simp(&(&b__ * &n_ * &p_ * x_.pow(&m_ + &n_ + 1) * angle.cos() * angle.sin().pow(&p_ - 1)
                        / ((&m_ + 1) * (&m_ + &n_ + 1))), x_)
                    + rubi_star(-b__.pow(2) * n_.pow(2) * p_.pow(2)
                            / ((&m_ + 1) * (&m_ + &n_ + 1)), recursive1)
                    + rubi_star(b__.pow(2) * n_.pow(2) * &p_ * (&p_ - 1)
                            / ((&m_ + 1) * (&m_ + &n_ + 1)), recursive2)
        },
    ));
}

fn push_rules_rule_3881(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, n_, p_, m_, x_);
    rules.push(rubi_rule!(
        order: 3881,
        source: "Int[x_^m_.*Cos[a_.+b_.*x_^n_]^p_,x_Symbol] :=
          x^(m+1)*Cos[a+b*x^n]^p/(m+1) +
          b*n*p*x^(m+n+1)*Sin[a+b*x^n]*Cos[a+b*x^n]^(p-1)/((m+1)*(m+n+1)) -
          b^2*n^2*p^2/((m+1)*(m+n+1)) \\[Star] Int[x^(m+2*n)*Cos[a+b*x^n]^p,x] +
          b^2*n^2*p*(p-1)/((m+1)*(m+n+1)) \\[Star] Int[x^(m+2*n)*Cos[a+b*x^n]^(p-2),x] /;
        FreeQ[{a,b},x] && GtQ[p,1] && IGtQ[n,0] && ILtQ[m,-2*n+1] && NeQ[m+n+1,0]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: ["G&R 2.638.1'", "G&R 2.638.2'"],
        pattern:  rubi_shared_pattern_17(symbols),
        with: [m_, a__, b__, n_, p_, x_],
        optional: [m_, a__, b__],
        when: {
            freeq!([a__, b__], x_)
                && gtq!(p_, 1)
                && igtq!(n_, 0)
                && integerq!(m_)
                && ltq!(m_, (-Atom::num(2) * &n_ + 1))
                && neq!(&m_ + &n_ + 1, 0)
        },
        rhs: {
            let angle = &a__ + &b__ * x_.pow(&n_);
            let recursive1 = rubi_rhs_int(&(x_.pow(&m_ + Atom::num(2) * &n_) * angle.cos().pow(&p_)), x_);
            let recursive2 = rubi_rhs_int(&(x_.pow(&m_ + Atom::num(2) * &n_) * angle.cos().pow(&p_ - 2)), x_);
            rubi_simp(&(x_.pow(&m_ + 1) * angle.cos().pow(&p_) / (&m_ + 1)), x_)
                    + rubi_simp(&(&b__ * &n_ * &p_ * x_.pow(&m_ + &n_ + 1) * angle.sin() * angle.cos().pow(&p_ - 1)
                        / ((&m_ + 1) * (&m_ + &n_ + 1))), x_)
                    + rubi_star(-b__.pow(2) * n_.pow(2) * p_.pow(2)
                            / ((&m_ + 1) * (&m_ + &n_ + 1)), recursive1)
                    + rubi_star(b__.pow(2) * n_.pow(2) * &p_ * (&p_ - 1)
                            / ((&m_ + 1) * (&m_ + &n_ + 1)), recursive2)
        },
    ));
}

fn push_rules_rule_3882(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, p_, m_, x_);
    rules.push(rubi_rule!(
        order: 3882,
        source: "Int[(e_.*x_)^m_*(a_.+b_.*Sin[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
          With[{k=Denominator[m]},
          k/e \\[Star] Subst[Int[x^(k*(m+1)-1)*(a+b*Sin[c+d*x^(k*n)/e^n])^p,x],x,(e*x)^(1/k)]] /;
        FreeQ[{a,b,c,d,e},x] && IntegerQ[p] && IGtQ[n,0] && FractionQ[m]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [e__, m_, a__, b__, c__, d__, n_, p_, x_],
        optional: [e__, a__, b__, c__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && integerq!(p_)
                && igtq!(n_, 0)
                && fractionq!(m_)
        },
        rhs: {
            let k_i = rubi_denominator(&m_).rubi_rhs();
            let k = Atom::num(k_i);
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub = Atom::var(substitution_symbol);
            let transformed_integrand = sub.pow(&k * (&m_ + 1) - 1)
                * (&a__ + &b__ * (&c__ + &d__ * sub.pow(&k * &n_) / e__.pow(&n_)).sin()).pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);
            rubi_star(&k / &e__, rubi_subst(
                    &transformed,
                    substitution_symbol,
                    (&e__ * x_).pow(Atom::num(1) / k_i),
                ))
        },
    ));
}

fn push_rules_rule_3883(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, p_, m_, x_);
    rules.push(rubi_rule!(
        order: 3883,
        source: "Int[(e_.*x_)^m_*(a_.+b_.*Cos[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
          With[{k=Denominator[m]},
          k/e \\[Star] Subst[Int[x^(k*(m+1)-1)*(a+b*Cos[c+d*x^(k*n)/e^n])^p,x],x,(e*x)^(1/k)]] /;
        FreeQ[{a,b,c,d,e},x] && IntegerQ[p] && IGtQ[n,0] && FractionQ[m]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [e__, m_, a__, b__, c__, d__, n_, p_, x_],
        optional: [e__, a__, b__, c__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && integerq!(p_)
                && igtq!(n_, 0)
                && fractionq!(m_)
        },
        rhs: {
            let k_i = rubi_denominator(&m_).rubi_rhs();
            let k = Atom::num(k_i);
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub = Atom::var(substitution_symbol);
            let transformed_integrand = sub.pow(&k * (&m_ + 1) - 1)
                * (&a__ + &b__ * (&c__ + &d__ * sub.pow(&k * &n_) / e__.pow(&n_)).cos()).pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);
            rubi_star(&k / &e__, rubi_subst(
                    &transformed,
                    substitution_symbol,
                    (&e__ * x_).pow(Atom::num(1) / k_i),
                ))
        },
    ));
}

fn push_rules_rule_3884(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, p_, m_, x_);
    rules.push(rubi_rule!(
        order: 3884,
        source: "Int[(e_.*x_)^m_.*(a_.+b_.*Sin[c_.+d_.*x_^n_])^p_,x_Symbol] :=
          Int[ExpandTrigReduce[(e*x)^m,(a+b*Sin[c+d*x^n])^p,x],x] /;
        FreeQ[{a,b,c,d,e,m},x] && IGtQ[p,1] && IGtQ[n,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [e__, m_, a__, b__, c__, d__, n_, p_, x_],
        optional: [e__, m_, a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_], x_)
                && igtq!(p_, 1)
                && igtq!(n_, 0)
        },
        rhs: {
            let u = (&e__ * x_).pow(&m_);
            let v = (&a__ + &b__ * (&c__ + &d__ * x_.pow(&n_)).sin()).pow(&p_);
            let expanded = rubi_expand_trig_reduce(&u, &v, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_3885(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, p_, m_, x_);
    rules.push(rubi_rule!(
        order: 3885,
        source: "Int[(e_.*x_)^m_.*(a_.+b_.*Cos[c_.+d_.*x_^n_])^p_,x_Symbol] :=
          Int[ExpandTrigReduce[(e*x)^m,(a+b*Cos[c+d*x^n])^p,x],x] /;
        FreeQ[{a,b,c,d,e,m},x] && IGtQ[p,1] && IGtQ[n,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [e__, m_, a__, b__, c__, d__, n_, p_, x_],
        optional: [e__, m_, a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_], x_)
                && igtq!(p_, 1)
                && igtq!(n_, 0)
        },
        rhs: {
            let u = (&e__ * x_).pow(&m_);
            let v = (&a__ + &b__ * (&c__ + &d__ * x_.pow(&n_)).cos()).pow(&p_);
            let expanded = rubi_expand_trig_reduce(&u, &v, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_3886(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, n_, p_, m_, x_);
    rules.push(rubi_rule!(
        order: 3886,
        source: "Int[x_^m_.*Sin[a_.+b_.*x_^n_]^p_,x_Symbol] :=
          x^n*Cos[a+b*x^n]*Sin[a+b*x^n]^(p+1)/(b*n*(p+1)) -
          n*Sin[a+b*x^n]^(p+2)/(b^2*n^2*(p+1)*(p+2)) +
          (p+2)/(p+1) \\[Star] Int[x^m*Sin[a+b*x^n]^(p+2),x] /;
        FreeQ[{a,b,m,n},x] && EqQ[m-2*n+1,0] && LtQ[p,-1] && NeQ[p,-2]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: ["G&R 2.643.1' special case when m-2n+1\\[Equal]0", "G&R 2.643.2' special case when m-2n+1\\[Equal]0"],
        pattern:  rubi_shared_pattern_20(symbols),
        with: [m_, a__, b__, n_, p_, x_],
        optional: [m_, a__, b__],
        when: {
            freeq!([a__, b__, m_, n_], x_)
                && eqq!(&m_ - Atom::num(2) * &n_ + 1, 0)
                && ltq!(p_, -1)
                && neq!(p_, -2)
        },
        rhs: {
            let angle = &a__ + &b__ * x_.pow(&n_);
            let recursive_integrand = x_.pow(&m_) * angle.sin().pow(&p_ + 2);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            rubi_simp(&(x_.pow(&n_) * angle.cos() * angle.sin().pow(&p_ + 1)
                    / (&b__ * &n_ * (&p_ + 1))), x_)
                    - rubi_simp(&(&n_ * angle.sin().pow(&p_ + 2)
                        / (b__.pow(2) * n_.pow(2) * (&p_ + 1) * (&p_ + 2))), x_)
                    + rubi_star((&p_ + 2) / (&p_ + 1), recursive)
        },
    ));
}

fn push_rules_rule_3887(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, n_, p_, m_, x_);
    rules.push(rubi_rule!(
        order: 3887,
        source: "Int[x_^m_.*Cos[a_.+b_.*x_^n_]^p_,x_Symbol] :=
          -x^n*Sin[a+b*x^n]*Cos[a+b*x^n]^(p+1)/(b*n*(p+1)) -
          n*Cos[a+b*x^n]^(p+2)/(b^2*n^2*(p+1)*(p+2)) +
          (p+2)/(p+1) \\[Star] Int[x^m*Cos[a+b*x^n]^(p+2),x] /;
        FreeQ[{a,b,m,n},x] && EqQ[m-2*n+1,0] && LtQ[p,-1] && NeQ[p,-2]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: ["G&R 2.643.1' special case when m-2n+1\\[Equal]0", "G&R 2.643.2' special case when m-2n+1\\[Equal]0"],
        pattern:  rubi_shared_pattern_17(symbols),
        with: [m_, a__, b__, n_, p_, x_],
        optional: [m_, a__, b__],
        when: {
            freeq!([a__, b__, m_, n_], x_)
                && eqq!(&m_ - Atom::num(2) * &n_ + 1, 0)
                && ltq!(p_, -1)
                && neq!(p_, -2)
        },
        rhs: {
            let angle = &a__ + &b__ * x_.pow(&n_);
            let recursive_integrand = x_.pow(&m_) * angle.cos().pow(&p_ + 2);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            rubi_simp(&(Atom::num(-1) * x_.pow(&n_) * angle.sin() * angle.cos().pow(&p_ + 1)
                    / (&b__ * &n_ * (&p_ + 1))), x_)
                    - rubi_simp(&(&n_ * angle.cos().pow(&p_ + 2)
                        / (b__.pow(2) * n_.pow(2) * (&p_ + 1) * (&p_ + 2))), x_)
                    + rubi_star((&p_ + 2) / (&p_ + 1), recursive)
        },
    ));
}

fn push_rules_rule_3888(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, n_, p_, m_, x_);
    rules.push(rubi_rule!(
        order: 3888,
        source: "Int[x_^m_.*Sin[a_.+b_.*x_^n_]^p_,x_Symbol] :=
          x^(m-n+1)*Cos[a+b*x^n]*Sin[a+b*x^n]^(p+1)/(b*n*(p+1)) -
          (m-n+1)*x^(m-2*n+1)*Sin[a+b*x^n]^(p+2)/(b^2*n^2*(p+1)*(p+2)) +
          (p+2)/(p+1) \\[Star] Int[x^m*Sin[a+b*x^n]^(p+2),x] +
          (m-n+1)*(m-2*n+1)/(b^2*n^2*(p+1)*(p+2)) \\[Star] Int[x^(m-2*n)*Sin[a+b*x^n]^(p+2),x] /;
        FreeQ[{a,b},x] && LtQ[p,-1] && NeQ[p,-2] && IGtQ[n,0] && IGtQ[m,2*n-1]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: ["G&R 2.643.1'", "G&R 2.643.2"],
        pattern:  rubi_shared_pattern_20(symbols),
        with: [m_, a__, b__, n_, p_, x_],
        optional: [m_, a__, b__],
        when: {
            freeq!([a__, b__], x_)
                && ltq!(p_, -1)
                && neq!(p_, -2)
                && igtq!(n_, 0)
                && integerq!(m_)
                && gtq!(&m_, Atom::num(2) * &n_ - 1)
        },
        rhs: {
            let angle = &a__ + &b__ * x_.pow(&n_);
            let recursive1 = rubi_rhs_int(&(x_.pow(&m_) * angle.sin().pow(&p_ + 2)), x_);
            let recursive2 = rubi_rhs_int(
                &(x_.pow(&m_ - Atom::num(2) * &n_) * angle.sin().pow(&p_ + 2)),
                x_,
            );
            rubi_simp(&(x_.pow(&m_ - &n_ + 1) * angle.cos() * angle.sin().pow(&p_ + 1)
                    / (&b__ * &n_ * (&p_ + 1))), x_)
                    - rubi_simp(&((&m_ - &n_ + 1) * x_.pow(&m_ - Atom::num(2) * &n_ + 1)
                        * angle.sin().pow(&p_ + 2)
                        / (b__.pow(2) * n_.pow(2) * (&p_ + 1) * (&p_ + 2))), x_)
                    + rubi_star((&p_ + 2) / (&p_ + 1), recursive1)
                    + rubi_star((&m_ - &n_ + 1) * (&m_ - Atom::num(2) * &n_ + 1)
                            / (b__.pow(2) * n_.pow(2) * (&p_ + 1) * (&p_ + 2)), recursive2)
        },
    ));
}

fn push_rules_rule_3889(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, n_, p_, m_, x_);
    rules.push(rubi_rule!(
        order: 3889,
        source: "Int[x_^m_.*Cos[a_.+b_.*x_^n_]^p_,x_Symbol] :=
          -x^(m-n+1)*Sin[a+b*x^n]*Cos[a+b*x^n]^(p+1)/(b*n*(p+1)) -
          (m-n+1)*x^(m-2*n+1)*Cos[a+b*x^n]^(p+2)/(b^2*n^2*(p+1)*(p+2)) +
          (p+2)/(p+1) \\[Star] Int[x^m*Cos[a+b*x^n]^(p+2),x] +
          (m-n+1)*(m-2*n+1)/(b^2*n^2*(p+1)*(p+2)) \\[Star] Int[x^(m-2*n)*Cos[a+b*x^n]^(p+2),x] /;
        FreeQ[{a,b},x] && LtQ[p,-1] && NeQ[p,-2] && IGtQ[n,0] && IGtQ[m,2*n-1]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: ["G&R 2.643.1'", "G&R 2.643.2"],
        pattern:  rubi_shared_pattern_17(symbols),
        with: [m_, a__, b__, n_, p_, x_],
        optional: [m_, a__, b__],
        when: {
            freeq!([a__, b__], x_)
                && ltq!(p_, -1)
                && neq!(p_, -2)
                && igtq!(n_, 0)
                && integerq!(m_)
                && gtq!(&m_, Atom::num(2) * &n_ - 1)
        },
        rhs: {
            let angle = &a__ + &b__ * x_.pow(&n_);
            let recursive1 = rubi_rhs_int(&(x_.pow(&m_) * angle.cos().pow(&p_ + 2)), x_);
            let recursive2 = rubi_rhs_int(
                &(x_.pow(&m_ - Atom::num(2) * &n_) * angle.cos().pow(&p_ + 2)),
                x_,
            );
            rubi_simp(&(Atom::num(-1) * x_.pow(&m_ - &n_ + 1) * angle.sin() * angle.cos().pow(&p_ + 1)
                    / (&b__ * &n_ * (&p_ + 1))), x_)
                    - rubi_simp(&((&m_ - &n_ + 1) * x_.pow(&m_ - Atom::num(2) * &n_ + 1)
                        * angle.cos().pow(&p_ + 2)
                        / (b__.pow(2) * n_.pow(2) * (&p_ + 1) * (&p_ + 2))), x_)
                    + rubi_star((&p_ + 2) / (&p_ + 1), recursive1)
                    + rubi_star((&m_ - &n_ + 1) * (&m_ - Atom::num(2) * &n_ + 1)
                            / (b__.pow(2) * n_.pow(2) * (&p_ + 1) * (&p_ + 2)), recursive2)
        },
    ));
}

fn push_rules_rule_3890(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, m_, x_);
    rules.push(rubi_rule!(
        order: 3890,
        source: "Int[x_^m_.*(a_.+b_.*Sin[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
          -Subst[Int[(a+b*Sin[c+d*x^(-n)])^p/x^(m+2),x],x,1/x] /;
        FreeQ[{a,b,c,d},x] && IGtQ[p,0] && ILtQ[n,0] && IntegerQ[m] && EqQ[n,-2]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_16(symbols),
        with: [m_, a__, b__, c__, d__, n_, p_, x_],
        optional: [m_, a__, b__, c__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && igtq!(p_, 0)
                && iltq!(n_, 0)
                && integerq!(m_)
                && eqq!(n_, -2)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub = Atom::var(substitution_symbol);
            let transformed_integrand =
                (&a__ + &b__ * (&c__ + &d__ * sub.pow(-&n_)).sin()).pow(&p_)
                    / sub.pow(&m_ + 2);
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);
            -rubi_subst(&transformed, substitution_symbol, Atom::num(1) / x_)
        },
    ));
}

fn push_rules_rule_3891(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, m_, x_);
    rules.push(rubi_rule!(
        order: 3891,
        source: "Int[x_^m_.*(a_.+b_.*Cos[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
          -Subst[Int[(a+b*Cos[c+d*x^(-n)])^p/x^(m+2),x],x,1/x] /;
        FreeQ[{a,b,c,d},x] && IGtQ[p,0] && ILtQ[n,0] && IntegerQ[m] && EqQ[n,-2]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_15(symbols),
        with: [m_, a__, b__, c__, d__, n_, p_, x_],
        optional: [m_, a__, b__, c__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && igtq!(p_, 0)
                && iltq!(n_, 0)
                && integerq!(m_)
                && eqq!(n_, -2)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub = Atom::var(substitution_symbol);
            let transformed_integrand =
                (&a__ + &b__ * (&c__ + &d__ * sub.pow(-&n_)).cos()).pow(&p_)
                    / sub.pow(&m_ + 2);
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);
            -rubi_subst(&transformed, substitution_symbol, Atom::num(1) / x_)
        },
    ));
}

fn push_rules_rule_3892(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, p_, m_, x_);
    rules.push(rubi_rule!(
        order: 3892,
        source: "Int[(e_.*x_)^m_*(a_.+b_.*Sin[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
          With[{k=Denominator[m]},
          -k/e \\[Star] Subst[Int[(a+b*Sin[c+d/(e^n*x^(k*n))])^p/x^(k*(m+1)+1),x],x,1/(e*x)^(1/k)]] /;
        FreeQ[{a,b,c,d,e},x] && IGtQ[p,0] && ILtQ[n,0] && FractionQ[m]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [e__, m_, a__, b__, c__, d__, n_, p_, x_],
        optional: [e__, a__, b__, c__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && igtq!(p_, 0)
                && iltq!(n_, 0)
                && fractionq!(m_)
        },
        rhs: {
            let k_i = rubi_denominator(&m_).rubi_rhs();
            let k = Atom::num(k_i);
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub = Atom::var(substitution_symbol);
            let transformed_integrand = (&a__
                + &b__ * (&c__ + &d__ / (e__.pow(&n_) * sub.pow(&k * &n_))).sin())
            .pow(&p_)
                / sub.pow(&k * (&m_ + 1) + 1);
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);
            rubi_star(-&k / &e__, rubi_subst(
                    &transformed,
                    substitution_symbol,
                    Atom::num(1) / (&e__ * x_).pow(Atom::num(1) / k_i),
                ))
        },
    ));
}

fn push_rules_rule_3893(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, p_, m_, x_);
    rules.push(rubi_rule!(
        order: 3893,
        source: "Int[(e_.*x_)^m_*(a_.+b_.*Cos[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
          With[{k=Denominator[m]},
          -k/e \\[Star] Subst[Int[(a+b*Cos[c+d/(e^n*x^(k*n))])^p/x^(k*(m+1)+1),x],x,1/(e*x)^(1/k)]] /;
        FreeQ[{a,b,c,d,e},x] && IGtQ[p,0] && ILtQ[n,0] && FractionQ[m]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [e__, m_, a__, b__, c__, d__, n_, p_, x_],
        optional: [e__, a__, b__, c__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && igtq!(p_, 0)
                && iltq!(n_, 0)
                && fractionq!(m_)
        },
        rhs: {
            let k_i = rubi_denominator(&m_).rubi_rhs();
            let k = Atom::num(k_i);
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub = Atom::var(substitution_symbol);
            let transformed_integrand = (&a__
                + &b__ * (&c__ + &d__ / (e__.pow(&n_) * sub.pow(&k * &n_))).cos())
            .pow(&p_)
                / sub.pow(&k * (&m_ + 1) + 1);
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);
            rubi_star(-&k / &e__, rubi_subst(
                    &transformed,
                    substitution_symbol,
                    Atom::num(1) / (&e__ * x_).pow(Atom::num(1) / k_i),
                ))
        },
    ));
}

fn push_rules_rule_3894(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, p_, m_, x_);
    rules.push(rubi_rule!(
        order: 3894,
        source: "Int[(e_.*x_)^m_*(a_.+b_.*Sin[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
          -(e*x)^m*(x^(-1))^m \\[Star] Subst[Int[(a+b*Sin[c+d*x^(-n)])^p/x^(m+2),x],x,1/x] /;
        FreeQ[{a,b,c,d,e,m},x] && IGtQ[p,0] && ILtQ[n,0] && Not[RationalQ[m]]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [e__, m_, a__, b__, c__, d__, n_, p_, x_],
        optional: [e__, a__, b__, c__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_], x_)
                && igtq!(p_, 0)
                && iltq!(n_, 0)
                && !rationalq!(m_)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub = Atom::var(substitution_symbol);
            let transformed_integrand =
                (&a__ + &b__ * (&c__ + &d__ * sub.pow(-&n_)).sin()).pow(&p_)
                    / sub.pow(&m_ + 2);
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);
            rubi_star(-(&e__ * x_).pow(&m_) * x_.pow(-1).pow(&m_), rubi_subst(
                    &transformed,
                    substitution_symbol,
                    Atom::num(1) / x_,
                ))
        },
    ));
}

fn push_rules_rule_3895(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, p_, m_, x_);
    rules.push(rubi_rule!(
        order: 3895,
        source: "Int[(e_.*x_)^m_*(a_.+b_.*Cos[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
          -(e*x)^m*(x^(-1))^m \\[Star] Subst[Int[(a+b*Cos[c+d*x^(-n)])^p/x^(m+2),x],x,1/x] /;
        FreeQ[{a,b,c,d,e,m},x] && IGtQ[p,0] && ILtQ[n,0] && Not[RationalQ[m]]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [e__, m_, a__, b__, c__, d__, n_, p_, x_],
        optional: [e__, a__, b__, c__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_], x_)
                && igtq!(p_, 0)
                && iltq!(n_, 0)
                && !rationalq!(m_)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub = Atom::var(substitution_symbol);
            let transformed_integrand =
                (&a__ + &b__ * (&c__ + &d__ * sub.pow(-&n_)).cos()).pow(&p_)
                    / sub.pow(&m_ + 2);
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);
            rubi_star(-(&e__ * x_).pow(&m_) * x_.pow(-1).pow(&m_), rubi_subst(
                    &transformed,
                    substitution_symbol,
                    Atom::num(1) / x_,
                ))
        },
    ));
}

fn push_rules_rule_3896(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, m_, x_);
    rules.push(rubi_rule!(
        order: 3896,
        source: "Int[x_^m_.*(a_.+b_.*Sin[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
          Module[{k=Denominator[n]},
          k \\[Star] Subst[Int[x^(k*(m+1)-1)*(a+b*Sin[c+d*x^(k*n)])^p,x],x,x^(1/k)]] /;
        FreeQ[{a,b,c,d,m},x] && IntegerQ[p] && FractionQ[n]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_16(symbols),
        with: [m_, a__, b__, c__, d__, n_, p_, x_],
        optional: [m_, a__, b__, c__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__, m_], x_)
                && integerq!(p_)
                && fractionq!(n_)
        },
        rhs: {
            let k_i = rubi_denominator(&n_).rubi_rhs();
            let k = Atom::num(k_i);
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub = Atom::var(substitution_symbol);
            let transformed_integrand = sub.pow(&k * (&m_ + 1) - 1)
                * (&a__ + &b__ * (&c__ + &d__ * sub.pow(&k * &n_)).sin()).pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);
            rubi_star(k, rubi_subst(
                    &transformed,
                    substitution_symbol,
                    x_.pow(Atom::num(1) / k_i),
                ))
        },
    ));
}

fn push_rules_rule_3897(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, m_, x_);
    rules.push(rubi_rule!(
        order: 3897,
        source: "Int[x_^m_.*(a_.+b_.*Cos[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
          Module[{k=Denominator[n]},
          k \\[Star] Subst[Int[x^(k*(m+1)-1)*(a+b*Cos[c+d*x^(k*n)])^p,x],x,x^(1/k)]] /;
        FreeQ[{a,b,c,d,m},x] && IntegerQ[p] && FractionQ[n]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_15(symbols),
        with: [m_, a__, b__, c__, d__, n_, p_, x_],
        optional: [m_, a__, b__, c__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__, m_], x_)
                && integerq!(p_)
                && fractionq!(n_)
        },
        rhs: {
            let k_i = rubi_denominator(&n_).rubi_rhs();
            let k = Atom::num(k_i);
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub = Atom::var(substitution_symbol);
            let transformed_integrand = sub.pow(&k * (&m_ + 1) - 1)
                * (&a__ + &b__ * (&c__ + &d__ * sub.pow(&k * &n_)).cos()).pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);
            rubi_star(k, rubi_subst(
                    &transformed,
                    substitution_symbol,
                    x_.pow(Atom::num(1) / k_i),
                ))
        },
    ));
}

fn push_rules_rule_3898(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, p_, m_, x_);
    rules.push(rubi_rule!(
        order: 3898,
        source: "Int[(e_*x_)^m_*(a_.+b_.*Sin[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
          e^IntPart[m]*(e*x)^FracPart[m]/x^FracPart[m] \\[Star] Int[x^m*(a+b*Sin[c+d*x^n])^p,x] /;
        FreeQ[{a,b,c,d,e,m},x] && IntegerQ[p] && FractionQ[n]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [e__, m_, a__, b__, c__, d__, n_, p_, x_],
        optional: [a__, b__, c__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_], x_)
                && integerq!(p_)
                && fractionq!(n_)
        },
        rhs: {
            let frac_m = rubi_frac_part(&m_);
            let recursive_integrand =
                x_.pow(&m_) * (&a__ + &b__ * (&c__ + &d__ * x_.pow(&n_)).sin()).pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            rubi_star(e__.pow(rubi_int_part(&m_)) * (&e__ * x_).pow(&frac_m)
                    / x_.pow(frac_m), recursive)
        },
    ));
}

fn push_rules_rule_3899(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, p_, m_, x_);
    rules.push(rubi_rule!(
        order: 3899,
        source: "Int[(e_*x_)^m_*(a_.+b_.*Cos[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
          e^IntPart[m]*(e*x)^FracPart[m]/x^FracPart[m] \\[Star] Int[x^m*(a+b*Cos[c+d*x^n])^p,x] /;
        FreeQ[{a,b,c,d,e,m},x] && IntegerQ[p] && FractionQ[n]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [e__, m_, a__, b__, c__, d__, n_, p_, x_],
        optional: [a__, b__, c__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_], x_)
                && integerq!(p_)
                && fractionq!(n_)
        },
        rhs: {
            let frac_m = rubi_frac_part(&m_);
            let recursive_integrand =
                x_.pow(&m_) * (&a__ + &b__ * (&c__ + &d__ * x_.pow(&n_)).cos()).pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            rubi_star(e__.pow(rubi_int_part(&m_)) * (&e__ * x_).pow(&frac_m)
                    / x_.pow(frac_m), recursive)
        },
    ));
}

fn push_rules_rule_3900(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, m_, x_);
    rules.push(rubi_rule!(
        order: 3900,
        source: "Int[x_^m_.*(a_.+b_.*Sin[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
          1/(m+1) \\[Star] Subst[Int[(a+b*Sin[c+d*x^Simplify[n/(m+1)]])^p,x],x,x^(m+1)] /;
        FreeQ[{a,b,c,d,m,n},x] && IntegerQ[p] && NeQ[m,-1] && IGtQ[Simplify[n/(m+1)],0] && Not[IntegerQ[n]]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_16(symbols),
        with: [m_, a__, b__, c__, d__, n_, p_, x_],
        optional: [m_, a__, b__, c__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__, m_, n_], x_)
                && integerq!(p_)
                && neq!(m_, -1)
                && {
                    let s = rubi_simplify(&(&n_ / (&m_ + 1)));
                    igtq!(s, 0) && !integerq!(n_)
                }
        },
        rhs: {
            let s = rubi_simplify(&(&n_ / (&m_ + 1)));
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub = Atom::var(substitution_symbol);
            let transformed_integrand = (&a__ + &b__ * (&c__ + &d__ * sub.pow(s)).sin()).pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);
            rubi_star(Atom::num(1) / (&m_ + 1), rubi_subst(
                    &transformed,
                    substitution_symbol,
                    x_.pow(&m_ + 1),
                ))
        },
    ));
}

fn push_rules_rule_3901(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, m_, x_);
    rules.push(rubi_rule!(
        order: 3901,
        source: "Int[x_^m_.*(a_.+b_.*Cos[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
          1/(m+1) \\[Star] Subst[Int[(a+b*Cos[c+d*x^Simplify[n/(m+1)]])^p,x],x,x^(m+1)] /;
        FreeQ[{a,b,c,d,m,n},x] && IntegerQ[p] && NeQ[m,-1] && IGtQ[Simplify[n/(m+1)],0] && Not[IntegerQ[n]]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_15(symbols),
        with: [m_, a__, b__, c__, d__, n_, p_, x_],
        optional: [m_, a__, b__, c__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__, m_, n_], x_)
                && integerq!(p_)
                && neq!(m_, -1)
                && {
                    let s = rubi_simplify(&(&n_ / (&m_ + 1)));
                    igtq!(s, 0) && !integerq!(n_)
                }
        },
        rhs: {
            let s = rubi_simplify(&(&n_ / (&m_ + 1)));
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub = Atom::var(substitution_symbol);
            let transformed_integrand = (&a__ + &b__ * (&c__ + &d__ * sub.pow(s)).cos()).pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);
            rubi_star(Atom::num(1) / (&m_ + 1), rubi_subst(
                    &transformed,
                    substitution_symbol,
                    x_.pow(&m_ + 1),
                ))
        },
    ));
}

fn push_rules_rule_3902(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, p_, m_, x_);
    rules.push(rubi_rule!(
        order: 3902,
        source: "Int[(e_*x_)^m_*(a_.+b_.*Sin[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
          e^IntPart[m]*(e*x)^FracPart[m]/x^FracPart[m] \\[Star] Int[x^m*(a+b*Sin[c+d*x^n])^p,x] /;
        FreeQ[{a,b,c,d,e,m,n},x] && IntegerQ[p] && NeQ[m,-1] && IGtQ[Simplify[n/(m+1)],0] && Not[IntegerQ[n]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [e__, m_, a__, b__, c__, d__, n_, p_, x_],
        optional: [a__, b__, c__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_], x_)
                && integerq!(p_)
                && neq!(m_, -1)
                && {
                    let s = rubi_simplify(&(&n_ / (&m_ + 1)));
                    igtq!(s, 0) && !integerq!(n_)
                }
        },
        rhs: {
            let frac_m = rubi_frac_part(&m_);
            let recursive_integrand =
                x_.pow(&m_) * (&a__ + &b__ * (&c__ + &d__ * x_.pow(&n_)).sin()).pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            rubi_star(e__.pow(rubi_int_part(&m_)) * (&e__ * x_).pow(&frac_m)
                    / x_.pow(frac_m), recursive)
        },
    ));
}

fn push_rules_rule_3903(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, p_, m_, x_);
    rules.push(rubi_rule!(
        order: 3903,
        source: "Int[(e_*x_)^m_*(a_.+b_.*Cos[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
          e^IntPart[m]*(e*x)^FracPart[m]/x^FracPart[m] \\[Star] Int[x^m*(a+b*Cos[c+d*x^n])^p,x] /;
        FreeQ[{a,b,c,d,e,m,n},x] && IntegerQ[p] && NeQ[m,-1] && IGtQ[Simplify[n/(m+1)],0] && Not[IntegerQ[n]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [e__, m_, a__, b__, c__, d__, n_, p_, x_],
        optional: [a__, b__, c__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_], x_)
                && integerq!(p_)
                && neq!(m_, -1)
                && {
                    let s = rubi_simplify(&(&n_ / (&m_ + 1)));
                    igtq!(s, 0) && !integerq!(n_)
                }
        },
        rhs: {
            let frac_m = rubi_frac_part(&m_);
            let recursive_integrand =
                x_.pow(&m_) * (&a__ + &b__ * (&c__ + &d__ * x_.pow(&n_)).cos()).pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            rubi_star(e__.pow(rubi_int_part(&m_)) * (&e__ * x_).pow(&frac_m)
                    / x_.pow(frac_m), recursive)
        },
    ));
}

fn push_rules_rule_3904(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; c__, d__, e__, n_, m_, x_);
    rules.push(rubi_rule!(
        order: 3904,
        source: "Int[(e_.*x_)^m_.*Sin[c_.+d_.*x_^n_],x_Symbol] :=
          I/2 \\[Star] Int[(e*x)^m*E^(-c*I-d*I*x^n),x] - I/2 \\[Star] Int[(e*x)^m*E^(c*I+d*I*x^n),x] /;
        FreeQ[{c,d,e,m,n},x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_12(symbols),
        with: [e__, m_, c__, d__, n_, x_],
        optional: [e__, m_, c__, d__],
        when: { freeq!([c__, d__, e__, m_, n_], x_) },
        rhs: {
            let i = rubi_i();
            let scaled_power = (&e__ * x_).pow(&m_);
            let recursive1 = rubi_rhs_int(
                &(&scaled_power * (-&c__ * &i - &d__ * &i * x_.pow(&n_)).exp()),
                x_,
            );
            let recursive2 = rubi_rhs_int(
                &(&scaled_power * (&c__ * &i + &d__ * &i * x_.pow(&n_)).exp()),
                x_,
            );
            rubi_star(&i / 2, recursive1)
                    + rubi_star(-i / 2, recursive2)
        },
    ));
}

fn push_rules_rule_3905(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; c__, d__, e__, n_, m_, x_);
    rules.push(rubi_rule!(
        order: 3905,
        source: "Int[(e_.*x_)^m_.*Cos[c_.+d_.*x_^n_],x_Symbol] :=
          1/2 \\[Star] Int[(e*x)^m*E^(-c*I-d*I*x^n),x] + 1/2 \\[Star] Int[(e*x)^m*E^(c*I+d*I*x^n),x] /;
        FreeQ[{c,d,e,m,n},x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_11(symbols),
        with: [e__, m_, c__, d__, n_, x_],
        optional: [e__, m_, c__, d__],
        when: { freeq!([c__, d__, e__, m_, n_], x_) },
        rhs: {
            let i = rubi_i();
            let scaled_power = (&e__ * x_).pow(&m_);
            let recursive1 = rubi_rhs_int(
                &(&scaled_power * (-&c__ * &i - &d__ * &i * x_.pow(&n_)).exp()),
                x_,
            );
            let recursive2 = rubi_rhs_int(
                &(&scaled_power * (&c__ * &i + &d__ * &i * x_.pow(&n_)).exp()),
                x_,
            );
            rubi_star(Atom::num(1) / 2, recursive1)
                    + rubi_star(Atom::num(1) / 2, recursive2)
        },
    ));
}

fn push_rules_rule_3906(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, p_, m_, x_);
    rules.push(rubi_rule!(
        order: 3906,
        source: "Int[(e_.*x_)^m_.*(a_.+b_.*Sin[c_.+d_.*x_^n_])^p_,x_Symbol] :=
          Int[ExpandTrigReduce[(e*x)^m,(a+b*Sin[c+d*x^n])^p,x],x] /;
        FreeQ[{a,b,c,d,e,m,n},x] && IGtQ[p,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [e__, m_, a__, b__, c__, d__, n_, p_, x_],
        optional: [e__, m_, a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_], x_)
                && igtq!(p_, 0)
        },
        rhs: {
            let u = (&e__ * x_).pow(&m_);
            let v = (&a__ + &b__ * (&c__ + &d__ * x_.pow(&n_)).sin()).pow(&p_);
            let expanded = rubi_expand_trig_reduce(&u, &v, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_3907(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, p_, m_, x_);
    rules.push(rubi_rule!(
        order: 3907,
        source: "Int[(e_.*x_)^m_.*(a_.+b_.*Cos[c_.+d_.*x_^n_])^p_,x_Symbol] :=
          Int[ExpandTrigReduce[(e*x)^m,(a+b*Cos[c+d*x^n])^p,x],x] /;
        FreeQ[{a,b,c,d,e,m,n},x] && IGtQ[p,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [e__, m_, a__, b__, c__, d__, n_, p_, x_],
        optional: [e__, m_, a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_], x_)
                && igtq!(p_, 0)
        },
        rhs: {
            let u = (&e__ * x_).pow(&m_);
            let v = (&a__ + &b__ * (&c__ + &d__ * x_.pow(&n_)).cos()).pow(&p_);
            let expanded = rubi_expand_trig_reduce(&u, &v, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_3908(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, p_, m_, x_);
    rules.push(rubi_rule!(
        order: 3908,
        source: "Int[(e_.*x_)^m_.*(a_.+b_.*Sin[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
          Unintegrable[(e*x)^m*(a+b*Sin[c+d*x^n])^p,x] /;
        FreeQ[{a,b,c,d,e,m,n,p},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [e__, m_, a__, b__, c__, d__, n_, p_, x_],
        optional: [e__, m_, a__, b__, c__, d__, p_],
        when: { freeq!([a__, b__, c__, d__, e__, m_, n_, p_], x_) },
        rhs: {
            let integrand =
                (&e__ * x_).pow(&m_) * (&a__ + &b__ * (&c__ + &d__ * x_.pow(&n_)).sin()).pow(&p_);
            rubi_unintegrable(integrand, x_)
        },
    ));
}

fn push_rules_rule_3909(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, p_, m_, x_);
    rules.push(rubi_rule!(
        order: 3909,
        source: "Int[(e_.*x_)^m_.*(a_.+b_.*Cos[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
          Unintegrable[(e*x)^m*(a+b*Cos[c+d*x^n])^p,x] /;
        FreeQ[{a,b,c,d,e,m,n,p},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [e__, m_, a__, b__, c__, d__, n_, p_, x_],
        optional: [e__, m_, a__, b__, c__, d__, p_],
        when: { freeq!([a__, b__, c__, d__, e__, m_, n_, p_], x_) },
        rhs: {
            let integrand =
                (&e__ * x_).pow(&m_) * (&a__ + &b__ * (&c__ + &d__ * x_.pow(&n_)).cos()).pow(&p_);
            rubi_unintegrable(integrand, x_)
        },
    ));
}

fn push_rules_rule_3910(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, e__, p_, m_, u_, x_);
    rules.push(rubi_rule!(
        order: 3910,
        source: "Int[(e_*x_)^m_.*(a_.+b_.*Sin[u_])^p_.,x_Symbol] :=
          Int[(e*x)^m*(a+b*Sin[ExpandToSum[u,x]])^p,x] /;
        FreeQ[{a,b,e,m,p},x] && BinomialQ[u,x] && Not[BinomialMatchQ[u,x]]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: (e__ * x_).pow(m_) * (a__ + b__ * (Atom::var(u_)).sin()).pow(p_),
        with: [e__, m_, a__, b__, u_, p_, x_],
        optional: [m_, a__, b__, p_],
        when: {
            freeq!([a__, b__, e__, m_, p_], x_)
                && rubi_binomial_q(&u_, x_)
                && !rubi_binomial_match_q(&u_, x_)
        },
        rhs: {
            let integrand = (&e__ * x_).pow(&m_) * (&a__ + &b__ * rubi_expand_to_sum(&u_, x_).sin()).pow(&p_);
            rubi_rhs_int(&integrand, x_)
        },
    ));
}

fn push_rules_rule_3911(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, e__, p_, m_, u_, x_);
    rules.push(rubi_rule!(
        order: 3911,
        source: "Int[(e_*x_)^m_.*(a_.+b_.*Cos[u_])^p_.,x_Symbol] :=
          Int[(e*x)^m*(a+b*Cos[ExpandToSum[u,x]])^p,x] /;
        FreeQ[{a,b,e,m,p},x] && BinomialQ[u,x] && Not[BinomialMatchQ[u,x]]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: (e__ * x_).pow(m_) * (a__ + b__ * (Atom::var(u_)).cos()).pow(p_),
        with: [e__, m_, a__, b__, u_, p_, x_],
        optional: [m_, a__, b__, p_],
        when: {
            freeq!([a__, b__, e__, m_, p_], x_)
                && rubi_binomial_q(&u_, x_)
                && !rubi_binomial_match_q(&u_, x_)
        },
        rhs: {
            let integrand = (&e__ * x_).pow(&m_) * (&a__ + &b__ * rubi_expand_to_sum(&u_, x_).cos()).pow(&p_);
            rubi_rhs_int(&integrand, x_)
        },
    ));
}

fn push_rules_rule_3912(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, h__, n_, p_, m_, x_);
    rules.push(rubi_rule!(
        order: 3912,
        source: "Int[(g_.+h_.*x_)^m_.*(a_.+b_.*Sin[c_.+d_.*(e_.+f_.*x_)^n_])^p_.,x_Symbol] :=
          1/(n*f) \\[Star] Subst[Int[ExpandIntegrand[(a+b*Sin[c+d*x])^p,x^(1/n-1)*(g-e*h/f+h*x^(1/n)/f)^m,x],x],x,(e+f*x)^n] /;
        FreeQ[{a,b,c,d,e,f,g,h,m},x] && IGtQ[p,0] && IntegerQ[1/n]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_14(symbols),
        with: [g__, h__, m_, a__, b__, c__, d__, e__, f__, n_, p_, x_],
        optional: [g__, h__, m_, a__, b__, c__, d__, e__, f__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__, m_], x_)
                && igtq!(p_, 0)
                && integerq!(Atom::num(1) / &n_)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub = Atom::var(substitution_symbol);
            let u = (&a__ + &b__ * (&c__ + &d__ * &sub).sin()).pow(&p_);
            let v = sub.pow(Atom::num(1) / &n_ - 1)
                * (&g__ - &e__ * &h__ / &f__ + &h__ * sub.pow(Atom::num(1) / &n_) / &f__).pow(&m_);
            let expanded = rubi_expand_integrand_product(&u, &v, substitution_symbol);
            let transformed = rubi_rhs_int(&expanded, substitution_symbol);
            let replacement = (&e__ + &f__ * x_).pow(&n_);

            rubi_star(Atom::num(1) / (&n_ * &f__), rubi_subst(&transformed, substitution_symbol, replacement))
        },
    ));
}

fn push_rules_rule_3913(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, h__, n_, p_, m_, x_);
    rules.push(rubi_rule!(
        order: 3913,
        source: "Int[(g_.+h_.*x_)^m_.*(a_.+b_.*Cos[c_.+d_.*(e_.+f_.*x_)^n_])^p_.,x_Symbol] :=
          1/(n*f) \\[Star] Subst[Int[ExpandIntegrand[(a+b*Cos[c+d*x])^p,x^(1/n-1)*(g-e*h/f+h*x^(1/n)/f)^m,x],x],x,(e+f*x)^n] /;
        FreeQ[{a,b,c,d,e,f,g,h,m},x] && IGtQ[p,0] && IntegerQ[1/n]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_13(symbols),
        with: [g__, h__, m_, a__, b__, c__, d__, e__, f__, n_, p_, x_],
        optional: [g__, h__, m_, a__, b__, c__, d__, e__, f__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__, m_], x_)
                && igtq!(p_, 0)
                && integerq!(Atom::num(1) / &n_)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub = Atom::var(substitution_symbol);
            let u = (&a__ + &b__ * (&c__ + &d__ * &sub).cos()).pow(&p_);
            let v = sub.pow(Atom::num(1) / &n_ - 1)
                * (&g__ - &e__ * &h__ / &f__ + &h__ * sub.pow(Atom::num(1) / &n_) / &f__).pow(&m_);
            let expanded = rubi_expand_integrand_product(&u, &v, substitution_symbol);
            let transformed = rubi_rhs_int(&expanded, substitution_symbol);
            let replacement = (&e__ + &f__ * x_).pow(&n_);

            rubi_star(Atom::num(1) / (&n_ * &f__), rubi_subst(&transformed, substitution_symbol, replacement))
        },
    ));
}

fn push_rules_rule_3914(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, h__, n_, p_, m_, x_);
    rules.push(rubi_rule!(
        order: 3914,
        source: "Int[(g_.+h_.*x_)^m_.*(a_.+b_.*Sin[c_.+d_.*(e_.+f_.*x_)^n_])^p_.,x_Symbol] :=
          Module[{k=If[FractionQ[n],Denominator[n],1]},
          k/f^(m+1) \\[Star] Subst[Int[ExpandIntegrand[(a+b*Sin[c+d*x^(k*n)])^p,x^(k-1)*(f*g-e*h+h*x^k)^m,x],x],x,(e+f*x)^(1/k)]] /;
        FreeQ[{a,b,c,d,e,f,g,h},x] && IGtQ[p,0] && IGtQ[m,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_14(symbols),
        with: [g__, h__, m_, a__, b__, c__, d__, e__, f__, n_, p_, x_],
        optional: [g__, h__, m_, a__, b__, c__, d__, e__, f__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__], x_)
                && igtq!(p_, 0)
                && igtq!(m_, 0)
        },
        rhs: {
            let k_i = if fractionq!(n_) { rubi_denominator(&n_).rubi_rhs() } else { 1 };
            let k = Atom::num(k_i);
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub = Atom::var(substitution_symbol);
            let u = (&a__ + &b__ * (&c__ + &d__ * sub.pow(&k * &n_)).sin()).pow(&p_);
            let v = sub.pow(&k - 1) * (&f__ * &g__ - &e__ * &h__ + &h__ * sub.pow(&k)).pow(&m_);
            let expanded = rubi_expand_integrand_product(&u, &v, substitution_symbol);
            let transformed = rubi_rhs_int(&expanded, substitution_symbol);
            let replacement = (&e__ + &f__ * x_).pow(Atom::num(1) / Atom::num(k_i));

            rubi_star(&k / f__.pow(&m_ + 1), rubi_subst(&transformed, substitution_symbol, replacement))
        },
    ));
}

fn push_rules_rule_3915(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, h__, n_, p_, m_, x_);
    rules.push(rubi_rule!(
        order: 3915,
        source: "Int[(g_.+h_.*x_)^m_.*(a_.+b_.*Cos[c_.+d_.*(e_.+f_.*x_)^n_])^p_.,x_Symbol] :=
          Module[{k=If[FractionQ[n],Denominator[n],1]},
          k/f^(m+1) \\[Star] Subst[Int[ExpandIntegrand[(a+b*Cos[c+d*x^(k*n)])^p,x^(k-1)*(f*g-e*h+h*x^k)^m,x],x],x,(e+f*x)^(1/k)]] /;
        FreeQ[{a,b,c,d,e,f,g,h},x] && IGtQ[p,0] && IGtQ[m,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_13(symbols),
        with: [g__, h__, m_, a__, b__, c__, d__, e__, f__, n_, p_, x_],
        optional: [g__, h__, m_, a__, b__, c__, d__, e__, f__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__], x_)
                && igtq!(p_, 0)
                && igtq!(m_, 0)
        },
        rhs: {
            let k_i = if fractionq!(n_) { rubi_denominator(&n_).rubi_rhs() } else { 1 };
            let k = Atom::num(k_i);
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub = Atom::var(substitution_symbol);
            let u = (&a__ + &b__ * (&c__ + &d__ * sub.pow(&k * &n_)).cos()).pow(&p_);
            let v = sub.pow(&k - 1) * (&f__ * &g__ - &e__ * &h__ + &h__ * sub.pow(&k)).pow(&m_);
            let expanded = rubi_expand_integrand_product(&u, &v, substitution_symbol);
            let transformed = rubi_rhs_int(&expanded, substitution_symbol);
            let replacement = (&e__ + &f__ * x_).pow(Atom::num(1) / Atom::num(k_i));

            rubi_star(&k / f__.pow(&m_ + 1), rubi_subst(&transformed, substitution_symbol, replacement))
        },
    ));
}

fn push_rules_rule_3916(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, h__, n_, p_, m_, x_);
    rules.push(rubi_rule!(
        order: 3916,
        source: "Int[(g_.+h_.*x_)^m_.*(a_.+b_.*Sin[c_.+d_.*(e_.+f_.*x_)^n_])^p_.,x_Symbol] :=
          1/f \\[Star] Subst[Int[(h*x/f)^m*(a+b*Sin[c+d*x^n])^p,x],x,e+f*x] /;
        FreeQ[{a,b,c,d,e,f,g,h,m},x] && IGtQ[p,0] && EqQ[f*g-e*h,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_14(symbols),
        with: [g__, h__, m_, a__, b__, c__, d__, e__, f__, n_, p_, x_],
        optional: [g__, h__, m_, a__, b__, c__, d__, e__, f__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__, m_], x_)
                && igtq!(p_, 0)
                && eqq!(&f__ * &g__ - &e__ * &h__, 0)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub = Atom::var(substitution_symbol);
            let transformed_integrand =
                (&h__ * &sub / &f__).pow(&m_) * (&a__ + &b__ * (&c__ + &d__ * sub.pow(&n_)).sin()).pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);

            rubi_star(Atom::num(1) / &f__, rubi_subst(
                    &transformed,
                    substitution_symbol,
                    &e__ + &f__ * x_,
                ))
        },
    ));
}

fn push_rules_rule_3917(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, h__, n_, p_, m_, x_);
    rules.push(rubi_rule!(
        order: 3917,
        source: "Int[(g_.+h_.*x_)^m_.*(a_.+b_.*Cos[c_.+d_.*(e_.+f_.*x_)^n_])^p_.,x_Symbol] :=
          1/f \\[Star] Subst[Int[(h*x/f)^m*(a+b*Cos[c+d*x^n])^p,x],x,e+f*x] /;
        FreeQ[{a,b,c,d,e,f,g,h,m},x] && IGtQ[p,0] && EqQ[f*g-e*h,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_13(symbols),
        with: [g__, h__, m_, a__, b__, c__, d__, e__, f__, n_, p_, x_],
        optional: [g__, h__, m_, a__, b__, c__, d__, e__, f__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__, m_], x_)
                && igtq!(p_, 0)
                && eqq!(&f__ * &g__ - &e__ * &h__, 0)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub = Atom::var(substitution_symbol);
            let transformed_integrand =
                (&h__ * &sub / &f__).pow(&m_) * (&a__ + &b__ * (&c__ + &d__ * sub.pow(&n_)).cos()).pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);

            rubi_star(Atom::num(1) / &f__, rubi_subst(
                    &transformed,
                    substitution_symbol,
                    &e__ + &f__ * x_,
                ))
        },
    ));
}

fn push_rules_rule_3918(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, h__, n_, p_, m_, x_);
    rules.push(rubi_rule!(
        order: 3918,
        source: "Int[(g_.+h_.*x_)^m_.*(a_.+b_.*Sin[c_.+d_.*(e_.+f_.*x_)^n_])^p_.,x_Symbol] :=
          Unintegrable[(g+h*x)^m*(a+b*Sin[c+d*(e+f*x)^n])^p,x] /;
        FreeQ[{a,b,c,d,e,f,g,h,m,n,p},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_14(symbols),
        with: [g__, h__, m_, a__, b__, c__, d__, e__, f__, n_, p_, x_],
        optional: [g__, h__, m_, a__, b__, c__, d__, e__, f__, p_],
        when: { freeq!([a__, b__, c__, d__, e__, f__, g__, h__, m_, n_, p_], x_) },
        rhs: {
            let integrand = (&g__ + &h__ * x_).pow(&m_)
                * (&a__ + &b__ * (&c__ + &d__ * (&e__ + &f__ * x_).pow(&n_)).sin()).pow(&p_);
            rubi_unintegrable(integrand, x_)
        },
    ));
}

fn push_rules_rule_3919(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, h__, n_, p_, m_, x_);
    rules.push(rubi_rule!(
        order: 3919,
        source: "Int[(g_.+h_.*x_)^m_.*(a_.+b_.*Cos[c_.+d_.*(e_.+f_.*x_)^n_])^p_.,x_Symbol] :=
          Unintegrable[(g+h*x)^m*(a+b*Cos[c+d*(e+f*x)^n])^p,x] /;
        FreeQ[{a,b,c,d,e,f,g,h,m,n,p},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_13(symbols),
        with: [g__, h__, m_, a__, b__, c__, d__, e__, f__, n_, p_, x_],
        optional: [g__, h__, m_, a__, b__, c__, d__, e__, f__, p_],
        when: { freeq!([a__, b__, c__, d__, e__, f__, g__, h__, m_, n_, p_], x_) },
        rhs: {
            let integrand = (&g__ + &h__ * x_).pow(&m_)
                * (&a__ + &b__ * (&c__ + &d__ * (&e__ + &f__ * x_).pow(&n_)).cos()).pow(&p_);
            rubi_unintegrable(integrand, x_)
        },
    ));
}

fn push_rules_rule_3920(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, n_, p_, m_, u_, v__);
    rules.push(rubi_rule!(
        order: 3920,
        source: "Int[v_^m_.*(a_.+b_.*Sin[c_.+d_.*u_^n_])^p_.,x_Symbol] :=
          Int[ExpandToSum[v,x]^m*(a+b*Sin[c+d*ExpandToSum[u,x]^n])^p,x] /;
        FreeQ[{a,b,c,d,m,n,p},x] && LinearQ[u,x] && LinearQ[v,x] && Not[LinearMatchQ[u,x] && LinearMatchQ[v,x]]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: Atom::var(v__).pow(m_) * (a__ + b__ * (c__ + d__ * Atom::var(u_).pow(n_)).sin()).pow(p_),
        with: [v__, m_, a__, b__, c__, d__, u_, n_, p_, x_],
        optional: [m_, a__, b__, c__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__, m_, n_, p_], x_)
                && rubi_linear_q(&u_, x_)
                && rubi_linear_q(&v__, x_)
                && !(rubi_linear_match_q(&u_, x_) && rubi_linear_match_q(&v__, x_))
        },
        rhs: {
            let integrand = rubi_expand_to_sum(&v__, x_).pow(&m_)
                * (&a__ + &b__ * (&c__ + &d__ * rubi_expand_to_sum(&u_, x_).pow(&n_)).sin()).pow(&p_);
            rubi_rhs_int(&integrand, x_)
        },
    ));
}

fn push_rules_rule_3921(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, n_, p_, m_, u_, v__);
    rules.push(rubi_rule!(
        order: 3921,
        source: "Int[v_^m_.*(a_.+b_.*Cos[c_.+d_.*u_^n_])^p_.,x_Symbol] :=
          Int[ExpandToSum[v,x]^m*(a+b*Cos[c+d*ExpandToSum[u,x]^n])^p,x] /;
        FreeQ[{a,b,c,d,m,n,p},x] && LinearQ[u,x] && LinearQ[v,x] && Not[LinearMatchQ[u,x] && LinearMatchQ[v,x]]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: Atom::var(v__).pow(m_) * (a__ + b__ * (c__ + d__ * Atom::var(u_).pow(n_)).cos()).pow(p_),
        with: [v__, m_, a__, b__, c__, d__, u_, n_, p_, x_],
        optional: [m_, a__, b__, c__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__, m_, n_, p_], x_)
                && rubi_linear_q(&u_, x_)
                && rubi_linear_q(&v__, x_)
                && !(rubi_linear_match_q(&u_, x_) && rubi_linear_match_q(&v__, x_))
        },
        rhs: {
            let integrand = rubi_expand_to_sum(&v__, x_).pow(&m_)
                * (&a__ + &b__ * (&c__ + &d__ * rubi_expand_to_sum(&u_, x_).pow(&n_)).cos()).pow(&p_);
            rubi_rhs_int(&integrand, x_)
        },
    ));
}

fn push_rules_rule_3922(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, n_, p_, m_, x_);
    rules.push(rubi_rule!(
        order: 3922,
        source: "Int[x_^m_.*Sin[a_.+b_.*x_^n_.]^p_.*Cos[a_.+b_.*x_^n_.],x_Symbol] :=
          Sin[a+b*x^n]^(p+1)/(b*n*(p+1)) /;
        FreeQ[{a,b,m,n,p},x] && EqQ[m,n-1] && NeQ[p,-1]",
        desc: "Power rule for integration",
        refs: [],
        pattern:  rubi_shared_pattern_21(symbols),
        with: [m_, a__, b__, n_, p_, x_],
        optional: [m_, a__, b__, n_, p_],
        when: {
            freeq!([a__, b__, m_, n_, p_], x_)
                && eqq!(m_, &n_ - 1)
                && neq!(p_, -1)
        },
        rhs: {
            rubi_simp(&((&a__ + &b__ * x_.pow(&n_)).sin().pow(&p_ + 1) / (&b__ * &n_ * (&p_ + 1))), x_)
        },
    ));
}

fn push_rules_rule_3923(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, n_, p_, m_, x_);
    rules.push(rubi_rule!(
        order: 3923,
        source: "Int[x_^m_.*Cos[a_.+b_.*x_^n_.]^p_.*Sin[a_.+b_.*x_^n_.],x_Symbol] :=
          -Cos[a+b*x^n]^(p+1)/(b*n*(p+1)) /;
        FreeQ[{a,b,m,n,p},x] && EqQ[m,n-1] && NeQ[p,-1]",
        desc: "Power rule for integration",
        refs: [],
        pattern:  rubi_shared_pattern_18(symbols),
        with: [m_, a__, b__, n_, p_, x_],
        optional: [m_, a__, b__, n_, p_],
        when: {
            freeq!([a__, b__, m_, n_, p_], x_)
                && eqq!(m_, &n_ - 1)
                && neq!(p_, -1)
        },
        rhs: {
            rubi_simp(&(-(&a__ + &b__ * x_.pow(&n_)).cos().pow(&p_ + 1) / (&b__ * &n_ * (&p_ + 1))), x_)
        },
    ));
}

fn push_rules_rule_3924(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, n_, p_, m_, x_);
    rules.push(rubi_rule!(
        order: 3924,
        source: "Int[x_^m_.*Sin[a_.+b_.*x_^n_.]^p_.*Cos[a_.+b_.*x_^n_.],x_Symbol] :=
          x^(m-n+1)*Sin[a+b*x^n]^(p+1)/(b*n*(p+1)) -
          (m-n+1)/(b*n*(p+1)) \\[Star] Int[x^(m-n)*Sin[a+b*x^n]^(p+1),x] /;
        FreeQ[{a,b,p},x] && LtQ[0,n,m+1] && NeQ[p,-1]",
        desc: "Integration by parts",
        refs: ["G&R 2.645.6", "G&R 2.645.3"],
        pattern:  rubi_shared_pattern_21(symbols),
        with: [m_, a__, b__, n_, p_, x_],
        optional: [m_, a__, b__, n_, p_],
        when: {
            freeq!([a__, b__, p_], x_)
                && ltq!(0, n_, &m_ + 1)
                && neq!(p_, -1)
        },
        rhs: {
            let denominator = &b__ * &n_ * (&p_ + 1);
            let recursive_integrand = x_.pow(&m_ - &n_) * (&a__ + &b__ * x_.pow(&n_)).sin().pow(&p_ + 1);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(x_.pow(&m_ - &n_ + 1) * (&a__ + &b__ * x_.pow(&n_)).sin().pow(&p_ + 1) / &denominator), x_)
                    + rubi_star(-(&m_ - &n_ + 1) / &denominator, recursive)
        },
    ));
}

fn push_rules_rule_3925(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, n_, p_, m_, x_);
    rules.push(rubi_rule!(
        order: 3925,
        source: "Int[x_^m_.*Cos[a_.+b_.*x_^n_.]^p_.*Sin[a_.+b_.*x_^n_.],x_Symbol] :=
          -x^(m-n+1)*Cos[a+b*x^n]^(p+1)/(b*n*(p+1)) +
          (m-n+1)/(b*n*(p+1)) \\[Star] Int[x^(m-n)*Cos[a+b*x^n]^(p+1),x] /;
        FreeQ[{a,b,p},x] && LtQ[0,n,m+1] && NeQ[p,-1]",
        desc: "Integration by parts",
        refs: ["G&R 2.645.6", "G&R 2.645.3"],
        pattern:  rubi_shared_pattern_18(symbols),
        with: [m_, a__, b__, n_, p_, x_],
        optional: [m_, a__, b__, n_, p_],
        when: {
            freeq!([a__, b__, p_], x_)
                && ltq!(0, n_, &m_ + 1)
                && neq!(p_, -1)
        },
        rhs: {
            let denominator = &b__ * &n_ * (&p_ + 1);
            let recursive_integrand = x_.pow(&m_ - &n_) * (&a__ + &b__ * x_.pow(&n_)).cos().pow(&p_ + 1);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(Atom::num(-1) * x_.pow(&m_ - &n_ + 1) * (&a__ + &b__ * x_.pow(&n_)).cos().pow(&p_ + 1) / &denominator), x_)
                    + rubi_star((&m_ - &n_ + 1) / &denominator, recursive)
        },
    ));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn downvalues_3810_through_3842_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .filter(|order| (3810..=3842).contains(order))
            .collect::<Vec<_>>();
        assert_eq!(orders, (3810..=3842).collect::<Vec<_>>());
    }

    #[test]
    fn downvalues_3843_through_3892_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .filter(|order| (3843..=3892).contains(order))
            .collect::<Vec<_>>();
        assert_eq!(orders, (3843..=3892).collect::<Vec<_>>());
    }

    #[test]
    fn downvalues_3893_through_3925_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .filter(|order| (3893..=3925).contains(order))
            .collect::<Vec<_>>();
        assert_eq!(orders, (3893..=3925).collect::<Vec<_>>());
    }
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
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (a__ + b__ * (c__ + d__ * (e__ + f__ * x_).pow(n_)).cos()).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (a__ + b__ * (c__ + d__ * (e__ + f__ * x_).pow(n_)).sin()).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_2(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (a__ + b__ * x_.pow(n_)).pow(p_) * (c__ + d__ * x_).sin()
}

#[inline(never)]
fn rubi_shared_pattern_3(symbols: &RubiSymbols) -> Atom {
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    (c__ + d__ * (e__ + f__ * x_).pow(n_)).cos()
}

#[inline(never)]
fn rubi_shared_pattern_4(symbols: &RubiSymbols) -> Atom {
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    (c__ + d__ * (e__ + f__ * x_).pow(n_)).sin()
}

#[inline(never)]
fn rubi_shared_pattern_5(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (c__ + d__ * x_).cos() * (a__ + b__ * x_.pow(n_)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_6(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (c__ + d__ * x_).cos() * (e__ * x_).pow(m_) * (a__ + b__ * x_.pow(n_)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_7(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (c__ + d__ * x_).cos() * x_.pow(m_) * (a__ + b__ * x_.pow(n_)).pow(p_)
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
    let x_ = symbols.x_;
    (e__ * x_).pow(m_) * (a__ + b__ * (c__ + d__ * x_.pow(n_)).cos()).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_9(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (e__ * x_).pow(m_) * (a__ + b__ * (c__ + d__ * x_.pow(n_)).sin()).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_10(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (e__ * x_).pow(m_) * (a__ + b__ * x_.pow(n_)).pow(p_) * (c__ + d__ * x_).sin()
}

#[inline(never)]
fn rubi_shared_pattern_11(symbols: &RubiSymbols) -> Atom {
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    (e__ * x_).pow(m_) * (c__ + d__ * x_.pow(n_)).cos()
}

#[inline(never)]
fn rubi_shared_pattern_12(symbols: &RubiSymbols) -> Atom {
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    (e__ * x_).pow(m_) * (c__ + d__ * x_.pow(n_)).sin()
}

#[inline(never)]
fn rubi_shared_pattern_13(symbols: &RubiSymbols) -> Atom {
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
    let x_ = symbols.x_;
    (g__ + h__ * x_).pow(m_) * (a__ + b__ * (c__ + d__ * (e__ + f__ * x_).pow(n_)).cos()).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_14(symbols: &RubiSymbols) -> Atom {
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
    let x_ = symbols.x_;
    (g__ + h__ * x_).pow(m_) * (a__ + b__ * (c__ + d__ * (e__ + f__ * x_).pow(n_)).sin()).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_15(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    x_.pow(m_) * (a__ + b__ * (c__ + d__ * x_.pow(n_)).cos()).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_16(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    x_.pow(m_) * (a__ + b__ * (c__ + d__ * x_.pow(n_)).sin()).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_17(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    x_.pow(m_) * (a__ + b__ * x_.pow(n_)).cos().pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_18(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    x_.pow(m_) * (a__ + b__ * x_.pow(n_)).cos().pow(p_) * (a__ + b__ * x_.pow(n_)).sin()
}

#[inline(never)]
fn rubi_shared_pattern_19(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    x_.pow(m_) * (a__ + b__ * x_.pow(n_)).pow(p_) * (c__ + d__ * x_).sin()
}

#[inline(never)]
fn rubi_shared_pattern_20(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    x_.pow(m_) * (a__ + b__ * x_.pow(n_)).sin().pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_21(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    x_.pow(m_) * (a__ + b__ * x_.pow(n_)).sin().pow(p_) * (a__ + b__ * x_.pow(n_)).cos()
}
