use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_4727(rules);
    push_rules_rule_4728(rules);
    push_rules_rule_4729(rules);
    push_rules_rule_4730(rules);
    push_rules_rule_4731(rules);
    push_rules_rule_4732(rules);
    push_rules_rule_4733(rules);
    push_rules_rule_4734(rules);
    push_rules_rule_4735(rules);
    push_rules_rule_4736(rules);
    push_rules_rule_4737(rules);
    push_rules_rule_4738(rules);
    push_rules_rule_4739(rules);
    push_rules_rule_4740(rules);
    push_rules_rule_4741(rules);
    push_rules_rule_4742(rules);
    push_rules_rule_4743(rules);
    push_rules_rule_4744(rules);
    push_rules_rule_4745(rules);
}

fn push_rules_rule_4727(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, n_, u__, x_);
    rules.push(rubi_rule!(
        order: 4727,
        source: "Int[u_*(c_.*cot[a_.+b_.*x_])^m_.*(d_.*tan[a_.+b_.*x_])^n_.,x_Symbol] :=
          (c*Cot[a+b*x])^m*(d*Tan[a+b*x])^m \\[Star] Int[ActivateTrig[u]*(d*Tan[a+b*x])^(n-m),x] /;
        FreeQ[{a,b,c,d,m,n},x] && KnownTangentIntegrandQ[u,x]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: u__ * (c__ * i_cot(a__ + b__ * x_)).pow(m_) * (d__ * i_tan(a__ + b__ * x_)).pow(n_),
        with: [u__, c__, a__, b__, m_, d__, n_, x_],
        optional: [c__, a__, b__, m_, d__, n_],
        when: {
            freeq!([a__, b__, c__, d__, m_, n_], x_)
                && rubi_known_tangent_integrand_q(&u__, x_)
        },
        rhs: {
            let angle = &a__ + &b__ * x_;
            let transformed = rubi_activate_trig(&u__) * (&d__ * angle.tan()).pow(&n_ - &m_);
            let recursive = rubi_rhs_int(&transformed, x_);
            let multiplier = rubi_mathematica_unscaled_reciprocal_power_product2(
                &c__,
                angle.cot(),
                &d__,
                angle.tan(),
                &m_,
            );

            rubi_star(multiplier, recursive)
        },
    ));
}

fn push_rules_rule_4728(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, n_, u__, x_);
    rules.push(rubi_rule!(
        order: 4728,
        source: "Int[u_*(c_.*tan[a_.+b_.*x_])^m_.*(d_.*cos[a_.+b_.*x_])^n_.,x_Symbol] :=
          (c*Tan[a+b*x])^m*(d*Cos[a+b*x])^m/(d*Sin[a+b*x])^m \\[Star] Int[ActivateTrig[u]*(d*Sin[a+b*x])^m/(d*Cos[a+b*x])^(m-n),x] /;
        FreeQ[{a,b,c,d,m,n},x] && KnownCotangentIntegrandQ[u,x]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: u__ * (c__ * i_tan(a__ + b__ * x_)).pow(m_) * (d__ * i_cos(a__ + b__ * x_)).pow(n_),
        with: [u__, c__, a__, b__, m_, d__, n_, x_],
        optional: [c__, a__, b__, m_, d__, n_],
        when: {
            freeq!([a__, b__, c__, d__, m_, n_], x_)
                && rubi_known_cotangent_integrand_q(&u__, x_)
        },
        rhs: {
            let angle = &a__ + &b__ * x_;
            let transformed =
                rubi_activate_trig(&u__) * (&d__ * angle.sin()).pow(&m_) / (&d__ * angle.cos()).pow(&m_ - &n_);
            let recursive = rubi_rhs_int(&transformed, x_);

            let coefficient = (&c__ * angle.tan()).pow(&m_)
                * (&d__ * angle.cos()).pow(&m_)
                / (&d__ * angle.sin()).pow(&m_);
            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_4729(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, m_, u__, x_);
    rules.push(rubi_rule!(
        order: 4729,
        source: "Int[u_*(c_.*cot[a_.+b_.*x_])^m_.,x_Symbol] :=
          (c*Cot[a+b*x])^m*(c*Tan[a+b*x])^m \\[Star] Int[ActivateTrig[u]/(c*Tan[a+b*x])^m,x] /;
        FreeQ[{a,b,c,m},x] && Not[IntegerQ[m]] && KnownTangentIntegrandQ[u,x]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: u__ * (c__ * i_cot(a__ + b__ * x_)).pow(m_),
        with: [u__, c__, a__, b__, m_, x_],
        optional: [c__, a__, b__, m_],
        when: {
            freeq!([a__, b__, c__, m_], x_)
                && !integerq!(m_)
                && rubi_known_tangent_integrand_q(&u__, x_)
        },
        rhs: {
            let angle = &a__ + &b__ * x_;
            let transformed = rubi_activate_trig(&u__) / (&c__ * angle.tan()).pow(&m_);
            let recursive = rubi_rhs_int(&transformed, x_);
            let multiplier = rubi_mathematica_unscaled_reciprocal_power_product(
                &c__,
                angle.cot(),
                angle.tan(),
                &m_,
            );

            rubi_star(multiplier, recursive)
        },
    ));
}

fn push_rules_rule_4730(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, m_, u__, x_);
    rules.push(rubi_rule!(
        order: 4730,
        source: "Int[u_*(c_.*tan[a_.+b_.*x_])^m_.,x_Symbol] :=
          (c*Cot[a+b*x])^m*(c*Tan[a+b*x])^m \\[Star] Int[ActivateTrig[u]/(c*Cot[a+b*x])^m,x] /;
        FreeQ[{a,b,c,m},x] && Not[IntegerQ[m]] && KnownCotangentIntegrandQ[u,x]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: u__ * (c__ * i_tan(a__ + b__ * x_)).pow(m_),
        with: [u__, c__, a__, b__, m_, x_],
        optional: [c__, a__, b__, m_],
        when: {
            freeq!([a__, b__, c__, m_], x_)
                && !integerq!(m_)
                && rubi_known_cotangent_integrand_q(&u__, x_)
        },
        rhs: {
            let angle = &a__ + &b__ * x_;
            let transformed = rubi_activate_trig(&u__) / (&c__ * angle.cot()).pow(&m_);
            let recursive = rubi_rhs_int(&transformed, x_);
            let multiplier = rubi_mathematica_unscaled_reciprocal_power_product(
                &c__,
                angle.cot(),
                angle.tan(),
                &m_,
            );

            rubi_star(multiplier, recursive)
        },
    ));
}

fn push_rules_rule_4731(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_a__, capital_b__, a__, b__, c__, n_, u__, x_);
    rules.push(rubi_rule!(
        order: 4731,
        source: "Int[u_*(c_.*tan[a_.+b_.*x_])^n_.*(A_+B_.*cot[a_.+b_.*x_]),x_Symbol] :=
          c \\[Star] Int[ActivateTrig[u]*(c*Tan[a+b*x])^(n-1)*(B+A*Tan[a+b*x]),x] /;
        FreeQ[{a,b,c,A,B,n},x] && KnownTangentIntegrandQ[u,x]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: u__ * (c__ * i_tan(a__ + b__ * x_)).pow(n_) * (capital_a__ + capital_b__ * i_cot(a__ + b__ * x_)),
        with: [u__, c__, a__, b__, n_, capital_a__, capital_b__, x_],
        optional: [c__, a__, b__, n_, capital_b__],
        when: {
            freeq!([a__, b__, c__, capital_a__, capital_b__, n_], x_)
                && rubi_known_tangent_integrand_q(&u__, x_)
        },
        rhs: {
            let angle = &a__ + &b__ * x_;
            let transformed =
                rubi_activate_trig(&u__) * (&c__ * angle.tan()).pow(&n_ - 1) * (&capital_b__ + &capital_a__ * angle.tan());
            let recursive = rubi_rhs_int(&transformed, x_);

            rubi_star(c__, recursive)
        },
    ));
}

fn push_rules_rule_4732(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_a__, capital_b__, a__, b__, c__, n_, u__, x_);
    rules.push(rubi_rule!(
        order: 4732,
        source: "Int[u_*(c_.*cot[a_.+b_.*x_])^n_.*(A_+B_.*tan[a_.+b_.*x_]),x_Symbol] :=
          c \\[Star] Int[ActivateTrig[u]*(c*Cot[a+b*x])^(n-1)*(B+A*Cot[a+b*x]),x] /;
        FreeQ[{a,b,c,A,B,n},x] && KnownCotangentIntegrandQ[u,x]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: u__ * (c__ * i_cot(a__ + b__ * x_)).pow(n_) * (capital_a__ + capital_b__ * i_tan(a__ + b__ * x_)),
        with: [u__, c__, a__, b__, n_, capital_a__, capital_b__, x_],
        optional: [c__, a__, b__, n_, capital_b__],
        when: {
            freeq!([a__, b__, c__, capital_a__, capital_b__, n_], x_)
                && rubi_known_cotangent_integrand_q(&u__, x_)
        },
        rhs: {
            let angle = &a__ + &b__ * x_;
            let transformed =
                rubi_activate_trig(&u__) * (&c__ * angle.cot()).pow(&n_ - 1) * (&capital_b__ + &capital_a__ * angle.cot());
            let recursive = rubi_rhs_int(&transformed, x_);

            rubi_star(c__, recursive)
        },
    ));
}

fn push_rules_rule_4733(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_a__, capital_b__, a__, b__, u__, x_);
    rules.push(rubi_rule!(
        order: 4733,
        source: "Int[u_*(A_+B_.*cot[a_.+b_.*x_]),x_Symbol] :=
          Int[ActivateTrig[u]*(B+A*Tan[a+b*x])/Tan[a+b*x],x] /;
        FreeQ[{a,b,A,B},x] && KnownTangentIntegrandQ[u,x]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: u__ * (capital_a__ + capital_b__ * i_cot(a__ + b__ * x_)),
        with: [u__, capital_a__, capital_b__, a__, b__, x_],
        optional: [capital_b__, a__, b__],
        when: {
            freeq!([a__, b__, capital_a__, capital_b__], x_)
                && rubi_known_tangent_integrand_q(&u__, x_)
        },
        rhs: {
            let angle = &a__ + &b__ * x_;
            let transformed = rubi_activate_trig(&u__) * (&capital_b__ + &capital_a__ * angle.tan()) / angle.tan();

            rubi_rhs_int(&transformed, x_)
        },
    ));
}

fn push_rules_rule_4734(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_a__, capital_b__, a__, b__, u__, x_);
    rules.push(rubi_rule!(
        order: 4734,
        source: "Int[u_*(A_+B_.*tan[a_.+b_.*x_]),x_Symbol] :=
          Int[ActivateTrig[u]*(B+A*Cot[a+b*x])/Cot[a+b*x],x] /;
        FreeQ[{a,b,A,B},x] && KnownCotangentIntegrandQ[u,x]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: u__ * (capital_a__ + capital_b__ * i_tan(a__ + b__ * x_)),
        with: [u__, capital_a__, capital_b__, a__, b__, x_],
        optional: [capital_b__, a__, b__],
        when: {
            freeq!([a__, b__, capital_a__, capital_b__], x_)
                && rubi_known_cotangent_integrand_q(&u__, x_)
        },
        rhs: {
            let angle = &a__ + &b__ * x_;
            let transformed = rubi_activate_trig(&u__) * (&capital_b__ + &capital_a__ * angle.cot()) / angle.cot();

            rubi_rhs_int(&transformed, x_)
        },
    ));
}

fn push_rules_rule_4735(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        capital_a__,
        capital_b__,
        capital_c__,
        a__,
        b__,
        c__,
        n_,
        u__,
        x_
    );
    rules.push(rubi_rule!(
        order: 4735,
        source: "Int[u_.*(c_.*tan[a_.+b_.*x_])^n_.*(A_.+B_.*cot[a_.+b_.*x_]+C_.*cot[a_.+b_.*x_]^2),x_Symbol] :=
          c^2 \\[Star] Int[ActivateTrig[u]*(c*Tan[a+b*x])^(n-2)*(C+B*Tan[a+b*x]+A*Tan[a+b*x]^2),x] /;
        FreeQ[{a,b,c,A,B,C,n},x] && KnownTangentIntegrandQ[u,x]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: u__ * (c__ * i_tan(a__ + b__ * x_)).pow(n_)
            * (capital_a__ + capital_b__ * i_cot(a__ + b__ * x_) + capital_c__ * i_cot(a__ + b__ * x_).pow(2)),
        with: [u__, c__, a__, b__, n_, capital_a__, capital_b__, capital_c__, x_],
        optional: [u__, c__, a__, b__, n_, capital_a__, capital_b__, capital_c__],
        when: {
            freeq!([a__, b__, c__, capital_a__, capital_b__, capital_c__, n_], x_)
                && rubi_known_tangent_integrand_q(&u__, x_)
        },
        rhs: {
            let angle = &a__ + &b__ * x_;
            let transformed = rubi_activate_trig(&u__)
                * (&c__ * angle.tan()).pow(&n_ - 2)
                * (&capital_c__ + &capital_b__ * angle.tan() + &capital_a__ * angle.tan().pow(2));
            let recursive = rubi_rhs_int(&transformed, x_);

            rubi_star(c__.pow(2), recursive)
        },
    ));
}

fn push_rules_rule_4736(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        capital_a__,
        capital_b__,
        capital_c__,
        a__,
        b__,
        c__,
        n_,
        u__,
        x_
    );
    rules.push(rubi_rule!(
        order: 4736,
        source: "Int[u_.*(c_.*cot[a_.+b_.*x_])^n_.*(A_.+B_.*tan[a_.+b_.*x_]+C_.*tan[a_.+b_.*x_]^2),x_Symbol] :=
          c^2 \\[Star] Int[ActivateTrig[u]*(c*Cot[a+b*x])^(n-2)*(C+B*Cot[a+b*x]+A*Cot[a+b*x]^2),x] /;
        FreeQ[{a,b,c,A,B,C,n},x] && KnownCotangentIntegrandQ[u,x]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: u__ * (c__ * i_cot(a__ + b__ * x_)).pow(n_)
            * (capital_a__ + capital_b__ * i_tan(a__ + b__ * x_) + capital_c__ * i_tan(a__ + b__ * x_).pow(2)),
        with: [u__, c__, a__, b__, n_, capital_a__, capital_b__, capital_c__, x_],
        optional: [u__, c__, a__, b__, n_, capital_a__, capital_b__, capital_c__],
        when: {
            freeq!([a__, b__, c__, capital_a__, capital_b__, capital_c__, n_], x_)
                && rubi_known_cotangent_integrand_q(&u__, x_)
        },
        rhs: {
            let angle = &a__ + &b__ * x_;
            let transformed = rubi_activate_trig(&u__)
                * (&c__ * angle.cot()).pow(&n_ - 2)
                * (&capital_c__ + &capital_b__ * angle.cot() + &capital_a__ * angle.cot().pow(2));
            let recursive = rubi_rhs_int(&transformed, x_);

            rubi_star(c__.pow(2), recursive)
        },
    ));
}

fn push_rules_rule_4737(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_a__, capital_c__, a__, b__, c__, n_, u__, x_);
    rules.push(rubi_rule!(
        order: 4737,
        source: "Int[u_.*(c_.*tan[a_.+b_.*x_])^n_.*(A_+C_.*cot[a_.+b_.*x_]^2),x_Symbol] :=
          c^2 \\[Star] Int[ActivateTrig[u]*(c*Tan[a+b*x])^(n-2)*(C+A*Tan[a+b*x]^2),x] /;
        FreeQ[{a,b,c,A,C,n},x] && KnownTangentIntegrandQ[u,x]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: u__ * (c__ * i_tan(a__ + b__ * x_)).pow(n_)
            * (capital_a__ + capital_c__ * i_cot(a__ + b__ * x_).pow(2)),
        with: [u__, c__, a__, b__, n_, capital_a__, capital_c__, x_],
        optional: [u__, c__, a__, b__, n_, capital_c__],
        when: {
            freeq!([a__, b__, c__, capital_a__, capital_c__, n_], x_)
                && rubi_known_tangent_integrand_q(&u__, x_)
        },
        rhs: {
            let angle = &a__ + &b__ * x_;
            let transformed =
                rubi_activate_trig(&u__) * (&c__ * angle.tan()).pow(&n_ - 2) * (&capital_c__ + &capital_a__ * angle.tan().pow(2));
            let recursive = rubi_rhs_int(&transformed, x_);

            rubi_star(c__.pow(2), recursive)
        },
    ));
}

fn push_rules_rule_4738(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_a__, capital_c__, a__, b__, c__, n_, u__, x_);
    rules.push(rubi_rule!(
        order: 4738,
        source: "Int[u_.*(c_.*cot[a_.+b_.*x_])^n_.*(A_+C_.*tan[a_.+b_.*x_]^2),x_Symbol] :=
          c^2 \\[Star] Int[ActivateTrig[u]*(c*Cot[a+b*x])^(n-2)*(C+A*Cot[a+b*x]^2),x] /;
        FreeQ[{a,b,c,A,C,n},x] && KnownCotangentIntegrandQ[u,x]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: u__ * (c__ * i_cot(a__ + b__ * x_)).pow(n_)
            * (capital_a__ + capital_c__ * i_tan(a__ + b__ * x_).pow(2)),
        with: [u__, c__, a__, b__, n_, capital_a__, capital_c__, x_],
        optional: [u__, c__, a__, b__, n_, capital_c__],
        when: {
            freeq!([a__, b__, c__, capital_a__, capital_c__, n_], x_)
                && rubi_known_cotangent_integrand_q(&u__, x_)
        },
        rhs: {
            let angle = &a__ + &b__ * x_;
            let transformed =
                rubi_activate_trig(&u__) * (&c__ * angle.cot()).pow(&n_ - 2) * (&capital_c__ + &capital_a__ * angle.cot().pow(2));
            let recursive = rubi_rhs_int(&transformed, x_);

            rubi_star(c__.pow(2), recursive)
        },
    ));
}

fn push_rules_rule_4739(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_a__, capital_b__, capital_c__, a__, b__, u__, x_);
    rules.push(rubi_rule!(
        order: 4739,
        source: "Int[u_*(A_.+B_.*cot[a_.+b_.*x_]+C_.*cot[a_.+b_.*x_]^2),x_Symbol] :=
          Int[ActivateTrig[u]*(C+B*Tan[a+b*x]+A*Tan[a+b*x]^2)/Tan[a+b*x]^2,x] /;
        FreeQ[{a,b,A,B,C},x] && KnownTangentIntegrandQ[u,x]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: u__ * (capital_a__ + capital_b__ * i_cot(a__ + b__ * x_) + capital_c__ * i_cot(a__ + b__ * x_).pow(2)),
        with: [u__, capital_a__, capital_b__, capital_c__, a__, b__, x_],
        optional: [capital_a__, capital_b__, capital_c__, a__, b__],
        when: {
            freeq!([a__, b__, capital_a__, capital_b__, capital_c__], x_)
                && rubi_known_tangent_integrand_q(&u__, x_)
        },
        rhs: {
            let angle = &a__ + &b__ * x_;
            let transformed = rubi_activate_trig(&u__)
                * (&capital_c__ + &capital_b__ * angle.tan() + &capital_a__ * angle.tan().pow(2))
                / angle.tan().pow(2);

            rubi_rhs_int(&transformed, x_)
        },
    ));
}

fn push_rules_rule_4740(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_a__, capital_b__, capital_c__, a__, b__, u__, x_);
    rules.push(rubi_rule!(
        order: 4740,
        source: "Int[u_*(A_.+B_.*tan[a_.+b_.*x_]+C_.*tan[a_.+b_.*x_]^2),x_Symbol] :=
          Int[ActivateTrig[u]*(C+B*Cot[a+b*x]+A*Cot[a+b*x]^2)/Cot[a+b*x]^2,x] /;
        FreeQ[{a,b,A,B,C},x] && KnownCotangentIntegrandQ[u,x]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: u__ * (capital_a__ + capital_b__ * i_tan(a__ + b__ * x_) + capital_c__ * i_tan(a__ + b__ * x_).pow(2)),
        with: [u__, capital_a__, capital_b__, capital_c__, a__, b__, x_],
        optional: [capital_a__, capital_b__, capital_c__, a__, b__],
        when: {
            freeq!([a__, b__, capital_a__, capital_b__, capital_c__], x_)
                && rubi_known_cotangent_integrand_q(&u__, x_)
        },
        rhs: {
            let angle = &a__ + &b__ * x_;
            let transformed = rubi_activate_trig(&u__)
                * (&capital_c__ + &capital_b__ * angle.cot() + &capital_a__ * angle.cot().pow(2))
                / angle.cot().pow(2);

            rubi_rhs_int(&transformed, x_)
        },
    ));
}

fn push_rules_rule_4741(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_a__, capital_c__, a__, b__, u__, x_);
    rules.push(rubi_rule!(
        order: 4741,
        source: "Int[u_*(A_+C_.*cot[a_.+b_.*x_]^2),x_Symbol] :=
          Int[ActivateTrig[u]*(C+A*Tan[a+b*x]^2)/Tan[a+b*x]^2,x] /;
        FreeQ[{a,b,A,C},x] && KnownTangentIntegrandQ[u,x]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: u__ * (capital_a__ + capital_c__ * i_cot(a__ + b__ * x_).pow(2)),
        with: [u__, capital_a__, capital_c__, a__, b__, x_],
        optional: [capital_c__, a__, b__],
        when: {
            freeq!([a__, b__, capital_a__, capital_c__], x_)
                && rubi_known_tangent_integrand_q(&u__, x_)
        },
        rhs: {
            let angle = &a__ + &b__ * x_;
            let transformed =
                rubi_activate_trig(&u__) * (&capital_c__ + &capital_a__ * angle.tan().pow(2)) / angle.tan().pow(2);

            rubi_rhs_int(&transformed, x_)
        },
    ));
}

fn push_rules_rule_4742(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_a__, capital_c__, a__, b__, u__, x_);
    rules.push(rubi_rule!(
        order: 4742,
        source: "Int[u_*(A_+C_.*tan[a_.+b_.*x_]^2),x_Symbol] :=
          Int[ActivateTrig[u]*(C+A*Cot[a+b*x]^2)/Cot[a+b*x]^2,x] /;
        FreeQ[{a,b,A,C},x] && KnownCotangentIntegrandQ[u,x]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: u__ * (capital_a__ + capital_c__ * i_tan(a__ + b__ * x_).pow(2)),
        with: [u__, capital_a__, capital_c__, a__, b__, x_],
        optional: [capital_c__, a__, b__],
        when: {
            freeq!([a__, b__, capital_a__, capital_c__], x_)
                && rubi_known_cotangent_integrand_q(&u__, x_)
        },
        rhs: {
            let angle = &a__ + &b__ * x_;
            let transformed =
                rubi_activate_trig(&u__) * (&capital_c__ + &capital_a__ * angle.cot().pow(2)) / angle.cot().pow(2);

            rubi_rhs_int(&transformed, x_)
        },
    ));
}

fn push_rules_rule_4743(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_a__, capital_b__, capital_c__, a__, b__, u__, x_);
    rules.push(rubi_rule!(
        order: 4743,
        source: "Int[u_*(A_.+B_.*tan[a_.+b_.*x_]+C_.*cot[a_.+b_.*x_]),x_Symbol] :=
          Int[ActivateTrig[u]*(C+A*Tan[a+b*x]+B*Tan[a+b*x]^2)/Tan[a+b*x],x] /;
        FreeQ[{a,b,A,B,C},x]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: u__ * (capital_a__ + capital_b__ * i_tan(a__ + b__ * x_) + capital_c__ * i_cot(a__ + b__ * x_)),
        with: [u__, capital_a__, capital_b__, capital_c__, a__, b__, x_],
        optional: [capital_a__, capital_b__, capital_c__, a__, b__],
        when: {
            freeq!([a__, b__, capital_a__, capital_b__, capital_c__], x_)
        },
        rhs: {
            let angle = &a__ + &b__ * x_;
            let transformed = rubi_activate_trig(&u__)
                * (&capital_c__ + &capital_a__ * angle.tan() + &capital_b__ * angle.tan().pow(2))
                / angle.tan();

            rubi_rhs_int(&transformed, x_)
        },
    ));
}

fn push_rules_rule_4744(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        capital_a__,
        capital_b__,
        capital_c__,
        a__,
        b__,
        n_,
        n1_,
        n2_,
        u__,
        x_
    );
    rules.push(rubi_rule!(
        order: 4744,
        source: "Int[u_*(A_.*tan[a_.+b_.*x_]^n_.+B_.*tan[a_.+b_.*x_]^n1_+C_.*tan[a_.+b_.*x_]^n2_),x_Symbol] :=
          Int[ActivateTrig[u]*Tan[a+b*x]^n*(A+B*Tan[a+b*x]+C*Tan[a+b*x]^2),x] /;
        FreeQ[{a,b,A,B,C,n},x] && EqQ[n1,n+1] && EqQ[n2,n+2]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: u__ * (capital_a__ * i_tan(a__ + b__ * x_).pow(n_)
            + capital_b__ * i_tan(a__ + b__ * x_).pow(n1_)
            + capital_c__ * i_tan(a__ + b__ * x_).pow(n2_)),
        with: [u__, capital_a__, a__, b__, n_, capital_b__, n1_, capital_c__, n2_, x_],
        optional: [capital_a__, capital_b__, capital_c__, a__, b__, n_],
        when: {
            freeq!([a__, b__, capital_a__, capital_b__, capital_c__, n_], x_)
                && eqq!(n1_, &n_ + 1)
                && eqq!(n2_, &n_ + 2)
        },
        rhs: {
            let angle = &a__ + &b__ * x_;
            let transformed = rubi_activate_trig(&u__)
                * angle.tan().pow(&n_)
                * (&capital_a__ + &capital_b__ * angle.tan() + &capital_c__ * angle.tan().pow(2));

            rubi_rhs_int(&transformed, x_)
        },
    ));
}

fn push_rules_rule_4745(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        capital_a__,
        capital_b__,
        capital_c__,
        a__,
        b__,
        n_,
        n1_,
        n2_,
        u__,
        x_
    );
    rules.push(rubi_rule!(
        order: 4745,
        source: "Int[u_*(A_.*cot[a_.+b_.*x_]^n_.+B_.*cot[a_.+b_.*x_]^n1_+C_.*cot[a_.+b_.*x_]^n2_),x_Symbol] :=
          Int[ActivateTrig[u]*Cot[a+b*x]^n*(A+B*Cot[a+b*x]+C*Cot[a+b*x]^2),x] /;
        FreeQ[{a,b,A,B,C,n},x] && EqQ[n1,n+1] && EqQ[n2,n+2]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: u__ * (capital_a__ * i_cot(a__ + b__ * x_).pow(n_)
            + capital_b__ * i_cot(a__ + b__ * x_).pow(n1_)
            + capital_c__ * i_cot(a__ + b__ * x_).pow(n2_)),
        with: [u__, capital_a__, a__, b__, n_, capital_b__, n1_, capital_c__, n2_, x_],
        optional: [capital_a__, capital_b__, capital_c__, a__, b__, n_],
        when: {
            freeq!([a__, b__, capital_a__, capital_b__, capital_c__, n_], x_)
                && eqq!(n1_, &n_ + 1)
                && eqq!(n2_, &n_ + 2)
        },
        rhs: {
            let angle = &a__ + &b__ * x_;
            let transformed = rubi_activate_trig(&u__)
                * angle.cot().pow(&n_)
                * (&capital_a__ + &capital_b__ * angle.cot() + &capital_c__ * angle.cot().pow(2));

            rubi_rhs_int(&transformed, x_)
        },
    ));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn downvalues_4727_through_4742_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .filter(|order| (4727..=4742).contains(order))
            .collect::<Vec<_>>();
        assert_eq!(orders, (4727..=4742).collect::<Vec<_>>());
    }

    #[test]
    fn downvalues_4743_through_4745_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .filter(|order| (4743..=4745).contains(order))
            .collect::<Vec<_>>();
        assert_eq!(orders, (4743..=4745).collect::<Vec<_>>());
    }
}
