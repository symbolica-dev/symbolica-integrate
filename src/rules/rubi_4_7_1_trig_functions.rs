use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_4702(rules);
    push_rules_rule_4703(rules);
    push_rules_rule_4704(rules);
    push_rules_rule_4705(rules);
    push_rules_rule_4706(rules);
    push_rules_rule_4707(rules);
    push_rules_rule_4708(rules);
    push_rules_rule_4709(rules);
    push_rules_rule_4710(rules);
    push_rules_rule_4711(rules);
    push_rules_rule_4712(rules);
    push_rules_rule_4713(rules);
    push_rules_rule_4714(rules);
    push_rules_rule_4715(rules);
    push_rules_rule_4716(rules);
    push_rules_rule_4717(rules);
    push_rules_rule_4718(rules);
    push_rules_rule_4719(rules);
    push_rules_rule_4720(rules);
    push_rules_rule_4721(rules);
    push_rules_rule_4722(rules);
    push_rules_rule_4723(rules);
    push_rules_rule_4724(rules);
    push_rules_rule_4725(rules);
    push_rules_rule_4726(rules);
}

fn push_rules_rule_4702(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, n_, u__, x_);
    rules.push(rubi_rule!(
        order: 4702,
        source: "Int[u_*(c_.*tan[a_.+b_.*x_])^m_.*(d_.*sin[a_.+b_.*x_])^n_.,x_Symbol] :=
          (c*Tan[a+b*x])^m*(d*Cos[a+b*x])^m/(d*Sin[a+b*x])^m \\[Star] Int[ActivateTrig[u]*(d*Sin[a+b*x])^(m+n)/(d*Cos[a+b*x])^m,x] /;
        FreeQ[{a,b,c,d,m,n},x] && KnownSineIntegrandQ[u,x] && Not[IntegerQ[m]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: u__ * (c__ * i_tan(a__ + b__ * x_)).pow(m_) * (d__ * i_sin(a__ + b__ * x_)).pow(n_),
        with: [u__, c__, a__, b__, m_, d__, n_, x_],
        optional: [c__, a__, b__, d__, n_, m_],
        when: {
            freeq!([a__, b__, c__, d__, m_, n_], x_)
                && rubi_known_sine_integrand_q(&u__, x_)
                && !integerq!(m_)
        },
        rhs: {
            let angle = &a__ + &b__ * x_;
            let transformed = rubi_activate_trig(&u__) * (&d__ * angle.sin()).pow(&m_ + &n_) / (&d__ * angle.cos()).pow(&m_);
            let recursive = rubi_rhs_int(&transformed, x_);

            let coefficient = (&c__ * angle.tan()).pow(&m_)
                * (&d__ * angle.cos()).pow(&m_)
                / (&d__ * angle.sin()).pow(&m_);
            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_4703(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, n_, u__, x_);
    rules.push(rubi_rule!(
        order: 4703,
        source: "Int[u_*(c_.*tan[a_.+b_.*x_])^m_.*(d_.*cos[a_.+b_.*x_])^n_.,x_Symbol] :=
          (c*Tan[a+b*x])^m*(d*Cos[a+b*x])^m/(d*Sin[a+b*x])^m \\[Star] Int[ActivateTrig[u]*(d*Sin[a+b*x])^m/(d*Cos[a+b*x])^(m-n),x] /;
        FreeQ[{a,b,c,d,m,n},x] && KnownSineIntegrandQ[u,x] && Not[IntegerQ[m]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: u__ * (c__ * i_tan(a__ + b__ * x_)).pow(m_) * (d__ * i_cos(a__ + b__ * x_)).pow(n_),
        with: [u__, c__, a__, b__, m_, d__, n_, x_],
        optional: [c__, a__, b__, d__, n_, m_],
        when: {
            freeq!([a__, b__, c__, d__, m_, n_], x_)
                && rubi_known_sine_integrand_q(&u__, x_)
                && !integerq!(m_)
        },
        rhs: {
            let angle = &a__ + &b__ * x_;
            let transformed = rubi_activate_trig(&u__) * (&d__ * angle.sin()).pow(&m_) / (&d__ * angle.cos()).pow(&m_ - &n_);
            let recursive = rubi_rhs_int(&transformed, x_);

            let coefficient = (&c__ * angle.tan()).pow(&m_)
                * (&d__ * angle.cos()).pow(&m_)
                / (&d__ * angle.sin()).pow(&m_);
            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_4704(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, n_, u__, x_);
    rules.push(rubi_rule!(
        order: 4704,
        source: "Int[u_*(c_.*cot[a_.+b_.*x_])^m_.*(d_.*sin[a_.+b_.*x_])^n_.,x_Symbol] :=
          (c*Cot[a+b*x])^m*(d*Sin[a+b*x])^m/(d*Cos[a+b*x])^m \\[Star] Int[ActivateTrig[u]*(d*Cos[a+b*x])^m/(d*Sin[a+b*x])^(m-n),x] /;
        FreeQ[{a,b,c,d,m,n},x] && KnownSineIntegrandQ[u,x] && Not[IntegerQ[m]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: u__ * (c__ * i_cot(a__ + b__ * x_)).pow(m_) * (d__ * i_sin(a__ + b__ * x_)).pow(n_),
        with: [u__, c__, a__, b__, m_, d__, n_, x_],
        optional: [c__, a__, b__, d__, n_, m_],
        when: {
            freeq!([a__, b__, c__, d__, m_, n_], x_)
                && rubi_known_sine_integrand_q(&u__, x_)
                && !integerq!(m_)
        },
        rhs: {
            let angle = &a__ + &b__ * x_;
            let transformed = rubi_activate_trig(&u__) * (&d__ * angle.cos()).pow(&m_) / (&d__ * angle.sin()).pow(&m_ - &n_);
            let recursive = rubi_rhs_int(&transformed, x_);

            let coefficient = (&c__ * angle.cot()).pow(&m_)
                * (&d__ * angle.sin()).pow(&m_)
                / (&d__ * angle.cos()).pow(&m_);
            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_4705(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, n_, u__, x_);
    rules.push(rubi_rule!(
        order: 4705,
        source: "Int[u_*(c_.*cot[a_.+b_.*x_])^m_.*(d_.*cos[a_.+b_.*x_])^n_.,x_Symbol] :=
          (c*Cot[a+b*x])^m*(d*Sin[a+b*x])^m/(d*Cos[a+b*x])^m \\[Star] Int[ActivateTrig[u]*(d*Cos[a+b*x])^(m+n)/(d*Sin[a+b*x])^m,x] /;
        FreeQ[{a,b,c,d,m,n},x] && KnownSineIntegrandQ[u,x] && Not[IntegerQ[m]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: u__ * (c__ * i_cot(a__ + b__ * x_)).pow(m_) * (d__ * i_cos(a__ + b__ * x_)).pow(n_),
        with: [u__, c__, a__, b__, m_, d__, n_, x_],
        optional: [c__, a__, b__, d__, n_, m_],
        when: {
            freeq!([a__, b__, c__, d__, m_, n_], x_)
                && rubi_known_sine_integrand_q(&u__, x_)
                && !integerq!(m_)
        },
        rhs: {
            let angle = &a__ + &b__ * x_;
            let transformed = rubi_activate_trig(&u__) * (&d__ * angle.cos()).pow(&m_ + &n_) / (&d__ * angle.sin()).pow(&m_);
            let recursive = rubi_rhs_int(&transformed, x_);

            let coefficient = (&c__ * angle.cot()).pow(&m_)
                * (&d__ * angle.sin()).pow(&m_)
                / (&d__ * angle.cos()).pow(&m_);
            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_4706(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, n_, u__, x_);
    rules.push(rubi_rule!(
        order: 4706,
        source: "Int[u_*(c_.*sec[a_.+b_.*x_])^m_.*(d_.*cos[a_.+b_.*x_])^n_.,x_Symbol] :=
          (c*Csc[a+b*x])^m*(d*Sin[a+b*x])^m \\[Star] Int[ActivateTrig[u]*(d*Sin[a+b*x])^(n-m),x] /;
        FreeQ[{a,b,c,d,m,n},x] && KnownSineIntegrandQ[u,x]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: u__ * (c__ * i_sec(a__ + b__ * x_)).pow(m_) * (d__ * i_cos(a__ + b__ * x_)).pow(n_),
        with: [u__, c__, a__, b__, m_, d__, n_, x_],
        optional: [c__, a__, b__, d__, n_, m_],
        when: {
            freeq!([a__, b__, c__, d__, m_, n_], x_)
                && rubi_known_sine_integrand_q(&u__, x_)
        },
        rhs: {
            let angle = &a__ + &b__ * x_;
            let transformed = rubi_activate_trig(&u__) * (&d__ * angle.cos()).pow(&n_ - &m_);
            let recursive = rubi_rhs_int(&transformed, x_);

            let coefficient =
                (&c__ * angle.sec()).pow(&m_) * (&d__ * angle.cos()).pow(&m_);
            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_4707(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, m_, u__, x_);
    rules.push(rubi_rule!(
        order: 4707,
        source: "Int[u_*(c_.*tan[a_.+b_.*x_])^m_.,x_Symbol] :=
          (c*Tan[a+b*x])^m*(c*Cos[a+b*x])^m/(c*Sin[a+b*x])^m \\[Star] Int[ActivateTrig[u]*(c*Sin[a+b*x])^m/(c*Cos[a+b*x])^m,x] /;
        FreeQ[{a,b,c,m},x] && Not[IntegerQ[m]] && KnownSineIntegrandQ[u,x]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: u__ * (c__ * i_tan(a__ + b__ * x_)).pow(m_),
        with: [u__, c__, a__, b__, m_, x_],
        optional: [c__, a__, b__, m_],
        when: {
            freeq!([a__, b__, c__, m_], x_)
                && !integerq!(m_)
                && rubi_known_sine_integrand_q(&u__, x_)
        },
        rhs: {
            let angle = &a__ + &b__ * x_;
            let transformed = rubi_activate_trig(&u__) * (&c__ * angle.sin()).pow(&m_) / (&c__ * angle.cos()).pow(&m_);
            let recursive = rubi_rhs_int(&transformed, x_);

            let coefficient = (&c__ * angle.tan()).pow(&m_)
                * (&c__ * angle.cos()).pow(&m_)
                / (&c__ * angle.sin()).pow(&m_);
            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_4708(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, m_, u__, x_);
    rules.push(rubi_rule!(
        order: 4708,
        source: "Int[u_*(c_.*cot[a_.+b_.*x_])^m_.,x_Symbol] :=
          (c*Cot[a+b*x])^m*(c*Sin[a+b*x])^m/(c*Cos[a+b*x])^m \\[Star] Int[ActivateTrig[u]*(c*Cos[a+b*x])^m/(c*Sin[a+b*x])^m,x] /;
        FreeQ[{a,b,c,m},x] && Not[IntegerQ[m]] && KnownSineIntegrandQ[u,x]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: u__ * (c__ * i_cot(a__ + b__ * x_)).pow(m_),
        with: [u__, c__, a__, b__, m_, x_],
        optional: [c__, a__, b__, m_],
        when: {
            freeq!([a__, b__, c__, m_], x_)
                && !integerq!(m_)
                && rubi_known_sine_integrand_q(&u__, x_)
        },
        rhs: {
            let angle = &a__ + &b__ * x_;
            let transformed = rubi_activate_trig(&u__) * (&c__ * angle.cos()).pow(&m_) / (&c__ * angle.sin()).pow(&m_);
            let recursive = rubi_rhs_int(&transformed, x_);

            let coefficient = (&c__ * angle.cot()).pow(&m_)
                * (&c__ * angle.sin()).pow(&m_)
                / (&c__ * angle.cos()).pow(&m_);
            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_4709(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, m_, u__, x_);
    rules.push(rubi_rule!(
        order: 4709,
        source: "Int[u_*(c_.*sec[a_.+b_.*x_])^m_.,x_Symbol] :=
          (c*Sec[a+b*x])^m*(c*Cos[a+b*x])^m \\[Star] Int[ActivateTrig[u]/(c*Cos[a+b*x])^m,x] /;
        FreeQ[{a,b,c,m},x] && Not[IntegerQ[m]] && KnownSineIntegrandQ[u,x]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: u__ * (c__ * i_sec(a__ + b__ * x_)).pow(m_),
        with: [u__, c__, a__, b__, m_, x_],
        optional: [c__, a__, b__, m_],
        when: {
            freeq!([a__, b__, c__, m_], x_)
                && !integerq!(m_)
                && rubi_known_sine_integrand_q(&u__, x_)
        },
        rhs: {
            let angle = &a__ + &b__ * x_;
            let transformed = rubi_activate_trig(&u__) / (&c__ * angle.cos()).pow(&m_);
            let recursive = rubi_rhs_int(&transformed, x_);

            let coefficient =
                (&c__ * angle.sec()).pow(&m_) * (&c__ * angle.cos()).pow(&m_);
            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_4710(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, m_, u__, x_);
    rules.push(rubi_rule!(
        order: 4710,
        source: "Int[u_*(c_.*csc[a_.+b_.*x_])^m_.,x_Symbol] :=
          (c*Csc[a+b*x])^m*(c*Sin[a+b*x])^m \\[Star] Int[ActivateTrig[u]/(c*Sin[a+b*x])^m,x] /;
        FreeQ[{a,b,c,m},x] && Not[IntegerQ[m]] && KnownSineIntegrandQ[u,x]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: u__ * (c__ * i_csc(a__ + b__ * x_)).pow(m_),
        with: [u__, c__, a__, b__, m_, x_],
        optional: [c__, a__, b__, m_],
        when: {
            freeq!([a__, b__, c__, m_], x_)
                && !integerq!(m_)
                && rubi_known_sine_integrand_q(&u__, x_)
        },
        rhs: {
            let angle = &a__ + &b__ * x_;
            let transformed = rubi_activate_trig(&u__) / (&c__ * angle.sin()).pow(&m_);
            let recursive = rubi_rhs_int(&transformed, x_);

            let coefficient =
                (&c__ * angle.csc()).pow(&m_) * (&c__ * angle.sin()).pow(&m_);
            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_4711(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_a__, capital_b__, a__, b__, c__, n_, u__, x_);
    rules.push(rubi_rule!(
        order: 4711,
        source: "Int[u_*(c_.*sin[a_.+b_.*x_])^n_.*(A_+B_.*csc[a_.+b_.*x_]),x_Symbol] :=
          c \\[Star] Int[ActivateTrig[u]*(c*Sin[a+b*x])^(n-1)*(B+A*Sin[a+b*x]),x] /;
        FreeQ[{a,b,c,A,B,n},x] && KnownSineIntegrandQ[u,x]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: u__ * (c__ * i_sin(a__ + b__ * x_)).pow(n_) * (capital_a__ + capital_b__ * i_csc(a__ + b__ * x_)),
        with: [u__, c__, a__, b__, n_, capital_a__, capital_b__, x_],
        optional: [c__, a__, b__, n_, capital_b__],
        when: {
            freeq!([a__, b__, c__, capital_a__, capital_b__, n_], x_)
                && rubi_known_sine_integrand_q(&u__, x_)
        },
        rhs: {
            let angle = &a__ + &b__ * x_;
            let transformed =
                rubi_activate_trig(&u__) * (&c__ * angle.sin()).pow(&n_ - 1) * (&capital_b__ + &capital_a__ * angle.sin());
            let recursive = rubi_rhs_int(&transformed, x_);

            rubi_star(c__, recursive)
        },
    ));
}

fn push_rules_rule_4712(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_a__, capital_b__, a__, b__, c__, n_, u__, x_);
    rules.push(rubi_rule!(
        order: 4712,
        source: "Int[u_*(c_.*cos[a_.+b_.*x_])^n_.*(A_+B_.*sec[a_.+b_.*x_]),x_Symbol] :=
          c \\[Star] Int[ActivateTrig[u]*(c*Cos[a+b*x])^(n-1)*(B+A*Cos[a+b*x]),x] /;
        FreeQ[{a,b,c,A,B,n},x] && KnownSineIntegrandQ[u,x]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: u__ * (c__ * i_cos(a__ + b__ * x_)).pow(n_) * (capital_a__ + capital_b__ * i_sec(a__ + b__ * x_)),
        with: [u__, c__, a__, b__, n_, capital_a__, capital_b__, x_],
        optional: [c__, a__, b__, n_, capital_b__],
        when: {
            freeq!([a__, b__, c__, capital_a__, capital_b__, n_], x_)
                && rubi_known_sine_integrand_q(&u__, x_)
        },
        rhs: {
            let angle = &a__ + &b__ * x_;
            let transformed =
                rubi_activate_trig(&u__) * (&c__ * angle.cos()).pow(&n_ - 1) * (&capital_b__ + &capital_a__ * angle.cos());
            let recursive = rubi_rhs_int(&transformed, x_);

            rubi_star(c__, recursive)
        },
    ));
}

fn push_rules_rule_4713(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_a__, capital_b__, a__, b__, u__, x_);
    rules.push(rubi_rule!(
        order: 4713,
        source: "Int[u_*(A_+B_.*csc[a_.+b_.*x_]),x_Symbol] :=
          Int[ActivateTrig[u]*(B+A*Sin[a+b*x])/Sin[a+b*x],x] /;
        FreeQ[{a,b,A,B},x] && KnownSineIntegrandQ[u,x]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: u__ * (capital_a__ + capital_b__ * i_csc(a__ + b__ * x_)),
        with: [u__, capital_a__, capital_b__, a__, b__, x_],
        optional: [capital_b__, a__, b__],
        when: {
            freeq!([a__, b__, capital_a__, capital_b__], x_)
                && rubi_known_sine_integrand_q(&u__, x_)
        },
        rhs: {
            let angle = &a__ + &b__ * x_;
            let transformed = rubi_activate_trig(&u__) * (&capital_b__ + &capital_a__ * angle.sin()) / angle.sin();

            rubi_rhs_int(&transformed, x_)
        },
    ));
}

fn push_rules_rule_4714(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_a__, capital_b__, a__, b__, u__, x_);
    rules.push(rubi_rule!(
        order: 4714,
        source: "Int[u_*(A_+B_.*sec[a_.+b_.*x_]),x_Symbol] :=
          Int[ActivateTrig[u]*(B+A*Cos[a+b*x])/Cos[a+b*x],x] /;
        FreeQ[{a,b,A,B},x] && KnownSineIntegrandQ[u,x]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: u__ * (capital_a__ + capital_b__ * i_sec(a__ + b__ * x_)),
        with: [u__, capital_a__, capital_b__, a__, b__, x_],
        optional: [capital_b__, a__, b__],
        when: {
            freeq!([a__, b__, capital_a__, capital_b__], x_)
                && rubi_known_sine_integrand_q(&u__, x_)
        },
        rhs: {
            let angle = &a__ + &b__ * x_;
            let transformed = rubi_activate_trig(&u__) * (&capital_b__ + &capital_a__ * angle.cos()) / angle.cos();

            rubi_rhs_int(&transformed, x_)
        },
    ));
}

fn push_rules_rule_4715(rules: &mut Vec<RubiRule>) {
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
        order: 4715,
        source: "Int[u_.*(c_.*sin[a_.+b_.*x_])^n_.*(A_.+B_.*csc[a_.+b_.*x_]+C_.*csc[a_.+b_.*x_]^2),x_Symbol] :=
          c^2 \\[Star] Int[ActivateTrig[u]*(c*Sin[a+b*x])^(n-2)*(C+B*Sin[a+b*x]+A*Sin[a+b*x]^2),x] /;
        FreeQ[{a,b,c,A,B,C,n},x] && KnownSineIntegrandQ[u,x]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: u__ * (c__ * i_sin(a__ + b__ * x_)).pow(n_)
            * (capital_a__ + capital_b__ * i_csc(a__ + b__ * x_) + capital_c__ * i_csc(a__ + b__ * x_).pow(2)),
        with: [u__, c__, a__, b__, n_, capital_a__, capital_b__, capital_c__, x_],
        optional: [u__, c__, a__, b__, n_, capital_a__, capital_b__, capital_c__],
        when: {
            freeq!([a__, b__, c__, capital_a__, capital_b__, capital_c__, n_], x_)
                && rubi_known_sine_integrand_q(&u__, x_)
        },
        rhs: {
            let angle = &a__ + &b__ * x_;
            let transformed = rubi_activate_trig(&u__)
                * (&c__ * angle.sin()).pow(&n_ - 2)
                * (&capital_c__ + &capital_b__ * angle.sin() + &capital_a__ * angle.sin().pow(2));
            let recursive = rubi_rhs_int(&transformed, x_);

            rubi_star(c__.pow(2), recursive)
        },
    ));
}

fn push_rules_rule_4716(rules: &mut Vec<RubiRule>) {
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
        order: 4716,
        source: "Int[u_.*(c_.*cos[a_.+b_.*x_])^n_.*(A_.+B_.*sec[a_.+b_.*x_]+C_.*sec[a_.+b_.*x_]^2),x_Symbol] :=
          c^2 \\[Star] Int[ActivateTrig[u]*(c*Cos[a+b*x])^(n-2)*(C+B*Cos[a+b*x]+A*Cos[a+b*x]^2),x] /;
        FreeQ[{a,b,c,A,B,C,n},x] && KnownSineIntegrandQ[u,x]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: u__ * (c__ * i_cos(a__ + b__ * x_)).pow(n_)
            * (capital_a__ + capital_b__ * i_sec(a__ + b__ * x_) + capital_c__ * i_sec(a__ + b__ * x_).pow(2)),
        with: [u__, c__, a__, b__, n_, capital_a__, capital_b__, capital_c__, x_],
        optional: [u__, c__, a__, b__, n_, capital_a__, capital_b__, capital_c__],
        when: {
            freeq!([a__, b__, c__, capital_a__, capital_b__, capital_c__, n_], x_)
                && rubi_known_sine_integrand_q(&u__, x_)
        },
        rhs: {
            let angle = &a__ + &b__ * x_;
            let transformed = rubi_activate_trig(&u__)
                * (&c__ * angle.cos()).pow(&n_ - 2)
                * (&capital_c__ + &capital_b__ * angle.cos() + &capital_a__ * angle.cos().pow(2));
            let recursive = rubi_rhs_int(&transformed, x_);

            rubi_star(c__.pow(2), recursive)
        },
    ));
}

fn push_rules_rule_4717(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_a__, capital_c__, a__, b__, c__, n_, u__, x_);
    rules.push(rubi_rule!(
        order: 4717,
        source: "Int[u_.*(c_.*sin[a_.+b_.*x_])^n_.*(A_+C_.*csc[a_.+b_.*x_]^2),x_Symbol] :=
          c^2 \\[Star] Int[ActivateTrig[u]*(c*Sin[a+b*x])^(n-2)*(C+A*Sin[a+b*x]^2),x] /;
        FreeQ[{a,b,c,A,C,n},x] && KnownSineIntegrandQ[u,x]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: u__ * (c__ * i_sin(a__ + b__ * x_)).pow(n_)
            * (capital_a__ + capital_c__ * i_csc(a__ + b__ * x_).pow(2)),
        with: [u__, c__, a__, b__, n_, capital_a__, capital_c__, x_],
        optional: [u__, c__, a__, b__, n_, capital_c__],
        when: {
            freeq!([a__, b__, c__, capital_a__, capital_c__, n_], x_)
                && rubi_known_sine_integrand_q(&u__, x_)
        },
        rhs: {
            let angle = &a__ + &b__ * x_;
            let transformed = rubi_activate_trig(&u__)
                * (&c__ * angle.sin()).pow(&n_ - 2)
                * (&capital_c__ + &capital_a__ * angle.sin().pow(2));
            let recursive = rubi_rhs_int(&transformed, x_);

            rubi_star(c__.pow(2), recursive)
        },
    ));
}

fn push_rules_rule_4718(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_a__, capital_c__, a__, b__, c__, n_, u__, x_);
    rules.push(rubi_rule!(
        order: 4718,
        source: "Int[u_.*(c_.*cos[a_.+b_.*x_])^n_.*(A_+C_.*sec[a_.+b_.*x_]^2),x_Symbol] :=
          c^2 \\[Star] Int[ActivateTrig[u]*(c*Cos[a+b*x])^(n-2)*(C+A*Cos[a+b*x]^2),x] /;
        FreeQ[{a,b,c,A,C,n},x] && KnownSineIntegrandQ[u,x]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: u__ * (c__ * i_cos(a__ + b__ * x_)).pow(n_)
            * (capital_a__ + capital_c__ * i_sec(a__ + b__ * x_).pow(2)),
        with: [u__, c__, a__, b__, n_, capital_a__, capital_c__, x_],
        optional: [u__, c__, a__, b__, n_, capital_c__],
        when: {
            freeq!([a__, b__, c__, capital_a__, capital_c__, n_], x_)
                && rubi_known_sine_integrand_q(&u__, x_)
        },
        rhs: {
            let angle = &a__ + &b__ * x_;
            let transformed = rubi_activate_trig(&u__)
                * (&c__ * angle.cos()).pow(&n_ - 2)
                * (&capital_c__ + &capital_a__ * angle.cos().pow(2));
            let recursive = rubi_rhs_int(&transformed, x_);

            rubi_star(c__.pow(2), recursive)
        },
    ));
}

fn push_rules_rule_4719(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_a__, capital_b__, capital_c__, a__, b__, u__, x_);
    rules.push(rubi_rule!(
        order: 4719,
        source: "Int[u_*(A_.+B_.*csc[a_.+b_.*x_]+C_.*csc[a_.+b_.*x_]^2),x_Symbol] :=
          Int[ActivateTrig[u]*(C+B*Sin[a+b*x]+A*Sin[a+b*x]^2)/Sin[a+b*x]^2,x] /;
        FreeQ[{a,b,A,B,C},x] && KnownSineIntegrandQ[u,x]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: u__ * (capital_a__ + capital_b__ * i_csc(a__ + b__ * x_) + capital_c__ * i_csc(a__ + b__ * x_).pow(2)),
        with: [u__, capital_a__, capital_b__, capital_c__, a__, b__, x_],
        optional: [capital_a__, capital_b__, capital_c__, a__, b__],
        when: {
            freeq!([a__, b__, capital_a__, capital_b__, capital_c__], x_)
                && rubi_known_sine_integrand_q(&u__, x_)
        },
        rhs: {
            let angle = &a__ + &b__ * x_;
            let transformed = rubi_activate_trig(&u__)
                * (&capital_c__ + &capital_b__ * angle.sin() + &capital_a__ * angle.sin().pow(2))
                / angle.sin().pow(2);

            rubi_rhs_int(&transformed, x_)
        },
    ));
}

fn push_rules_rule_4720(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_a__, capital_b__, capital_c__, a__, b__, u__, x_);
    rules.push(rubi_rule!(
        order: 4720,
        source: "Int[u_*(A_.+B_.*sec[a_.+b_.*x_]+C_.*sec[a_.+b_.*x_]^2),x_Symbol] :=
          Int[ActivateTrig[u]*(C+B*Cos[a+b*x]+A*Cos[a+b*x]^2)/Cos[a+b*x]^2,x] /;
        FreeQ[{a,b,A,B,C},x] && KnownSineIntegrandQ[u,x]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: u__ * (capital_a__ + capital_b__ * i_sec(a__ + b__ * x_) + capital_c__ * i_sec(a__ + b__ * x_).pow(2)),
        with: [u__, capital_a__, capital_b__, capital_c__, a__, b__, x_],
        optional: [capital_a__, capital_b__, capital_c__, a__, b__],
        when: {
            freeq!([a__, b__, capital_a__, capital_b__, capital_c__], x_)
                && rubi_known_sine_integrand_q(&u__, x_)
        },
        rhs: {
            let angle = &a__ + &b__ * x_;
            let transformed = rubi_activate_trig(&u__)
                * (&capital_c__ + &capital_b__ * angle.cos() + &capital_a__ * angle.cos().pow(2))
                / angle.cos().pow(2);

            rubi_rhs_int(&transformed, x_)
        },
    ));
}

fn push_rules_rule_4721(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_a__, capital_c__, a__, b__, u__, x_);
    rules.push(rubi_rule!(
        order: 4721,
        source: "Int[u_*(A_+C_.*csc[a_.+b_.*x_]^2),x_Symbol] :=
          Int[ActivateTrig[u]*(C+A*Sin[a+b*x]^2)/Sin[a+b*x]^2,x] /;
        FreeQ[{a,b,A,C},x] && KnownSineIntegrandQ[u,x]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: u__ * (capital_a__ + capital_c__ * i_csc(a__ + b__ * x_).pow(2)),
        with: [u__, capital_a__, capital_c__, a__, b__, x_],
        optional: [capital_c__, a__, b__],
        when: {
            freeq!([a__, b__, capital_a__, capital_c__], x_)
                && rubi_known_sine_integrand_q(&u__, x_)
        },
        rhs: {
            let angle = &a__ + &b__ * x_;
            let transformed =
                rubi_activate_trig(&u__) * (&capital_c__ + &capital_a__ * angle.sin().pow(2)) / angle.sin().pow(2);

            rubi_rhs_int(&transformed, x_)
        },
    ));
}

fn push_rules_rule_4722(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_a__, capital_c__, a__, b__, u__, x_);
    rules.push(rubi_rule!(
        order: 4722,
        source: "Int[u_*(A_+C_.*sec[a_.+b_.*x_]^2),x_Symbol] :=
          Int[ActivateTrig[u]*(C+A*Cos[a+b*x]^2)/Cos[a+b*x]^2,x] /;
        FreeQ[{a,b,A,C},x] && KnownSineIntegrandQ[u,x]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: u__ * (capital_a__ + capital_c__ * i_sec(a__ + b__ * x_).pow(2)),
        with: [u__, capital_a__, capital_c__, a__, b__, x_],
        optional: [capital_c__, a__, b__],
        when: {
            freeq!([a__, b__, capital_a__, capital_c__], x_)
                && rubi_known_sine_integrand_q(&u__, x_)
        },
        rhs: {
            let angle = &a__ + &b__ * x_;
            let transformed =
                rubi_activate_trig(&u__) * (&capital_c__ + &capital_a__ * angle.cos().pow(2)) / angle.cos().pow(2);

            rubi_rhs_int(&transformed, x_)
        },
    ));
}

fn push_rules_rule_4723(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_a__, capital_b__, capital_c__, a__, b__, u__, x_);
    rules.push(rubi_rule!(
        order: 4723,
        source: "Int[u_*(A_.+B_.*sin[a_.+b_.*x_]+C_.*csc[a_.+b_.*x_]),x_Symbol] :=
          Int[ActivateTrig[u]*(C+A*Sin[a+b*x]+B*Sin[a+b*x]^2)/Sin[a+b*x],x] /;
        FreeQ[{a,b,A,B,C},x]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: u__ * (capital_a__ + capital_b__ * i_sin(a__ + b__ * x_) + capital_c__ * i_csc(a__ + b__ * x_)),
        with: [u__, capital_a__, capital_b__, capital_c__, a__, b__, x_],
        optional: [capital_a__, capital_b__, capital_c__, a__, b__],
        when: {
            freeq!([a__, b__, capital_a__, capital_b__, capital_c__], x_)
        },
        rhs: {
            let angle = &a__ + &b__ * x_;
            let transformed = rubi_activate_trig(&u__)
                * (&capital_c__ + &capital_a__ * angle.sin() + &capital_b__ * angle.sin().pow(2))
                / angle.sin();

            rubi_rhs_int(&transformed, x_)
        },
    ));
}

fn push_rules_rule_4724(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_a__, capital_b__, capital_c__, a__, b__, u__, x_);
    rules.push(rubi_rule!(
        order: 4724,
        source: "Int[u_*(A_.+B_.*cos[a_.+b_.*x_]+C_.*sec[a_.+b_.*x_]),x_Symbol] :=
          Int[ActivateTrig[u]*(C+A*Cos[a+b*x]+B*Cos[a+b*x]^2)/Cos[a+b*x],x] /;
        FreeQ[{a,b,A,B,C},x]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: u__ * (capital_a__ + capital_b__ * i_cos(a__ + b__ * x_) + capital_c__ * i_sec(a__ + b__ * x_)),
        with: [u__, capital_a__, capital_b__, capital_c__, a__, b__, x_],
        optional: [capital_a__, capital_b__, capital_c__, a__, b__],
        when: {
            freeq!([a__, b__, capital_a__, capital_b__, capital_c__], x_)
        },
        rhs: {
            let angle = &a__ + &b__ * x_;
            let transformed = rubi_activate_trig(&u__)
                * (&capital_c__ + &capital_a__ * angle.cos() + &capital_b__ * angle.cos().pow(2))
                / angle.cos();

            rubi_rhs_int(&transformed, x_)
        },
    ));
}

fn push_rules_rule_4725(rules: &mut Vec<RubiRule>) {
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
        order: 4725,
        source: "Int[u_*(A_.*sin[a_.+b_.*x_]^n_.+B_.*sin[a_.+b_.*x_]^n1_+C_.*sin[a_.+b_.*x_]^n2_),x_Symbol] :=
          Int[ActivateTrig[u]*Sin[a+b*x]^n*(A+B*Sin[a+b*x]+C*Sin[a+b*x]^2),x] /;
        FreeQ[{a,b,A,B,C,n},x] && EqQ[n1,n+1] && EqQ[n2,n+2]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: u__ * (capital_a__ * i_sin(a__ + b__ * x_).pow(n_)
            + capital_b__ * i_sin(a__ + b__ * x_).pow(n1_)
            + capital_c__ * i_sin(a__ + b__ * x_).pow(n2_)),
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
                * angle.sin().pow(&n_)
                * (&capital_a__ + &capital_b__ * angle.sin() + &capital_c__ * angle.sin().pow(2));

            rubi_rhs_int(&transformed, x_)
        },
    ));
}

fn push_rules_rule_4726(rules: &mut Vec<RubiRule>) {
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
        order: 4726,
        source: "Int[u_*(A_.*cos[a_.+b_.*x_]^n_.+B_.*cos[a_.+b_.*x_]^n1_+C_.*cos[a_.+b_.*x_]^n2_),x_Symbol] :=
          Int[ActivateTrig[u]*Cos[a+b*x]^n*(A+B*Cos[a+b*x]+C*Cos[a+b*x]^2),x] /;
        FreeQ[{a,b,A,B,C,n},x] && EqQ[n1,n+1] && EqQ[n2,n+2]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: u__ * (capital_a__ * i_cos(a__ + b__ * x_).pow(n_)
            + capital_b__ * i_cos(a__ + b__ * x_).pow(n1_)
            + capital_c__ * i_cos(a__ + b__ * x_).pow(n2_)),
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
                * angle.cos().pow(&n_)
                * (&capital_a__ + &capital_b__ * angle.cos() + &capital_c__ * angle.cos().pow(2));

            rubi_rhs_int(&transformed, x_)
        },
    ));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn downvalues_4702_through_4726_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .filter(|order| (4702..=4726).contains(order))
            .collect::<Vec<_>>();
        assert_eq!(orders, (4702..=4726).collect::<Vec<_>>());
    }
}
