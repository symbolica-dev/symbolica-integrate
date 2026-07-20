use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_4746(rules);
    push_rules_rule_4747(rules);
    push_rules_rule_4748(rules);
    push_rules_rule_4749(rules);
    push_rules_rule_4750(rules);
    push_rules_rule_4751(rules);
    push_rules_rule_4752(rules);
    push_rules_rule_4753(rules);
    push_rules_rule_4754(rules);
    push_rules_rule_4755(rules);
    push_rules_rule_4756(rules);
    push_rules_rule_4757(rules);
    push_rules_rule_4758(rules);
    push_rules_rule_4759(rules);
    push_rules_rule_4760(rules);
    push_rules_rule_4761(rules);
    push_rules_rule_4762(rules);
    push_rules_rule_4763(rules);
    push_rules_rule_4764(rules);
    push_rules_rule_4765(rules);
    push_rules_rule_4766(rules);
    push_rules_rule_4767(rules);
    push_rules_rule_4768(rules);
    push_rules_rule_4769(rules);
}

fn push_rules_rule_4746(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, n_, u__, x_);
    rules.push(rubi_rule!(
        order: 4746,
        source: "Int[u_*(c_.*sin[a_.+b_.*x_])^m_.*(d_.*csc[a_.+b_.*x_])^n_.,x_Symbol] :=
          (c*Sin[a+b*x])^m*(d*Csc[a+b*x])^m \\[Star] Int[ActivateTrig[u]*(d*Csc[a+b*x])^(n-m),x] /;
        FreeQ[{a,b,c,d,m,n},x] && KnownSecantIntegrandQ[u,x]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: u__ * (c__ * i_sin(a__ + b__ * x_)).pow(m_) * (d__ * i_csc(a__ + b__ * x_)).pow(n_),
        with: [u__, c__, a__, b__, m_, d__, n_, x_],
        optional: [c__, a__, b__, m_, d__, n_],
        when: {
            freeq!([a__, b__, c__, d__, m_, n_], x_)
                && rubi_known_secant_integrand_q(&u__, x_)
        },
        rhs: {
            let angle = &a__ + &b__ * x_;
            let transformed = rubi_activate_trig(&u__) * (&d__ * angle.csc()).pow(&n_ - &m_);
            let recursive = rubi_rhs_int(&transformed, x_);

            let coefficient =
                (&c__ * angle.sin()).pow(&m_) * (&d__ * angle.csc()).pow(&m_);
            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_4747(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, n_, u__, x_);
    rules.push(rubi_rule!(
        order: 4747,
        source: "Int[u_*(c_.*cos[a_.+b_.*x_])^m_.*(d_.*sec[a_.+b_.*x_])^n_.,x_Symbol] :=
          (c*Cos[a+b*x])^m*(d*Sec[a+b*x])^m \\[Star] Int[ActivateTrig[u]*(d*Sec[a+b*x])^(n-m),x] /;
        FreeQ[{a,b,c,d,m,n},x] && KnownSecantIntegrandQ[u,x]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: u__ * (c__ * i_cos(a__ + b__ * x_)).pow(m_) * (d__ * i_sec(a__ + b__ * x_)).pow(n_),
        with: [u__, c__, a__, b__, m_, d__, n_, x_],
        optional: [c__, a__, b__, m_, d__, n_],
        when: {
            freeq!([a__, b__, c__, d__, m_, n_], x_)
                && rubi_known_secant_integrand_q(&u__, x_)
        },
        rhs: {
            let angle = &a__ + &b__ * x_;
            let transformed = rubi_activate_trig(&u__) * (&d__ * angle.sec()).pow(&n_ - &m_);
            let recursive = rubi_rhs_int(&transformed, x_);

            let coefficient =
                (&c__ * angle.cos()).pow(&m_) * (&d__ * angle.sec()).pow(&m_);
            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_4748(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, n_, u__, x_);
    rules.push(rubi_rule!(
        order: 4748,
        source: "Int[u_*(c_.*tan[a_.+b_.*x_])^m_.*(d_.*sec[a_.+b_.*x_])^n_.,x_Symbol] :=
          (c*Tan[a+b*x])^m*(d*Csc[a+b*x])^m/(d*Sec[a+b*x])^m \\[Star] Int[ActivateTrig[u]*(d*Sec[a+b*x])^(m+n)/(d*Csc[a+b*x])^m,x] /;
        FreeQ[{a,b,c,d,m,n},x] && KnownSecantIntegrandQ[u,x] && Not[IntegerQ[m]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: u__ * (c__ * i_tan(a__ + b__ * x_)).pow(m_) * (d__ * i_sec(a__ + b__ * x_)).pow(n_),
        with: [u__, c__, a__, b__, m_, d__, n_, x_],
        optional: [c__, a__, b__, m_, d__, n_],
        when: {
            freeq!([a__, b__, c__, d__, m_, n_], x_)
                && rubi_known_secant_integrand_q(&u__, x_)
                && !integerq!(m_)
        },
        rhs: {
            let angle = &a__ + &b__ * x_;
            let transformed =
                rubi_activate_trig(&u__) * (&d__ * angle.sec()).pow(&m_ + &n_) / (&d__ * angle.csc()).pow(&m_);
            let recursive = rubi_rhs_int(&transformed, x_);

            let coefficient = (&c__ * angle.tan()).pow(&m_)
                * (&d__ * angle.csc()).pow(&m_)
                / (&d__ * angle.sec()).pow(&m_);
            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_4749(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, n_, u__, x_);
    rules.push(rubi_rule!(
        order: 4749,
        source: "Int[u_*(c_.*tan[a_.+b_.*x_])^m_.*(d_.*csc[a_.+b_.*x_])^n_.,x_Symbol] :=
          (c*Tan[a+b*x])^m*(d*Csc[a+b*x])^m/(d*Sec[a+b*x])^m \\[Star] Int[ActivateTrig[u]*(d*Sec[a+b*x])^m/(d*Csc[a+b*x])^(m-n),x] /;
        FreeQ[{a,b,c,d,m,n},x] && KnownSecantIntegrandQ[u,x] && Not[IntegerQ[m]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: u__ * (c__ * i_tan(a__ + b__ * x_)).pow(m_) * (d__ * i_csc(a__ + b__ * x_)).pow(n_),
        with: [u__, c__, a__, b__, m_, d__, n_, x_],
        optional: [c__, a__, b__, m_, d__, n_],
        when: {
            freeq!([a__, b__, c__, d__, m_, n_], x_)
                && rubi_known_secant_integrand_q(&u__, x_)
                && !integerq!(m_)
        },
        rhs: {
            let angle = &a__ + &b__ * x_;
            let transformed =
                rubi_activate_trig(&u__) * (&d__ * angle.sec()).pow(&m_) / (&d__ * angle.csc()).pow(&m_ - &n_);
            let recursive = rubi_rhs_int(&transformed, x_);

            let coefficient = (&c__ * angle.tan()).pow(&m_)
                * (&d__ * angle.csc()).pow(&m_)
                / (&d__ * angle.sec()).pow(&m_);
            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_4750(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, n_, u__, x_);
    rules.push(rubi_rule!(
        order: 4750,
        source: "Int[u_*(c_.*cot[a_.+b_.*x_])^m_.*(d_.*sec[a_.+b_.*x_])^n_.,x_Symbol] :=
          (c*Cot[a+b*x])^m*(d*Sec[a+b*x])^m/(d*Csc[a+b*x])^m \\[Star] Int[ActivateTrig[u]*(d*Csc[a+b*x])^m/(d*Sec[a+b*x])^(m-n),x] /;
        FreeQ[{a,b,c,d,m,n},x] && KnownSecantIntegrandQ[u,x] && Not[IntegerQ[m]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: u__ * (c__ * i_cot(a__ + b__ * x_)).pow(m_) * (d__ * i_sec(a__ + b__ * x_)).pow(n_),
        with: [u__, c__, a__, b__, m_, d__, n_, x_],
        optional: [c__, a__, b__, m_, d__, n_],
        when: {
            freeq!([a__, b__, c__, d__, m_, n_], x_)
                && rubi_known_secant_integrand_q(&u__, x_)
                && !integerq!(m_)
        },
        rhs: {
            let angle = &a__ + &b__ * x_;
            let transformed =
                rubi_activate_trig(&u__) * (&d__ * angle.csc()).pow(&m_) / (&d__ * angle.sec()).pow(&m_ - &n_);
            let recursive = rubi_rhs_int(&transformed, x_);

            let coefficient = (&c__ * angle.cot()).pow(&m_)
                * (&d__ * angle.sec()).pow(&m_)
                / (&d__ * angle.csc()).pow(&m_);
            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_4751(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, n_, u__, x_);
    rules.push(rubi_rule!(
        order: 4751,
        source: "Int[u_*(c_.*cot[a_.+b_.*x_])^m_.*(d_.*csc[a_.+b_.*x_])^n_.,x_Symbol] :=
          (c*Cot[a+b*x])^m*(d*Sec[a+b*x])^m/(d*Csc[a+b*x])^m \\[Star] Int[ActivateTrig[u]*(d*Csc[a+b*x])^(m+n)/(d*Sec[a+b*x])^m,x] /;
        FreeQ[{a,b,c,d,m,n},x] && KnownSecantIntegrandQ[u,x] && Not[IntegerQ[m]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: u__ * (c__ * i_cot(a__ + b__ * x_)).pow(m_) * (d__ * i_csc(a__ + b__ * x_)).pow(n_),
        with: [u__, c__, a__, b__, m_, d__, n_, x_],
        optional: [c__, a__, b__, m_, d__, n_],
        when: {
            freeq!([a__, b__, c__, d__, m_, n_], x_)
                && rubi_known_secant_integrand_q(&u__, x_)
                && !integerq!(m_)
        },
        rhs: {
            let angle = &a__ + &b__ * x_;
            let transformed =
                rubi_activate_trig(&u__) * (&d__ * angle.csc()).pow(&m_ + &n_) / (&d__ * angle.sec()).pow(&m_);
            let recursive = rubi_rhs_int(&transformed, x_);

            let coefficient = (&c__ * angle.cot()).pow(&m_)
                * (&d__ * angle.sec()).pow(&m_)
                / (&d__ * angle.csc()).pow(&m_);
            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_4752(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, m_, u__, x_);
    rules.push(rubi_rule!(
        order: 4752,
        source: "Int[u_*(c_.*sin[a_.+b_.*x_])^m_.,x_Symbol] :=
          (c*Csc[a+b*x])^m*(c*Sin[a+b*x])^m \\[Star] Int[ActivateTrig[u]/(c*Csc[a+b*x])^m,x] /;
        FreeQ[{a,b,c,m},x] && Not[IntegerQ[m]] && KnownSecantIntegrandQ[u,x]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: u__ * (c__ * i_sin(a__ + b__ * x_)).pow(m_),
        with: [u__, c__, a__, b__, m_, x_],
        optional: [c__, a__, b__, m_],
        when: {
            freeq!([a__, b__, c__, m_], x_)
                && !integerq!(m_)
                && rubi_known_secant_integrand_q(&u__, x_)
        },
        rhs: {
            let angle = &a__ + &b__ * x_;
            let transformed = rubi_activate_trig(&u__) / (&c__ * angle.csc()).pow(&m_);
            let recursive = rubi_rhs_int(&transformed, x_);

            let coefficient =
                (&c__ * angle.csc()).pow(&m_) * (&c__ * angle.sin()).pow(&m_);
            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_4753(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, m_, u__, x_);
    rules.push(rubi_rule!(
        order: 4753,
        source: "Int[u_*(c_.*cos[a_.+b_.*x_])^m_.,x_Symbol] :=
          (c*Cos[a+b*x])^m*(c*Sec[a+b*x])^m \\[Star] Int[ActivateTrig[u]/(c*Sec[a+b*x])^m,x] /;
        FreeQ[{a,b,c,m},x] && Not[IntegerQ[m]] && KnownSecantIntegrandQ[u,x]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: u__ * (c__ * i_cos(a__ + b__ * x_)).pow(m_),
        with: [u__, c__, a__, b__, m_, x_],
        optional: [c__, a__, b__, m_],
        when: {
            freeq!([a__, b__, c__, m_], x_)
                && !integerq!(m_)
                && rubi_known_secant_integrand_q(&u__, x_)
        },
        rhs: {
            let angle = &a__ + &b__ * x_;
            let transformed = rubi_activate_trig(&u__) / (&c__ * angle.sec()).pow(&m_);
            let recursive = rubi_rhs_int(&transformed, x_);

            let coefficient =
                (&c__ * angle.cos()).pow(&m_) * (&c__ * angle.sec()).pow(&m_);
            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_4754(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, m_, u__, x_);
    rules.push(rubi_rule!(
        order: 4754,
        source: "Int[u_*(c_.*tan[a_.+b_.*x_])^m_.,x_Symbol] :=
          (c*Tan[a+b*x])^m*(c*Csc[a+b*x])^m/(c*Sec[a+b*x])^m \\[Star] Int[ActivateTrig[u]*(c*Sec[a+b*x])^m/(c*Csc[a+b*x])^m,x] /;
        FreeQ[{a,b,c,m},x] && Not[IntegerQ[m]] && KnownSecantIntegrandQ[u,x]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: u__ * (c__ * i_tan(a__ + b__ * x_)).pow(m_),
        with: [u__, c__, a__, b__, m_, x_],
        optional: [c__, a__, b__, m_],
        when: {
            freeq!([a__, b__, c__, m_], x_)
                && !integerq!(m_)
                && rubi_known_secant_integrand_q(&u__, x_)
        },
        rhs: {
            let angle = &a__ + &b__ * x_;
            let transformed = rubi_activate_trig(&u__) * (&c__ * angle.sec()).pow(&m_) / (&c__ * angle.csc()).pow(&m_);
            let recursive = rubi_rhs_int(&transformed, x_);

            let coefficient = (&c__ * angle.tan()).pow(&m_)
                * (&c__ * angle.csc()).pow(&m_)
                / (&c__ * angle.sec()).pow(&m_);
            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_4755(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, m_, u__, x_);
    rules.push(rubi_rule!(
        order: 4755,
        source: "Int[u_*(c_.*cot[a_.+b_.*x_])^m_.,x_Symbol] :=
          (c*Cot[a+b*x])^m*(c*Sec[a+b*x])^m/(c*Csc[a+b*x])^m \\[Star] Int[ActivateTrig[u]*(c*Csc[a+b*x])^m/(c*Sec[a+b*x])^m,x] /;
        FreeQ[{a,b,c,m},x] && Not[IntegerQ[m]] && KnownSecantIntegrandQ[u,x]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: u__ * (c__ * i_cot(a__ + b__ * x_)).pow(m_),
        with: [u__, c__, a__, b__, m_, x_],
        optional: [c__, a__, b__, m_],
        when: {
            freeq!([a__, b__, c__, m_], x_)
                && !integerq!(m_)
                && rubi_known_secant_integrand_q(&u__, x_)
        },
        rhs: {
            let angle = &a__ + &b__ * x_;
            let transformed = rubi_activate_trig(&u__) * (&c__ * angle.csc()).pow(&m_) / (&c__ * angle.sec()).pow(&m_);
            let recursive = rubi_rhs_int(&transformed, x_);

            let coefficient = (&c__ * angle.cot()).pow(&m_)
                * (&c__ * angle.sec()).pow(&m_)
                / (&c__ * angle.csc()).pow(&m_);
            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_4756(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_a__, capital_b__, a__, b__, c__, n_, u__, x_);
    rules.push(rubi_rule!(
        order: 4756,
        source: "Int[u_*(c_.*sec[a_.+b_.*x_])^n_.*(A_+B_.*cos[a_.+b_.*x_]),x_Symbol] :=
          c \\[Star] Int[ActivateTrig[u]*(c*Sec[a+b*x])^(n-1)*(B+A*Sec[a+b*x]),x] /;
        FreeQ[{a,b,c,A,B,n},x] && KnownSecantIntegrandQ[u,x]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: u__ * (c__ * i_sec(a__ + b__ * x_)).pow(n_) * (capital_a__ + capital_b__ * i_cos(a__ + b__ * x_)),
        with: [u__, c__, a__, b__, n_, capital_a__, capital_b__, x_],
        optional: [c__, a__, b__, n_, capital_b__],
        when: {
            freeq!([a__, b__, c__, capital_a__, capital_b__, n_], x_)
                && rubi_known_secant_integrand_q(&u__, x_)
        },
        rhs: {
            let angle = &a__ + &b__ * x_;
            let transformed =
                rubi_activate_trig(&u__) * (&c__ * angle.sec()).pow(&n_ - 1) * (&capital_b__ + &capital_a__ * angle.sec());
            let recursive = rubi_rhs_int(&transformed, x_);

            rubi_star(c__, recursive)
        },
    ));
}

fn push_rules_rule_4757(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_a__, capital_b__, a__, b__, c__, n_, u__, x_);
    rules.push(rubi_rule!(
        order: 4757,
        source: "Int[u_*(c_.*csc[a_.+b_.*x_])^n_.*(A_+B_.*sin[a_.+b_.*x_]),x_Symbol] :=
          c \\[Star] Int[ActivateTrig[u]*(c*Csc[a+b*x])^(n-1)*(B+A*Csc[a+b*x]),x] /;
        FreeQ[{a,b,c,A,B,n},x] && KnownSecantIntegrandQ[u,x]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: u__ * (c__ * i_csc(a__ + b__ * x_)).pow(n_) * (capital_a__ + capital_b__ * i_sin(a__ + b__ * x_)),
        with: [u__, c__, a__, b__, n_, capital_a__, capital_b__, x_],
        optional: [c__, a__, b__, n_, capital_b__],
        when: {
            freeq!([a__, b__, c__, capital_a__, capital_b__, n_], x_)
                && rubi_known_secant_integrand_q(&u__, x_)
        },
        rhs: {
            let angle = &a__ + &b__ * x_;
            let transformed =
                rubi_activate_trig(&u__) * (&c__ * angle.csc()).pow(&n_ - 1) * (&capital_b__ + &capital_a__ * angle.csc());
            let recursive = rubi_rhs_int(&transformed, x_);

            rubi_star(c__, recursive)
        },
    ));
}

fn push_rules_rule_4758(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_a__, capital_b__, a__, b__, u__, x_);
    rules.push(rubi_rule!(
        order: 4758,
        source: "Int[u_*(A_+B_.*cos[a_.+b_.*x_]),x_Symbol] :=
          Int[ActivateTrig[u]*(B+A*Sec[a+b*x])/Sec[a+b*x],x] /;
        FreeQ[{a,b,A,B},x] && KnownSecantIntegrandQ[u,x]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: u__ * (capital_a__ + capital_b__ * i_cos(a__ + b__ * x_)),
        with: [u__, capital_a__, capital_b__, a__, b__, x_],
        optional: [capital_b__, a__, b__],
        when: {
            freeq!([a__, b__, capital_a__, capital_b__], x_)
                && rubi_known_secant_integrand_q(&u__, x_)
        },
        rhs: {
            let angle = &a__ + &b__ * x_;
            let transformed = rubi_activate_trig(&u__) * (&capital_b__ + &capital_a__ * angle.sec()) / angle.sec();

            rubi_rhs_int(&transformed, x_)
        },
    ));
}

fn push_rules_rule_4759(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_a__, capital_b__, a__, b__, u__, x_);
    rules.push(rubi_rule!(
        order: 4759,
        source: "Int[u_*(A_+B_.*sin[a_.+b_.*x_]),x_Symbol] :=
          Int[ActivateTrig[u]*(B+A*Csc[a+b*x])/Csc[a+b*x],x] /;
        FreeQ[{a,b,A,B},x] && KnownSecantIntegrandQ[u,x]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: u__ * (capital_a__ + capital_b__ * i_sin(a__ + b__ * x_)),
        with: [u__, capital_a__, capital_b__, a__, b__, x_],
        optional: [capital_b__, a__, b__],
        when: {
            freeq!([a__, b__, capital_a__, capital_b__], x_)
                && rubi_known_secant_integrand_q(&u__, x_)
        },
        rhs: {
            let angle = &a__ + &b__ * x_;
            let transformed = rubi_activate_trig(&u__) * (&capital_b__ + &capital_a__ * angle.csc()) / angle.csc();

            rubi_rhs_int(&transformed, x_)
        },
    ));
}

fn push_rules_rule_4760(rules: &mut Vec<RubiRule>) {
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
        order: 4760,
        source: "Int[u_.*(c_.*sec[a_.+b_.*x_])^n_.*(A_.+B_.*cos[a_.+b_.*x_]+C_.*cos[a_.+b_.*x_]^2),x_Symbol] :=
          c^2 \\[Star] Int[ActivateTrig[u]*(c*Sec[a+b*x])^(n-2)*(C+B*Sec[a+b*x]+A*Sec[a+b*x]^2),x] /;
        FreeQ[{a,b,c,A,B,C,n},x] && KnownSecantIntegrandQ[u,x]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: u__ * (c__ * i_sec(a__ + b__ * x_)).pow(n_)
            * (capital_a__ + capital_b__ * i_cos(a__ + b__ * x_) + capital_c__ * i_cos(a__ + b__ * x_).pow(2)),
        with: [u__, c__, a__, b__, n_, capital_a__, capital_b__, capital_c__, x_],
        optional: [u__, c__, a__, b__, n_, capital_a__, capital_b__, capital_c__],
        when: {
            freeq!([a__, b__, c__, capital_a__, capital_b__, capital_c__, n_], x_)
                && rubi_known_secant_integrand_q(&u__, x_)
        },
        rhs: {
            let angle = &a__ + &b__ * x_;
            let transformed = rubi_activate_trig(&u__)
                * (&c__ * angle.sec()).pow(&n_ - 2)
                * (&capital_c__ + &capital_b__ * angle.sec() + &capital_a__ * angle.sec().pow(2));
            let recursive = rubi_rhs_int(&transformed, x_);

            rubi_star(c__.pow(2), recursive)
        },
    ));
}

fn push_rules_rule_4761(rules: &mut Vec<RubiRule>) {
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
        order: 4761,
        source: "Int[u_.*(c_.*csc[a_.+b_.*x_])^n_.*(A_.+B_.*sin[a_.+b_.*x_]+C_.*sin[a_.+b_.*x_]^2),x_Symbol] :=
          c^2 \\[Star] Int[ActivateTrig[u]*(c*Csc[a+b*x])^(n-2)*(C+B*Csc[a+b*x]+A*Csc[a+b*x]^2),x] /;
        FreeQ[{a,b,c,A,B,C,n},x] && KnownSecantIntegrandQ[u,x]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: u__ * (c__ * i_csc(a__ + b__ * x_)).pow(n_)
            * (capital_a__ + capital_b__ * i_sin(a__ + b__ * x_) + capital_c__ * i_sin(a__ + b__ * x_).pow(2)),
        with: [u__, c__, a__, b__, n_, capital_a__, capital_b__, capital_c__, x_],
        optional: [u__, c__, a__, b__, n_, capital_a__, capital_b__, capital_c__],
        when: {
            freeq!([a__, b__, c__, capital_a__, capital_b__, capital_c__, n_], x_)
                && rubi_known_secant_integrand_q(&u__, x_)
        },
        rhs: {
            let angle = &a__ + &b__ * x_;
            let transformed = rubi_activate_trig(&u__)
                * (&c__ * angle.csc()).pow(&n_ - 2)
                * (&capital_c__ + &capital_b__ * angle.csc() + &capital_a__ * angle.csc().pow(2));
            let recursive = rubi_rhs_int(&transformed, x_);

            rubi_star(c__.pow(2), recursive)
        },
    ));
}

fn push_rules_rule_4762(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_a__, capital_c__, a__, b__, c__, n_, u__, x_);
    rules.push(rubi_rule!(
        order: 4762,
        source: "Int[u_.*(c_.*sec[a_.+b_.*x_])^n_.*(A_+C_.*cos[a_.+b_.*x_]^2),x_Symbol] :=
          c^2 \\[Star] Int[ActivateTrig[u]*(c*Sec[a+b*x])^(n-2)*(C+A*Sec[a+b*x]^2),x] /;
        FreeQ[{a,b,c,A,C,n},x] && KnownSecantIntegrandQ[u,x]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: u__ * (c__ * i_sec(a__ + b__ * x_)).pow(n_)
            * (capital_a__ + capital_c__ * i_cos(a__ + b__ * x_).pow(2)),
        with: [u__, c__, a__, b__, n_, capital_a__, capital_c__, x_],
        optional: [u__, c__, a__, b__, n_, capital_c__],
        when: {
            freeq!([a__, b__, c__, capital_a__, capital_c__, n_], x_)
                && rubi_known_secant_integrand_q(&u__, x_)
        },
        rhs: {
            let angle = &a__ + &b__ * x_;
            let transformed =
                rubi_activate_trig(&u__) * (&c__ * angle.sec()).pow(&n_ - 2) * (&capital_c__ + &capital_a__ * angle.sec().pow(2));
            let recursive = rubi_rhs_int(&transformed, x_);

            rubi_star(c__.pow(2), recursive)
        },
    ));
}

fn push_rules_rule_4763(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_a__, capital_c__, a__, b__, c__, n_, u__, x_);
    rules.push(rubi_rule!(
        order: 4763,
        source: "Int[u_.*(c_.*csc[a_.+b_.*x_])^n_.*(A_+C_.*sin[a_.+b_.*x_]^2),x_Symbol] :=
          c^2 \\[Star] Int[ActivateTrig[u]*(c*Csc[a+b*x])^(n-2)*(C+A*Csc[a+b*x]^2),x] /;
        FreeQ[{a,b,c,A,C,n},x] && KnownSecantIntegrandQ[u,x]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: u__ * (c__ * i_csc(a__ + b__ * x_)).pow(n_)
            * (capital_a__ + capital_c__ * i_sin(a__ + b__ * x_).pow(2)),
        with: [u__, c__, a__, b__, n_, capital_a__, capital_c__, x_],
        optional: [u__, c__, a__, b__, n_, capital_c__],
        when: {
            freeq!([a__, b__, c__, capital_a__, capital_c__, n_], x_)
                && rubi_known_secant_integrand_q(&u__, x_)
        },
        rhs: {
            let angle = &a__ + &b__ * x_;
            let transformed =
                rubi_activate_trig(&u__) * (&c__ * angle.csc()).pow(&n_ - 2) * (&capital_c__ + &capital_a__ * angle.csc().pow(2));
            let recursive = rubi_rhs_int(&transformed, x_);

            rubi_star(c__.pow(2), recursive)
        },
    ));
}

fn push_rules_rule_4764(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_a__, capital_b__, capital_c__, a__, b__, u__, x_);
    rules.push(rubi_rule!(
        order: 4764,
        source: "Int[u_*(A_.+B_.*cos[a_.+b_.*x_]+C_.*cos[a_.+b_.*x_]^2),x_Symbol] :=
          Int[ActivateTrig[u]*(C+B*Sec[a+b*x]+A*Sec[a+b*x]^2)/Sec[a+b*x]^2,x] /;
        FreeQ[{a,b,A,B,C},x] && KnownSecantIntegrandQ[u,x]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: u__ * (capital_a__ + capital_b__ * i_cos(a__ + b__ * x_) + capital_c__ * i_cos(a__ + b__ * x_).pow(2)),
        with: [u__, capital_a__, capital_b__, capital_c__, a__, b__, x_],
        optional: [capital_a__, capital_b__, capital_c__, a__, b__],
        when: {
            freeq!([a__, b__, capital_a__, capital_b__, capital_c__], x_)
                && rubi_known_secant_integrand_q(&u__, x_)
        },
        rhs: {
            let angle = &a__ + &b__ * x_;
            let transformed = rubi_activate_trig(&u__)
                * (&capital_c__ + &capital_b__ * angle.sec() + &capital_a__ * angle.sec().pow(2))
                / angle.sec().pow(2);

            rubi_rhs_int(&transformed, x_)
        },
    ));
}

fn push_rules_rule_4765(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_a__, capital_b__, capital_c__, a__, b__, u__, x_);
    rules.push(rubi_rule!(
        order: 4765,
        source: "Int[u_*(A_.+B_.*sin[a_.+b_.*x_]+C_.*sin[a_.+b_.*x_]^2),x_Symbol] :=
          Int[ActivateTrig[u]*(C+B*Csc[a+b*x]+A*Csc[a+b*x]^2)/Csc[a+b*x]^2,x] /;
        FreeQ[{a,b,A,B,C},x] && KnownSecantIntegrandQ[u,x]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: u__ * (capital_a__ + capital_b__ * i_sin(a__ + b__ * x_) + capital_c__ * i_sin(a__ + b__ * x_).pow(2)),
        with: [u__, capital_a__, capital_b__, capital_c__, a__, b__, x_],
        optional: [capital_a__, capital_b__, capital_c__, a__, b__],
        when: {
            freeq!([a__, b__, capital_a__, capital_b__, capital_c__], x_)
                && rubi_known_secant_integrand_q(&u__, x_)
        },
        rhs: {
            let angle = &a__ + &b__ * x_;
            let transformed = rubi_activate_trig(&u__)
                * (&capital_c__ + &capital_b__ * angle.csc() + &capital_a__ * angle.csc().pow(2))
                / angle.csc().pow(2);

            rubi_rhs_int(&transformed, x_)
        },
    ));
}

fn push_rules_rule_4766(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_a__, capital_c__, a__, b__, u__, x_);
    rules.push(rubi_rule!(
        order: 4766,
        source: "Int[u_*(A_+C_.*cos[a_.+b_.*x_]^2),x_Symbol] :=
          Int[ActivateTrig[u]*(C+A*Sec[a+b*x]^2)/Sec[a+b*x]^2,x] /;
        FreeQ[{a,b,A,C},x] && KnownSecantIntegrandQ[u,x]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: u__ * (capital_a__ + capital_c__ * i_cos(a__ + b__ * x_).pow(2)),
        with: [u__, capital_a__, capital_c__, a__, b__, x_],
        optional: [capital_c__, a__, b__],
        when: {
            freeq!([a__, b__, capital_a__, capital_c__], x_)
                && rubi_known_secant_integrand_q(&u__, x_)
        },
        rhs: {
            let angle = &a__ + &b__ * x_;
            let transformed =
                rubi_activate_trig(&u__) * (&capital_c__ + &capital_a__ * angle.sec().pow(2)) / angle.sec().pow(2);

            rubi_rhs_int(&transformed, x_)
        },
    ));
}

fn push_rules_rule_4767(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_a__, capital_c__, a__, b__, u__, x_);
    rules.push(rubi_rule!(
        order: 4767,
        source: "Int[u_*(A_+C_.*sin[a_.+b_.*x_]^2),x_Symbol] :=
          Int[ActivateTrig[u]*(C+A*Csc[a+b*x]^2)/Csc[a+b*x]^2,x] /;
        FreeQ[{a,b,A,C},x] && KnownSecantIntegrandQ[u,x]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: u__ * (capital_a__ + capital_c__ * i_sin(a__ + b__ * x_).pow(2)),
        with: [u__, capital_a__, capital_c__, a__, b__, x_],
        optional: [capital_c__, a__, b__],
        when: {
            freeq!([a__, b__, capital_a__, capital_c__], x_)
                && rubi_known_secant_integrand_q(&u__, x_)
        },
        rhs: {
            let angle = &a__ + &b__ * x_;
            let transformed =
                rubi_activate_trig(&u__) * (&capital_c__ + &capital_a__ * angle.csc().pow(2)) / angle.csc().pow(2);

            rubi_rhs_int(&transformed, x_)
        },
    ));
}

fn push_rules_rule_4768(rules: &mut Vec<RubiRule>) {
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
        order: 4768,
        source: "Int[u_*(A_.*sec[a_.+b_.*x_]^n_.+B_.*sec[a_.+b_.*x_]^n1_+C_.*sec[a_.+b_.*x_]^n2_),x_Symbol] :=
          Int[ActivateTrig[u]*Sec[a+b*x]^n*(A+B*Sec[a+b*x]+C*Sec[a+b*x]^2),x] /;
        FreeQ[{a,b,A,B,C,n},x] && EqQ[n1,n+1] && EqQ[n2,n+2]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: u__ * (capital_a__ * i_sec(a__ + b__ * x_).pow(n_)
            + capital_b__ * i_sec(a__ + b__ * x_).pow(n1_)
            + capital_c__ * i_sec(a__ + b__ * x_).pow(n2_)),
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
                * angle.sec().pow(&n_)
                * (&capital_a__ + &capital_b__ * angle.sec() + &capital_c__ * angle.sec().pow(2));

            rubi_rhs_int(&transformed, x_)
        },
    ));
}

fn push_rules_rule_4769(rules: &mut Vec<RubiRule>) {
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
        order: 4769,
        source: "Int[u_*(A_.*csc[a_.+b_.*x_]^n_.+B_.*csc[a_.+b_.*x_]^n1_+C_.*csc[a_.+b_.*x_]^n2_),x_Symbol] :=
          Int[ActivateTrig[u]*Csc[a+b*x]^n*(A+B*Csc[a+b*x]+C*Csc[a+b*x]^2),x] /;
        FreeQ[{a,b,A,B,C,n},x] && EqQ[n1,n+1] && EqQ[n2,n+2]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: u__ * (capital_a__ * i_csc(a__ + b__ * x_).pow(n_)
            + capital_b__ * i_csc(a__ + b__ * x_).pow(n1_)
            + capital_c__ * i_csc(a__ + b__ * x_).pow(n2_)),
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
                * angle.csc().pow(&n_)
                * (&capital_a__ + &capital_b__ * angle.csc() + &capital_c__ * angle.csc().pow(2));

            rubi_rhs_int(&transformed, x_)
        },
    ));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn downvalues_4746_through_4769_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .filter(|order| (4746..=4769).contains(order))
            .collect::<Vec<_>>();
        assert_eq!(orders, (4746..=4769).collect::<Vec<_>>());
    }
}
