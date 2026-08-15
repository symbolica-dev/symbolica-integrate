use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_4932(rules);
    push_rules_rule_4933(rules);
    push_rules_rule_4934(rules);
    push_rules_rule_4935(rules);
    push_rules_rule_4936(rules);
    push_rules_rule_4937(rules);
    push_rules_rule_4938(rules);
    push_rules_rule_4939(rules);
    push_rules_rule_4940(rules);
    push_rules_rule_4941(rules);
    push_rules_rule_4942(rules);
    push_rules_rule_4943(rules);
    push_rules_rule_4944(rules);
    push_rules_rule_4945(rules);
    push_rules_rule_4946(rules);
    push_rules_rule_4947(rules);
    push_rules_rule_4948(rules);
    push_rules_rule_4949(rules);
    push_rules_rule_4950(rules);
    push_rules_rule_4951(rules);
    push_rules_rule_4952(rules);
    push_rules_rule_4953(rules);
    push_rules_rule_4954(rules);
    push_rules_rule_4955(rules);
    push_rules_rule_4956(rules);
    push_rules_rule_4957(rules);
    push_rules_rule_4958(rules);
    push_rules_rule_4959(rules);
    push_rules_rule_4960(rules);
    push_rules_rule_4961(rules);
    push_rules_rule_4962(rules);
    push_rules_rule_4963(rules);
    push_rules_rule_4964(rules);
    push_rules_rule_4965(rules);
    push_rules_rule_4966(rules);
    push_rules_rule_4967(rules);
    push_rules_rule_4968(rules);
    push_rules_rule_4969(rules);
    push_rules_rule_4970(rules);
    push_rules_rule_4971(rules);
    push_rules_rule_4972(rules);
    push_rules_rule_4973(rules);
    push_rules_rule_4974(rules);
    push_rules_rule_4975(rules);
    push_rules_rule_4976(rules);
    push_rules_rule_4977(rules);
}

fn push_rules_rule_4932(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_f_, a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 4932,
        source: "Int[F_^(c_.*(a_.+b_.*x_))*Sin[d_.+e_.*x_],x_Symbol] :=
          b*c*Log[F]*F^(c*(a+b*x))*Sin[d+e*x]/(e^2+b^2*c^2*Log[F]^2) -
          e*F^(c*(a+b*x))*Cos[d+e*x]/(e^2+b^2*c^2*Log[F]^2) /;
        FreeQ[{F,a,b,c,d,e},x] && NeQ[e^2+b^2*c^2*Log[F]^2,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: ["CRC 533, A&S 4.3.136", "CRC 538, A&S 4.3.137"],
        pattern: capital_f_.pow(c__ * (a__ + b__ * x_)) * (d__ + e__ * x_).sin(),
        with: [capital_f_, c__, a__, b__, d__, e__, x_],
        optional: [c__, a__, b__, d__, e__],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__], x_)
                && neq!(e__.pow(2) + b__.pow(2) * c__.pow(2) * capital_f_.log().pow(2), 0)
        },
        rhs: {
            let exponential = capital_f_.pow(&c__ * (&a__ + &b__ * x_));
            let angle = &d__ + &e__ * x_;
            let denominator = e__.pow(2) + b__.pow(2) * c__.pow(2) * capital_f_.log().pow(2);

            rubi_simp(&(&b__ * &c__ * capital_f_.log() * &exponential * angle.sin() / &denominator), x_)
                    - rubi_simp(&(&e__ * exponential * angle.cos() / denominator), x_)
        },
    ));
}

fn push_rules_rule_4933(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_f_, a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 4933,
        source: "Int[F_^(c_.*(a_.+b_.*x_))*Cos[d_.+e_.*x_],x_Symbol] :=
          b*c*Log[F]*F^(c*(a+b*x))*Cos[d+e*x]/(e^2+b^2*c^2*Log[F]^2) +
          e*F^(c*(a+b*x))*Sin[d+e*x]/(e^2+b^2*c^2*Log[F]^2) /;
        FreeQ[{F,a,b,c,d,e},x] && NeQ[e^2+b^2*c^2*Log[F]^2,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: ["CRC 533, A&S 4.3.136", "CRC 538, A&S 4.3.137"],
        pattern: capital_f_.pow(c__ * (a__ + b__ * x_)) * (d__ + e__ * x_).cos(),
        with: [capital_f_, c__, a__, b__, d__, e__, x_],
        optional: [c__, a__, b__, d__, e__],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__], x_)
                && neq!(e__.pow(2) + b__.pow(2) * c__.pow(2) * capital_f_.log().pow(2), 0)
        },
        rhs: {
            let exponential = capital_f_.pow(&c__ * (&a__ + &b__ * x_));
            let angle = &d__ + &e__ * x_;
            let denominator = e__.pow(2) + b__.pow(2) * c__.pow(2) * capital_f_.log().pow(2);

            rubi_simp(&(&b__ * &c__ * capital_f_.log() * &exponential * angle.cos() / &denominator), x_)
                    + rubi_simp(&(&e__ * exponential * angle.sin() / denominator), x_)
        },
    ));
}

fn push_rules_rule_4934(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, d__, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 4934,
        source: "Int[F_^(c_.*(a_.+b_.*x_))*Sin[d_.+e_.*x_]^n_,x_Symbol] :=
          b*c*Log[F]*F^(c*(a+b*x))*Sin[d+e*x]^n/(e^2*n^2+b^2*c^2*Log[F]^2) -
          e*n*F^(c*(a+b*x))*Cos[d+e*x]*Sin[d+e*x]^(n-1)/(e^2*n^2+b^2*c^2*Log[F]^2) +
          (n*(n-1)*e^2)/(e^2*n^2+b^2*c^2*Log[F]^2) \\[Star] Int[F^(c*(a+b*x))*Sin[d+e*x]^(n-2),x] /;
        FreeQ[{F,a,b,c,d,e},x] && NeQ[e^2*n^2+b^2*c^2*Log[F]^2,0] && GtQ[n,1]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: ["CRC 542, A&S 4.3.138", "CRC 543, A&S 4.3.139"],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [capital_f_, c__, a__, b__, d__, e__, n_, x_],
        optional: [c__, a__, b__, d__, e__],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__], x_)
                && neq!(e__.pow(2) * n_.pow(2) + b__.pow(2) * c__.pow(2) * capital_f_.log().pow(2), 0)
                && gtq!(n_, 1)
        },
        rhs: {
            let exponential = capital_f_.pow(&c__ * (&a__ + &b__ * x_));
            let angle = &d__ + &e__ * x_;
            let denominator = e__.pow(2) * n_.pow(2) + b__.pow(2) * c__.pow(2) * capital_f_.log().pow(2);
            let recursive_integrand = &exponential * angle.sin().pow(&n_ - 2);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let recursive_term = rubi_simp(&(&(&n_ * (&n_ - 1) * e__.pow(2) / &denominator) * &recursive), x_);

            rubi_simp(&(&b__ * &c__ * capital_f_.log() * &exponential * angle.sin().pow(&n_) / &denominator), x_)
                    - rubi_simp(&(&e__ * &n_ * &exponential * angle.cos() * angle.sin().pow(&n_ - 1) / &denominator), x_)
                    + rubi_star(Atom::num(1), recursive_term)
        },
    ));
}

fn push_rules_rule_4935(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_f_, a__, b__, c__, d__, e__, m_, x_);
    rules.push(rubi_rule!(
        order: 4935,
        source: "Int[F_^(c_.*(a_.+b_.*x_))*Cos[d_.+e_.*x_]^m_,x_Symbol] :=
          b*c*Log[F]*F^(c*(a+b*x))*Cos[d+e*x]^m/(e^2*m^2+b^2*c^2*Log[F]^2) +
          e*m*F^(c*(a+b*x))*Sin[d+e*x]*Cos[d+e*x]^(m-1)/(e^2*m^2+b^2*c^2*Log[F]^2) +
          (m*(m-1)*e^2)/(e^2*m^2+b^2*c^2*Log[F]^2) \\[Star] Int[F^(c*(a+b*x))*Cos[d+e*x]^(m-2),x] /;
        FreeQ[{F,a,b,c,d,e},x] && NeQ[e^2*m^2+b^2*c^2*Log[F]^2,0] && GtQ[m,1]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: ["CRC 542, A&S 4.3.138", "CRC 543, A&S 4.3.139"],
        pattern: capital_f_.pow(c__ * (a__ + b__ * x_)) * (d__ + e__ * x_).cos().pow(m_),
        with: [capital_f_, c__, a__, b__, d__, e__, m_, x_],
        optional: [c__, a__, b__, d__, e__],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__], x_)
                && neq!(e__.pow(2) * m_.pow(2) + b__.pow(2) * c__.pow(2) * capital_f_.log().pow(2), 0)
                && gtq!(m_, 1)
        },
        rhs: {
            let exponential = capital_f_.pow(&c__ * (&a__ + &b__ * x_));
            let angle = &d__ + &e__ * x_;
            let denominator = e__.pow(2) * m_.pow(2) + b__.pow(2) * c__.pow(2) * capital_f_.log().pow(2);
            let recursive_integrand = &exponential * angle.cos().pow(&m_ - 2);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let recursive_term = rubi_simp(&(&(&m_ * (&m_ - 1) * e__.pow(2) / &denominator) * &recursive), x_);

            rubi_simp(&(&b__ * &c__ * capital_f_.log() * &exponential * angle.cos().pow(&m_) / &denominator), x_)
                    + rubi_simp(&(&e__ * &m_ * &exponential * angle.sin() * angle.cos().pow(&m_ - 1) / &denominator), x_)
                    + rubi_star(Atom::num(1), recursive_term)
        },
    ));
}

fn push_rules_rule_4936(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, d__, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 4936,
        source: "Int[F_^(c_.*(a_.+b_.*x_))*Sin[d_.+e_.*x_]^n_,x_Symbol] :=
          -b*c*Log[F]*F^(c*(a+b*x))*Sin[d+e*x]^(n+2)/(e^2*(n+1)*(n+2)) +
          F^(c*(a+b*x))*Cos[d+e*x]*Sin[d+e*x]^(n+1)/(e*(n+1)) /;
        FreeQ[{F,a,b,c,d,e,n},x] && EqQ[e^2*(n+2)^2+b^2*c^2*Log[F]^2,0] && NeQ[n,-1] && NeQ[n,-2]",
        desc: "Apply the direct antiderivative formula.",
        refs: ["CRC 551 when e2 (n+2)2+b2c2Log[F]2\\[Equal]0", "CRC 552 when e2 (n+2)2+b2c2Log[F]2\\[Equal]0"],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [capital_f_, c__, a__, b__, d__, e__, n_, x_],
        optional: [c__, a__, b__, d__, e__],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__, n_], x_)
                && eqq!(e__.pow(2) * (&n_ + 2).pow(2) + b__.pow(2) * c__.pow(2) * capital_f_.log().pow(2), 0)
                && neq!(n_, -1)
                && neq!(n_, -2)
        },
        rhs: {
            let exponential = capital_f_.pow(&c__ * (&a__ + &b__ * x_));
            let angle = &d__ + &e__ * x_;

            rubi_simp(&(-&b__ * &c__ * capital_f_.log() * &exponential * angle.sin().pow(&n_ + 2)
                    / (e__.pow(2) * (&n_ + 1) * (&n_ + 2))), x_)
                    + rubi_simp(&(exponential * angle.cos() * angle.sin().pow(&n_ + 1) / (&e__ * (&n_ + 1))), x_)
        },
    ));
}

fn push_rules_rule_4937(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, d__, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 4937,
        source: "Int[F_^(c_.*(a_.+b_.*x_))*Cos[d_.+e_.*x_]^n_,x_Symbol] :=
          -b*c*Log[F]*F^(c*(a+b*x))*Cos[d+e*x]^(n+2)/(e^2*(n+1)*(n+2)) -
          F^(c*(a+b*x))*Sin[d+e*x]*Cos[d+e*x]^(n+1)/(e*(n+1)) /;
        FreeQ[{F,a,b,c,d,e,n},x] && EqQ[e^2*(n+2)^2+b^2*c^2*Log[F]^2,0] && NeQ[n,-1] && NeQ[n,-2]",
        desc: "Apply the direct antiderivative formula.",
        refs: ["CRC 551 when e2 (n+2)2+b2c2Log[F]2\\[Equal]0", "CRC 552 when e2 (n+2)2+b2c2Log[F]2\\[Equal]0"],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [capital_f_, c__, a__, b__, d__, e__, n_, x_],
        optional: [c__, a__, b__, d__, e__],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__, n_], x_)
                && eqq!(e__.pow(2) * (&n_ + 2).pow(2) + b__.pow(2) * c__.pow(2) * capital_f_.log().pow(2), 0)
                && neq!(n_, -1)
                && neq!(n_, -2)
        },
        rhs: {
            let exponential = capital_f_.pow(&c__ * (&a__ + &b__ * x_));
            let angle = &d__ + &e__ * x_;

            rubi_simp(&(-&b__ * &c__ * capital_f_.log() * &exponential * angle.cos().pow(&n_ + 2)
                    / (e__.pow(2) * (&n_ + 1) * (&n_ + 2))), x_)
                    - rubi_simp(&(exponential * angle.sin() * angle.cos().pow(&n_ + 1) / (&e__ * (&n_ + 1))), x_)
        },
    ));
}

fn push_rules_rule_4938(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, d__, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 4938,
        source: "Int[F_^(c_.*(a_.+b_.*x_))*Sin[d_.+e_.*x_]^n_,x_Symbol] :=
          -b*c*Log[F]*F^(c*(a+b*x))*Sin[d+e*x]^(n+2)/(e^2*(n+1)*(n+2)) +
          F^(c*(a+b*x))*Cos[d+e*x]*Sin[d+e*x]^(n+1)/(e*(n+1)) +
          (e^2*(n+2)^2+b^2*c^2*Log[F]^2)/(e^2*(n+1)*(n+2)) \\[Star] Int[F^(c*(a+b*x))*Sin[d+e*x]^(n+2),x] /;
        FreeQ[{F,a,b,c,d,e},x] && NeQ[e^2*(n+2)^2+b^2*c^2*Log[F]^2,0] && LtQ[n,-1] && NeQ[n,-2]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: ["CRC 551, CRC 542 inverted", "CRC 552, CRC 543 inverted"],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [capital_f_, c__, a__, b__, d__, e__, n_, x_],
        optional: [c__, a__, b__, d__, e__],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__], x_)
                && neq!(e__.pow(2) * (&n_ + 2).pow(2) + b__.pow(2) * c__.pow(2) * capital_f_.log().pow(2), 0)
                && ltq!(n_, -1)
                && neq!(n_, -2)
        },
        rhs: {
            let exponential = capital_f_.pow(&c__ * (&a__ + &b__ * x_));
            let angle = &d__ + &e__ * x_;
            let denominator = e__.pow(2) * (&n_ + 1) * (&n_ + 2);
            let balance = e__.pow(2) * (&n_ + 2).pow(2) + b__.pow(2) * c__.pow(2) * capital_f_.log().pow(2);
            let recursive_integrand = &exponential * angle.sin().pow(&n_ + 2);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let recursive_term = rubi_simp(&(&(&balance / &denominator) * &recursive), x_);

            rubi_simp(&(-&b__ * &c__ * capital_f_.log() * &exponential * angle.sin().pow(&n_ + 2) / &denominator), x_)
                    + rubi_simp(&(&exponential * angle.cos() * angle.sin().pow(&n_ + 1) / (&e__ * (&n_ + 1))), x_)
                    + rubi_star(Atom::num(1), recursive_term)
        },
    ));
}

fn push_rules_rule_4939(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, d__, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 4939,
        source: "Int[F_^(c_.*(a_.+b_.*x_))*Cos[d_.+e_.*x_]^n_,x_Symbol] :=
          -b*c*Log[F]*F^(c*(a+b*x))*Cos[d+e*x]^(n+2)/(e^2*(n+1)*(n+2)) -
          F^(c*(a+b*x))*Sin[d+e*x]*Cos[d+e*x]^(n+1)/(e*(n+1)) +
          (e^2*(n+2)^2+b^2*c^2*Log[F]^2)/(e^2*(n+1)*(n+2)) \\[Star] Int[F^(c*(a+b*x))*Cos[d+e*x]^(n+2),x] /;
        FreeQ[{F,a,b,c,d,e},x] && NeQ[e^2*(n+2)^2+b^2*c^2*Log[F]^2,0] && LtQ[n,-1] && NeQ[n,-2]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: ["CRC 551, CRC 542 inverted", "CRC 552, CRC 543 inverted"],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [capital_f_, c__, a__, b__, d__, e__, n_, x_],
        optional: [c__, a__, b__, d__, e__],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__], x_)
                && neq!(e__.pow(2) * (&n_ + 2).pow(2) + b__.pow(2) * c__.pow(2) * capital_f_.log().pow(2), 0)
                && ltq!(n_, -1)
                && neq!(n_, -2)
        },
        rhs: {
            let exponential = capital_f_.pow(&c__ * (&a__ + &b__ * x_));
            let angle = &d__ + &e__ * x_;
            let denominator = e__.pow(2) * (&n_ + 1) * (&n_ + 2);
            let balance = e__.pow(2) * (&n_ + 2).pow(2) + b__.pow(2) * c__.pow(2) * capital_f_.log().pow(2);
            let recursive_integrand = &exponential * angle.cos().pow(&n_ + 2);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let recursive_term = rubi_simp(&(&(&balance / &denominator) * &recursive), x_);

            rubi_simp(&(-&b__ * &c__ * capital_f_.log() * &exponential * angle.cos().pow(&n_ + 2) / &denominator), x_)
                    - rubi_simp(&(&exponential * angle.sin() * angle.cos().pow(&n_ + 1) / (&e__ * (&n_ + 1))), x_)
                    + rubi_star(Atom::num(1), recursive_term)
        },
    ));
}

fn push_rules_rule_4940(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, d__, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 4940,
        source: "Int[F_^(c_.*(a_.+b_.*x_))*Sin[d_.+e_.*x_]^n_,x_Symbol] :=
          E^(I*n*(d+e*x))*Sin[d+e*x]^n/(-1+E^(2*I*(d+e*x)))^n \\[Star] Int[F^(c*(a+b*x))*(-1+E^(2*I*(d+e*x)))^n/E^(I*n*(d+e*x)),x] /;
        FreeQ[{F,a,b,c,d,e,n},x] && Not[IntegerQ[n]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [capital_f_, c__, a__, b__, d__, e__, n_, x_],
        optional: [c__, a__, b__, d__, e__],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__, n_], x_)
                && !integerq!(n_)
        },
        rhs: {
            let i = Atom::i();
            let exponential = capital_f_.pow(&c__ * (&a__ + &b__ * x_));
            let angle = &d__ + &e__ * x_;
            let exp_i_n_angle = (&i * &n_ * &angle).exp();
            let exp_2_i_angle = (Atom::num(2) * &i * &angle).exp();
            let transformed_integrand = exponential * (-Atom::num(1) + &exp_2_i_angle).pow(&n_) / &exp_i_n_angle;
            let recursive = rubi_rhs_int(&transformed_integrand, x_);
            let coefficient = exp_i_n_angle * angle.sin().pow(&n_)
                / (-Atom::num(1) + exp_2_i_angle).pow(&n_);

            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_4941(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, d__, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 4941,
        source: "Int[F_^(c_.*(a_.+b_.*x_))*Cos[d_.+e_.*x_]^n_,x_Symbol] :=
          E^(I*n*(d+e*x))*Cos[d+e*x]^n/(1+E^(2*I*(d+e*x)))^n \\[Star] Int[F^(c*(a+b*x))*(1+E^(2*I*(d+e*x)))^n/E^(I*n*(d+e*x)),x] /;
        FreeQ[{F,a,b,c,d,e,n},x] && Not[IntegerQ[n]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [capital_f_, c__, a__, b__, d__, e__, n_, x_],
        optional: [c__, a__, b__, d__, e__],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__, n_], x_)
                && !integerq!(n_)
        },
        rhs: {
            let i = Atom::i();
            let exponential = capital_f_.pow(&c__ * (&a__ + &b__ * x_));
            let angle = &d__ + &e__ * x_;
            let exp_i_n_angle = (&i * &n_ * &angle).exp();
            let exp_2_i_angle = (Atom::num(2) * &i * &angle).exp();
            let transformed_integrand = exponential * (Atom::num(1) + &exp_2_i_angle).pow(&n_) / &exp_i_n_angle;
            let recursive = rubi_rhs_int(&transformed_integrand, x_);
            let coefficient =
                exp_i_n_angle * angle.cos().pow(&n_) / (Atom::num(1) + exp_2_i_angle).pow(&n_);

            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_4942(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_f_, a__, b__, c__, d__, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 4942,
        source: "Int[F_^(c_.*(a_.+b_.*x_))*Tan[d_.+e_.*x_]^n_.,x_Symbol] :=
          I^n \\[Star] Int[ExpandIntegrand[F^(c*(a+b*x))*(1-E^(2*I*(d+e*x)))^n/(1+E^(2*I*(d+e*x)))^n,x],x] /;
        FreeQ[{F,a,b,c,d,e},x] && IntegerQ[n]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: capital_f_.pow(c__ * (a__ + b__ * x_)) * (d__ + e__ * x_).tan().pow(n_),
        with: [capital_f_, c__, a__, b__, d__, e__, n_, x_],
        optional: [c__, a__, b__, d__, e__, n_],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__], x_)
                && integerq!(n_)
        },
        rhs: {
            let i = Atom::i();
            let exponential = capital_f_.pow(&c__ * (&a__ + &b__ * x_));
            let angle = &d__ + &e__ * x_;
            let exp_2_i_angle = (Atom::num(2) * &i * &angle).exp();
            let transformed_integrand =
                exponential * (Atom::num(1) - &exp_2_i_angle).pow(&n_) / (Atom::num(1) + &exp_2_i_angle).pow(&n_);
            let expanded = rubi_expand_integrand(&transformed_integrand, x_);
            let recursive = rubi_rhs_int(&expanded, x_);

            rubi_star(i.pow(&n_), recursive)
        },
    ));
}

fn push_rules_rule_4943(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_f_, a__, b__, c__, d__, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 4943,
        source: "Int[F_^(c_.*(a_.+b_.*x_))*Cot[d_.+e_.*x_]^n_.,x_Symbol] :=
          (-I)^n \\[Star] Int[ExpandIntegrand[F^(c*(a+b*x))*(1+E^(2*I*(d+e*x)))^n/(1-E^(2*I*(d+e*x)))^n,x],x] /;
        FreeQ[{F,a,b,c,d,e},x] && IntegerQ[n]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: capital_f_.pow(c__ * (a__ + b__ * x_)) * (d__ + e__ * x_).cot().pow(n_),
        with: [capital_f_, c__, a__, b__, d__, e__, n_, x_],
        optional: [c__, a__, b__, d__, e__, n_],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__], x_)
                && integerq!(n_)
        },
        rhs: {
            let i = Atom::i();
            let exponential = capital_f_.pow(&c__ * (&a__ + &b__ * x_));
            let angle = &d__ + &e__ * x_;
            let exp_2_i_angle = (Atom::num(2) * &i * &angle).exp();
            let transformed_integrand =
                exponential * (Atom::num(1) + &exp_2_i_angle).pow(&n_) / (Atom::num(1) - &exp_2_i_angle).pow(&n_);
            let expanded = rubi_expand_integrand(&transformed_integrand, x_);
            let recursive = rubi_rhs_int(&expanded, x_);

            rubi_star((-i).pow(&n_), recursive)
        },
    ));
}

fn push_rules_rule_4944(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, d__, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 4944,
        source: "Int[F_^(c_.*(a_.+b_.*x_))*Sec[d_.+e_.*x_]^n_,x_Symbol] :=
          b*c*Log[F]*F^(c*(a+b*x))*(Sec[d+e x]^n/(e^2*n^2+b^2*c^2*Log[F]^2)) -
          e*n*F^(c*(a+b*x))*Sec[d+e x]^(n+1)*(Sin[d+e x]/(e^2*n^2+b^2*c^2*Log[F]^2)) +
          e^2*n*((n+1)/(e^2*n^2+b^2*c^2*Log[F]^2)) \\[Star] Int[F^(c*(a+b*x))*Sec[d+e x]^(n+2),x] /;
        FreeQ[{F,a,b,c,d,e},x] && NeQ[e^2*n^2+b^2*c^2*Log[F]^2,0] && LtQ[n,-1]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [capital_f_, c__, a__, b__, d__, e__, n_, x_],
        optional: [c__, a__, b__, d__, e__],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__], x_)
                && neq!(e__.pow(2) * n_.pow(2) + b__.pow(2) * c__.pow(2) * capital_f_.log().pow(2), 0)
                && ltq!(n_, -1)
        },
        rhs: {
            let exponential = capital_f_.pow(&c__ * (&a__ + &b__ * x_));
            let angle = &d__ + &e__ * x_;
            let denominator = e__.pow(2) * n_.pow(2) + b__.pow(2) * c__.pow(2) * capital_f_.log().pow(2);
            let recursive_integrand = &exponential * angle.sec().pow(&n_ + 2);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let recursive_term = rubi_simp(&(&(e__.pow(2) * &n_ * (&n_ + 1) / &denominator) * &recursive), x_);

            rubi_simp(&(&b__ * &c__ * capital_f_.log() * &exponential * angle.sec().pow(&n_) / &denominator), x_)
                    - rubi_simp(&(&e__ * &n_ * &exponential * angle.sec().pow(&n_ + 1) * angle.sin() / &denominator), x_)
                    + rubi_star(Atom::num(1), recursive_term)
        },
    ));
}

fn push_rules_rule_4945(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, d__, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 4945,
        source: "Int[F_^(c_.*(a_.+b_.*x_))*Csc[d_.+e_.*x_]^n_,x_Symbol] :=
          b*c*Log[F]*F^(c*(a+b*x))*(Csc[d+e x]^n/(e^2*n^2+b^2*c^2*Log[F]^2)) +
          e*n*F^(c*(a+b*x))*Csc[d+e x]^(n+1)*(Cos[d+e x]/(e^2*n^2+b^2*c^2*Log[F]^2)) +
          e^2*n*((n+1)/(e^2*n^2+b^2*c^2*Log[F]^2)) \\[Star] Int[F^(c*(a+b*x))*Csc[d+e x]^(n+2),x] /;
        FreeQ[{F,a,b,c,d,e},x] && NeQ[e^2*n^2+b^2*c^2*Log[F]^2,0] && LtQ[n,-1]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [capital_f_, c__, a__, b__, d__, e__, n_, x_],
        optional: [c__, a__, b__, d__, e__],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__], x_)
                && neq!(e__.pow(2) * n_.pow(2) + b__.pow(2) * c__.pow(2) * capital_f_.log().pow(2), 0)
                && ltq!(n_, -1)
        },
        rhs: {
            let exponential = capital_f_.pow(&c__ * (&a__ + &b__ * x_));
            let angle = &d__ + &e__ * x_;
            let denominator = e__.pow(2) * n_.pow(2) + b__.pow(2) * c__.pow(2) * capital_f_.log().pow(2);
            let recursive_integrand = &exponential * angle.csc().pow(&n_ + 2);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let recursive_term = rubi_simp(&(&(e__.pow(2) * &n_ * (&n_ + 1) / &denominator) * &recursive), x_);

            rubi_simp(&(&b__ * &c__ * capital_f_.log() * &exponential * angle.csc().pow(&n_) / &denominator), x_)
                    + rubi_simp(&(&e__ * &n_ * &exponential * angle.csc().pow(&n_ + 1) * angle.cos() / &denominator), x_)
                    + rubi_star(Atom::num(1), recursive_term)
        },
    ));
}

fn push_rules_rule_4946(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, d__, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 4946,
        source: "Int[F_^(c_.*(a_.+b_.*x_))*Sec[d_.+e_.*x_]^n_,x_Symbol] :=
          -b*c*Log[F]*F^(c*(a+b*x))*Sec[d+e x]^(n-2)/(e^2*(n-1)*(n-2)) +
          F^(c*(a+b*x))*Sec[d+e x]^(n-1)*Sin[d+e x]/(e*(n-1)) /;
        FreeQ[{F,a,b,c,d,e,n},x] && EqQ[b^2*c^2*Log[F]^2+e^2*(n-2)^2,0] && NeQ[n,1] && NeQ[n,2]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [capital_f_, c__, a__, b__, d__, e__, n_, x_],
        optional: [c__, a__, b__, d__, e__],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__, n_], x_)
                && eqq!(b__.pow(2) * c__.pow(2) * capital_f_.log().pow(2) + e__.pow(2) * (&n_ - 2).pow(2), 0)
                && neq!(n_, 1)
                && neq!(n_, 2)
        },
        rhs: {
            let exponential = capital_f_.pow(&c__ * (&a__ + &b__ * x_));
            let angle = &d__ + &e__ * x_;

            rubi_simp(&(-&b__ * &c__ * capital_f_.log() * &exponential * angle.sec().pow(&n_ - 2)
                    / (e__.pow(2) * (&n_ - 1) * (&n_ - 2))), x_)
                    + rubi_simp(&(exponential * angle.sec().pow(&n_ - 1) * angle.sin() / (&e__ * (&n_ - 1))), x_)
        },
    ));
}

fn push_rules_rule_4947(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, d__, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 4947,
        source: "Int[F_^(c_.*(a_.+b_.*x_))*Csc[d_.+e_.*x_]^n_,x_Symbol] :=
          -b*c*Log[F]*F^(c*(a+b*x))*Csc[d+e x]^(n-2)/(e^2*(n-1)*(n-2)) +
          F^(c*(a+b*x))*Csc[d+e x]^(n-1)*Cos[d+e x]/(e*(n-1)) /;
        FreeQ[{F,a,b,c,d,e,n},x] && EqQ[b^2*c^2*Log[F]^2+e^2*(n-2)^2,0] && NeQ[n,1] && NeQ[n,2]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [capital_f_, c__, a__, b__, d__, e__, n_, x_],
        optional: [c__, a__, b__, d__, e__],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__, n_], x_)
                && eqq!(b__.pow(2) * c__.pow(2) * capital_f_.log().pow(2) + e__.pow(2) * (&n_ - 2).pow(2), 0)
                && neq!(n_, 1)
                && neq!(n_, 2)
        },
        rhs: {
            let exponential = capital_f_.pow(&c__ * (&a__ + &b__ * x_));
            let angle = &d__ + &e__ * x_;

            rubi_simp(&(-&b__ * &c__ * capital_f_.log() * &exponential * angle.csc().pow(&n_ - 2)
                    / (e__.pow(2) * (&n_ - 1) * (&n_ - 2))), x_)
                    + rubi_simp(&(exponential * angle.csc().pow(&n_ - 1) * angle.cos() / (&e__ * (&n_ - 1))), x_)
        },
    ));
}

fn push_rules_rule_4948(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, d__, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 4948,
        source: "Int[F_^(c_.*(a_.+b_.*x_))*Sec[d_.+e_.*x_]^n_,x_Symbol] :=
          -b*c*Log[F]*F^(c*(a+b*x))*Sec[d+e x]^(n-2)/(e^2*(n-1)*(n-2)) +
          F^(c*(a+b*x))*Sec[d+e x]^(n-1)*Sin[d+e x]/(e*(n-1)) +
          (e^2*(n-2)^2+b^2*c^2*Log[F]^2)/(e^2*(n-1)*(n-2)) \\[Star] Int[F^(c*(a+b*x))*Sec[d+e x]^(n-2),x] /;
        FreeQ[{F,a,b,c,d,e},x] && NeQ[b^2*c^2*Log[F]^2+e^2*(n-2)^2,0] && GtQ[n,1] && NeQ[n,2]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [capital_f_, c__, a__, b__, d__, e__, n_, x_],
        optional: [c__, a__, b__, d__, e__],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__], x_)
                && neq!(b__.pow(2) * c__.pow(2) * capital_f_.log().pow(2) + e__.pow(2) * (&n_ - 2).pow(2), 0)
                && gtq!(n_, 1)
                && neq!(n_, 2)
        },
        rhs: {
            let exponential = capital_f_.pow(&c__ * (&a__ + &b__ * x_));
            let angle = &d__ + &e__ * x_;
            let denominator = e__.pow(2) * (&n_ - 1) * (&n_ - 2);
            let balance = e__.pow(2) * (&n_ - 2).pow(2) + b__.pow(2) * c__.pow(2) * capital_f_.log().pow(2);
            let recursive_integrand = &exponential * angle.sec().pow(&n_ - 2);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let recursive_term = rubi_simp(&(&(&balance / &denominator) * &recursive), x_);

            rubi_simp(&(-&b__ * &c__ * capital_f_.log() * &exponential * angle.sec().pow(&n_ - 2) / &denominator), x_)
                    + rubi_simp(&(&exponential * angle.sec().pow(&n_ - 1) * angle.sin() / (&e__ * (&n_ - 1))), x_)
                    + rubi_star(Atom::num(1), recursive_term)
        },
    ));
}

fn push_rules_rule_4949(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, d__, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 4949,
        source: "Int[F_^(c_.*(a_.+b_.*x_))*Csc[d_.+e_.*x_]^n_,x_Symbol] :=
          -b*c*Log[F]*F^(c*(a+b*x))*Csc[d+e x]^(n-2)/(e^2*(n-1)*(n-2)) -
          F^(c*(a+b*x))*Csc[d+e x]^(n-1)*Cos[d+e x]/(e*(n-1)) +
          (e^2*(n-2)^2+b^2*c^2*Log[F]^2)/(e^2*(n-1)*(n-2)) \\[Star] Int[F^(c*(a+b*x))*Csc[d+e x]^(n-2),x] /;
        FreeQ[{F,a,b,c,d,e},x] && NeQ[b^2*c^2*Log[F]^2+e^2*(n-2)^2,0] && GtQ[n,1] && NeQ[n,2]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [capital_f_, c__, a__, b__, d__, e__, n_, x_],
        optional: [c__, a__, b__, d__, e__],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__], x_)
                && neq!(b__.pow(2) * c__.pow(2) * capital_f_.log().pow(2) + e__.pow(2) * (&n_ - 2).pow(2), 0)
                && gtq!(n_, 1)
                && neq!(n_, 2)
        },
        rhs: {
            let exponential = capital_f_.pow(&c__ * (&a__ + &b__ * x_));
            let angle = &d__ + &e__ * x_;
            let denominator = e__.pow(2) * (&n_ - 1) * (&n_ - 2);
            let balance = e__.pow(2) * (&n_ - 2).pow(2) + b__.pow(2) * c__.pow(2) * capital_f_.log().pow(2);
            let recursive_integrand = &exponential * angle.csc().pow(&n_ - 2);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let recursive_term = rubi_simp(&(&(&balance / &denominator) * &recursive), x_);

            rubi_simp(&(-&b__ * &c__ * capital_f_.log() * &exponential * angle.csc().pow(&n_ - 2) / &denominator), x_)
                    - rubi_simp(&(&exponential * angle.csc().pow(&n_ - 1) * angle.cos() / (&e__ * (&n_ - 1))), x_)
                    + rubi_star(Atom::num(1), recursive_term)
        },
    ));
}

fn push_rules_rule_4950(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_f_, a__, b__, c__, d__, e__, k__, n_, x_);
    rules.push(rubi_rule!(
        order: 4950,
        source: "Int[F_^(c_.*(a_.+b_.*x_))*Sec[d_.+k_.*Pi+e_.*x_]^n_.,x_Symbol] :=
          2^n*E^(I*k*n*Pi)*E^(I*n*(d+e*x))*F^(c*(a+b*x))/(I*e*n+b*c*Log[F])*
            Hypergeometric2F1[n,n/2-I*b*c*Log[F]/(2*e),1+n/2-I*b*c*Log[F]/(2*e),-E^(2*I*k*Pi)*E^(2*I*(d+e*x))] /;
        FreeQ[{F,a,b,c,d,e},x] && IntegerQ[4*k] && IntegerQ[n]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: capital_f_.pow(c__ * (a__ + b__ * x_)) * (d__ + k__ * Atom::var(Symbol::PI) + e__ * x_).sec().pow(n_),
        with: [capital_f_, c__, a__, b__, d__, k__, e__, n_, x_],
        optional: [c__, a__, b__, d__, k__, e__, n_],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__], x_)
                && integerq!(Atom::num(4) * &k__)
                && integerq!(n_)
        },
        rhs: {
            let i = Atom::i();
            let angle = &d__ + &e__ * x_;
            let exponential = capital_f_.pow(&c__ * (&a__ + &b__ * x_));
            let denominator = &i * &e__ * &n_ + &b__ * &c__ * capital_f_.log();
            let a1 = &n_;
            let a2 = &n_ / 2 - &i * &b__ * &c__ * capital_f_.log() / (Atom::num(2) * &e__);
            let a3 = Atom::num(1) + &a2;
            let z = -rubi_exp_two_i_pi_multiple(&k__)
                * (Atom::num(2) * &i * &angle).exp();

            rubi_simp(&(Atom::num(2).pow(&n_)
                    * (&i * &k__ * &n_ * Atom::var(Symbol::PI)).exp()
                    * (&i * &n_ * &angle).exp()
                    * exponential
                    * rubi_hypergeometric2f1(a1, a2, a3, z)
                    / denominator), x_)
        },
    ));
}

fn push_rules_rule_4951(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, d__, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 4951,
        source: "Int[F_^(c_.*(a_.+b_.*x_))*Sec[d_.+e_.*x_]^n_.,x_Symbol] :=
          2^n*E^(I*n*(d+e*x))*F^(c*(a+b*x))/(I*e*n+b*c*Log[F])*
            Hypergeometric2F1[n,n/2-I*b*c*Log[F]/(2*e),1+n/2-I*b*c*Log[F]/(2*e),-E^(2*I*(d+e*x))] /;
        FreeQ[{F,a,b,c,d,e},x] && IntegerQ[n]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [capital_f_, c__, a__, b__, d__, e__, n_, x_],
        optional: [c__, a__, b__, d__, e__, n_],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__], x_)
                && integerq!(n_)
        },
        rhs: {
            let i = Atom::i();
            let angle = &d__ + &e__ * x_;
            let exponential = capital_f_.pow(&c__ * (&a__ + &b__ * x_));
            let denominator = &i * &e__ * &n_ + &b__ * &c__ * capital_f_.log();
            let a1 = &n_;
            let a2 = &n_ / 2 - &i * &b__ * &c__ * capital_f_.log() / (Atom::num(2) * &e__);
            let a3 = Atom::num(1) + &a2;
            let z = -(Atom::num(2) * &i * &angle).exp();

            rubi_simp(&(Atom::num(2).pow(&n_)
                    * (&i * &n_ * &angle).exp()
                    * exponential
                    * rubi_hypergeometric2f1(a1, a2, a3, z)
                    / denominator), x_)
        },
    ));
}

fn push_rules_rule_4952(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_f_, a__, b__, c__, d__, e__, k__, n_, x_);
    rules.push(rubi_rule!(
        order: 4952,
        source: "Int[F_^(c_.*(a_.+b_.*x_))*Csc[d_.+k_.*Pi+e_.*x_]^n_.,x_Symbol] :=
          (-2*I)^n*E^(I*k*n*Pi)*E^(I*n*(d+e*x))*(F^(c*(a+b*x))/(I*e*n+b*c*Log[F]))*
            Hypergeometric2F1[n,n/2-I*b*c*Log[F]/(2*e),1+n/2-I*b*c*Log[F]/(2*e),E^(2*I*k*Pi)*E^(2*I*(d+e*x))] /;
        FreeQ[{F,a,b,c,d,e},x] && IntegerQ[4*k] && IntegerQ[n]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: capital_f_.pow(c__ * (a__ + b__ * x_)) * (d__ + k__ * Atom::var(Symbol::PI) + e__ * x_).csc().pow(n_),
        with: [capital_f_, c__, a__, b__, d__, k__, e__, n_, x_],
        optional: [c__, a__, b__, d__, k__, e__, n_],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__], x_)
                && integerq!(Atom::num(4) * &k__)
                && integerq!(n_)
        },
        rhs: {
            let i = Atom::i();
            let angle = &d__ + &e__ * x_;
            let exponential = capital_f_.pow(&c__ * (&a__ + &b__ * x_));
            let denominator = &i * &e__ * &n_ + &b__ * &c__ * capital_f_.log();
            let a1 = &n_;
            let a2 = &n_ / 2 - &i * &b__ * &c__ * capital_f_.log() / (Atom::num(2) * &e__);
            let a3 = Atom::num(1) + &a2;
            let z = rubi_exp_two_i_pi_multiple(&k__)
                * (Atom::num(2) * &i * &angle).exp();

            rubi_simp(&((-Atom::num(2) * &i).pow(&n_)
                    * (&i * &k__ * &n_ * Atom::var(Symbol::PI)).exp()
                    * (&i * &n_ * &angle).exp()
                    * exponential
                    * rubi_hypergeometric2f1(a1, a2, a3, z)
                    / denominator), x_)
        },
    ));
}

fn push_rules_rule_4953(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, d__, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 4953,
        source: "Int[F_^(c_.*(a_.+b_.*x_))*Csc[d_.+e_.*x_]^n_.,x_Symbol] :=
          (-2*I)^n*E^(I*n*(d+e*x))*(F^(c*(a+b*x))/(I*e*n+b*c*Log[F]))*
            Hypergeometric2F1[n,n/2-I*b*c*Log[F]/(2*e),1+n/2-I*b*c*Log[F]/(2*e),E^(2*I*(d+e*x))] /;
        FreeQ[{F,a,b,c,d,e},x] && IntegerQ[n]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [capital_f_, c__, a__, b__, d__, e__, n_, x_],
        optional: [c__, a__, b__, d__, e__, n_],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__], x_)
                && integerq!(n_)
        },
        rhs: {
            let i = Atom::i();
            let angle = &d__ + &e__ * x_;
            let exponential = capital_f_.pow(&c__ * (&a__ + &b__ * x_));
            let denominator = &i * &e__ * &n_ + &b__ * &c__ * capital_f_.log();
            let a1 = &n_;
            let a2 = &n_ / 2 - &i * &b__ * &c__ * capital_f_.log() / (Atom::num(2) * &e__);
            let a3 = Atom::num(1) + &a2;
            let z = (Atom::num(2) * &i * &angle).exp();

            rubi_simp(&((-Atom::num(2) * &i).pow(&n_)
                    * (&i * &n_ * &angle).exp()
                    * exponential
                    * rubi_hypergeometric2f1(a1, a2, a3, z)
                    / denominator), x_)
        },
    ));
}

fn push_rules_rule_4954(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, d__, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 4954,
        source: "Int[F_^(c_.*(a_.+b_.*x_))*Sec[d_.+e_.*x_]^n_.,x_Symbol] :=
          (1+E^(2*I*(d+e*x)))^n*Sec[d+e*x]^n/E^(I*n*(d+e*x)) \\[Star] Int[SimplifyIntegrand[F^(c*(a+b*x))*E^(I*n*(d+e*x))/(1+E^(2*I*(d+e*x)))^n,x],x] /;
        FreeQ[{F,a,b,c,d,e},x] && Not[IntegerQ[n]]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [capital_f_, c__, a__, b__, d__, e__, n_, x_],
        optional: [c__, a__, b__, d__, e__, n_],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__], x_)
                && !integerq!(n_)
        },
        rhs: {
            let i = Atom::i();
            let angle = &d__ + &e__ * x_;
            let exponential = capital_f_.pow(&c__ * (&a__ + &b__ * x_));
            let exp_i_n_angle = (&i * &n_ * &angle).exp();
            let exp_2_i_angle = (Atom::num(2) * &i * &angle).exp();
            let transformed = rubi_simplify_integrand(
                &(exponential * &exp_i_n_angle / (Atom::num(1) + &exp_2_i_angle).pow(&n_)),
                x_,
            );
            let recursive = rubi_rhs_int(&transformed, x_);
            let coefficient =
                (Atom::num(1) + exp_2_i_angle).pow(&n_) * angle.sec().pow(&n_) / exp_i_n_angle;

            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_4955(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, d__, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 4955,
        source: "Int[F_^(c_.*(a_.+b_.*x_))*Csc[d_.+e_.*x_]^n_.,x_Symbol] :=
          (1-E^(-2*I*(d+e*x)))^n*Csc[d+e*x]^n/E^(-I*n*(d+e*x)) \\[Star] Int[SimplifyIntegrand[F^(c*(a+b*x))*E^(-I*n*(d+e*x))/(1-E^(-2*I*(d+e*x)))^n,x],x] /;
        FreeQ[{F,a,b,c,d,e},x] && Not[IntegerQ[n]]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [capital_f_, c__, a__, b__, d__, e__, n_, x_],
        optional: [c__, a__, b__, d__, e__, n_],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__], x_)
                && !integerq!(n_)
        },
        rhs: {
            let i = Atom::i();
            let angle = &d__ + &e__ * x_;
            let exponential = capital_f_.pow(&c__ * (&a__ + &b__ * x_));
            let exp_minus_i_n_angle = (-&i * &n_ * &angle).exp();
            let exp_minus_2_i_angle = (-Atom::num(2) * &i * &angle).exp();
            let transformed = rubi_simplify_integrand(
                &(exponential * &exp_minus_i_n_angle / (Atom::num(1) - &exp_minus_2_i_angle).pow(&n_)),
                x_,
            );
            let recursive = rubi_rhs_int(&transformed, x_);
            let coefficient = (Atom::num(1) - exp_minus_2_i_angle).pow(&n_)
                * angle.csc().pow(&n_)
                / exp_minus_i_n_angle;

            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_4956(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, d__, e__, f__, g__, n_, x_);
    rules.push(rubi_rule!(
        order: 4956,
        source: "Int[F_^(c_.*(a_.+b_.*x_))*(f_+g_.*Sin[d_.+e_.*x_])^n_.,x_Symbol] :=
          2^n*f^n \\[Star] Int[F^(c*(a+b*x))*Cos[d/2-f*Pi/(4*g)+e*x/2]^(2*n),x] /;
        FreeQ[{F,a,b,c,d,e,f,g},x] && EqQ[f^2-g^2,0] && ILtQ[n,0]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [capital_f_, c__, a__, b__, f__, g__, d__, e__, n_, x_],
        optional: [c__, a__, b__, g__, d__, e__, n_],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__, f__, g__], x_)
                && eqq!(f__.pow(2) - g__.pow(2), 0)
                && iltq!(n_, 0)
        },
        rhs: {
            let exponential = capital_f_.pow(&c__ * (&a__ + &b__ * x_));
            let transformed_angle =
                &d__ / 2 + &e__ * x_ / 2 - &f__ * Atom::var(Symbol::PI) / (Atom::num(4) * &g__);
            let recursive_integrand = exponential * transformed_angle.cos().pow(Atom::num(2) * &n_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            let coefficient = Atom::num(2).pow(&n_) * f__.pow(&n_);

            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_4957(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, d__, e__, f__, g__, n_, x_);
    rules.push(rubi_rule!(
        order: 4957,
        source: "Int[F_^(c_.*(a_.+b_.*x_))*(f_+g_.*Cos[d_.+e_.*x_])^n_.,x_Symbol] :=
          2^n*f^n \\[Star] Int[F^(c*(a+b*x))*Cos[d/2+e*x/2]^(2*n),x] /;
        FreeQ[{F,a,b,c,d,e,f,g},x] && EqQ[f-g,0] && ILtQ[n,0]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [capital_f_, c__, a__, b__, f__, g__, d__, e__, n_, x_],
        optional: [c__, a__, b__, g__, d__, e__, n_],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__, f__, g__], x_)
                && eqq!(&f__ - &g__, 0)
                && iltq!(n_, 0)
        },
        rhs: {
            let exponential = capital_f_.pow(&c__ * (&a__ + &b__ * x_));
            let transformed_angle = &d__ / 2 + &e__ * x_ / 2;
            let recursive_integrand = exponential * transformed_angle.cos().pow(Atom::num(2) * &n_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            let coefficient = Atom::num(2).pow(&n_) * f__.pow(&n_);

            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_4958(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, d__, e__, f__, g__, n_, x_);
    rules.push(rubi_rule!(
        order: 4958,
        source: "Int[F_^(c_.*(a_.+b_.*x_))*(f_+g_.*Cos[d_.+e_.*x_])^n_.,x_Symbol] :=
          2^n*f^n \\[Star] Int[F^(c*(a+b*x))*Sin[d/2+e*x/2]^(2*n),x] /;
        FreeQ[{F,a,b,c,d,e,f,g},x] && EqQ[f+g,0] && ILtQ[n,0]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [capital_f_, c__, a__, b__, f__, g__, d__, e__, n_, x_],
        optional: [c__, a__, b__, g__, d__, e__, n_],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__, f__, g__], x_)
                && eqq!(&f__ + &g__, 0)
                && iltq!(n_, 0)
        },
        rhs: {
            let exponential = capital_f_.pow(&c__ * (&a__ + &b__ * x_));
            let transformed_angle = &d__ / 2 + &e__ * x_ / 2;
            let recursive_integrand = exponential * transformed_angle.sin().pow(Atom::num(2) * &n_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            let coefficient = Atom::num(2).pow(&n_) * f__.pow(&n_);

            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_4959(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, d__, e__, f__, g__, n_, x_);
    rules.push(rubi_rule!(
        order: 4959,
        source: "Int[F_^(c_.*(a_.+b_.*x_))*(f_+g_.*Sin[d_.+e_.*x_])^n_.,x_Symbol] :=
          (f+g*Sin[d+e*x])^n/Cos[d/2-f*Pi/(4*g)+e*x/2]^(2*n) \\[Star] Int[F^(c*(a+b*x))*Cos[d/2-f*Pi/(4*g)+e*x/2]^(2*n),x] /;
        FreeQ[{F,a,b,c,d,e,f,g,n},x] && EqQ[f^2-g^2,0] && Not[IntegerQ[n]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [capital_f_, c__, a__, b__, f__, g__, d__, e__, n_, x_],
        optional: [c__, a__, b__, g__, d__, e__, n_],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__, f__, g__, n_], x_)
                && eqq!(f__.pow(2) - g__.pow(2), 0)
                && !integerq!(n_)
        },
        rhs: {
            let exponential = capital_f_.pow(&c__ * (&a__ + &b__ * x_));
            let angle = &d__ + &e__ * x_;
            let transformed_angle = &d__ / 2 + &e__ * x_ / 2
                - &f__ * Atom::var(Symbol::PI) / (Atom::num(4) * &g__);
            let recursive_integrand = exponential * transformed_angle.cos().pow(Atom::num(2) * &n_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let coefficient = (&f__ + &g__ * angle.sin()).pow(&n_)
                / transformed_angle.cos().pow(Atom::num(2) * &n_);

            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_4960(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, d__, e__, f__, g__, n_, x_);
    rules.push(rubi_rule!(
        order: 4960,
        source: "Int[F_^(c_.*(a_.+b_.*x_))*(f_+g_.*Cos[d_.+e_.*x_])^n_.,x_Symbol] :=
          (f+g*Cos[d+e*x])^n/Cos[d/2+e*x/2]^(2*n) \\[Star] Int[F^(c*(a+b*x))*Cos[d/2+e*x/2]^(2*n),x] /;
        FreeQ[{F,a,b,c,d,e,f,g,n},x] && EqQ[f-g,0] && Not[IntegerQ[n]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [capital_f_, c__, a__, b__, f__, g__, d__, e__, n_, x_],
        optional: [c__, a__, b__, g__, d__, e__, n_],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__, f__, g__, n_], x_)
                && eqq!(&f__ - &g__, 0)
                && !integerq!(n_)
        },
        rhs: {
            let exponential = capital_f_.pow(&c__ * (&a__ + &b__ * x_));
            let angle = &d__ + &e__ * x_;
            let transformed_angle = &d__ / 2 + &e__ * x_ / 2;
            let recursive_integrand = exponential * transformed_angle.cos().pow(Atom::num(2) * &n_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let coefficient = (&f__ + &g__ * angle.cos()).pow(&n_)
                / transformed_angle.cos().pow(Atom::num(2) * &n_);

            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_4961(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, d__, e__, f__, g__, n_, x_);
    rules.push(rubi_rule!(
        order: 4961,
        source: "Int[F_^(c_.*(a_.+b_.*x_))*(f_+g_.*Cos[d_.+e_.*x_])^n_.,x_Symbol] :=
          (f+g*Cos[d+e*x])^n/Sin[d/2+e*x/2]^(2*n) \\[Star] Int[F^(c*(a+b*x))*Sin[d/2+e*x/2]^(2*n),x] /;
        FreeQ[{F,a,b,c,d,e,f,g,n},x] && EqQ[f+g,0] && Not[IntegerQ[n]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [capital_f_, c__, a__, b__, f__, g__, d__, e__, n_, x_],
        optional: [c__, a__, b__, g__, d__, e__, n_],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__, f__, g__, n_], x_)
                && eqq!(&f__ + &g__, 0)
                && !integerq!(n_)
        },
        rhs: {
            let exponential = capital_f_.pow(&c__ * (&a__ + &b__ * x_));
            let angle = &d__ + &e__ * x_;
            let transformed_angle = &d__ / 2 + &e__ * x_ / 2;
            let recursive_integrand = exponential * transformed_angle.sin().pow(Atom::num(2) * &n_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let coefficient = (&f__ + &g__ * angle.cos()).pow(&n_)
                / transformed_angle.sin().pow(Atom::num(2) * &n_);

            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_4962(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_f_, a__, b__, c__, d__, e__, f__, g__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 4962,
        source: "Int[F_^(c_.*(a_.+b_.*x_))*Cos[d_.+e_.*x_]^m_.*(f_+g_.*Sin[d_.+e_.*x_])^n_.,x_Symbol] :=
          g^n \\[Star] Int[F^(c*(a+b*x))*Tan[f*Pi/(4*g)-d/2-e*x/2]^m,x] /;
        FreeQ[{F,a,b,c,d,e,f,g},x] && EqQ[f^2-g^2,0] && IntegersQ[m,n] && EqQ[m+n,0]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: capital_f_.pow(c__ * (a__ + b__ * x_))
            * (d__ + e__ * x_).cos().pow(m_)
            * (f__ + g__ * (d__ + e__ * x_).sin()).pow(n_),
        with: [capital_f_, c__, a__, b__, d__, e__, m_, f__, g__, n_, x_],
        optional: [c__, a__, b__, d__, e__, g__, n_, m_],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__, f__, g__], x_)
                && eqq!(f__.pow(2) - g__.pow(2), 0)
                && integersq!([m_, n_])
                && eqq!(&m_ + &n_, 0)
        },
        rhs: {
            let exponential = capital_f_.pow(&c__ * (&a__ + &b__ * x_));
            let transformed_angle = &f__ * Atom::var(Symbol::PI) / (Atom::num(4) * &g__) - &d__ / 2 - &e__ * x_ / 2;
            let recursive_integrand = exponential * transformed_angle.tan().pow(&m_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(g__.pow(&n_), recursive)
        },
    ));
}

fn push_rules_rule_4963(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, d__, e__, f__, g__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 4963,
        source: "Int[F_^(c_.*(a_.+b_.*x_))*Sin[d_.+e_.*x_]^m_.*(f_+g_.*Cos[d_.+e_.*x_])^n_.,x_Symbol] :=
          f^n \\[Star] Int[F^(c*(a+b*x))*Tan[d/2+e*x/2]^m,x] /;
        FreeQ[{F,a,b,c,d,e,f,g},x] && EqQ[f-g,0] && IntegersQ[m,n] && EqQ[m+n,0]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [capital_f_, c__, a__, b__, d__, e__, m_, f__, g__, n_, x_],
        optional: [c__, a__, b__, d__, e__, g__, n_, m_],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__, f__, g__], x_)
                && eqq!(&f__ - &g__, 0)
                && integersq!([m_, n_])
                && eqq!(&m_ + &n_, 0)
        },
        rhs: {
            let exponential = capital_f_.pow(&c__ * (&a__ + &b__ * x_));
            let transformed_angle = &d__ / 2 + &e__ * x_ / 2;
            let recursive_integrand = exponential * transformed_angle.tan().pow(&m_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(f__.pow(&n_), recursive)
        },
    ));
}

fn push_rules_rule_4964(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, d__, e__, f__, g__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 4964,
        source: "Int[F_^(c_.*(a_.+b_.*x_))*Sin[d_.+e_.*x_]^m_.*(f_+g_.*Cos[d_.+e_.*x_])^n_.,x_Symbol] :=
          f^n \\[Star] Int[F^(c*(a+b*x))*Cot[d/2+e*x/2]^m,x] /;
        FreeQ[{F,a,b,c,d,e,f,g},x] && EqQ[f+g,0] && IntegersQ[m,n] && EqQ[m+n,0]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [capital_f_, c__, a__, b__, d__, e__, m_, f__, g__, n_, x_],
        optional: [c__, a__, b__, d__, e__, g__, n_, m_],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__, f__, g__], x_)
                && eqq!(&f__ + &g__, 0)
                && integersq!([m_, n_])
                && eqq!(&m_ + &n_, 0)
        },
        rhs: {
            let exponential = capital_f_.pow(&c__ * (&a__ + &b__ * x_));
            let transformed_angle = &d__ / 2 + &e__ * x_ / 2;
            let recursive_integrand = exponential * transformed_angle.cot().pow(&m_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(f__.pow(&n_), recursive)
        },
    ));
}

fn push_rules_rule_4965(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_f_, a__, b__, c__, d__, e__, f__, g__, h__, i__, x_);
    rules.push(rubi_rule!(
        order: 4965,
        source: "Int[F_^(c_.*(a_.+b_.*x_))*(h_+i_.*Cos[d_.+e_.*x_])/(f_+g_.*Sin[d_.+e_.*x_]),x_Symbol] :=
          2*i \\[Star] Int[F^(c*(a+b*x))*(Cos[d+e*x]/(f+g*Sin[d+e*x])),x] +
          Int[F^(c*(a+b*x))*((h-i*Cos[d+e*x])/(f+g*Sin[d+e*x])),x] /;
        FreeQ[{F,a,b,c,d,e,f,g,h,i},x] && EqQ[f^2-g^2,0] && EqQ[h^2-i^2,0] && EqQ[g*h-f*i,0]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: capital_f_.pow(c__ * (a__ + b__ * x_))
            * (h__ + i__ * (d__ + e__ * x_).cos())
            / (f__ + g__ * (d__ + e__ * x_).sin()),
        with: [capital_f_, c__, a__, b__, h__, i__, d__, e__, f__, g__, x_],
        optional: [c__, a__, b__, i__, d__, e__, g__],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__, f__, g__, h__, i__], x_)
                && eqq!(f__.pow(2) - g__.pow(2), 0)
                && eqq!(h__.pow(2) - i__.pow(2), 0)
                && eqq!(&g__ * &h__ - &f__ * &i__, 0)
        },
        rhs: {
            let exponential = capital_f_.pow(&c__ * (&a__ + &b__ * x_));
            let angle = &d__ + &e__ * x_;
            let denominator = &f__ + &g__ * angle.sin();
            let first_integrand = &exponential * angle.cos() / &denominator;
            let second_integrand = exponential * (&h__ - &i__ * angle.cos()) / denominator;
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(Atom::num(2) * &i__, first) + second
        },
    ));
}

fn push_rules_rule_4966(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_f_, a__, b__, c__, d__, e__, f__, g__, h__, i__, x_);
    rules.push(rubi_rule!(
        order: 4966,
        source: "Int[F_^(c_.*(a_.+b_.*x_))*(h_+i_.*Sin[d_.+e_.*x_])/(f_+g_.*Cos[d_.+e_.*x_]),x_Symbol] :=
          2*i \\[Star] Int[F^(c*(a+b*x))*(Sin[d+e*x]/(f+g*Cos[d+e*x])),x] +
          Int[F^(c*(a+b*x))*((h-i*Sin[d+e*x])/(f+g*Cos[d+e*x])),x] /;
        FreeQ[{F,a,b,c,d,e,f,g,h,i},x] && EqQ[f^2-g^2,0] && EqQ[h^2-i^2,0] && EqQ[g*h+f*i,0]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: capital_f_.pow(c__ * (a__ + b__ * x_))
            * (h__ + i__ * (d__ + e__ * x_).sin())
            / (f__ + g__ * (d__ + e__ * x_).cos()),
        with: [capital_f_, c__, a__, b__, h__, i__, d__, e__, f__, g__, x_],
        optional: [c__, a__, b__, i__, d__, e__, g__],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__, f__, g__, h__, i__], x_)
                && eqq!(f__.pow(2) - g__.pow(2), 0)
                && eqq!(h__.pow(2) - i__.pow(2), 0)
                && eqq!(&g__ * &h__ + &f__ * &i__, 0)
        },
        rhs: {
            let exponential = capital_f_.pow(&c__ * (&a__ + &b__ * x_));
            let angle = &d__ + &e__ * x_;
            let denominator = &f__ + &g__ * angle.cos();
            let first_integrand = &exponential * angle.sin() / &denominator;
            let second_integrand = exponential * (&h__ - &i__ * angle.sin()) / denominator;
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(Atom::num(2) * &i__, first) + second
        },
    ));
}

fn push_rules_rule_4967(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_f_, capital_g_, c__, n_, u_, v_);
    rules.push(rubi_rule!(
        order: 4967,
        source: "Int[F_^(c_.*u_)*G_[v_]^n_.,x_Symbol] :=
          Int[F^(c*ExpandToSum[u,x])*G[ExpandToSum[v,x]]^n,x] /;
        FreeQ[{F,c,n},x] && TrigQ[G] && LinearQ[{u,v},x] && Not[LinearMatchQ[{u,v},x]]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: capital_f_.pow(c__ * u_) * capital_g_.call( v_).pow(n_),
        with: [capital_f_, c__, u_, capital_g_, v_, n_, x_],
        optional: [c__, n_],
        when: {
            freeq!([capital_f_, c__, n_], x_)
                && rubi_trig_q(&capital_g_)
                && rubi_linear_q_list(&[&u_, &v_], x_)
                && !rubi_linear_match_q_list(&[&u_, &v_], x_)
        },
        rhs: {
            let expanded_u = rubi_expand_to_sum(&u_, x_);
            let expanded_v = rubi_expand_to_sum(&v_, x_);
            let recursive_integrand =
                capital_f_.pow(&c__ * expanded_u) * rubi_function_head_symbol(&capital_g_).rubi_rhs().call( expanded_v).pow(&n_);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_4968(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_f_, a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 4968,
        source: "Int[(f_.*x_)^m_.*F_^(c_.*(a_.+b_.*x_))*Sin[d_.+e_.*x_]^n_.,x_Symbol] :=
          Module[{u=IntHide[F^(c*(a+b*x))*Sin[d+e*x]^n,x]},
          (f*x)^m \\[Star] u - f*m \\[Star] Int[(f*x)^(m-1)*u,x]] /;
        FreeQ[{F,a,b,c,d,e,f},x] && IGtQ[n,0] && GtQ[m,0]",
        desc: "Integration by parts",
        refs: [],
        pattern: (f__ * x_).pow(m_) * capital_f_.pow(c__ * (a__ + b__ * x_)) * (d__ + e__ * x_).sin().pow(n_),
        with: [f__, m_, capital_f_, c__, a__, b__, d__, e__, n_, x_],
        optional: [f__, m_, c__, a__, b__, d__, e__, n_],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__, f__], x_)
                && igtq!(n_, 0)
                && gtq!(m_, 0)
        },
        rhs: {
            let exponential = capital_f_.pow(&c__ * (&a__ + &b__ * x_));
            let angle = &d__ + &e__ * x_;
            let scaled_x = &f__ * x_;
            let u = rubi_int_hide(&(exponential * angle.sin().pow(&n_)), x_).rubi_rhs();
            let recursive_integrand = scaled_x.pow(&m_ - 1) * &u;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(scaled_x.pow(&m_), u)
                    + rubi_star(-&f__ * &m_, recursive)
        },
    ));
}

fn push_rules_rule_4969(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_f_, a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 4969,
        source: "Int[(f_.*x_)^m_.*F_^(c_.*(a_.+b_.*x_))*Cos[d_.+e_.*x_]^n_.,x_Symbol] :=
          Module[{u=IntHide[F^(c*(a+b*x))*Cos[d+e*x]^n,x]},
          (f*x)^m \\[Star] u - f*m \\[Star] Int[(f*x)^(m-1)*u,x]] /;
        FreeQ[{F,a,b,c,d,e,f},x] && IGtQ[n,0] && GtQ[m,0]",
        desc: "Integration by parts",
        refs: [],
        pattern: (f__ * x_).pow(m_) * capital_f_.pow(c__ * (a__ + b__ * x_)) * (d__ + e__ * x_).cos().pow(n_),
        with: [f__, m_, capital_f_, c__, a__, b__, d__, e__, n_, x_],
        optional: [f__, m_, c__, a__, b__, d__, e__, n_],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__, f__], x_)
                && igtq!(n_, 0)
                && gtq!(m_, 0)
        },
        rhs: {
            let exponential = capital_f_.pow(&c__ * (&a__ + &b__ * x_));
            let angle = &d__ + &e__ * x_;
            let scaled_x = &f__ * x_;
            let u = rubi_int_hide(&(exponential * angle.cos().pow(&n_)), x_).rubi_rhs();
            let recursive_integrand = scaled_x.pow(&m_ - 1) * &u;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(scaled_x.pow(&m_), u)
                    + rubi_star(-&f__ * &m_, recursive)
        },
    ));
}

fn push_rules_rule_4970(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_f_, a__, b__, c__, d__, e__, f__, m_, x_);
    rules.push(rubi_rule!(
        order: 4970,
        source: "Int[(f_.*x_)^m_*F_^(c_.*(a_.+b_.*x_))*Sin[d_.+e_.*x_],x_Symbol] :=
          (f*x)^(m+1)/(f*(m+1))*F^(c*(a+b*x))*Sin[d+e*x] -
          e/(f*(m+1)) \\[Star] Int[(f*x)^(m+1)*F^(c*(a+b*x))*Cos[d+e*x],x] -
          b*c*Log[F]/(f*(m+1)) \\[Star] Int[(f*x)^(m+1)*F^(c*(a+b*x))*Sin[d+e*x],x] /;
        FreeQ[{F,a,b,c,d,e,f,m},x] && (LtQ[m,-1] || SumSimplerQ[m,1])",
        desc: "Integration by parts",
        refs: [],
        pattern: (f__ * x_).pow(m_) * capital_f_.pow(c__ * (a__ + b__ * x_)) * (d__ + e__ * x_).sin(),
        with: [f__, m_, capital_f_, c__, a__, b__, d__, e__, x_],
        optional: [f__, c__, a__, b__, d__, e__],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__, f__, m_], x_)
                && (ltq!(m_, -1) || sum_simplerq!(m_, 1))
        },
        rhs: {
            let scaled_x = &f__ * x_;
            let exponential = capital_f_.pow(&c__ * (&a__ + &b__ * x_));
            let angle = &d__ + &e__ * x_;
            let denominator = &f__ * (&m_ + 1);
            let cosine_integrand = scaled_x.pow(&m_ + 1) * &exponential * angle.cos();
            let sine_integrand = scaled_x.pow(&m_ + 1) * &exponential * angle.sin();
            let cosine_recursive = rubi_rhs_int(&cosine_integrand, x_);
            let sine_recursive = rubi_rhs_int(&sine_integrand, x_);
            let cosine_term = rubi_star(-&e__ / &denominator, cosine_recursive);
            let sine_term = rubi_star(
                -&b__ * &c__ * capital_f_.log() / &denominator,
                sine_recursive,
            );

            rubi_simp(&(scaled_x.pow(&m_ + 1) * &exponential * angle.sin() / &denominator), x_)
                    + cosine_term
                    + sine_term
        },
    ));
}

fn push_rules_rule_4971(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_f_, a__, b__, c__, d__, e__, f__, m_, x_);
    rules.push(rubi_rule!(
        order: 4971,
        source: "Int[(f_.*x_)^m_*F_^(c_.*(a_.+b_.*x_))*Cos[d_.+e_.*x_],x_Symbol] :=
          (f*x)^(m+1)/(f*(m+1))*F^(c*(a+b*x))*Cos[d+e*x] +
          e/(f*(m+1)) \\[Star] Int[(f*x)^(m+1)*F^(c*(a+b*x))*Sin[d+e*x],x] -
          b*c*Log[F]/(f*(m+1)) \\[Star] Int[(f*x)^(m+1)*F^(c*(a+b*x))*Cos[d+e*x],x] /;
        FreeQ[{F,a,b,c,d,e,f,m},x] && (LtQ[m,-1] || SumSimplerQ[m,1])",
        desc: "Integration by parts",
        refs: [],
        pattern: (f__ * x_).pow(m_) * capital_f_.pow(c__ * (a__ + b__ * x_)) * (d__ + e__ * x_).cos(),
        with: [f__, m_, capital_f_, c__, a__, b__, d__, e__, x_],
        optional: [f__, c__, a__, b__, d__, e__],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__, f__, m_], x_)
                && (ltq!(m_, -1) || sum_simplerq!(m_, 1))
        },
        rhs: {
            let scaled_x = &f__ * x_;
            let exponential = capital_f_.pow(&c__ * (&a__ + &b__ * x_));
            let angle = &d__ + &e__ * x_;
            let denominator = &f__ * (&m_ + 1);
            let sine_integrand = scaled_x.pow(&m_ + 1) * &exponential * angle.sin();
            let cosine_integrand = scaled_x.pow(&m_ + 1) * &exponential * angle.cos();
            let sine_recursive = rubi_rhs_int(&sine_integrand, x_);
            let cosine_recursive = rubi_rhs_int(&cosine_integrand, x_);
            let sine_term = rubi_star(&e__ / &denominator, sine_recursive);
            let cosine_term = rubi_star(
                -&b__ * &c__ * capital_f_.log() / &denominator,
                cosine_recursive,
            );

            rubi_simp(&(scaled_x.pow(&m_ + 1) * &exponential * angle.cos() / &denominator), x_)
                    + sine_term
                    + cosine_term
        },
    ));
}

fn push_rules_rule_4972(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_f_, a__, b__, c__, d__, e__, f__, g__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 4972,
        source: "Int[F_^(c_.*(a_.+b_.*x_))*Sin[d_.+e_.*x_]^m_.*Cos[f_.+g_.*x_]^n_.,x_Symbol] :=
          Int[ExpandTrigReduce[F^(c*(a+b*x)),Sin[d+e*x]^m*Cos[f+g*x]^n,x],x] /;
        FreeQ[{F,a,b,c,d,e,f,g},x] && IGtQ[m,0] && IGtQ[n,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: capital_f_.pow(c__ * (a__ + b__ * x_)) * (d__ + e__ * x_).sin().pow(m_) * (f__ + g__ * x_).cos().pow(n_),
        with: [capital_f_, c__, a__, b__, d__, e__, m_, f__, g__, n_, x_],
        optional: [c__, a__, b__, d__, e__, m_, f__, g__, n_],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__, f__, g__], x_)
                && igtq!(m_, 0)
                && igtq!(n_, 0)
        },
        rhs: {
            let multiplier = capital_f_.pow(&c__ * (&a__ + &b__ * x_));
            let product = (&d__ + &e__ * x_).sin().pow(&m_) * (&f__ + &g__ * x_).cos().pow(&n_);
            let expanded = rubi_expand_trig_reduce(&multiplier, &product, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_4973(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        capital_f_, a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_
    );
    rules.push(rubi_rule!(
        order: 4973,
        source: "Int[x_^p_.*F_^(c_.*(a_.+b_.*x_))*Sin[d_.+e_.*x_]^m_.*Cos[f_.+g_.*x_]^n_.,x_Symbol] :=
          Int[ExpandTrigReduce[x^p*F^(c*(a+b*x)),Sin[d+e*x]^m*Cos[f+g*x]^n,x],x] /;
        FreeQ[{F,a,b,c,d,e,f,g},x] && IGtQ[m,0] && IGtQ[n,0] && IGtQ[p,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: x_.pow(p_) * capital_f_.pow(c__ * (a__ + b__ * x_)) * (d__ + e__ * x_).sin().pow(m_) * (f__ + g__ * x_).cos().pow(n_),
        with: [p_, capital_f_, c__, a__, b__, d__, e__, m_, f__, g__, n_, x_],
        optional: [p_, c__, a__, b__, d__, e__, m_, f__, g__, n_],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__, f__, g__], x_)
                && igtq!(m_, 0)
                && igtq!(n_, 0)
                && igtq!(p_, 0)
        },
        rhs: {
            let multiplier = x_.pow(&p_) * capital_f_.pow(&c__ * (&a__ + &b__ * x_));
            let product = (&d__ + &e__ * x_).sin().pow(&m_) * (&f__ + &g__ * x_).cos().pow(&n_);
            let expanded = rubi_expand_trig_reduce(&multiplier, &product, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_4974(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        capital_f_, capital_g_, capital_h_, a__, b__, c__, d__, e__, m_, n_, x_
    );
    rules.push(rubi_rule!(
        order: 4974,
        source: "Int[F_^(c_.*(a_.+b_.*x_))*G_[d_.+e_.*x_]^m_.*H_[d_.+e_.*x_]^n_.,x_Symbol] :=
          Int[ExpandTrigToExp[F^(c*(a+b*x)),G[d+e*x]^m*H[d+e*x]^n,x],x] /;
        FreeQ[{F,a,b,c,d,e},x] && IGtQ[m,0] && IGtQ[n,0] && TrigQ[G] && TrigQ[H]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: capital_f_.pow(c__ * (a__ + b__ * x_))
            * capital_g_.call( d__ + e__ * x_).pow(m_)
            * capital_h_.call( d__ + e__ * x_).pow(n_),
        with: [capital_f_, c__, a__, b__, capital_g_, d__, e__, m_, capital_h_, n_, x_],
        optional: [c__, a__, b__, d__, e__, m_, n_],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__], x_)
                && igtq!(m_, 0)
                && igtq!(n_, 0)
                && rubi_trig_q(&capital_g_)
                && rubi_trig_q(&capital_h_)
        },
        rhs: {
            let multiplier = capital_f_.pow(&c__ * (&a__ + &b__ * x_));
            let angle = &d__ + &e__ * x_;
            let product =
                rubi_function_head_symbol(&capital_g_).rubi_rhs().call( &angle).pow(&m_) * rubi_function_head_symbol(&capital_h_).rubi_rhs().call( angle).pow(&n_);
            let expanded = rubi_expand_trig_to_exp(&multiplier, &product, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_4975(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_f_, n_, u_, v_);
    rules.push(rubi_rule!(
        order: 4975,
        source: "Int[F_^u_*Sin[v_]^n_.,x_Symbol] :=
          Int[ExpandTrigToExp[F^u,Sin[v]^n,x],x] /;
        FreeQ[F,x] && (LinearQ[u,x] || PolyQ[u,x,2]) && (LinearQ[v,x] || PolyQ[v,x,2]) && IGtQ[n,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: capital_f_.pow(u_) * (Atom::var(v_)).sin().pow(n_),
        with: [capital_f_, u_, v_, n_, x_],
        optional: [n_],
        when: {
            freeq!(capital_f_, x_)
                && (rubi_linear_q(&u_, x_) || rubi_poly_q_degree(&u_, x_, 2))
                && (rubi_linear_q(&v_, x_) || rubi_poly_q_degree(&v_, x_, 2))
                && igtq!(n_, 0)
        },
        rhs: {
            let multiplier = capital_f_.pow(&u_);
            let product = v_.sin().pow(&n_);
            let expanded = rubi_expand_trig_to_exp(&multiplier, &product, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_4976(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_f_, n_, u_, v_);
    rules.push(rubi_rule!(
        order: 4976,
        source: "Int[F_^u_*Cos[v_]^n_.,x_Symbol] :=
          Int[ExpandTrigToExp[F^u,Cos[v]^n,x],x] /;
        FreeQ[F,x] && (LinearQ[u,x] || PolyQ[u,x,2]) && (LinearQ[v,x] || PolyQ[v,x,2]) && IGtQ[n,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: capital_f_.pow(u_) * (Atom::var(v_)).cos().pow(n_),
        with: [capital_f_, u_, v_, n_, x_],
        optional: [n_],
        when: {
            freeq!(capital_f_, x_)
                && (rubi_linear_q(&u_, x_) || rubi_poly_q_degree(&u_, x_, 2))
                && (rubi_linear_q(&v_, x_) || rubi_poly_q_degree(&v_, x_, 2))
                && igtq!(n_, 0)
        },
        rhs: {
            let multiplier = capital_f_.pow(&u_);
            let product = v_.cos().pow(&n_);
            let expanded = rubi_expand_trig_to_exp(&multiplier, &product, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_4977(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_f_, m_, n_, u_, v_);
    rules.push(rubi_rule!(
        order: 4977,
        source: "Int[F_^u_*Sin[v_]^m_.*Cos[v_]^n_.,x_Symbol] :=
          Int[ExpandTrigToExp[F^u,Sin[v]^m*Cos[v]^n,x],x] /;
        FreeQ[F,x] && (LinearQ[u,x] || PolyQ[u,x,2]) && (LinearQ[v,x] || PolyQ[v,x,2]) && IGtQ[m,0] && IGtQ[n,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: capital_f_.pow(u_) * (Atom::var(v_)).sin().pow(m_) * (Atom::var(v_)).cos().pow(n_),
        with: [capital_f_, u_, v_, m_, n_, x_],
        optional: [m_, n_],
        when: {
            freeq!(capital_f_, x_)
                && (rubi_linear_q(&u_, x_) || rubi_poly_q_degree(&u_, x_, 2))
                && (rubi_linear_q(&v_, x_) || rubi_poly_q_degree(&v_, x_, 2))
                && igtq!(m_, 0)
                && igtq!(n_, 0)
        },
        rhs: {
            let multiplier = capital_f_.pow(&u_);
            let product = v_.sin().pow(&m_) * v_.cos().pow(&n_);
            let expanded = rubi_expand_trig_to_exp(&multiplier, &product, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn downvalues_4932_through_4942_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .filter(|order| (4932..=4942).contains(order))
            .collect::<Vec<_>>();
        assert_eq!(orders, (4932..=4942).collect::<Vec<_>>());
    }

    #[test]
    fn downvalues_4943_through_4977_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .filter(|order| (4943..=4977).contains(order))
            .collect::<Vec<_>>();
        assert_eq!(orders, (4943..=4977).collect::<Vec<_>>());
    }
}

// Generated shared pattern builders.

#[inline(never)]
fn rubi_shared_pattern_0(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let capital_f_ = symbols.capital_f_;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    capital_f_.pow(c__ * (a__ + b__ * x_)) * (d__ + e__ * x_).cos().pow(n_)
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let capital_f_ = symbols.capital_f_;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    capital_f_.pow(c__ * (a__ + b__ * x_)) * (d__ + e__ * x_).csc().pow(n_)
}

#[inline(never)]
fn rubi_shared_pattern_2(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let capital_f_ = symbols.capital_f_;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    capital_f_.pow(c__ * (a__ + b__ * x_)) * (d__ + e__ * x_).sec().pow(n_)
}

#[inline(never)]
fn rubi_shared_pattern_3(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let capital_f_ = symbols.capital_f_;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let g__ = symbols.g__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    capital_f_.pow(c__ * (a__ + b__ * x_))
        * (d__ + e__ * x_).sin().pow(m_)
        * (f__ + g__ * (d__ + e__ * x_).cos()).pow(n_)
}

#[inline(never)]
fn rubi_shared_pattern_4(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let capital_f_ = symbols.capital_f_;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    capital_f_.pow(c__ * (a__ + b__ * x_)) * (d__ + e__ * x_).sin().pow(n_)
}

#[inline(never)]
fn rubi_shared_pattern_5(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let capital_f_ = symbols.capital_f_;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let g__ = symbols.g__;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    capital_f_.pow(c__ * (a__ + b__ * x_)) * (f__ + g__ * (d__ + e__ * x_).cos()).pow(n_)
}

#[inline(never)]
fn rubi_shared_pattern_6(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let capital_f_ = symbols.capital_f_;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let g__ = symbols.g__;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    capital_f_.pow(c__ * (a__ + b__ * x_)) * (f__ + g__ * (d__ + e__ * x_).sin()).pow(n_)
}
