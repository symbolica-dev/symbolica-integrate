use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_5997(rules);
    push_rules_rule_5998(rules);
    push_rules_rule_5999(rules);
    push_rules_rule_6000(rules);
    push_rules_rule_6001(rules);
    push_rules_rule_6002(rules);
    push_rules_rule_6003(rules);
    push_rules_rule_6004(rules);
    push_rules_rule_6005(rules);
    push_rules_rule_6006(rules);
    push_rules_rule_6007(rules);
    push_rules_rule_6008(rules);
    push_rules_rule_6009(rules);
    push_rules_rule_6010(rules);
    push_rules_rule_6011(rules);
    push_rules_rule_6012(rules);
    push_rules_rule_6013(rules);
    push_rules_rule_6014(rules);
    push_rules_rule_6015(rules);
    push_rules_rule_6016(rules);
    push_rules_rule_6017(rules);
    push_rules_rule_6018(rules);
    push_rules_rule_6019(rules);
    push_rules_rule_6020(rules);
    push_rules_rule_6021(rules);
    push_rules_rule_6022(rules);
    push_rules_rule_6023(rules);
    push_rules_rule_6024(rules);
    push_rules_rule_6025(rules);
    push_rules_rule_6026(rules);
    push_rules_rule_6027(rules);
    push_rules_rule_6028(rules);
    push_rules_rule_6029(rules);
    push_rules_rule_6030(rules);
    push_rules_rule_6031(rules);
    push_rules_rule_6032(rules);
    push_rules_rule_6033(rules);
    push_rules_rule_6034(rules);
    push_rules_rule_6035(rules);
    push_rules_rule_6036(rules);
    push_rules_rule_6037(rules);
    push_rules_rule_6038(rules);
    push_rules_rule_6039(rules);
    push_rules_rule_6040(rules);
}

fn push_rules_rule_5997(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_f_, a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 5997,
        source: "Int[F_^(c_.*(a_.+b_.*x_))*Sinh[d_.+e_.*x_],x_Symbol] :=
          -b*c*Log[F]*F^(c*(a+b*x))*Sinh[d+e*x]/(e^2-b^2*c^2*Log[F]^2) +
          e*F^(c*(a+b*x))*Cosh[d+e*x]/(e^2-b^2*c^2*Log[F]^2) /;
        FreeQ[{F,a,b,c,d,e},x] && NeQ[e^2-b^2*c^2*Log[F]^2,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: ["CRC 533h", "CRC 538h"],
        pattern: capital_f_.pow(c__ * (a__ + b__ * x_)) * (d__ + e__ * x_).sinh(),
        with: [capital_f_, c__, a__, b__, d__, e__, x_],
        optional: [c__, a__, b__, d__, e__],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__], x_)
                && neq!(e__.pow(2) - b__.pow(2) * c__.pow(2) * capital_f_.log().pow(2), 0)
        },
        rhs: {
            let exponential = capital_f_.pow(&c__ * (&a__ + &b__ * x_));
            let angle = &d__ + &e__ * x_;
            let denominator = e__.pow(2) - b__.pow(2) * c__.pow(2) * capital_f_.log().pow(2);

            rubi_simp(&(-&b__ * &c__ * capital_f_.log() * &exponential * angle.sinh() / &denominator), x_)
                    + rubi_simp(&(&e__ * exponential * angle.cosh() / denominator), x_)
        },
    ));
}

fn push_rules_rule_5998(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_f_, a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 5998,
        source: "Int[F_^(c_.*(a_.+b_.*x_))*Cosh[d_.+e_.*x_],x_Symbol] :=
          -b*c*Log[F]*F^(c*(a+b*x))*Cosh[d+e*x]/(e^2-b^2*c^2*Log[F]^2) +
          e*F^(c*(a+b*x))*Sinh[d+e*x]/(e^2-b^2*c^2*Log[F]^2) /;
        FreeQ[{F,a,b,c,d,e},x] && NeQ[e^2-b^2*c^2*Log[F]^2,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: ["CRC 533h", "CRC 538h"],
        pattern: capital_f_.pow(c__ * (a__ + b__ * x_)) * (d__ + e__ * x_).cosh(),
        with: [capital_f_, c__, a__, b__, d__, e__, x_],
        optional: [c__, a__, b__, d__, e__],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__], x_)
                && neq!(e__.pow(2) - b__.pow(2) * c__.pow(2) * capital_f_.log().pow(2), 0)
        },
        rhs: {
            let exponential = capital_f_.pow(&c__ * (&a__ + &b__ * x_));
            let angle = &d__ + &e__ * x_;
            let denominator = e__.pow(2) - b__.pow(2) * c__.pow(2) * capital_f_.log().pow(2);

            rubi_simp(&(-&b__ * &c__ * capital_f_.log() * &exponential * angle.cosh() / &denominator), x_)
                    + rubi_simp(&(&e__ * exponential * angle.sinh() / denominator), x_)
        },
    ));
}

fn push_rules_rule_5999(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, d__, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 5999,
        source: "Int[F_^(c_.*(a_.+b_.*x_))*Sinh[d_.+e_.*x_]^n_,x_Symbol] :=
          -b*c*Log[F]*F^(c*(a+b*x))*Sinh[d+e*x]^n/(e^2*n^2-b^2*c^2*Log[F]^2) +
          e*n*F^(c*(a+b*x))*Cosh[d+e*x]*Sinh[d+e*x]^(n-1)/(e^2*n^2-b^2*c^2*Log[F]^2) -
          n*(n-1)*e^2/(e^2*n^2-b^2*c^2*Log[F]^2) \\[Star] Int[F^(c*(a+b*x))*Sinh[d+e*x]^(n-2),x] /;
        FreeQ[{F,a,b,c,d,e},x] && NeQ[e^2*n^2-b^2*c^2*Log[F]^2,0] && GtQ[n,1]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: ["CRC 542h", "CRC 543h"],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [capital_f_, c__, a__, b__, d__, e__, n_, x_],
        optional: [c__, a__, b__, d__, e__],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__], x_)
                && neq!(e__.pow(2) * n_.pow(2) - b__.pow(2) * c__.pow(2) * capital_f_.log().pow(2), 0)
                && gtq!(n_, 1)
        },
        rhs: {
            let exponential = capital_f_.pow(&c__ * (&a__ + &b__ * x_));
            let angle = &d__ + &e__ * x_;
            let denominator = e__.pow(2) * n_.pow(2) - b__.pow(2) * c__.pow(2) * capital_f_.log().pow(2);
            let recursive = rubi_rhs_int(&(&exponential * angle.sinh().pow(&n_ - 2)), x_);

            rubi_simp(&(-&b__ * &c__ * capital_f_.log() * &exponential * angle.sinh().pow(&n_) / &denominator), x_)
                    + rubi_simp(&(&e__ * &n_ * &exponential * angle.cosh() * angle.sinh().pow(&n_ - 1) / &denominator), x_)
                    - rubi_star(&n_ * (&n_ - 1) * e__.pow(2) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_6000(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, d__, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 6000,
        source: "Int[F_^(c_.*(a_.+b_.*x_))*Cosh[d_.+e_.*x_]^n_,x_Symbol] :=
          -b*c*Log[F]*F^(c*(a+b*x))*Cosh[d+e*x]^n/(e^2*n^2-b^2*c^2*Log[F]^2) +
          e*n*F^(c*(a+b*x))*Sinh[d+e*x]*Cosh[d+e*x]^(n-1)/(e^2*n^2-b^2*c^2*Log[F]^2) +
          n*(n-1)*e^2/(e^2*n^2-b^2*c^2*Log[F]^2) \\[Star] Int[F^(c*(a+b*x))*Cosh[d+e*x]^(n-2),x] /;
        FreeQ[{F,a,b,c,d,e},x] && NeQ[e^2*n^2-b^2*c^2*Log[F]^2,0] && GtQ[n,1]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: ["CRC 542h", "CRC 543h"],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [capital_f_, c__, a__, b__, d__, e__, n_, x_],
        optional: [c__, a__, b__, d__, e__],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__], x_)
                && neq!(e__.pow(2) * n_.pow(2) - b__.pow(2) * c__.pow(2) * capital_f_.log().pow(2), 0)
                && gtq!(n_, 1)
        },
        rhs: {
            let exponential = capital_f_.pow(&c__ * (&a__ + &b__ * x_));
            let angle = &d__ + &e__ * x_;
            let denominator = e__.pow(2) * n_.pow(2) - b__.pow(2) * c__.pow(2) * capital_f_.log().pow(2);
            let recursive = rubi_rhs_int(&(&exponential * angle.cosh().pow(&n_ - 2)), x_);

            rubi_simp(&(-&b__ * &c__ * capital_f_.log() * &exponential * angle.cosh().pow(&n_) / &denominator), x_)
                    + rubi_simp(&(&e__ * &n_ * &exponential * angle.sinh() * angle.cosh().pow(&n_ - 1) / &denominator), x_)
                    + rubi_star(&n_ * (&n_ - 1) * e__.pow(2) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_6001(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, d__, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 6001,
        source: "Int[F_^(c_.*(a_.+b_.*x_))*Sinh[d_.+e_.*x_]^n_,x_Symbol] :=
          -b*c*Log[F]*F^(c*(a+b*x))*Sinh[d+e*x]^(n+2)/(e^2*(n+1)*(n+2)) +
          F^(c*(a+b*x))*Cosh[d+e*x]*Sinh[d+e*x]^(n+1)/(e*(n+1)) /;
        FreeQ[{F,a,b,c,d,e,n},x] && EqQ[e^2*(n+2)^2-b^2*c^2*Log[F]^2,0] && NeQ[n,-1] && NeQ[n,-2]",
        desc: "Apply the direct antiderivative formula.",
        refs: ["CRC 551h when e2(n+2)2-b2c2Log[F]2\\[Equal]0", "CRC 552h when e2(n+2)2-b2c2Log[F]2\\[Equal]0"],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [capital_f_, c__, a__, b__, d__, e__, n_, x_],
        optional: [c__, a__, b__, d__, e__],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__, n_], x_)
                && eqq!(e__.pow(2) * (&n_ + 2).pow(2) - b__.pow(2) * c__.pow(2) * capital_f_.log().pow(2), 0)
                && neq!(n_, -1)
                && neq!(n_, -2)
        },
        rhs: {
            let exponential = capital_f_.pow(&c__ * (&a__ + &b__ * x_));
            let angle = &d__ + &e__ * x_;

            rubi_simp(&(-&b__ * &c__ * capital_f_.log() * &exponential * angle.sinh().pow(&n_ + 2)
                    / (e__.pow(2) * (&n_ + 1) * (&n_ + 2))), x_)
                    + rubi_simp(&(exponential * angle.cosh() * angle.sinh().pow(&n_ + 1) / (&e__ * (&n_ + 1))), x_)
        },
    ));
}

fn push_rules_rule_6002(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, d__, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 6002,
        source: "Int[F_^(c_.*(a_.+b_.*x_))*Cosh[d_.+e_.*x_]^n_,x_Symbol] :=
          b*c*Log[F]*F^(c*(a+b*x))*Cosh[d+e*x]^(n+2)/(e^2*(n+1)*(n+2)) -
          F^(c*(a+b*x))*Sinh[d+e*x]*Cosh[d+e*x]^(n+1)/(e*(n+1)) /;
        FreeQ[{F,a,b,c,d,e,n},x] && EqQ[e^2*(n+2)^2-b^2*c^2*Log[F]^2,0] && NeQ[n,-1] && NeQ[n,-2]",
        desc: "Apply the direct antiderivative formula.",
        refs: ["CRC 551h when e2(n+2)2-b2c2Log[F]2\\[Equal]0", "CRC 552h when e2(n+2)2-b2c2Log[F]2\\[Equal]0"],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [capital_f_, c__, a__, b__, d__, e__, n_, x_],
        optional: [c__, a__, b__, d__, e__],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__, n_], x_)
                && eqq!(e__.pow(2) * (&n_ + 2).pow(2) - b__.pow(2) * c__.pow(2) * capital_f_.log().pow(2), 0)
                && neq!(n_, -1)
                && neq!(n_, -2)
        },
        rhs: {
            let exponential = capital_f_.pow(&c__ * (&a__ + &b__ * x_));
            let angle = &d__ + &e__ * x_;

            rubi_simp(&(&b__ * &c__ * capital_f_.log() * &exponential * angle.cosh().pow(&n_ + 2)
                    / (e__.pow(2) * (&n_ + 1) * (&n_ + 2))), x_)
                    - rubi_simp(&(exponential * angle.sinh() * angle.cosh().pow(&n_ + 1) / (&e__ * (&n_ + 1))), x_)
        },
    ));
}

fn push_rules_rule_6003(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, d__, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 6003,
        source: "Int[F_^(c_.*(a_.+b_.*x_))*Sinh[d_.+e_.*x_]^n_,x_Symbol] :=
          -b*c*Log[F]*F^(c*(a+b*x))*Sinh[d+e*x]^(n+2)/(e^2*(n+1)*(n+2)) +
          F^(c*(a+b*x))*Cosh[d+e*x]*Sinh[d+e*x]^(n+1)/(e*(n+1)) -
          (e^2*(n+2)^2-b^2*c^2*Log[F]^2)/(e^2*(n+1)*(n+2)) \\[Star] Int[F^(c*(a+b*x))*Sinh[d+e*x]^(n+2),x] /;
        FreeQ[{F,a,b,c,d,e},x] && NeQ[e^2*(n+2)^2-b^2*c^2*Log[F]^2,0] && LtQ[n,-1] && NeQ[n,-2]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: ["CRC 551h, CRC 542h inverted", "CRC 552h, CRC 543h inverted"],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [capital_f_, c__, a__, b__, d__, e__, n_, x_],
        optional: [c__, a__, b__, d__, e__],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__], x_)
                && neq!(e__.pow(2) * (&n_ + 2).pow(2) - b__.pow(2) * c__.pow(2) * capital_f_.log().pow(2), 0)
                && ltq!(n_, -1)
                && neq!(n_, -2)
        },
        rhs: {
            let exponential = capital_f_.pow(&c__ * (&a__ + &b__ * x_));
            let angle = &d__ + &e__ * x_;
            let denominator = e__.pow(2) * (&n_ + 1) * (&n_ + 2);
            let balance = e__.pow(2) * (&n_ + 2).pow(2) - b__.pow(2) * c__.pow(2) * capital_f_.log().pow(2);
            let recursive = rubi_rhs_int(&(&exponential * angle.sinh().pow(&n_ + 2)), x_);

            rubi_simp(&(-&b__ * &c__ * capital_f_.log() * &exponential * angle.sinh().pow(&n_ + 2) / &denominator), x_)
                    + rubi_simp(&(&exponential * angle.cosh() * angle.sinh().pow(&n_ + 1) / (&e__ * (&n_ + 1))), x_)
                    - rubi_star(&balance / &denominator, recursive)
        },
    ));
}

fn push_rules_rule_6004(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, d__, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 6004,
        source: "Int[F_^(c_.*(a_.+b_.*x_))*Cosh[d_.+e_.*x_]^n_,x_Symbol] :=
          b*c*Log[F]*F^(c*(a+b*x))*Cosh[d+e*x]^(n+2)/(e^2*(n+1)*(n+2)) -
          F^(c*(a+b*x))*Sinh[d+e*x]*Cosh[d+e*x]^(n+1)/(e*(n+1)) +
          (e^2*(n+2)^2-b^2*c^2*Log[F]^2)/(e^2*(n+1)*(n+2)) \\[Star] Int[F^(c*(a+b*x))*Cosh[d+e*x]^(n+2),x] /;
        FreeQ[{F,a,b,c,d,e},x] && NeQ[e^2*(n+2)^2-b^2*c^2*Log[F]^2,0] && LtQ[n,-1] && NeQ[n,-2]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: ["CRC 551h, CRC 542h inverted", "CRC 552h, CRC 543h inverted"],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [capital_f_, c__, a__, b__, d__, e__, n_, x_],
        optional: [c__, a__, b__, d__, e__],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__], x_)
                && neq!(e__.pow(2) * (&n_ + 2).pow(2) - b__.pow(2) * c__.pow(2) * capital_f_.log().pow(2), 0)
                && ltq!(n_, -1)
                && neq!(n_, -2)
        },
        rhs: {
            let exponential = capital_f_.pow(&c__ * (&a__ + &b__ * x_));
            let angle = &d__ + &e__ * x_;
            let denominator = e__.pow(2) * (&n_ + 1) * (&n_ + 2);
            let balance = e__.pow(2) * (&n_ + 2).pow(2) - b__.pow(2) * c__.pow(2) * capital_f_.log().pow(2);
            let recursive = rubi_rhs_int(&(&exponential * angle.cosh().pow(&n_ + 2)), x_);

            rubi_simp(&(&b__ * &c__ * capital_f_.log() * &exponential * angle.cosh().pow(&n_ + 2) / &denominator), x_)
                    - rubi_simp(&(&exponential * angle.sinh() * angle.cosh().pow(&n_ + 1) / (&e__ * (&n_ + 1))), x_)
                    + rubi_star(&balance / &denominator, recursive)
        },
    ));
}

fn push_rules_rule_6005(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, d__, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 6005,
        source: "Int[F_^(c_.*(a_.+b_.*x_))*Sinh[d_.+e_.*x_]^n_,x_Symbol] :=
          E^(n*(d+e*x))*Sinh[d+e*x]^n/(-1+E^(2*(d+e*x)))^n \\[Star] Int[F^(c*(a+b*x))*(-1+E^(2*(d+e*x)))^n/E^(n*(d+e*x)),x] /;
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
            let exponential = capital_f_.pow(&c__ * (&a__ + &b__ * x_));
            let angle = &d__ + &e__ * x_;
            let exp_n_angle = (&n_ * &angle).exp();
            let exp_2_angle = (Atom::num(2) * &angle).exp();
            let transformed_integrand =
                exponential * (-Atom::num(1) + &exp_2_angle).pow(&n_) / &exp_n_angle;
            let recursive = rubi_rhs_int(&transformed_integrand, x_);

            let coefficient =
                exp_n_angle * angle.sinh().pow(&n_) / (-Atom::num(1) + exp_2_angle).pow(&n_);

            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_6006(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, d__, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 6006,
        source: "Int[F_^(c_.*(a_.+b_.*x_))*Cosh[d_.+e_.*x_]^n_,x_Symbol] :=
          E^(n*(d+e*x))*Cosh[d+e*x]^n/(1+E^(2*(d+e*x)))^n \\[Star] Int[F^(c*(a+b*x))*(1+E^(2*(d+e*x)))^n/E^(n*(d+e*x)),x] /;
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
            let exponential = capital_f_.pow(&c__ * (&a__ + &b__ * x_));
            let angle = &d__ + &e__ * x_;
            let exp_n_angle = (&n_ * &angle).exp();
            let exp_2_angle = (Atom::num(2) * &angle).exp();
            let transformed_integrand =
                exponential * (Atom::num(1) + &exp_2_angle).pow(&n_) / &exp_n_angle;
            let recursive = rubi_rhs_int(&transformed_integrand, x_);

            let coefficient =
                exp_n_angle * angle.cosh().pow(&n_) / (Atom::num(1) + exp_2_angle).pow(&n_);

            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_6007(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_f_, a__, b__, c__, d__, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 6007,
        source: "Int[F_^(c_.*(a_.+b_.*x_))*Tanh[d_.+e_.*x_]^n_.,x_Symbol] :=
          Int[ExpandIntegrand[F^(c*(a+b*x))*(-1+E^(2*(d+e*x)))^n/(1+E^(2*(d+e*x)))^n,x],x] /;
        FreeQ[{F,a,b,c,d,e},x] && IntegerQ[n]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: capital_f_.pow(c__ * (a__ + b__ * x_)) * (d__ + e__ * x_).tanh().pow(n_),
        with: [capital_f_, c__, a__, b__, d__, e__, n_, x_],
        optional: [c__, a__, b__, d__, e__, n_],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__], x_)
                && integerq!(n_)
        },
        rhs: {
            let exponential = capital_f_.pow(&c__ * (&a__ + &b__ * x_));
            let angle = &d__ + &e__ * x_;
            let exp_2_angle = (Atom::num(2) * &angle).exp();
            let transformed_integrand =
                exponential * (-Atom::num(1) + &exp_2_angle).pow(&n_) / (Atom::num(1) + &exp_2_angle).pow(&n_);
            let expanded = rubi_expand_integrand(&transformed_integrand, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_6008(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_f_, a__, b__, c__, d__, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 6008,
        source: "Int[F_^(c_.*(a_.+b_.*x_))*Coth[d_.+e_.*x_]^n_.,x_Symbol] :=
          Int[ExpandIntegrand[F^(c*(a+b*x))*(1+E^(2*(d+e*x)))^n/(-1+E^(2*(d+e*x)))^n,x],x] /;
        FreeQ[{F,a,b,c,d,e},x] && IntegerQ[n]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: capital_f_.pow(c__ * (a__ + b__ * x_)) * (d__ + e__ * x_).coth().pow(n_),
        with: [capital_f_, c__, a__, b__, d__, e__, n_, x_],
        optional: [c__, a__, b__, d__, e__, n_],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__], x_)
                && integerq!(n_)
        },
        rhs: {
            let exponential = capital_f_.pow(&c__ * (&a__ + &b__ * x_));
            let angle = &d__ + &e__ * x_;
            let exp_2_angle = (Atom::num(2) * &angle).exp();
            let transformed_integrand =
                exponential * (Atom::num(1) + &exp_2_angle).pow(&n_) / (-Atom::num(1) + &exp_2_angle).pow(&n_);
            let expanded = rubi_expand_integrand(&transformed_integrand, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_6009(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, d__, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 6009,
        source: "Int[F_^(c_.*(a_.+b_.*x_))*Sech[d_.+e_.*x_]^n_,x_Symbol] :=
          -b*c*Log[F]*F^(c*(a+b*x))*(Sech[d+e*x]^n/(e^2*n^2-b^2*c^2*Log[F]^2)) -
          e*n*F^(c*(a+b*x))*Sech[d+e*x]^(n+1)*(Sinh[d+e*x]/(e^2*n^2-b^2*c^2*Log[F]^2)) +
          e^2*n*((n+1)/(e^2*n^2-b^2*c^2*Log[F]^2)) \\[Star] Int[F^(c*(a+b*x))*Sech[d+e*x]^(n+2),x] /;
        FreeQ[{F,a,b,c,d,e},x] && NeQ[e^2*n^2+b^2*c^2*Log[F]^2,0] && LtQ[n,-1]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: ["CRC 552h inverted", "CRC 551h inverted"],
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
            let denominator = e__.pow(2) * n_.pow(2) - b__.pow(2) * c__.pow(2) * capital_f_.log().pow(2);
            let recursive = rubi_rhs_int(&(&exponential * angle.sech().pow(&n_ + 2)), x_);

            rubi_simp(&(-&b__ * &c__ * capital_f_.log() * &exponential * angle.sech().pow(&n_) / &denominator), x_)
                    - rubi_simp(&(&e__ * &n_ * &exponential * angle.sech().pow(&n_ + 1) * angle.sinh() / &denominator), x_)
                    + rubi_star(e__.pow(2) * &n_ * (&n_ + 1) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_6010(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, d__, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 6010,
        source: "Int[F_^(c_.*(a_.+b_.*x_))*Csch[d_.+e_.*x_]^n_,x_Symbol] :=
          -b*c*Log[F]*F^(c*(a+b*x))*(Csch[d+e*x]^n/(e^2*n^2-b^2*c^2*Log[F]^2)) -
          e*n*F^(c*(a+b*x))*Csch[d+e*x]^(n+1)*(Cosh[d+e*x]/(e^2*n^2-b^2*c^2*Log[F]^2)) -
          e^2*n*((n+1)/(e^2*n^2-b^2*c^2*Log[F]^2)) \\[Star] Int[F^(c*(a+b*x))*Csch[d+e*x]^(n+2),x] /;
        FreeQ[{F,a,b,c,d,e},x] && NeQ[e^2*n^2+b^2*c^2*Log[F]^2,0] && LtQ[n,-1]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: ["CRC 552h inverted", "CRC 551h inverted"],
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
            let denominator = e__.pow(2) * n_.pow(2) - b__.pow(2) * c__.pow(2) * capital_f_.log().pow(2);
            let recursive = rubi_rhs_int(&(&exponential * angle.csch().pow(&n_ + 2)), x_);

            rubi_simp(&(-&b__ * &c__ * capital_f_.log() * &exponential * angle.csch().pow(&n_) / &denominator), x_)
                    - rubi_simp(&(&e__ * &n_ * &exponential * angle.csch().pow(&n_ + 1) * angle.cosh() / &denominator), x_)
                    - rubi_star(e__.pow(2) * &n_ * (&n_ + 1) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_6011(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, d__, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 6011,
        source: "Int[F_^(c_.*(a_.+b_.*x_))*Sech[d_.+e_.*x_]^n_,x_Symbol] :=
          b*c*Log[F]*F^(c*(a+b*x))*Sech[d+e*x]^(n-2)/(e^2*(n-1)*(n-2)) +
          F^(c*(a+b*x))*Sech[d+e*x]^(n-1)*Sinh[d+e*x]/(e*(n-1)) /;
        FreeQ[{F,a,b,c,d,e,n},x] && EqQ[e^2*(n-2)^2-b^2*c^2*Log[F]^2,0] && NeQ[n,1] && NeQ[n,2]",
        desc: "Apply the direct antiderivative formula.",
        refs: ["CRC 552h with e2 (n-2)2-b2c2Log[F]2\\[Equal]0", "CRC 551h with e2 (n-2)2-b2c2Log[F]2\\[Equal]0"],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [capital_f_, c__, a__, b__, d__, e__, n_, x_],
        optional: [c__, a__, b__, d__, e__],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__, n_], x_)
                && eqq!(e__.pow(2) * (&n_ - 2).pow(2) - b__.pow(2) * c__.pow(2) * capital_f_.log().pow(2), 0)
                && neq!(n_, 1)
                && neq!(n_, 2)
        },
        rhs: {
            let exponential = capital_f_.pow(&c__ * (&a__ + &b__ * x_));
            let angle = &d__ + &e__ * x_;

            rubi_simp(&(&b__ * &c__ * capital_f_.log() * &exponential * angle.sech().pow(&n_ - 2)
                    / (e__.pow(2) * (&n_ - 1) * (&n_ - 2))), x_)
                    + rubi_simp(&(exponential * angle.sech().pow(&n_ - 1) * angle.sinh() / (&e__ * (&n_ - 1))), x_)
        },
    ));
}

fn push_rules_rule_6012(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, d__, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 6012,
        source: "Int[F_^(c_.*(a_.+b_.*x_))*Csch[d_.+e_.*x_]^n_,x_Symbol] :=
          -b*c*Log[F]*F^(c*(a+b*x))*Csch[d+e*x]^(n-2)/(e^2*(n-1)*(n-2)) -
          F^(c*(a+b*x))*Csch[d+e*x]^(n-1)*Cosh[d+e*x]/(e*(n-1)) /;
        FreeQ[{F,a,b,c,d,e,n},x] && EqQ[e^2*(n-2)^2-b^2*c^2*Log[F]^2,0] && NeQ[n,1] && NeQ[n,2]",
        desc: "Apply the direct antiderivative formula.",
        refs: ["CRC 552h with e2 (n-2)2-b2c2Log[F]2\\[Equal]0", "CRC 551h with e2 (n-2)2-b2c2Log[F]2\\[Equal]0"],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [capital_f_, c__, a__, b__, d__, e__, n_, x_],
        optional: [c__, a__, b__, d__, e__],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__, n_], x_)
                && eqq!(e__.pow(2) * (&n_ - 2).pow(2) - b__.pow(2) * c__.pow(2) * capital_f_.log().pow(2), 0)
                && neq!(n_, 1)
                && neq!(n_, 2)
        },
        rhs: {
            let exponential = capital_f_.pow(&c__ * (&a__ + &b__ * x_));
            let angle = &d__ + &e__ * x_;

            rubi_simp(&(-&b__ * &c__ * capital_f_.log() * &exponential * angle.csch().pow(&n_ - 2)
                    / (e__.pow(2) * (&n_ - 1) * (&n_ - 2))), x_)
                    - rubi_simp(&(exponential * angle.csch().pow(&n_ - 1) * angle.cosh() / (&e__ * (&n_ - 1))), x_)
        },
    ));
}

fn push_rules_rule_6013(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, d__, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 6013,
        source: "Int[F_^(c_.*(a_.+b_.*x_))*Sech[d_.+e_.*x_]^n_,x_Symbol] :=
          b*c*Log[F]*F^(c*(a+b*x))*Sech[d+e*x]^(n-2)/(e^2*(n-1)*(n-2)) +
          F^(c*(a+b*x))*Sech[d+e*x]^(n-1)*Sinh[d+e*x]/(e*(n-1)) +
          (e^2*(n-2)^2-b^2*c^2*Log[F]^2)/(e^2*(n-1)*(n-2)) \\[Star] Int[F^(c*(a+b*x))*Sech[d+e*x]^(n-2),x] /;
        FreeQ[{F,a,b,c,d,e},x] && NeQ[e^2*(n-2)^2-b^2*c^2*Log[F]^2,0] && GtQ[n,1] && NeQ[n,2]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: ["CRC 552h", "CRC 551h"],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [capital_f_, c__, a__, b__, d__, e__, n_, x_],
        optional: [c__, a__, b__, d__, e__],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__], x_)
                && neq!(e__.pow(2) * (&n_ - 2).pow(2) - b__.pow(2) * c__.pow(2) * capital_f_.log().pow(2), 0)
                && gtq!(n_, 1)
                && neq!(n_, 2)
        },
        rhs: {
            let exponential = capital_f_.pow(&c__ * (&a__ + &b__ * x_));
            let angle = &d__ + &e__ * x_;
            let denominator = e__.pow(2) * (&n_ - 1) * (&n_ - 2);
            let balance = e__.pow(2) * (&n_ - 2).pow(2) - b__.pow(2) * c__.pow(2) * capital_f_.log().pow(2);
            let recursive = rubi_rhs_int(&(&exponential * angle.sech().pow(&n_ - 2)), x_);

            rubi_simp(&(&b__ * &c__ * capital_f_.log() * &exponential * angle.sech().pow(&n_ - 2) / &denominator), x_)
                    + rubi_simp(&(&exponential * angle.sech().pow(&n_ - 1) * angle.sinh() / (&e__ * (&n_ - 1))), x_)
                    + rubi_star(&balance / &denominator, recursive)
        },
    ));
}

fn push_rules_rule_6014(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, d__, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 6014,
        source: "Int[F_^(c_.*(a_.+b_.*x_))*Csch[d_.+e_.*x_]^n_,x_Symbol] :=
          -b*c*Log[F]*F^(c*(a+b*x))*Csch[d+e*x]^(n-2)/(e^2*(n-1)*(n-2)) -
          F^(c*(a+b*x))*Csch[d+e*x]^(n-1)*Cosh[d+e*x]/(e*(n-1)) -
          (e^2*(n-2)^2-b^2*c^2*Log[F]^2)/(e^2*(n-1)*(n-2)) \\[Star] Int[F^(c*(a+b*x))*Csch[d+e*x]^(n-2),x] /;
        FreeQ[{F,a,b,c,d,e},x] && NeQ[e^2*(n-2)^2-b^2*c^2*Log[F]^2,0] && GtQ[n,1] && NeQ[n,2]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: ["CRC 552h", "CRC 551h"],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [capital_f_, c__, a__, b__, d__, e__, n_, x_],
        optional: [c__, a__, b__, d__, e__],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__], x_)
                && neq!(e__.pow(2) * (&n_ - 2).pow(2) - b__.pow(2) * c__.pow(2) * capital_f_.log().pow(2), 0)
                && gtq!(n_, 1)
                && neq!(n_, 2)
        },
        rhs: {
            let exponential = capital_f_.pow(&c__ * (&a__ + &b__ * x_));
            let angle = &d__ + &e__ * x_;
            let denominator = e__.pow(2) * (&n_ - 1) * (&n_ - 2);
            let balance = e__.pow(2) * (&n_ - 2).pow(2) - b__.pow(2) * c__.pow(2) * capital_f_.log().pow(2);
            let recursive = rubi_rhs_int(&(&exponential * angle.csch().pow(&n_ - 2)), x_);

            rubi_simp(&(-&b__ * &c__ * capital_f_.log() * &exponential * angle.csch().pow(&n_ - 2) / &denominator), x_)
                    - rubi_simp(&(&exponential * angle.csch().pow(&n_ - 1) * angle.cosh() / (&e__ * (&n_ - 1))), x_)
                    - rubi_star(&balance / &denominator, recursive)
        },
    ));
}

fn push_rules_rule_6015(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, d__, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 6015,
        source: "Int[F_^(c_.*(a_.+b_.*x_))*Sech[d_.+e_.*x_]^n_.,x_Symbol] :=
          2^n*E^(n*(d+e*x))*F^(c*(a+b*x))/(e*n+b*c*Log[F])*Hypergeometric2F1[n,n/2+b*c*Log[F]/(2*e),1+n/2+b*c*Log[F]/(2*e),-E^(2*(d+e*x))] /;
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
            let angle = &d__ + &e__ * x_;
            let exponential = capital_f_.pow(&c__ * (&a__ + &b__ * x_));
            let denominator = &e__ * &n_ + &b__ * &c__ * capital_f_.log();
            let parameter = &n_ / 2 + &b__ * &c__ * capital_f_.log() / (Atom::num(2) * &e__);

            rubi_simp(&(Atom::num(2).pow(&n_)
                    * (&n_ * &angle).exp()
                    * exponential
                    * rubi_hypergeometric2f1(
                        &n_,
                        &parameter,
                        Atom::num(1) + &parameter,
                        -(Atom::num(2) * &angle).exp(),
                    )
                    / denominator), x_)
        },
    ));
}

fn push_rules_rule_6016(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, d__, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 6016,
        source: "Int[F_^(c_.*(a_.+b_.*x_))*Csch[d_.+e_.*x_]^n_.,x_Symbol] :=
          (-2)^n*E^(n*(d+e*x))*F^(c*(a+b*x))/(e*n+b*c*Log[F])*Hypergeometric2F1[n,n/2+b*c*Log[F]/(2*e),1+n/2+b*c*Log[F]/(2*e),E^(2*(d+e*x))] /;
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
            let angle = &d__ + &e__ * x_;
            let exponential = capital_f_.pow(&c__ * (&a__ + &b__ * x_));
            let denominator = &e__ * &n_ + &b__ * &c__ * capital_f_.log();
            let parameter = &n_ / 2 + &b__ * &c__ * capital_f_.log() / (Atom::num(2) * &e__);

            rubi_simp(&((-Atom::num(2)).pow(&n_)
                    * (&n_ * &angle).exp()
                    * exponential
                    * rubi_hypergeometric2f1(
                        &n_,
                        &parameter,
                        Atom::num(1) + &parameter,
                        (Atom::num(2) * &angle).exp(),
                    )
                    / denominator), x_)
        },
    ));
}

fn push_rules_rule_6017(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, d__, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 6017,
        source: "Int[F_^(c_.*(a_.+b_.*x_))*Sech[d_.+e_.*x_]^n_.,x_Symbol] :=
          (1+E^(2*(d+e*x)))^n*Sech[d+e*x]^n/E^(n*(d+e*x)) \\[Star] Int[SimplifyIntegrand[F^(c*(a+b*x))*E^(n*(d+e*x))/(1+E^(2*(d+e*x)))^n,x],x] /;
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
            let angle = &d__ + &e__ * x_;
            let exponential = capital_f_.pow(&c__ * (&a__ + &b__ * x_));
            let exp_n_angle = (&n_ * &angle).exp();
            let exp_2_angle = (Atom::num(2) * &angle).exp();
            let transformed = rubi_simplify_integrand(
                &(exponential * &exp_n_angle / (Atom::num(1) + &exp_2_angle).pow(&n_)),
                x_,
            );
            let recursive = rubi_rhs_int(&transformed, x_);

            let coefficient =
                (Atom::num(1) + exp_2_angle).pow(&n_) * angle.sech().pow(&n_) / exp_n_angle;

            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_6018(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, d__, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 6018,
        source: "Int[F_^(c_.*(a_.+b_.*x_))*Csch[d_.+e_.*x_]^n_.,x_Symbol] :=
          (1-E^(-2*(d+e*x)))^n*Csch[d+e*x]^n/E^(-n*(d+e*x)) \\[Star] Int[SimplifyIntegrand[F^(c*(a+b*x))*E^(-n*(d+e*x))/(1-E^(-2*(d+e*x)))^n,x],x] /;
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
            let angle = &d__ + &e__ * x_;
            let exponential = capital_f_.pow(&c__ * (&a__ + &b__ * x_));
            let exp_minus_n_angle = (-&n_ * &angle).exp();
            let exp_minus_2_angle = (-Atom::num(2) * &angle).exp();
            let transformed = rubi_simplify_integrand(
                &(exponential * &exp_minus_n_angle / (Atom::num(1) - &exp_minus_2_angle).pow(&n_)),
                x_,
            );
            let recursive = rubi_rhs_int(&transformed, x_);

            let coefficient = (Atom::num(1) - exp_minus_2_angle).pow(&n_)
                * angle.csch().pow(&n_)
                / exp_minus_n_angle;

            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_6019(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, d__, e__, f__, g__, n_, x_);
    rules.push(rubi_rule!(
        order: 6019,
        source: "Int[F_^(c_.*(a_.+b_.*x_))*(f_+g_.*Sinh[d_.+e_.*x_])^n_.,x_Symbol] :=
          2^n*f^n \\[Star] Int[F^(c*(a+b*x))*Cosh[d/2-f*Pi/(4*g)+e*x/2]^(2*n),x] /;
        FreeQ[{F,a,b,c,d,e,f,g},x] && EqQ[f^2+g^2,0] && ILtQ[n,0]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [capital_f_, c__, a__, b__, f__, g__, d__, e__, n_, x_],
        optional: [c__, a__, b__, g__, d__, e__, n_],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__, f__, g__], x_)
                && eqq!(f__.pow(2) + g__.pow(2), 0)
                && iltq!(n_, 0)
        },
        rhs: {
            let exponential = capital_f_.pow(&c__ * (&a__ + &b__ * x_));
            let transformed_angle =
                &d__ / 2 + &e__ * x_ / 2 - &f__ * Atom::var(Symbol::PI) / (Atom::num(4) * &g__);
            let recursive_integrand = exponential * transformed_angle.cosh().pow(Atom::num(2) * &n_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            let coefficient = Atom::num(2).pow(&n_) * f__.pow(&n_);

            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_6020(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, d__, e__, f__, g__, n_, x_);
    rules.push(rubi_rule!(
        order: 6020,
        source: "Int[F_^(c_.*(a_.+b_.*x_))*(f_+g_.*Cosh[d_.+e_.*x_])^n_.,x_Symbol] :=
          2^n*g^n \\[Star] Int[F^(c*(a+b*x))*Cosh[d/2+e*x/2]^(2*n),x] /;
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
            let recursive_integrand = exponential * transformed_angle.cosh().pow(Atom::num(2) * &n_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            let coefficient = Atom::num(2).pow(&n_) * g__.pow(&n_);

            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_6021(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, d__, e__, f__, g__, n_, x_);
    rules.push(rubi_rule!(
        order: 6021,
        source: "Int[F_^(c_.*(a_.+b_.*x_))*(f_+g_.*Cosh[d_.+e_.*x_])^n_.,x_Symbol] :=
          2^n*g^n \\[Star] Int[F^(c*(a+b*x))*Sinh[d/2+e*x/2]^(2*n),x] /;
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
            let recursive_integrand = exponential * transformed_angle.sinh().pow(Atom::num(2) * &n_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            let coefficient = Atom::num(2).pow(&n_) * g__.pow(&n_);

            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_6022(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, d__, e__, f__, g__, n_, x_);
    rules.push(rubi_rule!(
        order: 6022,
        source: "Int[F_^(c_.*(a_.+b_.*x_))*(f_+g_.*Sinh[d_.+e_.*x_])^n_.,x_Symbol] :=
          (f+g*Sinh[d+e*x])^n/Cosh[d/2-f*Pi/(4*g)+e*x/2]^(2*n) \\[Star] Int[F^(c*(a+b*x))*Cosh[d/2-f*Pi/(4*g)+e*x/2]^(2*n),x] /;
        FreeQ[{F,a,b,c,d,e,f,g,n},x] && EqQ[f^2+g^2,0] && Not[IntegerQ[n]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [capital_f_, c__, a__, b__, f__, g__, d__, e__, n_, x_],
        optional: [c__, a__, b__, g__, d__, e__, n_],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__, f__, g__, n_], x_)
                && eqq!(f__.pow(2) + g__.pow(2), 0)
                && !integerq!(n_)
        },
        rhs: {
            let angle = &d__ + &e__ * x_;
            let transformed_angle =
                &d__ / 2 + &e__ * x_ / 2 - &f__ * Atom::var(Symbol::PI) / (Atom::num(4) * &g__);
            let exponential = capital_f_.pow(&c__ * (&a__ + &b__ * x_));
            let transformed_power = transformed_angle.cosh().pow(Atom::num(2) * &n_);
            let recursive = rubi_rhs_int(&(exponential * &transformed_power), x_);
            let coefficient =
                (&f__ + &g__ * angle.sinh()).pow(&n_) / transformed_power;

            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_6023(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, d__, e__, f__, g__, n_, x_);
    rules.push(rubi_rule!(
        order: 6023,
        source: "Int[F_^(c_.*(a_.+b_.*x_))*(f_+g_.*Cosh[d_.+e_.*x_])^n_.,x_Symbol] :=
          (f+g*Cosh[d+e*x])^n/Cosh[d/2+e*x/2]^(2*n) \\[Star] Int[F^(c*(a+b*x))*Cosh[d/2+e*x/2]^(2*n),x] /;
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
            let angle = &d__ + &e__ * x_;
            let transformed_angle = &d__ / 2 + &e__ * x_ / 2;
            let exponential = capital_f_.pow(&c__ * (&a__ + &b__ * x_));
            let transformed_power = transformed_angle.cosh().pow(Atom::num(2) * &n_);
            let recursive = rubi_rhs_int(&(exponential * &transformed_power), x_);
            let coefficient =
                (&f__ + &g__ * angle.cosh()).pow(&n_) / transformed_power;

            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_6024(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, d__, e__, f__, g__, n_, x_);
    rules.push(rubi_rule!(
        order: 6024,
        source: "Int[F_^(c_.*(a_.+b_.*x_))*(f_+g_.*Cosh[d_.+e_.*x_])^n_.,x_Symbol] :=
          (f+g*Cosh[d+e*x])^n/Sinh[d/2+e*x/2]^(2*n) \\[Star] Int[F^(c*(a+b*x))*Sinh[d/2+e*x/2]^(2*n),x] /;
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
            let angle = &d__ + &e__ * x_;
            let transformed_angle = &d__ / 2 + &e__ * x_ / 2;
            let exponential = capital_f_.pow(&c__ * (&a__ + &b__ * x_));
            let transformed_power = transformed_angle.sinh().pow(Atom::num(2) * &n_);
            let recursive = rubi_rhs_int(&(exponential * &transformed_power), x_);
            let coefficient =
                (&f__ + &g__ * angle.cosh()).pow(&n_) / transformed_power;

            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_6025(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_f_, a__, b__, c__, d__, e__, f__, g__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 6025,
        source: "Int[F_^(c_.*(a_.+b_.*x_))*Cosh[d_.+e_.*x_]^m_.*(f_+g_.*Sinh[d_.+e_.*x_])^n_.,x_Symbol] :=
          g^n \\[Star] Int[F^(c*(a+b*x))*Tanh[d/2+e*x/2-f*Pi/(4*g)]^m,x] /;
        FreeQ[{F,a,b,c,d,e,f,g},x] && EqQ[f^2+g^2,0] && IntegersQ[m,n] && EqQ[m+n,0]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: capital_f_.pow(c__ * (a__ + b__ * x_))
            * (d__ + e__ * x_).cosh().pow(m_)
            * (f__ + g__ * (d__ + e__ * x_).sinh()).pow(n_),
        with: [capital_f_, c__, a__, b__, d__, e__, m_, f__, g__, n_, x_],
        optional: [c__, a__, b__, d__, e__, m_, g__, n_],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__, f__, g__], x_)
                && eqq!(f__.pow(2) + g__.pow(2), 0)
                && integersq!([m_, n_])
                && eqq!(&m_ + &n_, 0)
        },
        rhs: {
            let exponential = capital_f_.pow(&c__ * (&a__ + &b__ * x_));
            let transformed_angle =
                &d__ / 2 + &e__ * x_ / 2 - &f__ * Atom::var(Symbol::PI) / (Atom::num(4) * &g__);
            let recursive_integrand = exponential * transformed_angle.tanh().pow(&m_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(g__.pow(&n_), recursive)
        },
    ));
}

fn push_rules_rule_6026(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, d__, e__, f__, g__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 6026,
        source: "Int[F_^(c_.*(a_.+b_.*x_))*Sinh[d_.+e_.*x_]^m_.*(f_+g_.*Cosh[d_.+e_.*x_])^n_.,x_Symbol] :=
          g^n \\[Star] Int[F^(c*(a+b*x))*Tanh[d/2+e*x/2]^m,x] /;
        FreeQ[{F,a,b,c,d,e,f,g},x] && EqQ[f-g,0] && IntegersQ[m,n] && EqQ[m+n,0]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [capital_f_, c__, a__, b__, d__, e__, m_, f__, g__, n_, x_],
        optional: [c__, a__, b__, d__, e__, m_, g__, n_],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__, f__, g__], x_)
                && eqq!(&f__ - &g__, 0)
                && integersq!([m_, n_])
                && eqq!(&m_ + &n_, 0)
        },
        rhs: {
            let exponential = capital_f_.pow(&c__ * (&a__ + &b__ * x_));
            let transformed_angle = &d__ / 2 + &e__ * x_ / 2;
            let recursive_integrand = exponential * transformed_angle.tanh().pow(&m_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(g__.pow(&n_), recursive)
        },
    ));
}

fn push_rules_rule_6027(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_f_, a__, b__, c__, d__, e__, f__, g__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 6027,
        source: "Int[F_^(c_.*(a_.+b_.*x_))*Sinh[d_.+e_.*x_]^m_.*(f_+g_.*Cosh[d_.+e_.*x_])^n_.,x_Symbol] :=
          g^n \\[Star] Int[F^(c*(a+b*x))*Coth[d/2+e*x/2]^m,x] /;
        FreeQ[{F,a,b,c,d,e,f,g},x] && EqQ[f+g,0] && IntegersQ[m,n] && EqQ[m+n,0]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [capital_f_, c__, a__, b__, d__, e__, m_, f__, g__, n_, x_],
        optional: [c__, a__, b__, d__, e__, m_, g__, n_],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__, f__, g__], x_)
                && eqq!(&f__ + &g__, 0)
                && integersq!([m_, n_])
                && eqq!(&m_ + &n_, 0)
        },
        rhs: {
            let exponential = capital_f_.pow(&c__ * (&a__ + &b__ * x_));
            let transformed_angle = &d__ / 2 + &e__ * x_ / 2;
            let recursive_integrand = exponential * transformed_angle.coth().pow(&m_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(g__.pow(&n_), recursive)
        },
    ));
}

fn push_rules_rule_6028(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_f_, a__, b__, c__, d__, e__, f__, g__, h__, i__, x_);
    rules.push(rubi_rule!(
        order: 6028,
        source: "Int[F_^(c_.*(a_.+b_.*x_))*(h_+i_.*Cosh[d_.+e_.*x_])/(f_+g_.*Sinh[d_.+e_.*x_]),x_Symbol] :=
          2*i \\[Star] Int[F^(c*(a+b*x))*(Cosh[d+e*x]/(f+g*Sinh[d+e*x])),x] +
          Int[F^(c*(a+b*x))*((h-i*Cosh[d+e*x])/(f+g*Sinh[d+e*x])),x] /;
        FreeQ[{F,a,b,c,d,e,f,g,h,i},x] && EqQ[f^2+g^2,0] && EqQ[h^2-i^2,0] && EqQ[g*h-f*i,0]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: capital_f_.pow(c__ * (a__ + b__ * x_))
            * (h__ + i__ * (d__ + e__ * x_).cosh())
            / (f__ + g__ * (d__ + e__ * x_).sinh()),
        with: [capital_f_, c__, a__, b__, h__, i__, d__, e__, f__, g__, x_],
        optional: [c__, a__, b__, i__, d__, e__, g__],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__, f__, g__, h__, i__], x_)
                && eqq!(f__.pow(2) + g__.pow(2), 0)
                && eqq!(h__.pow(2) - i__.pow(2), 0)
                && eqq!(&g__ * &h__ - &f__ * &i__, 0)
        },
        rhs: {
            let angle = &d__ + &e__ * x_;
            let exponential = capital_f_.pow(&c__ * (&a__ + &b__ * x_));
            let denominator = &f__ + &g__ * angle.sinh();
            let first = rubi_rhs_int(&(&exponential * angle.cosh() / &denominator), x_);
            let second =
                rubi_rhs_int(&(exponential * ((&h__ - &i__ * angle.cosh()) / denominator)), x_);

            rubi_star(Atom::num(2) * &i__, first) + second
        },
    ));
}

fn push_rules_rule_6029(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_f_, a__, b__, c__, d__, e__, f__, g__, h__, i__, x_);
    rules.push(rubi_rule!(
        order: 6029,
        source: "Int[F_^(c_.*(a_.+b_.*x_))*(h_+i_.*Sinh[d_.+e_.*x_])/(f_+g_.*Cosh[d_.+e_.*x_]),x_Symbol] :=
          2*i \\[Star] Int[F^(c*(a+b*x))*(Sinh[d+e*x]/(f+g*Cosh[d+e*x])),x] +
          Int[F^(c*(a+b*x))*((h-i*Sinh[d+e*x])/(f+g*Cosh[d+e*x])),x] /;
        FreeQ[{F,a,b,c,d,e,f,g,h,i},x] && EqQ[f^2-g^2,0] && EqQ[h^2+i^2,0] && EqQ[g*h+f*i,0]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: capital_f_.pow(c__ * (a__ + b__ * x_))
            * (h__ + i__ * (d__ + e__ * x_).sinh())
            / (f__ + g__ * (d__ + e__ * x_).cosh()),
        with: [capital_f_, c__, a__, b__, h__, i__, d__, e__, f__, g__, x_],
        optional: [c__, a__, b__, i__, d__, e__, g__],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__, f__, g__, h__, i__], x_)
                && eqq!(f__.pow(2) - g__.pow(2), 0)
                && eqq!(h__.pow(2) + i__.pow(2), 0)
                && eqq!(&g__ * &h__ + &f__ * &i__, 0)
        },
        rhs: {
            let angle = &d__ + &e__ * x_;
            let exponential = capital_f_.pow(&c__ * (&a__ + &b__ * x_));
            let denominator = &f__ + &g__ * angle.cosh();
            let first = rubi_rhs_int(&(&exponential * angle.sinh() / &denominator), x_);
            let second =
                rubi_rhs_int(&(exponential * ((&h__ - &i__ * angle.sinh()) / denominator)), x_);

            rubi_star(Atom::num(2) * &i__, first) + second
        },
    ));
}

fn push_rules_rule_6030(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_f_, c__, capital_g_, n_, u_, v_);
    rules.push(rubi_rule!(
        order: 6030,
        source: "Int[F_^(c_.*u_)*G_[v_]^n_.,x_Symbol] :=
          Int[F^(c*ExpandToSum[u,x])*G[ExpandToSum[v,x]]^n,x] /;
        FreeQ[{F,c,n},x] && HyperbolicQ[G] && LinearQ[{u,v},x] && Not[LinearMatchQ[{u,v},x]]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: capital_f_.pow(c__ * u_) * capital_g_.call(v_).pow(n_),
        with: [capital_f_, c__, u_, capital_g_, v_, n_, x_],
        optional: [c__, n_],
        when: {
            freeq!([capital_f_, c__, n_], x_)
                && rubi_hyperbolic_head_q(&capital_g_)
                && rubi_linear_q_list(&[&u_, &v_], x_)
                && !rubi_linear_match_q_list(&[&u_, &v_], x_)
        },
        rhs: {
            let expanded_u = rubi_expand_to_sum(&u_, x_);
            let expanded_v = rubi_expand_to_sum(&v_, x_);
            let capital_g_ = rubi_function_head_symbol(&capital_g_).unwrap();
            let integrand =
                capital_f_.pow(&c__ * expanded_u) * capital_g_.call(expanded_v).pow(&n_);

            rubi_rhs_int(&integrand, x_)
        },
    ));
}

fn push_rules_rule_6031(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_f_, a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 6031,
        source: "Int[(f_.*x_)^m_.*F_^(c_.*(a_.+b_.*x_))*Sinh[d_.+e_.*x_]^n_.,x_Symbol] :=
          Module[{u=IntHide[F^(c*(a+b*x))*Sinh[d+e*x]^n,x]},
          (f*x)^m \\[Star] u - f*m \\[Star] Int[(f*x)^(m-1)*u,x]] /;
        FreeQ[{F,a,b,c,d,e,f},x] && IGtQ[n,0] && GtQ[m,0]",
        desc: "Integration by parts",
        refs: [],
        pattern: (f__ * x_).pow(m_)
            * capital_f_.pow(c__ * (a__ + b__ * x_))
            * (d__ + e__ * x_).sinh().pow(n_),
        with: [f__, m_, capital_f_, c__, a__, b__, d__, e__, n_, x_],
        optional: [f__, m_, c__, a__, b__, d__, e__, n_],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__, f__], x_)
                && igtq!(n_, 0)
                && gtq!(m_, 0)
        },
        rhs: {
            let linear = &f__ * x_;
            let exponential = capital_f_.pow(&c__ * (&a__ + &b__ * x_));
            let angle = &d__ + &e__ * x_;
            let hidden = rubi_int_hide(&(exponential * angle.sinh().pow(&n_)), x_).rubi_rhs();
            let recursive = rubi_rhs_int(&(linear.pow(&m_ - 1) * &hidden), x_);

            rubi_star(linear.pow(&m_), hidden)
                    - rubi_star(&f__ * &m_, recursive)
        },
    ));
}

fn push_rules_rule_6032(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_f_, a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 6032,
        source: "Int[(f_.*x_)^m_.*F_^(c_.*(a_.+b_.*x_))*Cosh[d_.+e_.*x_]^n_.,x_Symbol] :=
          Module[{u=IntHide[F^(c*(a+b*x))*Cosh[d+e*x]^n,x]},
          (f*x)^m \\[Star] u - f*m \\[Star] Int[(f*x)^(m-1)*u,x]] /;
        FreeQ[{F,a,b,c,d,e,f},x] && IGtQ[n,0] && GtQ[m,0]",
        desc: "Integration by parts",
        refs: [],
        pattern: (f__ * x_).pow(m_)
            * capital_f_.pow(c__ * (a__ + b__ * x_))
            * (d__ + e__ * x_).cosh().pow(n_),
        with: [f__, m_, capital_f_, c__, a__, b__, d__, e__, n_, x_],
        optional: [f__, m_, c__, a__, b__, d__, e__, n_],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__, f__], x_)
                && igtq!(n_, 0)
                && gtq!(m_, 0)
        },
        rhs: {
            let linear = &f__ * x_;
            let exponential = capital_f_.pow(&c__ * (&a__ + &b__ * x_));
            let angle = &d__ + &e__ * x_;
            let hidden = rubi_int_hide(&(exponential * angle.cosh().pow(&n_)), x_).rubi_rhs();
            let recursive = rubi_rhs_int(&(linear.pow(&m_ - 1) * &hidden), x_);

            rubi_star(linear.pow(&m_), hidden)
                    - rubi_star(&f__ * &m_, recursive)
        },
    ));
}

fn push_rules_rule_6033(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_f_, a__, b__, c__, d__, e__, f__, m_, x_);
    rules.push(rubi_rule!(
        order: 6033,
        source: "Int[(f_.*x_)^m_*F_^(c_.*(a_.+b_.*x_))*Sinh[d_.+e_.*x_],x_Symbol] :=
          (f*x)^(m+1)/(f*(m+1))*F^(c*(a+b*x))*Sinh[d+e*x] -
          e/(f*(m+1)) \\[Star] Int[(f*x)^(m+1)*F^(c*(a+b*x))*Cosh[d+e*x],x] -
          b*c*Log[F]/(f*(m+1)) \\[Star] Int[(f*x)^(m+1)*F^(c*(a+b*x))*Sinh[d+e*x],x] /;
        FreeQ[{F,a,b,c,d,e,f,m},x] && (LtQ[m,-1] || SumSimplerQ[m,1])",
        desc: "Integration by parts",
        refs: [],
        pattern: (f__ * x_).pow(m_) * capital_f_.pow(c__ * (a__ + b__ * x_)) * (d__ + e__ * x_).sinh(),
        with: [f__, m_, capital_f_, c__, a__, b__, d__, e__, x_],
        optional: [f__, c__, a__, b__, d__, e__],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__, f__, m_], x_)
                && (ltq!(m_, -1) || sum_simplerq!(m_, 1))
        },
        rhs: {
            let linear = &f__ * x_;
            let exponential = capital_f_.pow(&c__ * (&a__ + &b__ * x_));
            let angle = &d__ + &e__ * x_;
            let denominator = &f__ * (&m_ + 1);
            let raised_linear = linear.pow(&m_ + 1);
            let cosh_recursive =
                rubi_rhs_int(&(&raised_linear * &exponential * angle.cosh()), x_);
            let sinh_recursive =
                rubi_rhs_int(&(&raised_linear * &exponential * angle.sinh()), x_);

            rubi_simp(&(raised_linear * &exponential * angle.sinh() / &denominator), x_)
                    - rubi_star(&e__ / &denominator, cosh_recursive)
                    - rubi_star(&b__ * &c__ * capital_f_.log() / denominator, sinh_recursive)
        },
    ));
}

fn push_rules_rule_6034(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_f_, a__, b__, c__, d__, e__, f__, m_, x_);
    rules.push(rubi_rule!(
        order: 6034,
        source: "Int[(f_.*x_)^m_*F_^(c_.*(a_.+b_.*x_))*Cosh[d_.+e_.*x_],x_Symbol] :=
          (f*x)^(m+1)/(f*(m+1))*F^(c*(a+b*x))*Cosh[d+e*x] -
          e/(f*(m+1)) \\[Star] Int[(f*x)^(m+1)*F^(c*(a+b*x))*Sinh[d+e*x],x] -
          b*c*Log[F]/(f*(m+1)) \\[Star] Int[(f*x)^(m+1)*F^(c*(a+b*x))*Cosh[d+e*x],x] /;
        FreeQ[{F,a,b,c,d,e,f,m},x] && (LtQ[m,-1] || SumSimplerQ[m,1])",
        desc: "Integration by parts",
        refs: [],
        pattern: (f__ * x_).pow(m_) * capital_f_.pow(c__ * (a__ + b__ * x_)) * (d__ + e__ * x_).cosh(),
        with: [f__, m_, capital_f_, c__, a__, b__, d__, e__, x_],
        optional: [f__, c__, a__, b__, d__, e__],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__, f__, m_], x_)
                && (ltq!(m_, -1) || sum_simplerq!(m_, 1))
        },
        rhs: {
            let linear = &f__ * x_;
            let exponential = capital_f_.pow(&c__ * (&a__ + &b__ * x_));
            let angle = &d__ + &e__ * x_;
            let denominator = &f__ * (&m_ + 1);
            let raised_linear = linear.pow(&m_ + 1);
            let sinh_recursive =
                rubi_rhs_int(&(&raised_linear * &exponential * angle.sinh()), x_);
            let cosh_recursive =
                rubi_rhs_int(&(&raised_linear * &exponential * angle.cosh()), x_);

            rubi_simp(&(raised_linear * &exponential * angle.cosh() / &denominator), x_)
                    - rubi_star(&e__ / &denominator, sinh_recursive)
                    - rubi_star(&b__ * &c__ * capital_f_.log() / denominator, cosh_recursive)
        },
    ));
}

fn push_rules_rule_6035(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_f_, a__, b__, c__, d__, e__, f__, g__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 6035,
        source: "Int[F_^(c_.*(a_.+b_.*x_))*Sinh[d_.+e_.*x_]^m_.*Cosh[f_.+g_.*x_]^n_.,x_Symbol] :=
          Int[ExpandTrigReduce[F^(c*(a+b*x)),Sinh[d+e*x]^m*Cosh[f+g*x]^n,x],x] /;
        FreeQ[{F,a,b,c,d,e,f,g},x] && IGtQ[m,0] && IGtQ[n,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: capital_f_.pow(c__ * (a__ + b__ * x_))
            * (d__ + e__ * x_).sinh().pow(m_)
            * (f__ + g__ * x_).cosh().pow(n_),
        with: [capital_f_, c__, a__, b__, d__, e__, m_, f__, g__, n_, x_],
        optional: [c__, a__, b__, d__, e__, m_, f__, g__, n_],
        when: {
            freeq!([capital_f_, a__, b__, c__, d__, e__, f__, g__], x_)
                && igtq!(m_, 0)
                && igtq!(n_, 0)
        },
        rhs: {
            let multiplier = capital_f_.pow(&c__ * (&a__ + &b__ * x_));
            let product =
                (&d__ + &e__ * x_).sinh().pow(&m_) * (&f__ + &g__ * x_).cosh().pow(&n_);
            let expanded = rubi_expand_trig_reduce(&multiplier, &product, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_6036(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        capital_f_, a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_
    );
    rules.push(rubi_rule!(
        order: 6036,
        source: "Int[x_^p_.*F_^(c_.*(a_.+b_.*x_))*Sinh[d_.+e_.*x_]^m_.*Cosh[f_.+g_.*x_]^n_.,x_Symbol] :=
          Int[ExpandTrigReduce[x^p*F^(c*(a+b*x)),Sinh[d+e*x]^m*Cosh[f+g*x]^n,x],x] /;
        FreeQ[{F,a,b,c,d,e,f,g},x] && IGtQ[m,0] && IGtQ[n,0] && IGtQ[p,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: x_.pow(p_)
            * capital_f_.pow(c__ * (a__ + b__ * x_))
            * (d__ + e__ * x_).sinh().pow(m_)
            * (f__ + g__ * x_).cosh().pow(n_),
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
            let product =
                (&d__ + &e__ * x_).sinh().pow(&m_) * (&f__ + &g__ * x_).cosh().pow(&n_);
            let expanded = rubi_expand_trig_reduce(&multiplier, &product, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_6037(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        capital_f_, a__, b__, c__, d__, e__, capital_g_, capital_h_, m_, n_, x_
    );
    rules.push(rubi_rule!(
        order: 6037,
        source: "Int[F_^(c_.*(a_.+b_.*x_))*G_[d_.+e_.*x_]^m_.*H_[d_.+e_.*x_]^n_.,x_Symbol] :=
          Int[ExpandTrigToExp[F^(c*(a+b*x)),G[d+e*x]^m*H[d+e*x]^n,x],x] /;
        FreeQ[{F,a,b,c,d,e},x] && IGtQ[m,0] && IGtQ[n,0] && HyperbolicQ[G] && HyperbolicQ[H]",
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
                && rubi_hyperbolic_head_q(&capital_g_)
                && rubi_hyperbolic_head_q(&capital_h_)
        },
        rhs: {
            let multiplier = capital_f_.pow(&c__ * (&a__ + &b__ * x_));
            let angle = &d__ + &e__ * x_;
            let product =
                rubi_function_head_symbol(&capital_g_).rubi_rhs().call( &angle).pow(&m_) * rubi_function_head_symbol(&capital_h_).rubi_rhs().call( angle).pow(&n_);
            let expanded = rubi_expand_hyperbolic_trig_to_exp(&multiplier, &product, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_6038(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_f_, n_, u_, v_);
    rules.push(rubi_rule!(
        order: 6038,
        source: "Int[F_^u_*Sinh[v_]^n_.,x_Symbol] :=
          Int[ExpandTrigToExp[F^u,Sinh[v]^n,x],x] /;
        FreeQ[F,x] && (LinearQ[u,x] || PolyQ[u,x,2]) && (LinearQ[v,x] || PolyQ[v,x,2]) && IGtQ[n,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: capital_f_.pow(u_) * Atom::var(v_).sinh().pow(n_),
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
            let product = v_.sinh().pow(&n_);
            let expanded = rubi_expand_hyperbolic_trig_to_exp(&multiplier, &product, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_6039(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_f_, n_, u_, v_);
    rules.push(rubi_rule!(
        order: 6039,
        source: "Int[F_^u_*Cosh[v_]^n_.,x_Symbol] :=
          Int[ExpandTrigToExp[F^u,Cosh[v]^n,x],x] /;
        FreeQ[F,x] && (LinearQ[u,x] || PolyQ[u,x,2]) && (LinearQ[v,x] || PolyQ[v,x,2]) && IGtQ[n,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: capital_f_.pow(u_) * Atom::var(v_).cosh().pow(n_),
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
            let product = v_.cosh().pow(&n_);
            let expanded = rubi_expand_hyperbolic_trig_to_exp(&multiplier, &product, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_6040(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_f_, m_, n_, u_, v_);
    rules.push(rubi_rule!(
        order: 6040,
        source: "Int[F_^u_*Sinh[v_]^m_.*Cosh[v_]^n_.,x_Symbol] :=
          Int[ExpandTrigToExp[F^u,Sinh[v]^m*Cosh[v]^n,x],x] /;
        FreeQ[F,x] && (LinearQ[u,x] || PolyQ[u,x,2]) && (LinearQ[v,x] || PolyQ[v,x,2]) && IGtQ[m,0] && IGtQ[n,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: capital_f_.pow(u_) * Atom::var(v_).sinh().pow(m_) * Atom::var(v_).cosh().pow(n_),
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
            let product = v_.sinh().pow(&m_) * v_.cosh().pow(&n_);
            let expanded = rubi_expand_hyperbolic_trig_to_exp(&multiplier, &product, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn downvalues_5997_through_6040_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .filter(|order| (5997..=6040).contains(order))
            .collect::<Vec<_>>();
        assert_eq!(orders, (5997..=6040).collect::<Vec<_>>());
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
    capital_f_.pow(c__ * (a__ + b__ * x_)) * (d__ + e__ * x_).cosh().pow(n_)
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
    capital_f_.pow(c__ * (a__ + b__ * x_)) * (d__ + e__ * x_).csch().pow(n_)
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
    capital_f_.pow(c__ * (a__ + b__ * x_)) * (d__ + e__ * x_).sech().pow(n_)
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
        * (d__ + e__ * x_).sinh().pow(m_)
        * (f__ + g__ * (d__ + e__ * x_).cosh()).pow(n_)
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
    capital_f_.pow(c__ * (a__ + b__ * x_)) * (d__ + e__ * x_).sinh().pow(n_)
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
    capital_f_.pow(c__ * (a__ + b__ * x_)) * (f__ + g__ * (d__ + e__ * x_).cosh()).pow(n_)
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
    capital_f_.pow(c__ * (a__ + b__ * x_)) * (f__ + g__ * (d__ + e__ * x_).sinh()).pow(n_)
}
