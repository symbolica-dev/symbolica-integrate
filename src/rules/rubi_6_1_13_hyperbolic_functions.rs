use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_5897(rules);
    push_rules_rule_5898(rules);
    push_rules_rule_5899(rules);
    push_rules_rule_5900(rules);
    push_rules_rule_5901(rules);
    push_rules_rule_5902(rules);
    push_rules_rule_5903(rules);
    push_rules_rule_5904(rules);
    push_rules_rule_5905(rules);
    push_rules_rule_5906(rules);
    push_rules_rule_5907(rules);
    push_rules_rule_5908(rules);
    push_rules_rule_5909(rules);
    push_rules_rule_5910(rules);
    push_rules_rule_5911(rules);
    push_rules_rule_5912(rules);
    push_rules_rule_5913(rules);
    push_rules_rule_5914(rules);
    push_rules_rule_5915(rules);
    push_rules_rule_5916(rules);
    push_rules_rule_5917(rules);
    push_rules_rule_5918(rules);
    push_rules_rule_5919(rules);
    push_rules_rule_5920(rules);
}

fn push_rules_rule_5897(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, x_);
    rules.push(rubi_rule!(
        order: 5897,
        source: "Int[Sinh[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
          1/2 \\[Star] Int[E^(a+b*x+c*x^2),x] - 1/2 \\[Star] Int[E^(-a-b*x-c*x^2),x] /;
        FreeQ[{a,b,c},x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (a__ + b__ * x_ + c__ * x_.pow(2)).sinh(),
        with: [a__, b__, c__, x_],
        optional: [a__, b__, c__],
        when: { freeq!([a__, b__, c__], x_) },
        rhs: {
            let angle = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            rubi_star(Atom::num(1) / 2, rubi_rhs_int(&angle.exp(), x_)) - rubi_star(Atom::num(1) / 2, rubi_rhs_int(&(-angle).exp(), x_))
        },
    ));
}

fn push_rules_rule_5898(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, x_);
    rules.push(rubi_rule!(
        order: 5898,
        source: "Int[Cosh[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
          1/2 \\[Star] Int[E^(a+b*x+c*x^2),x] + 1/2 \\[Star] Int[E^(-a-b*x-c*x^2),x] /;
        FreeQ[{a,b,c},x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (a__ + b__ * x_ + c__ * x_.pow(2)).cosh(),
        with: [a__, b__, c__, x_],
        optional: [a__, b__, c__],
        when: { freeq!([a__, b__, c__], x_) },
        rhs: {
            let angle = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            rubi_star(Atom::num(1) / 2, rubi_rhs_int(&angle.exp(), x_)) + rubi_star(Atom::num(1) / 2, rubi_rhs_int(&(-angle).exp(), x_))
        },
    ));
}

fn push_rules_rule_5899(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, n_, x_);
    rules.push(rubi_rule!(
        order: 5899,
        source: "Int[Sinh[a_.+b_.*x_+c_.*x_^2]^n_,x_Symbol] :=
          Int[ExpandTrigReduce[Sinh[a+b*x+c*x^2]^n,x],x] /;
        FreeQ[{a,b,c},x] && IGtQ[n,1]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (a__ + b__ * x_ + c__ * x_.pow(2)).sinh().pow(n_),
        with: [a__, b__, c__, n_, x_],
        optional: [a__, b__, c__],
        when: { freeq!([a__, b__, c__], x_) && igtq!(n_, 1) },
        rhs: {
            let power = (&a__ + &b__ * x_ + &c__ * x_.pow(2)).sinh().pow(&n_);
            rubi_rhs_int(
                &rubi_expand_trig_reduce(&Atom::num(1), &power, x_),
                x_,
            )
        },
    ));
}

fn push_rules_rule_5900(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, n_, x_);
    rules.push(rubi_rule!(
        order: 5900,
        source: "Int[Cosh[a_.+b_.*x_+c_.*x_^2]^n_,x_Symbol] :=
          Int[ExpandTrigReduce[Cosh[a+b*x+c*x^2]^n,x],x] /;
        FreeQ[{a,b,c},x] && IGtQ[n,1]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (a__ + b__ * x_ + c__ * x_.pow(2)).cosh().pow(n_),
        with: [a__, b__, c__, n_, x_],
        optional: [a__, b__, c__],
        when: { freeq!([a__, b__, c__], x_) && igtq!(n_, 1) },
        rhs: {
            let power = (&a__ + &b__ * x_ + &c__ * x_.pow(2)).cosh().pow(&n_);
            rubi_rhs_int(
                &rubi_expand_trig_reduce(&Atom::num(1), &power, x_),
                x_,
            )
        },
    ));
}

fn push_rules_rule_5901(rules: &mut Vec<RubiRule>) {
    rubi_symb!(n_, v_);
    rules.push(rubi_rule!(
        order: 5901,
        source: "Int[Sinh[v_]^n_.,x_Symbol] :=
          Int[Sinh[ExpandToSum[v,x]]^n,x] /;
        IGtQ[n,0] && QuadraticQ[v,x] && Not[QuadraticMatchQ[v,x]]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: Atom::var(v_).sinh().pow(n_),
        with: [v_, n_, x_],
        optional: [n_],
        when: { igtq!(n_, 0) && rubi_quadratic_q(&v_, x_) && !rubi_quadratic_match_q(&v_, x_) },
        rhs: {
            let expanded = rubi_expand_to_sum(&v_, x_);
            rubi_rhs_int(&expanded.sinh().pow(&n_), x_)
        },
    ));
}

fn push_rules_rule_5902(rules: &mut Vec<RubiRule>) {
    rubi_symb!(n_, v_);
    rules.push(rubi_rule!(
        order: 5902,
        source: "Int[Cosh[v_]^n_.,x_Symbol] :=
          Int[Cosh[ExpandToSum[v,x]]^n,x] /;
        IGtQ[n,0] && QuadraticQ[v,x] && Not[QuadraticMatchQ[v,x]]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: Atom::var(v_).cosh().pow(n_),
        with: [v_, n_, x_],
        optional: [n_],
        when: { igtq!(n_, 0) && rubi_quadratic_q(&v_, x_) && !rubi_quadratic_match_q(&v_, x_) },
        rhs: {
            let expanded = rubi_expand_to_sum(&v_, x_);
            rubi_rhs_int(&expanded.cosh().pow(&n_), x_)
        },
    ));
}

fn push_rules_rule_5903(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 5903,
        source: "Int[(d_.+e_.*x_)*Sinh[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
          e*Cosh[a+b*x+c*x^2]/(2*c) /;
        FreeQ[{a,b,c,d,e},x] && EqQ[b*e-2*c*d,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [d__, e__, a__, b__, c__, x_],
        optional: [d__, e__, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(&b__ * &e__ - Atom::num(2) * &c__ * &d__, 0)
        },
        rhs: {
            let angle = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            rubi_simp(&(&e__ * angle.cosh() / (Atom::num(2) * c__)), x_)
        },
    ));
}

fn push_rules_rule_5904(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 5904,
        source: "Int[(d_.+e_.*x_)*Cosh[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
          e*Sinh[a+b*x+c*x^2]/(2*c) /;
        FreeQ[{a,b,c,d,e},x] && EqQ[b*e-2*c*d,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [d__, e__, a__, b__, c__, x_],
        optional: [d__, e__, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(&b__ * &e__ - Atom::num(2) * &c__ * &d__, 0)
        },
        rhs: {
            let angle = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            rubi_simp(&(&e__ * angle.sinh() / (Atom::num(2) * c__)), x_)
        },
    ));
}

fn push_rules_rule_5905(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 5905,
        source: "Int[(d_.+e_.*x_)*Sinh[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
          e*Cosh[a+b*x+c*x^2]/(2*c) -
          (b*e-2*c*d)/(2*c) \\[Star] Int[Sinh[a+b*x+c*x^2],x] /;
        FreeQ[{a,b,c,d,e},x] && NeQ[b*e-2*c*d,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [d__, e__, a__, b__, c__, x_],
        optional: [d__, e__, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && neq!(&b__ * &e__ - Atom::num(2) * &c__ * &d__, 0)
        },
        rhs: {
            let angle = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let mismatch = &b__ * &e__ - Atom::num(2) * &c__ * &d__;
            rubi_simp(&(&e__ * &angle.cosh() / (Atom::num(2) * &c__)), x_)
                    - rubi_star(mismatch / (Atom::num(2) * &c__), rubi_rhs_int(&angle.sinh(), x_))
        },
    ));
}

fn push_rules_rule_5906(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 5906,
        source: "Int[(d_.+e_.*x_)*Cosh[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
          e*Sinh[a+b*x+c*x^2]/(2*c) -
          (b*e-2*c*d)/(2*c) \\[Star] Int[Cosh[a+b*x+c*x^2],x] /;
        FreeQ[{a,b,c,d,e},x] && NeQ[b*e-2*c*d,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [d__, e__, a__, b__, c__, x_],
        optional: [d__, e__, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && neq!(&b__ * &e__ - Atom::num(2) * &c__ * &d__, 0)
        },
        rhs: {
            let angle = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let mismatch = &b__ * &e__ - Atom::num(2) * &c__ * &d__;
            rubi_simp(&(&e__ * &angle.sinh() / (Atom::num(2) * &c__)), x_)
                    - rubi_star(mismatch / (Atom::num(2) * &c__), rubi_rhs_int(&angle.cosh(), x_))
        },
    ));
}

fn push_rules_rule_5907(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, x_);
    rules.push(rubi_rule!(
        order: 5907,
        source: "Int[(d_.+e_.*x_)^m_*Sinh[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
          e*(d+e*x)^(m-1)*Cosh[a+b*x+c*x^2]/(2*c) -
          e^2*(m-1)/(2*c) \\[Star] Int[(d+e*x)^(m-2)*Cosh[a+b*x+c*x^2],x] /;
        FreeQ[{a,b,c,d,e},x] && GtQ[m,1] && EqQ[b*e-2*c*d,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [d__, e__, m_, a__, b__, c__, x_],
        optional: [d__, e__, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && gtq!(m_, 1)
                && eqq!(&b__ * &e__ - Atom::num(2) * &c__ * &d__, 0)
        },
        rhs: {
            let linear = &d__ + &e__ * x_;
            let angle = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            rubi_simp(&(&e__ * linear.pow(&m_ - 1) * &angle.cosh() / (Atom::num(2) * &c__)), x_)
                    - rubi_star(e__.pow(2) * (&m_ - 1) / (Atom::num(2) * &c__), rubi_rhs_int(&(linear.pow(&m_ - 2) * angle.cosh()), x_))
        },
    ));
}

fn push_rules_rule_5908(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, x_);
    rules.push(rubi_rule!(
        order: 5908,
        source: "Int[(d_.+e_.*x_)^m_*Cosh[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
          e*(d+e*x)^(m-1)*Sinh[a+b*x+c*x^2]/(2*c) -
          e^2*(m-1)/(2*c) \\[Star] Int[(d+e*x)^(m-2)*Sinh[a+b*x+c*x^2],x] /;
        FreeQ[{a,b,c,d,e},x] && GtQ[m,1] && EqQ[b*e-2*c*d,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [d__, e__, m_, a__, b__, c__, x_],
        optional: [d__, e__, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && gtq!(m_, 1)
                && eqq!(&b__ * &e__ - Atom::num(2) * &c__ * &d__, 0)
        },
        rhs: {
            let linear = &d__ + &e__ * x_;
            let angle = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            rubi_simp(&(&e__ * linear.pow(&m_ - 1) * &angle.sinh() / (Atom::num(2) * &c__)), x_)
                    - rubi_star(e__.pow(2) * (&m_ - 1) / (Atom::num(2) * &c__), rubi_rhs_int(&(linear.pow(&m_ - 2) * angle.sinh()), x_))
        },
    ));
}

fn push_rules_rule_5909(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, x_);
    rules.push(rubi_rule!(
        order: 5909,
        source: "Int[(d_.+e_.*x_)^m_*Sinh[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
          e*(d+e*x)^(m-1)*Cosh[a+b*x+c*x^2]/(2*c) -
          (b*e-2*c*d)/(2*c) \\[Star] Int[(d+e*x)^(m-1)*Sinh[a+b*x+c*x^2],x] -
          e^2*(m-1)/(2*c) \\[Star] Int[(d+e*x)^(m-2)*Cosh[a+b*x+c*x^2],x] /;
        FreeQ[{a,b,c,d,e},x] && GtQ[m,1] && NeQ[b*e-2*c*d,0]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [d__, e__, m_, a__, b__, c__, x_],
        optional: [d__, e__, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && gtq!(m_, 1)
                && neq!(&b__ * &e__ - Atom::num(2) * &c__ * &d__, 0)
        },
        rhs: {
            let linear = &d__ + &e__ * x_;
            let angle = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let mismatch = &b__ * &e__ - Atom::num(2) * &c__ * &d__;
            rubi_simp(&(&e__ * linear.pow(&m_ - 1) * &angle.cosh() / (Atom::num(2) * &c__)), x_)
                    - rubi_star(&mismatch / (Atom::num(2) * &c__), rubi_rhs_int(
                            &(linear.pow(&m_ - 1) * &angle.sinh()),
                            x_,
                        ))
                    - rubi_star(e__.pow(2) * (&m_ - 1) / (Atom::num(2) * &c__), rubi_rhs_int(&(linear.pow(&m_ - 2) * angle.cosh()), x_))
        },
    ));
}

fn push_rules_rule_5910(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, x_);
    rules.push(rubi_rule!(
        order: 5910,
        source: "Int[(d_.+e_.*x_)^m_*Cosh[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
          e*(d+e*x)^(m-1)*Sinh[a+b*x+c*x^2]/(2*c) -
          (b*e-2*c*d)/(2*c) \\[Star] Int[(d+e*x)^(m-1)*Cosh[a+b*x+c*x^2],x] -
          e^2*(m-1)/(2*c) \\[Star] Int[(d+e*x)^(m-2)*Sinh[a+b*x+c*x^2],x] /;
        FreeQ[{a,b,c,d,e},x] && GtQ[m,1] && NeQ[b*e-2*c*d,0]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [d__, e__, m_, a__, b__, c__, x_],
        optional: [d__, e__, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && gtq!(m_, 1)
                && neq!(&b__ * &e__ - Atom::num(2) * &c__ * &d__, 0)
        },
        rhs: {
            let linear = &d__ + &e__ * x_;
            let angle = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let mismatch = &b__ * &e__ - Atom::num(2) * &c__ * &d__;
            rubi_simp(&(&e__ * linear.pow(&m_ - 1) * &angle.sinh() / (Atom::num(2) * &c__)), x_)
                    - rubi_star(&mismatch / (Atom::num(2) * &c__), rubi_rhs_int(
                            &(linear.pow(&m_ - 1) * &angle.cosh()),
                            x_,
                        ))
                    - rubi_star(e__.pow(2) * (&m_ - 1) / (Atom::num(2) * &c__), rubi_rhs_int(&(linear.pow(&m_ - 2) * angle.sinh()), x_))
        },
    ));
}

fn push_rules_rule_5911(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, x_);
    rules.push(rubi_rule!(
        order: 5911,
        source: "Int[(d_.+e_.*x_)^m_*Sinh[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
          (d+e*x)^(m+1)*Sinh[a+b*x+c*x^2]/(e*(m+1)) -
          2*c/(e^2*(m+1)) \\[Star] Int[(d+e*x)^(m+2)*Cosh[a+b*x+c*x^2],x] /;
        FreeQ[{a,b,c,d,e},x] && LtQ[m,-1] && EqQ[b*e-2*c*d,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [d__, e__, m_, a__, b__, c__, x_],
        optional: [d__, e__, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && ltq!(m_, -1)
                && eqq!(&b__ * &e__ - Atom::num(2) * &c__ * &d__, 0)
        },
        rhs: {
            let linear = &d__ + &e__ * x_;
            let angle = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            rubi_simp(&(linear.pow(&m_ + 1) * &angle.sinh() / (&e__ * (&m_ + 1))), x_)
                    - rubi_star(Atom::num(2) * &c__ / (e__.pow(2) * (&m_ + 1)), rubi_rhs_int(&(linear.pow(&m_ + 2) * angle.cosh()), x_))
        },
    ));
}

fn push_rules_rule_5912(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, x_);
    rules.push(rubi_rule!(
        order: 5912,
        source: "Int[(d_.+e_.*x_)^m_*Cosh[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
          (d+e*x)^(m+1)*Cosh[a+b*x+c*x^2]/(e*(m+1)) -
          2*c/(e^2*(m+1)) \\[Star] Int[(d+e*x)^(m+2)*Sinh[a+b*x+c*x^2],x] /;
        FreeQ[{a,b,c,d,e},x] && LtQ[m,-1] && EqQ[b*e-2*c*d,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [d__, e__, m_, a__, b__, c__, x_],
        optional: [d__, e__, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && ltq!(m_, -1)
                && eqq!(&b__ * &e__ - Atom::num(2) * &c__ * &d__, 0)
        },
        rhs: {
            let linear = &d__ + &e__ * x_;
            let angle = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            rubi_simp(&(linear.pow(&m_ + 1) * &angle.cosh() / (&e__ * (&m_ + 1))), x_)
                    - rubi_star(Atom::num(2) * &c__ / (e__.pow(2) * (&m_ + 1)), rubi_rhs_int(&(linear.pow(&m_ + 2) * angle.sinh()), x_))
        },
    ));
}

fn push_rules_rule_5913(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, x_);
    rules.push(rubi_rule!(
        order: 5913,
        source: "Int[(d_.+e_.*x_)^m_*Sinh[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
          (d+e*x)^(m+1)*Sinh[a+b*x+c*x^2]/(e*(m+1)) -
          (b*e-2*c*d)/(e^2*(m+1)) \\[Star] Int[(d+e*x)^(m+1)*Cosh[a+b*x+c*x^2],x] -
          2*c/(e^2*(m+1)) \\[Star] Int[(d+e*x)^(m+2)*Cosh[a+b*x+c*x^2],x] /;
        FreeQ[{a,b,c,d,e},x] && LtQ[m,-1] && NeQ[b*e-2*c*d,0]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [d__, e__, m_, a__, b__, c__, x_],
        optional: [d__, e__, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && ltq!(m_, -1)
                && neq!(&b__ * &e__ - Atom::num(2) * &c__ * &d__, 0)
        },
        rhs: {
            let linear = &d__ + &e__ * x_;
            let angle = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let mismatch = &b__ * &e__ - Atom::num(2) * &c__ * &d__;
            rubi_simp(&(linear.pow(&m_ + 1) * &angle.sinh() / (&e__ * (&m_ + 1))), x_)
                    - rubi_star(mismatch / (e__.pow(2) * (&m_ + 1)), rubi_rhs_int(
                            &(linear.pow(&m_ + 1) * &angle.cosh()),
                            x_,
                        ))
                    - rubi_star(Atom::num(2) * &c__ / (e__.pow(2) * (&m_ + 1)), rubi_rhs_int(&(linear.pow(&m_ + 2) * angle.cosh()), x_))
        },
    ));
}

fn push_rules_rule_5914(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, x_);
    rules.push(rubi_rule!(
        order: 5914,
        source: "Int[(d_.+e_.*x_)^m_*Cosh[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
          (d+e*x)^(m+1)*Cosh[a+b*x+c*x^2]/(e*(m+1)) -
          (b*e-2*c*d)/(e^2*(m+1)) \\[Star] Int[(d+e*x)^(m+1)*Sinh[a+b*x+c*x^2],x] -
          2*c/(e^2*(m+1)) \\[Star] Int[(d+e*x)^(m+2)*Sinh[a+b*x+c*x^2],x] /;
        FreeQ[{a,b,c,d,e},x] && LtQ[m,-1] && NeQ[b*e-2*c*d,0]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [d__, e__, m_, a__, b__, c__, x_],
        optional: [d__, e__, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && ltq!(m_, -1)
                && neq!(&b__ * &e__ - Atom::num(2) * &c__ * &d__, 0)
        },
        rhs: {
            let linear = &d__ + &e__ * x_;
            let angle = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let mismatch = &b__ * &e__ - Atom::num(2) * &c__ * &d__;
            rubi_simp(&(linear.pow(&m_ + 1) * &angle.cosh() / (&e__ * (&m_ + 1))), x_)
                    - rubi_star(mismatch / (e__.pow(2) * (&m_ + 1)), rubi_rhs_int(
                            &(linear.pow(&m_ + 1) * &angle.sinh()),
                            x_,
                        ))
                    - rubi_star(Atom::num(2) * &c__ / (e__.pow(2) * (&m_ + 1)), rubi_rhs_int(&(linear.pow(&m_ + 2) * angle.sinh()), x_))
        },
    ));
}

fn push_rules_rule_5915(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, x_);
    rules.push(rubi_rule!(
        order: 5915,
        source: "Int[(d_.+e_.*x_)^m_.*Sinh[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
          Unintegrable[(d+e*x)^m*Sinh[a+b*x+c*x^2],x] /;
        FreeQ[{a,b,c,d,e,m},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [d__, e__, m_, a__, b__, c__, x_],
        optional: [d__, e__, m_, a__, b__, c__],
        when: { freeq!([a__, b__, c__, d__, e__, m_], x_) },
        rhs: {
            rubi_unintegrable(
                (&d__ + &e__ * x_).pow(&m_) * (&a__ + &b__ * x_ + &c__ * x_.pow(2)).sinh(),
                x_,
            )
        },
    ));
}

fn push_rules_rule_5916(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, x_);
    rules.push(rubi_rule!(
        order: 5916,
        source: "Int[(d_.+e_.*x_)^m_.*Cosh[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
          Unintegrable[(d+e*x)^m*Cosh[a+b*x+c*x^2],x] /;
        FreeQ[{a,b,c,d,e,m},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [d__, e__, m_, a__, b__, c__, x_],
        optional: [d__, e__, m_, a__, b__, c__],
        when: { freeq!([a__, b__, c__, d__, e__, m_], x_) },
        rhs: {
            rubi_unintegrable(
                (&d__ + &e__ * x_).pow(&m_) * (&a__ + &b__ * x_ + &c__ * x_.pow(2)).cosh(),
                x_,
            )
        },
    ));
}

fn push_rules_rule_5917(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5917,
        source: "Int[(d_.+e_.*x_)^m_.*Sinh[a_.+b_.*x_+c_.*x_^2]^n_,x_Symbol] :=
          Int[ExpandTrigReduce[(d+e*x)^m,Sinh[a+b*x+c*x^2]^n,x],x] /;
        FreeQ[{a,b,c,d,e,m},x] && IGtQ[n,1]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (d__ + e__ * x_).pow(m_) * (a__ + b__ * x_ + c__ * x_.pow(2)).sinh().pow(n_),
        with: [d__, e__, m_, a__, b__, c__, n_, x_],
        optional: [d__, e__, m_, a__, b__, c__],
        when: { freeq!([a__, b__, c__, d__, e__, m_], x_) && igtq!(n_, 1) },
        rhs: {
            let multiplier = (&d__ + &e__ * x_).pow(&m_);
            let power = (&a__ + &b__ * x_ + &c__ * x_.pow(2)).sinh().pow(&n_);
            rubi_rhs_int(
                &rubi_expand_trig_reduce(&multiplier, &power, x_),
                x_,
            )
        },
    ));
}

fn push_rules_rule_5918(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5918,
        source: "Int[(d_.+e_.*x_)^m_.*Cosh[a_.+b_.*x_+c_.*x_^2]^n_,x_Symbol] :=
          Int[ExpandTrigReduce[(d+e*x)^m,Cosh[a+b*x+c*x^2]^n,x],x] /;
        FreeQ[{a,b,c,d,e,m},x] && IGtQ[n,1]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (d__ + e__ * x_).pow(m_) * (a__ + b__ * x_ + c__ * x_.pow(2)).cosh().pow(n_),
        with: [d__, e__, m_, a__, b__, c__, n_, x_],
        optional: [d__, e__, m_, a__, b__, c__],
        when: { freeq!([a__, b__, c__, d__, e__, m_], x_) && igtq!(n_, 1) },
        rhs: {
            let multiplier = (&d__ + &e__ * x_).pow(&m_);
            let power = (&a__ + &b__ * x_ + &c__ * x_.pow(2)).cosh().pow(&n_);
            rubi_rhs_int(
                &rubi_expand_trig_reduce(&multiplier, &power, x_),
                x_,
            )
        },
    ));
}

fn push_rules_rule_5919(rules: &mut Vec<RubiRule>) {
    rubi_symb!(m_, n_, u_, v_);
    rules.push(rubi_rule!(
        order: 5919,
        source: "Int[u_^m_.*Sinh[v_]^n_.,x_Symbol] :=
          Int[ExpandToSum[u,x]^m*Sinh[ExpandToSum[v,x]]^n,x] /;
        FreeQ[m,x] && IGtQ[n,0] && LinearQ[u,x] && QuadraticQ[v,x] && Not[LinearMatchQ[u,x] && QuadraticMatchQ[v,x]]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: Atom::var(u_).pow(m_) * Atom::var(v_).sinh().pow(n_),
        with: [u_, m_, v_, n_, x_],
        optional: [m_, n_],
        when: {
            freeq!(m_, x_)
                && igtq!(n_, 0)
                && rubi_linear_q(&u_, x_)
                && rubi_quadratic_q(&v_, x_)
                && !(rubi_linear_match_q(&u_, x_) && rubi_quadratic_match_q(&v_, x_))
        },
        rhs: {
            let expanded_u = rubi_expand_to_sum(&u_, x_);
            let expanded_v = rubi_expand_to_sum(&v_, x_);
            rubi_rhs_int(
                &(expanded_u.pow(&m_) * expanded_v.sinh().pow(&n_)),
                x_,
            )
        },
    ));
}

fn push_rules_rule_5920(rules: &mut Vec<RubiRule>) {
    rubi_symb!(m_, n_, u_, v_);
    rules.push(rubi_rule!(
        order: 5920,
        source: "Int[u_^m_.*Cosh[v_]^n_.,x_Symbol] :=
          Int[ExpandToSum[u,x]^m*Cosh[ExpandToSum[v,x]]^n,x] /;
        FreeQ[m,x] && IGtQ[n,0] && LinearQ[u,x] && QuadraticQ[v,x] && Not[LinearMatchQ[u,x] && QuadraticMatchQ[v,x]]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: Atom::var(u_).pow(m_) * Atom::var(v_).cosh().pow(n_),
        with: [u_, m_, v_, n_, x_],
        optional: [m_, n_],
        when: {
            freeq!(m_, x_)
                && igtq!(n_, 0)
                && rubi_linear_q(&u_, x_)
                && rubi_quadratic_q(&v_, x_)
                && !(rubi_linear_match_q(&u_, x_) && rubi_quadratic_match_q(&v_, x_))
        },
        rhs: {
            let expanded_u = rubi_expand_to_sum(&u_, x_);
            let expanded_v = rubi_expand_to_sum(&v_, x_);
            rubi_rhs_int(
                &(expanded_u.pow(&m_) * expanded_v.cosh().pow(&n_)),
                x_,
            )
        },
    ));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn downvalues_5897_through_5920_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .collect::<Vec<_>>();
        assert_eq!(orders, (5897..=5920).collect::<Vec<_>>());
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
    let x_ = symbols.x_;
    (d__ + e__ * x_) * (a__ + b__ * x_ + c__ * x_.pow(2)).cosh()
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let x_ = symbols.x_;
    (d__ + e__ * x_) * (a__ + b__ * x_ + c__ * x_.pow(2)).sinh()
}

#[inline(never)]
fn rubi_shared_pattern_2(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let m_ = symbols.m_;
    let x_ = symbols.x_;
    (d__ + e__ * x_).pow(m_) * (a__ + b__ * x_ + c__ * x_.pow(2)).cosh()
}

#[inline(never)]
fn rubi_shared_pattern_3(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let m_ = symbols.m_;
    let x_ = symbols.x_;
    (d__ + e__ * x_).pow(m_) * (a__ + b__ * x_ + c__ * x_.pow(2)).sinh()
}
