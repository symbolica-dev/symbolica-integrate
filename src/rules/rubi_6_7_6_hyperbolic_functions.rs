use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_5969(rules);
    push_rules_rule_5970(rules);
    push_rules_rule_5971(rules);
    push_rules_rule_5972(rules);
    push_rules_rule_5973(rules);
    push_rules_rule_5974(rules);
    push_rules_rule_5975(rules);
    push_rules_rule_5976(rules);
    push_rules_rule_5977(rules);
    push_rules_rule_5978(rules);
    push_rules_rule_5979(rules);
    push_rules_rule_5980(rules);
    push_rules_rule_5981(rules);
    push_rules_rule_5982(rules);
    push_rules_rule_5983(rules);
    push_rules_rule_5984(rules);
    push_rules_rule_5985(rules);
    push_rules_rule_5986(rules);
    push_rules_rule_5987(rules);
    push_rules_rule_5988(rules);
    push_rules_rule_5989(rules);
    push_rules_rule_5990(rules);
    push_rules_rule_5991(rules);
    push_rules_rule_5992(rules);
    push_rules_rule_5993(rules);
    push_rules_rule_5994(rules);
    push_rules_rule_5995(rules);
    push_rules_rule_5996(rules);
}

fn push_rules_rule_5969(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5969,
        source: "Int[(c_.+d_.*x_)^m_.*Sinh[a_.+b_.*x_]^n_.*Cosh[a_.+b_.*x_],x_Symbol] :=
          (c+d*x)^m*Sinh[a+b*x]^(n+1)/(b*(n+1)) -
          d*m/(b*(n+1)) \\[Star] Int[(c+d*x)^(m-1)*Sinh[a+b*x]^(n+1),x] /;
        FreeQ[{a,b,c,d,n},x] && IGtQ[m,0] && NeQ[n,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern: (c__ + d__ * x_).pow(m_) * (a__ + b__ * x_).sinh().pow(n_) * (a__ + b__ * x_).cosh(),
        with: [c__, d__, m_, a__, b__, n_, x_],
        optional: [c__, d__, m_, a__, b__, n_],
        when: {
            freeq!([a__, b__, c__, d__, n_], x_)
                && igtq!(m_, 0)
                && neq!(n_, -1)
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let angle = &a__ + &b__ * x_;
            let recursive = rubi_rhs_int(
                &(linear.pow(&m_ - 1) * angle.sinh().pow(&n_ + 1)),
                x_,
            );

            rubi_simp(&(linear.pow(&m_) * angle.sinh().pow(&n_ + 1) / (&b__ * (&n_ + 1))), x_)
                    - rubi_star(&d__ * &m_ / (&b__ * (&n_ + 1)), recursive)
        },
    ));
}

fn push_rules_rule_5970(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5970,
        source: "Int[(c_.+d_.*x_)^m_.*Sinh[a_.+b_.*x_]*Cosh[a_.+b_.*x_]^n_.,x_Symbol] :=
          (c+d*x)^m*Cosh[a+b*x]^(n+1)/(b*(n+1)) -
          d*m/(b*(n+1)) \\[Star] Int[(c+d*x)^(m-1)*Cosh[a+b*x]^(n+1),x] /;
        FreeQ[{a,b,c,d,n},x] && IGtQ[m,0] && NeQ[n,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern: (c__ + d__ * x_).pow(m_) * (a__ + b__ * x_).sinh() * (a__ + b__ * x_).cosh().pow(n_),
        with: [c__, d__, m_, a__, b__, n_, x_],
        optional: [c__, d__, m_, a__, b__, n_],
        when: {
            freeq!([a__, b__, c__, d__, n_], x_)
                && igtq!(m_, 0)
                && neq!(n_, -1)
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let angle = &a__ + &b__ * x_;
            let recursive = rubi_rhs_int(
                &(linear.pow(&m_ - 1) * angle.cosh().pow(&n_ + 1)),
                x_,
            );

            rubi_simp(&(linear.pow(&m_) * angle.cosh().pow(&n_ + 1) / (&b__ * (&n_ + 1))), x_)
                    - rubi_star(&d__ * &m_ / (&b__ * (&n_ + 1)), recursive)
        },
    ));
}

fn push_rules_rule_5971(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5971,
        source: "Int[(c_.+d_.*x_)^m_.*Sinh[a_.+b_.*x_]^n_.*Cosh[a_.+b_.*x_]^p_.,x_Symbol] :=
          Int[ExpandTrigReduce[(c+d*x)^m,Sinh[a+b*x]^n*Cosh[a+b*x]^p,x],x] /;
        FreeQ[{a,b,c,d,m},x] && IGtQ[n,0] && IGtQ[p,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (c__ + d__ * x_).pow(m_) * (a__ + b__ * x_).sinh().pow(n_) * (a__ + b__ * x_).cosh().pow(p_),
        with: [c__, d__, m_, a__, b__, n_, p_, x_],
        optional: [c__, d__, m_, a__, b__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, m_], x_)
                && igtq!(n_, 0)
                && igtq!(p_, 0)
        },
        rhs: {
            let multiplier = (&c__ + &d__ * x_).pow(&m_);
            let product = (&a__ + &b__ * x_).sinh().pow(&n_)
                * (&a__ + &b__ * x_).cosh().pow(&p_);
            rubi_rhs_int(
                &rubi_expand_trig_reduce(&multiplier, &product, x_),
                x_,
            )
        },
    ));
}

fn push_rules_rule_5972(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5972,
        source: "Int[(c_.+d_.*x_)^m_.*Sinh[a_.+b_.*x_]^n_.*Tanh[a_.+b_.*x_]^p_.,x_Symbol] :=
          Int[(c+d*x)^m*Sinh[a+b*x]^n*Tanh[a+b*x]^(p-2),x] - Int[(c+d*x)^m*Sinh[a+b*x]^(n-2)*Tanh[a+b*x]^p,x] /;
        FreeQ[{a,b,c,d,m},x] && IGtQ[n,0] && IGtQ[p,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (c__ + d__ * x_).pow(m_) * (a__ + b__ * x_).sinh().pow(n_) * (a__ + b__ * x_).tanh().pow(p_),
        with: [c__, d__, m_, a__, b__, n_, p_, x_],
        optional: [c__, d__, m_, a__, b__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, m_], x_)
                && igtq!(n_, 0)
                && igtq!(p_, 0)
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let angle = &a__ + &b__ * x_;
            let first = linear.pow(&m_) * angle.sinh().pow(&n_) * angle.tanh().pow(&p_ - 2);
            let second = linear.pow(&m_) * angle.sinh().pow(&n_ - 2) * angle.tanh().pow(&p_);

            rubi_rhs_int(&first, x_) - rubi_rhs_int(&second, x_)
        },
    ));
}

fn push_rules_rule_5973(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5973,
        source: "Int[(c_.+d_.*x_)^m_.*Cosh[a_.+b_.*x_]^n_.*Coth[a_.+b_.*x_]^p_.,x_Symbol] :=
          Int[(c+d*x)^m*Cosh[a+b*x]^n*Coth[a+b*x]^(p-2),x] + Int[(c+d*x)^m*Cosh[a+b*x]^(n-2)*Coth[a+b*x]^p,x] /;
        FreeQ[{a,b,c,d,m},x] && IGtQ[n,0] && IGtQ[p,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (c__ + d__ * x_).pow(m_) * (a__ + b__ * x_).cosh().pow(n_) * (a__ + b__ * x_).coth().pow(p_),
        with: [c__, d__, m_, a__, b__, n_, p_, x_],
        optional: [c__, d__, m_, a__, b__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, m_], x_)
                && igtq!(n_, 0)
                && igtq!(p_, 0)
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let angle = &a__ + &b__ * x_;
            let first = linear.pow(&m_) * angle.cosh().pow(&n_) * angle.coth().pow(&p_ - 2);
            let second = linear.pow(&m_) * angle.cosh().pow(&n_ - 2) * angle.coth().pow(&p_);

            rubi_rhs_int(&first, x_) + rubi_rhs_int(&second, x_)
        },
    ));
}

fn push_rules_rule_5974(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5974,
        source: "Int[(c_.+d_.*x_)^m_.*Sech[a_.+b_.*x_]^n_.*Tanh[a_.+b_.*x_]^p_.,x_Symbol] :=
          -(c+d*x)^m*Sech[a+b*x]^n/(b*n) +
          d*m/(b*n) \\[Star] Int[(c+d*x)^(m-1)*Sech[a+b*x]^n,x] /;
        FreeQ[{a,b,c,d,n},x] && EqQ[p,1] && GtQ[m,0]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [c__, d__, m_, a__, b__, n_, p_, x_],
        optional: [c__, d__, m_, a__, b__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, n_], x_)
                && eqq!(p_, 1)
                && gtq!(m_, 0)
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let angle = &a__ + &b__ * x_;
            let recursive =
                rubi_rhs_int(&(linear.pow(&m_ - 1) * angle.sech().pow(&n_)), x_);

            rubi_simp(&(-linear.pow(&m_) * angle.sech().pow(&n_) / (&b__ * &n_)), x_)
                    + rubi_star(&d__ * &m_ / (&b__ * &n_), recursive)
        },
    ));
}

fn push_rules_rule_5975(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5975,
        source: "Int[(c_.+d_.*x_)^m_.*Csch[a_.+b_.*x_]^n_.*Coth[a_.+b_.*x_]^p_.,x_Symbol] :=
          -(c+d*x)^m*Csch[a+b*x]^n/(b*n) +
          d*m/(b*n) \\[Star] Int[(c+d*x)^(m-1)*Csch[a+b*x]^n,x] /;
        FreeQ[{a,b,c,d,n},x] && EqQ[p,1] && GtQ[m,0]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [c__, d__, m_, a__, b__, n_, p_, x_],
        optional: [c__, d__, m_, a__, b__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, n_], x_)
                && eqq!(p_, 1)
                && gtq!(m_, 0)
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let angle = &a__ + &b__ * x_;
            let recursive =
                rubi_rhs_int(&(linear.pow(&m_ - 1) * angle.csch().pow(&n_)), x_);

            rubi_simp(&(-linear.pow(&m_) * angle.csch().pow(&n_) / (&b__ * &n_)), x_)
                    + rubi_star(&d__ * &m_ / (&b__ * &n_), recursive)
        },
    ));
}

fn push_rules_rule_5976(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5976,
        source: "Int[(c_.+d_.*x_)^m_.*Sech[a_.+b_.*x_]^2*Tanh[a_.+b_.*x_]^n_.,x_Symbol] :=
          (c+d*x)^m*Tanh[a+b*x]^(n+1)/(b*(n+1)) -
          d*m/(b*(n+1)) \\[Star] Int[(c+d*x)^(m-1)*Tanh[a+b*x]^(n+1),x] /;
        FreeQ[{a,b,c,d,n},x] && IGtQ[m,0] && NeQ[n,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern: (c__ + d__ * x_).pow(m_) * (a__ + b__ * x_).sech().pow(2) * (a__ + b__ * x_).tanh().pow(n_),
        with: [c__, d__, m_, a__, b__, n_, x_],
        optional: [c__, d__, m_, a__, b__, n_],
        when: {
            freeq!([a__, b__, c__, d__, n_], x_)
                && igtq!(m_, 0)
                && neq!(n_, -1)
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let angle = &a__ + &b__ * x_;
            let recursive = rubi_rhs_int(
                &(linear.pow(&m_ - 1) * angle.tanh().pow(&n_ + 1)),
                x_,
            );

            rubi_simp(&(linear.pow(&m_) * angle.tanh().pow(&n_ + 1) / (&b__ * (&n_ + 1))), x_)
                    - rubi_star(&d__ * &m_ / (&b__ * (&n_ + 1)), recursive)
        },
    ));
}

fn push_rules_rule_5977(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5977,
        source: "Int[(c_.+d_.*x_)^m_.*Csch[a_.+b_.*x_]^2*Coth[a_.+b_.*x_]^n_.,x_Symbol] :=
          -(c+d*x)^m*Coth[a+b*x]^(n+1)/(b*(n+1)) +
          d*m/(b*(n+1)) \\[Star] Int[(c+d*x)^(m-1)*Coth[a+b*x]^(n+1),x] /;
        FreeQ[{a,b,c,d,n},x] && IGtQ[m,0] && NeQ[n,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern: (c__ + d__ * x_).pow(m_) * (a__ + b__ * x_).csch().pow(2) * (a__ + b__ * x_).coth().pow(n_),
        with: [c__, d__, m_, a__, b__, n_, x_],
        optional: [c__, d__, m_, a__, b__, n_],
        when: {
            freeq!([a__, b__, c__, d__, n_], x_)
                && igtq!(m_, 0)
                && neq!(n_, -1)
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let angle = &a__ + &b__ * x_;
            let recursive = rubi_rhs_int(
                &(linear.pow(&m_ - 1) * angle.coth().pow(&n_ + 1)),
                x_,
            );

            rubi_simp(&(-linear.pow(&m_) * angle.coth().pow(&n_ + 1) / (&b__ * (&n_ + 1))), x_)
                    + rubi_star(&d__ * &m_ / (&b__ * (&n_ + 1)), recursive)
        },
    ));
}

fn push_rules_rule_5978(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 5978,
        source: "Int[(c_.+d_.*x_)^m_.*Sech[a_.+b_.*x_]*Tanh[a_.+b_.*x_]^p_,x_Symbol] :=
          Int[(c+d*x)^m*Sech[a+b*x]*Tanh[a+b*x]^(p-2),x] - Int[(c+d*x)^m*Sech[a+b*x]^3*Tanh[a+b*x]^(p-2),x] /;
        FreeQ[{a,b,c,d,m},x] && IGtQ[p/2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (c__ + d__ * x_).pow(m_) * (a__ + b__ * x_).sech() * (a__ + b__ * x_).tanh().pow(p_),
        with: [c__, d__, m_, a__, b__, p_, x_],
        optional: [c__, d__, m_, a__, b__],
        when: {
            freeq!([a__, b__, c__, d__, m_], x_) && igtq!(&p_ / 2, 0)
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let angle = &a__ + &b__ * x_;
            let reduced_tanh = angle.tanh().pow(&p_ - 2);
            let first = linear.pow(&m_) * angle.sech() * &reduced_tanh;
            let second = linear.pow(&m_) * angle.sech().pow(3) * reduced_tanh;

            rubi_rhs_int(&first, x_) - rubi_rhs_int(&second, x_)
        },
    ));
}

fn push_rules_rule_5979(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5979,
        source: "Int[(c_.+d_.*x_)^m_.*Sech[a_.+b_.*x_]^n_.*Tanh[a_.+b_.*x_]^p_,x_Symbol] :=
          Int[(c+d*x)^m*Sech[a+b*x]^n*Tanh[a+b*x]^(p-2),x] - Int[(c+d*x)^m*Sech[a+b*x]^(n+2)*Tanh[a+b*x]^(p-2),x] /;
        FreeQ[{a,b,c,d,m,n},x] && IGtQ[p/2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [c__, d__, m_, a__, b__, n_, p_, x_],
        optional: [c__, d__, m_, a__, b__, n_],
        when: {
            freeq!([a__, b__, c__, d__, m_, n_], x_) && igtq!(&p_ / 2, 0)
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let angle = &a__ + &b__ * x_;
            let reduced_tanh = angle.tanh().pow(&p_ - 2);
            let first = linear.pow(&m_) * angle.sech().pow(&n_) * &reduced_tanh;
            let second = linear.pow(&m_) * angle.sech().pow(&n_ + 2) * reduced_tanh;

            rubi_rhs_int(&first, x_) - rubi_rhs_int(&second, x_)
        },
    ));
}

fn push_rules_rule_5980(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 5980,
        source: "Int[(c_.+d_.*x_)^m_.*Csch[a_.+b_.*x_]*Coth[a_.+b_.*x_]^p_,x_Symbol] :=
          Int[(c+d*x)^m*Csch[a+b*x]*Coth[a+b*x]^(p-2),x] + Int[(c+d*x)^m*Csch[a+b*x]^3*Coth[a+b*x]^(p-2),x] /;
        FreeQ[{a,b,c,d,m},x] && IGtQ[p/2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (c__ + d__ * x_).pow(m_) * (a__ + b__ * x_).csch() * (a__ + b__ * x_).coth().pow(p_),
        with: [c__, d__, m_, a__, b__, p_, x_],
        optional: [c__, d__, m_, a__, b__],
        when: {
            freeq!([a__, b__, c__, d__, m_], x_) && igtq!(&p_ / 2, 0)
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let angle = &a__ + &b__ * x_;
            let reduced_coth = angle.coth().pow(&p_ - 2);
            let first = linear.pow(&m_) * angle.csch() * &reduced_coth;
            let second = linear.pow(&m_) * angle.csch().pow(3) * reduced_coth;

            rubi_rhs_int(&first, x_) + rubi_rhs_int(&second, x_)
        },
    ));
}

fn push_rules_rule_5981(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5981,
        source: "Int[(c_.+d_.*x_)^m_.*Csch[a_.+b_.*x_]^n_.*Coth[a_.+b_.*x_]^p_,x_Symbol] :=
          Int[(c+d*x)^m*Csch[a+b*x]^n*Coth[a+b*x]^(p-2),x] + Int[(c+d*x)^m*Csch[a+b*x]^(n+2)*Coth[a+b*x]^(p-2),x] /;
        FreeQ[{a,b,c,d,m,n},x] && IGtQ[p/2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [c__, d__, m_, a__, b__, n_, p_, x_],
        optional: [c__, d__, m_, a__, b__, n_],
        when: {
            freeq!([a__, b__, c__, d__, m_, n_], x_) && igtq!(&p_ / 2, 0)
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let angle = &a__ + &b__ * x_;
            let reduced_coth = angle.coth().pow(&p_ - 2);
            let first = linear.pow(&m_) * angle.csch().pow(&n_) * &reduced_coth;
            let second = linear.pow(&m_) * angle.csch().pow(&n_ + 2) * reduced_coth;

            rubi_rhs_int(&first, x_) + rubi_rhs_int(&second, x_)
        },
    ));
}

fn push_rules_rule_5982(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5982,
        source: "Int[(c_.+d_.*x_)^m_.*Sech[a_.+b_.*x_]^n_.*Tanh[a_.+b_.*x_]^p_.,x_Symbol] :=
          With[{u=IntHide[Sech[a+b*x]^n*Tanh[a+b*x]^p,x]},
          (c+d*x)^m \\[Star] u - d*m \\[Star] Int[(c+d*x)^(m-1)*u,x]] /;
        FreeQ[{a,b,c,d,n,p},x] && IGtQ[m,0] && (IntegerQ[n/2] || IntegerQ[(p-1)/2])",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [c__, d__, m_, a__, b__, n_, p_, x_],
        optional: [c__, d__, m_, a__, b__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, n_, p_], x_)
                && igtq!(m_, 0)
                && (integerq!(&n_ / 2) || integerq!((&p_ - 1) / 2))
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let angle = &a__ + &b__ * x_;
            let hidden = rubi_int_hide(&(angle.sech().pow(&n_) * angle.tanh().pow(&p_)), x_).rubi_rhs();
            let recursive = rubi_rhs_int(&(linear.pow(&m_ - 1) * &hidden), x_);

            rubi_star(linear.pow(&m_), hidden)
                    - rubi_star(&d__ * &m_, recursive)
        },
    ));
}

fn push_rules_rule_5983(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5983,
        source: "Int[(c_.+d_.*x_)^m_.*Csch[a_.+b_.*x_]^n_.*Coth[a_.+b_.*x_]^p_.,x_Symbol] :=
          With[{u=IntHide[Csch[a+b*x]^n*Coth[a+b*x]^p,x]},
          (c+d*x)^m \\[Star] u - d*m \\[Star] Int[(c+d*x)^(m-1)*u,x]] /;
        FreeQ[{a,b,c,d,n,p},x] && IGtQ[m,0] && (IntegerQ[n/2] || IntegerQ[(p-1)/2])",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [c__, d__, m_, a__, b__, n_, p_, x_],
        optional: [c__, d__, m_, a__, b__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, n_, p_], x_)
                && igtq!(m_, 0)
                && (integerq!(&n_ / 2) || integerq!((&p_ - 1) / 2))
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let angle = &a__ + &b__ * x_;
            let hidden = rubi_int_hide(&(angle.csch().pow(&n_) * angle.coth().pow(&p_)), x_).rubi_rhs();
            let recursive = rubi_rhs_int(&(linear.pow(&m_ - 1) * &hidden), x_);

            rubi_star(linear.pow(&m_), hidden)
                    - rubi_star(&d__ * &m_, recursive)
        },
    ));
}

fn push_rules_rule_5984(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5984,
        source: "Int[(c_.+d_.*x_)^m_.*Csch[a_.+b_.*x_]^n_.*Sech[a_.+b_.*x_]^n_., x_Symbol] :=
          2^n \\[Star] Int[(c+d*x)^m*Csch[2*a+2*b*x]^n,x] /;
        FreeQ[{a,b,c,d},x] && RationalQ[m] && IntegerQ[n]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: (c__ + d__ * x_).pow(m_) * (a__ + b__ * x_).csch().pow(n_) * (a__ + b__ * x_).sech().pow(n_),
        with: [c__, d__, m_, a__, b__, n_, x_],
        optional: [c__, d__, m_, a__, b__, n_],
        when: {
            freeq!([a__, b__, c__, d__], x_) && rationalq!(m_) && integerq!(n_)
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let doubled_angle = Atom::num(2) * &a__ + Atom::num(2) * &b__ * x_;
            let recursive =
                rubi_rhs_int(&(linear.pow(&m_) * doubled_angle.csch().pow(&n_)), x_);

            rubi_star(Atom::num(2).pow(&n_), recursive)
        },
    ));
}

fn push_rules_rule_5985(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5985,
        source: "Int[(c_.+d_.*x_)^m_.*Csch[a_.+b_.*x_]^n_.*Sech[a_.+b_.*x_]^p_., x_Symbol] :=
          With[{u=IntHide[Csch[a+b*x]^n*Sech[a+b*x]^p,x]},
          (c+d*x)^m \\[Star] u - d*m \\[Star] Int[(c+d*x)^(m-1)*u,x]] /;
        FreeQ[{a,b,c,d},x] && IntegersQ[n,p] && GtQ[m,0] && NeQ[n,p]",
        desc: "Integration by parts",
        refs: [],
        pattern: (c__ + d__ * x_).pow(m_) * (a__ + b__ * x_).csch().pow(n_) * (a__ + b__ * x_).sech().pow(p_),
        with: [c__, d__, m_, a__, b__, n_, p_, x_],
        optional: [c__, d__, m_, a__, b__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && integersq!([n_, p_])
                && gtq!(m_, 0)
                && neq!(n_, p_)
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let angle = &a__ + &b__ * x_;
            let hidden = rubi_int_hide(&(angle.csch().pow(&n_) * angle.sech().pow(&p_)), x_).rubi_rhs();
            let recursive = rubi_rhs_int(&(linear.pow(&m_ - 1) * &hidden), x_);

            rubi_star(linear.pow(&m_), hidden)
                    - rubi_star(&d__ * &m_, recursive)
        },
    ));
}

fn push_rules_rule_5986(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_f_, capital_g_, m_, n_, p_, u_, v_, w_);
    rules.push(rubi_rule!(
        order: 5986,
        source: "Int[u_^m_.*F_[v_]^n_.*G_[w_]^p_.,x_Symbol] :=
          Int[ExpandToSum[u,x]^m*F[ExpandToSum[v,x]]^n*G[ExpandToSum[v,x]]^p,x] /;
        FreeQ[{m,n,p},x] && HyperbolicQ[F] && HyperbolicQ[G] && EqQ[v,w] && LinearQ[{u,v,w},x] && Not[LinearMatchQ[{u,v,w},x]]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: u_.pow(m_)
            * capital_f_.call(v_).pow(n_)
            * capital_g_.call(w_).pow(p_),
        with: [u_, m_, capital_f_, v_, n_, capital_g_, w_, p_, x_],
        optional: [m_, n_, p_],
        when: {
            freeq!([m_, n_, p_], x_)
                && rubi_hyperbolic_head_q(&capital_f_)
                && rubi_hyperbolic_head_q(&capital_g_)
                && eqq!(v_, w_)
                && rubi_linear_q_list(&[&u_, &v_, &w_], x_)
                && !rubi_linear_match_q_list(&[&u_, &v_, &w_], x_)
        },
        rhs: {
            let expanded_u = rubi_expand_to_sum(&u_, x_);
            let expanded_v = rubi_expand_to_sum(&v_, x_);
            let capital_f_ = rubi_function_head_symbol(&capital_f_).unwrap();
            let capital_g_ = rubi_function_head_symbol(&capital_g_).unwrap();
            let integrand = expanded_u.pow(&m_)
                * capital_f_.call(&expanded_v).pow(&n_)
                * capital_g_.call(expanded_v).pow(&p_);

            rubi_rhs_int(&integrand, x_)
        },
    ));
}

fn push_rules_rule_5987(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5987,
        source: "Int[(e_.+f_.*x_)^m_.*Cosh[c_.+d_.*x_]*(a_+b_.*Sinh[c_.+d_.*x_])^n_.,x_Symbol] :=
          (e+f*x)^m*(a+b*Sinh[c+d*x])^(n+1)/(b*d*(n+1)) -
          f*m/(b*d*(n+1)) \\[Star] Int[(e+f*x)^(m-1)*(a+b*Sinh[c+d*x])^(n+1),x] /;
        FreeQ[{a,b,c,d,e,f,n},x] && IGtQ[m,0] && NeQ[n,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern: (e__ + f__ * x_).pow(m_)
            * (c__ + d__ * x_).cosh()
            * (a__ + b__ * (c__ + d__ * x_).sinh()).pow(n_),
        with: [e__, f__, m_, c__, d__, a__, b__, n_, x_],
        optional: [e__, f__, m_, c__, d__, b__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, n_], x_)
                && igtq!(m_, 0)
                && neq!(n_, -1)
        },
        rhs: {
            let linear = &e__ + &f__ * x_;
            let angle = &c__ + &d__ * x_;
            let binomial = &a__ + &b__ * angle.sinh();
            let denominator = &b__ * &d__ * (&n_ + 1);
            let recursive = rubi_rhs_int(&(linear.pow(&m_ - 1) * binomial.pow(&n_ + 1)), x_);

            rubi_simp(&(linear.pow(&m_) * binomial.pow(&n_ + 1) / &denominator), x_)
                    - rubi_star(&f__ * &m_ / &denominator, recursive)
        },
    ));
}

fn push_rules_rule_5988(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5988,
        source: "Int[(e_.+f_.*x_)^m_.*Sinh[c_.+d_.*x_]*(a_+b_.*Cosh[c_.+d_.*x_])^n_.,x_Symbol] :=
          (e+f*x)^m*(a+b*Cosh[c+d*x])^(n+1)/(b*d*(n+1)) -
          f*m/(b*d*(n+1)) \\[Star] Int[(e+f*x)^(m-1)*(a+b*Cosh[c+d*x])^(n+1),x] /;
        FreeQ[{a,b,c,d,e,f,n},x] && IGtQ[m,0] && NeQ[n,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern: (e__ + f__ * x_).pow(m_)
            * (c__ + d__ * x_).sinh()
            * (a__ + b__ * (c__ + d__ * x_).cosh()).pow(n_),
        with: [e__, f__, m_, c__, d__, a__, b__, n_, x_],
        optional: [e__, f__, m_, c__, d__, b__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, n_], x_)
                && igtq!(m_, 0)
                && neq!(n_, -1)
        },
        rhs: {
            let linear = &e__ + &f__ * x_;
            let angle = &c__ + &d__ * x_;
            let binomial = &a__ + &b__ * angle.cosh();
            let denominator = &b__ * &d__ * (&n_ + 1);
            let recursive = rubi_rhs_int(&(linear.pow(&m_ - 1) * binomial.pow(&n_ + 1)), x_);

            rubi_simp(&(linear.pow(&m_) * binomial.pow(&n_ + 1) / &denominator), x_)
                    - rubi_star(&f__ * &m_ / &denominator, recursive)
        },
    ));
}

fn push_rules_rule_5989(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5989,
        source: "Int[(e_.+f_.*x_)^m_.*Sech[c_.+d_.*x_]^2*(a_+b_.*Tanh[c_.+d_.*x_])^n_.,x_Symbol] :=
          (e+f*x)^m*(a+b*Tanh[c+d*x])^(n+1)/(b*d*(n+1)) -
          f*m/(b*d*(n+1)) \\[Star] Int[(e+f*x)^(m-1)*(a+b*Tanh[c+d*x])^(n+1),x] /;
        FreeQ[{a,b,c,d,e,f,n},x] && IGtQ[m,0] && NeQ[n,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern: (e__ + f__ * x_).pow(m_)
            * (c__ + d__ * x_).sech().pow(2)
            * (a__ + b__ * (c__ + d__ * x_).tanh()).pow(n_),
        with: [e__, f__, m_, c__, d__, a__, b__, n_, x_],
        optional: [e__, f__, m_, c__, d__, b__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, n_], x_)
                && igtq!(m_, 0)
                && neq!(n_, -1)
        },
        rhs: {
            let linear = &e__ + &f__ * x_;
            let angle = &c__ + &d__ * x_;
            let binomial = &a__ + &b__ * angle.tanh();
            let denominator = &b__ * &d__ * (&n_ + 1);
            let recursive = rubi_rhs_int(&(linear.pow(&m_ - 1) * binomial.pow(&n_ + 1)), x_);

            rubi_simp(&(linear.pow(&m_) * binomial.pow(&n_ + 1) / &denominator), x_)
                    - rubi_star(&f__ * &m_ / &denominator, recursive)
        },
    ));
}

fn push_rules_rule_5990(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5990,
        source: "Int[(e_.+f_.*x_)^m_.*Csch[c_.+d_.*x_]^2*(a_+b_.*Coth[c_.+d_.*x_])^n_.,x_Symbol] :=
          -(e+f*x)^m*(a+b*Coth[c+d*x])^(n+1)/(b*d*(n+1)) +
          f*m/(b*d*(n+1)) \\[Star] Int[(e+f*x)^(m-1)*(a+b*Coth[c+d*x])^(n+1),x] /;
        FreeQ[{a,b,c,d,e,f,n},x] && IGtQ[m,0] && NeQ[n,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern: (e__ + f__ * x_).pow(m_)
            * (c__ + d__ * x_).csch().pow(2)
            * (a__ + b__ * (c__ + d__ * x_).coth()).pow(n_),
        with: [e__, f__, m_, c__, d__, a__, b__, n_, x_],
        optional: [e__, f__, m_, c__, d__, b__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, n_], x_)
                && igtq!(m_, 0)
                && neq!(n_, -1)
        },
        rhs: {
            let linear = &e__ + &f__ * x_;
            let angle = &c__ + &d__ * x_;
            let binomial = &a__ + &b__ * angle.coth();
            let denominator = &b__ * &d__ * (&n_ + 1);
            let recursive = rubi_rhs_int(&(linear.pow(&m_ - 1) * binomial.pow(&n_ + 1)), x_);

            rubi_simp(&(-linear.pow(&m_) * binomial.pow(&n_ + 1) / &denominator), x_)
                    + rubi_star(&f__ * &m_ / &denominator, recursive)
        },
    ));
}

fn push_rules_rule_5991(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5991,
        source: "Int[(e_.+f_.*x_)^m_.*Sech[c_.+d_.*x_]*Tanh[c_.+d_.*x_]*(a_+b_.*Sech[c_.+d_.*x_])^n_.,x_Symbol] :=
          -(e+f*x)^m*(a+b*Sech[c+d*x])^(n+1)/(b*d*(n+1)) +
          f*m/(b*d*(n+1)) \\[Star] Int[(e+f*x)^(m-1)*(a+b*Sech[c+d*x])^(n+1),x] /;
        FreeQ[{a,b,c,d,e,f,n},x] && IGtQ[m,0] && NeQ[n,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern: (e__ + f__ * x_).pow(m_)
            * (c__ + d__ * x_).sech()
            * (c__ + d__ * x_).tanh()
            * (a__ + b__ * (c__ + d__ * x_).sech()).pow(n_),
        with: [e__, f__, m_, c__, d__, a__, b__, n_, x_],
        optional: [e__, f__, m_, c__, d__, b__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, n_], x_)
                && igtq!(m_, 0)
                && neq!(n_, -1)
        },
        rhs: {
            let linear = &e__ + &f__ * x_;
            let angle = &c__ + &d__ * x_;
            let binomial = &a__ + &b__ * angle.sech();
            let denominator = &b__ * &d__ * (&n_ + 1);
            let recursive = rubi_rhs_int(&(linear.pow(&m_ - 1) * binomial.pow(&n_ + 1)), x_);

            rubi_simp(&(-linear.pow(&m_) * binomial.pow(&n_ + 1) / &denominator), x_)
                    + rubi_star(&f__ * &m_ / &denominator, recursive)
        },
    ));
}

fn push_rules_rule_5992(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5992,
        source: "Int[(e_.+f_.*x_)^m_.*Csch[c_.+d_.*x_]*Coth[c_.+d_.*x_]*(a_+b_.*Csch[c_.+d_.*x_])^n_.,x_Symbol] :=
          -(e+f*x)^m*(a+b*Csch[c+d*x])^(n+1)/(b*d*(n+1)) +
          f*m/(b*d*(n+1)) \\[Star] Int[(e+f*x)^(m-1)*(a+b*Csch[c+d*x])^(n+1),x] /;
        FreeQ[{a,b,c,d,e,f,n},x] && IGtQ[m,0] && NeQ[n,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern: (e__ + f__ * x_).pow(m_)
            * (c__ + d__ * x_).csch()
            * (c__ + d__ * x_).coth()
            * (a__ + b__ * (c__ + d__ * x_).csch()).pow(n_),
        with: [e__, f__, m_, c__, d__, a__, b__, n_, x_],
        optional: [e__, f__, m_, c__, d__, b__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, n_], x_)
                && igtq!(m_, 0)
                && neq!(n_, -1)
        },
        rhs: {
            let linear = &e__ + &f__ * x_;
            let angle = &c__ + &d__ * x_;
            let binomial = &a__ + &b__ * angle.csch();
            let denominator = &b__ * &d__ * (&n_ + 1);
            let recursive = rubi_rhs_int(&(linear.pow(&m_ - 1) * binomial.pow(&n_ + 1)), x_);

            rubi_simp(&(-linear.pow(&m_) * binomial.pow(&n_ + 1) / &denominator), x_)
                    + rubi_star(&f__ * &m_ / &denominator, recursive)
        },
    ));
}

fn push_rules_rule_5993(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 5993,
        source: "Int[(e_.+f_.*x_)^m_.*Sinh[a_.+b_.*x_]^p_.*Sinh[c_.+d_.*x_]^q_.,x_Symbol] :=
          Int[ExpandTrigReduce[(e+f*x)^m,Sinh[a+b*x]^p*Sinh[c+d*x]^q,x],x] /;
        FreeQ[{a,b,c,d,e,f},x] && IGtQ[p,0] && IGtQ[q,0] && IntegerQ[m]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (e__ + f__ * x_).pow(m_) * (a__ + b__ * x_).sinh().pow(p_) * (c__ + d__ * x_).sinh().pow(q_),
        with: [e__, f__, m_, a__, b__, p_, c__, d__, q_, x_],
        optional: [e__, f__, m_, a__, b__, p_, c__, d__, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && igtq!(p_, 0)
                && igtq!(q_, 0)
                && integerq!(m_)
        },
        rhs: {
            let multiplier = (&e__ + &f__ * x_).pow(&m_);
            let product = (&a__ + &b__ * x_).sinh().pow(&p_)
                * (&c__ + &d__ * x_).sinh().pow(&q_);
            let expanded = rubi_expand_trig_reduce(&multiplier, &product, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_5994(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 5994,
        source: "Int[(e_.+f_.*x_)^m_.*Cosh[a_.+b_.*x_]^p_.*Cosh[c_.+d_.*x_]^q_.,x_Symbol] :=
          Int[ExpandTrigReduce[(e+f*x)^m,Cosh[a+b*x]^p*Cosh[c+d*x]^q,x],x] /;
        FreeQ[{a,b,c,d,e,f},x] && IGtQ[p,0] && IGtQ[q,0] && IntegerQ[m]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (e__ + f__ * x_).pow(m_) * (a__ + b__ * x_).cosh().pow(p_) * (c__ + d__ * x_).cosh().pow(q_),
        with: [e__, f__, m_, a__, b__, p_, c__, d__, q_, x_],
        optional: [e__, f__, m_, a__, b__, p_, c__, d__, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && igtq!(p_, 0)
                && igtq!(q_, 0)
                && integerq!(m_)
        },
        rhs: {
            let multiplier = (&e__ + &f__ * x_).pow(&m_);
            let product = (&a__ + &b__ * x_).cosh().pow(&p_)
                * (&c__ + &d__ * x_).cosh().pow(&q_);
            let expanded = rubi_expand_trig_reduce(&multiplier, &product, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_5995(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 5995,
        source: "Int[(e_.+f_.*x_)^m_.*Sinh[a_.+b_.*x_]^p_.*Cosh[c_.+d_.*x_]^q_.,x_Symbol] :=
          Int[ExpandTrigReduce[(e+f*x)^m,Sinh[a+b*x]^p*Cosh[c+d*x]^q,x],x] /;
        FreeQ[{a,b,c,d,e,f,m},x] && IGtQ[p,0] && IGtQ[q,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (e__ + f__ * x_).pow(m_) * (a__ + b__ * x_).sinh().pow(p_) * (c__ + d__ * x_).cosh().pow(q_),
        with: [e__, f__, m_, a__, b__, p_, c__, d__, q_, x_],
        optional: [e__, f__, m_, a__, b__, p_, c__, d__, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_], x_)
                && igtq!(p_, 0)
                && igtq!(q_, 0)
        },
        rhs: {
            let multiplier = (&e__ + &f__ * x_).pow(&m_);
            let product = (&a__ + &b__ * x_).sinh().pow(&p_)
                * (&c__ + &d__ * x_).cosh().pow(&q_);
            let expanded = rubi_expand_trig_reduce(&multiplier, &product, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_5996(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        capital_f_, capital_g_, a__, b__, c__, d__, e__, f__, m_, p_, q_, x_
    );
    rules.push(rubi_rule!(
        order: 5996,
        source: "Int[(e_.+f_.*x_)^m_.*F_[a_.+b_.*x_]^p_.*G_[c_.+d_.*x_]^q_.,x_Symbol] :=
          Int[ExpandTrigExpand[(e+f*x)^m*G[c+d*x]^q,F,c+d*x,p,b/d,x],x] /;
        FreeQ[{a,b,c,d,e,f,m},x] && MemberQ[{Sinh,Cosh},F] && MemberQ[{Sech,Csch},G] && IGtQ[p,0] && IGtQ[q,0] && EqQ[b*c-a*d,0] && IGtQ[b/d,1]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (e__ + f__ * x_).pow(m_)
            * capital_f_.call( a__ + b__ * x_).pow(p_)
            * capital_g_.call( c__ + d__ * x_).pow(q_),
        with: [e__, f__, m_, capital_f_, a__, b__, p_, capital_g_, c__, d__, q_, x_],
        optional: [e__, f__, m_, a__, b__, c__, d__, q_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_], x_)
                && (eqq!(capital_f_, Atom::var(symbol!("sinh"))) || eqq!(capital_f_, Atom::var(symbol!("cosh"))))
                && (eqq!(capital_g_, Atom::var(symbol!("sech"))) || eqq!(capital_g_, Atom::var(symbol!("csch"))))
                && igtq!(p_, 0)
                && igtq!(q_, 0)
                && eqq!(&b__ * &c__ - &a__ * &d__, 0)
                && igtq!(&b__ / &d__, 1)
        },
        rhs: {
            let angle = &c__ + &d__ * x_;
            let multiplier =
                (&e__ + &f__ * x_).pow(&m_) * rubi_function_head_symbol(&capital_g_).rubi_rhs().call( &angle).pow(&q_);
            let expanded = rubi_expand_hyperbolic_trig_expand(
                &multiplier,
                &capital_f_,
                &angle,
                &p_,
                &(&b__ / &d__),
            ).rubi_rhs();

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn downvalues_5969_through_5996_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .filter(|order| (5969..=5996).contains(order))
            .collect::<Vec<_>>();
        assert_eq!(orders, (5969..=5996).collect::<Vec<_>>());
    }
}

// Generated shared pattern builders.

#[inline(never)]
fn rubi_shared_pattern_0(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (c__ + d__ * x_).pow(m_) * (a__ + b__ * x_).csch().pow(n_) * (a__ + b__ * x_).coth().pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (c__ + d__ * x_).pow(m_) * (a__ + b__ * x_).sech().pow(n_) * (a__ + b__ * x_).tanh().pow(p_)
}
