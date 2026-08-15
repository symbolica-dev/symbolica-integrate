use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_4904(rules);
    push_rules_rule_4905(rules);
    push_rules_rule_4906(rules);
    push_rules_rule_4907(rules);
    push_rules_rule_4908(rules);
    push_rules_rule_4909(rules);
    push_rules_rule_4910(rules);
    push_rules_rule_4911(rules);
    push_rules_rule_4912(rules);
    push_rules_rule_4913(rules);
    push_rules_rule_4914(rules);
    push_rules_rule_4915(rules);
    push_rules_rule_4916(rules);
    push_rules_rule_4917(rules);
    push_rules_rule_4918(rules);
    push_rules_rule_4919(rules);
    push_rules_rule_4920(rules);
    push_rules_rule_4921(rules);
    push_rules_rule_4922(rules);
    push_rules_rule_4923(rules);
    push_rules_rule_4924(rules);
    push_rules_rule_4925(rules);
    push_rules_rule_4926(rules);
    push_rules_rule_4927(rules);
    push_rules_rule_4928(rules);
    push_rules_rule_4929(rules);
    push_rules_rule_4930(rules);
    push_rules_rule_4931(rules);
}

fn push_rules_rule_4904(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 4904,
        source: "Int[(c_.+d_.*x_)^m_.*Sin[a_.+b_.*x_]^n_.*Cos[a_.+b_.*x_],x_Symbol] :=
          (c+d*x)^m*Sin[a+b*x]^(n+1)/(b*(n+1)) -
          d*m/(b*(n+1)) \\[Star] Int[(c+d*x)^(m-1)*Sin[a+b*x]^(n+1),x] /;
        FreeQ[{a,b,c,d,n},x] && IGtQ[m,0] && NeQ[n,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern: (c__ + d__ * x_).pow(m_) * (a__ + b__ * x_).sin().pow(n_) * (a__ + b__ * x_).cos(),
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
            let recursive_integrand = linear.pow(&m_ - 1) * angle.sin().pow(&n_ + 1);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let recursive_term = rubi_simp(&(&(&d__ * &m_ / (&b__ * (&n_ + 1))) * &recursive), x_);

            rubi_simp(&(linear.pow(&m_) * angle.sin().pow(&n_ + 1) / (&b__ * (&n_ + 1))), x_) - rubi_star(Atom::num(1), recursive_term)
        },
    ));
}

fn push_rules_rule_4905(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 4905,
        source: "Int[(c_.+d_.*x_)^m_.*Sin[a_.+b_.*x_]*Cos[a_.+b_.*x_]^n_.,x_Symbol] :=
          -(c+d*x)^m*Cos[a+b*x]^(n+1)/(b*(n+1)) +
          d*m/(b*(n+1)) \\[Star] Int[(c+d*x)^(m-1)*Cos[a+b*x]^(n+1),x] /;
        FreeQ[{a,b,c,d,n},x] && IGtQ[m,0] && NeQ[n,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern: (c__ + d__ * x_).pow(m_) * (a__ + b__ * x_).sin() * (a__ + b__ * x_).cos().pow(n_),
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
            let recursive_integrand = linear.pow(&m_ - 1) * angle.cos().pow(&n_ + 1);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let recursive_term = rubi_simp(&(&(&d__ * &m_ / (&b__ * (&n_ + 1))) * &recursive), x_);

            rubi_simp(&(-linear.pow(&m_) * angle.cos().pow(&n_ + 1) / (&b__ * (&n_ + 1))), x_)
                    + rubi_star(Atom::num(1), recursive_term)
        },
    ));
}

fn push_rules_rule_4906(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 4906,
        source: "Int[(c_.+d_.*x_)^m_.*Sin[a_.+b_.*x_]^n_.*Cos[a_.+b_.*x_]^p_.,x_Symbol] :=
          Int[ExpandTrigReduce[(c+d*x)^m,Sin[a+b*x]^n*Cos[a+b*x]^p,x],x] /;
        FreeQ[{a,b,c,d,m},x] && IGtQ[n,0] && IGtQ[p,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (c__ + d__ * x_).pow(m_) * (a__ + b__ * x_).sin().pow(n_) * (a__ + b__ * x_).cos().pow(p_),
        with: [c__, d__, m_, a__, b__, n_, p_, x_],
        optional: [c__, d__, m_, a__, b__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, m_], x_)
                && igtq!(n_, 0)
                && igtq!(p_, 0)
        },
        rhs: {
            let linear_power = (&c__ + &d__ * x_).pow(&m_);
            let trig_product = (&a__ + &b__ * x_).sin().pow(&n_)
                * (&a__ + &b__ * x_).cos().pow(&p_);
            let expanded = rubi_expand_trig_reduce(&linear_power, &trig_product, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_4907(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 4907,
        source: "Int[(c_.+d_.*x_)^m_.*Sin[a_.+b_.*x_]^n_.*Tan[a_.+b_.*x_]^p_.,x_Symbol] :=
          -Int[(c+d*x)^m*Sin[a+b*x]^n*Tan[a+b*x]^(p-2),x] + Int[(c+d*x)^m*Sin[a+b*x]^(n-2)*Tan[a+b*x]^p,x] /;
        FreeQ[{a,b,c,d,m},x] && IGtQ[n,0] && IGtQ[p,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (c__ + d__ * x_).pow(m_) * (a__ + b__ * x_).sin().pow(n_) * (a__ + b__ * x_).tan().pow(p_),
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
            let first_integrand = linear.pow(&m_) * angle.sin().pow(&n_) * angle.tan().pow(&p_ - 2);
            let second_integrand = linear.pow(&m_) * angle.sin().pow(&n_ - 2) * angle.tan().pow(&p_);
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            -first + second
        },
    ));
}

fn push_rules_rule_4908(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 4908,
        source: "Int[(c_.+d_.*x_)^m_.*Cos[a_.+b_.*x_]^n_.*Cot[a_.+b_.*x_]^p_.,x_Symbol] :=
          -Int[(c+d*x)^m*Cos[a+b*x]^n*Cot[a+b*x]^(p-2),x] + Int[(c+d*x)^m*Cos[a+b*x]^(n-2)*Cot[a+b*x]^p,x] /;
        FreeQ[{a,b,c,d,m},x] && IGtQ[n,0] && IGtQ[p,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (c__ + d__ * x_).pow(m_) * (a__ + b__ * x_).cos().pow(n_) * (a__ + b__ * x_).cot().pow(p_),
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
            let first_integrand = linear.pow(&m_) * angle.cos().pow(&n_) * angle.cot().pow(&p_ - 2);
            let second_integrand = linear.pow(&m_) * angle.cos().pow(&n_ - 2) * angle.cot().pow(&p_);
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            -first + second
        },
    ));
}

fn push_rules_rule_4909(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 4909,
        source: "Int[(c_.+d_.*x_)^m_.*Sec[a_.+b_.*x_]^n_.*Tan[a_.+b_.*x_]^p_.,x_Symbol] :=
          (c+d*x)^m*Sec[a+b*x]^n/(b*n) -
          d*m/(b*n) \\[Star] Int[(c+d*x)^(m-1)*Sec[a+b*x]^n,x] /;
        FreeQ[{a,b,c,d,n},x] && EqQ[p,1] && GtQ[m,0]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [c__, d__, m_, a__, b__, n_, p_, x_],
        optional: [c__, d__, m_, a__, b__, p_, n_],
        when: {
            freeq!([a__, b__, c__, d__, n_], x_)
                && eqq!(p_, 1)
                && gtq!(m_, 0)
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let angle = &a__ + &b__ * x_;
            let recursive_integrand = linear.pow(&m_ - 1) * angle.sec().pow(&n_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let recursive_term = rubi_simp(&(&(&d__ * &m_ / (&b__ * &n_)) * &recursive), x_);

            rubi_simp(&(linear.pow(&m_) * angle.sec().pow(&n_) / (&b__ * &n_)), x_) - rubi_star(Atom::num(1), recursive_term)
        },
    ));
}

fn push_rules_rule_4910(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 4910,
        source: "Int[(c_.+d_.*x_)^m_.*Csc[a_.+b_.*x_]^n_.*Cot[a_.+b_.*x_]^p_.,x_Symbol] :=
          -(c+d*x)^m*Csc[a+b*x]^n/(b*n) +
          d*m/(b*n) \\[Star] Int[(c+d*x)^(m-1)*Csc[a+b*x]^n,x] /;
        FreeQ[{a,b,c,d,n},x] && EqQ[p,1] && GtQ[m,0]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [c__, d__, m_, a__, b__, n_, p_, x_],
        optional: [c__, d__, m_, a__, b__, p_, n_],
        when: {
            freeq!([a__, b__, c__, d__, n_], x_)
                && eqq!(p_, 1)
                && gtq!(m_, 0)
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let angle = &a__ + &b__ * x_;
            let recursive_integrand = linear.pow(&m_ - 1) * angle.csc().pow(&n_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let recursive_term = rubi_simp(&(&(&d__ * &m_ / (&b__ * &n_)) * &recursive), x_);

            rubi_simp(&(-linear.pow(&m_) * angle.csc().pow(&n_) / (&b__ * &n_)), x_) + rubi_star(Atom::num(1), recursive_term)
        },
    ));
}

fn push_rules_rule_4911(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 4911,
        source: "Int[(c_.+d_.*x_)^m_.*Sec[a_.+b_.*x_]^2*Tan[a_.+b_.*x_]^n_.,x_Symbol] :=
          (c+d*x)^m*Tan[a+b*x]^(n+1)/(b*(n+1)) -
          d*m/(b*(n +1)) \\[Star] Int[(c+d*x)^(m-1)*Tan[a+b*x]^(n+1),x] /;
        FreeQ[{a,b,c,d,n},x] && IGtQ[m,0] && NeQ[n,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern: (c__ + d__ * x_).pow(m_) * (a__ + b__ * x_).sec().pow(2) * (a__ + b__ * x_).tan().pow(n_),
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
            let recursive_integrand = linear.pow(&m_ - 1) * angle.tan().pow(&n_ + 1);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let recursive_term = rubi_simp(&(&(&d__ * &m_ / (&b__ * (&n_ + 1))) * &recursive), x_);

            rubi_simp(&(linear.pow(&m_) * angle.tan().pow(&n_ + 1) / (&b__ * (&n_ + 1))), x_) - rubi_star(Atom::num(1), recursive_term)
        },
    ));
}

fn push_rules_rule_4912(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 4912,
        source: "Int[(c_.+d_.*x_)^m_.*Csc[a_.+b_.*x_]^2*Cot[a_.+b_.*x_]^n_.,x_Symbol] :=
          -(c+d*x)^m*Cot[a+b*x]^(n+1)/(b*(n+1)) +
          d*m/(b*(n +1)) \\[Star] Int[(c+d*x)^(m-1)*Cot[a+b*x]^(n+1),x] /;
        FreeQ[{a,b,c,d,n},x] && IGtQ[m,0] && NeQ[n,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern: (c__ + d__ * x_).pow(m_) * (a__ + b__ * x_).csc().pow(2) * (a__ + b__ * x_).cot().pow(n_),
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
            let recursive_integrand = linear.pow(&m_ - 1) * angle.cot().pow(&n_ + 1);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let recursive_term = rubi_simp(&(&(&d__ * &m_ / (&b__ * (&n_ + 1))) * &recursive), x_);

            rubi_simp(&(-linear.pow(&m_) * angle.cot().pow(&n_ + 1) / (&b__ * (&n_ + 1))), x_)
                    + rubi_star(Atom::num(1), recursive_term)
        },
    ));
}

fn push_rules_rule_4913(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 4913,
        source: "Int[(c_.+d_.*x_)^m_.*Sec[a_.+b_.*x_]*Tan[a_.+b_.*x_]^p_,x_Symbol] :=
          -Int[(c+d*x)^m*Sec[a+b*x]*Tan[a+b*x]^(p-2),x] + Int[(c+d*x)^m*Sec[a+b*x]^3*Tan[a+b*x]^(p-2),x] /;
        FreeQ[{a,b,c,d,m},x] && IGtQ[p/2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (c__ + d__ * x_).pow(m_) * (a__ + b__ * x_).sec() * (a__ + b__ * x_).tan().pow(p_),
        with: [c__, d__, m_, a__, b__, p_, x_],
        optional: [c__, d__, m_, a__, b__],
        when: {
            freeq!([a__, b__, c__, d__, m_], x_) && igtq!(&p_ / 2, 0)
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let angle = &a__ + &b__ * x_;
            let first_integrand = linear.pow(&m_) * angle.sec() * angle.tan().pow(&p_ - 2);
            let second_integrand = linear.pow(&m_) * angle.sec().pow(3) * angle.tan().pow(&p_ - 2);
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            -first + second
        },
    ));
}

fn push_rules_rule_4914(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 4914,
        source: "Int[(c_.+d_.*x_)^m_.*Sec[a_.+b_.*x_]^n_.*Tan[a_.+b_.*x_]^p_,x_Symbol] :=
          -Int[(c+d*x)^m*Sec[a+b*x]^n*Tan[a+b*x]^(p-2),x] + Int[(c+d*x)^m*Sec[a+b*x]^(n+2)*Tan[a+b*x]^(p-2),x] /;
        FreeQ[{a,b,c,d,m,n},x] && IGtQ[p/2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [c__, d__, m_, a__, b__, n_, p_, x_],
        optional: [c__, d__, m_, a__, b__, n_],
        when: {
            freeq!([a__, b__, c__, d__, m_, n_], x_)
                && igtq!(&p_ / 2, 0)
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let angle = &a__ + &b__ * x_;
            let first_integrand = linear.pow(&m_) * angle.sec().pow(&n_) * angle.tan().pow(&p_ - 2);
            let second_integrand = linear.pow(&m_) * angle.sec().pow(&n_ + 2) * angle.tan().pow(&p_ - 2);
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            -first + second
        },
    ));
}

fn push_rules_rule_4915(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 4915,
        source: "Int[(c_.+d_.*x_)^m_.*Csc[a_.+b_.*x_]*Cot[a_.+b_.*x_]^p_,x_Symbol] :=
          -Int[(c+d*x)^m*Csc[a+b*x]*Cot[a+b*x]^(p-2),x] + Int[(c+d*x)^m*Csc[a+b*x]^3*Cot[a+b*x]^(p-2),x] /;
        FreeQ[{a,b,c,d,m},x] && IGtQ[p/2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (c__ + d__ * x_).pow(m_) * (a__ + b__ * x_).csc() * (a__ + b__ * x_).cot().pow(p_),
        with: [c__, d__, m_, a__, b__, p_, x_],
        optional: [c__, d__, m_, a__, b__],
        when: {
            freeq!([a__, b__, c__, d__, m_], x_) && igtq!(&p_ / 2, 0)
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let angle = &a__ + &b__ * x_;
            let first_integrand = linear.pow(&m_) * angle.csc() * angle.cot().pow(&p_ - 2);
            let second_integrand = linear.pow(&m_) * angle.csc().pow(3) * angle.cot().pow(&p_ - 2);
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            -first + second
        },
    ));
}

fn push_rules_rule_4916(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 4916,
        source: "Int[(c_.+d_.*x_)^m_.*Csc[a_.+b_.*x_]^n_.*Cot[a_.+b_.*x_]^p_,x_Symbol] :=
          -Int[(c+d*x)^m*Csc[a+b*x]^n*Cot[a+b*x]^(p-2),x] + Int[(c+d*x)^m*Csc[a+b*x]^(n+2)*Cot[a+b*x]^(p-2),x] /;
        FreeQ[{a,b,c,d,m,n},x] && IGtQ[p/2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [c__, d__, m_, a__, b__, n_, p_, x_],
        optional: [c__, d__, m_, a__, b__, n_],
        when: {
            freeq!([a__, b__, c__, d__, m_, n_], x_)
                && igtq!(&p_ / 2, 0)
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let angle = &a__ + &b__ * x_;
            let first_integrand = linear.pow(&m_) * angle.csc().pow(&n_) * angle.cot().pow(&p_ - 2);
            let second_integrand = linear.pow(&m_) * angle.csc().pow(&n_ + 2) * angle.cot().pow(&p_ - 2);
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            -first + second
        },
    ));
}

fn push_rules_rule_4917(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 4917,
        source: "Int[(c_.+d_.*x_)^m_.*Sec[a_.+b_.*x_]^n_.*Tan[a_.+b_.*x_]^p_.,x_Symbol] :=
          Module[{u=IntHide[Sec[a+b*x]^n*Tan[a+b*x]^p,x]},
          (c+d*x)^m \\[Star] u - d*m \\[Star] Int[(c+d*x)^(m-1)*u,x]] /;
        FreeQ[{a,b,c,d,n,p},x] && IGtQ[m,0] && (IntegerQ[n/2] || IntegerQ[(p-1)/2])",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [c__, d__, m_, a__, b__, n_, p_, x_],
        optional: [c__, d__, m_, a__, b__, p_, n_],
        when: {
            freeq!([a__, b__, c__, d__, n_, p_], x_)
                && igtq!(m_, 0)
                && (integerq!(&n_ / 2) || integerq!((&p_ - 1) / 2))
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let angle = &a__ + &b__ * x_;
            let u = rubi_int_hide(&(angle.sec().pow(&n_) * angle.tan().pow(&p_)), x_).rubi_rhs();
            let recursive_integrand = linear.pow(&m_ - 1) * &u;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(linear.pow(&m_), u)
                    - rubi_star(&d__ * &m_, recursive)
        },
    ));
}

fn push_rules_rule_4918(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 4918,
        source: "Int[(c_.+d_.*x_)^m_.*Csc[a_.+b_.*x_]^n_.*Cot[a_.+b_.*x_]^p_.,x_Symbol] :=
          Module[{u=IntHide[Csc[a+b*x]^n*Cot[a+b*x]^p,x]},
          (c+d*x)^m \\[Star] u - d*m \\[Star] Int[(c+d*x)^(m-1)*u,x]] /;
        FreeQ[{a,b,c,d,n,p},x] && IGtQ[m,0] && (IntegerQ[n/2] || IntegerQ[(p-1)/2])",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [c__, d__, m_, a__, b__, n_, p_, x_],
        optional: [c__, d__, m_, a__, b__, p_, n_],
        when: {
            freeq!([a__, b__, c__, d__, n_, p_], x_)
                && igtq!(m_, 0)
                && (integerq!(&n_ / 2) || integerq!((&p_ - 1) / 2))
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let angle = &a__ + &b__ * x_;
            let u = rubi_int_hide(&(angle.csc().pow(&n_) * angle.cot().pow(&p_)), x_).rubi_rhs();
            let recursive_integrand = linear.pow(&m_ - 1) * &u;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(linear.pow(&m_), u)
                    - rubi_star(&d__ * &m_, recursive)
        },
    ));
}

fn push_rules_rule_4919(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 4919,
        source: "Int[(c_.+d_.*x_)^m_.*Csc[a_.+b_.*x_]^n_.*Sec[a_.+b_.*x_]^n_., x_Symbol] :=
          2^n \\[Star] Int[(c+d*x)^m*Csc[2*a+2*b*x]^n,x] /;
        FreeQ[{a,b,c,d,m},x] && IntegerQ[n] && RationalQ[m]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: (c__ + d__ * x_).pow(m_) * (a__ + b__ * x_).csc().pow(n_) * (a__ + b__ * x_).sec().pow(n_),
        with: [c__, d__, m_, a__, b__, n_, x_],
        optional: [c__, d__, m_, a__, b__, n_],
        when: {
            freeq!([a__, b__, c__, d__, m_], x_)
                && integerq!(n_)
                && rationalq!(m_)
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let doubled_angle = Atom::num(2) * &a__ + Atom::num(2) * &b__ * x_;
            let recursive_integrand = linear.pow(&m_) * doubled_angle.csc().pow(&n_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(Atom::num(2).pow(&n_), recursive)
        },
    ));
}

fn push_rules_rule_4920(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 4920,
        source: "Int[(c_.+d_.*x_)^m_.*Csc[a_.+b_.*x_]^n_.*Sec[a_.+b_.*x_]^p_., x_Symbol] :=
          Module[{u=IntHide[Csc[a+b*x]^n*Sec[a+b*x]^p,x]},
          (c+d*x)^m \\[Star] u - d*m \\[Star] Int[(c+d*x)^(m-1)*u,x]] /;
        FreeQ[{a,b,c,d},x] && IntegersQ[n,p] && GtQ[m,0] && NeQ[n,p]",
        desc: "Integration by parts",
        refs: [],
        pattern: (c__ + d__ * x_).pow(m_) * (a__ + b__ * x_).csc().pow(n_) * (a__ + b__ * x_).sec().pow(p_),
        with: [c__, d__, m_, a__, b__, n_, p_, x_],
        optional: [c__, d__, m_, a__, b__, p_, n_],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && integersq!([n_, p_])
                && gtq!(m_, 0)
                && neq!(n_, p_)
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let angle = &a__ + &b__ * x_;
            let u = rubi_int_hide(&(angle.csc().pow(&n_) * angle.sec().pow(&p_)), x_).rubi_rhs();
            let recursive_integrand = linear.pow(&m_ - 1) * &u;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(linear.pow(&m_), u)
                    - rubi_star(&d__ * &m_, recursive)
        },
    ));
}

fn push_rules_rule_4921(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_f_, capital_g_, m_, n_, p_, u_, v_, w_);
    rules.push(rubi_rule!(
        order: 4921,
        source: "Int[u_^m_.*F_[v_]^n_.*G_[w_]^p_.,x_Symbol] :=
          Int[ExpandToSum[u,x]^m*F[ExpandToSum[v,x]]^n*G[ExpandToSum[v,x]]^p,x] /;
        FreeQ[{m,n,p},x] && TrigQ[F] && TrigQ[G] && EqQ[v,w] && LinearQ[{u,v,w},x] && Not[LinearMatchQ[{u,v,w},x]]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: u_.pow(m_) * capital_f_.call( v_).pow(n_) * capital_g_.call( w_).pow(p_),
        with: [u_, m_, capital_f_, v_, n_, capital_g_, w_, p_, x_],
        optional: [m_, p_, n_],
        when: {
            freeq!([m_, n_, p_], x_)
                && rubi_trig_q(&capital_f_)
                && rubi_trig_q(&capital_g_)
                && eqq!(v_, w_)
                && rubi_linear_q_list(&[&u_, &v_, &w_], x_)
                && !rubi_linear_match_q_list(&[&u_, &v_, &w_], x_)
        },
        rhs: {
            let expanded_u = rubi_expand_to_sum(&u_, x_);
            let expanded_v = rubi_expand_to_sum(&v_, x_);
            let recursive_integrand = expanded_u.pow(&m_)
                * rubi_function_head_symbol(&capital_f_).rubi_rhs().call( &expanded_v).pow(&n_)
                * rubi_function_head_symbol(&capital_g_).rubi_rhs().call( expanded_v).pow(&p_);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_4922(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a_, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 4922,
        source: "Int[(e_.+f_.*x_)^m_.*Cos[c_.+d_.*x_]*(a_+b_.*Sin[c_.+d_.*x_])^n_.,x_Symbol] :=
          (e+f*x)^m*(a+b*Sin[c+d*x])^(n+1)/(b*d*(n+1)) -
          f*m/(b*d*(n+1)) \\[Star] Int[(e+f*x)^(m-1)*(a+b*Sin[c+d*x])^(n+1),x] /;
        FreeQ[{a,b,c,d,e,f,n},x] && IGtQ[m,0] && NeQ[n,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern: (e__ + f__ * x_).pow(m_) * (c__ + d__ * x_).cos() * (a_ + b__ * (c__ + d__ * x_).sin()).pow(n_),
        with: [e__, f__, m_, c__, d__, a_, b__, n_, x_],
        optional: [e__, f__, m_, c__, d__, b__, n_],
        when: {
            freeq!([a_, b__, c__, d__, e__, f__, n_], x_)
                && igtq!(m_, 0)
                && neq!(n_, -1)
        },
        rhs: {
            let linear = &e__ + &f__ * x_;
            let angle = &c__ + &d__ * x_;
            let argument = &a_ + &b__ * angle.sin();
            let recursive_integrand = linear.pow(&m_ - 1) * argument.pow(&n_ + 1);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let recursive_term = rubi_simp(&(&(&f__ * &m_ / (&b__ * &d__ * (&n_ + 1))) * &recursive), x_);

            rubi_simp(&(linear.pow(&m_) * argument.pow(&n_ + 1) / (&b__ * &d__ * (&n_ + 1))), x_) - rubi_star(Atom::num(1), recursive_term)
        },
    ));
}

fn push_rules_rule_4923(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a_, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 4923,
        source: "Int[(e_.+f_.*x_)^m_.*Sin[c_.+d_.*x_]*(a_+b_.*Cos[c_.+d_.*x_])^n_.,x_Symbol] :=
          -(e+f*x)^m*(a+b*Cos[c+d*x])^(n+1)/(b*d*(n+1)) +
          f*m/(b*d*(n+1)) \\[Star] Int[(e+f*x)^(m-1)*(a+b*Cos[c+d*x])^(n+1),x] /;
        FreeQ[{a,b,c,d,e,f,n},x] && IGtQ[m,0] && NeQ[n,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern: (e__ + f__ * x_).pow(m_) * (c__ + d__ * x_).sin() * (a_ + b__ * (c__ + d__ * x_).cos()).pow(n_),
        with: [e__, f__, m_, c__, d__, a_, b__, n_, x_],
        optional: [e__, f__, m_, c__, d__, b__, n_],
        when: {
            freeq!([a_, b__, c__, d__, e__, f__, n_], x_)
                && igtq!(m_, 0)
                && neq!(n_, -1)
        },
        rhs: {
            let linear = &e__ + &f__ * x_;
            let angle = &c__ + &d__ * x_;
            let argument = &a_ + &b__ * angle.cos();
            let recursive_integrand = linear.pow(&m_ - 1) * argument.pow(&n_ + 1);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let recursive_term = rubi_simp(&(&(&f__ * &m_ / (&b__ * &d__ * (&n_ + 1))) * &recursive), x_);

            rubi_simp(&(-linear.pow(&m_) * argument.pow(&n_ + 1) / (&b__ * &d__ * (&n_ + 1))), x_)
                    + rubi_star(Atom::num(1), recursive_term)
        },
    ));
}

fn push_rules_rule_4924(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a_, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 4924,
        source: "Int[(e_.+f_.*x_)^m_.*Sec[c_.+d_.*x_]^2*(a_+b_.*Tan[c_.+d_.*x_])^n_.,x_Symbol] :=
          (e+f*x)^m*(a+b*Tan[c+d*x])^(n+1)/(b*d*(n+1)) -
          f*m/(b*d*(n+1)) \\[Star] Int[(e+f*x)^(m-1)*(a+b*Tan[c+d*x])^(n+1),x] /;
        FreeQ[{a,b,c,d,e,f,n},x] && IGtQ[m,0] && NeQ[n,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern: (e__ + f__ * x_).pow(m_) * (c__ + d__ * x_).sec().pow(2) * (a_ + b__ * (c__ + d__ * x_).tan()).pow(n_),
        with: [e__, f__, m_, c__, d__, a_, b__, n_, x_],
        optional: [e__, f__, m_, c__, d__, b__, n_],
        when: {
            freeq!([a_, b__, c__, d__, e__, f__, n_], x_)
                && igtq!(m_, 0)
                && neq!(n_, -1)
        },
        rhs: {
            let linear = &e__ + &f__ * x_;
            let angle = &c__ + &d__ * x_;
            let argument = &a_ + &b__ * angle.tan();
            let recursive_integrand = linear.pow(&m_ - 1) * argument.pow(&n_ + 1);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let recursive_term = rubi_simp(&(&(&f__ * &m_ / (&b__ * &d__ * (&n_ + 1))) * &recursive), x_);

            rubi_simp(&(linear.pow(&m_) * argument.pow(&n_ + 1) / (&b__ * &d__ * (&n_ + 1))), x_) - rubi_star(Atom::num(1), recursive_term)
        },
    ));
}

fn push_rules_rule_4925(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a_, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 4925,
        source: "Int[(e_.+f_.*x_)^m_.*Csc[c_.+d_.*x_]^2*(a_+b_.*Cot[c_.+d_.*x_])^n_.,x_Symbol] :=
          -(e+f*x)^m*(a+b*Cot[c+d*x])^(n+1)/(b*d*(n+1)) +
          f*m/(b*d*(n+1)) \\[Star] Int[(e+f*x)^(m-1)*(a+b*Cot[c+d*x])^(n+1),x] /;
        FreeQ[{a,b,c,d,e,f,n},x] && IGtQ[m,0] && NeQ[n,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern: (e__ + f__ * x_).pow(m_) * (c__ + d__ * x_).csc().pow(2) * (a_ + b__ * (c__ + d__ * x_).cot()).pow(n_),
        with: [e__, f__, m_, c__, d__, a_, b__, n_, x_],
        optional: [e__, f__, m_, c__, d__, b__, n_],
        when: {
            freeq!([a_, b__, c__, d__, e__, f__, n_], x_)
                && igtq!(m_, 0)
                && neq!(n_, -1)
        },
        rhs: {
            let linear = &e__ + &f__ * x_;
            let angle = &c__ + &d__ * x_;
            let argument = &a_ + &b__ * angle.cot();
            let recursive_integrand = linear.pow(&m_ - 1) * argument.pow(&n_ + 1);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let recursive_term = rubi_simp(&(&(&f__ * &m_ / (&b__ * &d__ * (&n_ + 1))) * &recursive), x_);

            rubi_simp(&(-linear.pow(&m_) * argument.pow(&n_ + 1) / (&b__ * &d__ * (&n_ + 1))), x_)
                    + rubi_star(Atom::num(1), recursive_term)
        },
    ));
}

fn push_rules_rule_4926(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a_, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 4926,
        source: "Int[(e_.+f_.*x_)^m_.*Sec[c_.+d_.*x_]*Tan[c_.+d_.*x_]*(a_+b_.*Sec[c_.+d_.*x_])^n_.,x_Symbol] :=
          (e+f*x)^m*(a+b*Sec[c+d*x])^(n+1)/(b*d*(n+1)) -
          f*m/(b*d*(n+1)) \\[Star] Int[(e+f*x)^(m-1)*(a+b*Sec[c+d*x])^(n+1),x] /;
        FreeQ[{a,b,c,d,e,f,n},x] && IGtQ[m,0] && NeQ[n,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern: (e__ + f__ * x_).pow(m_) * (c__ + d__ * x_).sec() * (c__ + d__ * x_).tan() * (a_ + b__ * (c__ + d__ * x_).sec()).pow(n_),
        with: [e__, f__, m_, c__, d__, a_, b__, n_, x_],
        optional: [e__, f__, m_, c__, d__, b__, n_],
        when: {
            freeq!([a_, b__, c__, d__, e__, f__, n_], x_)
                && igtq!(m_, 0)
                && neq!(n_, -1)
        },
        rhs: {
            let linear = &e__ + &f__ * x_;
            let angle = &c__ + &d__ * x_;
            let argument = &a_ + &b__ * angle.sec();
            let recursive_integrand = linear.pow(&m_ - 1) * argument.pow(&n_ + 1);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let recursive_term = rubi_simp(&(&(&f__ * &m_ / (&b__ * &d__ * (&n_ + 1))) * &recursive), x_);

            rubi_simp(&(linear.pow(&m_) * argument.pow(&n_ + 1) / (&b__ * &d__ * (&n_ + 1))), x_) - rubi_star(Atom::num(1), recursive_term)
        },
    ));
}

fn push_rules_rule_4927(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a_, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 4927,
        source: "Int[(e_.+f_.*x_)^m_.*Csc[c_.+d_.*x_]*Cot[c_.+d_.*x_]*(a_+b_.*Csc[c_.+d_.*x_])^n_.,x_Symbol] :=
          -(e+f*x)^m*(a+b*Csc[c+d*x])^(n+1)/(b*d*(n+1)) +
          f*m/(b*d*(n+1)) \\[Star] Int[(e+f*x)^(m-1)*(a+b*Csc[c+d*x])^(n+1),x] /;
        FreeQ[{a,b,c,d,e,f,n},x] && IGtQ[m,0] && NeQ[n,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern: (e__ + f__ * x_).pow(m_) * (c__ + d__ * x_).csc() * (c__ + d__ * x_).cot() * (a_ + b__ * (c__ + d__ * x_).csc()).pow(n_),
        with: [e__, f__, m_, c__, d__, a_, b__, n_, x_],
        optional: [e__, f__, m_, c__, d__, b__, n_],
        when: {
            freeq!([a_, b__, c__, d__, e__, f__, n_], x_)
                && igtq!(m_, 0)
                && neq!(n_, -1)
        },
        rhs: {
            let linear = &e__ + &f__ * x_;
            let angle = &c__ + &d__ * x_;
            let argument = &a_ + &b__ * angle.csc();
            let recursive_integrand = linear.pow(&m_ - 1) * argument.pow(&n_ + 1);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let recursive_term = rubi_simp(&(&(&f__ * &m_ / (&b__ * &d__ * (&n_ + 1))) * &recursive), x_);

            rubi_simp(&(-linear.pow(&m_) * argument.pow(&n_ + 1) / (&b__ * &d__ * (&n_ + 1))), x_)
                    + rubi_star(Atom::num(1), recursive_term)
        },
    ));
}

fn push_rules_rule_4928(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 4928,
        source: "Int[(e_.+f_.*x_)^m_.*Sin[a_.+b_.*x_]^p_.*Sin[c_.+d_.*x_]^q_.,x_Symbol] :=
          Int[ExpandTrigReduce[(e+f*x)^m,Sin[a+b*x]^p*Sin[c+d*x]^q,x],x] /;
        FreeQ[{a,b,c,d,e,f},x] && IGtQ[p,0] && IGtQ[q,0] && IntegerQ[m]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (e__ + f__ * x_).pow(m_) * (a__ + b__ * x_).sin().pow(p_) * (c__ + d__ * x_).sin().pow(q_),
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
            let product = (&a__ + &b__ * x_).sin().pow(&p_)
                * (&c__ + &d__ * x_).sin().pow(&q_);
            let expanded = rubi_expand_trig_reduce(&multiplier, &product, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_4929(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 4929,
        source: "Int[(e_.+f_.*x_)^m_.*Cos[a_.+b_.*x_]^p_.*Cos[c_.+d_.*x_]^q_.,x_Symbol] :=
          Int[ExpandTrigReduce[(e+f*x)^m,Cos[a+b*x]^p*Cos[c+d*x]^q,x],x] /;
        FreeQ[{a,b,c,d,e,f},x] && IGtQ[p,0] && IGtQ[q,0] && IntegerQ[m]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (e__ + f__ * x_).pow(m_) * (a__ + b__ * x_).cos().pow(p_) * (c__ + d__ * x_).cos().pow(q_),
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
            let product = (&a__ + &b__ * x_).cos().pow(&p_)
                * (&c__ + &d__ * x_).cos().pow(&q_);
            let expanded = rubi_expand_trig_reduce(&multiplier, &product, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_4930(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 4930,
        source: "Int[(e_.+f_.*x_)^m_.*Sin[a_.+b_.*x_]^p_.*Cos[c_.+d_.*x_]^q_.,x_Symbol] :=
          Int[ExpandTrigReduce[(e+f*x)^m,Sin[a+b*x]^p*Cos[c+d*x]^q,x],x] /;
        FreeQ[{a,b,c,d,e,f,m},x] && IGtQ[p,0] && IGtQ[q,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (e__ + f__ * x_).pow(m_) * (a__ + b__ * x_).sin().pow(p_) * (c__ + d__ * x_).cos().pow(q_),
        with: [e__, f__, m_, a__, b__, p_, c__, d__, q_, x_],
        optional: [e__, f__, m_, a__, b__, p_, c__, d__, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_], x_)
                && igtq!(p_, 0)
                && igtq!(q_, 0)
        },
        rhs: {
            let multiplier = (&e__ + &f__ * x_).pow(&m_);
            let product = (&a__ + &b__ * x_).sin().pow(&p_)
                * (&c__ + &d__ * x_).cos().pow(&q_);
            let expanded = rubi_expand_trig_reduce(&multiplier, &product, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_4931(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        capital_f_, capital_g_, a__, b__, c__, d__, e__, f__, m_, p_, q_, x_
    );
    rules.push(rubi_rule!(
        order: 4931,
        source: "Int[(e_.+f_.*x_)^m_.*F_[a_.+b_.*x_]^p_.*G_[c_.+d_.*x_]^q_.,x_Symbol] :=
          Int[ExpandTrigExpand[(e+f*x)^m*G[c+d*x]^q,F,c+d*x,p,b/d,x],x] /;
        FreeQ[{a,b,c,d,e,f,m},x] && MemberQ[{Sin,Cos},F] && MemberQ[{Sec,Csc},G] && IGtQ[p,0] && IGtQ[q,0] && EqQ[b*c-a*d,0] && IGtQ[b/d,1]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (e__ + f__ * x_).pow(m_)
            * capital_f_.call( a__ + b__ * x_).pow(p_)
            * capital_g_.call( c__ + d__ * x_).pow(q_),
        with: [e__, f__, m_, capital_f_, a__, b__, p_, capital_g_, c__, d__, q_, x_],
        optional: [e__, f__, m_, a__, b__, c__, d__, q_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_], x_)
                && (rubi_function_head_member_q(&capital_f_, &[Symbol::SIN, rubi_symbols().inert_sin])
                    || rubi_function_head_member_q(&capital_f_, &[Symbol::COS, rubi_symbols().inert_cos]))
                && !rubi_inert_trig_q(&capital_f_)
                && (rubi_function_head_member_q(&capital_g_, &[symbolica::transcendental::sec(), rubi_symbols().inert_sec])
                    || rubi_function_head_member_q(&capital_g_, &[symbolica::transcendental::csc(), rubi_symbols().inert_csc]))
                && !rubi_inert_trig_q(&capital_g_)
                && igtq!(p_, 0)
                && igtq!(q_, 0)
                && eqq!(&b__ * &c__ - &a__ * &d__, 0)
                && igtq!(&b__ / &d__, 1)
        },
        rhs: {
            let angle = &c__ + &d__ * x_;
            let u = (&e__ + &f__ * x_).pow(&m_) * rubi_function_head_symbol(&capital_g_).rubi_rhs().call( &angle).pow(&q_);
            let expanded = rubi_expand_trig_expand(&u, &capital_f_, &angle, &p_, &(&b__ / &d__), x_).rubi_rhs();

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn downvalues_4904_through_4931_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .filter(|order| (4904..=4931).contains(order))
            .collect::<Vec<_>>();
        assert_eq!(orders, (4904..=4931).collect::<Vec<_>>());
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
    (c__ + d__ * x_).pow(m_) * (a__ + b__ * x_).csc().pow(n_) * (a__ + b__ * x_).cot().pow(p_)
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
    (c__ + d__ * x_).pow(m_) * (a__ + b__ * x_).sec().pow(n_) * (a__ + b__ * x_).tan().pow(p_)
}
