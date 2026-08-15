use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_7027(rules);
    push_rules_rule_7028(rules);
    push_rules_rule_7029(rules);
    push_rules_rule_7030(rules);
    push_rules_rule_7031(rules);
    push_rules_rule_7032(rules);
    push_rules_rule_7033(rules);
    push_rules_rule_7034(rules);
    push_rules_rule_7035(rules);
    push_rules_rule_7036(rules);
    push_rules_rule_7037(rules);
    push_rules_rule_7038(rules);
    push_rules_rule_7039(rules);
    push_rules_rule_7040(rules);
    push_rules_rule_7041(rules);
    push_rules_rule_7042(rules);
    // Rubi 8.3 block 17 is commented out in the markdown source.

    push_rules_rule_7043(rules);
    push_rules_rule_7044(rules);
    push_rules_rule_7045(rules);
    push_rules_rule_7046(rules);
    push_rules_rule_7047(rules);
    push_rules_rule_7048(rules);
    push_rules_rule_7049(rules);
    push_rules_rule_7050(rules);
    push_rules_rule_7051(rules);
    push_rules_rule_7052(rules);
}

fn push_rules_rule_7027(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, n_, x_);
    rules.push(rubi_rule!(
        order: 7027,
        source: "Int[ExpIntegralE[n_,a_.+b_.*x_],x_Symbol] :=
          -ExpIntegralE[n+1,a+b*x]/b /;
        FreeQ[{a,b,n},x]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: rubi_exp_integral_e(Atom::var(n_), a__ + b__ * x_),
        with: [n_, a__, b__, x_],
        optional: [a__, b__],
        when: { freeq!([a__, b__, n_], x_) },
        rhs: { rubi_simp(&(-rubi_exp_integral_e(&n_ + 1, &a__ + &b__ * x_) / &b__), x_) },
    ));
}

fn push_rules_rule_7028(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; b__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 7028,
        source: "Int[x_^m_.*ExpIntegralE[n_,b_.*x_],x_Symbol] :=
          -x^m*ExpIntegralE[n+1,b*x]/b +
          m/b \\[Star] Int[x^(m-1)*ExpIntegralE[n+1,b*x],x] /;
        FreeQ[b,x] && EqQ[m+n,0] && IGtQ[m,0]",
        desc: "Inverted integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [m_, n_, b__, x_],
        optional: [m_, b__],
        when: { freeq!(b__, x_) && eqq!(&m_ + &n_, 0) && igtq!(m_, 0) },
        rhs: {
            rubi_simp(&(Atom::num(-1) * x_.pow(&m_) * rubi_exp_integral_e(&n_ + 1, &b__ * x_) / &b__), x_)
                    + rubi_star(&m_, rubi_rhs_int(&(x_.pow(&m_ - 1) * rubi_exp_integral_e(&n_ + 1, &b__ * x_)), x_) / &b__)
        },
    ));
}

fn push_rules_rule_7029(rules: &mut Vec<RubiRule>) {
    rubi_symb!(b__, x_);
    rules.push(rubi_rule!(
        order: 7029,
        source: "Int[ExpIntegralE[1,b_.*x_]/x_,x_Symbol] :=
          b*x*HypergeometricPFQ[{1,1,1},{2,2,2},-b*x] - EulerGamma*Log[x] - 1/2*Log[b*x]^2 /;
        FreeQ[b,x]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: rubi_exp_integral_e(Atom::num(1), b__ * x_) / x_,
        with: [b__, x_],
        optional: [b__],
        when: { freeq!(b__, x_) },
        rhs: {
            let scaled = &b__ * x_;
            rubi_simp(&(&scaled
                    * rubi_hypergeometric_pfq_3_3(
                        Atom::num(1),
                        Atom::num(1),
                        Atom::num(1),
                        Atom::num(2),
                        Atom::num(2),
                        Atom::num(2),
                        -&scaled,
                    )), x_)
                    - rubi_simp(
                        &(Atom::var(symbolica::transcendental::euler_gamma()) * x_.log()),
                        x_,
                    )
                    - rubi_simp(&(scaled.log().pow(2) / 2), x_)
        },
    ));
}

fn push_rules_rule_7030(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; b__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 7030,
        source: "Int[x_^m_*ExpIntegralE[n_,b_.*x_],x_Symbol] :=
          x^(m+1)*ExpIntegralE[n,b*x]/(m+1) +
          b/(m+1) \\[Star] Int[x^(m+1)*ExpIntegralE[n-1,b*x],x] /;
        FreeQ[b,x] && EqQ[m+n,0] && ILtQ[m,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [m_, n_, b__, x_],
        optional: [b__],
        when: { freeq!(b__, x_) && eqq!(&m_ + &n_, 0) && iltq!(m_, -1) },
        rhs: {
            rubi_simp(&(x_.pow(&m_ + 1) * rubi_exp_integral_e(&n_, &b__ * x_) / (&m_ + 1)), x_)
                    + rubi_star(&b__, rubi_rhs_int(&(x_.pow(&m_ + 1) * rubi_exp_integral_e(&n_ - 1, &b__ * x_)), x_) / (&m_ + 1))
        },
    ));
}

fn push_rules_rule_7031(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; b__, d__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 7031,
        source: "Int[(d_.*x_)^m_*ExpIntegralE[n_,b_.*x_],x_Symbol] :=
          (d*x)^m*Gamma[m+1]*Log[x]/(b*(b*x)^m) - (d*x)^(m+1)*HypergeometricPFQ[{m+1,m+1},{m+2,m+2},-b*x]/(d*(m+1)^2) /;
        FreeQ[{b,d,m,n},x] && EqQ[m+n,0] && Not[IntegerQ[m]]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [d__, m_, n_, b__, x_],
        optional: [d__, b__],
        when: { freeq!([b__, d__, m_, n_], x_) && eqq!(&m_ + &n_, 0) && !integerq!(m_) },
        rhs: {
            let scaled_d = &d__ * x_;
            let scaled_b = &b__ * x_;
            rubi_simp(&(scaled_d.pow(&m_) * rubi_gamma_unary(&m_ + 1) * x_.log() / (&b__ * scaled_b.pow(&m_))), x_)
                    - rubi_simp(&(scaled_d.pow(&m_ + 1)
                        * rubi_hypergeometric_pfq_2_2(&m_ + 1, &m_ + 1, &m_ + 2, &m_ + 2, -scaled_b)
                        / (&d__ * (&m_ + 1).pow(2))), x_)
        },
    ));
}

fn push_rules_rule_7032(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; b__, d__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 7032,
        source: "Int[(d_.*x_)^m_.*ExpIntegralE[n_,b_.*x_],x_Symbol] :=
          (d*x)^(m+1)*ExpIntegralE[n,b*x]/(d*(m+n)) - (d*x)^(m+1)*ExpIntegralE[-m,b*x]/(d*(m+n)) /;
        FreeQ[{b,d,m,n},x] && NeQ[m+n,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [d__, m_, n_, b__, x_],
        optional: [d__, m_, b__],
        when: { freeq!([b__, d__, m_, n_], x_) && neq!(&m_ + &n_, 0) },
        rhs: {
            let scaled = &d__ * x_;
            let denominator = &d__ * (&m_ + &n_);
            rubi_simp(&(scaled.pow(&m_ + 1) * rubi_exp_integral_e(n_, &b__ * x_) / &denominator), x_)
                    - rubi_simp(&(scaled.pow(&m_ + 1) * rubi_exp_integral_e(-&m_, &b__ * x_) / denominator), x_)
        },
    ));
}

fn push_rules_rule_7033(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 7033,
        source: "Int[(c_.+d_.*x_)^m_.*ExpIntegralE[n_,a_+b_.*x_],x_Symbol] :=
          -(c+d*x)^m*ExpIntegralE[n+1,a+b*x]/b +
          d*m/b \\[Star] Int[(c+d*x)^(m-1)*ExpIntegralE[n+1,a+b*x],x] /;
        FreeQ[{a,b,c,d,m,n},x] && (IGtQ[m,0] || ILtQ[n,0] || GtQ[m,0] && LtQ[n,-1])",
        desc: "Inverted integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [c__, d__, m_, n_, a__, b__, x_],
        optional: [c__, d__, m_, b__],
        when: {
            freeq!([a__, b__, c__, d__, m_, n_], x_)
                && (igtq!(m_, 0) || iltq!(n_, 0) || gtq!(m_, 0) && ltq!(n_, -1))
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let argument = &a__ + &b__ * x_;
            rubi_simp(&(-linear.pow(&m_) * rubi_exp_integral_e(&n_ + 1, &argument) / &b__), x_)
                    + rubi_star(&d__ * &m_ / &b__, rubi_rhs_int(&(linear.pow(&m_ - 1) * rubi_exp_integral_e(&n_ + 1, argument)), x_))
        },
    ));
}

fn push_rules_rule_7034(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 7034,
        source: "Int[(c_.+d_.*x_)^m_.*ExpIntegralE[n_,a_+b_.*x_],x_Symbol] :=
          (c+d*x)^(m+1)*ExpIntegralE[n,a+b*x]/(d*(m+1)) +
          b/(d*(m+1)) \\[Star] Int[(c+d*x)^(m+1)*ExpIntegralE[n-1,a+b*x],x] /;
        FreeQ[{a,b,c,d,m,n},x] && (IGtQ[n,0] || LtQ[m,-1] && GtQ[n,0]) && NeQ[m,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [c__, d__, m_, n_, a__, b__, x_],
        optional: [c__, d__, m_, b__],
        when: {
            freeq!([a__, b__, c__, d__, m_, n_], x_)
                && (igtq!(n_, 0) || ltq!(m_, -1) && gtq!(n_, 0))
                && neq!(m_, -1)
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let argument = &a__ + &b__ * x_;
            rubi_simp(&(linear.pow(&m_ + 1) * rubi_exp_integral_e(&n_, &argument) / (&d__ * (&m_ + 1))), x_)
                    + rubi_star(b__, rubi_rhs_int(&(linear.pow(&m_ + 1) * rubi_exp_integral_e(&n_ - 1, argument)), x_) / (&d__ * (&m_ + 1)))
        },
    ));
}

fn push_rules_rule_7035(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 7035,
        source: "Int[(c_.+d_.*x_)^m_.*ExpIntegralE[n_,a_+b_.*x_],x_Symbol] :=
          Unintegrable[(c+d*x)^m*ExpIntegralE[n,a+b*x],x] /;
        FreeQ[{a,b,c,d,m,n},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [c__, d__, m_, n_, a__, b__, x_],
        optional: [c__, d__, m_, b__],
        when: { freeq!([a__, b__, c__, d__, m_, n_], x_) },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let argument = &a__ + &b__ * x_;
            rubi_unintegrable(linear.pow(&m_) * rubi_exp_integral_e(n_, argument), x_)
        },
    ));
}

fn push_rules_rule_7036(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, x_);
    rules.push(rubi_rule!(
        order: 7036,
        source: "Int[ExpIntegralEi[a_.+b_.*x_],x_Symbol] :=
          (a+b*x)*ExpIntegralEi[a+b*x]/b - E^(a+b*x)/b /;
        FreeQ[{a,b},x]",
        desc: "Integration by parts",
        refs: [],
        pattern: rubi_exp_integral_ei(a__ + b__ * x_),
        with: [a__, b__, x_],
        optional: [a__, b__],
        when: { freeq!([a__, b__], x_) },
        rhs: {
            let argument = &a__ + &b__ * x_;
            rubi_simp(&(&argument * rubi_exp_integral_ei(&argument) / &b__), x_) - rubi_simp(&(argument.exp() / &b__), x_)
        },
    ));
}

fn push_rules_rule_7037(rules: &mut Vec<RubiRule>) {
    rubi_symb!(b__, x_);
    rules.push(rubi_rule!(
        order: 7037,
        source: "Int[ExpIntegralEi[b_.*x_]/x_,x_Symbol] :=
          Log[x]*(ExpIntegralEi[b*x]+ExpIntegralE[1,-b*x]) - Int[ExpIntegralE[1,-b*x]/x,x] /;
        FreeQ[b,x]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: rubi_exp_integral_ei(b__ * x_) / x_,
        with: [b__, x_],
        optional: [b__],
        when: { freeq!(b__, x_) },
        rhs: {
            let argument = &b__ * x_;
            rubi_simp(&(x_.log() * (rubi_exp_integral_ei(&argument) + rubi_exp_integral_e(Atom::num(1), -argument))), x_)
                    - rubi_rhs_int(&(rubi_exp_integral_e(Atom::num(1), -&b__ * x_) / x_), x_)
        },
    ));
}

fn push_rules_rule_7038(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 7038,
        source: "Int[ExpIntegralEi[a_.+b_.*x_]/(c_.+d_.*x_),x_Symbol] :=
          Unintegrable[ExpIntegralEi[a+b*x]/(c+d*x),x] /;
        FreeQ[{a,b,c,d},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern: rubi_exp_integral_ei(a__ + b__ * x_) / (c__ + d__ * x_),
        with: [a__, b__, c__, d__, x_],
        optional: [a__, b__, c__, d__],
        when: { freeq!([a__, b__, c__, d__], x_) },
        rhs: {
            let argument = &a__ + &b__ * x_;
            let denominator = &c__ + &d__ * x_;
            rubi_unintegrable(rubi_exp_integral_ei(argument) / denominator, x_)
        },
    ));
}

fn push_rules_rule_7039(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, x_);
    rules.push(rubi_rule!(
        order: 7039,
        source: "Int[(c_.+d_.*x_)^m_.*ExpIntegralEi[a_.+b_.*x_],x_Symbol] :=
          (c+d*x)^(m+1)*ExpIntegralEi[a+b*x]/(d*(m+1)) -
          b/(d*(m+1)) \\[Star] Int[(c+d*x)^(m+1)*E^(a+b*x)/(a+b*x),x] /;
        FreeQ[{a,b,c,d,m},x] && NeQ[m,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern: (c__ + d__ * x_).pow(m_) * rubi_exp_integral_ei(a__ + b__ * x_),
        with: [c__, d__, m_, a__, b__, x_],
        optional: [c__, d__, m_, a__, b__],
        when: { freeq!([a__, b__, c__, d__, m_], x_) && neq!(m_, -1) },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let argument = &a__ + &b__ * x_;
            rubi_simp(&(linear.pow(&m_ + 1) * rubi_exp_integral_ei(&argument) / (&d__ * (&m_ + 1))), x_)
                    - rubi_star(b__, rubi_rhs_int(&(linear.pow(&m_ + 1) * &argument.exp() / argument), x_) / (&d__ * (&m_ + 1)))
        },
    ));
}

fn push_rules_rule_7040(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, x_);
    rules.push(rubi_rule!(
        order: 7040,
        source: "Int[ExpIntegralEi[a_.+b_.*x_]^2,x_Symbol] :=
          (a+b*x)*ExpIntegralEi[a+b*x]^2/b -
          2 \\[Star] Int[E^(a+b*x)*ExpIntegralEi[a+b*x],x] /;
        FreeQ[{a,b},x]",
        desc: "Integration by parts",
        refs: [],
        pattern: rubi_exp_integral_ei(a__ + b__ * x_).pow(2),
        with: [a__, b__, x_],
        optional: [a__, b__],
        when: { freeq!([a__, b__], x_) },
        rhs: {
            let argument = &a__ + &b__ * x_;
            rubi_simp(&(&argument * rubi_exp_integral_ei(&argument).pow(2) / &b__), x_)
                    - rubi_star(Atom::num(2), rubi_rhs_int(&(argument.exp() * rubi_exp_integral_ei(argument)), x_))
        },
    ));
}

fn push_rules_rule_7041(rules: &mut Vec<RubiRule>) {
    rubi_symb!(b__, m_, x_);
    rules.push(rubi_rule!(
        order: 7041,
        source: "Int[x_^m_.*ExpIntegralEi[b_.*x_]^2,x_Symbol] :=
          x^(m+1)*ExpIntegralEi[b*x]^2/(m+1) -
          2/(m+1) \\[Star] Int[x^m*E^(b*x)*ExpIntegralEi[b*x],x] /;
        FreeQ[b,x] && IGtQ[m,0]",
        desc: "Integration by parts",
        refs: [],
        pattern: x_.pow(m_) * rubi_exp_integral_ei(b__ * x_).pow(2),
        with: [m_, b__, x_],
        optional: [m_, b__],
        when: { freeq!(b__, x_) && igtq!(m_, 0) },
        rhs: {
            let argument = &b__ * x_;
            rubi_simp(&(x_.pow(&m_ + 1) * rubi_exp_integral_ei(&argument).pow(2) / (&m_ + 1)), x_)
                    - rubi_star(Atom::num(2), rubi_rhs_int(&(x_.pow(&m_) * argument.exp() * rubi_exp_integral_ei(argument)), x_) / (&m_ + 1))
        },
    ));
}

fn push_rules_rule_7042(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, m_, x_);
    rules.push(rubi_rule!(
        order: 7042,
        source: "Int[x_^m_.*ExpIntegralEi[a_+b_.*x_]^2,x_Symbol] :=
          x^(m+1)*ExpIntegralEi[a+b*x]^2/(m+1) +
          a*x^m*ExpIntegralEi[a+b*x]^2/(b*(m+1)) -
          2/(m+1) \\[Star] Int[x^m*E^(a+b*x)*ExpIntegralEi[a+b*x],x] -
          a*m/(b*(m+1)) \\[Star] Int[x^(m-1)*ExpIntegralEi[a+b*x]^2,x] /;
        FreeQ[{a,b},x] && IGtQ[m,0]",
        desc: "Iterated integration by parts",
        refs: [],
        pattern: x_.pow(m_) * rubi_exp_integral_ei(a__ + b__ * x_).pow(2),
        with: [m_, a__, b__, x_],
        optional: [m_, b__],
        when: { freeq!([a__, b__], x_) && igtq!(m_, 0) },
        rhs: {
            let argument = &a__ + &b__ * x_;
            rubi_simp(&(x_.pow(&m_ + 1) * rubi_exp_integral_ei(&argument).pow(2) / (&m_ + 1)), x_)
                    + rubi_simp(&(&a__ * x_.pow(&m_) * rubi_exp_integral_ei(&argument).pow(2) / (&b__ * (&m_ + 1))), x_)
                    - rubi_star(Atom::num(2), rubi_rhs_int(&(x_.pow(&m_) * argument.exp() * rubi_exp_integral_ei(&argument)), x_)
                        / (&m_ + 1))
                    - rubi_star(&a__ * &m_ / (&b__ * (&m_ + 1)), rubi_rhs_int(&(x_.pow(&m_ - 1) * rubi_exp_integral_ei(argument).pow(2)), x_))
        },
    ));
}

fn push_rules_rule_7043(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 7043,
        source: "Int[E^(a_.+b_.*x_)*ExpIntegralEi[c_.+d_.*x_],x_Symbol] :=
          E^(a+b*x)*ExpIntegralEi[c+d*x]/b -
          d/b \\[Star] Int[E^(a+c+(b+d)*x)/(c+d*x),x] /;
        FreeQ[{a,b,c,d},x]",
        desc: "Integration by parts",
        refs: [],
        pattern: (a__ + b__ * x_).exp() * rubi_exp_integral_ei(c__ + d__ * x_),
        with: [a__, b__, c__, d__, x_],
        optional: [a__, b__, c__, d__],
        when: { freeq!([a__, b__, c__, d__], x_) },
        rhs: {
            let exponential = (&a__ + &b__ * x_).exp();
            let argument = &c__ + &d__ * x_;
            let recursive_exponential = (&a__ + &c__ + (&b__ + &d__) * x_).exp();
            rubi_simp(&(exponential * rubi_exp_integral_ei(&argument) / &b__), x_)
                    - rubi_star(d__, rubi_rhs_int(&(recursive_exponential / argument), x_) / &b__)
        },
    ));
}

fn push_rules_rule_7044(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, x_);
    rules.push(rubi_rule!(
        order: 7044,
        source: "Int[x_^m_.*E^(a_.+b_.*x_)*ExpIntegralEi[c_.+d_.*x_],x_Symbol] :=
          x^m*E^(a+b*x)*ExpIntegralEi[c+d*x]/b -
          d/b \\[Star] Int[x^m*E^(a+c+(b+d)*x)/(c+d*x),x] -
          m/b \\[Star] Int[x^(m-1)*E^(a+b*x)*ExpIntegralEi[c+d*x],x] /;
        FreeQ[{a,b,c,d},x] && IGtQ[m,0]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [m_, a__, b__, c__, d__, x_],
        optional: [m_, a__, b__, c__, d__],
        when: { freeq!([a__, b__, c__, d__], x_) && igtq!(m_, 0) },
        rhs: {
            let exponential = (&a__ + &b__ * x_).exp();
            let argument = &c__ + &d__ * x_;
            let recursive_exponential = (&a__ + &c__ + (&b__ + &d__) * x_).exp();
            rubi_simp(&(x_.pow(&m_) * &exponential * rubi_exp_integral_ei(&argument) / &b__), x_)
                    - rubi_star(d__, rubi_rhs_int(&(x_.pow(&m_) * recursive_exponential / &argument), x_) / &b__)
                    - rubi_star(&m_, rubi_rhs_int(&(x_.pow(&m_ - 1) * exponential * rubi_exp_integral_ei(argument)), x_) / &b__)
        },
    ));
}

fn push_rules_rule_7045(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, x_);
    rules.push(rubi_rule!(
        order: 7045,
        source: "Int[x_^m_*E^(a_.+b_.*x_)*ExpIntegralEi[c_.+d_.*x_],x_Symbol] :=
          x^(m+1)*E^(a+b*x)*ExpIntegralEi[c+d*x]/(m+1) -
          d/(m+1) \\[Star] Int[x^(m+1)*E^(a+c+(b+d)*x)/(c+d*x),x] -
          b/(m+1) \\[Star] Int[x^(m+1)*E^(a+b*x)*ExpIntegralEi[c+d*x],x] /;
        FreeQ[{a,b,c,d},x] && ILtQ[m,-1]",
        desc: "Inverted integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [m_, a__, b__, c__, d__, x_],
        optional: [a__, b__, c__, d__],
        when: { freeq!([a__, b__, c__, d__], x_) && iltq!(m_, -1) },
        rhs: {
            let exponential = (&a__ + &b__ * x_).exp();
            let argument = &c__ + &d__ * x_;
            let recursive_exponential = (&a__ + &c__ + (&b__ + &d__) * x_).exp();
            rubi_simp(&(x_.pow(&m_ + 1) * &exponential * rubi_exp_integral_ei(&argument) / (&m_ + 1)), x_)
                    - rubi_star(d__, rubi_rhs_int(&(x_.pow(&m_ + 1) * recursive_exponential / &argument), x_) / (&m_ + 1))
                    - rubi_star(b__, rubi_rhs_int(&(x_.pow(&m_ + 1) * exponential * rubi_exp_integral_ei(argument)), x_) / (&m_ + 1))
        },
    ));
}

fn push_rules_rule_7046(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 7046,
        source: "Int[ExpIntegralEi[d_.*(a_.+b_.*Log[c_.*x_^n_.])],x_Symbol] :=
          x*ExpIntegralEi[d*(a+b*Log[c*x^n])] - b*n*E^(a*d) \\[Star] Int[(c*x^n)^(b*d)/(a+b*Log[c*x^n]),x] /;
        FreeQ[{a,b,c,d,n},x]",
        desc: "Integration by parts",
        refs: [],
        pattern: rubi_exp_integral_ei(d__ * (a__ + b__ * (c__ * x_.pow(n_)).log())),
        with: [d__, a__, b__, c__, n_, x_],
        optional: [d__, a__, b__, c__, n_],
        when: { freeq!([a__, b__, c__, d__, n_], x_) },
        rhs: {
            let log_argument = &c__ * x_.pow(&n_);
            let affine_log = &a__ + &b__ * &log_argument.log();
            let argument = &d__ * &affine_log;
            rubi_simp(&(x_ * rubi_exp_integral_ei(argument)), x_)
                    - rubi_star(&b__ * &n_ * (&a__ * &d__).exp(), rubi_rhs_int(&(log_argument.pow(&b__ * &d__) / affine_log), x_))
        },
    ));
}

fn push_rules_rule_7047(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 7047,
        source: "Int[ExpIntegralEi[d_.*(a_.+b_.*Log[c_.*x_^n_.])]/x_,x_Symbol] :=
          1/n \\[Star] Subst[ExpIntegralEi[d*(a+b*x)],x,Log[c*x^n]] /;
        FreeQ[{a,b,c,d,n},x]",
        desc: "Integration by substitution",
        refs: [],
        pattern: rubi_exp_integral_ei(d__ * (a__ + b__ * (c__ * x_.pow(n_)).log())) / x_,
        with: [d__, a__, b__, c__, n_, x_],
        optional: [d__, a__, b__, c__, n_],
        when: { freeq!([a__, b__, c__, d__, n_], x_) },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let payload = rubi_exp_integral_ei(&d__ * (&a__ + &b__ * sub_atom));
            rubi_star(Atom::num(1) / &n_, rubi_subst(&payload, sub, (&c__ * x_.pow(&n_)).log()))
        },
    ));
}

fn push_rules_rule_7048(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 7048,
        source: "Int[(e_.*x_)^m_.*ExpIntegralEi[d_.*(a_.+b_.*Log[c_.*x_^n_.])],x_Symbol] :=
          (e*x)^(m+1)*ExpIntegralEi[d*(a+b*Log[c*x^n])]/(e*(m+1)) -
          b*n*E^(a*d)*(c*x^n)^(b*d)/((m+1)*(e*x)^(b*d*n)) \\[Star] Int[(e*x)^(m+b*d*n)/(a+b*Log[c*x^n]),x] /;
        FreeQ[{a,b,c,d,e,m,n},x] && NeQ[m,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern: (e__ * x_).pow(m_) * rubi_exp_integral_ei(d__ * (a__ + b__ * (c__ * x_.pow(n_)).log())),
        with: [e__, m_, d__, a__, b__, c__, n_, x_],
        optional: [e__, m_, d__, a__, b__, c__, n_],
        when: { freeq!([a__, b__, c__, d__, e__, m_, n_], x_) && neq!(m_, -1) },
        rhs: {
            let scaled = &e__ * x_;
            let log_argument = &c__ * x_.pow(&n_);
            let affine_log = &a__ + &b__ * &log_argument.log();
            let argument = &d__ * &affine_log;
            let bd = &b__ * &d__;
            let bdn = &bd * &n_;
            rubi_simp(&(scaled.pow(&m_ + 1) * rubi_exp_integral_ei(argument) / (&e__ * (&m_ + 1))), x_)
                    - rubi_star(&b__ * &n_ * (&a__ * &d__).exp() * log_argument.pow(&bd) / ((&m_ + 1) * scaled.pow(&bdn)), rubi_rhs_int(&(scaled.pow(&m_ + &bdn) / affine_log), x_))
        },
    ));
}

fn push_rules_rule_7049(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, x_);
    rules.push(rubi_rule!(
        order: 7049,
        source: "Int[LogIntegral[a_.+b_.*x_],x_Symbol] :=
          (a+b*x)*LogIntegral[a+b*x]/b - ExpIntegralEi[2*Log[a+b*x]]/b /;
        FreeQ[{a,b},x]",
        desc: "Integration by parts",
        refs: [],
        pattern: rubi_log_integral(a__ + b__ * x_),
        with: [a__, b__, x_],
        optional: [a__, b__],
        when: { freeq!([a__, b__], x_) },
        rhs: {
            let argument = &a__ + &b__ * x_;
            rubi_simp(&(&argument * rubi_log_integral(&argument) / &b__), x_) - rubi_simp(&(rubi_exp_integral_ei(Atom::num(2) * argument.log()) / &b__), x_)
        },
    ));
}

fn push_rules_rule_7050(rules: &mut Vec<RubiRule>) {
    rubi_symb!(b__, x_);
    rules.push(rubi_rule!(
        order: 7050,
        source: "Int[LogIntegral[b_.*x_]/x_,x_Symbol] :=
          -b*x + Log[b*x]*LogIntegral[b*x] /;
        FreeQ[b,x]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: rubi_log_integral(b__ * x_) / x_,
        with: [b__, x_],
        optional: [b__],
        when: { freeq!(b__, x_) },
        rhs: {
            let argument = &b__ * x_;
            rubi_simp(&(-&argument), x_) + rubi_simp(&(&argument.log() * rubi_log_integral(argument)), x_)
        },
    ));
}

fn push_rules_rule_7051(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 7051,
        source: "Int[LogIntegral[a_.+b_.*x_]/(c_.+d_.*x_),x_Symbol] :=
          Unintegrable[LogIntegral[a+b*x]/(c+d*x),x] /;
        FreeQ[{a,b,c,d},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern: rubi_log_integral(a__ + b__ * x_) / (c__ + d__ * x_),
        with: [a__, b__, c__, d__, x_],
        optional: [a__, b__, c__, d__],
        when: { freeq!([a__, b__, c__, d__], x_) },
        rhs: {
            let argument = &a__ + &b__ * x_;
            let denominator = &c__ + &d__ * x_;
            rubi_unintegrable(rubi_log_integral(argument) / denominator, x_)
        },
    ));
}

fn push_rules_rule_7052(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, x_);
    rules.push(rubi_rule!(
        order: 7052,
        source: "Int[(c_.+d_.*x_)^m_.*LogIntegral[a_.+b_.*x_],x_Symbol] :=
          (c+d*x)^(m+1)*LogIntegral[a+b*x]/(d*(m+1)) - b/(d*(m+1)) \\[Star] Int[(c+d*x)^(m+1)/Log[a+b*x],x] /;
        FreeQ[{a,b,c,d,m},x] && NeQ[m,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern: (c__ + d__ * x_).pow(m_) * rubi_log_integral(a__ + b__ * x_),
        with: [c__, d__, m_, a__, b__, x_],
        optional: [c__, d__, m_, a__, b__],
        when: { freeq!([a__, b__, c__, d__, m_], x_) && neq!(m_, -1) },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let argument = &a__ + &b__ * x_;
            rubi_simp(&(linear.pow(&m_ + 1) * rubi_log_integral(&argument) / (&d__ * (&m_ + 1))), x_)
                    - rubi_star(b__, rubi_rhs_int(&(linear.pow(&m_ + 1) / argument.log()), x_) / (&d__ * (&m_ + 1)))
        },
    ));
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
    let x_ = symbols.x_;
    (c__ + d__ * x_).pow(m_) * rubi_exp_integral_e(Atom::var(n_), a__ + b__ * x_)
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let b__ = symbols.b__;
    let d__ = symbols.d__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    (d__ * x_).pow(m_) * rubi_exp_integral_e(Atom::var(n_), b__ * x_)
}

#[inline(never)]
fn rubi_shared_pattern_2(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let m_ = symbols.m_;
    let x_ = symbols.x_;
    x_.pow(m_) * (a__ + b__ * x_).exp() * rubi_exp_integral_ei(c__ + d__ * x_)
}

#[inline(never)]
fn rubi_shared_pattern_3(symbols: &RubiSymbols) -> Atom {
    let b__ = symbols.b__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    x_.pow(m_) * rubi_exp_integral_e(Atom::var(n_), b__ * x_)
}
