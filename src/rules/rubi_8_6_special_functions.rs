use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_7111(rules);
    push_rules_rule_7112(rules);
    // Rubi 8.6 block 3 is commented out in the markdown source.

    push_rules_rule_7113(rules);
    push_rules_rule_7114(rules);
    push_rules_rule_7115(rules);
    push_rules_rule_7116(rules);
    push_rules_rule_7117(rules);
    push_rules_rule_7118(rules);
    push_rules_rule_7119(rules);
    push_rules_rule_7120(rules);
    push_rules_rule_7121(rules);
    push_rules_rule_7122(rules);
    push_rules_rule_7123(rules);
    push_rules_rule_7124(rules);
    push_rules_rule_7125(rules);
    push_rules_rule_7126(rules);
    push_rules_rule_7127(rules);
    push_rules_rule_7128(rules);
    push_rules_rule_7129(rules);
    push_rules_rule_7130(rules);
    push_rules_rule_7131(rules);
    push_rules_rule_7132(rules);
    push_rules_rule_7133(rules);
    push_rules_rule_7134(rules);
}

fn push_rules_rule_7111(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, n_, x_);
    rules.push(rubi_rule!(
        order: 7111,
        source: "Int[Gamma[n_,a_.+b_.*x_],x_Symbol] :=
          (a+b*x)*Gamma[n,a+b*x]/b - Gamma[n+1,a+b*x]/b /;
        FreeQ[{a,b,n},x]",
        desc: "Integration by parts",
        refs: [],
        pattern: rubi_gamma(Atom::var(n_), a__ + b__ * x_),
        with: [n_, a__, b__, x_],
        optional: [a__, b__],
        when: { freeq!([a__, b__, n_], x_) },
        rhs: {
            let argument = &a__ + &b__ * x_;
            rubi_simp(&(&argument * rubi_gamma(&n_, &argument) / &b__), x_) - rubi_simp(&(rubi_gamma(&n_ + 1, argument) / &b__), x_)
        },
    ));
}

fn push_rules_rule_7112(rules: &mut Vec<RubiRule>) {
    rubi_symb!(b__, x_);
    rules.push(rubi_rule!(
        order: 7112,
        source: "Int[Gamma[0,b_.*x_]/x_,x_Symbol] :=
          b*x*HypergeometricPFQ[{1,1,1},{2,2,2},-b*x] - EulerGamma*Log[x] - 1/2*Log[b*x]^2 /;
        FreeQ[b,x]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: rubi_gamma(Atom::num(0), b__ * x_) / x_,
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

fn push_rules_rule_7113(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; b__, n_, x_);
    rules.push(rubi_rule!(
        order: 7113,
        source: "Int[Gamma[n_,b_.*x_]/x_,x_Symbol] :=
          -Gamma[n-1,b*x] + (n-1) \\[Star] Int[Gamma[n-1,b*x]/x,x] /;
        FreeQ[b,x] && IGtQ[n,1]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [n_, b__, x_],
        optional: [b__],
        when: { freeq!(b__, x_) && igtq!(n_, 1) },
        rhs: {
            let argument = &b__ * x_;
            rubi_simp(&(-rubi_gamma(&n_ - 1, &argument)), x_)
                    + rubi_star(&n_ - 1, rubi_rhs_int(&(rubi_gamma(&n_ - 1, argument) / x_), x_))
        },
    ));
}

fn push_rules_rule_7114(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; b__, n_, x_);
    rules.push(rubi_rule!(
        order: 7114,
        source: "Int[Gamma[n_,b_.*x_]/x_,x_Symbol] :=
          Gamma[n,b*x]/n + 1/n \\[Star] Int[Gamma[n+1,b*x]/x,x] /;
        FreeQ[b,x] && ILtQ[n,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [n_, b__, x_],
        optional: [b__],
        when: { freeq!(b__, x_) && iltq!(n_, 0) },
        rhs: {
            let argument = &b__ * x_;
            rubi_simp(&(rubi_gamma(&n_, &argument) / &n_), x_) + rubi_star(Atom::num(1) / &n_, rubi_rhs_int(&(rubi_gamma(&n_ + 1, argument) / x_), x_))
        },
    ));
}

fn push_rules_rule_7115(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; b__, n_, x_);
    rules.push(rubi_rule!(
        order: 7115,
        source: "Int[Gamma[n_,b_.*x_]/x_,x_Symbol] :=
          Gamma[n]*Log[x] - (b*x)^n/n^2*HypergeometricPFQ[{n,n},{1+n,1+n},-b*x] /;
        FreeQ[{b,n},x] && Not[IntegerQ[n]]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [n_, b__, x_],
        optional: [b__],
        when: { freeq!([b__, n_], x_) && !integerq!(n_) },
        rhs: {
            let scaled = &b__ * x_;
            rubi_simp(&(rubi_gamma_unary(&n_) * x_.log()), x_)
                    - rubi_simp(&(scaled.pow(&n_) * rubi_hypergeometric_pfq_2_2(&n_, &n_, &n_ + 1, &n_ + 1, -scaled) / n_.pow(2)), x_)
        },
    ));
}

fn push_rules_rule_7116(rules: &mut Vec<RubiRule>) {
    rubi_symb!(b__, d__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 7116,
        source: "Int[(d_.*x_)^m_.*Gamma[n_,b_.*x_],x_Symbol] :=
          (d*x)^(m+1)*Gamma[n,b*x]/(d*(m+1)) -
          (d*x)^m*Gamma[m+n+1,b*x]/(b*(m+1)*(b*x)^m) /;
        FreeQ[{b,d,m,n},x] && NeQ[m,-1]",
        desc: "Integration by parts and piecewise constant extraction",
        refs: [],
        pattern: (d__ * x_).pow(m_) * rubi_gamma(Atom::var(n_), b__ * x_),
        with: [d__, m_, n_, b__, x_],
        optional: [d__, m_, b__],
        when: { freeq!([b__, d__, m_, n_], x_) && neq!(m_, -1) },
        rhs: {
            let scaled = &d__ * x_;
            let argument = &b__ * x_;
            rubi_simp(&(scaled.pow(&m_ + 1) * rubi_gamma(&n_, &argument) / (&d__ * (&m_ + 1))), x_)
                    - rubi_simp(&(scaled.pow(&m_) * rubi_gamma(&m_ + &n_ + 1, &argument) / (&b__ * (&m_ + 1) * argument.pow(&m_))), x_)
        },
    ));
}

fn push_rules_rule_7117(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a_, b__, c_, d__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 7117,
        source: "Int[(c_+d_.*x_)^m_.*Gamma[n_,a_+b_.*x_],x_Symbol] :=
          1/b \\[Star] Subst[Int[(d*x/b)^m*Gamma[n,x],x],x,a+b*x] /;
        FreeQ[{a,b,c,d,m,n},x] && EqQ[b*c-a*d,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (Atom::var(c_) + d__ * x_).pow(m_) * rubi_gamma(Atom::var(n_), Atom::var(a_) + b__ * x_),
        with: [c_, d__, m_, n_, a_, b__, x_],
        optional: [d__, m_, b__],
        when: { freeq!([a_, b__, c_, d__, m_, n_], x_) && eqq!(&b__ * &c_ - &a_ * &d__, 0) },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let payload = (&d__ * &sub_atom / &b__).pow(&m_) * rubi_gamma(&n_, sub_atom);
            let integrated = rubi_rhs_int(&payload, sub);
            rubi_star(Atom::num(1) / &b__, rubi_subst(&integrated, sub, a_ + &b__ * x_))
        },
    ));
}

fn push_rules_rule_7118(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 7118,
        source: "Int[Gamma[n_,a_.+b_.*x_]/(c_.+d_.*x_),x_Symbol] :=
          Int[(a+b*x)^(n-1)/((c+d*x)*E^(a+b*x)),x] + (n-1) \\[Star] Int[Gamma[n-1,a+b*x]/(c+d*x),x] /;
        FreeQ[{a,b,c,d},x] && IGtQ[n,1]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: rubi_gamma(Atom::var(n_), a__ + b__ * x_) / (c__ + d__ * x_),
        with: [n_, a__, b__, c__, d__, x_],
        optional: [a__, b__, c__, d__],
        when: { freeq!([a__, b__, c__, d__], x_) && igtq!(n_, 1) },
        rhs: {
            let argument = &a__ + &b__ * x_;
            let denominator = &c__ + &d__ * x_;
            rubi_rhs_int(&(argument.pow(&n_ - 1) / (&denominator * &argument.exp())), x_)
                    + rubi_star(&n_ - 1, rubi_rhs_int(&(rubi_gamma(&n_ - 1, argument) / denominator), x_))
        },
    ));
}

fn push_rules_rule_7119(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 7119,
        source: "Int[(c_.+d_.*x_)^m_.*Gamma[n_,a_.+b_.*x_],x_Symbol] :=
          Block[{$UseGamma=True},
            (c+d*x)^(m+1)*Gamma[n,a+b*x]/(d*(m+1)) +
            b/(d*(m+1)) \\[Star] Int[(c+d*x)^(m+1)*(a+b*x)^(n-1)/E^(a+b*x),x]] /;
        FreeQ[{a,b,c,d,m,n},x] && (IGtQ[m,0] || IGtQ[n,0] || IntegersQ[m,n]) && NeQ[m,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [c__, d__, m_, n_, a__, b__, x_],
        optional: [c__, d__, m_, a__, b__],
        when: {
            freeq!([a__, b__, c__, d__, m_, n_], x_)
                && (igtq!(m_, 0) || igtq!(n_, 0) || integersq!([m_, n_]))
                && neq!(m_, -1)
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let argument = &a__ + &b__ * x_;
            rubi_simp(&(linear.pow(&m_ + 1) * rubi_gamma(&n_, &argument) / (&d__ * (&m_ + 1))), x_)
                    + rubi_star(b__, rubi_rhs_int(&(linear.pow(&m_ + 1) * argument.pow(&n_ - 1) / argument.exp()), x_) / (&d__ * (&m_ + 1)))
        },
    ));
}

fn push_rules_rule_7120(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 7120,
        source: "Int[(c_.+d_.*x_)^m_.*Gamma[n_,a_.+b_.*x_],x_Symbol] :=
          Unintegrable[(c+d*x)^m*Gamma[n,a+b*x],x] /;
        FreeQ[{a,b,c,d,m,n},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [c__, d__, m_, n_, a__, b__, x_],
        optional: [c__, d__, m_, a__, b__],
        when: { freeq!([a__, b__, c__, d__, m_, n_], x_) },
        rhs: {
            rubi_unintegrable((&c__ + &d__ * x_).pow(&m_) * rubi_gamma(&n_, &a__ + &b__ * x_), x_)
        },
    ));
}

fn push_rules_rule_7121(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, x_);
    rules.push(rubi_rule!(
        order: 7121,
        source: "Int[LogGamma[a_.+b_.*x_],x_Symbol] :=
          PolyGamma[-2,a+b*x]/b /;
        FreeQ[{a,b},x]",
        desc: "Primitive rule",
        refs: [],
        pattern: rubi_log_gamma(a__ + b__ * x_),
        with: [a__, b__, x_],
        optional: [a__, b__],
        when: { freeq!([a__, b__], x_) },
        rhs: {
            let argument = &a__ + &b__ * x_;
            rubi_simp(&(argument.polygamma(-2) / &b__), x_)
        },
    ));
}

fn push_rules_rule_7122(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, x_);
    rules.push(rubi_rule!(
        order: 7122,
        source: "Int[(c_.+d_.*x_)^m_.*LogGamma[a_.+b_.*x_],x_Symbol] :=
          (c+d*x)^m*PolyGamma[-2,a+b*x]/b -
          d*m/b \\[Star] Int[(c+d*x)^(m-1)*PolyGamma[-2,a+b*x],x] /;
        FreeQ[{a,b,c,d},x] && IGtQ[m,0]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [c__, d__, m_, a__, b__, x_],
        optional: [c__, d__, m_, a__, b__],
        when: { freeq!([a__, b__, c__, d__], x_) && igtq!(m_, 0) },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let argument = &a__ + &b__ * x_;
            rubi_simp(&(linear.pow(&m_) * &argument.polygamma(-2) / &b__), x_)
                    - rubi_star(&d__ * &m_ / &b__, rubi_rhs_int(&(linear.pow(&m_ - 1) * argument.polygamma(-2)), x_))
        },
    ));
}

fn push_rules_rule_7123(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, x_);
    rules.push(rubi_rule!(
        order: 7123,
        source: "Int[(c_.+d_.*x_)^m_.*LogGamma[a_.+b_.*x_],x_Symbol] :=
          Unintegrable[(c+d*x)^m*LogGamma[a+b*x],x] /;
        FreeQ[{a,b,c,d,m},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [c__, d__, m_, a__, b__, x_],
        optional: [c__, d__, m_, a__, b__],
        when: { freeq!([a__, b__, c__, d__, m_], x_) },
        rhs: {
            rubi_unintegrable((&c__ + &d__ * x_).pow(&m_) * rubi_log_gamma(&a__ + &b__ * x_), x_)
        },
    ));
}

fn push_rules_rule_7124(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, n_, x_);
    rules.push(rubi_rule!(
        order: 7124,
        source: "Int[PolyGamma[n_,a_.+b_.*x_],x_Symbol] :=
          PolyGamma[n-1,a+b*x]/b /;
        FreeQ[{a,b,n},x]",
        desc: "Primitive rule",
        refs: [],
        pattern: (a__ + b__ * x_).polygamma(n_),
        with: [n_, a__, b__, x_],
        optional: [a__, b__],
        when: { freeq!([a__, b__, n_], x_) },
        rhs: {
            let argument = a__ + &b__ * x_;
            polygamma_primitive(n_, argument, b__, x_).rubi_rhs()
        },
    ));
}

fn push_rules_rule_7125(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 7125,
        source: "Int[(c_.+d_.*x_)^m_.*PolyGamma[n_,a_.+b_.*x_],x_Symbol] :=
          (c+d*x)^m*PolyGamma[n-1,a+b*x]/b - d*m/b \\[Star] Int[(c+d*x)^(m-1)*PolyGamma[n-1,a+b*x],x] /;
        FreeQ[{a,b,c,d,n},x] && GtQ[m,0]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [c__, d__, m_, n_, a__, b__, x_],
        optional: [c__, d__, m_, a__, b__],
        when: { freeq!([a__, b__, c__, d__, n_], x_) && gtq!(m_, 0) },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let argument = &a__ + &b__ * x_;
            rubi_simp(&(linear.pow(&m_) * &argument.polygamma(&n_ - 1) / &b__), x_)
                    - rubi_star(&d__ * &m_ / &b__, rubi_rhs_int(&(linear.pow(&m_ - 1) * argument.polygamma(&n_ - 1)), x_))
        },
    ));
}

fn push_rules_rule_7126(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 7126,
        source: "Int[(c_.+d_.*x_)^m_.*PolyGamma[n_,a_.+b_.*x_],x_Symbol] :=
          (c+d*x)^(m+1)*PolyGamma[n,a+b*x]/(d*(m+1)) -
          b/(d*(m+1)) \\[Star] Int[(c+d*x)^(m+1)*PolyGamma[n+1,a+b*x],x] /;
        FreeQ[{a,b,c,d,n},x] && LtQ[m,-1]",
        desc: "Inverted integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [c__, d__, m_, n_, a__, b__, x_],
        optional: [c__, d__, m_, a__, b__],
        when: { freeq!([a__, b__, c__, d__, n_], x_) && ltq!(m_, -1) },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let argument = &a__ + &b__ * x_;
            rubi_simp(&(linear.pow(&m_ + 1) * &argument.polygamma(&n_) / (&d__ * (&m_ + 1))), x_)
                    - rubi_star(b__, rubi_rhs_int(&(linear.pow(&m_ + 1) * argument.polygamma(&n_ + 1)), x_) / (&d__ * (&m_ + 1)))
        },
    ));
}

fn push_rules_rule_7127(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 7127,
        source: "Int[(c_.+d_.*x_)^m_.*PolyGamma[n_,a_.+b_.*x_],x_Symbol] :=
          Unintegrable[(c+d*x)^m*PolyGamma[n,a+b*x],x] /;
        FreeQ[{a,b,c,d,m,n},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [c__, d__, m_, n_, a__, b__, x_],
        optional: [c__, d__, m_, a__, b__],
        when: { freeq!([a__, b__, c__, d__, m_, n_], x_) },
        rhs: {
            let argument = &a__ + &b__ * x_;
            rubi_unintegrable((&c__ + &d__ * x_).pow(&m_) * argument.polygamma(&n_), x_)
        },
    ));
}

fn push_rules_rule_7128(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, n_, x_);
    rules.push(rubi_rule!(
        order: 7128,
        source: "Int[Gamma[a_.+b_.*x_]^n_.*PolyGamma[0,a_.+b_.*x_],x_Symbol] :=
          Gamma[a+b*x]^n/(b*n) /;
        FreeQ[{a,b,n},x]",
        desc: "Primitive rule",
        refs: [],
        pattern: rubi_gamma_unary(a__ + b__ * x_).pow(n_) * (a__ + b__ * x_).polygamma(0),
        with: [a__, b__, n_, x_],
        optional: [a__, b__, n_],
        when: { freeq!([a__, b__, n_], x_) },
        rhs: {
            let argument = &a__ + &b__ * x_;
            rubi_simp(&(rubi_gamma_unary(argument).pow(&n_) / (&b__ * &n_)), x_)
        },
    ));
}

fn push_rules_rule_7129(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, n_, x_);
    rules.push(rubi_rule!(
        order: 7129,
        source: "Int[((a_.+b_.*x_)!)^n_.*PolyGamma[0,c_.+b_.*x_],x_Symbol] :=
          ((a+b*x)!)^n/(b*n) /;
        FreeQ[{a,b,c,n},x] && EqQ[c,a+1]",
        desc: "Primitive rule",
        refs: [],
        pattern: rubi_factorial(a__ + b__ * x_).pow(n_) * (c__ + b__ * x_).polygamma(0),
        with: [a__, b__, n_, c__, x_],
        optional: [a__, b__, c__, n_],
        when: { freeq!([a__, b__, c__, n_], x_) && eqq!(c__, &a__ + 1) },
        rhs: {
            let argument = &a__ + &b__ * x_;
            rubi_simp(&(rubi_factorial(argument).pow(&n_) / (&b__ * &n_)), x_)
        },
    ));
}

fn push_rules_rule_7130(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 7130,
        source: "Int[Gamma[p_,d_.*(a_.+b_.*Log[c_.*x_^n_.])],x_Symbol] :=
          x*Gamma[p,d*(a+b*Log[c*x^n])] + b*d*n*E^(-a*d) \\[Star] Int[(d*(a+b*Log[c*x^n]))^(p-1)/(c*x^n)^(b*d),x] /;
        FreeQ[{a,b,c,d,n,p},x]",
        desc: "Integration by parts",
        refs: [],
        pattern: rubi_gamma(Atom::var(p_), d__ * (a__ + b__ * (c__ * x_.pow(n_)).log())),
        with: [p_, d__, a__, b__, c__, n_, x_],
        optional: [d__, a__, b__, c__, n_],
        when: { freeq!([a__, b__, c__, d__, n_, p_], x_) },
        rhs: {
            let log_base = &c__ * x_.pow(&n_);
            let argument = &d__ * (&a__ + &b__ * &log_base.log());
            rubi_simp(&(x_ * rubi_gamma(&p_, &argument)), x_)
                    + rubi_star(&b__ * &d__ * &n_ * (-&a__ * &d__).exp(), rubi_rhs_int(&(argument.pow(&p_ - 1) / log_base.pow(&b__ * &d__)), x_))
        },
    ));
}

fn push_rules_rule_7131(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 7131,
        source: "Int[Gamma[p_,d_.*(a_.+b_.*Log[c_.*x_^n_.])]/x_,x_Symbol] :=
          1/n \\[Star] Subst[Gamma[p,d*(a+b*x)],x,Log[c*x^n]] /;
        FreeQ[{a,b,c,d,n,p},x]",
        desc: "Integration by substitution",
        refs: [],
        pattern: rubi_gamma(Atom::var(p_), d__ * (a__ + b__ * (c__ * x_.pow(n_)).log())) / x_,
        with: [p_, d__, a__, b__, c__, n_, x_],
        optional: [d__, a__, b__, c__, n_],
        when: { freeq!([a__, b__, c__, d__, n_, p_], x_) },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let payload = rubi_gamma(&p_, &d__ * (&a__ + &b__ * sub_atom));
            rubi_star(Atom::num(1) / &n_, rubi_subst(&payload, sub, (&c__ * x_.pow(&n_)).log()))
        },
    ));
}

fn push_rules_rule_7132(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 7132,
        source: "Int[(e_.*x_)^m_.*Gamma[p_,d_.*(a_.+b_.*Log[c_.*x_^n_.])],x_Symbol] :=
          (e*x)^(m+1)*Gamma[p,d*(a+b*Log[c*x^n])]/(e*(m+1)) +
          b*d*n*E^(-a*d)*(e*x)^(b*d*n)/((m+1)*(c*x^n)^(b*d)) \\[Star] Int[(e*x)^(m-b*d*n)*(d*(a+b*Log[c*x^n]))^(p-1),x] /;
        FreeQ[{a,b,c,d,e,m,n,p},x] && NeQ[m,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern: (e__ * x_).pow(m_) * rubi_gamma(Atom::var(p_), d__ * (a__ + b__ * (c__ * x_.pow(n_)).log())),
        with: [e__, m_, p_, d__, a__, b__, c__, n_, x_],
        optional: [e__, m_, d__, a__, b__, c__, n_],
        when: { freeq!([a__, b__, c__, d__, e__, m_, n_, p_], x_) && neq!(m_, -1) },
        rhs: {
            let scaled = &e__ * x_;
            let log_base = &c__ * x_.pow(&n_);
            let bd = &b__ * &d__;
            let bdn = &bd * &n_;
            let argument = &d__ * (&a__ + &b__ * &log_base.log());
            rubi_simp(&(scaled.pow(&m_ + 1) * rubi_gamma(&p_, &argument) / (&e__ * (&m_ + 1))), x_)
                    + rubi_star(&b__ * &d__ * &n_ * (-&a__ * &d__).exp() * scaled.pow(&bdn) / ((&m_ + 1) * log_base.pow(bd)), rubi_rhs_int(&(scaled.pow(&m_ - &bdn) * argument.pow(&p_ - 1)), x_))
        },
    ));
}

fn push_rules_rule_7133(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d_, e__, f__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 7133,
        source: "Int[Gamma[p_,f_.*(a_.+b_.*Log[c_.*(d_+e_.*x_)^n_.])],x_Symbol] :=
          1/e \\[Star] Subst[Int[Gamma[p,f*(a+b*Log[c*x^n])],x],x,d+e*x] /;
        FreeQ[{a,b,c,d,e,f,n,p},x]",
        desc: "Integration by substitution",
        refs: [],
        pattern: rubi_gamma(Atom::var(p_), f__ * (a__ + b__ * (c__ * (Atom::var(d_) + e__ * x_).pow(n_)).log())),
        with: [p_, f__, a__, b__, c__, d_, e__, n_, x_],
        optional: [f__, a__, b__, c__, e__, n_],
        when: { freeq!([a__, b__, c__, d_, e__, f__, n_, p_], x_) },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let payload = rubi_gamma(&p_, &f__ * (&a__ + &b__ * (&c__ * sub_atom.pow(&n_)).log()));
            let integrated = rubi_rhs_int(&payload, sub);
            rubi_star(Atom::num(1) / &e__, rubi_subst(&integrated, sub, d_ + &e__ * x_))
        },
    ));
}

fn push_rules_rule_7134(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d_, e__, f__, g_, h__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 7134,
        source: "Int[(g_+h_. x_)^m_.*Gamma[p_,f_.*(a_.+b_.*Log[c_.*(d_+e_.*x_)^n_.])],x_Symbol] :=
          1/e \\[Star] Subst[Int[(g*x/d)^m*Gamma[p,f*(a+b*Log[c*x^n])],x],x,d+e*x] /;
        FreeQ[{a,b,c,d,e,f,g,h,m,n,p},x] && EqQ[e*g-d*h,0]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern: (Atom::var(g_) + h__ * x_).pow(m_)
            * rubi_gamma(Atom::var(p_), f__ * (a__ + b__ * (c__ * (Atom::var(d_) + e__ * x_).pow(n_)).log())),
        with: [g_, h__, m_, p_, f__, a__, b__, c__, d_, e__, n_, x_],
        optional: [h__, m_, f__, a__, b__, c__, e__, n_],
        when: {
            freeq!([a__, b__, c__, d_, e__, f__, g_, h__, m_, n_, p_], x_)
                && eqq!(&e__ * &g_ - &d_ * &h__, 0)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let payload = (&g_ * &sub_atom / &d_).pow(&m_)
                * rubi_gamma(&p_, &f__ * (&a__ + &b__ * (&c__ * sub_atom.pow(&n_)).log()));
            let integrated = rubi_rhs_int(&payload, sub);
            rubi_star(Atom::num(1) / &e__, rubi_subst(&integrated, sub, d_ + &e__ * x_))
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
    (c__ + d__ * x_).pow(m_) * (a__ + b__ * x_).polygamma(n_)
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    (c__ + d__ * x_).pow(m_) * rubi_gamma(Atom::var(n_), a__ + b__ * x_)
}

#[inline(never)]
fn rubi_shared_pattern_2(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let m_ = symbols.m_;
    let x_ = symbols.x_;
    (c__ + d__ * x_).pow(m_) * rubi_log_gamma(a__ + b__ * x_)
}

#[inline(never)]
fn rubi_shared_pattern_3(symbols: &RubiSymbols) -> Atom {
    let b__ = symbols.b__;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    rubi_gamma(Atom::var(n_), b__ * x_) / x_
}
