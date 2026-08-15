use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_2738(rules);
    push_rules_rule_2739(rules);
    push_rules_rule_2740(rules);
    push_rules_rule_2741(rules);
    push_rules_rule_2742(rules);
    push_rules_rule_2743(rules);
    push_rules_rule_2744(rules);
    push_rules_rule_2745(rules);
    push_rules_rule_2746(rules);
    push_rules_rule_2747(rules);
    push_rules_rule_2748(rules);
    push_rules_rule_2749(rules);
}

fn push_rules_rule_2738(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, n_, x_);
    rules.push(rubi_rule!(
        order: 2738,
        source: "Int[(a_.+b_.*Log[c_.*x_^n_.])/x_,x_Symbol] :=
          (a+b*Log[c*x^n])^2/(2*b*n) /;
        FreeQ[{a,b,c,n},x]",
        desc: "Integration by substitution",
        refs: ["CRC 491"],
        pattern: (a__ + b__ * (c__ * x_.pow(n_)).log()) / x_,
        with: [a__, b__, c__, n_, x_],
        optional: [a__, b__, c__, n_],
        when: { freeq!([a__, b__, c__, n_], x_) },
        rhs: {
            let denominator = Atom::num(2) * &b__ * &n_;
            let logarithmic = &a__ + &b__ * (&c__ * x_.pow(&n_)).log();

            rubi_simp(&(logarithmic.pow(2) / denominator), x_)
        },
    ));
}

fn push_rules_rule_2739(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 2739,
        source: "Int[(a_.+b_.*Log[c_.*x_^n_.])^p_./x_,x_Symbol] :=
          1/(b*n) \\[Star] Subst[Int[x^p,x],x,a+b*Log[c*x^n]] /;
        FreeQ[{a,b,c,n,p},x]",
        desc: "Integration by substitution",
        refs: ["CRC 491"],
        pattern: (a__ + b__ * (c__ * x_.pow(n_)).log()).pow(p_) / x_,
        with: [a__, b__, c__, n_, p_, x_],
        optional: [a__, b__, c__, n_, p_],
        when: { freeq!([a__, b__, c__, n_, p_], x_) },
        rhs: {
            let denominator = &b__ * &n_;
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let substitution_variable = Atom::var(substitution_symbol);
            let transformed_primitive =
                rubi_rhs_int(&substitution_variable.pow(&p_), substitution_symbol);
            let substitution = &a__ + &b__ * (&c__ * x_.pow(&n_)).log();
            let substituted = rubi_subst(&transformed_primitive, substitution_symbol, substitution);

            rubi_star(Atom::num(1) / denominator, substituted)
        },
    ));
}

fn push_rules_rule_2740(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 2740,
        source: "Int[(d_.*x_)^m_.*(a_.+b_.*Log[c_.*x_^n_.]),x_Symbol] :=
          b*(d*x)^(m+1)*Log[c*x^n]/(d*(m+1)) /;
        FreeQ[{a,b,c,d,m,n},x] && NeQ[m,-1] && EqQ[a*(m+1)-b*n,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [d__, m_, a__, b__, c__, n_, x_],
        optional: [d__, m_, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, m_, n_], x_)
                && neq!(m_, -1)
                && eqq!(&a__ * (&m_ + 1) - &b__ * &n_, 0)
        },
        rhs: {
            let denominator = &d__ * (&m_ + 1);
            let scaled_monomial = &d__ * x_;

            rubi_simp(
                &(
                &b__ * scaled_monomial.pow(&m_ + 1) * (&c__ * x_.pow(&n_)).log()
                    / denominator
                ),
                x_,
            )
        },
    ));
}

fn push_rules_rule_2741(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 2741,
        source: "Int[(d_.*x_)^m_.*(a_.+b_.*Log[c_.*x_^n_.]),x_Symbol] :=
          (d*x)^(m+1)*(a+b*Log[c*x^n])/(d*(m+1)) - b*n*(d*x)^(m+1)/(d*(m+1)^2) /;
        FreeQ[{a,b,c,d,m,n},x] && NeQ[m,-1]",
        desc: "Integration by parts",
        refs: ["G&R 2.721.1, CRC 496, A&S 4.1.51"],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [d__, m_, a__, b__, c__, n_, x_],
        optional: [d__, m_, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, m_, n_], x_)
                && neq!(m_, -1)
        },
        rhs: {
            let denominator = &d__ * (&m_ + 1);
            let squared_denominator = &d__ * (&m_ + 1).pow(2);
            let scaled_monomial = &d__ * x_;
            let logarithmic = &a__ + &b__ * (&c__ * x_.pow(&n_)).log();

            rubi_simp(
                    &(scaled_monomial.pow(&m_ + 1) * logarithmic / denominator),
                    x_,
                ) - rubi_simp(
                    &(&b__ * &n_ * scaled_monomial.pow(&m_ + 1) / squared_denominator),
                    x_,
                )
        },
    ));
}

fn push_rules_rule_2742(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 2742,
        source: "Int[(d_.*x_)^m_.*(a_.+b_.*Log[c_.*x_^n_.])^p_.,x_Symbol] :=
          (d*x)^(m+1)*(a+b*Log[c*x^n])^p/(d*(m+1)) - b*n*p/(m+1) \\[Star] Int[(d*x)^m*(a+b*Log[c*x^n])^(p-1),x] /;
        FreeQ[{a,b,c,d,m,n},x] && NeQ[m,-1] && GtQ[p,0]",
        desc: "Integration by parts",
        refs: ["G&R 2.721.1, CRC 496, A&S 4.1.51"],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [d__, m_, a__, b__, c__, n_, p_, x_],
        optional: [d__, m_, a__, b__, c__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, m_, n_], x_)
                && neq!(m_, -1)
                && gtq!(p_, 0)
        },
        rhs: {
            let denominator = &d__ * (&m_ + 1);
            let scaled_monomial = &d__ * x_;
            let logarithmic = &a__ + &b__ * (&c__ * x_.pow(&n_)).log();
            let recursive_integrand =
                scaled_monomial.pow(&m_) * logarithmic.pow(&p_ - 1);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(
                    &(scaled_monomial.pow(&m_ + 1) * logarithmic.pow(&p_) / denominator),
                    x_,
                ) - rubi_star(&b__ * &n_ * &p_ / (&m_ + 1), recursive)
        },
    ));
}

fn push_rules_rule_2743(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 2743,
        source: "Int[(d_.*x_)^m_.*(a_.+b_.*Log[c_.*x_^n_.])^p_,x_Symbol] :=
          (d*x)^(m+1)*(a+b*Log[c*x^n])^(p+1)/(b*d*n*(p+1)) - (m+1)/(b*n*(p+1)) \\[Star] Int[(d*x)^m*(a+b*Log[c*x^n])^(p+1),x] /;
        FreeQ[{a,b,c,d,m,n},x] && NeQ[m,-1] && LtQ[p,-1]",
        desc: "Inverted integration by parts",
        refs: ["G&R 2.724.1, CRC 495"],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [d__, m_, a__, b__, c__, n_, p_, x_],
        optional: [d__, m_, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, m_, n_], x_)
                && neq!(m_, -1)
                && ltq!(p_, -1)
        },
        rhs: {
            let denominator = &b__ * &d__ * &n_ * (&p_ + 1);
            let recursive_denominator = &b__ * &n_ * (&p_ + 1);
            let scaled_monomial = &d__ * x_;
            let logarithmic = &a__ + &b__ * (&c__ * x_.pow(&n_)).log();
            let raised_power = &p_ + 1;
            let recursive_integrand = scaled_monomial.pow(&m_) * logarithmic.pow(&raised_power);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(
                    &(scaled_monomial.pow(&m_ + 1) * logarithmic.pow(&raised_power) / denominator),
                    x_,
                ) - rubi_star(&m_ + 1, recursive / recursive_denominator)
        },
    ));
}

fn push_rules_rule_2744(rules: &mut Vec<RubiRule>) {
    rubi_symb!(c__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 2744,
        source: "Int[x_^m_./Log[c_.*x_^n_],x_Symbol] :=
          1/n \\[Star] Subst[Int[1/Log[c*x],x],x,x^n] /;
        FreeQ[{c,m,n},x] && EqQ[m,n-1]",
        desc: "Integration by substitution",
        refs: [],
        pattern: x_.pow(m_) / (c__ * x_.pow(n_)).log(),
        with: [m_, c__, n_, x_],
        optional: [m_, c__],
        when: { freeq!([c__, m_, n_], x_) && eqq!(m_, &n_ - 1) },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let substitution_variable = Atom::var(substitution_symbol);
            let transformed_integrand = Atom::num(1) / (&c__ * &substitution_variable).log();
            let transformed_primitive = rubi_rhs_int(&transformed_integrand, substitution_symbol);
            let substitution = x_.pow(&n_);
            let substituted = rubi_subst(&transformed_primitive, substitution_symbol, substitution);

            rubi_star(Atom::num(1) / n_, substituted)
        },
    ));
}

fn push_rules_rule_2745(rules: &mut Vec<RubiRule>) {
    rubi_symb!(c__, d__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 2745,
        source: "Int[(d_*x_)^m_./Log[c_.*x_^n_],x_Symbol] :=
          (d*x)^m/x^m \\[Star] Int[x^m/Log[c*x^n],x] /;
        FreeQ[{c,d,m,n},x] && EqQ[m,n-1]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: (d__ * x_).pow(m_) / (c__ * x_.pow(n_)).log(),
        with: [d__, m_, c__, n_, x_],
        optional: [m_, c__],
        when: {
            freeq!([c__, d__, m_, n_], x_)
                && eqq!(m_, &n_ - 1)
        },
        rhs: {
            let recursive_integrand = x_.pow(&m_) / (&c__ * x_.pow(&n_)).log();
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let scaled_monomial = &d__ * x_;

            rubi_star(scaled_monomial.pow(&m_), recursive / x_.pow(m_))
        },
    ));
}

fn push_rules_rule_2746(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 2746,
        source: "Int[x_^m_.*(a_.+b_.*Log[c_.*x_])^p_,x_Symbol] :=
          1/c^(m+1) \\[Star] Subst[Int[E^((m+1)*x)*(a+b*x)^p,x],x,Log[c*x]] /;
        FreeQ[{a,b,c,p},x] && IntegerQ[m]",
        desc: "Integration by substitution",
        refs: [],
        pattern: x_.pow(m_) * (a__ + b__ * (c__ * x_).log()).pow(p_),
        with: [m_, a__, b__, c__, p_, x_],
        optional: [m_, a__, b__, c__],
        when: { freeq!([a__, b__, c__, p_], x_) && integerq!(m_) },
        rhs: {
            let denominator = c__.pow(&m_ + 1);
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let substitution_variable = Atom::var(substitution_symbol);
            let transformed_integrand = ((&m_ + 1) * &substitution_variable).exp()
                * (&a__ + &b__ * &substitution_variable).pow(&p_);
            let transformed_primitive = rubi_rhs_int(&transformed_integrand, substitution_symbol);
            let substitution = (&c__ * x_).log();
            let substituted = rubi_subst(&transformed_primitive, substitution_symbol, substitution);

            rubi_star(Atom::num(1) / denominator, substituted)
        },
    ));
}

fn push_rules_rule_2747(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 2747,
        source: "Int[(d_.*x_)^m_.*(a_.+b_.*Log[c_.*x_^n_.])^p_,x_Symbol] :=
          (d*x)^(m+1)/(d*n*(c*x^n)^((m+1)/n)) \\[Star] Subst[Int[E^((m+1)/n*x)*(a+b*x)^p,x],x,Log[c*x^n]] /;
        FreeQ[{a,b,c,d,m,n,p},x]",
        desc: "Piecewise constant extraction and integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [d__, m_, a__, b__, c__, n_, p_, x_],
        optional: [d__, m_, a__, b__, c__, n_],
        when: { freeq!([a__, b__, c__, d__, m_, n_, p_], x_) },
        rhs: {
            let exponent = (&m_ + 1) / &n_;
            let log_argument = &c__ * x_.pow(&n_);
            let denominator = &d__ * &n_ * log_argument.pow(&exponent);
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let substitution_variable = Atom::var(substitution_symbol);
            let transformed_integrand = (&exponent * &substitution_variable).exp()
                * (&a__ + &b__ * &substitution_variable).pow(&p_);
            let transformed_primitive = rubi_rhs_int(&transformed_integrand, substitution_symbol);
            let substitution = log_argument.log();
            let scaled_monomial = &d__ * x_;
            let substituted = rubi_subst(&transformed_primitive, substitution_symbol, substitution);

            rubi_star(scaled_monomial.pow(&m_ + 1), substituted
                    / denominator)
        },
    ));
}

fn push_rules_rule_2748(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 2748,
        source: "Int[(d_.*x_^q_)^m_*(a_.+b_.*Log[c_.*x_^n_.])^p_.,x_Symbol] :=
          (d*x^q)^m/x^(m*q) \\[Star] Int[x^(m*q)*(a+b*Log[c*x^n])^p,x] /;
        FreeQ[{a,b,c,d,m,n,p,q},x]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: (d__ * x_.pow(q_)).pow(m_) * (a__ + b__ * (c__ * x_.pow(n_)).log()).pow(p_),
        with: [d__, q_, m_, a__, b__, c__, n_, p_, x_],
        optional: [d__, a__, b__, c__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, m_, n_, p_, q_], x_)
        },
        rhs: {
            let total_power = &m_ * &q_;
            let logarithmic = &a__ + &b__ * (&c__ * x_.pow(&n_)).log();
            let recursive_integrand = x_.pow(&total_power) * logarithmic.pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let scaled_power_monomial = &d__ * x_.pow(&q_);

            rubi_star(scaled_power_monomial.pow(&m_), recursive / x_.pow(total_power))
        },
    ));
}

fn push_rules_rule_2749(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d1__, d2__, m1_, m2_, n_, p_, q1_, q2_, x_);
    rules.push(rubi_rule!(
        order: 2749,
        source: "Int[(d1_.*x_^q1_)^m1_*(d2_.*x_^q2_)^m2_*(a_.+b_.*Log[c_.*x_^n_.])^p_.,x_Symbol] :=
          (d1*x^q1)^m1*(d2*x^q2)^m2/x^(m1*q1+m2*q2) \\[Star] Int[x^(m1*q1+m2*q2)*(a+b*Log[c*x^n])^p,x] /;
        FreeQ[{a,b,c,d1,d2,m1,m2,n,p,q1,q2},x]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: (d1__ * x_.pow(q1_)).pow(m1_)
            * (d2__ * x_.pow(q2_)).pow(m2_)
            * (a__ + b__ * (c__ * x_.pow(n_)).log()).pow(p_),
        with: [d1__, q1_, m1_, d2__, q2_, m2_, a__, b__, c__, n_, p_, x_],
        optional: [d1__, d2__, a__, b__, c__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d1__, d2__, m1_, m2_, n_, p_, q1_, q2_], x_)
        },
        rhs: {
            let total_power = &m1_ * &q1_ + &m2_ * &q2_;
            let logarithmic = &a__ + &b__ * (&c__ * x_.pow(&n_)).log();
            let recursive_integrand = x_.pow(&total_power) * logarithmic.pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let first_monomial = &d1__ * x_.pow(&q1_);
            let second_monomial = &d2__ * x_.pow(&q2_);

            rubi_star(first_monomial.pow(&m1_) * second_monomial.pow(&m2_) / x_.pow(total_power), recursive)
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
    (d__ * x_).pow(m_) * (a__ + b__ * (c__ * x_.pow(n_)).log())
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
    (d__ * x_).pow(m_) * (a__ + b__ * (c__ * x_.pow(n_)).log()).pow(p_)
}
