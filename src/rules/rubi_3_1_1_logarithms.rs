use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_2732(rules);
    push_rules_rule_2733(rules);
    push_rules_rule_2734(rules);
    push_rules_rule_2735(rules);
    push_rules_rule_2736(rules);
    push_rules_rule_2737(rules);
}

fn push_rules_rule_2732(rules: &mut Vec<RubiRule>) {
    rubi_symb!(c__, n_, x_);
    rules.push(rubi_rule!(
        order: 2732,
        source: "Int[Log[c_.*x_^n_.],x_Symbol] :=
          x*Log[c*x^n] - n*x /;
        FreeQ[{c,n},x]",
        desc: "Integration by parts",
        refs: ["G&R 2.711.1, CRC 485, CRC 490"],
        pattern: (c__ * x_.pow(n_)).log(),
        with: [c__, n_, x_],
        optional: [c__, n_],
        when: { freeq!([c__, n_], x_) },
        rhs: {
            rubi_simp(&(x_ * (&c__ * x_.pow(&n_)).log()), x_)
                    - rubi_simp(&(&n_ * x_), x_)
        },
    ));
}

fn push_rules_rule_2733(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 2733,
        source: "Int[(a_.+b_.*Log[c_.*x_^n_.])^p_.,x_Symbol] :=
          x*(a+b*Log[c*x^n])^p - b*n*p \\[Star] Int[(a+b*Log[c*x^n])^(p-1),x] /;
        FreeQ[{a,b,c,n},x] && GtQ[p,0] && IntegerQ[2*p]",
        desc: "Integration by parts",
        refs: ["G&R 2.711.1, CRC 485, CRC 490"],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, n_, p_, x_],
        optional: [a__, b__, c__, n_, p_],
        when: {
            freeq!([a__, b__, c__, n_], x_)
                && gtq!(p_, 0)
                && integerq!(Atom::num(2) * &p_)
        },
        rhs: {
            let logarithmic = &a__ + &b__ * (&c__ * x_.pow(&n_)).log();
            let recursive_integrand = logarithmic.pow(&p_ - 1);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(x_ * logarithmic.pow(&p_)), x_)
                    - rubi_star(&b__ * &n_ * &p_, recursive)
        },
    ));
}

fn push_rules_rule_2734(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 2734,
        source: "Int[(a_.+b_.*Log[c_.*x_^n_.])^p_,x_Symbol] :=
          x*(a+b*Log[c*x^n])^(p+1)/(b*n*(p+1)) - 1/(b*n*(p+1)) \\[Star] Int[(a+b*Log[c*x^n])^(p+1),x] /;
        FreeQ[{a,b,c,n},x] && LtQ[p,-1] && IntegerQ[2*p]",
        desc: "Inverted integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, n_, p_, x_],
        optional: [a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, n_], x_)
                && ltq!(p_, -1)
                && integerq!(Atom::num(2) * &p_)
        },
        rhs: {
            let denominator = &b__ * &n_ * (&p_ + 1);
            let logarithmic = &a__ + &b__ * (&c__ * x_.pow(&n_)).log();
            let raised_power = &p_ + 1;
            let recursive_integrand = logarithmic.pow(&raised_power);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(
                    &(x_ * logarithmic.pow(&raised_power) / &denominator),
                    x_,
                ) - rubi_star(Atom::num(1) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_2735(rules: &mut Vec<RubiRule>) {
    rubi_symb!(c__, x_);
    rules.push(rubi_rule!(
        order: 2735,
        source: "Int[1/Log[c_.*x_],x_Symbol] :=
          LogIntegral[c*x]/c /;
        FreeQ[c,x]",
        desc: "Integration by substitution and algebraic simplification",
        refs: ["CRC 492"],
        pattern: Atom::num(1) / (c__ * x_).log(),
        with: [c__, x_],
        optional: [c__],
        when: { freeq!(c__, x_) },
        rhs: {
            rubi_simp(
                &(rubi_log_integral(&c__ * x_) / c__),
                x_,
            )
        },
    ));
}

fn push_rules_rule_2736(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 2736,
        source: "Int[(a_.+b_.*Log[c_.*x_^n_.])^p_,x_Symbol] :=
          1/(n*c^(1/n)) \\[Star] Subst[Int[E^(x/n)*(a+b*x)^p,x],x,Log[c*x^n]] /;
        FreeQ[{a,b,c,p},x] && IntegerQ[1/n]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, n_, p_, x_],
        optional: [a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, p_], x_)
                && integerq!(Atom::num(1) / &n_)
        },
        rhs: {
            let denominator = &n_ * c__.pow(Atom::num(1) / &n_);
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let substitution_variable = Atom::var(substitution_symbol);
            let transformed_integrand = (&substitution_variable / &n_).exp()
                * (&a__ + &b__ * &substitution_variable).pow(&p_);
            let transformed_primitive = rubi_rhs_int(&transformed_integrand, substitution_symbol);
            let substitution = (&c__ * x_.pow(&n_)).log();
            let substituted = rubi_subst(&transformed_primitive, substitution_symbol, substitution);

            rubi_star(Atom::num(1) / denominator, substituted)
        },
    ));
}

fn push_rules_rule_2737(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 2737,
        source: "Int[(a_.+b_.*Log[c_.*x_^n_.])^p_,x_Symbol] :=
          x/(n*(c*x^n)^(1/n)) \\[Star] Subst[Int[E^(x/n)*(a+b*x)^p,x],x,Log[c*x^n]] /;
        FreeQ[{a,b,c,n,p},x]",
        desc: "Piecewise constant extraction and integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, n_, p_, x_],
        optional: [a__, b__, c__, n_],
        when: { freeq!([a__, b__, c__, n_, p_], x_) },
        rhs: {
            let log_argument = &c__ * x_.pow(&n_);
            let denominator = &n_ * log_argument.pow(Atom::num(1) / &n_);
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let substitution_variable = Atom::var(substitution_symbol);
            let transformed_integrand = (&substitution_variable / &n_).exp()
                * (&a__ + &b__ * &substitution_variable).pow(&p_);
            let transformed_primitive = rubi_rhs_int(&transformed_integrand, substitution_symbol);
            let substitution = log_argument.log();
            let substituted = rubi_subst(&transformed_primitive, substitution_symbol, substitution);

            rubi_star(x_, substituted / denominator)
        },
    ));
}

// Generated shared pattern builders.

#[inline(never)]
fn rubi_shared_pattern_0(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (a__ + b__ * (c__ * x_.pow(n_)).log()).pow(p_)
}
