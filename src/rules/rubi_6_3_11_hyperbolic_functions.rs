use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_5923(rules);
    push_rules_rule_5924(rules);
    push_rules_rule_5925(rules);
    push_rules_rule_5926(rules);
    push_rules_rule_5927(rules);
    push_rules_rule_5928(rules);
    push_rules_rule_5929(rules);
    push_rules_rule_5930(rules);
    push_rules_rule_5931(rules);
    push_rules_rule_5932(rules);
    push_rules_rule_5933(rules);
    push_rules_rule_5934(rules);
    push_rules_rule_5935(rules);
    push_rules_rule_5936(rules);
    push_rules_rule_5937(rules);
    push_rules_rule_5938(rules);
    push_rules_rule_5939(rules);
    push_rules_rule_5940(rules);
    push_rules_rule_5941(rules);
    push_rules_rule_5942(rules);
}

fn push_rules_rule_5923(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5923,
        source: "Int[(a_.+b_.*Tanh[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
          1/n \\[Star] Subst[Int[x^(1/n-1)*(a+b*Tanh[c+d*x])^p,x],x,x^n] /;
        FreeQ[{a,b,c,d,p},x] && IGtQ[1/n,0] && IntegerQ[p]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, n_, p_, x_],
        optional: [a__, b__, c__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__, p_], x_)
                && igtq!(Atom::num(1) / &n_, 0)
                && integerq!(p_)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub = Atom::var(substitution_symbol);
            let transformed_integrand = sub.pow(Atom::num(1) / &n_ - 1)
                * (&a__ + &b__ * (&c__ + &d__ * &sub).tanh()).pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);

            rubi_star(Atom::num(1) / &n_, rubi_subst(&transformed, substitution_symbol, x_.pow(&n_)))
        },
    ));
}

fn push_rules_rule_5924(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5924,
        source: "Int[(a_.+b_.*Coth[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
          1/n \\[Star] Subst[Int[x^(1/n-1)*(a+b*Coth[c+d*x])^p,x],x,x^n] /;
        FreeQ[{a,b,c,d,p},x] && IGtQ[1/n,0] && IntegerQ[p]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, n_, p_, x_],
        optional: [a__, b__, c__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__, p_], x_)
                && igtq!(Atom::num(1) / &n_, 0)
                && integerq!(p_)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub = Atom::var(substitution_symbol);
            let transformed_integrand = sub.pow(Atom::num(1) / &n_ - 1)
                * (&a__ + &b__ * (&c__ + &d__ * &sub).coth()).pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);

            rubi_star(Atom::num(1) / &n_, rubi_subst(&transformed, substitution_symbol, x_.pow(&n_)))
        },
    ));
}

fn push_rules_rule_5925(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5925,
        source: "Int[(a_.+b_.*Tanh[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
          Integral[(a+b*Tanh[c+d*x^n])^p,x] /;
        FreeQ[{a,b,c,d,n,p},x]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, n_, p_, x_],
        optional: [a__, b__, c__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__, n_, p_], x_)
        },
        rhs: {
            rubi_simp(&(rubi_deferred_integral(
                &(&a__ + &b__ * (&c__ + &d__ * x_.pow(&n_)).tanh()).pow(&p_),
                x_,
            )), x_)
        },
    ));
}

fn push_rules_rule_5926(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5926,
        source: "Int[(a_.+b_.*Coth[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
          Integral[(a+b*Coth[c+d*x^n])^p,x] /;
        FreeQ[{a,b,c,d,n,p},x]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, n_, p_, x_],
        optional: [a__, b__, c__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__, n_, p_], x_)
        },
        rhs: {
            rubi_simp(&(rubi_deferred_integral(
                &(&a__ + &b__ * (&c__ + &d__ * x_.pow(&n_)).coth()).pow(&p_),
                x_,
            )), x_)
        },
    ));
}

fn push_rules_rule_5927(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, n_, p_, u_);
    rules.push(rubi_rule!(
        order: 5927,
        source: "Int[(a_.+b_.*Tanh[c_.+d_.*u_^n_])^p_.,x_Symbol] :=
          1/Coefficient[u,x,1] \\[Star] Subst[Int[(a+b*Tanh[c+d*x^n])^p,x],x,u] /;
        FreeQ[{a,b,c,d,n,p},x] && LinearQ[u,x] && NeQ[u,x]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (a__ + b__ * (c__ + d__ * Atom::var(u_).pow(n_)).tanh()).pow(p_),
        with: [a__, b__, c__, d__, u_, n_, p_, x_],
        optional: [a__, b__, c__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__, n_, p_], x_)
                && rubi_linear_q(&u_, x_)
                && neq!(u_, x_)
        },
        rhs: {
            let coefficient = rubi_coefficient(&u_, x_, 1).rubi_rhs();
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub = Atom::var(substitution_symbol);
            let transformed_integrand =
                (&a__ + &b__ * (&c__ + &d__ * sub.pow(&n_)).tanh()).pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);

            rubi_star(Atom::num(1) / coefficient, rubi_subst(&transformed, substitution_symbol, &u_))
        },
    ));
}

fn push_rules_rule_5928(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, n_, p_, u_);
    rules.push(rubi_rule!(
        order: 5928,
        source: "Int[(a_.+b_.*Coth[c_.+d_.*u_^n_])^p_.,x_Symbol] :=
          1/Coefficient[u,x,1] \\[Star] Subst[Int[(a+b*Coth[c+d*x^n])^p,x],x,u] /;
        FreeQ[{a,b,c,d,n,p},x] && LinearQ[u,x] && NeQ[u,x]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (a__ + b__ * (c__ + d__ * Atom::var(u_).pow(n_)).coth()).pow(p_),
        with: [a__, b__, c__, d__, u_, n_, p_, x_],
        optional: [a__, b__, c__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__, n_, p_], x_)
                && rubi_linear_q(&u_, x_)
                && neq!(u_, x_)
        },
        rhs: {
            let coefficient = rubi_coefficient(&u_, x_, 1).rubi_rhs();
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub = Atom::var(substitution_symbol);
            let transformed_integrand =
                (&a__ + &b__ * (&c__ + &d__ * sub.pow(&n_)).coth()).pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);

            rubi_star(Atom::num(1) / coefficient, rubi_subst(&transformed, substitution_symbol, &u_))
        },
    ));
}

fn push_rules_rule_5929(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, p_, u_);
    rules.push(rubi_rule!(
        order: 5929,
        source: "Int[(a_.+b_.*Tanh[u_])^p_.,x_Symbol] :=
          Int[(a+b*Tanh[ExpandToSum[u,x]])^p,x] /;
        FreeQ[{a,b,p},x] && BinomialQ[u,x] && Not[BinomialMatchQ[u,x]]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: (a__ + b__ * Atom::var(u_).tanh()).pow(p_),
        with: [a__, b__, u_, p_, x_],
        optional: [a__, b__, p_],
        when: {
            freeq!([a__, b__, p_], x_)
                && rubi_binomial_q(&u_, x_)
                && !rubi_binomial_match_q(&u_, x_)
        },
        rhs: {
            rubi_rhs_int(
                &(&a__ + &b__ * rubi_expand_to_sum(&u_, x_).tanh()).pow(&p_),
                x_,
            )
        },
    ));
}

fn push_rules_rule_5930(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, p_, u_);
    rules.push(rubi_rule!(
        order: 5930,
        source: "Int[(a_.+b_.*Coth[u_])^p_.,x_Symbol] :=
          Int[(a+b*Coth[ExpandToSum[u,x]])^p,x] /;
        FreeQ[{a,b,p},x] && BinomialQ[u,x] && Not[BinomialMatchQ[u,x]]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: (a__ + b__ * Atom::var(u_).coth()).pow(p_),
        with: [a__, b__, u_, p_, x_],
        optional: [a__, b__, p_],
        when: {
            freeq!([a__, b__, p_], x_)
                && rubi_binomial_q(&u_, x_)
                && !rubi_binomial_match_q(&u_, x_)
        },
        rhs: {
            rubi_rhs_int(
                &(&a__ + &b__ * rubi_expand_to_sum(&u_, x_).coth()).pow(&p_),
                x_,
            )
        },
    ));
}

fn push_rules_rule_5931(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5931,
        source: "Int[x_^m_.*(a_.+b_.*Tanh[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
          1/n \\[Star] Subst[Int[x^(Simplify[(m+1)/n]-1)*(a+b*Tanh[c+d*x])^p,x],x,x^n] /;
        FreeQ[{a,b,c,d,m,n,p},x] && IGtQ[Simplify[(m+1)/n],0] && IntegerQ[p]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [m_, a__, b__, c__, d__, n_, p_, x_],
        optional: [m_, a__, b__, c__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__, m_, n_, p_], x_)
                && igtq!(rubi_simplify(&((&m_ + 1) / &n_)), 0)
                && integerq!(p_)
        },
        rhs: {
            let s = rubi_simplify(&((&m_ + 1) / &n_));
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub = Atom::var(substitution_symbol);
            let transformed_integrand =
                sub.pow(&s - 1) * (&a__ + &b__ * (&c__ + &d__ * &sub).tanh()).pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);

            rubi_star(Atom::num(1) / &n_, rubi_subst(&transformed, substitution_symbol, x_.pow(&n_)))
        },
    ));
}

fn push_rules_rule_5932(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5932,
        source: "Int[x_^m_.*(a_.+b_.*Coth[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
          1/n \\[Star] Subst[Int[x^(Simplify[(m+1)/n]-1)*(a+b*Coth[c+d*x])^p,x],x,x^n] /;
        FreeQ[{a,b,c,d,m,n,p},x] && IGtQ[Simplify[(m+1)/n],0] && IntegerQ[p]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [m_, a__, b__, c__, d__, n_, p_, x_],
        optional: [m_, a__, b__, c__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__, m_, n_, p_], x_)
                && igtq!(rubi_simplify(&((&m_ + 1) / &n_)), 0)
                && integerq!(p_)
        },
        rhs: {
            let s = rubi_simplify(&((&m_ + 1) / &n_));
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub = Atom::var(substitution_symbol);
            let transformed_integrand =
                sub.pow(&s - 1) * (&a__ + &b__ * (&c__ + &d__ * &sub).coth()).pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);

            rubi_star(Atom::num(1) / &n_, rubi_subst(&transformed, substitution_symbol, x_.pow(&n_)))
        },
    ));
}

fn push_rules_rule_5933(rules: &mut Vec<RubiRule>) {
    rubi_symb!(c__, d__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5933,
        source: "Int[x_^m_.*Tanh[c_.+d_.*x_^n_]^2,x_Symbol] :=
          -x^(m-n+1)*Tanh[c+d*x^n]/(d*n) + Int[x^m,x] + (m-n+1)/(d*n)*Int[x^(m-n)*Tanh[c+d*x^n],x] /;
        FreeQ[{c,d,m,n},x]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern: x_.pow(m_) * (c__ + d__ * x_.pow(n_)).tanh().pow(2),
        with: [m_, c__, d__, n_, x_],
        optional: [m_, c__, d__],
        when: { freeq!([c__, d__, m_, n_], x_) },
        rhs: {
            let angle = &c__ + &d__ * x_.pow(&n_);
            let recursive1 = rubi_rhs_int(x_.pow(&m_), x_);
            let recursive2 = rubi_rhs_int(&(x_.pow(&m_ - &n_) * angle.tanh()), x_);

            rubi_simp(&(Atom::num(-1) * x_.pow(&m_ - &n_ + 1) * angle.tanh() / (&d__ * &n_)), x_)
                    + recursive1
                    + rubi_simp(&((&m_ - &n_ + 1) * recursive2 / (&d__ * n_)), x_)
        },
    ));
}

fn push_rules_rule_5934(rules: &mut Vec<RubiRule>) {
    rubi_symb!(c__, d__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5934,
        source: "Int[x_^m_.*Coth[c_.+d_.*x_^n_]^2,x_Symbol] :=
          -x^(m-n+1)*Coth[c+d*x^n]/(d*n) + Int[x^m,x] + (m-n+1)/(d*n)*Int[x^(m-n)*Coth[c+d*x^n],x] /;
        FreeQ[{c,d,m,n},x]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern: x_.pow(m_) * (c__ + d__ * x_.pow(n_)).coth().pow(2),
        with: [m_, c__, d__, n_, x_],
        optional: [m_, c__, d__],
        when: { freeq!([c__, d__, m_, n_], x_) },
        rhs: {
            let angle = &c__ + &d__ * x_.pow(&n_);
            let recursive1 = rubi_rhs_int(x_.pow(&m_), x_);
            let recursive2 = rubi_rhs_int(&(x_.pow(&m_ - &n_) * angle.coth()), x_);

            rubi_simp(&(Atom::num(-1) * x_.pow(&m_ - &n_ + 1) * angle.coth() / (&d__ * &n_)), x_)
                    + recursive1
                    + rubi_simp(&((&m_ - &n_ + 1) * recursive2 / (&d__ * n_)), x_)
        },
    ));
}

fn push_rules_rule_5935(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5935,
        source: "Int[x_^m_.*(a_.+b_.*Tanh[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
          Integral[x^m*(a+b*Tanh[c+d*x^n])^p,x] /;
        FreeQ[{a,b,c,d,m,n,p},x]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [m_, a__, b__, c__, d__, n_, p_, x_],
        optional: [m_, a__, b__, c__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__, m_, n_, p_], x_)
        },
        rhs: {
            rubi_simp(&(rubi_deferred_integral(
                &(x_.pow(&m_)
                    * (&a__ + &b__ * (&c__ + &d__ * x_.pow(&n_)).tanh()).pow(&p_)),
                x_,
            )), x_)
        },
    ));
}

fn push_rules_rule_5936(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5936,
        source: "Int[x_^m_.*(a_.+b_.*Coth[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
          Integral[x^m*(a+b*Coth[c+d*x^n])^p,x] /;
        FreeQ[{a,b,c,d,m,n,p},x]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [m_, a__, b__, c__, d__, n_, p_, x_],
        optional: [m_, a__, b__, c__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__, m_, n_, p_], x_)
        },
        rhs: {
            rubi_simp(&(rubi_deferred_integral(
                &(x_.pow(&m_)
                    * (&a__ + &b__ * (&c__ + &d__ * x_.pow(&n_)).coth()).pow(&p_)),
                x_,
            )), x_)
        },
    ));
}

fn push_rules_rule_5937(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5937,
        source: "Int[(e_*x_)^m_.*(a_.+b_.*Tanh[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
          e^IntPart[m]*(e*x)^FracPart[m]/x^FracPart[m] \\[Star] Int[x^m*(a+b*Tanh[c+d*x^n])^p,x] /;
        FreeQ[{a,b,c,d,e,m,n,p},x]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: (e__ * x_).pow(m_) * (a__ + b__ * (c__ + d__ * x_.pow(n_)).tanh()).pow(p_),
        with: [e__, m_, a__, b__, c__, d__, n_, p_, x_],
        optional: [a__, b__, c__, d__, p_, m_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_, p_], x_)
        },
        rhs: {
            let frac_m = rubi_frac_part(&m_);
            let recursive_integrand =
                x_.pow(&m_) * (&a__ + &b__ * (&c__ + &d__ * x_.pow(&n_)).tanh()).pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(e__.pow(rubi_int_part(&m_)) * (&e__ * x_).pow(&frac_m)
                    / x_.pow(frac_m), recursive)
        },
    ));
}

fn push_rules_rule_5938(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5938,
        source: "Int[(e_*x_)^m_.*(a_.+b_.*Coth[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
          e^IntPart[m]*(e*x)^FracPart[m]/x^FracPart[m] \\[Star] Int[x^m*(a+b*Coth[c+d*x^n])^p,x] /;
        FreeQ[{a,b,c,d,e,m,n,p},x]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: (e__ * x_).pow(m_) * (a__ + b__ * (c__ + d__ * x_.pow(n_)).coth()).pow(p_),
        with: [e__, m_, a__, b__, c__, d__, n_, p_, x_],
        optional: [a__, b__, c__, d__, p_, m_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_, p_], x_)
        },
        rhs: {
            let frac_m = rubi_frac_part(&m_);
            let recursive_integrand =
                x_.pow(&m_) * (&a__ + &b__ * (&c__ + &d__ * x_.pow(&n_)).coth()).pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(e__.pow(rubi_int_part(&m_)) * (&e__ * x_).pow(&frac_m)
                    / x_.pow(frac_m), recursive)
        },
    ));
}

fn push_rules_rule_5939(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, e__, m_, p_, u_, x_);
    rules.push(rubi_rule!(
        order: 5939,
        source: "Int[(e_*x_)^m_.*(a_.+b_.*Tanh[u_])^p_.,x_Symbol] :=
          Int[(e*x)^m*(a+b*Tanh[ExpandToSum[u,x]])^p,x] /;
        FreeQ[{a,b,e,m,p},x] && BinomialQ[u,x] && Not[BinomialMatchQ[u,x]]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: (e__ * x_).pow(m_) * (a__ + b__ * Atom::var(u_).tanh()).pow(p_),
        with: [e__, m_, a__, b__, u_, p_, x_],
        optional: [a__, b__, p_, m_],
        when: {
            freeq!([a__, b__, e__, m_, p_], x_)
                && rubi_binomial_q(&u_, x_)
                && !rubi_binomial_match_q(&u_, x_)
        },
        rhs: {
            rubi_rhs_int(
                &((&e__ * x_).pow(&m_)
                    * (&a__ + &b__ * rubi_expand_to_sum(&u_, x_).tanh()).pow(&p_)),
                x_,
            )
        },
    ));
}

fn push_rules_rule_5940(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, e__, m_, p_, u_, x_);
    rules.push(rubi_rule!(
        order: 5940,
        source: "Int[(e_*x_)^m_.*(a_.+b_.*Coth[u_])^p_.,x_Symbol] :=
          Int[(e*x)^m*(a+b*Coth[ExpandToSum[u,x]])^p,x] /;
        FreeQ[{a,b,e,m,p},x] && BinomialQ[u,x] && Not[BinomialMatchQ[u,x]]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: (e__ * x_).pow(m_) * (a__ + b__ * Atom::var(u_).coth()).pow(p_),
        with: [e__, m_, a__, b__, u_, p_, x_],
        optional: [a__, b__, p_, m_],
        when: {
            freeq!([a__, b__, e__, m_, p_], x_)
                && rubi_binomial_q(&u_, x_)
                && !rubi_binomial_match_q(&u_, x_)
        },
        rhs: {
            rubi_rhs_int(
                &((&e__ * x_).pow(&m_)
                    * (&a__ + &b__ * rubi_expand_to_sum(&u_, x_).coth()).pow(&p_)),
                x_,
            )
        },
    ));
}

fn push_rules_rule_5941(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, m_, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 5941,
        source: "Int[x_^m_.*Sech[a_.+b_.*x_^n_.]^p_.*Tanh[a_.+b_.*x_^n_.]^q_.,x_Symbol] :=
          -x^(m-n+1)*Sech[a+b*x^n]^p/(b*n*p) +
          (m-n+1)/(b*n*p) \\[Star] Int[x^(m-n)*Sech[a+b*x^n]^p,x] /;
        FreeQ[{a,b,p},x] && RationalQ[m] && IntegerQ[n] && GeQ[m-n,0] && EqQ[q,1]",
        desc: "Integration by parts",
        refs: [],
        pattern: x_.pow(m_) * (a__ + b__ * x_.pow(n_)).sech().pow(p_) * (a__ + b__ * x_.pow(n_)).tanh().pow(q_),
        with: [m_, a__, b__, n_, p_, q_, x_],
        optional: [m_, a__, b__, n_, q_, p_],
        when: {
            freeq!([a__, b__, p_], x_)
                && rationalq!(m_)
                && integerq!(n_)
                && geq!(&m_ - &n_, 0)
                && eqq!(q_, 1)
        },
        rhs: {
            let angle = &a__ + &b__ * x_.pow(&n_);
            let recursive =
                rubi_rhs_int(&(x_.pow(&m_ - &n_) * angle.sech().pow(&p_)), x_);

            rubi_simp(&(Atom::num(-1) * x_.pow(&m_ - &n_ + 1) * angle.sech().pow(&p_) / (&b__ * &n_ * &p_)), x_)
                    + rubi_star((&m_ - &n_ + 1) / (&b__ * &n_ * &p_), recursive)
        },
    ));
}

fn push_rules_rule_5942(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, m_, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 5942,
        source: "Int[x_^m_.*Csch[a_.+b_.*x_^n_.]^p_.*Coth[a_.+b_.*x_^n_.]^q_.,x_Symbol] :=
          -x^(m-n+1)*Csch[a+b*x^n]^p/(b*n*p) +
          (m-n+1)/(b*n*p) \\[Star] Int[x^(m-n)*Csch[a+b*x^n]^p,x] /;
        FreeQ[{a,b,p},x] && RationalQ[m] && IntegerQ[n] && GeQ[m-n,0] && EqQ[q,1]",
        desc: "Integration by parts",
        refs: [],
        pattern: x_.pow(m_) * (a__ + b__ * x_.pow(n_)).csch().pow(p_) * (a__ + b__ * x_.pow(n_)).coth().pow(q_),
        with: [m_, a__, b__, n_, p_, q_, x_],
        optional: [m_, a__, b__, n_, q_, p_],
        when: {
            freeq!([a__, b__, p_], x_)
                && rationalq!(m_)
                && integerq!(n_)
                && geq!(&m_ - &n_, 0)
                && eqq!(q_, 1)
        },
        rhs: {
            let angle = &a__ + &b__ * x_.pow(&n_);
            let recursive =
                rubi_rhs_int(&(x_.pow(&m_ - &n_) * angle.csch().pow(&p_)), x_);

            rubi_simp(&(Atom::num(-1) * x_.pow(&m_ - &n_ + 1) * angle.csch().pow(&p_) / (&b__ * &n_ * &p_)), x_)
                    + rubi_star((&m_ - &n_ + 1) / (&b__ * &n_ * &p_), recursive)
        },
    ));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn downvalues_5923_through_5942_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .collect::<Vec<_>>();
        assert_eq!(orders, (5923..=5942).collect::<Vec<_>>());
    }
}

// Generated shared pattern builders.

#[inline(never)]
fn rubi_shared_pattern_0(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (a__ + b__ * (c__ + d__ * x_.pow(n_)).coth()).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (a__ + b__ * (c__ + d__ * x_.pow(n_)).tanh()).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_2(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    x_.pow(m_) * (a__ + b__ * (c__ + d__ * x_.pow(n_)).coth()).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_3(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    x_.pow(m_) * (a__ + b__ * (c__ + d__ * x_.pow(n_)).tanh()).pow(p_)
}
