use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_5951(rules);
    push_rules_rule_5952(rules);
    push_rules_rule_5953(rules);
    push_rules_rule_5954(rules);
    push_rules_rule_5955(rules);
    push_rules_rule_5956(rules);
    push_rules_rule_5957(rules);
    push_rules_rule_5958(rules);
    push_rules_rule_5959(rules);
    push_rules_rule_5960(rules);
    push_rules_rule_5961(rules);
    push_rules_rule_5962(rules);
    push_rules_rule_5963(rules);
    push_rules_rule_5964(rules);
    push_rules_rule_5965(rules);
    push_rules_rule_5966(rules);
    push_rules_rule_5967(rules);
    push_rules_rule_5968(rules);
}

fn push_rules_rule_5951(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5951,
        source: "Int[(a_.+b_.*Sech[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
          1/n \\[Star] Subst[Int[x^(1/n-1)*(a+b*Sech[c+d*x])^p,x],x,x^n] /;
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
                * (&a__ + &b__ * (&c__ + &d__ * &sub).sech()).pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);

            rubi_star(Atom::num(1) / &n_, rubi_subst(&transformed, substitution_symbol, x_.pow(&n_)))
        },
    ));
}

fn push_rules_rule_5952(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5952,
        source: "Int[(a_.+b_.*Csch[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
          1/n \\[Star] Subst[Int[x^(1/n-1)*(a+b*Csch[c+d*x])^p,x],x,x^n] /;
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
                * (&a__ + &b__ * (&c__ + &d__ * &sub).csch()).pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);

            rubi_star(Atom::num(1) / &n_, rubi_subst(&transformed, substitution_symbol, x_.pow(&n_)))
        },
    ));
}

fn push_rules_rule_5953(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5953,
        source: "Int[(a_.+b_.*Sech[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
          Unintegrable[(a+b*Sech[c+d*x^n])^p,x] /;
        FreeQ[{a,b,c,d,n,p},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, n_, p_, x_],
        optional: [a__, b__, c__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__, n_, p_], x_)
        },
        rhs: {
            rubi_unintegrable(
                (&a__ + &b__ * (&c__ + &d__ * x_.pow(&n_)).sech()).pow(&p_),
                x_,
            )
        },
    ));
}

fn push_rules_rule_5954(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5954,
        source: "Int[(a_.+b_.*Csch[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
          Unintegrable[(a+b*Csch[c+d*x^n])^p,x] /;
        FreeQ[{a,b,c,d,n,p},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, n_, p_, x_],
        optional: [a__, b__, c__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__, n_, p_], x_)
        },
        rhs: {
            rubi_unintegrable(
                (&a__ + &b__ * (&c__ + &d__ * x_.pow(&n_)).csch()).pow(&p_),
                x_,
            )
        },
    ));
}

fn push_rules_rule_5955(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, n_, p_, u_);
    rules.push(rubi_rule!(
        order: 5955,
        source: "Int[(a_.+b_.*Sech[c_.+d_.*u_^n_])^p_.,x_Symbol] :=
          1/Coefficient[u,x,1] \\[Star] Subst[Int[(a+b*Sech[c+d*x^n])^p,x],x,u] /;
        FreeQ[{a,b,c,d,n,p},x] && LinearQ[u,x] && NeQ[u,x]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (a__ + b__ * (c__ + d__ * Atom::var(u_).pow(n_)).sech()).pow(p_),
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
                (&a__ + &b__ * (&c__ + &d__ * sub.pow(&n_)).sech()).pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);

            rubi_star(Atom::num(1) / coefficient, rubi_subst(&transformed, substitution_symbol, &u_))
        },
    ));
}

fn push_rules_rule_5956(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, n_, p_, u_);
    rules.push(rubi_rule!(
        order: 5956,
        source: "Int[(a_.+b_.*Csch[c_.+d_.*u_^n_])^p_.,x_Symbol] :=
          1/Coefficient[u,x,1] \\[Star] Subst[Int[(a+b*Csch[c+d*x^n])^p,x],x,u] /;
        FreeQ[{a,b,c,d,n,p},x] && LinearQ[u,x] && NeQ[u,x]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (a__ + b__ * (c__ + d__ * Atom::var(u_).pow(n_)).csch()).pow(p_),
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
                (&a__ + &b__ * (&c__ + &d__ * sub.pow(&n_)).csch()).pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);

            rubi_star(Atom::num(1) / coefficient, rubi_subst(&transformed, substitution_symbol, &u_))
        },
    ));
}

fn push_rules_rule_5957(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, p_, u_);
    rules.push(rubi_rule!(
        order: 5957,
        source: "Int[(a_.+b_.*Sech[u_])^p_.,x_Symbol] :=
          Int[(a+b*Sech[ExpandToSum[u,x]])^p,x] /;
        FreeQ[{a,b,p},x] && BinomialQ[u,x] && Not[BinomialMatchQ[u,x]]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: (a__ + b__ * Atom::var(u_).sech()).pow(p_),
        with: [a__, b__, u_, p_, x_],
        optional: [a__, b__, p_],
        when: {
            freeq!([a__, b__, p_], x_)
                && rubi_binomial_q(&u_, x_)
                && !rubi_binomial_match_q(&u_, x_)
        },
        rhs: {
            rubi_rhs_int(
                &(&a__ + &b__ * rubi_expand_to_sum(&u_, x_).sech()).pow(&p_),
                x_,
            )
        },
    ));
}

fn push_rules_rule_5958(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, p_, u_);
    rules.push(rubi_rule!(
        order: 5958,
        source: "Int[(a_.+b_.*Csch[u_])^p_.,x_Symbol] :=
          Int[(a+b*Csch[ExpandToSum[u,x]])^p,x] /;
        FreeQ[{a,b,p},x] && BinomialQ[u,x] && Not[BinomialMatchQ[u,x]]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: (a__ + b__ * Atom::var(u_).csch()).pow(p_),
        with: [a__, b__, u_, p_, x_],
        optional: [a__, b__, p_],
        when: {
            freeq!([a__, b__, p_], x_)
                && rubi_binomial_q(&u_, x_)
                && !rubi_binomial_match_q(&u_, x_)
        },
        rhs: {
            rubi_rhs_int(
                &(&a__ + &b__ * rubi_expand_to_sum(&u_, x_).csch()).pow(&p_),
                x_,
            )
        },
    ));
}

fn push_rules_rule_5959(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5959,
        source: "Int[x_^m_.*(a_.+b_.*Sech[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
          1/n \\[Star] Subst[Int[x^(Simplify[(m+1)/n]-1)*(a+b*Sech[c+d*x])^p,x],x,x^n] /;
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
                sub.pow(&s - 1) * (&a__ + &b__ * (&c__ + &d__ * &sub).sech()).pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);

            rubi_star(Atom::num(1) / &n_, rubi_subst(&transformed, substitution_symbol, x_.pow(&n_)))
        },
    ));
}

fn push_rules_rule_5960(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5960,
        source: "Int[x_^m_.*(a_.+b_.*Csch[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
          1/n \\[Star] Subst[Int[x^(Simplify[(m+1)/n]-1)*(a+b*Csch[c+d*x])^p,x],x,x^n] /;
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
                sub.pow(&s - 1) * (&a__ + &b__ * (&c__ + &d__ * &sub).csch()).pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);

            rubi_star(Atom::num(1) / &n_, rubi_subst(&transformed, substitution_symbol, x_.pow(&n_)))
        },
    ));
}

fn push_rules_rule_5961(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5961,
        source: "Int[x_^m_.*(a_.+b_.*Sech[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
          Unintegrable[x^m*(a+b*Sech[c+d*x^n])^p,x] /;
        FreeQ[{a,b,c,d,m,n,p},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [m_, a__, b__, c__, d__, n_, p_, x_],
        optional: [m_, a__, b__, c__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__, m_, n_, p_], x_)
        },
        rhs: {
            rubi_unintegrable(
                x_.pow(&m_)
                    * (&a__ + &b__ * (&c__ + &d__ * x_.pow(&n_)).sech()).pow(&p_),
                x_,
            )
        },
    ));
}

fn push_rules_rule_5962(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5962,
        source: "Int[x_^m_.*(a_.+b_.*Csch[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
          Unintegrable[x^m*(a+b*Csch[c+d*x^n])^p,x] /;
        FreeQ[{a,b,c,d,m,n,p},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [m_, a__, b__, c__, d__, n_, p_, x_],
        optional: [m_, a__, b__, c__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__, m_, n_, p_], x_)
        },
        rhs: {
            rubi_unintegrable(
                x_.pow(&m_)
                    * (&a__ + &b__ * (&c__ + &d__ * x_.pow(&n_)).csch()).pow(&p_),
                x_,
            )
        },
    ));
}

fn push_rules_rule_5963(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5963,
        source: "Int[(e_*x_)^m_.*(a_.+b_.*Sech[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
          e^IntPart[m]*(e*x)^FracPart[m]/x^FracPart[m] \\[Star] Int[x^m*(a+b*Sech[c+d*x^n])^p,x] /;
        FreeQ[{a,b,c,d,e,m,n,p},x]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: (e__ * x_).pow(m_) * (a__ + b__ * (c__ + d__ * x_.pow(n_)).sech()).pow(p_),
        with: [e__, m_, a__, b__, c__, d__, n_, p_, x_],
        optional: [a__, b__, c__, d__, p_, m_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_, p_], x_)
        },
        rhs: {
            let frac_m = rubi_frac_part(&m_);
            let recursive_integrand =
                x_.pow(&m_) * (&a__ + &b__ * (&c__ + &d__ * x_.pow(&n_)).sech()).pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(e__.pow(rubi_int_part(&m_)) * (&e__ * x_).pow(&frac_m)
                    / x_.pow(frac_m), recursive)
        },
    ));
}

fn push_rules_rule_5964(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5964,
        source: "Int[(e_*x_)^m_.*(a_.+b_.*Csch[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
          e^IntPart[m]*(e*x)^FracPart[m]/x^FracPart[m] \\[Star] Int[x^m*(a+b*Csch[c+d*x^n])^p,x] /;
        FreeQ[{a,b,c,d,e,m,n,p},x]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: (e__ * x_).pow(m_) * (a__ + b__ * (c__ + d__ * x_.pow(n_)).csch()).pow(p_),
        with: [e__, m_, a__, b__, c__, d__, n_, p_, x_],
        optional: [a__, b__, c__, d__, p_, m_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_, p_], x_)
        },
        rhs: {
            let frac_m = rubi_frac_part(&m_);
            let recursive_integrand =
                x_.pow(&m_) * (&a__ + &b__ * (&c__ + &d__ * x_.pow(&n_)).csch()).pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(e__.pow(rubi_int_part(&m_)) * (&e__ * x_).pow(&frac_m)
                    / x_.pow(frac_m), recursive)
        },
    ));
}

fn push_rules_rule_5965(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, e__, m_, p_, u_, x_);
    rules.push(rubi_rule!(
        order: 5965,
        source: "Int[(e_*x_)^m_.*(a_.+b_.*Sech[u_])^p_.,x_Symbol] :=
          Int[(e*x)^m*(a+b*Sech[ExpandToSum[u,x]])^p,x] /;
        FreeQ[{a,b,e,m,p},x] && BinomialQ[u,x] && Not[BinomialMatchQ[u,x]]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: (e__ * x_).pow(m_) * (a__ + b__ * Atom::var(u_).sech()).pow(p_),
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
                    * (&a__ + &b__ * rubi_expand_to_sum(&u_, x_).sech()).pow(&p_)),
                x_,
            )
        },
    ));
}

fn push_rules_rule_5966(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, e__, m_, p_, u_, x_);
    rules.push(rubi_rule!(
        order: 5966,
        source: "Int[(e_*x_)^m_.*(a_.+b_.*Csch[u_])^p_.,x_Symbol] :=
          Int[(e*x)^m*(a+b*Csch[ExpandToSum[u,x]])^p,x] /;
        FreeQ[{a,b,e,m,p},x] && BinomialQ[u,x] && Not[BinomialMatchQ[u,x]]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: (e__ * x_).pow(m_) * (a__ + b__ * Atom::var(u_).csch()).pow(p_),
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
                    * (&a__ + &b__ * rubi_expand_to_sum(&u_, x_).csch()).pow(&p_)),
                x_,
            )
        },
    ));
}

fn push_rules_rule_5967(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5967,
        source: "Int[x_^m_.*Sech[a_.+b_.*x_^n_.]^p_*Sinh[a_.+b_.*x_^n_.],x_Symbol] :=
          -x^(m-n+1)*Sech[a+b*x^n]^(p-1)/(b*n*(p-1)) +
          (m-n+1)/(b*n*(p-1)) \\[Star] Int[x^(m-n)*Sech[a+b*x^n]^(p-1),x] /;
        FreeQ[{a,b,p},x] && IntegerQ[n] && GeQ[m-n,0] && NeQ[p,1]",
        desc: "Integration by parts",
        refs: [],
        pattern: x_.pow(m_) * (a__ + b__ * x_.pow(n_)).sech().pow(p_) * (a__ + b__ * x_.pow(n_)).sinh(),
        with: [m_, a__, b__, n_, p_, x_],
        optional: [m_, a__, b__, n_],
        when: {
            freeq!([a__, b__, p_], x_)
                && integerq!(n_)
                && geq!(&m_ - &n_, 0)
                && neq!(p_, 1)
        },
        rhs: {
            let angle = &a__ + &b__ * x_.pow(&n_);
            let recursive =
                rubi_rhs_int(&(x_.pow(&m_ - &n_) * angle.sech().pow(&p_ - 1)), x_);

            rubi_simp(&(Atom::num(-1) * x_.pow(&m_ - &n_ + 1) * angle.sech().pow(&p_ - 1)
                    / (&b__ * &n_ * (&p_ - 1))), x_)
                    + rubi_star((&m_ - &n_ + 1) / (&b__ * &n_ * (&p_ - 1)), recursive)
        },
    ));
}

fn push_rules_rule_5968(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5968,
        source: "Int[x_^m_.*Csch[a_.+b_.*x_^n_.]^p_*Cosh[a_.+b_.*x_^n_.],x_Symbol] :=
          -x^(m-n+1)*Csch[a+b*x^n]^(p-1)/(b*n*(p-1)) +
          (m-n+1)/(b*n*(p-1)) \\[Star] Int[x^(m-n)*Csch[a+b*x^n]^(p-1),x] /;
        FreeQ[{a,b,p},x] && IntegerQ[n] && GeQ[m-n,0] && NeQ[p,1]",
        desc: "Integration by parts",
        refs: [],
        pattern: x_.pow(m_) * (a__ + b__ * x_.pow(n_)).csch().pow(p_) * (a__ + b__ * x_.pow(n_)).cosh(),
        with: [m_, a__, b__, n_, p_, x_],
        optional: [m_, a__, b__, n_],
        when: {
            freeq!([a__, b__, p_], x_)
                && integerq!(n_)
                && geq!(&m_ - &n_, 0)
                && neq!(p_, 1)
        },
        rhs: {
            let angle = &a__ + &b__ * x_.pow(&n_);
            let recursive =
                rubi_rhs_int(&(x_.pow(&m_ - &n_) * angle.csch().pow(&p_ - 1)), x_);

            rubi_simp(&(Atom::num(-1) * x_.pow(&m_ - &n_ + 1) * angle.csch().pow(&p_ - 1)
                    / (&b__ * &n_ * (&p_ - 1))), x_)
                    + rubi_star((&m_ - &n_ + 1) / (&b__ * &n_ * (&p_ - 1)), recursive)
        },
    ));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn downvalues_5951_through_5968_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .collect::<Vec<_>>();
        assert_eq!(orders, (5951..=5968).collect::<Vec<_>>());
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
    (a__ + b__ * (c__ + d__ * x_.pow(n_)).csch()).pow(p_)
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
    (a__ + b__ * (c__ + d__ * x_.pow(n_)).sech()).pow(p_)
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
    x_.pow(m_) * (a__ + b__ * (c__ + d__ * x_.pow(n_)).csch()).pow(p_)
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
    x_.pow(m_) * (a__ + b__ * (c__ + d__ * x_.pow(n_)).sech()).pow(p_)
}
