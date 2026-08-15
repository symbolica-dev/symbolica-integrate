use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_5821(rules);
    push_rules_rule_5822(rules);
    push_rules_rule_5823(rules);
    push_rules_rule_5824(rules);
    push_rules_rule_5825(rules);
    push_rules_rule_5826(rules);
    push_rules_rule_5827(rules);
    push_rules_rule_5828(rules);
    push_rules_rule_5829(rules);
    push_rules_rule_5830(rules);
    push_rules_rule_5831(rules);
    push_rules_rule_5832(rules);
    push_rules_rule_5833(rules);
    push_rules_rule_5834(rules);
    push_rules_rule_5835(rules);
    push_rules_rule_5836(rules);
    push_rules_rule_5837(rules);
    push_rules_rule_5838(rules);
    push_rules_rule_5839(rules);
    push_rules_rule_5840(rules);
    push_rules_rule_5841(rules);
    push_rules_rule_5842(rules);
    push_rules_rule_5843(rules);
    push_rules_rule_5844(rules);
    push_rules_rule_5845(rules);
    push_rules_rule_5846(rules);
    push_rules_rule_5847(rules);
    push_rules_rule_5848(rules);
    push_rules_rule_5849(rules);
    push_rules_rule_5850(rules);
    push_rules_rule_5851(rules);
    push_rules_rule_5852(rules);
    push_rules_rule_5853(rules);
    push_rules_rule_5854(rules);
    push_rules_rule_5855(rules);
    push_rules_rule_5856(rules);
    push_rules_rule_5857(rules);
    push_rules_rule_5858(rules);
    push_rules_rule_5859(rules);
    push_rules_rule_5860(rules);
    push_rules_rule_5861(rules);
    push_rules_rule_5862(rules);
    push_rules_rule_5863(rules);
    push_rules_rule_5864(rules);
    push_rules_rule_5865(rules);
    push_rules_rule_5866(rules);
    push_rules_rule_5867(rules);
    push_rules_rule_5868(rules);
    push_rules_rule_5869(rules);
    push_rules_rule_5870(rules);
    push_rules_rule_5871(rules);
    push_rules_rule_5872(rules);
    push_rules_rule_5873(rules);
    push_rules_rule_5874(rules);
    push_rules_rule_5875(rules);
    push_rules_rule_5876(rules);
    push_rules_rule_5877(rules);
    push_rules_rule_5878(rules);
    push_rules_rule_5879(rules);
    push_rules_rule_5880(rules);
    push_rules_rule_5881(rules);
    push_rules_rule_5882(rules);
    push_rules_rule_5883(rules);
    push_rules_rule_5884(rules);
    push_rules_rule_5885(rules);
    push_rules_rule_5886(rules);
    push_rules_rule_5887(rules);
    push_rules_rule_5888(rules);
    push_rules_rule_5889(rules);
    push_rules_rule_5890(rules);
    push_rules_rule_5891(rules);
    push_rules_rule_5892(rules);
    push_rules_rule_5893(rules);
    push_rules_rule_5894(rules);
    push_rules_rule_5895(rules);
    push_rules_rule_5896(rules);
}

fn push_rules_rule_5821(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; c__, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 5821,
        source: "Int[Sinh[c_.+d_.*x_^n_],x_Symbol] :=
          1/2 \\[Star] Int[E^(c+d*x^n),x] - 1/2 \\[Star] Int[E^(-c-d*x^n),x] /;
        FreeQ[{c,d},x] && IGtQ[n,1]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [c__, d__, n_, x_],
        optional: [c__, d__],
        when: { freeq!([c__, d__], x_) && igtq!(n_, 1) },
        rhs: {
            let angle = &c__ + &d__ * x_.pow(&n_);
            rubi_star(Atom::num(1) / 2, rubi_rhs_int(&angle.exp(), x_)) - rubi_star(Atom::num(1) / 2, rubi_rhs_int(&(-angle).exp(), x_))
        },
    ));
}

fn push_rules_rule_5822(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; c__, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 5822,
        source: "Int[Cosh[c_.+d_.*x_^n_],x_Symbol] :=
          1/2 \\[Star] Int[E^(c+d*x^n),x] + 1/2 \\[Star] Int[E^(-c-d*x^n),x] /;
        FreeQ[{c,d},x] && IGtQ[n,1]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [c__, d__, n_, x_],
        optional: [c__, d__],
        when: { freeq!([c__, d__], x_) && igtq!(n_, 1) },
        rhs: {
            let angle = &c__ + &d__ * x_.pow(&n_);
            rubi_star(Atom::num(1) / 2, rubi_rhs_int(&angle.exp(), x_)) + rubi_star(Atom::num(1) / 2, rubi_rhs_int(&(-angle).exp(), x_))
        },
    ));
}

fn push_rules_rule_5823(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5823,
        source: "Int[(a_.+b_.*Sinh[c_.+d_.*x_^n_])^p_,x_Symbol] :=
          Int[ExpandTrigReduce[(a+b*Sinh[c+d*x^n])^p,x],x] /;
        FreeQ[{a,b,c,d},x] && IGtQ[n,1] && IGtQ[p,1]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, n_, p_, x_],
        optional: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && igtq!(n_, 1)
                && igtq!(p_, 1)
        },
        rhs: {
            let integrand = (&a__ + &b__ * (&c__ + &d__ * x_.pow(&n_)).sinh()).pow(&p_);
            rubi_rhs_int(
                &rubi_expand_trig_reduce(&Atom::num(1), &integrand, x_),
                x_,
            )
        },
    ));
}

fn push_rules_rule_5824(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5824,
        source: "Int[(a_.+b_.*Cosh[c_.+d_.*x_^n_])^p_,x_Symbol] :=
          Int[ExpandTrigReduce[(a+b*Cosh[c+d*x^n])^p,x],x] /;
        FreeQ[{a,b,c,d},x] && IGtQ[n,1] && IGtQ[p,1]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, n_, p_, x_],
        optional: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && igtq!(n_, 1)
                && igtq!(p_, 1)
        },
        rhs: {
            let integrand = (&a__ + &b__ * (&c__ + &d__ * x_.pow(&n_)).cosh()).pow(&p_);
            rubi_rhs_int(
                &rubi_expand_trig_reduce(&Atom::num(1), &integrand, x_),
                x_,
            )
        },
    ));
}

fn push_rules_rule_5825(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5825,
        source: "Int[(a_.+b_.*Sinh[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
          -Subst[Int[(a+b*Sinh[c+d*x^(-n)])^p/x^2,x],x,1/x] /;
        FreeQ[{a,b,c,d},x] && ILtQ[n,0] && IntegerQ[p]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, n_, p_, x_],
        optional: [a__, b__, c__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && iltq!(n_, 0)
                && integerq!(p_)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub = Atom::var(substitution_symbol);
            let transformed_integrand =
                (&a__ + &b__ * (&c__ + &d__ * sub.pow(-&n_)).sinh()).pow(&p_) / sub.pow(2);
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);

            -rubi_subst(&transformed, substitution_symbol, Atom::num(1) / x_)
        },
    ));
}

fn push_rules_rule_5826(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5826,
        source: "Int[(a_.+b_.*Cosh[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
          -Subst[Int[(a+b*Cosh[c+d*x^(-n)])^p/x^2,x],x,1/x] /;
        FreeQ[{a,b,c,d},x] && ILtQ[n,0] && IntegerQ[p]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, n_, p_, x_],
        optional: [a__, b__, c__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && iltq!(n_, 0)
                && integerq!(p_)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub = Atom::var(substitution_symbol);
            let transformed_integrand =
                (&a__ + &b__ * (&c__ + &d__ * sub.pow(-&n_)).cosh()).pow(&p_) / sub.pow(2);
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);

            -rubi_subst(&transformed, substitution_symbol, Atom::num(1) / x_)
        },
    ));
}

fn push_rules_rule_5827(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5827,
        source: "Int[(a_.+b_.*Sinh[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
          Module[{k=Denominator[n]},
          k \\[Star] Subst[Int[x^(k-1)*(a+b*Sinh[c+d*x^(k*n)])^p,x],x,x^(1/k)]] /;
        FreeQ[{a,b,c,d},x] && FractionQ[n] && IntegerQ[p]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, n_, p_, x_],
        optional: [a__, b__, c__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && fractionq!(n_)
                && integerq!(p_)
        },
        rhs: {
            let k_i = rubi_denominator(&n_).rubi_rhs();
            let k = Atom::num(k_i);
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub = Atom::var(substitution_symbol);
            let transformed_integrand = sub.pow(&k - Atom::num(1))
                * (&a__ + &b__ * (&c__ + &d__ * sub.pow((&k * &n_).expand())).sinh()).pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);

            rubi_star(k, rubi_subst(
                    &transformed,
                    substitution_symbol,
                    x_.pow(Atom::num(1) / k_i),
                ))
        },
    ));
}

fn push_rules_rule_5828(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5828,
        source: "Int[(a_.+b_.*Cosh[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
          Module[{k=Denominator[n]},
          k \\[Star] Subst[Int[x^(k-1)*(a+b*Cosh[c+d*x^(k*n)])^p,x],x,x^(1/k)]] /;
        FreeQ[{a,b,c,d},x] && FractionQ[n] && IntegerQ[p]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, n_, p_, x_],
        optional: [a__, b__, c__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && fractionq!(n_)
                && integerq!(p_)
        },
        rhs: {
            let k_i = rubi_denominator(&n_).rubi_rhs();
            let k = Atom::num(k_i);
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub = Atom::var(substitution_symbol);
            let transformed_integrand = sub.pow(&k - Atom::num(1))
                * (&a__ + &b__ * (&c__ + &d__ * sub.pow((&k * &n_).expand())).cosh()).pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);

            rubi_star(k, rubi_subst(
                    &transformed,
                    substitution_symbol,
                    x_.pow(Atom::num(1) / k_i),
                ))
        },
    ));
}

fn push_rules_rule_5829(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; c__, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 5829,
        source: "Int[Sinh[c_.+d_.*x_^n_],x_Symbol] :=
          1/2 \\[Star] Int[E^(c+d*x^n),x] - 1/2 \\[Star] Int[E^(-c-d*x^n),x] /;
        FreeQ[{c,d,n},x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [c__, d__, n_, x_],
        optional: [c__, d__],
        when: { freeq!([c__, d__, n_], x_) },
        rhs: {
            let angle = &c__ + &d__ * x_.pow(&n_);
            rubi_star(Atom::num(1) / 2, rubi_rhs_int(&angle.exp(), x_)) - rubi_star(Atom::num(1) / 2, rubi_rhs_int(&(-angle).exp(), x_))
        },
    ));
}

fn push_rules_rule_5830(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; c__, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 5830,
        source: "Int[Cosh[c_.+d_.*x_^n_],x_Symbol] :=
          1/2 \\[Star] Int[E^(c+d*x^n),x] + 1/2 \\[Star] Int[E^(-c-d*x^n),x] /;
        FreeQ[{c,d,n},x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [c__, d__, n_, x_],
        optional: [c__, d__],
        when: { freeq!([c__, d__, n_], x_) },
        rhs: {
            let angle = &c__ + &d__ * x_.pow(&n_);
            rubi_star(Atom::num(1) / 2, rubi_rhs_int(&angle.exp(), x_)) + rubi_star(Atom::num(1) / 2, rubi_rhs_int(&(-angle).exp(), x_))
        },
    ));
}

fn push_rules_rule_5831(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5831,
        source: "Int[(a_.+b_.*Sinh[c_.+d_.*x_^n_])^p_,x_Symbol] :=
          Int[ExpandTrigReduce[(a+b*Sinh[c+d*x^n])^p,x],x] /;
        FreeQ[{a,b,c,d,n},x] && IGtQ[p,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, n_, p_, x_],
        optional: [a__, b__, c__, d__],
        when: { freeq!([a__, b__, c__, d__, n_], x_) && igtq!(p_, 0) },
        rhs: {
            let integrand = (&a__ + &b__ * (&c__ + &d__ * x_.pow(&n_)).sinh()).pow(&p_);
            rubi_rhs_int(
                &rubi_expand_trig_reduce(&Atom::num(1), &integrand, x_),
                x_,
            )
        },
    ));
}

fn push_rules_rule_5832(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5832,
        source: "Int[(a_.+b_.*Cosh[c_.+d_.*x_^n_])^p_,x_Symbol] :=
          Int[ExpandTrigReduce[(a+b*Cosh[c+d*x^n])^p,x],x] /;
        FreeQ[{a,b,c,d,n},x] && IGtQ[p,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, n_, p_, x_],
        optional: [a__, b__, c__, d__],
        when: { freeq!([a__, b__, c__, d__, n_], x_) && igtq!(p_, 0) },
        rhs: {
            let integrand = (&a__ + &b__ * (&c__ + &d__ * x_.pow(&n_)).cosh()).pow(&p_);
            rubi_rhs_int(
                &rubi_expand_trig_reduce(&Atom::num(1), &integrand, x_),
                x_,
            )
        },
    ));
}

fn push_rules_rule_5833(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, u_);
    rules.push(rubi_rule!(
        order: 5833,
        source: "Int[(a_.+b_.*Sinh[c_.+d_.*u_^n_])^p_.,x_Symbol] :=
          1/Coefficient[u,x,1] \\[Star] Subst[Int[(a+b*Sinh[c+d*x^n])^p,x],x,u] /;
        FreeQ[{a,b,c,d,n},x] && IntegerQ[p] && LinearQ[u,x] && NeQ[u,x]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, u_, n_, p_, x_],
        optional: [a__, b__, c__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__, n_], x_)
                && integerq!(p_)
                && rubi_linear_q(&u_, x_)
                && neq!(u_, x_)
        },
        rhs: {
            let coefficient = rubi_coefficient(&u_, x_, 1).rubi_rhs();
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub = Atom::var(substitution_symbol);
            let transformed_integrand =
                (&a__ + &b__ * (&c__ + &d__ * sub.pow(&n_)).sinh()).pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);

            rubi_star(Atom::num(1) / coefficient, rubi_subst(&transformed, substitution_symbol, &u_))
        },
    ));
}

fn push_rules_rule_5834(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, u_);
    rules.push(rubi_rule!(
        order: 5834,
        source: "Int[(a_.+b_.*Cosh[c_.+d_.*u_^n_])^p_.,x_Symbol] :=
          1/Coefficient[u,x,1] \\[Star] Subst[Int[(a+b*Cosh[c+d*x^n])^p,x],x,u] /;
        FreeQ[{a,b,c,d,n},x] && IntegerQ[p] && LinearQ[u,x] && NeQ[u,x]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, u_, n_, p_, x_],
        optional: [a__, b__, c__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__, n_], x_)
                && integerq!(p_)
                && rubi_linear_q(&u_, x_)
                && neq!(u_, x_)
        },
        rhs: {
            let coefficient = rubi_coefficient(&u_, x_, 1).rubi_rhs();
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub = Atom::var(substitution_symbol);
            let transformed_integrand =
                (&a__ + &b__ * (&c__ + &d__ * sub.pow(&n_)).cosh()).pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);

            rubi_star(Atom::num(1) / coefficient, rubi_subst(&transformed, substitution_symbol, &u_))
        },
    ));
}

fn push_rules_rule_5835(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, u_);
    rules.push(rubi_rule!(
        order: 5835,
        source: "Int[(a_.+b_.*Sinh[c_.+d_.*u_^n_])^p_,x_Symbol] :=
          Unintegrable[(a+b*Sinh[c+d*u^n])^p,x] /;
        FreeQ[{a,b,c,d,n,p},x] && LinearQ[u,x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, u_, n_, p_, x_],
        optional: [a__, b__, c__, d__],
        when: { freeq!([a__, b__, c__, d__, n_, p_], x_) && rubi_linear_q(&u_, x_) },
        rhs: {
            rubi_unintegrable(
                (&a__ + &b__ * (&c__ + &d__ * u_.pow(&n_)).sinh()).pow(&p_),
                x_,
            )
        },
    ));
}

fn push_rules_rule_5836(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, u_);
    rules.push(rubi_rule!(
        order: 5836,
        source: "Int[(a_.+b_.*Cosh[c_.+d_.*u_^n_])^p_,x_Symbol] :=
          Unintegrable[(a+b*Cosh[c+d*u^n])^p,x] /;
        FreeQ[{a,b,c,d,n,p},x] && LinearQ[u,x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, u_, n_, p_, x_],
        optional: [a__, b__, c__, d__],
        when: { freeq!([a__, b__, c__, d__, n_, p_], x_) && rubi_linear_q(&u_, x_) },
        rhs: {
            rubi_unintegrable(
                (&a__ + &b__ * (&c__ + &d__ * u_.pow(&n_)).cosh()).pow(&p_),
                x_,
            )
        },
    ));
}

fn push_rules_rule_5837(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, p_, u_);
    rules.push(rubi_rule!(
        order: 5837,
        source: "Int[(a_.+b_.*Sinh[u_])^p_.,x_Symbol] :=
          Int[(a+b*Sinh[ExpandToSum[u,x]])^p,x] /;
        FreeQ[{a,b,p},x] && BinomialQ[u,x] && Not[BinomialMatchQ[u,x]]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: (a__ + b__ * Atom::var(u_).sinh()).pow(p_),
        with: [a__, b__, u_, p_, x_],
        optional: [a__, b__, p_],
        when: {
            freeq!([a__, b__, p_], x_) && rubi_binomial_q(&u_, x_) && !rubi_binomial_match_q(&u_, x_)
        },
        rhs: {
            let expanded = rubi_expand_to_sum(&u_, x_);
            rubi_rhs_int(
                &(&a__ + &b__ * expanded.sinh()).pow(&p_),
                x_,
            )
        },
    ));
}

fn push_rules_rule_5838(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, p_, u_);
    rules.push(rubi_rule!(
        order: 5838,
        source: "Int[(a_.+b_.*Cosh[u_])^p_.,x_Symbol] :=
          Int[(a+b*Cosh[ExpandToSum[u,x]])^p,x] /;
        FreeQ[{a,b,p},x] && BinomialQ[u,x] && Not[BinomialMatchQ[u,x]]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: (a__ + b__ * Atom::var(u_).cosh()).pow(p_),
        with: [a__, b__, u_, p_, x_],
        optional: [a__, b__, p_],
        when: {
            freeq!([a__, b__, p_], x_) && rubi_binomial_q(&u_, x_) && !rubi_binomial_match_q(&u_, x_)
        },
        rhs: {
            let expanded = rubi_expand_to_sum(&u_, x_);
            rubi_rhs_int(
                &(&a__ + &b__ * expanded.cosh()).pow(&p_),
                x_,
            )
        },
    ));
}

fn push_rules_rule_5839(rules: &mut Vec<RubiRule>) {
    rubi_symb!(d__, n_, x_);
    rules.push(rubi_rule!(
        order: 5839,
        source: "Int[Sinh[d_.*x_^n_]/x_,x_Symbol] :=
          SinhIntegral[d*x^n]/n /;
        FreeQ[{d,n},x]",
        desc: "Primitive rule",
        refs: [],
        pattern: (d__ * x_.pow(n_)).sinh() / x_,
        with: [d__, n_, x_],
        optional: [d__],
        when: { freeq!([d__, n_], x_) },
        rhs: { rubi_simp(&(rubi_sinh_integral(d__ * x_.pow(&n_)) / n_), x_) },
    ));
}

fn push_rules_rule_5840(rules: &mut Vec<RubiRule>) {
    rubi_symb!(d__, n_, x_);
    rules.push(rubi_rule!(
        order: 5840,
        source: "Int[Cosh[d_.*x_^n_]/x_,x_Symbol] :=
          CoshIntegral[d*x^n]/n /;
        FreeQ[{d,n},x]",
        desc: "Primitive rule",
        refs: [],
        pattern: (d__ * x_.pow(n_)).cosh() / x_,
        with: [d__, n_, x_],
        optional: [d__],
        when: { freeq!([d__, n_], x_) },
        rhs: { rubi_simp(&(rubi_cosh_integral(d__ * x_.pow(&n_)) / n_), x_) },
    ));
}

fn push_rules_rule_5841(rules: &mut Vec<RubiRule>) {
    rubi_symb!(c__, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 5841,
        source: "Int[Sinh[c_+d_.*x_^n_]/x_,x_Symbol] :=
          Sinh[c] \\[Star] Int[Cosh[d*x^n]/x,x] + Cosh[c] \\[Star] Int[Sinh[d*x^n]/x,x] /;
        FreeQ[{c,d,n},x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (c__ + d__ * x_.pow(n_)).sinh() / x_,
        with: [c__, d__, n_, x_],
        optional: [d__],
        when: { freeq!([c__, d__, n_], x_) },
        rhs: {
            let scaled = &d__ * x_.pow(&n_);
            rubi_star(c__.sinh(), rubi_rhs_int(&(&scaled.cosh() / x_), x_)) + rubi_star(c__.cosh(), rubi_rhs_int(&(scaled.sinh() / x_), x_))
        },
    ));
}

fn push_rules_rule_5842(rules: &mut Vec<RubiRule>) {
    rubi_symb!(c__, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 5842,
        source: "Int[Cosh[c_+d_.*x_^n_]/x_,x_Symbol] :=
          Cosh[c] \\[Star] Int[Cosh[d*x^n]/x,x] + Sinh[c] \\[Star] Int[Sinh[d*x^n]/x,x] /;
        FreeQ[{c,d,n},x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (c__ + d__ * x_.pow(n_)).cosh() / x_,
        with: [c__, d__, n_, x_],
        optional: [d__],
        when: { freeq!([c__, d__, n_], x_) },
        rhs: {
            let scaled = &d__ * x_.pow(&n_);
            rubi_star(c__.cosh(), rubi_rhs_int(&(&scaled.cosh() / x_), x_)) + rubi_star(c__.sinh(), rubi_rhs_int(&(scaled.sinh() / x_), x_))
        },
    ));
}

fn push_rules_rule_5843(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5843,
        source: "Int[x_^m_.*(a_.+b_.*Sinh[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
          1/n \\[Star] Subst[Int[x^(Simplify[(m+1)/n]-1)*(a+b*Sinh[c+d*x])^p,x],x,x^n] /;
        FreeQ[{a,b,c,d,m,n,p},x] && IntegerQ[Simplify[(m+1)/n]] && (EqQ[p,1] || EqQ[m,n-1] || IntegerQ[p] && GtQ[Simplify[(m+1)/n],0])",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_11(symbols),
        with: [m_, a__, b__, c__, d__, n_, p_, x_],
        optional: [m_, a__, b__, c__, d__, p_],
        when: {
            let quotient = rubi_simplify(&((&m_ + 1) / &n_));
            freeq!([a__, b__, c__, d__, m_, n_, p_], x_)
                && integerq!(quotient)
                && (eqq!(p_, 1) || eqq!(m_, &n_ - 1) || integerq!(p_) && gtq!(quotient, 0))
        },
        rhs: {
            let quotient = rubi_simplify(&((&m_ + 1) / &n_));
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub = Atom::var(substitution_symbol);
            let transformed_integrand =
                sub.pow(&quotient - 1) * (&a__ + &b__ * (&c__ + &d__ * &sub).sinh()).pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);

            rubi_star(Atom::num(1) / &n_, rubi_subst(&transformed, substitution_symbol, x_.pow(&n_)))
        },
    ));
}

fn push_rules_rule_5844(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5844,
        source: "Int[x_^m_.*(a_.+b_.*Cosh[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
          1/n \\[Star] Subst[Int[x^(Simplify[(m+1)/n]-1)*(a+b*Cosh[c+d*x])^p,x],x,x^n] /;
        FreeQ[{a,b,c,d,m,n,p},x] && IntegerQ[Simplify[(m+1)/n]] && (EqQ[p,1] || EqQ[m,n-1] || IntegerQ[p] && GtQ[Simplify[(m+1)/n],0])",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_10(symbols),
        with: [m_, a__, b__, c__, d__, n_, p_, x_],
        optional: [m_, a__, b__, c__, d__, p_],
        when: {
            let quotient = rubi_simplify(&((&m_ + 1) / &n_));
            freeq!([a__, b__, c__, d__, m_, n_, p_], x_)
                && integerq!(quotient)
                && (eqq!(p_, 1) || eqq!(m_, &n_ - 1) || integerq!(p_) && gtq!(quotient, 0))
        },
        rhs: {
            let quotient = rubi_simplify(&((&m_ + 1) / &n_));
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub = Atom::var(substitution_symbol);
            let transformed_integrand =
                sub.pow(&quotient - 1) * (&a__ + &b__ * (&c__ + &d__ * &sub).cosh()).pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);

            rubi_star(Atom::num(1) / &n_, rubi_subst(&transformed, substitution_symbol, x_.pow(&n_)))
        },
    ));
}

fn push_rules_rule_5845(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; e__, a__, b__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5845,
        source: "Int[(e_*x_)^m_*(a_.+b_.*Sinh[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
          e^IntPart[m]*(e*x)^FracPart[m]/x^FracPart[m] \\[Star] Int[x^m*(a+b*Sinh[c+d*x^n])^p,x] /;
        FreeQ[{a,b,c,d,e,m,n,p},x] && IntegerQ[Simplify[(m+1)/n]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [e__, m_, a__, b__, c__, d__, n_, p_, x_],
        optional: [a__, b__, c__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_, p_], x_)
                && integerq!(rubi_simplify(&((&m_ + 1) / &n_)))
        },
        rhs: {
            let frac_m = rubi_frac_part(&m_);
            let recursive = rubi_rhs_int(
                &(x_.pow(&m_) * (&a__ + &b__ * (&c__ + &d__ * x_.pow(&n_)).sinh()).pow(&p_)),
                x_,
            );
            rubi_star(e__.pow(rubi_int_part(&m_)) * (&e__ * x_).pow(&frac_m) / x_.pow(frac_m), recursive)
        },
    ));
}

fn push_rules_rule_5846(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; e__, a__, b__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5846,
        source: "Int[(e_*x_)^m_*(a_.+b_.*Cosh[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
          e^IntPart[m]*(e*x)^FracPart[m]/x^FracPart[m] \\[Star] Int[x^m*(a+b*Cosh[c+d*x^n])^p,x] /;
        FreeQ[{a,b,c,d,e,m,n,p},x] && IntegerQ[Simplify[(m+1)/n]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [e__, m_, a__, b__, c__, d__, n_, p_, x_],
        optional: [a__, b__, c__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_, p_], x_)
                && integerq!(rubi_simplify(&((&m_ + 1) / &n_)))
        },
        rhs: {
            let frac_m = rubi_frac_part(&m_);
            let recursive = rubi_rhs_int(
                &(x_.pow(&m_) * (&a__ + &b__ * (&c__ + &d__ * x_.pow(&n_)).cosh()).pow(&p_)),
                x_,
            );
            rubi_star(e__.pow(rubi_int_part(&m_)) * (&e__ * x_).pow(&frac_m) / x_.pow(frac_m), recursive)
        },
    ));
}

fn push_rules_rule_5847(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; c__, d__, e__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5847,
        source: "Int[(e_.*x_)^m_.*Sinh[c_.+d_.*x_^n_],x_Symbol] :=
          e^(n-1)*(e*x)^(m-n+1)*Cosh[c+d*x^n]/(d*n) -
          e^n*(m-n+1)/(d*n) \\[Star] Int[(e*x)^(m-n)*Cosh[c+d*x^n],x] /;
        FreeQ[{c,d,e},x] && IGtQ[n,0] && LtQ[0,n,m+1]",
        desc: "Integration by parts",
        refs: ["CRC 392, A&S 4.3.119", "CRC 396, A&S 4.3.123"],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [e__, m_, c__, d__, n_, x_],
        optional: [e__, m_, c__, d__],
        when: {
            freeq!([c__, d__, e__], x_) && igtq!(n_, 0) && ltq!(0, n_, &m_ + 1)
        },
        rhs: {
            let angle = &c__ + &d__ * x_.pow(&n_);
            rubi_simp(&(e__.pow(&n_ - 1) * (&e__ * x_).pow(&m_ - &n_ + 1) * &angle.cosh()
                    / (&d__ * &n_)), x_)
                    - rubi_star(e__.pow(&n_) * (&m_ - &n_ + 1) / (&d__ * &n_), rubi_rhs_int(&((&e__ * x_).pow(&m_ - &n_) * angle.cosh()), x_))
        },
    ));
}

fn push_rules_rule_5848(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; c__, d__, e__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5848,
        source: "Int[(e_.*x_)^m_.*Cosh[c_.+d_.*x_^n_],x_Symbol] :=
          e^(n-1)*(e*x)^(m-n+1)*Sinh[c+d*x^n]/(d*n) -
          e^n*(m-n+1)/(d*n) \\[Star] Int[(e*x)^(m-n)*Sinh[c+d*x^n],x] /;
        FreeQ[{c,d,e},x] && IGtQ[n,0] && LtQ[0,n,m+1]",
        desc: "Integration by parts",
        refs: ["CRC 392, A&S 4.3.119", "CRC 396, A&S 4.3.123"],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [e__, m_, c__, d__, n_, x_],
        optional: [e__, m_, c__, d__],
        when: {
            freeq!([c__, d__, e__], x_) && igtq!(n_, 0) && ltq!(0, n_, &m_ + 1)
        },
        rhs: {
            let angle = &c__ + &d__ * x_.pow(&n_);
            rubi_simp(&(e__.pow(&n_ - 1) * (&e__ * x_).pow(&m_ - &n_ + 1) * &angle.sinh()
                    / (&d__ * &n_)), x_)
                    - rubi_star(e__.pow(&n_) * (&m_ - &n_ + 1) / (&d__ * &n_), rubi_rhs_int(&((&e__ * x_).pow(&m_ - &n_) * angle.sinh()), x_))
        },
    ));
}

fn push_rules_rule_5849(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; c__, d__, e__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5849,
        source: "Int[(e_.*x_)^m_*Sinh[c_.+d_.*x_^n_],x_Symbol] :=
          (e*x)^(m+1)*Sinh[c+d*x^n]/(e*(m+1)) -
          d*n/(e^n*(m+1)) \\[Star] Int[(e*x)^(m+n)*Cosh[c+d*x^n],x] /;
        FreeQ[{c,d,e},x] && IGtQ[n,0] && LtQ[m,-1]",
        desc: "Integration by parts",
        refs: ["CRC 405, A&S 4.3.120", "CRC 406, A&S 4.3.124"],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [e__, m_, c__, d__, n_, x_],
        optional: [e__, c__, d__],
        when: { freeq!([c__, d__, e__], x_) && igtq!(n_, 0) && ltq!(m_, -1) },
        rhs: {
            let angle = &c__ + &d__ * x_.pow(&n_);
            rubi_simp(&((&e__ * x_).pow(&m_ + 1) * &angle.sinh() / (&e__ * (&m_ + 1))), x_)
                    - rubi_star(&d__ * &n_ / (e__.pow(&n_) * (&m_ + 1)), rubi_rhs_int(&((&e__ * x_).pow(&m_ + &n_) * angle.cosh()), x_))
        },
    ));
}

fn push_rules_rule_5850(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; c__, d__, e__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5850,
        source: "Int[(e_.*x_)^m_*Cosh[c_.+d_.*x_^n_],x_Symbol] :=
          (e*x)^(m+1)*Cosh[c+d*x^n]/(e*(m+1)) -
          d*n/(e^n*(m+1)) \\[Star] Int[(e*x)^(m+n)*Sinh[c+d*x^n],x] /;
        FreeQ[{c,d,e},x] && IGtQ[n,0] && LtQ[m,-1]",
        desc: "Integration by parts",
        refs: ["CRC 405, A&S 4.3.120", "CRC 406, A&S 4.3.124"],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [e__, m_, c__, d__, n_, x_],
        optional: [e__, c__, d__],
        when: { freeq!([c__, d__, e__], x_) && igtq!(n_, 0) && ltq!(m_, -1) },
        rhs: {
            let angle = &c__ + &d__ * x_.pow(&n_);
            rubi_simp(&((&e__ * x_).pow(&m_ + 1) * &angle.cosh() / (&e__ * (&m_ + 1))), x_)
                    - rubi_star(&d__ * &n_ / (e__.pow(&n_) * (&m_ + 1)), rubi_rhs_int(&((&e__ * x_).pow(&m_ + &n_) * angle.sinh()), x_))
        },
    ));
}

fn push_rules_rule_5851(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; c__, d__, e__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5851,
        source: "Int[(e_.*x_)^m_.*Sinh[c_.+d_.*x_^n_],x_Symbol] :=
          1/2 \\[Star] Int[(e*x)^m*E^(c+d*x^n),x] - 1/2 \\[Star] Int[(e*x)^m*E^(-c-d*x^n),x] /;
        FreeQ[{c,d,e,m},x] && IGtQ[n,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [e__, m_, c__, d__, n_, x_],
        optional: [e__, m_, c__, d__],
        when: { freeq!([c__, d__, e__, m_], x_) && igtq!(n_, 0) },
        rhs: {
            let angle = &c__ + &d__ * x_.pow(&n_);
            let power = (&e__ * x_).pow(&m_);
            rubi_star(Atom::num(1) / 2, rubi_rhs_int(&(&power * &angle.exp()), x_)) - rubi_star(Atom::num(1) / 2, rubi_rhs_int(&(power * (-angle).exp()), x_))
        },
    ));
}

fn push_rules_rule_5852(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; c__, d__, e__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5852,
        source: "Int[(e_.*x_)^m_.*Cosh[c_.+d_.*x_^n_],x_Symbol] :=
          1/2 \\[Star] Int[(e*x)^m*E^(c+d*x^n),x] + 1/2 \\[Star] Int[(e*x)^m*E^(-c-d*x^n),x] /;
        FreeQ[{c,d,e,m},x] && IGtQ[n,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [e__, m_, c__, d__, n_, x_],
        optional: [e__, m_, c__, d__],
        when: { freeq!([c__, d__, e__, m_], x_) && igtq!(n_, 0) },
        rhs: {
            let angle = &c__ + &d__ * x_.pow(&n_);
            let power = (&e__ * x_).pow(&m_);
            rubi_star(Atom::num(1) / 2, rubi_rhs_int(&(&power * &angle.exp()), x_)) + rubi_star(Atom::num(1) / 2, rubi_rhs_int(&(power * (-angle).exp()), x_))
        },
    ));
}

fn push_rules_rule_5853(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5853,
        source: "Int[x_^m_.*Sinh[a_.+b_.*x_^n_]^p_,x_Symbol] :=
          -Sinh[a+b*x^n]^p/((n-1)*x^(n-1)) +
          b*n*p/(n-1) \\[Star] Int[Sinh[a+b*x^n]^(p-1)*Cosh[a+b*x^n],x] /;
        FreeQ[{a,b},x] && IntegersQ[n,p] && EqQ[m+n,0] && GtQ[p,1] && NeQ[n,1]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_14(symbols),
        with: [m_, a__, b__, n_, p_, x_],
        optional: [m_, a__, b__],
        when: {
            freeq!([a__, b__], x_)
                && integersq!([n_, p_])
                && eqq!(&m_ + &n_, 0)
                && gtq!(p_, 1)
                && neq!(n_, 1)
        },
        rhs: {
            let angle = &a__ + &b__ * x_.pow(&n_);
            rubi_simp(&(-&angle.sinh().pow(&p_) / ((&n_ - 1) * x_.pow(&n_ - 1))), x_)
                    + rubi_star(&b__ * &n_ * &p_ / (&n_ - 1), rubi_rhs_int(&(&angle.sinh().pow(&p_ - 1) * angle.cosh()), x_))
        },
    ));
}

fn push_rules_rule_5854(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5854,
        source: "Int[x_^m_.*Cosh[a_.+b_.*x_^n_]^p_,x_Symbol] :=
          -Cosh[a+b*x^n]^p/((n-1)*x^(n-1)) +
          b*n*p/(n-1) \\[Star] Int[Cosh[a+b*x^n]^(p-1)*Sinh[a+b*x^n],x] /;
        FreeQ[{a,b},x] && IntegersQ[n,p] && EqQ[m+n,0] && GtQ[p,1] && NeQ[n,1]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_12(symbols),
        with: [m_, a__, b__, n_, p_, x_],
        optional: [m_, a__, b__],
        when: {
            freeq!([a__, b__], x_)
                && integersq!([n_, p_])
                && eqq!(&m_ + &n_, 0)
                && gtq!(p_, 1)
                && neq!(n_, 1)
        },
        rhs: {
            let angle = &a__ + &b__ * x_.pow(&n_);
            rubi_simp(&(-&angle.cosh().pow(&p_) / ((&n_ - 1) * x_.pow(&n_ - 1))), x_)
                    + rubi_star(&b__ * &n_ * &p_ / (&n_ - 1), rubi_rhs_int(&(&angle.cosh().pow(&p_ - 1) * angle.sinh()), x_))
        },
    ));
}

fn push_rules_rule_5855(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5855,
        source: "Int[x_^m_.*Sinh[a_.+b_.*x_^n_]^p_,x_Symbol] :=
          -n*Sinh[a+b*x^n]^p/(b^2*n^2*p^2) +
          x^n*Cosh[a+b*x^n]*Sinh[a+b*x^n]^(p-1)/(b*n*p) -
          (p-1)/p \\[Star] Int[x^m*Sinh[a+b*x^n]^(p-2),x] /;
        FreeQ[{a,b,m,n},x] && EqQ[m-2*n+1] && GtQ[p,1]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: ["G&R 2.471.1b' special case when m-2n+1\\[Equal]0", "G&R 2.471.1a' special case with m-2n+1\\[Equal]0"],
        pattern:  rubi_shared_pattern_14(symbols),
        with: [m_, a__, b__, n_, p_, x_],
        optional: [m_, a__, b__],
        when: {
            freeq!([a__, b__, m_, n_], x_)
                && eqq!(&m_ - Atom::num(2) * &n_ + 1, 0)
                && gtq!(p_, 1)
        },
        rhs: {
            let angle = &a__ + &b__ * x_.pow(&n_);
            let denominator = b__.pow(2) * n_.pow(2) * p_.pow(2);
            rubi_simp(&(-&n_ * &angle.sinh().pow(&p_) / &denominator), x_)
                    + rubi_simp(&(x_.pow(&n_) * &angle.cosh() * &angle.sinh().pow(&p_ - 1)
                        / (&b__ * &n_ * &p_)), x_)
                    - rubi_star((&p_ - 1) / &p_, rubi_rhs_int(&(x_.pow(&m_) * angle.sinh().pow(&p_ - 2)), x_))
        },
    ));
}

fn push_rules_rule_5856(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5856,
        source: "Int[x_^m_.*Cosh[a_.+b_.*x_^n_]^p_,x_Symbol] :=
          -n*Cosh[a+b*x^n]^p/(b^2*n^2*p^2) +
          x^n*Sinh[a+b*x^n]*Cosh[a+b*x^n]^(p-1)/(b*n*p) +
          (p-1)/p \\[Star] Int[x^m*Cosh[a+b*x^n]^(p-2),x] /;
        FreeQ[{a,b,m,n},x] && EqQ[m-2*n+1] && GtQ[p,1]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: ["G&R 2.471.1b' special case when m-2n+1\\[Equal]0", "G&R 2.471.1a' special case with m-2n+1\\[Equal]0"],
        pattern:  rubi_shared_pattern_12(symbols),
        with: [m_, a__, b__, n_, p_, x_],
        optional: [m_, a__, b__],
        when: {
            freeq!([a__, b__, m_, n_], x_)
                && eqq!(&m_ - Atom::num(2) * &n_ + 1, 0)
                && gtq!(p_, 1)
        },
        rhs: {
            let angle = &a__ + &b__ * x_.pow(&n_);
            let denominator = b__.pow(2) * n_.pow(2) * p_.pow(2);
            rubi_simp(&(-&n_ * &angle.cosh().pow(&p_) / &denominator), x_)
                    + rubi_simp(&(x_.pow(&n_) * &angle.sinh() * &angle.cosh().pow(&p_ - 1)
                        / (&b__ * &n_ * &p_)), x_)
                    + rubi_star((&p_ - 1) / &p_, rubi_rhs_int(&(x_.pow(&m_) * angle.cosh().pow(&p_ - 2)), x_))
        },
    ));
}

fn push_rules_rule_5857(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5857,
        source: "Int[x_^m_.*Sinh[a_.+b_.*x_^n_]^p_,x_Symbol] :=
          -(m-n+1)*x^(m-2*n+1)*Sinh[a+b*x^n]^p/(b^2*n^2*p^2) +
          x^(m-n+1)*Cosh[a+b*x^n]*Sinh[a+b*x^n]^(p-1)/(b*n*p) -
          (p-1)/p \\[Star] Int[x^m*Sinh[a+b*x^n]^(p-2),x] +
          (m-n+1)*(m-2*n+1)/(b^2*n^2*p^2) \\[Star] Int[x^(m-2*n)*Sinh[a+b*x^n]^p,x] /;
        FreeQ[{a,b},x] && IntegersQ[m,n] && GtQ[p,1] && LtQ[0,2*n,m+1]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: ["G&R 2.471.1b'", "G&R 2.631.3'"],
        pattern:  rubi_shared_pattern_14(symbols),
        with: [m_, a__, b__, n_, p_, x_],
        optional: [m_, a__, b__],
        when: {
            let two_n = Atom::num(2) * &n_;
            freeq!([a__, b__], x_)
                && integersq!([m_, n_])
                && gtq!(p_, 1)
                && ltq!(0, &two_n, &m_ + 1)
        },
        rhs: {
            let angle = &a__ + &b__ * x_.pow(&n_);
            let m_n_1 = &m_ - &n_ + 1;
            let m_2n_1 = &m_ - Atom::num(2) * &n_ + 1;
            let denominator = b__.pow(2) * n_.pow(2) * p_.pow(2);
            rubi_simp(&(-&m_n_1 * x_.pow(&m_2n_1) * &angle.sinh().pow(&p_) / &denominator), x_)
                    + rubi_simp(&(x_.pow(&m_n_1) * &angle.cosh() * &angle.sinh().pow(&p_ - 1)
                        / (&b__ * &n_ * &p_)), x_)
                    - rubi_star((&p_ - 1) / &p_, rubi_rhs_int(
                            &(x_.pow(&m_) * &angle.sinh().pow(&p_ - 2)),
                            x_,
                        ))
                    + rubi_star(&m_n_1 * &m_2n_1 / &denominator, rubi_rhs_int(
                            &(x_.pow(&m_ - Atom::num(2) * &n_) * angle.sinh().pow(&p_)),
                            x_,
                        ))
        },
    ));
}

fn push_rules_rule_5858(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5858,
        source: "Int[x_^m_.*Cosh[a_.+b_.*x_^n_]^p_,x_Symbol] :=
          -(m-n+1)*x^(m-2*n+1)*Cosh[a+b*x^n]^p/(b^2*n^2*p^2) +
          x^(m-n+1)*Sinh[a+b*x^n]*Cosh[a+b*x^n]^(p-1)/(b*n*p) +
          (p-1)/p \\[Star] Int[x^m*Cosh[a+b*x^n]^(p-2),x] +
          (m-n+1)*(m-2*n+1)/(b^2*n^2*p^2) \\[Star] Int[x^(m-2*n)*Cosh[a+b*x^n]^p,x] /;
        FreeQ[{a,b},x] && IntegersQ[m,n] && GtQ[p,1] && LtQ[0,2*n,m+1]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: ["G&R 2.471.1b'", "G&R 2.631.3'"],
        pattern:  rubi_shared_pattern_12(symbols),
        with: [m_, a__, b__, n_, p_, x_],
        optional: [m_, a__, b__],
        when: {
            let two_n = Atom::num(2) * &n_;
            freeq!([a__, b__], x_)
                && integersq!([m_, n_])
                && gtq!(p_, 1)
                && ltq!(0, &two_n, &m_ + 1)
        },
        rhs: {
            let angle = &a__ + &b__ * x_.pow(&n_);
            let m_n_1 = &m_ - &n_ + 1;
            let m_2n_1 = &m_ - Atom::num(2) * &n_ + 1;
            let denominator = b__.pow(2) * n_.pow(2) * p_.pow(2);
            rubi_simp(&(-&m_n_1 * x_.pow(&m_2n_1) * &angle.cosh().pow(&p_) / &denominator), x_)
                    + rubi_simp(&(x_.pow(&m_n_1) * &angle.sinh() * &angle.cosh().pow(&p_ - 1)
                        / (&b__ * &n_ * &p_)), x_)
                    + rubi_star((&p_ - 1) / &p_, rubi_rhs_int(
                            &(x_.pow(&m_) * &angle.cosh().pow(&p_ - 2)),
                            x_,
                        ))
                    + rubi_star(&m_n_1 * &m_2n_1 / &denominator, rubi_rhs_int(
                            &(x_.pow(&m_ - Atom::num(2) * &n_) * angle.cosh().pow(&p_)),
                            x_,
                        ))
        },
    ));
}

fn push_rules_rule_5859(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5859,
        source: "Int[x_^m_.*Sinh[a_.+b_.*x_^n_]^p_,x_Symbol] :=
          x^(m+1)*Sinh[a+b*x^n]^p/(m+1) -
          b*n*p*x^(m+n+1)*Cosh[a+b*x^n]*Sinh[a+b*x^n]^(p-1)/((m+1)*(m+n+1)) +
          b^2*n^2*p^2/((m+1)*(m+n+1)) \\[Star] Int[x^(m+2*n)*Sinh[a+b*x^n]^p,x] +
          b^2*n^2*p*(p-1)/((m+1)*(m+n+1)) \\[Star] Int[x^(m+2*n)*Sinh[a+b*x^n]^(p-2),x] /;
        FreeQ[{a,b},x] && IntegersQ[m,n] && GtQ[p,1] && LtQ[0,2*n,1-m] && NeQ[m+n+1,0]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: ["G&R 2.475.1'", "G&R 2.475.2'"],
        pattern:  rubi_shared_pattern_14(symbols),
        with: [m_, a__, b__, n_, p_, x_],
        optional: [m_, a__, b__],
        when: {
            let two_n = Atom::num(2) * &n_;
            freeq!([a__, b__], x_)
                && integersq!([m_, n_])
                && gtq!(p_, 1)
                && ltq!(0, &two_n, Atom::num(1) - &m_)
                && neq!(&m_ + &n_ + 1, 0)
        },
        rhs: {
            let angle = &a__ + &b__ * x_.pow(&n_);
            let denominator = (&m_ + 1) * (&m_ + &n_ + 1);
            rubi_simp(&(x_.pow(&m_ + 1) * &angle.sinh().pow(&p_) / (&m_ + 1)), x_)
                    - rubi_simp(&(&b__ * &n_ * &p_ * x_.pow(&m_ + &n_ + 1) * &angle.cosh()
                        * &angle.sinh().pow(&p_ - 1)
                        / &denominator), x_)
                    + rubi_star(b__.pow(2) * n_.pow(2) * p_.pow(2) / &denominator, rubi_rhs_int(
                            &(x_.pow(&m_ + Atom::num(2) * &n_)
                                * &angle.sinh().pow(&p_)),
                            x_,
                        ))
                    + rubi_star(b__.pow(2) * n_.pow(2) * &p_ * (&p_ - 1) / &denominator, rubi_rhs_int(
                            &(x_.pow(&m_ + Atom::num(2) * &n_)
                                * angle.sinh().pow(&p_ - 2)),
                            x_,
                        ))
        },
    ));
}

fn push_rules_rule_5860(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5860,
        source: "Int[x_^m_.*Cosh[a_.+b_.*x_^n_]^p_,x_Symbol] :=
          x^(m+1)*Cosh[a+b*x^n]^p/(m+1) -
          b*n*p*x^(m+n+1)*Sinh[a+b*x^n]*Cosh[a+b*x^n]^(p-1)/((m+1)*(m+n+1)) +
          b^2*n^2*p^2/((m+1)*(m+n+1)) \\[Star] Int[x^(m+2*n)*Cosh[a+b*x^n]^p,x] -
          b^2*n^2*p*(p-1)/((m+1)*(m+n+1)) \\[Star] Int[x^(m+2*n)*Cosh[a+b*x^n]^(p-2),x] /;
        FreeQ[{a,b},x] && IntegersQ[m,n] && GtQ[p,1] && LtQ[0,2*n,1-m] && NeQ[m+n+1,0]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: ["G&R 2.475.1'", "G&R 2.475.2'"],
        pattern:  rubi_shared_pattern_12(symbols),
        with: [m_, a__, b__, n_, p_, x_],
        optional: [m_, a__, b__],
        when: {
            let two_n = Atom::num(2) * &n_;
            freeq!([a__, b__], x_)
                && integersq!([m_, n_])
                && gtq!(p_, 1)
                && ltq!(0, &two_n, Atom::num(1) - &m_)
                && neq!(&m_ + &n_ + 1, 0)
        },
        rhs: {
            let angle = &a__ + &b__ * x_.pow(&n_);
            let denominator = (&m_ + 1) * (&m_ + &n_ + 1);
            rubi_simp(&(x_.pow(&m_ + 1) * &angle.cosh().pow(&p_) / (&m_ + 1)), x_)
                    - rubi_simp(&(&b__ * &n_ * &p_ * x_.pow(&m_ + &n_ + 1) * &angle.sinh()
                        * &angle.cosh().pow(&p_ - 1)
                        / &denominator), x_)
                    + rubi_star(b__.pow(2) * n_.pow(2) * p_.pow(2) / &denominator, rubi_rhs_int(
                            &(x_.pow(&m_ + Atom::num(2) * &n_)
                                * &angle.cosh().pow(&p_)),
                            x_,
                        ))
                    - rubi_star(b__.pow(2) * n_.pow(2) * &p_ * (&p_ - 1) / &denominator, rubi_rhs_int(
                            &(x_.pow(&m_ + Atom::num(2) * &n_)
                                * angle.cosh().pow(&p_ - 2)),
                            x_,
                        ))
        },
    ));
}

fn push_rules_rule_5861(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5861,
        source: "Int[(e_.*x_)^m_*(a_.+b_.*Sinh[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
          With[{k=Denominator[m]},
          k/e \\[Star] Subst[Int[x^(k*(m+1)-1)*(a+b*Sinh[c+d*x^(k*n)/e^n])^p,x],x,(e*x)^(1/k)]] /;
        FreeQ[{a,b,c,d,e},x] && IntegerQ[p] && IGtQ[n,0] && FractionQ[m]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [e__, m_, a__, b__, c__, d__, n_, p_, x_],
        optional: [e__, a__, b__, c__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && integerq!(p_)
                && igtq!(n_, 0)
                && fractionq!(m_)
        },
        rhs: {
            let k_i = rubi_denominator(&m_).rubi_rhs();
            let k = Atom::num(k_i);
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub = Atom::var(substitution_symbol);
            let transformed_integrand = sub.pow(&k * (&m_ + 1) - 1)
                * (&a__
                    + &b__
                        * (&c__ + &d__ * sub.pow((&k * &n_).expand()) / e__.pow(&n_)).sinh())
                .pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);

            rubi_star(&k / &e__, rubi_subst(
                    &transformed,
                    substitution_symbol,
                    (&e__ * x_).pow(Atom::num(1) / k_i),
                ))
        },
    ));
}

fn push_rules_rule_5862(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5862,
        source: "Int[(e_.*x_)^m_*(a_.+b_.*Cosh[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
          With[{k=Denominator[m]},
          k/e \\[Star] Subst[Int[x^(k*(m+1)-1)*(a+b*Cosh[c+d*x^(k*n)/e^n])^p,x],x,(e*x)^(1/k)]] /;
        FreeQ[{a,b,c,d,e},x] && IntegerQ[p] && IGtQ[n,0] && FractionQ[m]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [e__, m_, a__, b__, c__, d__, n_, p_, x_],
        optional: [e__, a__, b__, c__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && integerq!(p_)
                && igtq!(n_, 0)
                && fractionq!(m_)
        },
        rhs: {
            let k_i = rubi_denominator(&m_).rubi_rhs();
            let k = Atom::num(k_i);
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub = Atom::var(substitution_symbol);
            let transformed_integrand = sub.pow(&k * (&m_ + 1) - 1)
                * (&a__
                    + &b__
                        * (&c__ + &d__ * sub.pow((&k * &n_).expand()) / e__.pow(&n_)).cosh())
                .pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);

            rubi_star(&k / &e__, rubi_subst(
                    &transformed,
                    substitution_symbol,
                    (&e__ * x_).pow(Atom::num(1) / k_i),
                ))
        },
    ));
}

fn push_rules_rule_5863(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5863,
        source: "Int[(e_.*x_)^m_.*(a_.+b_.*Sinh[c_.+d_.*x_^n_])^p_,x_Symbol] :=
          Int[ExpandTrigReduce[(e*x)^m,(a+b*Sinh[c+d*x^n])^p,x],x] /;
        FreeQ[{a,b,c,d,e,m},x] && IGtQ[p,1] && IGtQ[n,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [e__, m_, a__, b__, c__, d__, n_, p_, x_],
        optional: [e__, m_, a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_], x_)
                && igtq!(p_, 1)
                && igtq!(n_, 0)
        },
        rhs: {
            let multiplier = (&e__ * x_).pow(&m_);
            let power = (&a__ + &b__ * (&c__ + &d__ * x_.pow(&n_)).sinh()).pow(&p_);
            rubi_rhs_int(
                &rubi_expand_trig_reduce(&multiplier, &power, x_),
                x_,
            )
        },
    ));
}

fn push_rules_rule_5864(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5864,
        source: "Int[(e_.*x_)^m_.*(a_.+b_.*Cosh[c_.+d_.*x_^n_])^p_,x_Symbol] :=
          Int[ExpandTrigReduce[(e*x)^m,(a+b*Cosh[c+d*x^n])^p,x],x] /;
        FreeQ[{a,b,c,d,e,m},x] && IGtQ[p,1] && IGtQ[n,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [e__, m_, a__, b__, c__, d__, n_, p_, x_],
        optional: [e__, m_, a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_], x_)
                && igtq!(p_, 1)
                && igtq!(n_, 0)
        },
        rhs: {
            let multiplier = (&e__ * x_).pow(&m_);
            let power = (&a__ + &b__ * (&c__ + &d__ * x_.pow(&n_)).cosh()).pow(&p_);
            rubi_rhs_int(
                &rubi_expand_trig_reduce(&multiplier, &power, x_),
                x_,
            )
        },
    ));
}

fn push_rules_rule_5865(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5865,
        source: "Int[x_^m_.*Sinh[a_.+b_.*x_^n_]^p_,x_Symbol] :=
          x^n*Cosh[a+b*x^n]*Sinh[a+b*x^n]^(p+1)/(b*n*(p+1)) -
          n*Sinh[a+b*x^n]^(p+2)/(b^2*n^2*(p+1)*(p+2)) -
          (p+2)/(p+1) \\[Star] Int[x^m*Sinh[a+b*x^n]^(p+2),x] /;
        FreeQ[{a,b,m,n},x] && EqQ[m-2*n+1,0] && LtQ[p,-1] && NeQ[p,-2]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: ["G&R 2.477.1 special case when m-2n+1=0", "G&R 2.477.2' special case with m-2n+1=0"],
        pattern:  rubi_shared_pattern_14(symbols),
        with: [m_, a__, b__, n_, p_, x_],
        optional: [m_, a__, b__],
        when: {
            freeq!([a__, b__, m_, n_], x_)
                && eqq!(&m_ - Atom::num(2) * &n_ + 1, 0)
                && ltq!(p_, -1)
                && neq!(p_, -2)
        },
        rhs: {
            let angle = &a__ + &b__ * x_.pow(&n_);
            let denominator = b__.pow(2) * n_.pow(2) * (&p_ + 1) * (&p_ + 2);
            rubi_simp(&(x_.pow(&n_) * &angle.cosh() * &angle.sinh().pow(&p_ + 1)
                    / (&b__ * &n_ * (&p_ + 1))), x_)
                    - rubi_simp(&(&n_ * &angle.sinh().pow(&p_ + 2) / &denominator), x_)
                    - rubi_star((&p_ + 2) / (&p_ + 1), rubi_rhs_int(&(x_.pow(&m_) * angle.sinh().pow(&p_ + 2)), x_))
        },
    ));
}

fn push_rules_rule_5866(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5866,
        source: "Int[x_^m_.*Cosh[a_.+b_.*x_^n_]^p_,x_Symbol] :=
          -x^n*Sinh[a+b*x^n]*Cosh[a+b*x^n]^(p+1)/(b*n*(p+1)) +
          n*Cosh[a+b*x^n]^(p+2)/(b^2*n^2*(p+1)*(p+2)) +
          (p+2)/(p+1) \\[Star] Int[x^m*Cosh[a+b*x^n]^(p+2),x] /;
        FreeQ[{a,b,m,n},x] && EqQ[m-2*n+1,0] && LtQ[p,-1] && NeQ[p,-2]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: ["G&R 2.477.1 special case when m-2n+1=0", "G&R 2.477.2' special case with m-2n+1=0"],
        pattern:  rubi_shared_pattern_12(symbols),
        with: [m_, a__, b__, n_, p_, x_],
        optional: [m_, a__, b__],
        when: {
            freeq!([a__, b__, m_, n_], x_)
                && eqq!(&m_ - Atom::num(2) * &n_ + 1, 0)
                && ltq!(p_, -1)
                && neq!(p_, -2)
        },
        rhs: {
            let angle = &a__ + &b__ * x_.pow(&n_);
            let denominator = b__.pow(2) * n_.pow(2) * (&p_ + 1) * (&p_ + 2);
            rubi_simp(&(Atom::num(-1) * x_.pow(&n_) * &angle.sinh() * &angle.cosh().pow(&p_ + 1)
                    / (&b__ * &n_ * (&p_ + 1))), x_)
                    + rubi_simp(&(&n_ * &angle.cosh().pow(&p_ + 2) / &denominator), x_)
                    + rubi_star((&p_ + 2) / (&p_ + 1), rubi_rhs_int(&(x_.pow(&m_) * angle.cosh().pow(&p_ + 2)), x_))
        },
    ));
}

fn push_rules_rule_5867(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5867,
        source: "Int[x_^m_.*Sinh[a_.+b_.*x_^n_]^p_,x_Symbol] :=
          x^(m-n+1)*Cosh[a+b*x^n]*Sinh[a+b*x^n]^(p+1)/(b*n*(p+1)) -
          (m-n+1)*x^(m-2*n+1)*Sinh[a+b*x^n]^(p+2)/(b^2*n^2*(p+1)*(p+2)) -
          (p+2)/(p+1) \\[Star] Int[x^m*Sinh[a+b*x^n]^(p+2),x] +
          (m-n+1)*(m-2*n+1)/(b^2*n^2*(p+1)*(p+2)) \\[Star] Int[x^(m-2*n)*Sinh[a+b*x^n]^(p+2),x] /;
        FreeQ[{a,b},x] && IntegersQ[m,n] && LtQ[p,-1] && NeQ[p,-2] && LtQ[0,2*n,m+1]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: ["G&R 2.477.1", "G&R 2.477.2"],
        pattern:  rubi_shared_pattern_14(symbols),
        with: [m_, a__, b__, n_, p_, x_],
        optional: [m_, a__, b__],
        when: {
            let two_n = Atom::num(2) * &n_;
            freeq!([a__, b__], x_)
                && integersq!([m_, n_])
                && ltq!(p_, -1)
                && neq!(p_, -2)
                && ltq!(0, &two_n, &m_ + 1)
        },
        rhs: {
            let angle = &a__ + &b__ * x_.pow(&n_);
            let m_n_1 = &m_ - &n_ + 1;
            let m_2n_1 = &m_ - Atom::num(2) * &n_ + 1;
            let denominator = b__.pow(2) * n_.pow(2) * (&p_ + 1) * (&p_ + 2);
            rubi_simp(&(x_.pow(&m_n_1) * &angle.cosh() * &angle.sinh().pow(&p_ + 1)
                    / (&b__ * &n_ * (&p_ + 1))), x_)
                    - rubi_simp(&(&m_n_1 * x_.pow(&m_2n_1) * &angle.sinh().pow(&p_ + 2)
                        / &denominator), x_)
                    - rubi_star((&p_ + 2) / (&p_ + 1), rubi_rhs_int(
                            &(x_.pow(&m_) * &angle.sinh().pow(&p_ + 2)),
                            x_,
                        ))
                    + rubi_star(&m_n_1 * &m_2n_1 / &denominator, rubi_rhs_int(
                            &(x_.pow(&m_ - Atom::num(2) * &n_)
                                * angle.sinh().pow(&p_ + 2)),
                            x_,
                        ))
        },
    ));
}

fn push_rules_rule_5868(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5868,
        source: "Int[x_^m_.*Cosh[a_.+b_.*x_^n_]^p_,x_Symbol] :=
          -x^(m-n+1)*Sinh[a+b*x^n]*Cosh[a+b*x^n]^(p+1)/(b*n*(p+1)) +
          (m-n+1)*x^(m-2*n+1)*Cosh[a+b*x^n]^(p+2)/(b^2*n^2*(p+1)*(p+2)) +
          (p+2)/(p+1) \\[Star] Int[x^m*Cosh[a+b*x^n]^(p+2),x] -
          (m-n+1)*(m-2*n+1)/(b^2*n^2*(p+1)*(p+2)) \\[Star] Int[x^(m-2*n)*Cosh[a+b*x^n]^(p+2),x] /;
        FreeQ[{a,b},x] && IntegersQ[m,n] && LtQ[p,-1] && NeQ[p,-2] && LtQ[0,2*n,m+1]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: ["G&R 2.477.1", "G&R 2.477.2"],
        pattern:  rubi_shared_pattern_12(symbols),
        with: [m_, a__, b__, n_, p_, x_],
        optional: [m_, a__, b__],
        when: {
            let two_n = Atom::num(2) * &n_;
            freeq!([a__, b__], x_)
                && integersq!([m_, n_])
                && ltq!(p_, -1)
                && neq!(p_, -2)
                && ltq!(0, &two_n, &m_ + 1)
        },
        rhs: {
            let angle = &a__ + &b__ * x_.pow(&n_);
            let m_n_1 = &m_ - &n_ + 1;
            let m_2n_1 = &m_ - Atom::num(2) * &n_ + 1;
            let denominator = b__.pow(2) * n_.pow(2) * (&p_ + 1) * (&p_ + 2);
            rubi_simp(&(Atom::num(-1) * x_.pow(&m_n_1) * &angle.sinh() * &angle.cosh().pow(&p_ + 1)
                    / (&b__ * &n_ * (&p_ + 1))), x_)
                    + rubi_simp(&(&m_n_1 * x_.pow(&m_2n_1) * &angle.cosh().pow(&p_ + 2)
                        / &denominator), x_)
                    + rubi_star((&p_ + 2) / (&p_ + 1), rubi_rhs_int(
                            &(x_.pow(&m_) * &angle.cosh().pow(&p_ + 2)),
                            x_,
                        ))
                    - rubi_star(&m_n_1 * &m_2n_1 / &denominator, rubi_rhs_int(
                            &(x_.pow(&m_ - Atom::num(2) * &n_)
                                * angle.cosh().pow(&p_ + 2)),
                            x_,
                        ))
        },
    ));
}

fn push_rules_rule_5869(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5869,
        source: "Int[x_^m_.*(a_.+b_.*Sinh[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
          -Subst[Int[(a+b*Sinh[c+d*x^(-n)])^p/x^(m+2),x],x,1/x] /;
        FreeQ[{a,b,c,d},x] && IntegerQ[p] && ILtQ[n,0] && IntegerQ[m]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_11(symbols),
        with: [m_, a__, b__, c__, d__, n_, p_, x_],
        optional: [m_, a__, b__, c__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && integerq!(p_)
                && iltq!(n_, 0)
                && integerq!(m_)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub = Atom::var(substitution_symbol);
            let transformed_integrand =
                (&a__ + &b__ * (&c__ + &d__ * sub.pow(-&n_)).sinh()).pow(&p_) / sub.pow(&m_ + 2);
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);

            -rubi_subst(&transformed, substitution_symbol, Atom::num(1) / x_)
        },
    ));
}

fn push_rules_rule_5870(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5870,
        source: "Int[x_^m_.*(a_.+b_.*Cosh[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
          -Subst[Int[(a+b*Cosh[c+d*x^(-n)])^p/x^(m+2),x],x,1/x] /;
        FreeQ[{a,b,c,d},x] && IntegerQ[p] && ILtQ[n,0] && IntegerQ[m]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_10(symbols),
        with: [m_, a__, b__, c__, d__, n_, p_, x_],
        optional: [m_, a__, b__, c__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && integerq!(p_)
                && iltq!(n_, 0)
                && integerq!(m_)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub = Atom::var(substitution_symbol);
            let transformed_integrand =
                (&a__ + &b__ * (&c__ + &d__ * sub.pow(-&n_)).cosh()).pow(&p_) / sub.pow(&m_ + 2);
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);

            -rubi_subst(&transformed, substitution_symbol, Atom::num(1) / x_)
        },
    ));
}

fn push_rules_rule_5871(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5871,
        source: "Int[(e_.*x_)^m_*(a_.+b_.*Sinh[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
          With[{k=Denominator[m]},
          -k/e \\[Star] Subst[Int[(a+b*Sinh[c+d/(e^n*x^(k*n))])^p/x^(k*(m+1)+1),x],x,1/(e*x)^(1/k)]] /;
        FreeQ[{a,b,c,d,e},x] && IntegerQ[p] && ILtQ[n,0] && FractionQ[m]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [e__, m_, a__, b__, c__, d__, n_, p_, x_],
        optional: [e__, a__, b__, c__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && integerq!(p_)
                && iltq!(n_, 0)
                && fractionq!(m_)
        },
        rhs: {
            let k_i = rubi_denominator(&m_).rubi_rhs();
            let k = Atom::num(k_i);
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub = Atom::var(substitution_symbol);
            let transformed_integrand = (&a__
                + &b__ * (&c__ + &d__ / (e__.pow(&n_) * sub.pow((&k * &n_).expand()))).sinh())
            .pow(&p_)
                / sub.pow(&k * (&m_ + 1) + 1);
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);

            rubi_star(-k / &e__, rubi_subst(
                    &transformed,
                    substitution_symbol,
                    Atom::num(1) / (&e__ * x_).pow(Atom::num(1) / k_i),
                ))
        },
    ));
}

fn push_rules_rule_5872(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5872,
        source: "Int[(e_.*x_)^m_*(a_.+b_.*Cosh[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
          With[{k=Denominator[m]},
          -k/e \\[Star] Subst[Int[(a+b*Cosh[c+d/(e^n*x^(k*n))])^p/x^(k*(m+1)+1),x],x,1/(e*x)^(1/k)]] /;
        FreeQ[{a,b,c,d,e},x] && IntegerQ[p] && ILtQ[n,0] && FractionQ[m]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [e__, m_, a__, b__, c__, d__, n_, p_, x_],
        optional: [e__, a__, b__, c__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && integerq!(p_)
                && iltq!(n_, 0)
                && fractionq!(m_)
        },
        rhs: {
            let k_i = rubi_denominator(&m_).rubi_rhs();
            let k = Atom::num(k_i);
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub = Atom::var(substitution_symbol);
            let transformed_integrand = (&a__
                + &b__ * (&c__ + &d__ / (e__.pow(&n_) * sub.pow((&k * &n_).expand()))).cosh())
            .pow(&p_)
                / sub.pow(&k * (&m_ + 1) + 1);
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);

            rubi_star(-k / &e__, rubi_subst(
                    &transformed,
                    substitution_symbol,
                    Atom::num(1) / (&e__ * x_).pow(Atom::num(1) / k_i),
                ))
        },
    ));
}

fn push_rules_rule_5873(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5873,
        source: "Int[(e_.*x_)^m_*(a_.+b_.*Sinh[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
          -(e*x)^m*(x^(-1))^m \\[Star] Subst[Int[(a+b*Sinh[c+d*x^(-n)])^p/x^(m+2),x],x,1/x] /;
        FreeQ[{a,b,c,d,e,m},x] && IntegerQ[p] && ILtQ[n,0] && Not[RationalQ[m]]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [e__, m_, a__, b__, c__, d__, n_, p_, x_],
        optional: [e__, a__, b__, c__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_], x_)
                && integerq!(p_)
                && iltq!(n_, 0)
                && !rationalq!(m_)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub = Atom::var(substitution_symbol);
            let transformed_integrand =
                (&a__ + &b__ * (&c__ + &d__ * sub.pow(-&n_)).sinh()).pow(&p_) / sub.pow(&m_ + 2);
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);

            rubi_star(-(&e__ * x_).pow(&m_) * (Atom::num(1) / x_).pow(&m_), rubi_subst(&transformed, substitution_symbol, Atom::num(1) / x_))
        },
    ));
}

fn push_rules_rule_5874(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5874,
        source: "Int[(e_.*x_)^m_*(a_.+b_.*Cosh[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
          -(e*x)^m*(x^(-1))^m \\[Star] Subst[Int[(a+b*Cosh[c+d*x^(-n)])^p/x^(m+2),x],x,1/x] /;
        FreeQ[{a,b,c,d,e,m},x] && IntegerQ[p] && ILtQ[n,0] && Not[RationalQ[m]]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [e__, m_, a__, b__, c__, d__, n_, p_, x_],
        optional: [e__, a__, b__, c__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_], x_)
                && integerq!(p_)
                && iltq!(n_, 0)
                && !rationalq!(m_)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub = Atom::var(substitution_symbol);
            let transformed_integrand =
                (&a__ + &b__ * (&c__ + &d__ * sub.pow(-&n_)).cosh()).pow(&p_) / sub.pow(&m_ + 2);
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);

            rubi_star(-(&e__ * x_).pow(&m_) * (Atom::num(1) / x_).pow(&m_), rubi_subst(&transformed, substitution_symbol, Atom::num(1) / x_))
        },
    ));
}

fn push_rules_rule_5875(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5875,
        source: "Int[x_^m_.*(a_.+b_.*Sinh[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
          Module[{k=Denominator[n]},
          k \\[Star] Subst[Int[x^(k*(m+1)-1)*(a+b*Sinh[c+d*x^(k*n)])^p,x],x,x^(1/k)]] /;
        FreeQ[{a,b,c,d,m},x] && IntegerQ[p] && FractionQ[n]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_11(symbols),
        with: [m_, a__, b__, c__, d__, n_, p_, x_],
        optional: [m_, a__, b__, c__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__, m_], x_)
                && integerq!(p_)
                && fractionq!(n_)
        },
        rhs: {
            let k_i = rubi_denominator(&n_).rubi_rhs();
            let k = Atom::num(k_i);
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub = Atom::var(substitution_symbol);
            let transformed_integrand = sub.pow(&k * (&m_ + 1) - 1)
                * (&a__ + &b__ * (&c__ + &d__ * sub.pow((&k * &n_).expand())).sinh()).pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);

            rubi_star(k, rubi_subst(
                    &transformed,
                    substitution_symbol,
                    x_.pow(Atom::num(1) / k_i),
                ))
        },
    ));
}

fn push_rules_rule_5876(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5876,
        source: "Int[x_^m_.*(a_.+b_.*Cosh[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
          Module[{k=Denominator[n]},
          k \\[Star] Subst[Int[x^(k*(m+1)-1)*(a+b*Cosh[c+d*x^(k*n)])^p,x],x,x^(1/k)]] /;
        FreeQ[{a,b,c,d,m},x] && IntegerQ[p] && FractionQ[n]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_10(symbols),
        with: [m_, a__, b__, c__, d__, n_, p_, x_],
        optional: [m_, a__, b__, c__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__, m_], x_)
                && integerq!(p_)
                && fractionq!(n_)
        },
        rhs: {
            let k_i = rubi_denominator(&n_).rubi_rhs();
            let k = Atom::num(k_i);
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub = Atom::var(substitution_symbol);
            let transformed_integrand = sub.pow(&k * (&m_ + 1) - 1)
                * (&a__ + &b__ * (&c__ + &d__ * sub.pow((&k * &n_).expand())).cosh()).pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);

            rubi_star(k, rubi_subst(
                    &transformed,
                    substitution_symbol,
                    x_.pow(Atom::num(1) / k_i),
                ))
        },
    ));
}

fn push_rules_rule_5877(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; e__, a__, b__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5877,
        source: "Int[(e_*x_)^m_*(a_.+b_.*Sinh[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
          e^IntPart[m]*(e*x)^FracPart[m]/x^FracPart[m] \\[Star] Int[x^m*(a+b*Sinh[c+d*x^n])^p,x] /;
        FreeQ[{a,b,c,d,e,m},x] && IntegerQ[p] && FractionQ[n]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [e__, m_, a__, b__, c__, d__, n_, p_, x_],
        optional: [a__, b__, c__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_], x_)
                && integerq!(p_)
                && fractionq!(n_)
        },
        rhs: {
            let frac_m = rubi_frac_part(&m_);
            let recursive = rubi_rhs_int(
                &(x_.pow(&m_)
                    * (&a__ + &b__ * (&c__ + &d__ * x_.pow(&n_)).sinh()).pow(&p_)),
                x_,
            );
            rubi_star(e__.pow(rubi_int_part(&m_)) * (&e__ * x_).pow(&frac_m)
                    / x_.pow(frac_m), recursive)
        },
    ));
}

fn push_rules_rule_5878(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; e__, a__, b__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5878,
        source: "Int[(e_*x_)^m_*(a_.+b_.*Cosh[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
          e^IntPart[m]*(e*x)^FracPart[m]/x^FracPart[m] \\[Star] Int[x^m*(a+b*Cosh[c+d*x^n])^p,x] /;
        FreeQ[{a,b,c,d,e,m},x] && IntegerQ[p] && FractionQ[n]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [e__, m_, a__, b__, c__, d__, n_, p_, x_],
        optional: [a__, b__, c__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_], x_)
                && integerq!(p_)
                && fractionq!(n_)
        },
        rhs: {
            let frac_m = rubi_frac_part(&m_);
            let recursive = rubi_rhs_int(
                &(x_.pow(&m_)
                    * (&a__ + &b__ * (&c__ + &d__ * x_.pow(&n_)).cosh()).pow(&p_)),
                x_,
            );
            rubi_star(e__.pow(rubi_int_part(&m_)) * (&e__ * x_).pow(&frac_m)
                    / x_.pow(frac_m), recursive)
        },
    ));
}

fn push_rules_rule_5879(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5879,
        source: "Int[x_^m_.*(a_.+b_.*Sinh[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
          1/(m+1) \\[Star] Subst[Int[(a+b*Sinh[c+d*x^Simplify[n/(m+1)]])^p,x],x,x^(m+1)] /;
        FreeQ[{a,b,c,d,m,n},x] && IntegerQ[p] && NeQ[m,-1] && IGtQ[Simplify[n/(m+1)],0] && Not[IntegerQ[n]]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_11(symbols),
        with: [m_, a__, b__, c__, d__, n_, p_, x_],
        optional: [m_, a__, b__, c__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__, m_, n_], x_)
                && integerq!(p_)
                && neq!(m_, -1)
                && {
                    let quotient = rubi_simplify(&(&n_ / (&m_ + 1)));
                    igtq!(quotient, 0) && !integerq!(n_)
                }
        },
        rhs: {
            let quotient = rubi_simplify(&(&n_ / (&m_ + 1)));
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub = Atom::var(substitution_symbol);
            let transformed_integrand = (&a__ + &b__ * (&c__ + &d__ * sub.pow(&quotient)).sinh()).pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);

            rubi_star(Atom::num(1) / (&m_ + 1), rubi_subst(
                    &transformed,
                    substitution_symbol,
                    x_.pow(&m_ + 1),
                ))
        },
    ));
}

fn push_rules_rule_5880(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5880,
        source: "Int[x_^m_.*(a_.+b_.*Cosh[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
          1/(m+1) \\[Star] Subst[Int[(a+b*Cosh[c+d*x^Simplify[n/(m+1)]])^p,x],x,x^(m+1)] /;
        FreeQ[{a,b,c,d,m,n},x] && IntegerQ[p] && NeQ[m,-1] && IGtQ[Simplify[n/(m+1)],0] && Not[IntegerQ[n]]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_10(symbols),
        with: [m_, a__, b__, c__, d__, n_, p_, x_],
        optional: [m_, a__, b__, c__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__, m_, n_], x_)
                && integerq!(p_)
                && neq!(m_, -1)
                && {
                    let quotient = rubi_simplify(&(&n_ / (&m_ + 1)));
                    igtq!(quotient, 0) && !integerq!(n_)
                }
        },
        rhs: {
            let quotient = rubi_simplify(&(&n_ / (&m_ + 1)));
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub = Atom::var(substitution_symbol);
            let transformed_integrand = (&a__ + &b__ * (&c__ + &d__ * sub.pow(&quotient)).cosh()).pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);

            rubi_star(Atom::num(1) / (&m_ + 1), rubi_subst(
                    &transformed,
                    substitution_symbol,
                    x_.pow(&m_ + 1),
                ))
        },
    ));
}

fn push_rules_rule_5881(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; e__, a__, b__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5881,
        source: "Int[(e_*x_)^m_*(a_.+b_.*Sinh[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
          e^IntPart[m]*(e*x)^FracPart[m]/x^FracPart[m] \\[Star] Int[x^m*(a+b*Sinh[c+d*x^n])^p,x] /;
        FreeQ[{a,b,c,d,e,m,n},x] && IntegerQ[p] && NeQ[m,-1] && IGtQ[Simplify[n/(m+1)],0] && Not[IntegerQ[n]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [e__, m_, a__, b__, c__, d__, n_, p_, x_],
        optional: [a__, b__, c__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_], x_)
                && integerq!(p_)
                && neq!(m_, -1)
                && igtq!(rubi_simplify(&(&n_ / (&m_ + 1))), 0)
                && !integerq!(n_)
        },
        rhs: {
            let frac_m = rubi_frac_part(&m_);
            let recursive = rubi_rhs_int(
                &(x_.pow(&m_)
                    * (&a__ + &b__ * (&c__ + &d__ * x_.pow(&n_)).sinh()).pow(&p_)),
                x_,
            );
            rubi_star(e__.pow(rubi_int_part(&m_)) * (&e__ * x_).pow(&frac_m)
                    / x_.pow(frac_m), recursive)
        },
    ));
}

fn push_rules_rule_5882(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; e__, a__, b__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5882,
        source: "Int[(e_*x_)^m_*(a_.+b_.*Cosh[c_.+d_.*x_^n_])^p_.,x_Symbol] :=
          e^IntPart[m]*(e*x)^FracPart[m]/x^FracPart[m] \\[Star] Int[x^m*(a+b*Cosh[c+d*x^n])^p,x] /;
        FreeQ[{a,b,c,d,e,m,n},x] && IntegerQ[p] && NeQ[m,-1] && IGtQ[Simplify[n/(m+1)],0] && Not[IntegerQ[n]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [e__, m_, a__, b__, c__, d__, n_, p_, x_],
        optional: [a__, b__, c__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_], x_)
                && integerq!(p_)
                && neq!(m_, -1)
                && igtq!(rubi_simplify(&(&n_ / (&m_ + 1))), 0)
                && !integerq!(n_)
        },
        rhs: {
            let frac_m = rubi_frac_part(&m_);
            let recursive = rubi_rhs_int(
                &(x_.pow(&m_)
                    * (&a__ + &b__ * (&c__ + &d__ * x_.pow(&n_)).cosh()).pow(&p_)),
                x_,
            );
            rubi_star(e__.pow(rubi_int_part(&m_)) * (&e__ * x_).pow(&frac_m)
                    / x_.pow(frac_m), recursive)
        },
    ));
}

fn push_rules_rule_5883(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; c__, d__, e__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5883,
        source: "Int[(e_.*x_)^m_.*Sinh[c_.+d_.*x_^n_],x_Symbol] :=
          1/2 \\[Star] Int[(e*x)^m*E^(c+d*x^n),x] - 1/2 \\[Star] Int[(e*x)^m*E^(-c-d*x^n),x] /;
        FreeQ[{c,d,e,m,n},x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [e__, m_, c__, d__, n_, x_],
        optional: [e__, m_, c__, d__],
        when: { freeq!([c__, d__, e__, m_, n_], x_) },
        rhs: {
            let angle = &c__ + &d__ * x_.pow(&n_);
            let power = (&e__ * x_).pow(&m_);
            rubi_star(Atom::num(1) / 2, rubi_rhs_int(&(&power * &angle.exp()), x_)) - rubi_star(Atom::num(1) / 2, rubi_rhs_int(&(power * (-angle).exp()), x_))
        },
    ));
}

fn push_rules_rule_5884(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; c__, d__, e__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5884,
        source: "Int[(e_.*x_)^m_.*Cosh[c_.+d_.*x_^n_],x_Symbol] :=
          1/2 \\[Star] Int[(e*x)^m*E^(c+d*x^n),x] + 1/2 \\[Star] Int[(e*x)^m*E^(-c-d*x^n),x] /;
        FreeQ[{c,d,e,m,n},x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [e__, m_, c__, d__, n_, x_],
        optional: [e__, m_, c__, d__],
        when: { freeq!([c__, d__, e__, m_, n_], x_) },
        rhs: {
            let angle = &c__ + &d__ * x_.pow(&n_);
            let power = (&e__ * x_).pow(&m_);
            rubi_star(Atom::num(1) / 2, rubi_rhs_int(&(&power * &angle.exp()), x_)) + rubi_star(Atom::num(1) / 2, rubi_rhs_int(&(power * (-angle).exp()), x_))
        },
    ));
}

fn push_rules_rule_5885(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5885,
        source: "Int[(e_.*x_)^m_.*(a_.+b_.*Sinh[c_.+d_.*x_^n_])^p_,x_Symbol] :=
          Int[ExpandTrigReduce[(e*x)^m,(a+b*Sinh[c+d*x^n])^p,x],x] /;
        FreeQ[{a,b,c,d,e,m,n},x] && IGtQ[p,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [e__, m_, a__, b__, c__, d__, n_, p_, x_],
        optional: [e__, m_, a__, b__, c__, d__],
        when: { freeq!([a__, b__, c__, d__, e__, m_, n_], x_) && igtq!(p_, 0) },
        rhs: {
            let multiplier = (&e__ * x_).pow(&m_);
            let power = (&a__ + &b__ * (&c__ + &d__ * x_.pow(&n_)).sinh()).pow(&p_);
            rubi_rhs_int(
                &rubi_expand_trig_reduce(&multiplier, &power, x_),
                x_,
            )
        },
    ));
}

fn push_rules_rule_5886(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5886,
        source: "Int[(e_.*x_)^m_.*(a_.+b_.*Cosh[c_.+d_.*x_^n_])^p_,x_Symbol] :=
          Int[ExpandTrigReduce[(e*x)^m,(a+b*Cosh[c+d*x^n])^p,x],x] /;
        FreeQ[{a,b,c,d,e,m,n},x] && IGtQ[p,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [e__, m_, a__, b__, c__, d__, n_, p_, x_],
        optional: [e__, m_, a__, b__, c__, d__],
        when: { freeq!([a__, b__, c__, d__, e__, m_, n_], x_) && igtq!(p_, 0) },
        rhs: {
            let multiplier = (&e__ * x_).pow(&m_);
            let power = (&a__ + &b__ * (&c__ + &d__ * x_.pow(&n_)).cosh()).pow(&p_);
            rubi_rhs_int(
                &rubi_expand_trig_reduce(&multiplier, &power, x_),
                x_,
            )
        },
    ));
}

fn push_rules_rule_5887(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, n_, p_, u_, x_);
    rules.push(rubi_rule!(
        order: 5887,
        source: "Int[x_^m_.*(a_.+b_.*Sinh[c_.+d_.*u_^n_])^p_.,x_Symbol] :=
          1/Coefficient[u,x,1]^(m+1) \\[Star] Subst[Int[(x-Coefficient[u,x,0])^m*(a+b*Sinh[c+d*x^n])^p,x],x,u] /;
        FreeQ[{a,b,c,d,n,p},x] && LinearQ[u,x] && NeQ[u,x] && IntegerQ[m]",
        desc: "Integration by substitution",
        refs: [],
        pattern: x_.pow(m_) * (a__ + b__ * (c__ + d__ * Atom::var(u_).pow(n_)).sinh()).pow(p_),
        with: [m_, a__, b__, c__, d__, u_, n_, p_, x_],
        optional: [m_, a__, b__, c__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__, n_, p_], x_)
                && rubi_linear_q(&u_, x_)
                && neq!(u_, x_)
                && integerq!(m_)
        },
        rhs: {
            let coefficient = rubi_coefficient(&u_, x_, 1).rubi_rhs();
            let constant = rubi_coefficient(&u_, x_, 0).rubi_rhs();
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub = Atom::var(substitution_symbol);
            let transformed_integrand =
                (&sub - constant).pow(&m_) * (&a__ + &b__ * (&c__ + &d__ * sub.pow(&n_)).sinh()).pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);

            rubi_star(Atom::num(1) / coefficient.pow(&m_ + 1), rubi_subst(&transformed, substitution_symbol, &u_))
        },
    ));
}

fn push_rules_rule_5888(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, n_, p_, u_, x_);
    rules.push(rubi_rule!(
        order: 5888,
        source: "Int[x_^m_.*(a_.+b_.*Cosh[c_.+d_.*u_^n_])^p_.,x_Symbol] :=
          1/Coefficient[u,x,1]^(m+1) \\[Star] Subst[Int[(x-Coefficient[u,x,0])^m*(a+b*Cosh[c+d*x^n])^p,x],x,u] /;
        FreeQ[{a,b,c,d,n,p},x] && LinearQ[u,x] && NeQ[u,x] && IntegerQ[m]",
        desc: "Integration by substitution",
        refs: [],
        pattern: x_.pow(m_) * (a__ + b__ * (c__ + d__ * Atom::var(u_).pow(n_)).cosh()).pow(p_),
        with: [m_, a__, b__, c__, d__, u_, n_, p_, x_],
        optional: [m_, a__, b__, c__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__, n_, p_], x_)
                && rubi_linear_q(&u_, x_)
                && neq!(u_, x_)
                && integerq!(m_)
        },
        rhs: {
            let coefficient = rubi_coefficient(&u_, x_, 1).rubi_rhs();
            let constant = rubi_coefficient(&u_, x_, 0).rubi_rhs();
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub = Atom::var(substitution_symbol);
            let transformed_integrand =
                (&sub - constant).pow(&m_) * (&a__ + &b__ * (&c__ + &d__ * sub.pow(&n_)).cosh()).pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);

            rubi_star(Atom::num(1) / coefficient.pow(&m_ + 1), rubi_subst(&transformed, substitution_symbol, &u_))
        },
    ));
}

fn push_rules_rule_5889(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, n_, p_, u_, x_);
    rules.push(rubi_rule!(
        order: 5889,
        source: "Int[(e_.*x_)^m_.*(a_.+b_.*Sinh[c_.+d_.*u_^n_])^p_.,x_Symbol] :=
          Unintegrable[(e*x)^m*(a+b*Sinh[c+d*u^n])^p,x] /;
        FreeQ[{a,b,c,d,e,m,n,p},x] && LinearQ[u,x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern: (e__ * x_).pow(m_) * (a__ + b__ * (c__ + d__ * Atom::var(u_).pow(n_)).sinh()).pow(p_),
        with: [e__, m_, a__, b__, c__, d__, u_, n_, p_, x_],
        optional: [e__, m_, a__, b__, c__, d__, p_],
        when: { freeq!([a__, b__, c__, d__, e__, m_, n_, p_], x_) && rubi_linear_q(&u_, x_) },
        rhs: {
            rubi_unintegrable(
                (&e__ * x_).pow(&m_) * (&a__ + &b__ * (&c__ + &d__ * u_.pow(&n_)).sinh()).pow(&p_),
                x_,
            )
        },
    ));
}

fn push_rules_rule_5890(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, n_, p_, u_, x_);
    rules.push(rubi_rule!(
        order: 5890,
        source: "Int[(e_.*x_)^m_.*(a_.+b_.*Cosh[c_.+d_.*u_^n_])^p_.,x_Symbol] :=
          Unintegrable[(e*x)^m*(a+b*Cosh[c+d*u^n])^p,x] /;
        FreeQ[{a,b,c,d,e,m,n,p},x] && LinearQ[u,x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern: (e__ * x_).pow(m_) * (a__ + b__ * (c__ + d__ * Atom::var(u_).pow(n_)).cosh()).pow(p_),
        with: [e__, m_, a__, b__, c__, d__, u_, n_, p_, x_],
        optional: [e__, m_, a__, b__, c__, d__, p_],
        when: { freeq!([a__, b__, c__, d__, e__, m_, n_, p_], x_) && rubi_linear_q(&u_, x_) },
        rhs: {
            rubi_unintegrable(
                (&e__ * x_).pow(&m_) * (&a__ + &b__ * (&c__ + &d__ * u_.pow(&n_)).cosh()).pow(&p_),
                x_,
            )
        },
    ));
}

fn push_rules_rule_5891(rules: &mut Vec<RubiRule>) {
    rubi_symb!(e__, a__, b__, m_, p_, u_, x_);
    rules.push(rubi_rule!(
        order: 5891,
        source: "Int[(e_*x_)^m_.*(a_.+b_.*Sinh[u_])^p_.,x_Symbol] :=
          Int[(e*x)^m*(a+b*Sinh[ExpandToSum[u,x]])^p,x] /;
        FreeQ[{a,b,e,m,p},x] && BinomialQ[u,x] && Not[BinomialMatchQ[u,x]]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: (e__ * x_).pow(m_) * (a__ + b__ * Atom::var(u_).sinh()).pow(p_),
        with: [e__, m_, a__, b__, u_, p_, x_],
        optional: [m_, a__, b__, p_],
        when: {
            freeq!([a__, b__, e__, m_, p_], x_)
                && rubi_binomial_q(&u_, x_)
                && !rubi_binomial_match_q(&u_, x_)
        },
        rhs: {
            let expanded = rubi_expand_to_sum(&u_, x_);
            rubi_rhs_int(
                &((&e__ * x_).pow(&m_) * (&a__ + &b__ * expanded.sinh()).pow(&p_)),
                x_,
            )
        },
    ));
}

fn push_rules_rule_5892(rules: &mut Vec<RubiRule>) {
    rubi_symb!(e__, a__, b__, m_, p_, u_, x_);
    rules.push(rubi_rule!(
        order: 5892,
        source: "Int[(e_*x_)^m_.*(a_.+b_.*Cosh[u_])^p_.,x_Symbol] :=
          Int[(e*x)^m*(a+b*Cosh[ExpandToSum[u,x]])^p,x] /;
        FreeQ[{a,b,e,m,p},x] && BinomialQ[u,x] && Not[BinomialMatchQ[u,x]]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: (e__ * x_).pow(m_) * (a__ + b__ * Atom::var(u_).cosh()).pow(p_),
        with: [e__, m_, a__, b__, u_, p_, x_],
        optional: [m_, a__, b__, p_],
        when: {
            freeq!([a__, b__, e__, m_, p_], x_)
                && rubi_binomial_q(&u_, x_)
                && !rubi_binomial_match_q(&u_, x_)
        },
        rhs: {
            let expanded = rubi_expand_to_sum(&u_, x_);
            rubi_rhs_int(
                &((&e__ * x_).pow(&m_) * (&a__ + &b__ * expanded.cosh()).pow(&p_)),
                x_,
            )
        },
    ));
}

fn push_rules_rule_5893(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5893,
        source: "Int[x_^m_.*Sinh[a_.+b_.*x_^n_]^p_.*Cosh[a_.+b_.*x_^n_.],x_Symbol] :=
          Sinh[a+b*x^n]^(p+1)/(b*n*(p+1)) /;
        FreeQ[{a,b,m,n,p},x] && EqQ[m,n-1] && NeQ[p,-1]",
        desc: "Power rule for integration",
        refs: [],
        pattern:  rubi_shared_pattern_15(symbols),
        with: [m_, a__, b__, n_, p_, x_],
        optional: [m_, a__, b__, p_, n_],
        when: { freeq!([a__, b__, m_, n_, p_], x_) && eqq!(m_, &n_ - 1) && neq!(p_, -1) },
        rhs: {
            let angle = &a__ + &b__ * x_.pow(&n_);
            rubi_simp(&(angle.sinh().pow(&p_ + 1) / (&b__ * &n_ * (&p_ + 1))), x_)
        },
    ));
}

fn push_rules_rule_5894(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5894,
        source: "Int[x_^m_.*Cosh[a_.+b_.*x_^n_]^p_.*Sinh[a_.+b_.*x_^n_.],x_Symbol] :=
          Cosh[a+b*x^n]^(p+1)/(b*n*(p+1)) /;
        FreeQ[{a,b,m,n,p},x] && EqQ[m,n-1] && NeQ[p,-1]",
        desc: "Power rule for integration",
        refs: [],
        pattern:  rubi_shared_pattern_13(symbols),
        with: [m_, a__, b__, n_, p_, x_],
        optional: [m_, a__, b__, p_, n_],
        when: { freeq!([a__, b__, m_, n_, p_], x_) && eqq!(m_, &n_ - 1) && neq!(p_, -1) },
        rhs: {
            let angle = &a__ + &b__ * x_.pow(&n_);
            rubi_simp(&(angle.cosh().pow(&p_ + 1) / (&b__ * &n_ * (&p_ + 1))), x_)
        },
    ));
}

fn push_rules_rule_5895(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5895,
        source: "Int[x_^m_.*Sinh[a_.+b_.*x_^n_.]^p_.*Cosh[a_.+b_.*x_^n_.],x_Symbol] :=
          x^(m-n+1)*Sinh[a+b*x^n]^(p+1)/(b*n*(p+1)) -
          (m-n+1)/(b*n*(p+1)) \\[Star] Int[x^(m-n)*Sinh[a+b*x^n]^(p+1),x] /;
        FreeQ[{a,b,p},x] && LtQ[0,n,m+1] && NeQ[p,-1]",
        desc: "Integration by parts",
        refs: ["G&R 2.479.6", "G&R 2.479.3"],
        pattern:  rubi_shared_pattern_15(symbols),
        with: [m_, a__, b__, n_, p_, x_],
        optional: [m_, a__, b__, n_, p_],
        when: {
            freeq!([a__, b__, p_], x_) && ltq!(0, n_, &m_ + 1) && neq!(p_, -1)
        },
        rhs: {
            let angle = &a__ + &b__ * x_.pow(&n_);
            let degree = &m_ - &n_ + 1;
            rubi_simp(&(x_.pow(&degree) * &angle.sinh().pow(&p_ + 1) / (&b__ * &n_ * (&p_ + 1))), x_)
                    - rubi_star(&degree / (&b__ * &n_ * (&p_ + 1)), rubi_rhs_int(
                            &(x_.pow(&m_ - &n_) * angle.sinh().pow(&p_ + 1)),
                            x_,
                        ))
        },
    ));
}

fn push_rules_rule_5896(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5896,
        source: "Int[x_^m_.*Cosh[a_.+b_.*x_^n_.]^p_.*Sinh[a_.+b_.*x_^n_.],x_Symbol] :=
          x^(m-n+1)*Cosh[a+b*x^n]^(p+1)/(b*n*(p+1)) -
          (m-n+1)/(b*n*(p+1)) \\[Star] Int[x^(m-n)*Cosh[a+b*x^n]^(p+1),x] /;
        FreeQ[{a,b,p},x] && LtQ[0,n,m+1] && NeQ[p,-1]",
        desc: "Integration by parts",
        refs: ["G&R 2.479.6", "G&R 2.479.3"],
        pattern:  rubi_shared_pattern_13(symbols),
        with: [m_, a__, b__, n_, p_, x_],
        optional: [m_, a__, b__, n_, p_],
        when: {
            freeq!([a__, b__, p_], x_) && ltq!(0, n_, &m_ + 1) && neq!(p_, -1)
        },
        rhs: {
            let angle = &a__ + &b__ * x_.pow(&n_);
            let degree = &m_ - &n_ + 1;
            rubi_simp(&(x_.pow(&degree) * &angle.cosh().pow(&p_ + 1) / (&b__ * &n_ * (&p_ + 1))), x_)
                    - rubi_star(&degree / (&b__ * &n_ * (&p_ + 1)), rubi_rhs_int(
                            &(x_.pow(&m_ - &n_) * angle.cosh().pow(&p_ + 1)),
                            x_,
                        ))
        },
    ));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn downvalues_5821_through_5842_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .filter(|order| (5821..=5842).contains(order))
            .collect::<Vec<_>>();
        assert_eq!(orders, (5821..=5842).collect::<Vec<_>>());
    }

    #[test]
    fn downvalues_5843_through_5892_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .filter(|order| (5843..=5892).contains(order))
            .collect::<Vec<_>>();
        assert_eq!(orders, (5843..=5892).collect::<Vec<_>>());
    }

    #[test]
    fn downvalues_5893_through_5896_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .filter(|order| (5893..=5896).contains(order))
            .collect::<Vec<_>>();
        assert_eq!(orders, (5893..=5896).collect::<Vec<_>>());
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
    let u_ = symbols.u_;
    (a__ + b__ * (c__ + d__ * Atom::var(u_).pow(n_)).cosh()).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let u_ = symbols.u_;
    (a__ + b__ * (c__ + d__ * Atom::var(u_).pow(n_)).sinh()).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_2(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (a__ + b__ * (c__ + d__ * x_.pow(n_)).cosh()).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_3(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (a__ + b__ * (c__ + d__ * x_.pow(n_)).sinh()).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_4(symbols: &RubiSymbols) -> Atom {
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    (c__ + d__ * x_.pow(n_)).cosh()
}

#[inline(never)]
fn rubi_shared_pattern_5(symbols: &RubiSymbols) -> Atom {
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    (c__ + d__ * x_.pow(n_)).sinh()
}

#[inline(never)]
fn rubi_shared_pattern_6(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (e__ * x_).pow(m_) * (a__ + b__ * (c__ + d__ * x_.pow(n_)).cosh()).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_7(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (e__ * x_).pow(m_) * (a__ + b__ * (c__ + d__ * x_.pow(n_)).sinh()).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_8(symbols: &RubiSymbols) -> Atom {
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    (e__ * x_).pow(m_) * (c__ + d__ * x_.pow(n_)).cosh()
}

#[inline(never)]
fn rubi_shared_pattern_9(symbols: &RubiSymbols) -> Atom {
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    (e__ * x_).pow(m_) * (c__ + d__ * x_.pow(n_)).sinh()
}

#[inline(never)]
fn rubi_shared_pattern_10(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    x_.pow(m_) * (a__ + b__ * (c__ + d__ * x_.pow(n_)).cosh()).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_11(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    x_.pow(m_) * (a__ + b__ * (c__ + d__ * x_.pow(n_)).sinh()).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_12(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    x_.pow(m_) * (a__ + b__ * x_.pow(n_)).cosh().pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_13(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    x_.pow(m_) * (a__ + b__ * x_.pow(n_)).cosh().pow(p_) * (a__ + b__ * x_.pow(n_)).sinh()
}

#[inline(never)]
fn rubi_shared_pattern_14(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    x_.pow(m_) * (a__ + b__ * x_.pow(n_)).sinh().pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_15(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    x_.pow(m_) * (a__ + b__ * x_.pow(n_)).sinh().pow(p_) * (a__ + b__ * x_.pow(n_)).cosh()
}
