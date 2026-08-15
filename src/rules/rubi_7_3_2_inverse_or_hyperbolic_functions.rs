use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_6446(rules);
    push_rules_rule_6447(rules);
    push_rules_rule_6448(rules);
    push_rules_rule_6449(rules);
    push_rules_rule_6450(rules);
    push_rules_rule_6451(rules);
    push_rules_rule_6452(rules);
    push_rules_rule_6453(rules);
    push_rules_rule_6454(rules);
    push_rules_rule_6455(rules);
    push_rules_rule_6456(rules);
    push_rules_rule_6457(rules);
    push_rules_rule_6458(rules);
    push_rules_rule_6459(rules);
    push_rules_rule_6460(rules);
    push_rules_rule_6461(rules);
    push_rules_rule_6462(rules);
    push_rules_rule_6463(rules);
    push_rules_rule_6464(rules);
    push_rules_rule_6465(rules);
    push_rules_rule_6466(rules);
    push_rules_rule_6467(rules);
    push_rules_rule_6468(rules);
    push_rules_rule_6469(rules);
}

fn push_rules_rule_6446(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, x_);
    rules.push(rubi_rule!(
        order: 6446,
        source: "Int[(a_.+b_.*ArcTanh[c_.*x_])/x_,x_Symbol] :=
          a*Log[x] - b/2*PolyLog[2,-c*x] + b/2*PolyLog[2,c*x] /;
        FreeQ[{a,b,c},x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (a__ + b__ * (c__ * x_).atanh()) / x_,
        with: [a__, b__, c__, x_],
        optional: [a__, b__, c__],
        when: { freeq!([a__, b__, c__], x_) },
        rhs: {
            rubi_simp(&(a__ * x_.log()), x_) - rubi_simp(&(&b__ * (-&c__ * x_).polylog(2) / Atom::num(2)), x_)
                    + rubi_simp(&(b__ * (&c__ * x_).polylog(2) / Atom::num(2)), x_)
        },
    ));
}

fn push_rules_rule_6447(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, x_);
    rules.push(rubi_rule!(
        order: 6447,
        source: "Int[(a_.+b_.*ArcCoth[c_.*x_])/x_,x_Symbol] :=
          a*Log[x] + b/2*PolyLog[2,-1/(c*x)] - b/2*PolyLog[2,1/(c*x)] /;
        FreeQ[{a,b,c},x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (a__ + b__ * (c__ * x_).acoth()) / x_,
        with: [a__, b__, c__, x_],
        optional: [a__, b__, c__],
        when: { freeq!([a__, b__, c__], x_) },
        rhs: {
            rubi_simp(&(a__ * x_.log()), x_)
                    + rubi_simp(&(&b__ * (-Atom::num(1) / (&c__ * x_)).polylog(2) / Atom::num(2)), x_)
                    - rubi_simp(&(b__ * (Atom::num(1) / (&c__ * x_)).polylog(2) / Atom::num(2)), x_)
        },
    ));
}

fn push_rules_rule_6448(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, p_, x_);
    rules.push(rubi_rule!(
        order: 6448,
        source: "Int[(a_.+b_.*ArcTanh[c_.*x_])^p_/x_,x_Symbol] :=
          2*(a+b*ArcTanh[c*x])^p*ArcTanh[1-2/(1-c*x)] -
          2*b*c*p \\[Star] Int[(a+b*ArcTanh[c*x])^(p-1)*ArcTanh[1-2/(1-c*x)]/(1-c^2*x^2),x] /;
        FreeQ[{a,b,c},x] && IGtQ[p,1]",
        desc: "Integration by parts",
        refs: [],
        pattern: (a__ + b__ * (c__ * x_).atanh()).pow(p_) / x_,
        with: [a__, b__, c__, p_, x_],
        optional: [a__, b__, c__],
        when: { freeq!([a__, b__, c__], x_) && igtq!(p_, 1) },
        rhs: {
            let argument = &a__ + &b__ * (&c__ * x_).atanh();
            let auxiliary = (Atom::num(1) - Atom::num(2) / (Atom::num(1) - &c__ * x_)).atanh();
            let recursive = argument.pow(&p_ - Atom::num(1)) * &auxiliary
                / (Atom::num(1) - c__.pow(2) * x_.pow(2));
            let recursive_primitive = rubi_rhs_int(&recursive, x_);
            let recursive_term = rubi_simp(&(&(Atom::num(2) * &b__ * &c__ * &p_) * &recursive_primitive), x_);
            rubi_simp(&(Atom::num(2) * argument.pow(&p_) * auxiliary), x_)
                    - rubi_star(Atom::num(1), recursive_term)
        },
    ));
}

fn push_rules_rule_6449(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, p_, x_);
    rules.push(rubi_rule!(
        order: 6449,
        source: "Int[(a_.+b_.*ArcCoth[c_.*x_])^p_/x_,x_Symbol] :=
          2*(a+b*ArcCoth[c*x])^p*ArcCoth[1-2/(1-c*x)] -
          2*b*c*p \\[Star] Int[(a+b*ArcCoth[c*x])^(p-1)*ArcCoth[1-2/(1-c*x)]/(1-c^2*x^2),x] /;
        FreeQ[{a,b,c},x] && IGtQ[p,1]",
        desc: "Integration by parts",
        refs: [],
        pattern: (a__ + b__ * (c__ * x_).acoth()).pow(p_) / x_,
        with: [a__, b__, c__, p_, x_],
        optional: [a__, b__, c__],
        when: { freeq!([a__, b__, c__], x_) && igtq!(p_, 1) },
        rhs: {
            let argument = &a__ + &b__ * (&c__ * x_).acoth();
            let auxiliary = (Atom::num(1) - Atom::num(2) / (Atom::num(1) - &c__ * x_)).acoth();
            let recursive = argument.pow(&p_ - Atom::num(1)) * &auxiliary
                / (Atom::num(1) - c__.pow(2) * x_.pow(2));
            let recursive_primitive = rubi_rhs_int(&recursive, x_);
            let recursive_term = rubi_simp(&(&(Atom::num(2) * &b__ * &c__ * &p_) * &recursive_primitive), x_);
            rubi_simp(&(Atom::num(2) * argument.pow(&p_) * auxiliary), x_)
                    - rubi_star(Atom::num(1), recursive_term)
        },
    ));
}

fn push_rules_rule_6450(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6450,
        source: "Int[(a_.+b_.*ArcTanh[c_.*x_^n_])^p_./x_,x_Symbol] :=
          1/n \\[Star] Subst[Int[(a+b*ArcTanh[c*x])^p/x,x],x,x^n] /;
        FreeQ[{a,b,c,n},x] && IGtQ[p,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (a__ + b__ * (c__ * x_.pow(n_)).atanh()).pow(p_) / x_,
        with: [a__, b__, c__, n_, p_, x_],
        optional: [a__, b__, c__, p_],
        when: {
            freeq!([a__, b__, c__, n_], x_)
                && igtq!(p_, 0)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().rubi_rhs();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let payload = (&a__ + &b__ * (&c__ * &sub_atom).atanh()).pow(&p_) / &sub_atom;
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            let substituted = rubi_subst(&primitive, substitution_symbol, x_.pow(&n_));
            rubi_star(Atom::num(1) / &n_, substituted)
        },
    ));
}

fn push_rules_rule_6451(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6451,
        source: "Int[(a_.+b_.*ArcCoth[c_.*x_^n_])^p_./x_,x_Symbol] :=
          1/n \\[Star] Subst[Int[(a+b*ArcCoth[c*x])^p/x,x],x,x^n] /;
        FreeQ[{a,b,c,n},x] && IGtQ[p,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (a__ + b__ * (c__ * x_.pow(n_)).acoth()).pow(p_) / x_,
        with: [a__, b__, c__, n_, p_, x_],
        optional: [a__, b__, c__, p_],
        when: {
            freeq!([a__, b__, c__, n_], x_)
                && igtq!(p_, 0)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().rubi_rhs();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let payload = (&a__ + &b__ * (&c__ * &sub_atom).acoth()).pow(&p_) / &sub_atom;
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            let substituted = rubi_subst(&primitive, substitution_symbol, x_.pow(&n_));
            rubi_star(Atom::num(1) / &n_, substituted)
        },
    ));
}

fn push_rules_rule_6452(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6452,
        source: "Int[x_^m_.*(a_.+b_.*ArcTanh[c_.*x_^n_.])^p_.,x_Symbol] :=
          x^(m+1)*(a+b*ArcTanh[c*x^n])^p/(m+1) -
          b*c*n*p/(m+1) \\[Star] Int[x^(m+n)*(a+b*ArcTanh[c*x^n])^(p-1)/(1-c^2*x^(2*n)),x] /;
        FreeQ[{a,b,c,m,n},x] && IGtQ[p,0] && (EqQ[p,1] || EqQ[n,1] && IntegerQ[m])  && NeQ[m,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [m_, a__, b__, c__, n_, p_, x_],
        optional: [a__, b__, c__, n_, p_, m_],
        when: {
            freeq!([a__, b__, c__, m_, n_], x_)
                && igtq!(p_, 0)
                && (eqq!(p_, 1) || eqq!(n_, 1) && integerq!(m_))
                && neq!(m_, -1)
        },
        rhs: {
            let argument = &a__ + &b__ * (&c__ * x_.pow(&n_)).atanh();
            let recursive = x_.pow(&m_ + &n_) * argument.pow(&p_ - Atom::num(1))
                / (Atom::num(1) - c__.pow(2) * x_.pow(Atom::num(2) * &n_));
            let recursive_primitive = rubi_rhs_int(&recursive, x_);
            let recursive_term = rubi_simp(&(&(&b__ * &c__ * &n_ * &p_ / (&m_ + Atom::num(1))) * &recursive_primitive), x_);
            rubi_simp(&(x_.pow(&m_ + Atom::num(1)) * argument.pow(&p_) / (&m_ + Atom::num(1))), x_)
                    - rubi_star(Atom::num(1), recursive_term)
        },
    ));
}

fn push_rules_rule_6453(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6453,
        source: "Int[x_^m_.*(a_.+b_.*ArcCoth[c_.*x_^n_.])^p_.,x_Symbol] :=
          x^(m+1)*(a+b*ArcCoth[c*x^n])^p/(m+1) -
          b*c*n*p/(m+1) \\[Star] Int[x^(m+n)*(a+b*ArcCoth[c*x^n])^(p-1)/(1-c^2*x^(2*n)),x] /;
        FreeQ[{a,b,c,m,n},x] && IGtQ[p,0] && (EqQ[p,1] || EqQ[n,1] && IntegerQ[m])  && NeQ[m,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [m_, a__, b__, c__, n_, p_, x_],
        optional: [a__, b__, c__, n_, p_, m_],
        when: {
            freeq!([a__, b__, c__, m_, n_], x_)
                && igtq!(p_, 0)
                && (eqq!(p_, 1) || eqq!(n_, 1) && integerq!(m_))
                && neq!(m_, -1)
        },
        rhs: {
            let argument = &a__ + &b__ * (&c__ * x_.pow(&n_)).acoth();
            let recursive = x_.pow(&m_ + &n_) * argument.pow(&p_ - Atom::num(1))
                / (Atom::num(1) - c__.pow(2) * x_.pow(Atom::num(2) * &n_));
            let recursive_primitive = rubi_rhs_int(&recursive, x_);
            let recursive_term = rubi_simp(&(&(&b__ * &c__ * &n_ * &p_ / (&m_ + Atom::num(1))) * &recursive_primitive), x_);
            rubi_simp(&(x_.pow(&m_ + Atom::num(1)) * argument.pow(&p_) / (&m_ + Atom::num(1))), x_)
                    - rubi_star(Atom::num(1), recursive_term)
        },
    ));
}

fn push_rules_rule_6454(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6454,
        source: "Int[x_^m_.*(a_.+b_.*ArcTanh[c_.*x_^n_])^p_.,x_Symbol] :=
          1/n \\[Star] Subst[Int[x^(Simplify[(m+1)/n]-1)*(a+b*ArcTanh[c*x])^p,x],x,x^n] /;
        FreeQ[{a,b,c,m,n},x] && IGtQ[p,1] && IntegerQ[Simplify[(m+1)/n]]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [m_, a__, b__, c__, n_, p_, x_],
        optional: [a__, b__, c__, p_, m_],
        when: {
            freeq!([a__, b__, c__, m_, n_], x_)
                && igtq!(p_, 1)
                && integerq!(rubi_simplify(&((&m_ + Atom::num(1)) / &n_)))
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().rubi_rhs();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let exponent = rubi_simplify(&((&m_ + Atom::num(1)) / &n_)) - Atom::num(1);
            let payload = sub_atom.pow(exponent) * (&a__ + &b__ * (&c__ * &sub_atom).atanh()).pow(&p_);
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            let substituted = rubi_subst(&primitive, substitution_symbol, x_.pow(&n_));
            rubi_star(Atom::num(1) / &n_, substituted)
        },
    ));
}

fn push_rules_rule_6455(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6455,
        source: "Int[x_^m_.*(a_.+b_.*ArcCoth[c_.*x_^n_])^p_.,x_Symbol] :=
          1/n \\[Star] Subst[Int[x^(Simplify[(m+1)/n]-1)*(a+b*ArcCoth[c*x])^p,x],x,x^n] /;
        FreeQ[{a,b,c,m,n},x] && IGtQ[p,1] && IntegerQ[Simplify[(m+1)/n]]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [m_, a__, b__, c__, n_, p_, x_],
        optional: [a__, b__, c__, p_, m_],
        when: {
            freeq!([a__, b__, c__, m_, n_], x_)
                && igtq!(p_, 1)
                && integerq!(rubi_simplify(&((&m_ + Atom::num(1)) / &n_)))
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().rubi_rhs();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let exponent = rubi_simplify(&((&m_ + Atom::num(1)) / &n_)) - Atom::num(1);
            let payload = sub_atom.pow(exponent) * (&a__ + &b__ * (&c__ * &sub_atom).acoth()).pow(&p_);
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            let substituted = rubi_subst(&primitive, substitution_symbol, x_.pow(&n_));
            rubi_star(Atom::num(1) / &n_, substituted)
        },
    ));
}

fn push_rules_rule_6456(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6456,
        source: "Int[x_^m_.*(a_.+b_.*ArcTanh[c_.*x_^n_])^p_,x_Symbol] :=
          Int[ExpandIntegrand[x^m*(a+b*Log[1+c*x^n]/2-b*Log[1-c*x^n]/2)^p,x],x] /;
        FreeQ[{a,b,c},x] && IGtQ[p,1] && IGtQ[n,0] && IntegerQ[m]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [m_, a__, b__, c__, n_, p_, x_],
        optional: [a__, b__, c__, m_],
        when: {
            freeq!([a__, b__, c__], x_)
                && igtq!(p_, 1)
                && igtq!(n_, 0)
                && integerq!(m_)
        },
        rhs: {
            let payload = x_.pow(&m_)
                * (&a__ + &b__ * (Atom::num(1) + &c__ * x_.pow(&n_)).log() / Atom::num(2)
                    - &b__ * (Atom::num(1) - &c__ * x_.pow(&n_)).log() / Atom::num(2))
                    .pow(&p_);
            let expanded = rubi_expand_integrand(&payload, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_6457(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6457,
        source: "Int[x_^m_.*(a_.+b_.*ArcCoth[c_.*x_^n_])^p_,x_Symbol] :=
          Int[ExpandIntegrand[x^m*(a+b*Log[1+x^(-n)/c]/2-b*Log[1-x^(-n)/c]/2)^p,x],x] /;
        FreeQ[{a,b,c},x] && IGtQ[p,1] && IGtQ[n,0] && IntegerQ[m]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [m_, a__, b__, c__, n_, p_, x_],
        optional: [a__, b__, c__, m_],
        when: {
            freeq!([a__, b__, c__], x_)
                && igtq!(p_, 1)
                && igtq!(n_, 0)
                && integerq!(m_)
        },
        rhs: {
            let reciprocal_power = x_.pow(-&n_) / &c__;
            let payload = x_.pow(&m_)
                * (&a__ + &b__ * (Atom::num(1) + &reciprocal_power).log() / Atom::num(2)
                    - &b__ * (Atom::num(1) - reciprocal_power).log() / Atom::num(2))
                    .pow(&p_);
            let expanded = rubi_expand_integrand(&payload, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_6458(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6458,
        source: "Int[x_^m_.*(a_.+b_.*ArcTanh[c_.*x_^n_])^p_,x_Symbol] :=
          With[{k=Denominator[m]},
          k \\[Star] Subst[Int[x^(k*(m+1)-1)*(a+b*ArcTanh[c*x^(k*n)])^p,x],x,x^(1/k)]] /;
        FreeQ[{a,b,c},x] && IGtQ[p,1] && IGtQ[n,0] && FractionQ[m]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [m_, a__, b__, c__, n_, p_, x_],
        optional: [a__, b__, c__, m_],
        when: {
            freeq!([a__, b__, c__], x_)
                && igtq!(p_, 1)
                && igtq!(n_, 0)
                && fractionq!(m_)
        },
        rhs: {
            let k_i = rubi_denominator(&m_).rubi_rhs();
            let k = Atom::num(k_i);
            let substitution_guard = fresh_substitution_symbol().rubi_rhs();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let payload = sub_atom.pow(&k * (&m_ + Atom::num(1)) - Atom::num(1))
                * (&a__ + &b__ * (&c__ * sub_atom.pow(&k * &n_)).atanh()).pow(&p_);
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            let substituted = rubi_subst(
                &primitive,
                substitution_symbol,
                x_.pow(Atom::num(1) / k_i),
            );
            rubi_star(k, substituted)
        },
    ));
}

fn push_rules_rule_6459(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6459,
        source: "Int[x_^m_.*(a_.+b_.*ArcCoth[c_.*x_^n_])^p_,x_Symbol] :=
          With[{k=Denominator[m]},
          k \\[Star] Subst[Int[x^(k*(m+1)-1)*(a+b*ArcCoth[c*x^(k*n)])^p,x],x,x^(1/k)]] /;
        FreeQ[{a,b,c},x] && IGtQ[p,1] && IGtQ[n,0] && FractionQ[m]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [m_, a__, b__, c__, n_, p_, x_],
        optional: [a__, b__, c__, m_],
        when: {
            freeq!([a__, b__, c__], x_)
                && igtq!(p_, 1)
                && igtq!(n_, 0)
                && fractionq!(m_)
        },
        rhs: {
            let k_i = rubi_denominator(&m_).rubi_rhs();
            let k = Atom::num(k_i);
            let substitution_guard = fresh_substitution_symbol().rubi_rhs();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let payload = sub_atom.pow(&k * (&m_ + Atom::num(1)) - Atom::num(1))
                * (&a__ + &b__ * (&c__ * sub_atom.pow(&k * &n_)).acoth()).pow(&p_);
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            let substituted = rubi_subst(
                &primitive,
                substitution_symbol,
                x_.pow(Atom::num(1) / k_i),
            );
            rubi_star(k, substituted)
        },
    ));
}

fn push_rules_rule_6460(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6460,
        source: "Int[x_^m_.*(a_.+b_.*ArcTanh[c_.*x_^n_])^p_,x_Symbol] :=
          Int[x^m*(a+b*ArcCoth[x^(-n)/c])^p,x] /;
        FreeQ[{a,b,c,m},x] && IGtQ[p,1] && ILtQ[n,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [m_, a__, b__, c__, n_, p_, x_],
        optional: [a__, b__, c__, m_],
        when: {
            freeq!([a__, b__, c__, m_], x_)
                && igtq!(p_, 1)
                && iltq!(n_, 0)
        },
        rhs: {
            let transformed = x_.pow(&m_) * (&a__ + &b__ * (x_.pow(-&n_) / &c__).acoth()).pow(&p_);
            rubi_rhs_int(&transformed, x_)
        },
    ));
}

fn push_rules_rule_6461(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6461,
        source: "Int[x_^m_.*(a_.+b_.*ArcCoth[c_.*x_^n_])^p_,x_Symbol] :=
          Int[x^m*(a+b*ArcTanh[x^(-n)/c])^p,x] /;
        FreeQ[{a,b,c,m},x] && IGtQ[p,1] && ILtQ[n,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [m_, a__, b__, c__, n_, p_, x_],
        optional: [a__, b__, c__, m_],
        when: {
            freeq!([a__, b__, c__, m_], x_)
                && igtq!(p_, 1)
                && iltq!(n_, 0)
        },
        rhs: {
            let transformed = x_.pow(&m_) * (&a__ + &b__ * (x_.pow(-&n_) / &c__).atanh()).pow(&p_);
            rubi_rhs_int(&transformed, x_)
        },
    ));
}

fn push_rules_rule_6462(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6462,
        source: "Int[x_^m_.*(a_.+b_.*ArcTanh[c_.*x_^n_])^p_,x_Symbol] :=
          With[{k=Denominator[n]},
          k \\[Star] Subst[Int[x^(k*(m+1)-1)*(a+b*ArcTanh[c*x^(k*n)])^p,x],x,x^(1/k)]] /;
        FreeQ[{a,b,c,m},x] && IGtQ[p,1] && FractionQ[n]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [m_, a__, b__, c__, n_, p_, x_],
        optional: [a__, b__, c__, m_],
        when: {
            freeq!([a__, b__, c__, m_], x_)
                && igtq!(p_, 1)
                && fractionq!(n_)
        },
        rhs: {
            let k_i = rubi_denominator(&n_).rubi_rhs();
            let k = Atom::num(k_i);
            let substitution_guard = fresh_substitution_symbol().rubi_rhs();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let payload = sub_atom.pow(&k * (&m_ + Atom::num(1)) - Atom::num(1))
                * (&a__ + &b__ * (&c__ * sub_atom.pow(&k * &n_)).atanh()).pow(&p_);
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            let substituted = rubi_subst(
                &primitive,
                substitution_symbol,
                x_.pow(Atom::num(1) / k_i),
            );
            rubi_star(k, substituted)
        },
    ));
}

fn push_rules_rule_6463(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6463,
        source: "Int[x_^m_.*(a_.+b_.*ArcCoth[c_.*x_^n_])^p_,x_Symbol] :=
          With[{k=Denominator[n]},
          k \\[Star] Subst[Int[x^(k*(m+1)-1)*(a+b*ArcCoth[c*x^(k*n)])^p,x],x,x^(1/k)]] /;
        FreeQ[{a,b,c,m},x] && IGtQ[p,1] && FractionQ[n]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [m_, a__, b__, c__, n_, p_, x_],
        optional: [a__, b__, c__, m_],
        when: {
            freeq!([a__, b__, c__, m_], x_)
                && igtq!(p_, 1)
                && fractionq!(n_)
        },
        rhs: {
            let k_i = rubi_denominator(&n_).rubi_rhs();
            let k = Atom::num(k_i);
            let substitution_guard = fresh_substitution_symbol().rubi_rhs();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let payload = sub_atom.pow(&k * (&m_ + Atom::num(1)) - Atom::num(1))
                * (&a__ + &b__ * (&c__ * sub_atom.pow(&k * &n_)).acoth()).pow(&p_);
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            let substituted = rubi_subst(
                &primitive,
                substitution_symbol,
                x_.pow(Atom::num(1) / k_i),
            );
            rubi_star(k, substituted)
        },
    ));
}

fn push_rules_rule_6464(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 6464,
        source: "Int[(d_*x_)^m_*(a_.+b_.*ArcTanh[c_.*x_^n_.]),x_Symbol] :=
          (d*x)^(m+1)*(a+b*ArcTanh[c*x^n])/(d*(m+1)) -
          b*c*n/(d^n*(m+1)) \\[Star] Int[(d*x)^(m+n)/(1-c^2*x^(2*n)),x] /;
        FreeQ[{a,b,c,d,m,n},x] && IntegerQ[n] && NeQ[m,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern: (d__ * x_).pow(m_) * (a__ + b__ * (c__ * x_.pow(n_)).atanh()),
        with: [d__, m_, a__, b__, c__, n_, x_],
        optional: [a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, m_, n_], x_)
                && integerq!(n_)
                && neq!(m_, -1)
        },
        rhs: {
            let scaled = &d__ * x_;
            let argument = &a__ + &b__ * (&c__ * x_.pow(&n_)).atanh();
            let recursive = scaled.pow(&m_ + &n_) / (Atom::num(1) - c__.pow(2) * x_.pow(Atom::num(2) * &n_));
            let recursive_primitive = rubi_rhs_int(&recursive, x_);
            let recursive_term = rubi_simp(&(&(&b__ * &c__ * &n_ / (d__.pow(&n_) * (&m_ + Atom::num(1)))) * &recursive_primitive), x_);
            rubi_simp(&(scaled.pow(&m_ + Atom::num(1)) * argument / (&d__ * (&m_ + Atom::num(1)))), x_)
                    - rubi_star(Atom::num(1), recursive_term)
        },
    ));
}

fn push_rules_rule_6465(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 6465,
        source: "Int[(d_*x_)^m_*(a_.+b_.*ArcCoth[c_.*x_^n_.]),x_Symbol] :=
          (d*x)^(m+1)*(a+b*ArcCoth[c*x^n])/(d*(m+1)) -
          b*c*n/(d^n*(m+1)) \\[Star] Int[(d*x)^(m+n)/(1-c^2*x^(2*n)),x] /;
        FreeQ[{a,b,c,d,m,n},x] && IntegerQ[n] && NeQ[m,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern: (d__ * x_).pow(m_) * (a__ + b__ * (c__ * x_.pow(n_)).acoth()),
        with: [d__, m_, a__, b__, c__, n_, x_],
        optional: [a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, m_, n_], x_)
                && integerq!(n_)
                && neq!(m_, -1)
        },
        rhs: {
            let scaled = &d__ * x_;
            let argument = &a__ + &b__ * (&c__ * x_.pow(&n_)).acoth();
            let recursive = scaled.pow(&m_ + &n_) / (Atom::num(1) - c__.pow(2) * x_.pow(Atom::num(2) * &n_));
            let recursive_primitive = rubi_rhs_int(&recursive, x_);
            let recursive_term = rubi_simp(&(&(&b__ * &c__ * &n_ / (d__.pow(&n_) * (&m_ + Atom::num(1)))) * &recursive_primitive), x_);
            rubi_simp(&(scaled.pow(&m_ + Atom::num(1)) * argument / (&d__ * (&m_ + Atom::num(1)))), x_)
                    - rubi_star(Atom::num(1), recursive_term)
        },
    ));
}

fn push_rules_rule_6466(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d_, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6466,
        source: "Int[(d_*x_)^m_*(a_.+b_.*ArcTanh[c_.*x_^n_.])^p_.,x_Symbol] :=
          d^IntPart[m]*(d*x)^FracPart[m]/x^FracPart[m] \\[Star] Int[x^m*(a+b*ArcTanh[c*x^n])^p,x] /;
        FreeQ[{a,b,c,d,m,n},x] && IGtQ[p,0] && (EqQ[p,1] || RationalQ[m,n])",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: (d_ * x_).pow(m_) * (a__ + b__ * (c__ * x_.pow(n_)).atanh()).pow(p_),
        with: [d_, m_, a__, b__, c__, n_, p_, x_],
        optional: [a__, b__, c__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d_, m_, n_], x_)
                && igtq!(p_, 0)
                && (eqq!(p_, 1) || rationalq!([m_, n_]))
        },
        rhs: {
            let argument = &a__ + &b__ * (&c__ * x_.pow(&n_)).atanh();
            let recursive = x_.pow(&m_) * argument.pow(&p_);
            let prefactor = d_.pow(rubi_int_part(&m_))
                * (&d_ * x_).pow(rubi_frac_part(&m_))
                / x_.pow(rubi_frac_part(&m_));
            let recursive_primitive = rubi_rhs_int(&recursive, x_);
            rubi_star(prefactor, recursive_primitive)
        },
    ));
}

fn push_rules_rule_6467(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d_, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6467,
        source: "Int[(d_*x_)^m_*(a_.+b_.*ArcCoth[c_.*x_^n_.])^p_.,x_Symbol] :=
          d^IntPart[m]*(d*x)^FracPart[m]/x^FracPart[m] \\[Star] Int[x^m*(a+b*ArcCoth[c*x^n])^p,x] /;
        FreeQ[{a,b,c,d,m,n},x] && IGtQ[p,0] && (EqQ[p,1] || RationalQ[m,n])",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: (d_ * x_).pow(m_) * (a__ + b__ * (c__ * x_.pow(n_)).acoth()).pow(p_),
        with: [d_, m_, a__, b__, c__, n_, p_, x_],
        optional: [a__, b__, c__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d_, m_, n_], x_)
                && igtq!(p_, 0)
                && (eqq!(p_, 1) || rationalq!([m_, n_]))
        },
        rhs: {
            let argument = &a__ + &b__ * (&c__ * x_.pow(&n_)).acoth();
            let recursive = x_.pow(&m_) * argument.pow(&p_);
            let prefactor = d_.pow(rubi_int_part(&m_))
                * (&d_ * x_).pow(rubi_frac_part(&m_))
                / x_.pow(rubi_frac_part(&m_));
            let recursive_primitive = rubi_rhs_int(&recursive, x_);
            rubi_star(prefactor, recursive_primitive)
        },
    ));
}

fn push_rules_rule_6468(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6468,
        source: "Int[(d_.*x_)^m_.*(a_.+b_.*ArcTanh[c_.*x_^n_.])^p_.,x_Symbol] :=
          Unintegrable[(d*x)^m*(a+b*ArcTanh[c*x^n])^p,x] /;
        FreeQ[{a,b,c,d,m,n,p},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern: (d__ * x_).pow(m_) * (a__ + b__ * (c__ * x_.pow(n_)).atanh()).pow(p_),
        with: [d__, m_, a__, b__, c__, n_, p_, x_],
        optional: [d__, m_, a__, b__, c__, n_, p_],
        when: { freeq!([a__, b__, c__, d__, m_, n_, p_], x_) },
        rhs: {
            let integrand = (&d__ * x_).pow(&m_) * (&a__ + &b__ * (&c__ * x_.pow(&n_)).atanh()).pow(&p_);
            rubi_unintegrable(integrand, x_)
        },
    ));
}

fn push_rules_rule_6469(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6469,
        source: "Int[(d_.*x_)^m_.*(a_.+b_.*ArcCoth[c_.*x_^n_.])^p_.,x_Symbol] :=
          Unintegrable[(d*x)^m*(a+b*ArcCoth[c*x^n])^p,x] /;
        FreeQ[{a,b,c,d,m,n,p},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern: (d__ * x_).pow(m_) * (a__ + b__ * (c__ * x_.pow(n_)).acoth()).pow(p_),
        with: [d__, m_, a__, b__, c__, n_, p_, x_],
        optional: [d__, m_, a__, b__, c__, n_, p_],
        when: { freeq!([a__, b__, c__, d__, m_, n_, p_], x_) },
        rhs: {
            let integrand = (&d__ * x_).pow(&m_) * (&a__ + &b__ * (&c__ * x_.pow(&n_)).acoth()).pow(&p_);
            rubi_unintegrable(integrand, x_)
        },
    ));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn downvalues_6446_through_6469_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .filter(|order| (6446..=6469).contains(order))
            .collect::<Vec<_>>();
        assert_eq!(orders, (6446..=6469).collect::<Vec<_>>());
    }
}

// Generated shared pattern builders.

#[inline(never)]
fn rubi_shared_pattern_0(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    x_.pow(m_) * (a__ + b__ * (c__ * x_.pow(n_)).acoth()).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    x_.pow(m_) * (a__ + b__ * (c__ * x_.pow(n_)).atanh()).pow(p_)
}
