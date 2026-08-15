use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_5355(rules);
    push_rules_rule_5356(rules);
    push_rules_rule_5357(rules);
    push_rules_rule_5358(rules);
    push_rules_rule_5359(rules);
    push_rules_rule_5360(rules);
    push_rules_rule_5361(rules);
    push_rules_rule_5362(rules);
    push_rules_rule_5363(rules);
    push_rules_rule_5364(rules);
    push_rules_rule_5365(rules);
    push_rules_rule_5366(rules);
    push_rules_rule_5367(rules);
    push_rules_rule_5368(rules);
    push_rules_rule_5369(rules);
    push_rules_rule_5370(rules);
    push_rules_rule_5371(rules);
    push_rules_rule_5372(rules);
    push_rules_rule_5373(rules);
    push_rules_rule_5374(rules);
    push_rules_rule_5375(rules);
    push_rules_rule_5376(rules);
    push_rules_rule_5377(rules);
    push_rules_rule_5378(rules);
}

fn push_rules_rule_5355(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, x_);
    rules.push(rubi_rule!(
        order: 5355,
        source: "Int[(a_.+b_.*ArcTan[c_.*x_])/x_,x_Symbol] :=
          a*Log[x] + I*b/2 \\[Star] Int[Log[1-I*c*x]/x,x] - I*b/2 \\[Star] Int[Log[1+I*c*x]/x,x] /;
        FreeQ[{a,b,c},x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (a__ + b__ * (c__ * x_).atan()) / x_,
        with: [a__, b__, c__, x_],
        optional: [a__, b__, c__],
        when: { freeq!([a__, b__, c__], x_) },
        rhs: {
            let i = Atom::i();
            let recursive_1 = (Atom::num(1) - &i * &c__ * x_).log() / x_;
            let recursive_2 = (Atom::num(1) + &i * &c__ * x_).log() / x_;
            rubi_simp(&(a__ * x_.log()), x_)
                    + rubi_star(&i * &b__ / Atom::num(2), rubi_rhs_int(&recursive_1, x_))
                    - rubi_star(i * b__ / Atom::num(2), rubi_rhs_int(&recursive_2, x_))
        },
    ));
}

fn push_rules_rule_5356(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, x_);
    rules.push(rubi_rule!(
        order: 5356,
        source: "Int[(a_.+b_.*ArcCot[c_.*x_])/x_,x_Symbol] :=
          a*Log[x] + I*b/2 \\[Star] Int[Log[1-I/(c*x)]/x,x] - I*b/2 \\[Star] Int[Log[1+I/(c*x)]/x,x] /;
        FreeQ[{a,b,c},x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (a__ + b__ * (c__ * x_).acot()) / x_,
        with: [a__, b__, c__, x_],
        optional: [a__, b__, c__],
        when: { freeq!([a__, b__, c__], x_) },
        rhs: {
            let i = Atom::i();
            let recursive_1 = (Atom::num(1) - &i / (&c__ * x_)).log() / x_;
            let recursive_2 = (Atom::num(1) + &i / (&c__ * x_)).log() / x_;
            rubi_simp(&(a__ * x_.log()), x_)
                    + rubi_star(&i * &b__ / Atom::num(2), rubi_rhs_int(&recursive_1, x_))
                    - rubi_star(i * b__ / Atom::num(2), rubi_rhs_int(&recursive_2, x_))
        },
    ));
}

fn push_rules_rule_5357(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, p_, x_);
    rules.push(rubi_rule!(
        order: 5357,
        source: "Int[(a_.+b_.*ArcTan[c_.*x_])^p_/x_,x_Symbol] :=
          2*(a+b*ArcTan[c*x])^p*ArcTanh[1-2/(1+I*c*x)] -
          2*b*c*p \\[Star] Int[(a+b*ArcTan[c*x])^(p-1)*ArcTanh[1-2/(1+I*c*x)]/(1+c^2*x^2),x] /;
        FreeQ[{a,b,c},x] && IGtQ[p,1]",
        desc: "Integration by parts",
        refs: [],
        pattern: (a__ + b__ * (c__ * x_).atan()).pow(p_) / x_,
        with: [a__, b__, c__, p_, x_],
        optional: [a__, b__, c__],
        when: { freeq!([a__, b__, c__], x_) && igtq!(p_, 1) },
        rhs: {
            let i = Atom::i();
            let argument = &a__ + &b__ * (&c__ * x_).atan();
            let auxiliary = (Atom::num(1) - Atom::num(2) / (Atom::num(1) + &i * &c__ * x_)).atanh();
            let recursive = argument.pow(&p_ - Atom::num(1)) * &auxiliary
                / (Atom::num(1) + c__.pow(2) * x_.pow(2));
            rubi_simp(&(Atom::num(2) * argument.pow(&p_) * auxiliary), x_)
                    - rubi_star(Atom::num(2) * &b__ * &c__ * &p_, rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_5358(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, p_, x_);
    rules.push(rubi_rule!(
        order: 5358,
        source: "Int[(a_.+b_.*ArcCot[c_.*x_])^p_/x_,x_Symbol] :=
          2*(a+b*ArcCot[c*x])^p*ArcCoth[1-2/(1+I*c*x)] +
          2*b*c*p \\[Star] Int[(a+b*ArcCot[c*x])^(p-1)*ArcCoth[1-2/(1+I*c*x)]/(1+c^2*x^2),x] /;
        FreeQ[{a,b,c},x] && IGtQ[p,1]",
        desc: "Integration by parts",
        refs: [],
        pattern: (a__ + b__ * (c__ * x_).acot()).pow(p_) / x_,
        with: [a__, b__, c__, p_, x_],
        optional: [a__, b__, c__],
        when: { freeq!([a__, b__, c__], x_) && igtq!(p_, 1) },
        rhs: {
            let i = Atom::i();
            let argument = &a__ + &b__ * (&c__ * x_).acot();
            let auxiliary = (Atom::num(1) - Atom::num(2) / (Atom::num(1) + &i * &c__ * x_)).acoth();
            let recursive = argument.pow(&p_ - Atom::num(1)) * &auxiliary
                / (Atom::num(1) + c__.pow(2) * x_.pow(2));
            rubi_simp(&(Atom::num(2) * argument.pow(&p_) * auxiliary), x_)
                    + rubi_star(Atom::num(2) * &b__ * &c__ * &p_, rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_5359(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5359,
        source: "Int[(a_.+b_.*ArcTan[c_.*x_^n_])^p_./x_,x_Symbol] :=
          1/n \\[Star] Subst[Int[(a+b*ArcTan[c*x])^p/x,x],x,x^n] /;
        FreeQ[{a,b,c,n},x] && IGtQ[p,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (a__ + b__ * (c__ * x_.pow(n_)).atan()).pow(p_) / x_,
        with: [a__, b__, c__, n_, p_, x_],
        optional: [a__, b__, c__, p_],
        when: {
            freeq!([a__, b__, c__, n_], x_)
                && igtq!(p_, 0)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let payload = (&a__ + &b__ * (&c__ * &sub_atom).atan()).pow(&p_) / &sub_atom;
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            rubi_star(Atom::num(1) / &n_, rubi_subst(&primitive, substitution_symbol, x_.pow(&n_)))
        },
    ));
}

fn push_rules_rule_5360(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5360,
        source: "Int[(a_.+b_.*ArcCot[c_.*x_^n_])^p_./x_,x_Symbol] :=
          1/n \\[Star] Subst[Int[(a+b*ArcCot[c*x])^p/x,x],x,x^n] /;
        FreeQ[{a,b,c,n},x] && IGtQ[p,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (a__ + b__ * (c__ * x_.pow(n_)).acot()).pow(p_) / x_,
        with: [a__, b__, c__, n_, p_, x_],
        optional: [a__, b__, c__, p_],
        when: {
            freeq!([a__, b__, c__, n_], x_)
                && igtq!(p_, 0)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let payload = (&a__ + &b__ * (&c__ * &sub_atom).acot()).pow(&p_) / &sub_atom;
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            rubi_star(Atom::num(1) / &n_, rubi_subst(&primitive, substitution_symbol, x_.pow(&n_)))
        },
    ));
}

fn push_rules_rule_5361(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5361,
        source: "Int[x_^m_.*(a_.+b_.*ArcTan[c_.*x_^n_.])^p_.,x_Symbol] :=
          x^(m+1)*(a+b*ArcTan[c*x^n])^p/(m+1) -
          b*c*n*p/(m+1) \\[Star] Int[x^(m+n)*(a+b*ArcTan[c*x^n])^(p-1)/(1+c^2*x^(2*n)),x] /;
        FreeQ[{a,b,c,m,n},x] && IGtQ[p,0] && (EqQ[p,1] || EqQ[n,1] && IntegerQ[m])  && NeQ[m,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [m_, a__, b__, c__, n_, p_, x_],
        optional: [m_, a__, b__, c__, n_, p_],
        when: {
            freeq!([a__, b__, c__, m_, n_], x_)
                && igtq!(p_, 0)
                && (eqq!(p_, 1) || eqq!(n_, 1) && integerq!(m_))
                && neq!(m_, -1)
        },
        rhs: {
            let argument = &a__ + &b__ * (&c__ * x_.pow(&n_)).atan();
            let recursive = x_.pow(&m_ + &n_) * argument.pow(&p_ - Atom::num(1))
                / (Atom::num(1) + c__.pow(2) * x_.pow(Atom::num(2) * &n_));
            rubi_simp(&(x_.pow(&m_ + Atom::num(1)) * argument.pow(&p_) / (&m_ + Atom::num(1))), x_)
                    - rubi_star(&b__ * &c__ * &n_ * &p_ / (&m_ + Atom::num(1)), rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_5362(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5362,
        source: "Int[x_^m_.*(a_.+b_.*ArcCot[c_.*x_^n_.])^p_.,x_Symbol] :=
          x^(m+1)*(a+b*ArcCot[c*x^n])^p/(m+1) +
          b*c*n*p/(m+1) \\[Star] Int[x^(m+n)*(a+b*ArcCot[c*x^n])^(p-1)/(1+c^2*x^(2*n)),x] /;
        FreeQ[{a,b,c,m,n},x] && IGtQ[p,0] && (EqQ[p,1] || EqQ[n,1] && IntegerQ[m])  && NeQ[m,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [m_, a__, b__, c__, n_, p_, x_],
        optional: [m_, a__, b__, c__, n_, p_],
        when: {
            freeq!([a__, b__, c__, m_, n_], x_)
                && igtq!(p_, 0)
                && (eqq!(p_, 1) || eqq!(n_, 1) && integerq!(m_))
                && neq!(m_, -1)
        },
        rhs: {
            let argument = &a__ + &b__ * (&c__ * x_.pow(&n_)).acot();
            let recursive = x_.pow(&m_ + &n_) * argument.pow(&p_ - Atom::num(1))
                / (Atom::num(1) + c__.pow(2) * x_.pow(Atom::num(2) * &n_));
            rubi_simp(&(x_.pow(&m_ + Atom::num(1)) * argument.pow(&p_) / (&m_ + Atom::num(1))), x_)
                    + rubi_star(&b__ * &c__ * &n_ * &p_ / (&m_ + Atom::num(1)), rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_5363(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5363,
        source: "Int[x_^m_.*(a_.+b_.*ArcTan[c_.*x_^n_])^p_.,x_Symbol] :=
          1/n \\[Star] Subst[Int[x^(Simplify[(m+1)/n]-1)*(a+b*ArcTan[c*x])^p,x],x,x^n] /;
        FreeQ[{a,b,c,m,n},x] && IGtQ[p,1] && IntegerQ[Simplify[(m+1)/n]]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [m_, a__, b__, c__, n_, p_, x_],
        optional: [m_, a__, b__, c__, p_],
        when: {
            freeq!([a__, b__, c__, m_, n_], x_)
                && igtq!(p_, 1)
                && integerq!(rubi_simplify(&((&m_ + Atom::num(1)) / &n_)))
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let exponent = rubi_simplify(&((&m_ + Atom::num(1)) / &n_)) - Atom::num(1);
            let payload = sub_atom.pow(exponent) * (&a__ + &b__ * (&c__ * &sub_atom).atan()).pow(&p_);
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            rubi_star(Atom::num(1) / &n_, rubi_subst(&primitive, substitution_symbol, x_.pow(&n_)))
        },
    ));
}

fn push_rules_rule_5364(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5364,
        source: "Int[x_^m_.*(a_.+b_.*ArcCot[c_.*x_^n_])^p_.,x_Symbol] :=
          1/n \\[Star] Subst[Int[x^(Simplify[(m+1)/n]-1)*(a+b*ArcCot[c*x])^p,x],x,x^n] /;
        FreeQ[{a,b,c,m,n},x] && IGtQ[p,1] && IntegerQ[Simplify[(m+1)/n]]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [m_, a__, b__, c__, n_, p_, x_],
        optional: [m_, a__, b__, c__, p_],
        when: {
            freeq!([a__, b__, c__, m_, n_], x_)
                && igtq!(p_, 1)
                && integerq!(rubi_simplify(&((&m_ + Atom::num(1)) / &n_)))
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let exponent = rubi_simplify(&((&m_ + Atom::num(1)) / &n_)) - Atom::num(1);
            let payload = sub_atom.pow(exponent) * (&a__ + &b__ * (&c__ * &sub_atom).acot()).pow(&p_);
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            rubi_star(Atom::num(1) / &n_, rubi_subst(&primitive, substitution_symbol, x_.pow(&n_)))
        },
    ));
}

fn push_rules_rule_5365(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5365,
        source: "Int[x_^m_.*(a_.+b_.*ArcTan[c_.*x_^n_])^p_,x_Symbol] :=
          Int[ExpandIntegrand[x^m*(a+(I*b*Log[1-I*c*x^n])/2-(I*b*Log[1+I*c*x^n])/2)^p,x],x] /;
        FreeQ[{a,b,c},x] && IGtQ[p,1] && IGtQ[n,0] && IntegerQ[m]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [m_, a__, b__, c__, n_, p_, x_],
        optional: [m_, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__], x_)
                && igtq!(p_, 1)
                && igtq!(n_, 0)
                && integerq!(m_)
        },
        rhs: {
            let i = Atom::i();
            let power = x_.pow(&n_);
            let payload = x_.pow(&m_)
                * (&a__ + &i * &b__ * (Atom::num(1) - &i * &c__ * &power).log() / Atom::num(2)
                    - &i * &b__ * (Atom::num(1) + &i * &c__ * power).log() / Atom::num(2))
                    .pow(&p_);
            let expanded = rubi_expand_integrand(&payload, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_5366(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5366,
        source: "Int[x_^m_.*(a_.+b_.*ArcCot[c_.*x_^n_])^p_,x_Symbol] :=
          Int[ExpandIntegrand[x^m*(a+(I*b*Log[1-I*x^(-n)/c])/2-(I*b*Log[1+I*x^(-n)/c])/2)^p,x],x] /;
        FreeQ[{a,b,c},x] && IGtQ[p,1] && IGtQ[n,0] && IntegerQ[m]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [m_, a__, b__, c__, n_, p_, x_],
        optional: [m_, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__], x_)
                && igtq!(p_, 1)
                && igtq!(n_, 0)
                && integerq!(m_)
        },
        rhs: {
            let i = Atom::i();
            let reciprocal_power = x_.pow(-&n_) / &c__;
            let payload = x_.pow(&m_)
                * (&a__ + &i * &b__ * (Atom::num(1) - &i * &reciprocal_power).log() / Atom::num(2)
                    - &i * &b__ * (Atom::num(1) + &i * reciprocal_power).log() / Atom::num(2))
                    .pow(&p_);
            let expanded = rubi_expand_integrand(&payload, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_5367(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5367,
        source: "Int[x_^m_.*(a_.+b_.*ArcTan[c_.*x_^n_])^p_,x_Symbol] :=
          With[{k=Denominator[m]},
          k \\[Star] Subst[Int[x^(k*(m+1)-1)*(a+b*ArcTan[c*x^(k*n)])^p,x],x,x^(1/k)]] /;
        FreeQ[{a,b,c},x] && IGtQ[p,1] && IGtQ[n,0] && FractionQ[m]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [m_, a__, b__, c__, n_, p_, x_],
        optional: [m_, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__], x_)
                && igtq!(p_, 1)
                && igtq!(n_, 0)
                && fractionq!(m_)
        },
        rhs: {
            let k_i = rubi_denominator(&m_).rubi_rhs();
            let k = Atom::num(k_i);
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let payload = sub_atom.pow(&k * (&m_ + Atom::num(1)) - Atom::num(1))
                * (&a__ + &b__ * (&c__ * sub_atom.pow(&k * &n_)).atan()).pow(&p_);
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            rubi_star(k, rubi_subst(&primitive, substitution_symbol, x_.pow(Atom::num(1) / k_i)))
        },
    ));
}

fn push_rules_rule_5368(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5368,
        source: "Int[x_^m_.*(a_.+b_.*ArcCot[c_.*x_^n_])^p_,x_Symbol] :=
          With[{k=Denominator[m]},
          k \\[Star] Subst[Int[x^(k*(m+1)-1)*(a+b*ArcCot[c*x^(k*n)])^p,x],x,x^(1/k)]] /;
        FreeQ[{a,b,c},x] && IGtQ[p,1] && IGtQ[n,0] && FractionQ[m]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [m_, a__, b__, c__, n_, p_, x_],
        optional: [m_, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__], x_)
                && igtq!(p_, 1)
                && igtq!(n_, 0)
                && fractionq!(m_)
        },
        rhs: {
            let k_i = rubi_denominator(&m_).rubi_rhs();
            let k = Atom::num(k_i);
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let payload = sub_atom.pow(&k * (&m_ + Atom::num(1)) - Atom::num(1))
                * (&a__ + &b__ * (&c__ * sub_atom.pow(&k * &n_)).acot()).pow(&p_);
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            rubi_star(k, rubi_subst(&primitive, substitution_symbol, x_.pow(Atom::num(1) / k_i)))
        },
    ));
}

fn push_rules_rule_5369(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5369,
        source: "Int[x_^m_.*(a_.+b_.*ArcTan[c_.*x_^n_])^p_,x_Symbol] :=
          Int[x^m*(a+b*ArcCot[x^(-n)/c])^p,x] /;
        FreeQ[{a,b,c},x] && IGtQ[p,1] && ILtQ[n,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [m_, a__, b__, c__, n_, p_, x_],
        optional: [m_, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__], x_)
                && igtq!(p_, 1)
                && iltq!(n_, 0)
        },
        rhs: {
            let transformed = x_.pow(&m_) * (&a__ + &b__ * (x_.pow(-&n_) / &c__).acot()).pow(&p_);
            rubi_rhs_int(&transformed, x_)
        },
    ));
}

fn push_rules_rule_5370(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5370,
        source: "Int[x_^m_.*(a_.+b_.*ArcCot[c_.*x_^n_])^p_,x_Symbol] :=
          Int[x^m*(a+b*ArcTan[x^(-n)/c])^p,x] /;
        FreeQ[{a,b,c},x] && IGtQ[p,1] && ILtQ[n,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [m_, a__, b__, c__, n_, p_, x_],
        optional: [m_, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__], x_)
                && igtq!(p_, 1)
                && iltq!(n_, 0)
        },
        rhs: {
            let transformed = x_.pow(&m_) * (&a__ + &b__ * (x_.pow(-&n_) / &c__).atan()).pow(&p_);
            rubi_rhs_int(&transformed, x_)
        },
    ));
}

fn push_rules_rule_5371(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5371,
        source: "Int[x_^m_.*(a_.+b_.*ArcTan[c_.*x_^n_])^p_,x_Symbol] :=
          With[{k=Denominator[n]},
          k \\[Star] Subst[Int[x^(k*(m+1)-1)*(a+b*ArcTan[c*x^(k*n)])^p,x],x,x^(1/k)]] /;
        FreeQ[{a,b,c},x] && IGtQ[p,1] && FractionQ[n]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [m_, a__, b__, c__, n_, p_, x_],
        optional: [m_, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__], x_)
                && igtq!(p_, 1)
                && fractionq!(n_)
        },
        rhs: {
            let k_i = rubi_denominator(&n_).rubi_rhs();
            let k = Atom::num(k_i);
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let payload = sub_atom.pow(&k * (&m_ + Atom::num(1)) - Atom::num(1))
                * (&a__ + &b__ * (&c__ * sub_atom.pow(&k * &n_)).atan()).pow(&p_);
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            rubi_star(k, rubi_subst(&primitive, substitution_symbol, x_.pow(Atom::num(1) / k_i)))
        },
    ));
}

fn push_rules_rule_5372(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5372,
        source: "Int[x_^m_.*(a_.+b_.*ArcCot[c_.*x_^n_])^p_,x_Symbol] :=
          With[{k=Denominator[n]},
          k \\[Star] Subst[Int[x^(k*(m+1)-1)*(a+b*ArcCot[c*x^(k*n)])^p,x],x,x^(1/k)]] /;
        FreeQ[{a,b,c},x] && IGtQ[p,1] && FractionQ[n]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [m_, a__, b__, c__, n_, p_, x_],
        optional: [m_, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__], x_)
                && igtq!(p_, 1)
                && fractionq!(n_)
        },
        rhs: {
            let k_i = rubi_denominator(&n_).rubi_rhs();
            let k = Atom::num(k_i);
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let payload = sub_atom.pow(&k * (&m_ + Atom::num(1)) - Atom::num(1))
                * (&a__ + &b__ * (&c__ * sub_atom.pow(&k * &n_)).acot()).pow(&p_);
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            rubi_star(k, rubi_subst(&primitive, substitution_symbol, x_.pow(Atom::num(1) / k_i)))
        },
    ));
}

fn push_rules_rule_5373(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d_, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5373,
        source: "Int[(d_*x_)^m_*(a_.+b_.*ArcTan[c_.*x_^n_.]),x_Symbol] :=
          (d*x)^(m+1)*(a+b*ArcTan[c*x^n])/(d*(m+1)) -
          b*c*n/(d^n*(m+1)) \\[Star] Int[(d*x)^(m+n)/(1+c^2*x^(2*n)),x] /;
        FreeQ[{a,b,c,d,m,n},x] && IntegerQ[n] && NeQ[m,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern: (d_ * x_).pow(m_) * (a__ + b__ * (c__ * x_.pow(n_)).atan()),
        with: [d_, m_, a__, b__, c__, n_, x_],
        optional: [a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d_, m_, n_], x_)
                && integerq!(n_)
                && neq!(m_, -1)
        },
        rhs: {
            let scaled = &d_ * x_;
            let argument = &a__ + &b__ * (&c__ * x_.pow(&n_)).atan();
            let recursive = scaled.pow(&m_ + &n_) / (Atom::num(1) + c__.pow(2) * x_.pow(Atom::num(2) * &n_));
            rubi_simp(&(scaled.pow(&m_ + Atom::num(1)) * argument / (&d_ * (&m_ + Atom::num(1)))), x_)
                    - rubi_star(&b__ * &c__ * &n_ / (d_.pow(&n_) * (&m_ + Atom::num(1))), rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_5374(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d_, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5374,
        source: "Int[(d_*x_)^m_*(a_.+b_.*ArcCot[c_.*x_^n_.]),x_Symbol] :=
          (d*x)^(m+1)*(a+b*ArcCot[c*x^n])/(d*(m+1)) +
          b*c*n/(d^n*(m+1)) \\[Star] Int[(d*x)^(m+n)/(1+c^2*x^(2*n)),x] /;
        FreeQ[{a,b,c,d,m,n},x] && IntegerQ[n] && NeQ[m,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern: (d_ * x_).pow(m_) * (a__ + b__ * (c__ * x_.pow(n_)).acot()),
        with: [d_, m_, a__, b__, c__, n_, x_],
        optional: [a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d_, m_, n_], x_)
                && integerq!(n_)
                && neq!(m_, -1)
        },
        rhs: {
            let scaled = &d_ * x_;
            let argument = &a__ + &b__ * (&c__ * x_.pow(&n_)).acot();
            let recursive = scaled.pow(&m_ + &n_) / (Atom::num(1) + c__.pow(2) * x_.pow(Atom::num(2) * &n_));
            rubi_simp(&(scaled.pow(&m_ + Atom::num(1)) * argument / (&d_ * (&m_ + Atom::num(1)))), x_)
                    + rubi_star(&b__ * &c__ * &n_ / (d_.pow(&n_) * (&m_ + Atom::num(1))), rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_5375(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5375,
        source: "Int[(d_.*x_)^m_*(a_.+b_.*ArcTan[c_.*x_^n_])^p_.,x_Symbol] :=
          d^IntPart[m]*(d*x)^FracPart[m]/x^FracPart[m] \\[Star] Int[x^m*(a+b*ArcTan[c*x])^p,x] /;
        FreeQ[{a,b,c,d,m,n},x] && IGtQ[p,0] && (EqQ[p,1] || RationalQ[m,n])",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [d__, m_, a__, b__, c__, n_, p_, x_],
        optional: [d__, a__, b__, c__, p_],
        when: {
            freeq!([a__, b__, c__, d__, m_, n_], x_)
                && igtq!(p_, 0)
                && (eqq!(p_, 1) || rationalq!([m_, n_]))
        },
        rhs: {
            let frac_m = rubi_frac_part(&m_);
            let argument = &a__ + &b__ * (&c__ * x_.pow(&n_)).atan();
            let recursive = x_.pow(&m_) * argument.pow(&p_);
            rubi_star(d__.pow(rubi_int_part(&m_)) * (&d__ * x_).pow(&frac_m) / x_.pow(frac_m), rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_5376(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5376,
        source: "Int[(d_.*x_)^m_*(a_.+b_.*ArcCot[c_.*x_^n_])^p_.,x_Symbol] :=
          d^IntPart[m]*(d*x)^FracPart[m]/x^FracPart[m] \\[Star] Int[x^m*(a+b*ArcCot[c*x])^p,x] /;
        FreeQ[{a,b,c,d,m,n},x] && IGtQ[p,0] && (EqQ[p,1] || RationalQ[m,n])",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [d__, m_, a__, b__, c__, n_, p_, x_],
        optional: [d__, a__, b__, c__, p_],
        when: {
            freeq!([a__, b__, c__, d__, m_, n_], x_)
                && igtq!(p_, 0)
                && (eqq!(p_, 1) || rationalq!([m_, n_]))
        },
        rhs: {
            let frac_m = rubi_frac_part(&m_);
            let argument = &a__ + &b__ * (&c__ * x_.pow(&n_)).acot();
            let recursive = x_.pow(&m_) * argument.pow(&p_);
            rubi_star(d__.pow(rubi_int_part(&m_)) * (&d__ * x_).pow(&frac_m) / x_.pow(frac_m), rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_5377(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5377,
        source: "Int[(d_.*x_)^m_.*(a_.+b_.*ArcTan[c_.*x_^n_.])^p_.,x_Symbol] :=
          Unintegrable[(d*x)^m*(a+b*ArcTan[c*x^n])^p,x] /;
        FreeQ[{a,b,c,d,m,n,p},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [d__, m_, a__, b__, c__, n_, p_, x_],
        optional: [d__, m_, a__, b__, c__, n_, p_],
        when: { freeq!([a__, b__, c__, d__, m_, n_, p_], x_) },
        rhs: {
            let integrand = (&d__ * x_).pow(&m_) * (&a__ + &b__ * (&c__ * x_.pow(&n_)).atan()).pow(&p_);
            rubi_unintegrable(integrand, x_)
        },
    ));
}

fn push_rules_rule_5378(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5378,
        source: "Int[(d_.*x_)^m_.*(a_.+b_.*ArcCot[c_.*x_^n_.])^p_.,x_Symbol] :=
          Unintegrable[(d*x)^m*(a+b*ArcCot[c*x^n])^p,x] /;
        FreeQ[{a,b,c,d,m,n,p},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [d__, m_, a__, b__, c__, n_, p_, x_],
        optional: [d__, m_, a__, b__, c__, n_, p_],
        when: { freeq!([a__, b__, c__, d__, m_, n_, p_], x_) },
        rhs: {
            let integrand = (&d__ * x_).pow(&m_) * (&a__ + &b__ * (&c__ * x_.pow(&n_)).acot()).pow(&p_);
            rubi_unintegrable(integrand, x_)
        },
    ));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn downvalues_5355_through_5378_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .filter(|order| (5355..=5378).contains(order))
            .collect::<Vec<_>>();
        assert_eq!(orders, (5355..=5378).collect::<Vec<_>>());
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
    (d__ * x_).pow(m_) * (a__ + b__ * (c__ * x_.pow(n_)).acot()).pow(p_)
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
    (d__ * x_).pow(m_) * (a__ + b__ * (c__ * x_.pow(n_)).atan()).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_2(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    x_.pow(m_) * (a__ + b__ * (c__ * x_.pow(n_)).acot()).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_3(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    x_.pow(m_) * (a__ + b__ * (c__ * x_.pow(n_)).atan()).pow(p_)
}
