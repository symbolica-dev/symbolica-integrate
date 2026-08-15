use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_5562(rules);
    push_rules_rule_5563(rules);
    push_rules_rule_5564(rules);
    push_rules_rule_5565(rules);
    push_rules_rule_5566(rules);
    push_rules_rule_5567(rules);
    push_rules_rule_5568(rules);
    push_rules_rule_5569(rules);
    push_rules_rule_5570(rules);
    push_rules_rule_5571(rules);
    push_rules_rule_5572(rules);
    push_rules_rule_5573(rules);
    push_rules_rule_5574(rules);
    push_rules_rule_5575(rules);
    push_rules_rule_5576(rules);
    push_rules_rule_5577(rules);
    push_rules_rule_5578(rules);
    push_rules_rule_5579(rules);
    push_rules_rule_5580(rules);
    push_rules_rule_5581(rules);
}

fn push_rules_rule_5562(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c_, d__, p_, x_);
    rules.push(rubi_rule!(
        order: 5562,
        source: "Int[(a_.+b_.*ArcTan[c_+d_.*x_])^p_.,x_Symbol] :=
          1/d \\[Star] Subst[Int[(a+b*ArcTan[x])^p,x],x,c+d*x] /;
        FreeQ[{a,b,c,d},x] && IGtQ[p,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c_, d__, p_, x_],
        optional: [a__, b__, d__, p_],
        when: { freeq!([a__, b__, c_, d__], x_) && igtq!(p_, 0) },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let payload = (&a__ + &b__ * sub_atom.atan()).pow(&p_);
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            rubi_star(Atom::num(1) / &d__, rubi_subst(&primitive, substitution_symbol, &c_ + &d__ * x_))
        },
    ));
}

fn push_rules_rule_5563(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c_, d__, p_, x_);
    rules.push(rubi_rule!(
        order: 5563,
        source: "Int[(a_.+b_.*ArcCot[c_+d_.*x_])^p_.,x_Symbol] :=
          1/d \\[Star] Subst[Int[(a+b*ArcCot[x])^p,x],x,c+d*x] /;
        FreeQ[{a,b,c,d},x] && IGtQ[p,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c_, d__, p_, x_],
        optional: [a__, b__, d__, p_],
        when: { freeq!([a__, b__, c_, d__], x_) && igtq!(p_, 0) },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let payload = (&a__ + &b__ * sub_atom.acot()).pow(&p_);
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            rubi_star(Atom::num(1) / &d__, rubi_subst(&primitive, substitution_symbol, &c_ + &d__ * x_))
        },
    ));
}

fn push_rules_rule_5564(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c_, d__, p_, x_);
    rules.push(rubi_rule!(
        order: 5564,
        source: "Int[(a_.+b_.*ArcTan[c_+d_.*x_])^p_,x_Symbol] :=
          Unintegrable[(a+b*ArcTan[c+d*x])^p,x] /;
        FreeQ[{a,b,c,d,p},x] && Not[IGtQ[p,0]]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c_, d__, p_, x_],
        optional: [a__, b__, d__],
        when: { freeq!([a__, b__, c_, d__, p_], x_) && !igtq!(p_, 0) },
        rhs: {
            rubi_unintegrable((&a__ + &b__ * (&c_ + &d__ * x_).atan()).pow(&p_), x_)
        },
    ));
}

fn push_rules_rule_5565(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c_, d__, p_, x_);
    rules.push(rubi_rule!(
        order: 5565,
        source: "Int[(a_.+b_.*ArcCot[c_+d_.*x_])^p_,x_Symbol] :=
          Unintegrable[(a+b*ArcCot[c+d*x])^p,x] /;
        FreeQ[{a,b,c,d,p},x] && Not[IGtQ[p,0]]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c_, d__, p_, x_],
        optional: [a__, b__, d__],
        when: { freeq!([a__, b__, c_, d__, p_], x_) && !igtq!(p_, 0) },
        rhs: {
            rubi_unintegrable((&a__ + &b__ * (&c_ + &d__ * x_).acot()).pow(&p_), x_)
        },
    ));
}

fn push_rules_rule_5566(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c_, d__, e__, f__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 5566,
        source: "Int[(e_.+f_.*x_)^m_.*(a_.+b_.*ArcTan[c_+d_.*x_])^p_.,x_Symbol] :=
          1/d \\[Star] Subst[Int[(f*x/d)^m*(a+b*ArcTan[x])^p,x],x,c+d*x] /;
        FreeQ[{a,b,c,d,e,f,m},x] && EqQ[d*e-c*f,0] && IGtQ[p,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [e__, f__, m_, a__, b__, c_, d__, p_, x_],
        optional: [e__, f__, m_, a__, b__, d__, p_],
        when: {
            freeq!([a__, b__, c_, d__, e__, f__, m_], x_)
                && eqq!(&d__ * &e__ - &c_ * &f__, 0)
                && igtq!(p_, 0)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let payload = (&f__ * &sub_atom / &d__).pow(&m_) * (&a__ + &b__ * sub_atom.atan()).pow(&p_);
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            rubi_star(Atom::num(1) / &d__, rubi_subst(&primitive, substitution_symbol, &c_ + &d__ * x_))
        },
    ));
}

fn push_rules_rule_5567(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c_, d__, e__, f__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 5567,
        source: "Int[(e_.+f_.*x_)^m_.*(a_.+b_.*ArcCot[c_+d_.*x_])^p_.,x_Symbol] :=
          1/d \\[Star] Subst[Int[(f*x/d)^m*(a+b*ArcCot[x])^p,x],x,c+d*x] /;
        FreeQ[{a,b,c,d,e,f,m},x] && EqQ[d*e-c*f,0] && IGtQ[p,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [e__, f__, m_, a__, b__, c_, d__, p_, x_],
        optional: [e__, f__, m_, a__, b__, d__, p_],
        when: {
            freeq!([a__, b__, c_, d__, e__, f__, m_], x_)
                && eqq!(&d__ * &e__ - &c_ * &f__, 0)
                && igtq!(p_, 0)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let payload = (&f__ * &sub_atom / &d__).pow(&m_) * (&a__ + &b__ * sub_atom.acot()).pow(&p_);
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            rubi_star(Atom::num(1) / &d__, rubi_subst(&primitive, substitution_symbol, &c_ + &d__ * x_))
        },
    ));
}

fn push_rules_rule_5568(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c_, d__, e__, f__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 5568,
        source: "Int[(e_.+f_.*x_)^m_*(a_.+b_.*ArcTan[c_+d_.*x_])^p_.,x_Symbol] :=
          (e+f*x)^(m+1)*(a+b*ArcTan[c+d*x])^p/(f*(m+1)) -
          b*d*p/(f*(m+1)) \\[Star] Int[(e+f*x)^(m+1)*(a+b*ArcTan[c+d*x])^(p-1)/(1+(c+d*x)^2),x] /;
        FreeQ[{a,b,c,d,e,f},x] && IGtQ[p,0] && ILtQ[m,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [e__, f__, m_, a__, b__, c_, d__, p_, x_],
        optional: [e__, f__, a__, b__, d__, p_],
        when: {
            freeq!([a__, b__, c_, d__, e__, f__], x_) && igtq!(p_, 0) && iltq!(m_, -1)
        },
        rhs: {
            let linear = &e__ + &f__ * x_;
            let shifted = &c_ + &d__ * x_;
            let argument = &a__ + &b__ * &shifted.atan();
            let recursive = linear.pow(&m_ + 1) * argument.pow(&p_ - 1)
                / (Atom::num(1) + shifted.pow(2));
            rubi_simp(&(linear.pow(&m_ + 1) * argument.pow(&p_) / (&f__ * (&m_ + 1))), x_)
                    - rubi_star(&b__ * &d__ * &p_ / (&f__ * (&m_ + 1)), rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_5569(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c_, d__, e__, f__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 5569,
        source: "Int[(e_.+f_.*x_)^m_*(a_.+b_.*ArcCot[c_+d_.*x_])^p_.,x_Symbol] :=
          (e+f*x)^(m+1)*(a+b*ArcCot[c+d*x])^p/(f*(m+1)) +
          b*d*p/(f*(m+1)) \\[Star] Int[(e+f*x)^(m+1)*(a+b*ArcCot[c+d*x])^(p-1)/(1+(c+d*x)^2),x] /;
        FreeQ[{a,b,c,d,e,f},x] && IGtQ[p,0] && ILtQ[m,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [e__, f__, m_, a__, b__, c_, d__, p_, x_],
        optional: [e__, f__, a__, b__, d__, p_],
        when: {
            freeq!([a__, b__, c_, d__, e__, f__], x_) && igtq!(p_, 0) && iltq!(m_, -1)
        },
        rhs: {
            let linear = &e__ + &f__ * x_;
            let shifted = &c_ + &d__ * x_;
            let argument = &a__ + &b__ * &shifted.acot();
            let recursive = linear.pow(&m_ + 1) * argument.pow(&p_ - 1)
                / (Atom::num(1) + shifted.pow(2));
            rubi_simp(&(linear.pow(&m_ + 1) * argument.pow(&p_) / (&f__ * (&m_ + 1))), x_)
                    + rubi_star(&b__ * &d__ * &p_ / (&f__ * (&m_ + 1)), rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_5570(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c_, d__, e__, f__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 5570,
        source: "Int[(e_.+f_.*x_)^m_.*(a_.+b_.*ArcTan[c_+d_.*x_])^p_.,x_Symbol] :=
          1/d \\[Star] Subst[Int[((d*e-c*f)/d+f*x/d)^m*(a+b*ArcTan[x])^p,x],x,c+d*x] /;
        FreeQ[{a,b,c,d,e,f,m,p},x] && IGtQ[p,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [e__, f__, m_, a__, b__, c_, d__, p_, x_],
        optional: [e__, f__, m_, a__, b__, d__, p_],
        when: { freeq!([a__, b__, c_, d__, e__, f__, m_, p_], x_) && igtq!(p_, 0) },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let transformed_linear = (&d__ * &e__ - &c_ * &f__) / &d__ + &f__ * &sub_atom / &d__;
            let payload = transformed_linear.pow(&m_) * (&a__ + &b__ * sub_atom.atan()).pow(&p_);
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            rubi_star(Atom::num(1) / &d__, rubi_subst(&primitive, substitution_symbol, &c_ + &d__ * x_))
        },
    ));
}

fn push_rules_rule_5571(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c_, d__, e__, f__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 5571,
        source: "Int[(e_.+f_.*x_)^m_.*(a_.+b_.*ArcCot[c_+d_.*x_])^p_.,x_Symbol] :=
          1/d \\[Star] Subst[Int[((d*e-c*f)/d+f*x/d)^m*(a+b*ArcCot[x])^p,x],x,c+d*x] /;
        FreeQ[{a,b,c,d,e,f,m,p},x] && IGtQ[p,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [e__, f__, m_, a__, b__, c_, d__, p_, x_],
        optional: [e__, f__, m_, a__, b__, d__, p_],
        when: { freeq!([a__, b__, c_, d__, e__, f__, m_, p_], x_) && igtq!(p_, 0) },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let transformed_linear = (&d__ * &e__ - &c_ * &f__) / &d__ + &f__ * &sub_atom / &d__;
            let payload = transformed_linear.pow(&m_) * (&a__ + &b__ * sub_atom.acot()).pow(&p_);
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            rubi_star(Atom::num(1) / &d__, rubi_subst(&primitive, substitution_symbol, &c_ + &d__ * x_))
        },
    ));
}

fn push_rules_rule_5572(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c_, d__, e__, f__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 5572,
        source: "Int[(e_.+f_.*x_)^m_.*(a_.+b_.*ArcTan[c_+d_.*x_])^p_,x_Symbol] :=
          Unintegrable[(e+f*x)^m*(a+b*ArcTan[c+d*x])^p,x] /;
        FreeQ[{a,b,c,d,e,f,m,p},x] && Not[IGtQ[p,0]]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [e__, f__, m_, a__, b__, c_, d__, p_, x_],
        optional: [e__, f__, m_, a__, b__, d__],
        when: {
            freeq!([a__, b__, c_, d__, e__, f__, m_, p_], x_) && !igtq!(p_, 0)
        },
        rhs: {
            rubi_unintegrable(
                (&e__ + &f__ * x_).pow(&m_) * (&a__ + &b__ * (&c_ + &d__ * x_).atan()).pow(&p_),
                x_,
            )
        },
    ));
}

fn push_rules_rule_5573(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c_, d__, e__, f__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 5573,
        source: "Int[(e_.+f_.*x_)^m_.*(a_.+b_.*ArcCot[c_+d_.*x_])^p_,x_Symbol] :=
          Unintegrable[(e+f*x)^m*(a+b*ArcCot[c+d*x])^p,x] /;
        FreeQ[{a,b,c,d,e,f,m,p},x] && Not[IGtQ[p,0]]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [e__, f__, m_, a__, b__, c_, d__, p_, x_],
        optional: [e__, f__, m_, a__, b__, d__],
        when: {
            freeq!([a__, b__, c_, d__, e__, f__, m_, p_], x_) && !igtq!(p_, 0)
        },
        rhs: {
            rubi_unintegrable(
                (&e__ + &f__ * x_).pow(&m_) * (&a__ + &b__ * (&c_ + &d__ * x_).acot()).pow(&p_),
                x_,
            )
        },
    ));
}

fn push_rules_rule_5574(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a_, b__, c_, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 5574,
        source: "Int[ArcTan[a_+b_.*x_]/(c_+d_.*x_^n_.),x_Symbol] :=
          I/2 \\[Star] Int[Log[1-I*a-I*b*x]/(c+d*x^n),x] -
          I/2 \\[Star] Int[Log[1+I*a+I*b*x]/(c+d*x^n),x] /;
        FreeQ[{a,b,c,d},x] && RationalQ[n]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a_, b__, c_, d__, n_, x_],
        optional: [b__, d__, n_],
        when: { freeq!([a_, b__, c_, d__], x_) && rationalq!(n_) },
        rhs: {
            let i = Atom::i();
            let affine = &a_ + &b__ * x_;
            let denominator = &c_ + &d__ * x_.pow(&n_);
            let coefficient = &i / Atom::num(2);
            rubi_star(&coefficient, rubi_rhs_int(
                        &((Atom::num(1) - &i * &affine).log() / &denominator),
                        x_,
                    )) - rubi_star(coefficient, rubi_rhs_int(
                        &((Atom::num(1) + Atom::i() * affine).log() / denominator),
                        x_,
                    ))
        },
    ));
}

fn push_rules_rule_5575(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a_, b__, c_, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 5575,
        source: "Int[ArcCot[a_+b_.*x_]/(c_+d_.*x_^n_.),x_Symbol] :=
          I/2 \\[Star] Int[Log[(-I+a+b*x)/(a+b*x)]/(c+d*x^n),x] -
          I/2 \\[Star] Int[Log[(I+a+b*x)/(a+b*x)]/(c+d*x^n),x] /;
        FreeQ[{a,b,c,d},x] && RationalQ[n]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a_, b__, c_, d__, n_, x_],
        optional: [b__, d__, n_],
        when: { freeq!([a_, b__, c_, d__], x_) && rationalq!(n_) },
        rhs: {
            let i = Atom::i();
            let affine = &a_ + &b__ * x_;
            let denominator = &c_ + &d__ * x_.pow(&n_);
            let coefficient = &i / Atom::num(2);
            rubi_star(&coefficient, rubi_rhs_int(
                        &(((-&i + &affine) / &affine).log() / &denominator),
                        x_,
                    )) - rubi_star(coefficient, rubi_rhs_int(
                        &(((Atom::i() + &affine) / affine).log() / denominator),
                        x_,
                    ))
        },
    ));
}

fn push_rules_rule_5576(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a_, b__, c_, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 5576,
        source: "Int[ArcTan[a_+b_.*x_]/(c_+d_.*x_^n_),x_Symbol] :=
          Unintegrable[ArcTan[a+b*x]/(c+d*x^n),x] /;
        FreeQ[{a,b,c,d,n},x] && Not[RationalQ[n]]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a_, b__, c_, d__, n_, x_],
        optional: [b__, d__],
        when: { freeq!([a_, b__, c_, d__, n_], x_) && !rationalq!(n_) },
        rhs: {
            rubi_unintegrable(
                (&a_ + &b__ * x_).atan() / (&c_ + &d__ * x_.pow(&n_)),
                x_,
            )
        },
    ));
}

fn push_rules_rule_5577(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a_, b__, c_, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 5577,
        source: "Int[ArcCot[a_+b_.*x_]/(c_+d_.*x_^n_),x_Symbol] :=
          Unintegrable[ArcCot[a+b*x]/(c+d*x^n),x] /;
        FreeQ[{a,b,c,d,n},x] && Not[RationalQ[n]]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a_, b__, c_, d__, n_, x_],
        optional: [b__, d__],
        when: { freeq!([a_, b__, c_, d__, n_], x_) && !rationalq!(n_) },
        rhs: {
            rubi_unintegrable(
                (&a_ + &b__ * x_).acot() / (&c_ + &d__ * x_.pow(&n_)),
                x_,
            )
        },
    ));
}

fn push_rules_rule_5578(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        capital_a__,
        capital_b__,
        capital_c__,
        a__,
        b__,
        c_,
        d__,
        p_,
        q_,
        x_
    );
    rules.push(rubi_rule!(
        order: 5578,
        source: "Int[(A_.+B_.*x_+C_.*x_^2)^q_.*(a_.+b_.*ArcTan[c_+d_.*x_])^p_.,x_Symbol] :=
          1/d \\[Star] Subst[Int[(C/d^2+C/d^2*x^2)^q*(a+b*ArcTan[x])^p,x],x,c+d*x] /;
        FreeQ[{a,b,c,d,A,B,C,p,q},x] && EqQ[B*(1+c^2)-2*A*c*d,0] && EqQ[2*c*C-B*d,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (capital_a__ + capital_b__ * x_ + capital_c__ * x_.pow(2)).pow(q_)
            * (a__ + b__ * (c_ + d__ * x_).atan()).pow(p_),
        with: [capital_a__, capital_b__, capital_c__, q_, a__, b__, c_, d__, p_, x_],
        optional: [capital_a__, capital_b__, capital_c__, q_, a__, b__, d__, p_],
        when: {
            freeq!([a__, b__, c_, d__, capital_a__, capital_b__, capital_c__, p_, q_], x_)
                && eqq!(&capital_b__ * (Atom::num(1) + c_.pow(2)) - Atom::num(2) * &capital_a__ * &c_ * &d__, 0)
                && eqq!(Atom::num(2) * &c_ * &capital_c__ - &capital_b__ * &d__, 0)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let transformed_quadratic = &capital_c__ / d__.pow(2) + &capital_c__ * sub_atom.pow(2) / d__.pow(2);
            let payload = transformed_quadratic.pow(&q_) * (&a__ + &b__ * sub_atom.atan()).pow(&p_);
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            rubi_star(Atom::num(1) / &d__, rubi_subst(&primitive, substitution_symbol, &c_ + &d__ * x_))
        },
    ));
}

fn push_rules_rule_5579(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        capital_a__,
        capital_b__,
        capital_c__,
        a__,
        b__,
        c_,
        d__,
        p_,
        q_,
        x_
    );
    rules.push(rubi_rule!(
        order: 5579,
        source: "Int[(A_.+B_.*x_+C_.*x_^2)^q_.*(a_.+b_.*ArcCot[c_+d_.*x_])^p_.,x_Symbol] :=
          1/d \\[Star] Subst[Int[(C/d^2+C/d^2*x^2)^q*(a+b*ArcCot[x])^p,x],x,c+d*x] /;
        FreeQ[{a,b,c,d,A,B,C,p,q},x] && EqQ[B*(1+c^2)-2*A*c*d,0] && EqQ[2*c*C-B*d,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (capital_a__ + capital_b__ * x_ + capital_c__ * x_.pow(2)).pow(q_)
            * (a__ + b__ * (c_ + d__ * x_).acot()).pow(p_),
        with: [capital_a__, capital_b__, capital_c__, q_, a__, b__, c_, d__, p_, x_],
        optional: [capital_a__, capital_b__, capital_c__, q_, a__, b__, d__, p_],
        when: {
            freeq!([a__, b__, c_, d__, capital_a__, capital_b__, capital_c__, p_, q_], x_)
                && eqq!(&capital_b__ * (Atom::num(1) + c_.pow(2)) - Atom::num(2) * &capital_a__ * &c_ * &d__, 0)
                && eqq!(Atom::num(2) * &c_ * &capital_c__ - &capital_b__ * &d__, 0)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let transformed_quadratic = &capital_c__ / d__.pow(2) + &capital_c__ * sub_atom.pow(2) / d__.pow(2);
            let payload = transformed_quadratic.pow(&q_) * (&a__ + &b__ * sub_atom.acot()).pow(&p_);
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            rubi_star(Atom::num(1) / &d__, rubi_subst(&primitive, substitution_symbol, &c_ + &d__ * x_))
        },
    ));
}

fn push_rules_rule_5580(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        capital_a__,
        capital_b__,
        capital_c__,
        a__,
        b__,
        c_,
        d__,
        e__,
        f__,
        m_,
        p_,
        q_,
        x_
    );
    rules.push(rubi_rule!(
        order: 5580,
        source: "Int[(e_.+f_.*x_)^m_.*(A_.+B_.*x_+C_.*x_^2)^q_.*(a_.+b_.*ArcTan[c_+d_.*x_])^p_.,x_Symbol] :=
          1/d \\[Star] Subst[Int[((d*e-c*f)/d+f*x/d)^m*(C/d^2+C/d^2*x^2)^q*(a+b*ArcTan[x])^p,x],x,c+d*x] /;
        FreeQ[{a,b,c,d,e,f,A,B,C,m,p,q},x] && EqQ[B*(1+c^2)-2*A*c*d,0] && EqQ[2*c*C-B*d,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (e__ + f__ * x_).pow(m_)
            * (capital_a__ + capital_b__ * x_ + capital_c__ * x_.pow(2)).pow(q_)
            * (a__ + b__ * (c_ + d__ * x_).atan()).pow(p_),
        with: [e__, f__, m_, capital_a__, capital_b__, capital_c__, q_, a__, b__, c_, d__, p_, x_],
        optional: [e__, f__, m_, capital_a__, capital_b__, capital_c__, q_, a__, b__, d__, p_],
        when: {
            freeq!([a__, b__, c_, d__, e__, f__, capital_a__, capital_b__, capital_c__, m_, p_, q_], x_)
                && eqq!(&capital_b__ * (Atom::num(1) + c_.pow(2)) - Atom::num(2) * &capital_a__ * &c_ * &d__, 0)
                && eqq!(Atom::num(2) * &c_ * &capital_c__ - &capital_b__ * &d__, 0)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let transformed_linear = (&d__ * &e__ - &c_ * &f__) / &d__ + &f__ * &sub_atom / &d__;
            let transformed_quadratic = &capital_c__ / d__.pow(2) + &capital_c__ * sub_atom.pow(2) / d__.pow(2);
            let payload = transformed_linear.pow(&m_)
                * transformed_quadratic.pow(&q_)
                * (&a__ + &b__ * sub_atom.atan()).pow(&p_);
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            rubi_star(Atom::num(1) / &d__, rubi_subst(&primitive, substitution_symbol, &c_ + &d__ * x_))
        },
    ));
}

fn push_rules_rule_5581(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        capital_a__,
        capital_b__,
        capital_c__,
        a__,
        b__,
        c_,
        d__,
        e__,
        f__,
        m_,
        p_,
        q_,
        x_
    );
    rules.push(rubi_rule!(
        order: 5581,
        source: "Int[(e_.+f_.*x_)^m_.*(A_.+B_.*x_+C_.*x_^2)^q_.*(a_.+b_.*ArcCot[c_+d_.*x_])^p_.,x_Symbol] :=
          1/d \\[Star] Subst[Int[((d*e-c*f)/d+f*x/d)^m*(C/d^2+C/d^2*x^2)^q*(a+b*ArcCot[x])^p,x],x,c+d*x] /;
        FreeQ[{a,b,c,d,e,f,A,B,C,m,p,q},x] && EqQ[B*(1+c^2)-2*A*c*d,0] && EqQ[2*c*C-B*d,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (e__ + f__ * x_).pow(m_)
            * (capital_a__ + capital_b__ * x_ + capital_c__ * x_.pow(2)).pow(q_)
            * (a__ + b__ * (c_ + d__ * x_).acot()).pow(p_),
        with: [e__, f__, m_, capital_a__, capital_b__, capital_c__, q_, a__, b__, c_, d__, p_, x_],
        optional: [e__, f__, m_, capital_a__, capital_b__, capital_c__, q_, a__, b__, d__, p_],
        when: {
            freeq!([a__, b__, c_, d__, e__, f__, capital_a__, capital_b__, capital_c__, m_, p_, q_], x_)
                && eqq!(&capital_b__ * (Atom::num(1) + c_.pow(2)) - Atom::num(2) * &capital_a__ * &c_ * &d__, 0)
                && eqq!(Atom::num(2) * &c_ * &capital_c__ - &capital_b__ * &d__, 0)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let transformed_linear = (&d__ * &e__ - &c_ * &f__) / &d__ + &f__ * &sub_atom / &d__;
            let transformed_quadratic = &capital_c__ / d__.pow(2) + &capital_c__ * sub_atom.pow(2) / d__.pow(2);
            let payload = transformed_linear.pow(&m_)
                * transformed_quadratic.pow(&q_)
                * (&a__ + &b__ * sub_atom.acot()).pow(&p_);
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            rubi_star(Atom::num(1) / &d__, rubi_subst(&primitive, substitution_symbol, &c_ + &d__ * x_))
        },
    ));
}

// Generated shared pattern builders.

#[inline(never)]
fn rubi_shared_pattern_0(symbols: &RubiSymbols) -> Atom {
    let a_ = symbols.a_;
    let b__ = symbols.b__;
    let c_ = symbols.c_;
    let d__ = symbols.d__;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    (a_ + b__ * x_).acot() / (c_ + d__ * x_.pow(n_))
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a_ = symbols.a_;
    let b__ = symbols.b__;
    let c_ = symbols.c_;
    let d__ = symbols.d__;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    (a_ + b__ * x_).atan() / (c_ + d__ * x_.pow(n_))
}

#[inline(never)]
fn rubi_shared_pattern_2(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c_ = symbols.c_;
    let d__ = symbols.d__;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (a__ + b__ * (c_ + d__ * x_).acot()).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_3(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c_ = symbols.c_;
    let d__ = symbols.d__;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (a__ + b__ * (c_ + d__ * x_).atan()).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_4(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c_ = symbols.c_;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (e__ + f__ * x_).pow(m_) * (a__ + b__ * (c_ + d__ * x_).acot()).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_5(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c_ = symbols.c_;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (e__ + f__ * x_).pow(m_) * (a__ + b__ * (c_ + d__ * x_).atan()).pow(p_)
}
