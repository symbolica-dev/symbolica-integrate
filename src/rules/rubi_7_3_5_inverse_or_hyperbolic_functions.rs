use super::super::*;

pub(super) fn push_rules(_rules: &mut Vec<RubiRule>) {}

pub(super) fn push_rules_6653_through_6672(rules: &mut Vec<RubiRule>) {
    push_rules_rule_6653(rules);
    push_rules_rule_6654(rules);
    push_rules_rule_6655(rules);
    push_rules_rule_6656(rules);
    push_rules_rule_6657(rules);
    push_rules_rule_6658(rules);
    push_rules_rule_6659(rules);
    push_rules_rule_6660(rules);
    push_rules_rule_6661(rules);
    push_rules_rule_6662(rules);
    push_rules_rule_6663(rules);
    push_rules_rule_6664(rules);
    push_rules_rule_6665(rules);
    push_rules_rule_6666(rules);
    push_rules_rule_6667(rules);
    push_rules_rule_6668(rules);
    push_rules_rule_6669(rules);
    push_rules_rule_6670(rules);
    push_rules_rule_6671(rules);
    push_rules_rule_6672(rules);
}

fn push_rules_rule_6653(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, p_, x_);
    rules.push(rubi_rule!(
        order: 6653,
        source: "Int[(a_.+b_.*ArcTanh[c_+d_.*x_])^p_.,x_Symbol] :=
          1/d \\[Star] Subst[Int[(a+b*ArcTanh[x])^p,x],x,c+d*x] /;
        FreeQ[{a,b,c,d},x] && IGtQ[p,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, p_, x_],
        optional: [a__, b__, d__, p_],
        when: { freeq!([a__, b__, c__, d__], x_) && igtq!(p_, 0) },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().rubi_rhs();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let payload = (&a__ + &b__ * sub_atom.atanh()).pow(&p_);
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            let substituted = rubi_subst(
                &primitive,
                substitution_symbol,
                &c__ + &d__ * x_,
            );

            rubi_star(Atom::num(1) / &d__, substituted)
        },
    ));
}

fn push_rules_rule_6654(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, p_, x_);
    rules.push(rubi_rule!(
        order: 6654,
        source: "Int[(a_.+b_.*ArcCoth[c_+d_.*x_])^p_.,x_Symbol] :=
          1/d \\[Star] Subst[Int[(a+b*ArcCoth[x])^p,x],x,c+d*x] /;
        FreeQ[{a,b,c,d},x] && IGtQ[p,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, p_, x_],
        optional: [a__, b__, d__, p_],
        when: { freeq!([a__, b__, c__, d__], x_) && igtq!(p_, 0) },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().rubi_rhs();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let payload = (&a__ + &b__ * sub_atom.acoth()).pow(&p_);
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            let substituted = rubi_subst(
                &primitive,
                substitution_symbol,
                &c__ + &d__ * x_,
            );

            rubi_star(Atom::num(1) / &d__, substituted)
        },
    ));
}

fn push_rules_rule_6655(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, p_, x_);
    rules.push(rubi_rule!(
        order: 6655,
        source: "Int[(a_.+b_.*ArcTanh[c_+d_.*x_])^p_,x_Symbol] :=
          Unintegrable[(a+b*ArcTanh[c+d*x])^p,x] /;
        FreeQ[{a,b,c,d,p},x] && Not[IGtQ[p,0]]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, p_, x_],
        optional: [a__, b__, d__],
        when: { freeq!([a__, b__, c__, d__, p_], x_) && !igtq!(p_, 0) },
        rhs: {
            rubi_unintegrable((&a__ + &b__ * (&c__ + &d__ * x_).atanh()).pow(&p_), x_)
        },
    ));
}

fn push_rules_rule_6656(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, p_, x_);
    rules.push(rubi_rule!(
        order: 6656,
        source: "Int[(a_.+b_.*ArcCoth[c_+d_.*x_])^p_,x_Symbol] :=
          Unintegrable[(a+b*ArcCoth[c+d*x])^p,x] /;
        FreeQ[{a,b,c,d,p},x] && Not[IGtQ[p,0]]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, p_, x_],
        optional: [a__, b__, d__],
        when: { freeq!([a__, b__, c__, d__, p_], x_) && !igtq!(p_, 0) },
        rhs: {
            rubi_unintegrable((&a__ + &b__ * (&c__ + &d__ * x_).acoth()).pow(&p_), x_)
        },
    ));
}

fn push_rules_rule_6657(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 6657,
        source: "Int[(e_.+f_.*x_)^m_.*(a_.+b_.*ArcTanh[c_+d_.*x_])^p_.,x_Symbol] :=
          1/d \\[Star] Subst[Int[(f*x/d)^m*(a+b*ArcTanh[x])^p,x],x,c+d*x] /;
        FreeQ[{a,b,c,d,e,f,m},x] && EqQ[d*e-c*f,0] && IGtQ[p,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [e__, f__, m_, a__, b__, c__, d__, p_, x_],
        optional: [e__, f__, m_, a__, b__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_], x_)
                && eqq!(&d__ * &e__ - &c__ * &f__, 0)
                && igtq!(p_, 0)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().rubi_rhs();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let payload = (&f__ * &sub_atom / &d__).pow(&m_) * (&a__ + &b__ * sub_atom.atanh()).pow(&p_);
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            let substituted = rubi_subst(
                &primitive,
                substitution_symbol,
                &c__ + &d__ * x_,
            );

            rubi_star(Atom::num(1) / &d__, substituted)
        },
    ));
}

fn push_rules_rule_6658(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 6658,
        source: "Int[(e_.+f_.*x_)^m_.*(a_.+b_.*ArcCoth[c_+d_.*x_])^p_.,x_Symbol] :=
          1/d \\[Star] Subst[Int[(f*x/d)^m*(a+b*ArcCoth[x])^p,x],x,c+d*x] /;
        FreeQ[{a,b,c,d,e,f,m},x] && EqQ[d*e-c*f,0] && IGtQ[p,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [e__, f__, m_, a__, b__, c__, d__, p_, x_],
        optional: [e__, f__, m_, a__, b__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_], x_)
                && eqq!(&d__ * &e__ - &c__ * &f__, 0)
                && igtq!(p_, 0)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().rubi_rhs();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let payload = (&f__ * &sub_atom / &d__).pow(&m_) * (&a__ + &b__ * sub_atom.acoth()).pow(&p_);
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            let substituted = rubi_subst(
                &primitive,
                substitution_symbol,
                &c__ + &d__ * x_,
            );

            rubi_star(Atom::num(1) / &d__, substituted)
        },
    ));
}

fn push_rules_rule_6659(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 6659,
        source: "Int[(e_.+f_.*x_)^m_*(a_.+b_.*ArcTanh[c_+d_.*x_])^p_.,x_Symbol] :=
          (e+f*x)^(m+1)*(a+b*ArcTanh[c+d*x])^p/(f*(m+1)) -
          b*d*p/(f*(m+1)) \\[Star] Int[(e+f*x)^(m+1)*(a+b*ArcTanh[c+d*x])^(p-1)/(1-(c+d*x)^2),x] /;
        FreeQ[{a,b,c,d,e,f},x] && IGtQ[p,0] && ILtQ[m,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [e__, f__, m_, a__, b__, c__, d__, p_, x_],
        optional: [e__, f__, a__, b__, d__, p_],
        when: { freeq!([a__, b__, c__, d__, e__, f__], x_) && igtq!(p_, 0) && iltq!(m_, -1) },
        rhs: {
            let linear = &e__ + &f__ * x_;
            let argument = &a__ + &b__ * (&c__ + &d__ * x_).atanh();
            let recursive = linear.pow(&m_ + 1) * argument.pow(&p_ - 1)
                / (Atom::num(1) - (&c__ + &d__ * x_).pow(2));

            rubi_simp(&(linear.pow(&m_ + 1) * argument.pow(&p_)
                    / (&f__ * (&m_ + 1))), x_)
                    - rubi_star(&b__ * &d__ * &p_ / (&f__ * (&m_ + 1)), rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_6660(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 6660,
        source: "Int[(e_.+f_.*x_)^m_*(a_.+b_.*ArcCoth[c_+d_.*x_])^p_.,x_Symbol] :=
          (e+f*x)^(m+1)*(a+b*ArcCoth[c+d*x])^p/(f*(m+1)) -
          b*d*p/(f*(m+1)) \\[Star] Int[(e+f*x)^(m+1)*(a+b*ArcCoth[c+d*x])^(p-1)/(1-(c+d*x)^2),x] /;
        FreeQ[{a,b,c,d,e,f},x] && IGtQ[p,0] && ILtQ[m,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [e__, f__, m_, a__, b__, c__, d__, p_, x_],
        optional: [e__, f__, a__, b__, d__, p_],
        when: { freeq!([a__, b__, c__, d__, e__, f__], x_) && igtq!(p_, 0) && iltq!(m_, -1) },
        rhs: {
            let linear = &e__ + &f__ * x_;
            let argument = &a__ + &b__ * (&c__ + &d__ * x_).acoth();
            let recursive = linear.pow(&m_ + 1) * argument.pow(&p_ - 1)
                / (Atom::num(1) - (&c__ + &d__ * x_).pow(2));

            rubi_simp(&(linear.pow(&m_ + 1) * argument.pow(&p_)
                    / (&f__ * (&m_ + 1))), x_)
                    - rubi_star(&b__ * &d__ * &p_ / (&f__ * (&m_ + 1)), rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_6661(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 6661,
        source: "Int[(e_.+f_.*x_)^m_.*(a_.+b_.*ArcTanh[c_+d_.*x_])^p_.,x_Symbol] :=
          1/d \\[Star] Subst[Int[((d*e-c*f)/d+f*x/d)^m*(a+b*ArcTanh[x])^p,x],x,c+d*x] /;
        FreeQ[{a,b,c,d,e,f,m},x] && IGtQ[p,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [e__, f__, m_, a__, b__, c__, d__, p_, x_],
        optional: [e__, f__, m_, a__, b__, d__, p_],
        when: { freeq!([a__, b__, c__, d__, e__, f__, m_], x_) && igtq!(p_, 0) },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().rubi_rhs();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let transformed_linear = (&d__ * &e__ - &c__ * &f__) / &d__ + &f__ * &sub_atom / &d__;
            let payload = transformed_linear.pow(&m_) * (&a__ + &b__ * sub_atom.atanh()).pow(&p_);
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            let substituted = rubi_subst(
                &primitive,
                substitution_symbol,
                &c__ + &d__ * x_,
            );

            rubi_star(Atom::num(1) / &d__, substituted)
        },
    ));
}

fn push_rules_rule_6662(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 6662,
        source: "Int[(e_.+f_.*x_)^m_.*(a_.+b_.*ArcCoth[c_+d_.*x_])^p_.,x_Symbol] :=
          1/d \\[Star] Subst[Int[((d*e-c*f)/d+f*x/d)^m*(a+b*ArcCoth[x])^p,x],x,c+d*x] /;
        FreeQ[{a,b,c,d,e,f,m},x] && IGtQ[p,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [e__, f__, m_, a__, b__, c__, d__, p_, x_],
        optional: [e__, f__, m_, a__, b__, d__, p_],
        when: { freeq!([a__, b__, c__, d__, e__, f__, m_], x_) && igtq!(p_, 0) },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().rubi_rhs();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let transformed_linear = (&d__ * &e__ - &c__ * &f__) / &d__ + &f__ * &sub_atom / &d__;
            let payload = transformed_linear.pow(&m_) * (&a__ + &b__ * sub_atom.acoth()).pow(&p_);
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            let substituted = rubi_subst(
                &primitive,
                substitution_symbol,
                &c__ + &d__ * x_,
            );

            rubi_star(Atom::num(1) / &d__, substituted)
        },
    ));
}

fn push_rules_rule_6663(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 6663,
        source: "Int[(e_.+f_.*x_)^m_.*(a_.+b_.*ArcTanh[c_+d_.*x_])^p_,x_Symbol] :=
          Unintegrable[(e+f*x)^m*(a+b*ArcTanh[c+d*x])^p,x] /;
        FreeQ[{a,b,c,d,e,f,m,p},x] && Not[IGtQ[p,0]]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [e__, f__, m_, a__, b__, c__, d__, p_, x_],
        optional: [e__, f__, m_, a__, b__, d__],
        when: { freeq!([a__, b__, c__, d__, e__, f__, m_, p_], x_) && !igtq!(p_, 0) },
        rhs: {
            let integrand = (&e__ + &f__ * x_).pow(&m_) * (&a__ + &b__ * (&c__ + &d__ * x_).atanh()).pow(&p_);
            rubi_unintegrable(integrand, x_)
        },
    ));
}

fn push_rules_rule_6664(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 6664,
        source: "Int[(e_.+f_.*x_)^m_.*(a_.+b_.*ArcCoth[c_+d_.*x_])^p_,x_Symbol] :=
          Unintegrable[(e+f*x)^m*(a+b*ArcCoth[c+d*x])^p,x] /;
        FreeQ[{a,b,c,d,e,f,m,p},x] && Not[IGtQ[p,0]]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [e__, f__, m_, a__, b__, c__, d__, p_, x_],
        optional: [e__, f__, m_, a__, b__, d__],
        when: { freeq!([a__, b__, c__, d__, e__, f__, m_, p_], x_) && !igtq!(p_, 0) },
        rhs: {
            let integrand = (&e__ + &f__ * x_).pow(&m_) * (&a__ + &b__ * (&c__ + &d__ * x_).acoth()).pow(&p_);
            rubi_unintegrable(integrand, x_)
        },
    ));
}

fn push_rules_rule_6665(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; c__, d__, e__, f__, n_, x_);
    rules.push(rubi_rule!(
        order: 6665,
        source: "Int[ArcTanh[c_+d_.*x_]/(e_+f_.*x_^n_.),x_Symbol] :=
          1/2 \\[Star] Int[Log[1+c+d*x]/(e+f*x^n),x] -
          1/2 \\[Star] Int[Log[1-c-d*x]/(e+f*x^n),x] /;
        FreeQ[{c,d,e,f},x] && RationalQ[n]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [c__, d__, e__, f__, n_, x_],
        optional: [d__, f__, n_],
        when: { freeq!([c__, d__, e__, f__], x_) && rationalq!(n_) },
        rhs: {
            let denominator = &e__ + &f__ * x_.pow(&n_);
            let first = rubi_rhs_int(
                &((Atom::num(1) + &c__ + &d__ * x_).log()
                    / &denominator),
                x_,
            );
            let second = rubi_rhs_int(
                &((Atom::num(1) - &c__ - &d__ * x_).log()
                    / denominator),
                x_,
            );

            rubi_star(Atom::num(1) / 2, first)
                    - rubi_star(Atom::num(1) / 2, second)
        },
    ));
}

fn push_rules_rule_6666(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; c__, d__, e__, f__, n_, x_);
    rules.push(rubi_rule!(
        order: 6666,
        source: "Int[ArcCoth[c_+d_.*x_]/(e_+f_.*x_^n_.),x_Symbol] :=
          1/2 \\[Star] Int[Log[(1+c+d*x)/(c+d*x)]/(e+f*x^n),x] -
          1/2 \\[Star] Int[Log[(-1+c+d*x)/(c+d*x)]/(e+f*x^n),x] /;
        FreeQ[{c,d,e,f},x] && RationalQ[n]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [c__, d__, e__, f__, n_, x_],
        optional: [d__, f__, n_],
        when: { freeq!([c__, d__, e__, f__], x_) && rationalq!(n_) },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let denominator = &e__ + &f__ * x_.pow(&n_);
            let first = rubi_rhs_int(
                &(((Atom::num(1) + &linear) / &linear).log()
                    / &denominator),
                x_,
            );
            let second = rubi_rhs_int(
                &(((-Atom::num(1) + &linear) / linear).log()
                    / denominator),
                x_,
            );

            rubi_star(Atom::num(1) / 2, first)
                    - rubi_star(Atom::num(1) / 2, second)
        },
    ));
}

fn push_rules_rule_6667(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; c__, d__, e__, f__, n_, x_);
    rules.push(rubi_rule!(
        order: 6667,
        source: "Int[ArcTanh[c_+d_.*x_]/(e_+f_.*x_^n_),x_Symbol] :=
          Unintegrable[ArcTanh[c+d*x]/(e+f*x^n),x] /;
        FreeQ[{c,d,e,f,n},x] && Not[RationalQ[n]]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [c__, d__, e__, f__, n_, x_],
        optional: [d__, f__],
        when: { freeq!([c__, d__, e__, f__, n_], x_) && !rationalq!(n_) },
        rhs: {
            rubi_unintegrable((&c__ + &d__ * x_).atanh() / (&e__ + &f__ * x_.pow(&n_)), x_)
        },
    ));
}

fn push_rules_rule_6668(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; c__, d__, e__, f__, n_, x_);
    rules.push(rubi_rule!(
        order: 6668,
        source: "Int[ArcCoth[c_+d_.*x_]/(e_+f_.*x_^n_),x_Symbol] :=
          Unintegrable[ArcCoth[c+d*x]/(e+f*x^n),x] /;
        FreeQ[{c,d,e,f,n},x] && Not[RationalQ[n]]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [c__, d__, e__, f__, n_, x_],
        optional: [d__, f__],
        when: { freeq!([c__, d__, e__, f__, n_], x_) && !rationalq!(n_) },
        rhs: {
            rubi_unintegrable((&c__ + &d__ * x_).acoth() / (&e__ + &f__ * x_.pow(&n_)), x_)
        },
    ));
}

fn push_rules_rule_6669(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        capital_a__,
        capital_b__,
        capital_c__,
        a__,
        b__,
        c__,
        d__,
        p_,
        q_,
        x_
    );
    rules.push(rubi_rule!(
        order: 6669,
        source: "Int[(A_.+B_.*x_+C_.*x_^2)^q_.*(a_.+b_.*ArcTanh[c_+d_.*x_])^p_.,x_Symbol] :=
          1/d \\[Star] Subst[Int[(-C/d^2+C/d^2*x^2)^q*(a+b*ArcTanh[x])^p,x],x,c+d*x] /;
        FreeQ[{a,b,c,d,A,B,C,p,q},x] && EqQ[B*(1-c^2)+2*A*c*d,0] && EqQ[2*c*C-B*d,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (capital_a__ + capital_b__ * x_ + capital_c__ * x_.pow(2)).pow(q_)
            * (a__ + b__ * (c__ + d__ * x_).atanh()).pow(p_),
        with: [capital_a__, capital_b__, capital_c__, q_, a__, b__, c__, d__, p_, x_],
        optional: [capital_a__, capital_b__, capital_c__, q_, a__, b__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__, capital_a__, capital_b__, capital_c__, p_, q_], x_)
                && eqq!(&capital_b__ * (Atom::num(1) - c__.pow(2)) + Atom::num(2) * &capital_a__ * &c__ * &d__, 0)
                && eqq!(Atom::num(2) * &c__ * &capital_c__ - &capital_b__ * &d__, 0)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().rubi_rhs();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let transformed_quadratic = -&capital_c__ / d__.pow(2) + &capital_c__ * sub_atom.pow(2) / d__.pow(2);
            let payload = transformed_quadratic.pow(&q_) * (&a__ + &b__ * sub_atom.atanh()).pow(&p_);
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            let substituted = rubi_subst(
                &primitive,
                substitution_symbol,
                &c__ + &d__ * x_,
            );

            rubi_star(Atom::num(1) / &d__, substituted)
        },
    ));
}

fn push_rules_rule_6670(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        capital_a__,
        capital_b__,
        capital_c__,
        a__,
        b__,
        c__,
        d__,
        p_,
        q_,
        x_
    );
    rules.push(rubi_rule!(
        order: 6670,
        source: "Int[(A_.+B_.*x_+C_.*x_^2)^q_.*(a_.+b_.*ArcCoth[c_+d_.*x_])^p_.,x_Symbol] :=
          1/d \\[Star] Subst[Int[(C/d^2+C/d^2*x^2)^q*(a+b*ArcCoth[x])^p,x],x,c+d*x] /;
        FreeQ[{a,b,c,d,A,B,C,p,q},x] && EqQ[B*(1-c^2)+2*A*c*d,0] && EqQ[2*c*C-B*d,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (capital_a__ + capital_b__ * x_ + capital_c__ * x_.pow(2)).pow(q_)
            * (a__ + b__ * (c__ + d__ * x_).acoth()).pow(p_),
        with: [capital_a__, capital_b__, capital_c__, q_, a__, b__, c__, d__, p_, x_],
        optional: [capital_a__, capital_b__, capital_c__, q_, a__, b__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__, capital_a__, capital_b__, capital_c__, p_, q_], x_)
                && eqq!(&capital_b__ * (Atom::num(1) - c__.pow(2)) + Atom::num(2) * &capital_a__ * &c__ * &d__, 0)
                && eqq!(Atom::num(2) * &c__ * &capital_c__ - &capital_b__ * &d__, 0)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().rubi_rhs();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let transformed_quadratic = &capital_c__ / d__.pow(2) + &capital_c__ * sub_atom.pow(2) / d__.pow(2);
            let payload = transformed_quadratic.pow(&q_) * (&a__ + &b__ * sub_atom.acoth()).pow(&p_);
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            let substituted = rubi_subst(
                &primitive,
                substitution_symbol,
                &c__ + &d__ * x_,
            );

            rubi_star(Atom::num(1) / &d__, substituted)
        },
    ));
}

fn push_rules_rule_6671(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        capital_a__,
        capital_b__,
        capital_c__,
        a__,
        b__,
        c__,
        d__,
        e__,
        f__,
        m_,
        p_,
        q_,
        x_
    );
    rules.push(rubi_rule!(
        order: 6671,
        source: "Int[(e_.+f_.*x_)^m_.*(A_.+B_.*x_+C_.*x_^2)^q_.*(a_.+b_.*ArcTanh[c_+d_.*x_])^p_.,x_Symbol] :=
          1/d \\[Star] Subst[Int[((d*e-c*f)/d+f*x/d)^m*(-C/d^2+C/d^2*x^2)^q*(a+b*ArcTanh[x])^p,x],x,c+d*x] /;
        FreeQ[{a,b,c,d,e,f,A,B,C,m,p,q},x] && EqQ[B*(1-c^2)+2*A*c*d,0] && EqQ[2*c*C-B*d,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (e__ + f__ * x_).pow(m_)
            * (capital_a__ + capital_b__ * x_ + capital_c__ * x_.pow(2)).pow(q_)
            * (a__ + b__ * (c__ + d__ * x_).atanh()).pow(p_),
        with: [e__, f__, m_, capital_a__, capital_b__, capital_c__, q_, a__, b__, c__, d__, p_, x_],
        optional: [e__, f__, m_, capital_a__, capital_b__, capital_c__, q_, a__, b__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, capital_a__, capital_b__, capital_c__, m_, p_, q_], x_)
                && eqq!(&capital_b__ * (Atom::num(1) - c__.pow(2)) + Atom::num(2) * &capital_a__ * &c__ * &d__, 0)
                && eqq!(Atom::num(2) * &c__ * &capital_c__ - &capital_b__ * &d__, 0)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().rubi_rhs();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let transformed_linear = (&d__ * &e__ - &c__ * &f__) / &d__ + &f__ * &sub_atom / &d__;
            let transformed_quadratic = -&capital_c__ / d__.pow(2) + &capital_c__ * sub_atom.pow(2) / d__.pow(2);
            let payload = transformed_linear.pow(&m_)
                * transformed_quadratic.pow(&q_)
                * (&a__ + &b__ * sub_atom.atanh()).pow(&p_);
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            let substituted = rubi_subst(
                &primitive,
                substitution_symbol,
                &c__ + &d__ * x_,
            );

            rubi_star(Atom::num(1) / &d__, substituted)
        },
    ));
}

fn push_rules_rule_6672(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        capital_a__,
        capital_b__,
        capital_c__,
        a__,
        b__,
        c__,
        d__,
        e__,
        f__,
        m_,
        p_,
        q_,
        x_
    );
    rules.push(rubi_rule!(
        order: 6672,
        source: "Int[(e_.+f_.*x_)^m_.*(A_.+B_.*x_+C_.*x_^2)^q_.*(a_.+b_.*ArcCoth[c_+d_.*x_])^p_.,x_Symbol] :=
          1/d \\[Star] Subst[Int[((d*e-c*f)/d+f*x/d)^m*(-C/d^2+C/d^2*x^2)^q*(a+b*ArcCoth[x])^p,x],x,c+d*x] /;
        FreeQ[{a,b,c,d,e,f,A,B,C,m,p,q},x] && EqQ[B*(1-c^2)+2*A*c*d,0] && EqQ[2*c*C-B*d,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (e__ + f__ * x_).pow(m_)
            * (capital_a__ + capital_b__ * x_ + capital_c__ * x_.pow(2)).pow(q_)
            * (a__ + b__ * (c__ + d__ * x_).acoth()).pow(p_),
        with: [e__, f__, m_, capital_a__, capital_b__, capital_c__, q_, a__, b__, c__, d__, p_, x_],
        optional: [e__, f__, m_, capital_a__, capital_b__, capital_c__, q_, a__, b__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, capital_a__, capital_b__, capital_c__, m_, p_, q_], x_)
                && eqq!(&capital_b__ * (Atom::num(1) - c__.pow(2)) + Atom::num(2) * &capital_a__ * &c__ * &d__, 0)
                && eqq!(Atom::num(2) * &c__ * &capital_c__ - &capital_b__ * &d__, 0)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().rubi_rhs();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let transformed_linear = (&d__ * &e__ - &c__ * &f__) / &d__ + &f__ * &sub_atom / &d__;
            let transformed_quadratic = -&capital_c__ / d__.pow(2) + &capital_c__ * sub_atom.pow(2) / d__.pow(2);
            let payload = transformed_linear.pow(&m_)
                * transformed_quadratic.pow(&q_)
                * (&a__ + &b__ * sub_atom.acoth()).pow(&p_);
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            let substituted = rubi_subst(
                &primitive,
                substitution_symbol,
                &c__ + &d__ * x_,
            );

            rubi_star(Atom::num(1) / &d__, substituted)
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
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (a__ + b__ * (c__ + d__ * x_).acoth()).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (a__ + b__ * (c__ + d__ * x_).atanh()).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_2(symbols: &RubiSymbols) -> Atom {
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    (c__ + d__ * x_).acoth() / (e__ + f__ * x_.pow(n_))
}

#[inline(never)]
fn rubi_shared_pattern_3(symbols: &RubiSymbols) -> Atom {
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    (c__ + d__ * x_).atanh() / (e__ + f__ * x_.pow(n_))
}

#[inline(never)]
fn rubi_shared_pattern_4(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (e__ + f__ * x_).pow(m_) * (a__ + b__ * (c__ + d__ * x_).acoth()).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_5(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (e__ + f__ * x_).pow(m_) * (a__ + b__ * (c__ + d__ * x_).atanh()).pow(p_)
}
