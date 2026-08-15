use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_5180(rules);
    push_rules_rule_5181(rules);
    push_rules_rule_5182(rules);
    push_rules_rule_5183(rules);
    push_rules_rule_5184(rules);
    push_rules_rule_5185(rules);
    push_rules_rule_5186(rules);
    push_rules_rule_5187(rules);
    push_rules_rule_5188(rules);
    push_rules_rule_5189(rules);
    push_rules_rule_5190(rules);
    push_rules_rule_5191(rules);
    push_rules_rule_5192(rules);
    push_rules_rule_5193(rules);
    push_rules_rule_5194(rules);
    push_rules_rule_5195(rules);
    push_rules_rule_5196(rules);
    push_rules_rule_5197(rules);
    push_rules_rule_5198(rules);
    push_rules_rule_5199(rules);
    push_rules_rule_5200(rules);
    push_rules_rule_5201(rules);
    push_rules_rule_5202(rules);
    push_rules_rule_5203(rules);
    push_rules_rule_5204(rules);
    push_rules_rule_5205(rules);
    push_rules_rule_5206(rules);
    push_rules_rule_5207(rules);
    push_rules_rule_5208(rules);
    push_rules_rule_5209(rules);
    push_rules_rule_5210(rules);
    push_rules_rule_5211(rules);
    push_rules_rule_5212(rules);
    push_rules_rule_5213(rules);
    push_rules_rule_5214(rules);
    push_rules_rule_5215(rules);
    // Block 19 is disabled in the Rubi source embedded in docs/rubi_pdf_rules.md.

    push_rules_rule_5216(rules);
    push_rules_rule_5217(rules);
    push_rules_rule_5218(rules);
    push_rules_rule_5219(rules);
    push_rules_rule_5220(rules);
    push_rules_rule_5221(rules);
    push_rules_rule_5222(rules);
    push_rules_rule_5223(rules);
    push_rules_rule_5224(rules);
    push_rules_rule_5225(rules);
    push_rules_rule_5226(rules);
    push_rules_rule_5227(rules);
    push_rules_rule_5228(rules);
    push_rules_rule_5229(rules);
    push_rules_rule_5230(rules);
    push_rules_rule_5231(rules);
    push_rules_rule_5232(rules);
    push_rules_rule_5233(rules);
    push_rules_rule_5234(rules);
    push_rules_rule_5235(rules);
    push_rules_rule_5236(rules);
    push_rules_rule_5237(rules);
    push_rules_rule_5238(rules);
    push_rules_rule_5239(rules);
}

fn push_rules_rule_5180(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 5180,
        source: "Int[x_*(a_.+b_.*ArcSin[c_.*x_])^n_./(d_+e_.*x_^2),x_Symbol] :=
          -1/e \\[Star] Subst[Int[(a+b*x)^n*Tan[x],x],x,ArcSin[c*x]] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && IGtQ[n,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: x_ * (a__ + b__ * (c__ * x_).asin()).pow(n_) / (d__ + e__ * x_.pow(2)),
        with: [a__, b__, c__, n_, d__, e__, x_],
        optional: [a__, b__, c__, e__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && igtq!(n_, 0)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let payload = (&a__ + &b__ * &sub_atom).pow(&n_) * sub_atom.tan();
            let primitive = rubi_rhs_int(&payload, sub);
            let substituted = rubi_subst(&primitive, sub, (&c__ * x_).asin());
            rubi_star(-Atom::num(1) / &e__, substituted)
        },
    ));
}

fn push_rules_rule_5181(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 5181,
        source: "Int[x_*(a_.+b_.*ArcCos[c_.*x_])^n_./(d_+e_.*x_^2),x_Symbol] :=
          1/e \\[Star] Subst[Int[(a+b*x)^n*Cot[x],x],x,ArcCos[c*x]] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && IGtQ[n,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: x_ * (a__ + b__ * (c__ * x_).acos()).pow(n_) / (d__ + e__ * x_.pow(2)),
        with: [a__, b__, c__, n_, d__, e__, x_],
        optional: [a__, b__, c__, e__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && igtq!(n_, 0)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let payload = (&a__ + &b__ * &sub_atom).pow(&n_) * sub_atom.cot();
            let primitive = rubi_rhs_int(&payload, sub);
            let substituted = rubi_subst(&primitive, sub, (&c__ * x_).acos());
            rubi_star(Atom::num(1) / &e__, substituted)
        },
    ));
}

fn push_rules_rule_5182(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, n_, p_, x_);
    let rule = rubi_rule!(
        order: 5182,
        source: "Int[x_*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
          (d+e*x^2)^(p+1)*(a+b*ArcSin[c*x])^n/(2*e*(p+1)) +
          b*n/(2*c*(p+1))*Simp[(d+e*x^2)^p/(1-c^2*x^2)^p] \\[Star] Int[(1-c^2*x^2)^(p+1/2)*(a+b*ArcSin[c*x])^(n-1),x] /;
        FreeQ[{a,b,c,d,e,p},x] && EqQ[c^2*d+e,0] && GtQ[n,0] && NeQ[p,-1]",
        desc: "Integration by parts and piecewise constant extraction",
        refs: [],
        pattern: x_ * (d__ + e__ * x_.pow(2)).pow(p_) * (a__ + b__ * (c__ * x_).asin()).pow(n_),
        with: [d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [e__, p_, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, p_], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && gtq!(n_, 0)
                && neq!(p_, -1)
        },
        rhs: {
            let quadratic = &d__ + &e__ * x_.pow(2);
            let denominator = Atom::num(1) - c__.pow(2) * x_.pow(2);
            let argument = &a__ + &b__ * (&c__ * x_).asin();
            let recursive = denominator

                .pow(&p_ + half_integer_atom(1))
                * argument.pow(&n_ - Atom::num(1));
            rubi_simp(&(quadratic.pow(&p_ + Atom::num(1)) * argument.pow(&n_)
                    / (Atom::num(2) * &e__ * (&p_ + Atom::num(1)))), x_)
                    + rubi_star(&b__ * &n_
                            * rubi_simp(&(quadratic.pow(&p_) / denominator.pow(&p_)), x_)
                            / (Atom::num(2) * &c__ * (&p_ + Atom::num(1))), rubi_rhs_int(&recursive, x_))
        },
    );
    rules.push(rule.with_early_x_dependent(x_));
}

fn push_rules_rule_5183(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, n_, p_, x_);
    let rule = rubi_rule!(
        order: 5183,
        source: "Int[x_*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
          (d+e*x^2)^(p+1)*(a+b*ArcCos[c*x])^n/(2*e*(p+1)) -
          b*n/(2*c*(p+1))*Simp[(d+e*x^2)^p/(1-c^2*x^2)^p] \\[Star] Int[(1-c^2*x^2)^(p+1/2)*(a+b*ArcCos[c*x])^(n-1),x] /;
        FreeQ[{a,b,c,d,e,p},x] && EqQ[c^2*d+e,0] && GtQ[n,0] && NeQ[p,-1]",
        desc: "Integration by parts and piecewise constant extraction",
        refs: [],
        pattern: x_ * (d__ + e__ * x_.pow(2)).pow(p_) * (a__ + b__ * (c__ * x_).acos()).pow(n_),
        with: [d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [e__, p_, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, p_], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && gtq!(n_, 0)
                && neq!(p_, -1)
        },
        rhs: {
            let quadratic = &d__ + &e__ * x_.pow(2);
            let denominator = Atom::num(1) - c__.pow(2) * x_.pow(2);
            let argument = &a__ + &b__ * (&c__ * x_).acos();
            let recursive = denominator

                .pow(&p_ + half_integer_atom(1))
                * argument.pow(&n_ - Atom::num(1));
            rubi_simp(&(quadratic.pow(&p_ + Atom::num(1)) * argument.pow(&n_)
                    / (Atom::num(2) * &e__ * (&p_ + Atom::num(1)))), x_)
                    + rubi_star(-&b__ * &n_
                            * rubi_simp(&(quadratic.pow(&p_) / denominator.pow(&p_)), x_)
                            / (Atom::num(2) * &c__ * (&p_ + Atom::num(1))), rubi_rhs_int(&recursive, x_))
        },
    );
    rules.push(rule.with_early_x_dependent(x_));
}

fn push_rules_rule_5184(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 5184,
        source: "Int[(a_.+b_.*ArcSin[c_.*x_])^n_./(x_*(d_+e_.*x_^2)),x_Symbol] :=
          1/d \\[Star] Subst[Int[(a+b*x)^n/(Cos[x]*Sin[x]),x],x,ArcSin[c*x]] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && IGtQ[n,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (a__ + b__ * (c__ * x_).asin()).pow(n_) / (x_ * (d__ + e__ * x_.pow(2))),
        with: [a__, b__, c__, n_, d__, e__, x_],
        optional: [a__, b__, c__, e__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && igtq!(n_, 0)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let payload = (&a__ + &b__ * &sub_atom).pow(&n_) / (sub_atom.cos() * sub_atom.sin());
            let primitive = rubi_rhs_int(&payload, sub);
            let substituted = rubi_subst(&primitive, sub, (&c__ * x_).asin());
            rubi_star(Atom::num(1) / &d__, substituted)
        },
    ));
}

fn push_rules_rule_5185(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 5185,
        source: "Int[(a_.+b_.*ArcCos[c_.*x_])^n_./(x_*(d_+e_.*x_^2)),x_Symbol] :=
          -1/d \\[Star] Subst[Int[(a+b*x)^n/(Cos[x]*Sin[x]),x],x,ArcCos[c*x]] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && IGtQ[n,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (a__ + b__ * (c__ * x_).acos()).pow(n_) / (x_ * (d__ + e__ * x_.pow(2))),
        with: [a__, b__, c__, n_, d__, e__, x_],
        optional: [a__, b__, c__, e__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && igtq!(n_, 0)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let payload = (&a__ + &b__ * &sub_atom).pow(&n_) / (sub_atom.cos() * sub_atom.sin());
            let primitive = rubi_rhs_int(&payload, sub);
            let substituted = rubi_subst(&primitive, sub, (&c__ * x_).acos());
            rubi_star(-Atom::num(1) / &d__, substituted)
        },
    ));
}

fn push_rules_rule_5186(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5186,
        source: "Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
          (f*x)^(m+1)*(d+e*x^2)^(p+1)*(a+b*ArcSin[c*x])^n/(d*f*(m+1)) -
          b*c*n/(f*(m+1))*Simp[(d+e*x^2)^p/(1-c^2*x^2)^p] \\[Star] Int[(f*x)^(m+1)*(1-c^2*x^2)^(p+1/2)*(a+b*ArcSin[c*x])^(n-1),x] /;
        FreeQ[{a,b,c,d,e,f,m,p},x] && EqQ[c^2*d+e,0] && GtQ[n,0] && EqQ[m+2*p+3,0] && NeQ[m,-1]",
        desc: "Integration by parts and piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [f__, m_, d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [f__, e__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, p_], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && gtq!(n_, 0)
                && eqq!(&m_ + Atom::num(2) * &p_ + Atom::num(3), 0)
                && neq!(m_, -1)
        },
        rhs: {
            let scaled = &f__ * x_;
            let quadratic = &d__ + &e__ * x_.pow(2);
            let denominator = Atom::num(1) - c__.pow(2) * x_.pow(2);
            let argument = &a__ + &b__ * (&c__ * x_).asin();
            let recursive = scaled.pow(&m_ + Atom::num(1))
                * denominator.pow(&p_ + half_integer_atom(1))
                * argument.pow(&n_ - Atom::num(1));
            rubi_simp(&(scaled.pow(&m_ + Atom::num(1))
                    * quadratic.pow(&p_ + Atom::num(1))
                    * argument.pow(&n_)
                    / (&d__ * &f__ * (&m_ + Atom::num(1)))), x_)
                    + rubi_star(-&b__ * &c__ * &n_
                            * rubi_simp(&(quadratic.pow(&p_) / denominator.pow(&p_)), x_)
                            / (&f__ * (&m_ + Atom::num(1))), rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_5187(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5187,
        source: "Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
          (f*x)^(m+1)*(d+e*x^2)^(p+1)*(a+b*ArcCos[c*x])^n/(d*f*(m+1)) +
          b*c*n/(f*(m+1))*Simp[(d+e*x^2)^p/(1-c^2*x^2)^p] \\[Star] Int[(f*x)^(m+1)*(1-c^2*x^2)^(p+1/2)*(a+b*ArcCos[c*x])^(n-1),x] /;
        FreeQ[{a,b,c,d,e,f,m,p},x] && EqQ[c^2*d+e,0] && GtQ[n,0] && EqQ[m+2*p+3,0] && NeQ[m,-1]",
        desc: "Integration by parts and piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [f__, m_, d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [f__, e__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, p_], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && gtq!(n_, 0)
                && eqq!(&m_ + Atom::num(2) * &p_ + Atom::num(3), 0)
                && neq!(m_, -1)
        },
        rhs: {
            let scaled = &f__ * x_;
            let quadratic = &d__ + &e__ * x_.pow(2);
            let denominator = Atom::num(1) - c__.pow(2) * x_.pow(2);
            let argument = &a__ + &b__ * (&c__ * x_).acos();
            let recursive = scaled.pow(&m_ + Atom::num(1))
                * denominator.pow(&p_ + half_integer_atom(1))
                * argument.pow(&n_ - Atom::num(1));
            rubi_simp(&(scaled.pow(&m_ + Atom::num(1))
                    * quadratic.pow(&p_ + Atom::num(1))
                    * argument.pow(&n_)
                    / (&d__ * &f__ * (&m_ + Atom::num(1)))), x_)
                    + rubi_star(&b__ * &c__ * &n_
                            * rubi_simp(&(quadratic.pow(&p_) / denominator.pow(&p_)), x_)
                            / (&f__ * (&m_ + Atom::num(1))), rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_5188(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, p_, x_);
    let rule = rubi_rule!(
        order: 5188,
        source: "Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_.*x_])/x_,x_Symbol] :=
          (d+e*x^2)^p*(a+b*ArcSin[c*x])/(2*p) -
          b*c*d^p/(2*p) \\[Star] Int[(1-c^2*x^2)^(p-1/2),x] +
          d \\[Star] Int[(d+e*x^2)^(p-1)*(a+b*ArcSin[c*x])/x,x] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && IGtQ[p,0]",
        desc: "Inverted integration by parts",
        refs: [],
        pattern: (d__ + e__ * x_.pow(2)).pow(p_) * (a__ + b__ * (c__ * x_).asin()) / x_,
        with: [d__, e__, p_, a__, b__, c__, x_],
        optional: [e__, p_, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && igtq!(p_, 0)
        },
        rhs: {
            let quadratic = &d__ + &e__ * x_.pow(2);
            let denominator = Atom::num(1) - c__.pow(2) * x_.pow(2);
            let argument = &a__ + &b__ * (&c__ * x_).asin();
            let recursive_1 = denominator.pow(&p_ - half_integer_atom(1));
            let recursive_2 = quadratic.pow(&p_ - Atom::num(1)) * &argument / x_;
            rubi_simp(&(quadratic.pow(&p_) * argument / (Atom::num(2) * &p_)), x_)
                    + rubi_star(-&b__ * &c__ * d__.pow(&p_) / (Atom::num(2) * &p_), rubi_rhs_int(&recursive_1, x_))
                    + rubi_star(d__, rubi_rhs_int(&recursive_2, x_))
        },
    );
    rules.push(rule.with_early_x_dependent(x_));
}

fn push_rules_rule_5189(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, p_, x_);
    let rule = rubi_rule!(
        order: 5189,
        source: "Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_.*x_])/x_,x_Symbol] :=
          (d+e*x^2)^p*(a+b*ArcCos[c*x])/(2*p) +
          b*c*d^p/(2*p) \\[Star] Int[(1-c^2*x^2)^(p-1/2),x] +
          d \\[Star] Int[(d+e*x^2)^(p-1)*(a+b*ArcCos[c*x])/x,x] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && IGtQ[p,0]",
        desc: "Inverted integration by parts",
        refs: [],
        pattern: (d__ + e__ * x_.pow(2)).pow(p_) * (a__ + b__ * (c__ * x_).acos()) / x_,
        with: [d__, e__, p_, a__, b__, c__, x_],
        optional: [e__, p_, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && igtq!(p_, 0)
        },
        rhs: {
            let quadratic = &d__ + &e__ * x_.pow(2);
            let denominator = Atom::num(1) - c__.pow(2) * x_.pow(2);
            let argument = &a__ + &b__ * (&c__ * x_).acos();
            let recursive_1 = denominator.pow(&p_ - half_integer_atom(1));
            let recursive_2 = quadratic.pow(&p_ - Atom::num(1)) * &argument / x_;
            rubi_simp(&(quadratic.pow(&p_) * argument / (Atom::num(2) * &p_)), x_)
                    + rubi_star(&b__ * &c__ * d__.pow(&p_) / (Atom::num(2) * &p_), rubi_rhs_int(&recursive_1, x_))
                    + rubi_star(d__, rubi_rhs_int(&recursive_2, x_))
        },
    );
    rules.push(rule.with_early_x_dependent(x_));
}

fn push_rules_rule_5190(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 5190,
        source: "Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_.*x_]),x_Symbol] :=
          (f*x)^(m+1)*(d+e*x^2)^p*(a+b*ArcSin[c*x])/(f*(m+1)) -
          b*c*d^p/(f*(m+1)) \\[Star] Int[(f*x)^(m+1)*(1-c^2*x^2)^(p-1/2),x] -
          2*e*p/(f^2*(m+1)) \\[Star] Int[(f*x)^(m+2)*(d+e*x^2)^(p-1)*(a+b*ArcSin[c*x]),x] /;
        FreeQ[{a,b,c,d,e,f},x] && EqQ[c^2*d+e,0] && IGtQ[p,0] && ILtQ[(m+1)/2,0]",
        desc: "Inverted integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [f__, m_, d__, e__, p_, a__, b__, c__, x_],
        optional: [f__, e__, p_, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && igtq!(p_, 0)
                && iltq!((&m_ + Atom::num(1)) / Atom::num(2), 0)
        },
        rhs: {
            let scaled = &f__ * x_;
            let quadratic = &d__ + &e__ * x_.pow(2);
            let denominator = Atom::num(1) - c__.pow(2) * x_.pow(2);
            let argument = &a__ + &b__ * (&c__ * x_).asin();
            let recursive_1 = scaled.pow(&m_ + Atom::num(1)) * denominator.pow(&p_ - half_integer_atom(1));
            let recursive_2 = scaled.pow(&m_ + Atom::num(2)) * quadratic.pow(&p_ - Atom::num(1)) * &argument;
            rubi_simp(&(scaled.pow(&m_ + Atom::num(1)) * quadratic.pow(&p_) * argument
                    / (&f__ * (&m_ + Atom::num(1)))), x_)
                    + rubi_star(-&b__ * &c__ * d__.pow(&p_) / (&f__ * (&m_ + Atom::num(1))), rubi_rhs_int(&recursive_1, x_))
                    + rubi_star(-Atom::num(2) * &e__ * &p_
                            / (f__.pow(2) * (&m_ + Atom::num(1))), rubi_rhs_int(&recursive_2, x_))
        },
    ));
}

fn push_rules_rule_5191(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 5191,
        source: "Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_.*x_]),x_Symbol] :=
          (f*x)^(m+1)*(d+e*x^2)^p*(a+b*ArcCos[c*x])/(f*(m+1)) +
          b*c*d^p/(f*(m+1)) \\[Star] Int[(f*x)^(m+1)*(1-c^2*x^2)^(p-1/2),x] -
          2*e*p/(f^2*(m+1)) \\[Star] Int[(f*x)^(m+2)*(d+e*x^2)^(p-1)*(a+b*ArcCos[c*x]),x] /;
        FreeQ[{a,b,c,d,e,f},x] && EqQ[c^2*d+e,0] && IGtQ[p,0] && ILtQ[(m+1)/2,0]",
        desc: "Inverted integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [f__, m_, d__, e__, p_, a__, b__, c__, x_],
        optional: [f__, e__, p_, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && igtq!(p_, 0)
                && iltq!((&m_ + Atom::num(1)) / Atom::num(2), 0)
        },
        rhs: {
            let scaled = &f__ * x_;
            let quadratic = &d__ + &e__ * x_.pow(2);
            let denominator = Atom::num(1) - c__.pow(2) * x_.pow(2);
            let argument = &a__ + &b__ * (&c__ * x_).acos();
            let recursive_1 = scaled.pow(&m_ + Atom::num(1)) * denominator.pow(&p_ - half_integer_atom(1));
            let recursive_2 = scaled.pow(&m_ + Atom::num(2)) * quadratic.pow(&p_ - Atom::num(1)) * &argument;
            rubi_simp(&(scaled.pow(&m_ + Atom::num(1)) * quadratic.pow(&p_) * argument
                    / (&f__ * (&m_ + Atom::num(1)))), x_)
                    + rubi_star(&b__ * &c__ * d__.pow(&p_) / (&f__ * (&m_ + Atom::num(1))), rubi_rhs_int(&recursive_1, x_))
                    + rubi_star(-Atom::num(2) * &e__ * &p_
                            / (f__.pow(2) * (&m_ + Atom::num(1))), rubi_rhs_int(&recursive_2, x_))
        },
    ));
}

fn push_rules_rule_5192(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 5192,
        source: "Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_.*x_]),x_Symbol] :=
          With[{u=IntHide[(f*x)^m*(d+e*x^2)^p,x]},
          (a+b*ArcSin[c*x]) \\[Star] u - b*c \\[Star] Int[SimplifyIntegrand[u/Sqrt[1-c^2*x^2],x],x]] /;
        FreeQ[{a,b,c,d,e,f,m},x] && EqQ[c^2*d+e,0] && IGtQ[p,0]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [f__, m_, d__, e__, p_, a__, b__, c__, x_],
        optional: [f__, e__, p_, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && igtq!(p_, 0)
        },
        rhs: {
            let argument = &a__ + &b__ * (&c__ * x_).asin();
            let u = rubi_int_hide(
                &((&f__ * x_).pow(&m_) * (&d__ + &e__ * x_.pow(2)).pow(&p_)),
                x_,
            ).rubi_rhs();
            let recursive = rubi_simplify_integrand(&(&u / (Atom::num(1) - c__.pow(2) * x_.pow(2)).sqrt()), x_);
            rubi_star(argument, u)
                    + rubi_star(-&b__ * &c__, rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_5193(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 5193,
        source: "Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_.*x_]),x_Symbol] :=
          With[{u=IntHide[(f*x)^m*(d+e*x^2)^p,x]},
          (a+b*ArcCos[c*x]) \\[Star] u + b*c \\[Star] Int[SimplifyIntegrand[u/Sqrt[1-c^2*x^2],x],x]] /;
        FreeQ[{a,b,c,d,e,f,m},x] && EqQ[c^2*d+e,0] && IGtQ[p,0]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [f__, m_, d__, e__, p_, a__, b__, c__, x_],
        optional: [f__, e__, p_, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && igtq!(p_, 0)
        },
        rhs: {
            let argument = &a__ + &b__ * (&c__ * x_).acos();
            let u = rubi_int_hide(
                &((&f__ * x_).pow(&m_) * (&d__ + &e__ * x_.pow(2)).pow(&p_)),
                x_,
            ).rubi_rhs();
            let recursive = rubi_simplify_integrand(&(&u / (Atom::num(1) - c__.pow(2) * x_.pow(2)).sqrt()), x_);
            rubi_star(argument, u) + rubi_star(&b__ * &c__, rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_5194(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 5194,
        source: "Int[x_^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSin[c_.*x_]),x_Symbol] :=
          With[{u=IntHide[x^m*(d+e*x^2)^p,x]},
          (a+b*ArcSin[c*x]) \\[Star] u -
          b*c*Simp[Sqrt[d+e*x^2]/Sqrt[1-c^2*x^2]] \\[Star] Int[SimplifyIntegrand[u/Sqrt[d+e*x^2],x],x]] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && IntegerQ[p-1/2] && NeQ[p,-1/2] && (IGtQ[(m+1)/2,0] || ILtQ[(m+2*p+3)/2,0])",
        desc: "Integration by parts and piecewise constant extraction",
        refs: [],
        pattern: x_.pow(m_) * (d__ + e__ * x_.pow(2)).pow(p_) * (a__ + b__ * (c__ * x_).asin()),
        with: [m_, d__, e__, p_, a__, b__, c__, x_],
        optional: [e__, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && integerq!(&p_ - half_integer_atom(1))
                && neq!(p_, -half_integer_atom(1))
                && (igtq!((&m_ + Atom::num(1)) / Atom::num(2), 0)
                    || iltq!((&m_ + Atom::num(2) * &p_ + Atom::num(3)) / Atom::num(2), 0))
        },
        rhs: {
            let quadratic = &d__ + &e__ * x_.pow(2);
            let denominator = Atom::num(1) - c__.pow(2) * x_.pow(2);
            let argument = &a__ + &b__ * (&c__ * x_).asin();
            let u = rubi_int_hide(&(x_.pow(&m_) * quadratic.pow(&p_)), x_).rubi_rhs();
            let recursive = rubi_simplify_integrand(&(&u / quadratic.sqrt()), x_);
            rubi_star(argument, u)
                    - rubi_star(&b__ * &c__ * rubi_simp(&(quadratic.sqrt() / denominator.sqrt()), x_), rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_5195(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 5195,
        source: "Int[x_^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCos[c_.*x_]),x_Symbol] :=
          With[{u=IntHide[x^m*(d+e*x^2)^p,x]},
          (a+b*ArcCos[c*x]) \\[Star] u +
          b*c*Simp[Sqrt[d+e*x^2]/Sqrt[1-c^2*x^2]] \\[Star] Int[SimplifyIntegrand[u/Sqrt[d+e*x^2],x],x]] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && IntegerQ[p-1/2] && NeQ[p,-1/2] && (IGtQ[(m+1)/2,0] || ILtQ[(m+2*p+3)/2,0])",
        desc: "Integration by parts and piecewise constant extraction",
        refs: [],
        pattern: x_.pow(m_) * (d__ + e__ * x_.pow(2)).pow(p_) * (a__ + b__ * (c__ * x_).acos()),
        with: [m_, d__, e__, p_, a__, b__, c__, x_],
        optional: [e__, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && integerq!(&p_ - half_integer_atom(1))
                && neq!(p_, -half_integer_atom(1))
                && (igtq!((&m_ + Atom::num(1)) / Atom::num(2), 0)
                    || iltq!((&m_ + Atom::num(2) * &p_ + Atom::num(3)) / Atom::num(2), 0))
        },
        rhs: {
            let quadratic = &d__ + &e__ * x_.pow(2);
            let denominator = Atom::num(1) - c__.pow(2) * x_.pow(2);
            let argument = &a__ + &b__ * (&c__ * x_).acos();
            let u = rubi_int_hide(&(x_.pow(&m_) * quadratic.pow(&p_)), x_).rubi_rhs();
            let recursive = rubi_simplify_integrand(&(&u / quadratic.sqrt()), x_);
            rubi_star(argument, u)
                    + rubi_star(&b__ * &c__ * rubi_simp(&(quadratic.sqrt() / denominator.sqrt()), x_), rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_5196(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5196,
        source: "Int[(f_.*x_)^m_*Sqrt[d_+e_.*x_^2]*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
          (f*x)^(m+1)*Sqrt[d+e*x^2]*(a+b*ArcSin[c*x])^n/(f*(m+1)) -
          b*c*n/(f*(m+1))*Simp[Sqrt[d+e*x^2]/Sqrt[1-c^2*x^2]] \\[Star] Int[(f*x)^(m+1)*(a+b*ArcSin[c*x])^(n-1),x] +
          c^2/(f^2*(m+1))*Simp[Sqrt[d+e*x^2]/Sqrt[1-c^2*x^2]] \\[Star] Int[(f*x)^(m+2)*(a+b*ArcSin[c*x])^n/Sqrt[1-c^2*x^2],x] /;
        FreeQ[{a,b,c,d,e,f},x] && EqQ[c^2*d+e,0] && GtQ[n,0] && LtQ[m,-1]",
        desc: "Inverted integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [f__, m_, d__, e__, a__, b__, c__, n_, x_],
        optional: [f__, e__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && gtq!(n_, 0)
                && ltq!(m_, -1)
        },
        rhs: {
            let scaled = &f__ * x_;
            let quadratic = &d__ + &e__ * x_.pow(2);
            let denominator = Atom::num(1) - c__.pow(2) * x_.pow(2);
            let argument = &a__ + &b__ * (&c__ * x_).asin();
            let ratio = rubi_simp(&(quadratic.sqrt() / denominator.sqrt()), x_);
            let recursive_1 = scaled.pow(&m_ + Atom::num(1)) * argument.pow(&n_ - Atom::num(1));
            let recursive_2 = scaled.pow(&m_ + Atom::num(2)) * argument.pow(&n_) / denominator.sqrt();
            rubi_simp(&(scaled.pow(&m_ + Atom::num(1)) * quadratic.sqrt() * argument.pow(&n_)
                    / (&f__ * (&m_ + Atom::num(1)))), x_)
                    - rubi_star(&b__ * &c__ * &n_ / (&f__ * (&m_ + Atom::num(1))) * &ratio, rubi_rhs_int(&recursive_1, x_))
                    + rubi_star(c__.pow(2) / (f__.pow(2) * (&m_ + Atom::num(1))) * ratio, rubi_rhs_int(&recursive_2, x_))
        },
    ));
}

fn push_rules_rule_5197(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5197,
        source: "Int[(f_.*x_)^m_*Sqrt[d_+e_.*x_^2]*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
          (f*x)^(m+1)*Sqrt[d+e*x^2]*(a+b*ArcCos[c*x])^n/(f*(m+1)) +
          b*c*n/(f*(m+1))*Simp[Sqrt[d+e*x^2]/Sqrt[1-c^2*x^2]] \\[Star] Int[(f*x)^(m+1)*(a+b*ArcCos[c*x])^(n-1),x] +
          c^2/(f^2*(m+1))*Simp[Sqrt[d+e*x^2]/Sqrt[1-c^2*x^2]] \\[Star] Int[(f*x)^(m+2)*(a+b*ArcCos[c*x])^n/Sqrt[1-c^2*x^2],x] /;
        FreeQ[{a,b,c,d,e,f},x] && EqQ[c^2*d+e,0] && GtQ[n,0] && LtQ[m,-1]",
        desc: "Inverted integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [f__, m_, d__, e__, a__, b__, c__, n_, x_],
        optional: [f__, e__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && gtq!(n_, 0)
                && ltq!(m_, -1)
        },
        rhs: {
            let scaled = &f__ * x_;
            let quadratic = &d__ + &e__ * x_.pow(2);
            let denominator = Atom::num(1) - c__.pow(2) * x_.pow(2);
            let argument = &a__ + &b__ * (&c__ * x_).acos();
            let ratio = rubi_simp(&(quadratic.sqrt() / denominator.sqrt()), x_);
            let recursive_1 = scaled.pow(&m_ + Atom::num(1)) * argument.pow(&n_ - Atom::num(1));
            let recursive_2 = scaled.pow(&m_ + Atom::num(2)) * argument.pow(&n_) / denominator.sqrt();
            rubi_simp(&(scaled.pow(&m_ + Atom::num(1)) * quadratic.sqrt() * argument.pow(&n_)
                    / (&f__ * (&m_ + Atom::num(1)))), x_)
                    + rubi_star(&b__ * &c__ * &n_ / (&f__ * (&m_ + Atom::num(1))) * &ratio, rubi_rhs_int(&recursive_1, x_))
                    + rubi_star(c__.pow(2) / (f__.pow(2) * (&m_ + Atom::num(1))) * ratio, rubi_rhs_int(&recursive_2, x_))
        },
    ));
}

fn push_rules_rule_5198(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5198,
        source: "Int[(f_.*x_)^m_*Sqrt[d_+e_.*x_^2]*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
          (f*x)^(m+1)*Sqrt[d+e*x^2]*(a+b*ArcSin[c*x])^n/(f*(m+2)) -
          b*c*n/(f*(m+2))*Simp[Sqrt[d+e*x^2]/Sqrt[1-c^2*x^2]] \\[Star] Int[(f*x)^(m+1)*(a+b*ArcSin[c*x])^(n-1),x] +
          1/(m+2)*Simp[Sqrt[d+e*x^2]/Sqrt[1-c^2*x^2]] \\[Star] Int[(f*x)^m*(a+b*ArcSin[c*x])^n/Sqrt[1-c^2*x^2],x] /;
        FreeQ[{a,b,c,d,e,f,m},x] && EqQ[c^2*d+e,0] && GtQ[n,0] && (IGtQ[m,-2] || EqQ[n,1])",
        desc: "Inverted integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [f__, m_, d__, e__, a__, b__, c__, n_, x_],
        optional: [f__, e__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && gtq!(n_, 0)
                && (igtq!(m_, -2) || eqq!(n_, 1))
        },
        rhs: {
            let scaled = &f__ * x_;
            let quadratic = &d__ + &e__ * x_.pow(2);
            let denominator = Atom::num(1) - c__.pow(2) * x_.pow(2);
            let argument = &a__ + &b__ * (&c__ * x_).asin();
            let ratio = rubi_simp(&(quadratic.sqrt() / denominator.sqrt()), x_);
            let recursive_1 = scaled.pow(&m_ + Atom::num(1)) * argument.pow(&n_ - Atom::num(1));
            let recursive_2 = scaled.pow(&m_) * argument.pow(&n_) / denominator.sqrt();
            rubi_simp(&(scaled.pow(&m_ + Atom::num(1)) * quadratic.sqrt() * argument.pow(&n_)
                    / (&f__ * (&m_ + Atom::num(2)))), x_)
                    - rubi_star(&b__ * &c__ * &n_ / (&f__ * (&m_ + Atom::num(2))) * &ratio, rubi_rhs_int(&recursive_1, x_))
                    + rubi_star(ratio / (&m_ + Atom::num(2)), rubi_rhs_int(&recursive_2, x_))
        },
    ));
}

fn push_rules_rule_5199(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5199,
        source: "Int[(f_.*x_)^m_*Sqrt[d_+e_.*x_^2]*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
          (f*x)^(m+1)*Sqrt[d+e*x^2]*(a+b*ArcCos[c*x])^n/(f*(m+2)) +
          b*c*n/(f*(m+2))*Simp[Sqrt[d+e*x^2]/Sqrt[1-c^2*x^2]] \\[Star] Int[(f*x)^(m+1)*(a+b*ArcCos[c*x])^(n-1),x] +
          1/(m+2)*Simp[Sqrt[d+e*x^2]/Sqrt[1-c^2*x^2]] \\[Star] Int[(f*x)^m*(a+b*ArcCos[c*x])^n/Sqrt[1-c^2*x^2],x] /;
        FreeQ[{a,b,c,d,e,f,m},x] && EqQ[c^2*d+e,0] && GtQ[n,0] && (IGtQ[m,-2] || EqQ[n,1])",
        desc: "Inverted integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [f__, m_, d__, e__, a__, b__, c__, n_, x_],
        optional: [f__, e__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && gtq!(n_, 0)
                && (igtq!(m_, -2) || eqq!(n_, 1))
        },
        rhs: {
            let scaled = &f__ * x_;
            let quadratic = &d__ + &e__ * x_.pow(2);
            let denominator = Atom::num(1) - c__.pow(2) * x_.pow(2);
            let argument = &a__ + &b__ * (&c__ * x_).acos();
            let ratio = rubi_simp(&(quadratic.sqrt() / denominator.sqrt()), x_);
            let recursive_1 = scaled.pow(&m_ + Atom::num(1)) * argument.pow(&n_ - Atom::num(1));
            let recursive_2 = scaled.pow(&m_) * argument.pow(&n_) / denominator.sqrt();
            rubi_simp(&(scaled.pow(&m_ + Atom::num(1)) * quadratic.sqrt() * argument.pow(&n_)
                    / (&f__ * (&m_ + Atom::num(2)))), x_)
                    + rubi_star(&b__ * &c__ * &n_ / (&f__ * (&m_ + Atom::num(2))) * &ratio, rubi_rhs_int(&recursive_1, x_))
                    + rubi_star(ratio / (&m_ + Atom::num(2)), rubi_rhs_int(&recursive_2, x_))
        },
    ));
}

fn push_rules_rule_5200(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5200,
        source: "Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
          (f*x)^(m+1)*(d+e*x^2)^p*(a+b*ArcSin[c*x])^n/(f*(m+1)) -
          2*e*p/(f^2*(m+1)) \\[Star] Int[(f*x)^(m+2)*(d+e*x^2)^(p-1)*(a+b*ArcSin[c*x])^n,x] -
          b*c*n/(f*(m+1))*Simp[(d+e*x^2)^p/(1-c^2*x^2)^p] \\[Star] Int[(f*x)^(m+1)*(1-c^2*x^2)^(p-1/2)*(a+b*ArcSin[c*x])^(n-1),x] /;
        FreeQ[{a,b,c,d,e,f},x] && EqQ[c^2*d+e,0] && GtQ[n,0] && GtQ[p,0] && LtQ[m,-1]",
        desc: "Inverted integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [f__, m_, d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [f__, e__, p_, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && gtq!(n_, 0)
                && gtq!(p_, 0)
                && ltq!(m_, -1)
        },
        rhs: {
            let scaled = &f__ * x_;
            let quadratic = &d__ + &e__ * x_.pow(2);
            let denominator = Atom::num(1) - c__.pow(2) * x_.pow(2);
            let argument = &a__ + &b__ * (&c__ * x_).asin();
            let recursive_1 =
                scaled.pow(&m_ + Atom::num(2)) * quadratic.pow(&p_ - Atom::num(1)) * argument.pow(&n_);
            let recursive_2 = scaled.pow(&m_ + Atom::num(1))
                * denominator.pow(&p_ - half_integer_atom(1))
                * argument.pow(&n_ - Atom::num(1));
            rubi_simp(&(scaled.pow(&m_ + Atom::num(1)) * quadratic.pow(&p_) * argument.pow(&n_)
                    / (&f__ * (&m_ + Atom::num(1)))), x_)
                    - rubi_star(Atom::num(2) * &e__ * &p_ / (f__.pow(2) * (&m_ + Atom::num(1))), rubi_rhs_int(&recursive_1, x_))
                    - rubi_star(&b__ * &c__ * &n_ / (&f__ * (&m_ + Atom::num(1)))
                            * rubi_simp(&(quadratic.pow(&p_) / denominator.pow(&p_)), x_), rubi_rhs_int(&recursive_2, x_))
        },
    ));
}

fn push_rules_rule_5201(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5201,
        source: "Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
          (f*x)^(m+1)*(d+e*x^2)^p*(a+b*ArcCos[c*x])^n/(f*(m+1)) -
          2*e*p/(f^2*(m+1)) \\[Star] Int[(f*x)^(m+2)*(d+e*x^2)^(p-1)*(a+b*ArcCos[c*x])^n,x] +
          b*c*n/(f*(m+1))*Simp[(d+e*x^2)^p/(1-c^2*x^2)^p] \\[Star] Int[(f*x)^(m+1)*(1-c^2*x^2)^(p-1/2)*(a+b*ArcCos[c*x])^(n-1),x] /;
        FreeQ[{a,b,c,d,e,f},x] && EqQ[c^2*d+e,0] && GtQ[n,0] && GtQ[p,0] && LtQ[m,-1]",
        desc: "Inverted integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [f__, m_, d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [f__, e__, p_, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && gtq!(n_, 0)
                && gtq!(p_, 0)
                && ltq!(m_, -1)
        },
        rhs: {
            let scaled = &f__ * x_;
            let quadratic = &d__ + &e__ * x_.pow(2);
            let denominator = Atom::num(1) - c__.pow(2) * x_.pow(2);
            let argument = &a__ + &b__ * (&c__ * x_).acos();
            let recursive_1 =
                scaled.pow(&m_ + Atom::num(2)) * quadratic.pow(&p_ - Atom::num(1)) * argument.pow(&n_);
            let recursive_2 = scaled.pow(&m_ + Atom::num(1))
                * denominator.pow(&p_ - half_integer_atom(1))
                * argument.pow(&n_ - Atom::num(1));
            rubi_simp(&(scaled.pow(&m_ + Atom::num(1)) * quadratic.pow(&p_) * argument.pow(&n_)
                    / (&f__ * (&m_ + Atom::num(1)))), x_)
                    - rubi_star(Atom::num(2) * &e__ * &p_ / (f__.pow(2) * (&m_ + Atom::num(1))), rubi_rhs_int(&recursive_1, x_))
                    + rubi_star(&b__ * &c__ * &n_ / (&f__ * (&m_ + Atom::num(1)))
                            * rubi_simp(&(quadratic.pow(&p_) / denominator.pow(&p_)), x_), rubi_rhs_int(&recursive_2, x_))
        },
    ));
}

fn push_rules_rule_5202(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5202,
        source: "Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
          (f*x)^(m+1)*(d+e*x^2)^p*(a+b*ArcSin[c*x])^n/(f*(m+2*p+1)) +
          2*d*p/(m+2*p+1) \\[Star] Int[(f*x)^m*(d+e*x^2)^(p-1)*(a+b*ArcSin[c*x])^n,x] -
          b*c*n/(f*(m+2*p+1))*Simp[(d+e*x^2)^p/(1-c^2*x^2)^p] \\[Star] Int[(f*x)^(m+1)*(1-c^2*x^2)^(p-1/2)*(a+b*ArcSin[c*x])^(n-1),x] /;
        FreeQ[{a,b,c,d,e,f,m},x] && EqQ[c^2*d+e,0] && GtQ[n,0] && GtQ[p,0] && Not[LtQ[m,-1]]",
        desc: "Inverted integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [f__, m_, d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [f__, e__, p_, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && gtq!(n_, 0)
                && gtq!(p_, 0)
                && !ltq!(m_, -1)
        },
        rhs: {
            let scaled = &f__ * x_;
            let quadratic = &d__ + &e__ * x_.pow(2);
            let denominator = Atom::num(1) - c__.pow(2) * x_.pow(2);
            let argument = &a__ + &b__ * (&c__ * x_).asin();
            let denominator_sum = &m_ + Atom::num(2) * &p_ + Atom::num(1);
            let recursive_1 = scaled.pow(&m_) * quadratic.pow(&p_ - Atom::num(1)) * argument.pow(&n_);
            let recursive_2 = scaled.pow(&m_ + Atom::num(1))
                * denominator.pow(&p_ - half_integer_atom(1))
                * argument.pow(&n_ - Atom::num(1));
            rubi_simp(&(scaled.pow(&m_ + Atom::num(1)) * quadratic.pow(&p_) * argument.pow(&n_)
                    / (&f__ * &denominator_sum)), x_)
                    + rubi_star(Atom::num(2) * &d__ * &p_ / &denominator_sum, rubi_rhs_int(&recursive_1, x_))
                    - rubi_star(&b__ * &c__ * &n_ / (&f__ * &denominator_sum)
                            * rubi_simp(&(quadratic.pow(&p_) / denominator.pow(&p_)), x_), rubi_rhs_int(&recursive_2, x_))
        },
    ));
}

fn push_rules_rule_5203(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5203,
        source: "Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
          (f*x)^(m+1)*(d+e*x^2)^p*(a+b*ArcCos[c*x])^n/(f*(m+2*p+1)) +
          2*d*p/(m+2*p+1) \\[Star] Int[(f*x)^m*(d+e*x^2)^(p-1)*(a+b*ArcCos[c*x])^n,x] +
          b*c*n/(f*(m+2*p+1))*Simp[(d+e*x^2)^p/(1-c^2*x^2)^p] \\[Star] Int[(f*x)^(m+1)*(1-c^2*x^2)^(p-1/2)*(a+b*ArcCos[c*x])^(n-1),x] /;
        FreeQ[{a,b,c,d,e,f,m},x] && EqQ[c^2*d+e,0] && GtQ[n,0] && GtQ[p,0] && Not[LtQ[m,-1]]",
        desc: "Inverted integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [f__, m_, d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [f__, e__, p_, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && gtq!(n_, 0)
                && gtq!(p_, 0)
                && !ltq!(m_, -1)
        },
        rhs: {
            let scaled = &f__ * x_;
            let quadratic = &d__ + &e__ * x_.pow(2);
            let denominator = Atom::num(1) - c__.pow(2) * x_.pow(2);
            let argument = &a__ + &b__ * (&c__ * x_).acos();
            let denominator_sum = &m_ + Atom::num(2) * &p_ + Atom::num(1);
            let recursive_1 = scaled.pow(&m_) * quadratic.pow(&p_ - Atom::num(1)) * argument.pow(&n_);
            let recursive_2 = scaled.pow(&m_ + Atom::num(1))
                * denominator.pow(&p_ - half_integer_atom(1))
                * argument.pow(&n_ - Atom::num(1));
            rubi_simp(&(scaled.pow(&m_ + Atom::num(1)) * quadratic.pow(&p_) * argument.pow(&n_)
                    / (&f__ * &denominator_sum)), x_)
                    + rubi_star(Atom::num(2) * &d__ * &p_ / &denominator_sum, rubi_rhs_int(&recursive_1, x_))
                    + rubi_star(&b__ * &c__ * &n_ / (&f__ * &denominator_sum)
                            * rubi_simp(&(quadratic.pow(&p_) / denominator.pow(&p_)), x_), rubi_rhs_int(&recursive_2, x_))
        },
    ));
}

fn push_rules_rule_5204(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5204,
        source: "Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
          (f*x)^(m+1)*(d+e*x^2)^(p+1)*(a+b*ArcSin[c*x])^n/(d*f*(m+1)) +
          c^2*(m+2*p+3)/(f^2*(m+1)) \\[Star] Int[(f*x)^(m+2)*(d+e*x^2)^p*(a+b*ArcSin[c*x])^n,x] -
          b*c*n/(f*(m+1))*Simp[(d+e*x^2)^p/(1-c^2*x^2)^p] \\[Star] Int[(f*x)^(m+1)*(1-c^2*x^2)^(p+1/2)*(a+b*ArcSin[c*x])^(n-1),x] /;
        FreeQ[{a,b,c,d,e,f,p},x] && EqQ[c^2*d+e,0] && GtQ[n,0] && ILtQ[m,-1]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [f__, m_, d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [f__, e__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, p_], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && gtq!(n_, 0)
                && iltq!(m_, -1)
        },
        rhs: {
            let scaled = &f__ * x_;
            let quadratic = &d__ + &e__ * x_.pow(2);
            let denominator = Atom::num(1) - c__.pow(2) * x_.pow(2);
            let argument = &a__ + &b__ * (&c__ * x_).asin();
            let recursive_1 = scaled.pow(&m_ + Atom::num(2)) * quadratic.pow(&p_) * argument.pow(&n_);
            let recursive_2 = scaled.pow(&m_ + Atom::num(1))
                * denominator.pow(&p_ + half_integer_atom(1))
                * argument.pow(&n_ - Atom::num(1));
            rubi_simp(&(scaled.pow(&m_ + Atom::num(1)) * quadratic.pow(&p_ + Atom::num(1)) * argument.pow(&n_)
                    / (&d__ * &f__ * (&m_ + Atom::num(1)))), x_)
                    + rubi_star(c__.pow(2) * (&m_ + Atom::num(2) * &p_ + Atom::num(3))
                            / (f__.pow(2) * (&m_ + Atom::num(1))), rubi_rhs_int(&recursive_1, x_))
                    - rubi_star(&b__ * &c__ * &n_ / (&f__ * (&m_ + Atom::num(1)))
                            * rubi_simp(&(quadratic.pow(&p_) / denominator.pow(&p_)), x_), rubi_rhs_int(&recursive_2, x_))
        },
    ));
}

fn push_rules_rule_5205(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5205,
        source: "Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
          (f*x)^(m+1)*(d+e*x^2)^(p+1)*(a+b*ArcCos[c*x])^n/(d*f*(m+1)) +
          c^2*(m+2*p+3)/(f^2*(m+1)) \\[Star] Int[(f*x)^(m+2)*(d+e*x^2)^p*(a+b*ArcCos[c*x])^n,x] +
          b*c*n/(f*(m+1))*Simp[(d+e*x^2)^p/(1-c^2*x^2)^p] \\[Star] Int[(f*x)^(m+1)*(1-c^2*x^2)^(p+1/2)*(a+b*ArcCos[c*x])^(n-1),x] /;
        FreeQ[{a,b,c,d,e,f,p},x] && EqQ[c^2*d+e,0] && GtQ[n,0] && ILtQ[m,-1]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [f__, m_, d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [f__, e__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, p_], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && gtq!(n_, 0)
                && iltq!(m_, -1)
        },
        rhs: {
            let scaled = &f__ * x_;
            let quadratic = &d__ + &e__ * x_.pow(2);
            let denominator = Atom::num(1) - c__.pow(2) * x_.pow(2);
            let argument = &a__ + &b__ * (&c__ * x_).acos();
            let recursive_1 = scaled.pow(&m_ + Atom::num(2)) * quadratic.pow(&p_) * argument.pow(&n_);
            let recursive_2 = scaled.pow(&m_ + Atom::num(1))
                * denominator.pow(&p_ + half_integer_atom(1))
                * argument.pow(&n_ - Atom::num(1));
            rubi_simp(&(scaled.pow(&m_ + Atom::num(1)) * quadratic.pow(&p_ + Atom::num(1)) * argument.pow(&n_)
                    / (&d__ * &f__ * (&m_ + Atom::num(1)))), x_)
                    + rubi_star(c__.pow(2) * (&m_ + Atom::num(2) * &p_ + Atom::num(3))
                            / (f__.pow(2) * (&m_ + Atom::num(1))), rubi_rhs_int(&recursive_1, x_))
                    + rubi_star(&b__ * &c__ * &n_ / (&f__ * (&m_ + Atom::num(1)))
                            * rubi_simp(&(quadratic.pow(&p_) / denominator.pow(&p_)), x_), rubi_rhs_int(&recursive_2, x_))
        },
    ));
}

fn push_rules_rule_5206(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5206,
        source: "Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
          f*(f*x)^(m-1)*(d+e*x^2)^(p+1)*(a+b*ArcSin[c*x])^n/(2*e*(p+1)) -
          f^2*(m-1)/(2*e*(p+1)) \\[Star] Int[(f*x)^(m-2)*(d+e*x^2)^(p+1)*(a+b*ArcSin[c*x])^n,x] +
          b*f*n/(2*c*(p+1))*Simp[(d+e*x^2)^p/(1-c^2*x^2)^p] \\[Star] Int[(f*x)^(m-1)*(1-c^2*x^2)^(p+1/2)*(a+b*ArcSin[c*x])^(n-1),x] /;
        FreeQ[{a,b,c,d,e,f},x] && EqQ[c^2*d+e,0] && GtQ[n,0] && LtQ[p,-1] && IGtQ[m,1]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [f__, m_, d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [f__, e__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && gtq!(n_, 0)
                && ltq!(p_, -1)
                && igtq!(m_, 1)
        },
        rhs: {
            let scaled = &f__ * x_;
            let quadratic = &d__ + &e__ * x_.pow(2);
            let denominator = Atom::num(1) - c__.pow(2) * x_.pow(2);
            let argument = &a__ + &b__ * (&c__ * x_).asin();
            let recursive_1 = scaled.pow(&m_ - Atom::num(2))
                * quadratic.pow(&p_ + Atom::num(1))
                * argument.pow(&n_);
            let recursive_2 = scaled.pow(&m_ - Atom::num(1))
                * denominator.pow(&p_ + half_integer_atom(1))
                * argument.pow(&n_ - Atom::num(1));
            rubi_simp(&(&f__ * scaled.pow(&m_ - Atom::num(1)) * quadratic.pow(&p_ + Atom::num(1)) * argument.pow(&n_)
                    / (Atom::num(2) * &e__ * (&p_ + Atom::num(1)))), x_)
                    - rubi_star(f__.pow(2) * (&m_ - Atom::num(1))
                            / (Atom::num(2) * &e__ * (&p_ + Atom::num(1))), rubi_rhs_int(&recursive_1, x_))
                    + rubi_star(&b__ * &f__ * &n_ / (Atom::num(2) * &c__ * (&p_ + Atom::num(1)))
                            * rubi_simp(&(quadratic.pow(&p_) / denominator.pow(&p_)), x_), rubi_rhs_int(&recursive_2, x_))
        },
    ));
}

fn push_rules_rule_5207(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5207,
        source: "Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
          f*(f*x)^(m-1)*(d+e*x^2)^(p+1)*(a+b*ArcCos[c*x])^n/(2*e*(p+1)) -
          f^2*(m-1)/(2*e*(p+1)) \\[Star] Int[(f*x)^(m-2)*(d+e*x^2)^(p+1)*(a+b*ArcCos[c*x])^n,x] -
          b*f*n/(2*c*(p+1))*Simp[(d+e*x^2)^p/(1-c^2*x^2)^p] \\[Star] Int[(f*x)^(m-1)*(1-c^2*x^2)^(p+1/2)*(a+b*ArcCos[c*x])^(n-1),x] /;
        FreeQ[{a,b,c,d,e,f},x] && EqQ[c^2*d+e,0] && GtQ[n,0] && LtQ[p,-1] && IGtQ[m,1]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [f__, m_, d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [f__, e__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && gtq!(n_, 0)
                && ltq!(p_, -1)
                && igtq!(m_, 1)
        },
        rhs: {
            let scaled = &f__ * x_;
            let quadratic = &d__ + &e__ * x_.pow(2);
            let denominator = Atom::num(1) - c__.pow(2) * x_.pow(2);
            let argument = &a__ + &b__ * (&c__ * x_).acos();
            let recursive_1 = scaled.pow(&m_ - Atom::num(2))
                * quadratic.pow(&p_ + Atom::num(1))
                * argument.pow(&n_);
            let recursive_2 = scaled.pow(&m_ - Atom::num(1))
                * denominator.pow(&p_ + half_integer_atom(1))
                * argument.pow(&n_ - Atom::num(1));
            rubi_simp(&(&f__ * scaled.pow(&m_ - Atom::num(1)) * quadratic.pow(&p_ + Atom::num(1)) * argument.pow(&n_)
                    / (Atom::num(2) * &e__ * (&p_ + Atom::num(1)))), x_)
                    - rubi_star(f__.pow(2) * (&m_ - Atom::num(1))
                            / (Atom::num(2) * &e__ * (&p_ + Atom::num(1))), rubi_rhs_int(&recursive_1, x_))
                    - rubi_star(&b__ * &f__ * &n_ / (Atom::num(2) * &c__ * (&p_ + Atom::num(1)))
                            * rubi_simp(&(quadratic.pow(&p_) / denominator.pow(&p_)), x_), rubi_rhs_int(&recursive_2, x_))
        },
    ));
}

fn push_rules_rule_5208(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5208,
        source: "Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
          -(f*x)^(m+1)*(d+e*x^2)^(p+1)*(a+b*ArcSin[c*x])^n/(2*d*f*(p+1)) +
          (m+2*p+3)/(2*d*(p+1)) \\[Star] Int[(f*x)^m*(d+e*x^2)^(p+1)*(a+b*ArcSin[c*x])^n,x] +
          b*c*n/(2*f*(p+1))*Simp[(d+e*x^2)^p/(1-c^2*x^2)^p] \\[Star]
            Int[(f*x)^(m+1)*(1-c^2*x^2)^(p+1/2)*(a+b*ArcSin[c*x])^(n-1),x] /;
        FreeQ[{a,b,c,d,e,f,m},x] && EqQ[c^2*d+e,0] && GtQ[n,0] && LtQ[p,-1] && Not[GtQ[m,1]] && (IntegerQ[m] || IntegerQ[p] || EqQ[n,1])",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [f__, m_, d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [f__, e__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && gtq!(n_, 0)
                && ltq!(p_, -1)
                && !gtq!(m_, 1)
                && (integerq!(m_) || integerq!(p_) || eqq!(n_, 1))
        },
        rhs: {
            let scaled = &f__ * x_;
            let quadratic = &d__ + &e__ * x_.pow(2);
            let denominator = Atom::num(1) - c__.pow(2) * x_.pow(2);
            let argument = &a__ + &b__ * (&c__ * x_).asin();
            let recursive_1 =
                scaled.pow(&m_) * quadratic.pow(&p_ + Atom::num(1)) * argument.pow(&n_);
            let recursive_2 = scaled.pow(&m_ + Atom::num(1))
                * denominator.pow(&p_ + half_integer_atom(1))
                * argument.pow(&n_ - Atom::num(1));
            rubi_simp(&(-scaled.pow(&m_ + Atom::num(1)) * quadratic.pow(&p_ + Atom::num(1)) * argument.pow(&n_)
                    / (Atom::num(2) * &d__ * &f__ * (&p_ + Atom::num(1)))), x_)
                    + rubi_star((&m_ + Atom::num(2) * &p_ + Atom::num(3))
                            / (Atom::num(2) * &d__ * (&p_ + Atom::num(1))), rubi_rhs_int(&recursive_1, x_))
                    + rubi_star(&b__ * &c__ * &n_ / (Atom::num(2) * &f__ * (&p_ + Atom::num(1)))
                            * rubi_simp(&(quadratic.pow(&p_) / denominator.pow(&p_)), x_), rubi_rhs_int(&recursive_2, x_))
        },
    ));
}

fn push_rules_rule_5209(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5209,
        source: "Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
          -(f*x)^(m+1)*(d+e*x^2)^(p+1)*(a+b*ArcCos[c*x])^n/(2*d*f*(p+1)) +
          (m+2*p+3)/(2*d*(p+1)) \\[Star] Int[(f*x)^m*(d+e*x^2)^(p+1)*(a+b*ArcCos[c*x])^n,x] -
          b*c*n/(2*f*(p+1))*Simp[(d+e*x^2)^p/(1-c^2*x^2)^p] \\[Star]
            Int[(f*x)^(m+1)*(1-c^2*x^2)^(p+1/2)*(a+b*ArcCos[c*x])^(n-1),x] /;
        FreeQ[{a,b,c,d,e,f,m},x] && EqQ[c^2*d+e,0] && GtQ[n,0] && LtQ[p,-1] && Not[GtQ[m,1]] && (IntegerQ[m] || IntegerQ[p] || EqQ[n,1])",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [f__, m_, d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [f__, e__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && gtq!(n_, 0)
                && ltq!(p_, -1)
                && !gtq!(m_, 1)
                && (integerq!(m_) || integerq!(p_) || eqq!(n_, 1))
        },
        rhs: {
            let scaled = &f__ * x_;
            let quadratic = &d__ + &e__ * x_.pow(2);
            let denominator = Atom::num(1) - c__.pow(2) * x_.pow(2);
            let argument = &a__ + &b__ * (&c__ * x_).acos();
            let recursive_1 =
                scaled.pow(&m_) * quadratic.pow(&p_ + Atom::num(1)) * argument.pow(&n_);
            let recursive_2 = scaled.pow(&m_ + Atom::num(1))
                * denominator.pow(&p_ + half_integer_atom(1))
                * argument.pow(&n_ - Atom::num(1));
            rubi_simp(&(-scaled.pow(&m_ + Atom::num(1)) * quadratic.pow(&p_ + Atom::num(1)) * argument.pow(&n_)
                    / (Atom::num(2) * &d__ * &f__ * (&p_ + Atom::num(1)))), x_)
                    + rubi_star((&m_ + Atom::num(2) * &p_ + Atom::num(3))
                            / (Atom::num(2) * &d__ * (&p_ + Atom::num(1))), rubi_rhs_int(&recursive_1, x_))
                    - rubi_star(&b__ * &c__ * &n_ / (Atom::num(2) * &f__ * (&p_ + Atom::num(1)))
                            * rubi_simp(&(quadratic.pow(&p_) / denominator.pow(&p_)), x_), rubi_rhs_int(&recursive_2, x_))
        },
    ));
}

fn push_rules_rule_5210(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5210,
        source: "Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
          f*(f*x)^(m-1)*(d+e*x^2)^(p+1)*(a+b*ArcSin[c*x])^n/(e*(m+2*p+1)) +
          f^2*(m-1)/(c^2*(m+2*p+1)) \\[Star] Int[(f*x)^(m-2)*(d+e*x^2)^p*(a+b*ArcSin[c*x])^n,x] +
          b*f*n/(c*(m+2*p+1))*Simp[(d+e*x^2)^p/(1-c^2*x^2)^p] \\[Star]
            Int[(f*x)^(m-1)*(1-c^2*x^2)^(p+1/2)*(a+b*ArcSin[c*x])^(n-1),x] /;
        FreeQ[{a,b,c,d,e,f,p},x] && EqQ[c^2*d+e,0] && GtQ[n,0] && IGtQ[m,1] && NeQ[m+2*p+1,0]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [f__, m_, d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [f__, e__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, p_], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && gtq!(n_, 0)
                && igtq!(m_, 1)
                && neq!(&m_ + Atom::num(2) * &p_ + Atom::num(1), 0)
        },
        rhs: {
            let scaled = &f__ * x_;
            let quadratic = &d__ + &e__ * x_.pow(2);
            let denominator = Atom::num(1) - c__.pow(2) * x_.pow(2);
            let argument = &a__ + &b__ * (&c__ * x_).asin();
            let denominator_sum = &m_ + Atom::num(2) * &p_ + Atom::num(1);
            let recursive_1 =
                scaled.pow(&m_ - Atom::num(2)) * quadratic.pow(&p_) * argument.pow(&n_);
            let recursive_2 = scaled.pow(&m_ - Atom::num(1))
                * denominator.pow(&p_ + half_integer_atom(1))
                * argument.pow(&n_ - Atom::num(1));
            rubi_simp(&(&f__ * scaled.pow(&m_ - Atom::num(1)) * quadratic.pow(&p_ + Atom::num(1)) * argument.pow(&n_)
                    / (&e__ * &denominator_sum)), x_)
                    + rubi_star(f__.pow(2) * (&m_ - Atom::num(1)) / (c__.pow(2) * &denominator_sum), rubi_rhs_int(&recursive_1, x_))
                    + rubi_star(&b__ * &f__ * &n_ / (&c__ * &denominator_sum)
                            * rubi_simp(&(quadratic.pow(&p_) / denominator.pow(&p_)), x_), rubi_rhs_int(&recursive_2, x_))
        },
    ));
}

fn push_rules_rule_5211(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5211,
        source: "Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
          f*(f*x)^(m-1)*(d+e*x^2)^(p+1)*(a+b*ArcCos[c*x])^n/(e*(m+2*p+1)) +
          f^2*(m-1)/(c^2*(m+2*p+1)) \\[Star] Int[(f*x)^(m-2)*(d+e*x^2)^p*(a+b*ArcCos[c*x])^n,x] -
          b*f*n/(c*(m+2*p+1))*Simp[(d+e*x^2)^p/(1-c^2*x^2)^p] \\[Star]
            Int[(f*x)^(m-1)*(1-c^2*x^2)^(p+1/2)*(a+b*ArcCos[c*x])^(n-1),x] /;
        FreeQ[{a,b,c,d,e,f,p},x] && EqQ[c^2*d+e,0] && GtQ[n,0] && IGtQ[m,1] && NeQ[m+2*p+1,0]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [f__, m_, d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [f__, e__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, p_], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && gtq!(n_, 0)
                && igtq!(m_, 1)
                && neq!(&m_ + Atom::num(2) * &p_ + Atom::num(1), 0)
        },
        rhs: {
            let scaled = &f__ * x_;
            let quadratic = &d__ + &e__ * x_.pow(2);
            let denominator = Atom::num(1) - c__.pow(2) * x_.pow(2);
            let argument = &a__ + &b__ * (&c__ * x_).acos();
            let denominator_sum = &m_ + Atom::num(2) * &p_ + Atom::num(1);
            let recursive_1 =
                scaled.pow(&m_ - Atom::num(2)) * quadratic.pow(&p_) * argument.pow(&n_);
            let recursive_2 = scaled.pow(&m_ - Atom::num(1))
                * denominator.pow(&p_ + half_integer_atom(1))
                * argument.pow(&n_ - Atom::num(1));
            rubi_simp(&(&f__ * scaled.pow(&m_ - Atom::num(1)) * quadratic.pow(&p_ + Atom::num(1)) * argument.pow(&n_)
                    / (&e__ * &denominator_sum)), x_)
                    + rubi_star(f__.pow(2) * (&m_ - Atom::num(1)) / (c__.pow(2) * &denominator_sum), rubi_rhs_int(&recursive_1, x_))
                    - rubi_star(&b__ * &f__ * &n_ / (&c__ * &denominator_sum)
                            * rubi_simp(&(quadratic.pow(&p_) / denominator.pow(&p_)), x_), rubi_rhs_int(&recursive_2, x_))
        },
    ));
}

fn push_rules_rule_5212(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5212,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_.*x_])^n_,x_Symbol] :=
          (f*x)^m*Sqrt[1-c^2*x^2]*(d+e*x^2)^p*(a+b*ArcSin[c*x])^(n+1)/(b*c*(n+1)) -
          f*m/(b*c*(n+1))*Simp[(d+e*x^2)^p/(1-c^2*x^2)^p] \\[Star]
            Int[(f*x)^(m-1)*(1-c^2*x^2)^(p-1/2)*(a+b*ArcSin[c*x])^(n+1),x] /;
        FreeQ[{a,b,c,d,e,f,m,p},x] && EqQ[c^2*d+e,0] && LtQ[n,-1] && EqQ[m+2*p+1,0]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [f__, m_, d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [f__, m_, e__, p_, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, p_], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && ltq!(n_, -1)
                && eqq!(&m_ + Atom::num(2) * &p_ + Atom::num(1), 0)
        },
        rhs: {
            let scaled = &f__ * x_;
            let quadratic = &d__ + &e__ * x_.pow(2);
            let denominator = Atom::num(1) - c__.pow(2) * x_.pow(2);
            let argument = &a__ + &b__ * (&c__ * x_).asin();
            let ratio = rubi_simp(&(quadratic.pow(&p_) / denominator.pow(&p_)), x_);
            let recursive =
                scaled.pow(&m_ - Atom::num(1)) * denominator.pow(&p_ - half_integer_atom(1)) * argument.pow(&n_ + Atom::num(1));
            rubi_simp(&(scaled.pow(&m_) * (Atom::num(1) - c__.pow(2) * x_.pow(2)).sqrt() * quadratic.pow(&p_) * argument.pow(&n_ + Atom::num(1))
                    / (&b__ * &c__ * (&n_ + Atom::num(1)))), x_)
                    - rubi_star(&f__ * &m_ / (&b__ * &c__ * (&n_ + Atom::num(1))) * ratio, rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_5213(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5213,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_.*x_])^n_,x_Symbol] :=
          -(f*x)^m*Sqrt[1-c^2*x^2]*(d+e*x^2)^p*(a+b*ArcCos[c*x])^(n+1)/(b*c*(n+1)) +
          f*m/(b*c*(n+1))*Simp[(d+e*x^2)^p/(1-c^2*x^2)^p] \\[Star]
            Int[(f*x)^(m-1)*(1-c^2*x^2)^(p-1/2)*(a+b*ArcCos[c*x])^(n+1),x] /;
        FreeQ[{a,b,c,d,e,f,m,p},x] && EqQ[c^2*d+e,0] && LtQ[n,-1] && EqQ[m+2*p+1,0]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [f__, m_, d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [f__, m_, e__, p_, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, p_], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && ltq!(n_, -1)
                && eqq!(&m_ + Atom::num(2) * &p_ + Atom::num(1), 0)
        },
        rhs: {
            let scaled = &f__ * x_;
            let quadratic = &d__ + &e__ * x_.pow(2);
            let denominator = Atom::num(1) - c__.pow(2) * x_.pow(2);
            let argument = &a__ + &b__ * (&c__ * x_).acos();
            let ratio = rubi_simp(&(quadratic.pow(&p_) / denominator.pow(&p_)), x_);
            let recursive =
                scaled.pow(&m_ - Atom::num(1)) * denominator.pow(&p_ - half_integer_atom(1)) * argument.pow(&n_ + Atom::num(1));
            rubi_simp(&(-scaled.pow(&m_) * (Atom::num(1) - c__.pow(2) * x_.pow(2)).sqrt() * quadratic.pow(&p_) * argument.pow(&n_ + Atom::num(1))
                    / (&b__ * &c__ * (&n_ + Atom::num(1)))), x_)
                    + rubi_star(&f__ * &m_ / (&b__ * &c__ * (&n_ + Atom::num(1))) * ratio, rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_5214(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5214,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_.*x_])^n_,x_Symbol] :=
          (f*x)^m*Sqrt[1-c^2*x^2]*(d+e*x^2)^p*(a+b*ArcSin[c*x])^(n+1)/(b*c*(n+1)) -
          f*m/(b*c*(n+1))*Simp[(d+e*x^2)^p/(1-c^2*x^2)^p] \\[Star] Int[(f*x)^(m-1)*(1-c^2*x^2)^(p-1/2)*(a+b*ArcSin[c*x])^(n+1),x] +
          c*(m+2*p+1)/(b*f*(n+1))*Simp[(d+e*x^2)^p/(1-c^2*x^2)^p] \\[Star] Int[(f*x)^(m+1)*(1-c^2*x^2)^(p-1/2)*(a+b*ArcSin[c*x])^(n+1),x] /;
        FreeQ[{a,b,c,d,e,f},x] && EqQ[c^2*d+e,0] && LtQ[n,-1] && IGtQ[2*p,0] && NeQ[m+2*p+1,0] && IGtQ[m,-3]",
        desc: "Integration by parts and piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [f__, m_, d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [f__, m_, e__, p_, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && ltq!(n_, -1)
                && igtq!(Atom::num(2) * &p_, 0)
                && neq!(&m_ + Atom::num(2) * &p_ + Atom::num(1), 0)
                && igtq!(m_, -3)
        },
        rhs: {
            let scaled = &f__ * x_;
            let quadratic = &d__ + &e__ * x_.pow(2);
            let denominator = Atom::num(1) - c__.pow(2) * x_.pow(2);
            let argument = &a__ + &b__ * (&c__ * x_).asin();
            let ratio = rubi_simp(&(quadratic.pow(&p_) / denominator.pow(&p_)), x_);
            let recursive_1 = scaled.pow(&m_ - Atom::num(1))
                * denominator.pow(&p_ - half_integer_atom(1))
                * argument.pow(&n_ + Atom::num(1));
            let recursive_2 = scaled.pow(&m_ + Atom::num(1))
                * denominator.pow(&p_ - half_integer_atom(1))
                * argument.pow(&n_ + Atom::num(1));
            rubi_simp(&(scaled.pow(&m_) * denominator.sqrt() * quadratic.pow(&p_) * argument.pow(&n_ + Atom::num(1))
                    / (&b__ * &c__ * (&n_ + Atom::num(1)))), x_)
                    - rubi_star(&f__ * &m_ / (&b__ * &c__ * (&n_ + Atom::num(1))) * &ratio, rubi_rhs_int(&recursive_1, x_))
                    + rubi_star(&c__ * (&m_ + Atom::num(2) * &p_ + Atom::num(1))
                            / (&b__ * &f__ * (&n_ + Atom::num(1)))
                            * ratio, rubi_rhs_int(&recursive_2, x_))
        },
    ));
}

fn push_rules_rule_5215(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5215,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_.*x_])^n_,x_Symbol] :=
          -(f*x)^m*Sqrt[1-c^2*x^2]*(d+e*x^2)^p*(a+b*ArcCos[c*x])^(n+1)/(b*c*(n+1)) +
          f*m/(b*c*(n+1))*Simp[(d+e*x^2)^p/(1-c^2*x^2)^p] \\[Star] Int[(f*x)^(m-1)*(1-c^2*x^2)^(p-1/2)*(a+b*ArcCos[c*x])^(n+1),x] -
          c*(m+2*p+1)/(b*f*(n+1))*Simp[(d+e*x^2)^p/(1-c^2*x^2)^p] \\[Star] Int[(f*x)^(m+1)*(1-c^2*x^2)^(p-1/2)*(a+b*ArcCos[c*x])^(n+1),x] /;
        FreeQ[{a,b,c,d,e,f},x] && EqQ[c^2*d+e,0] && LtQ[n,-1] && IGtQ[2*p,0] && NeQ[m+2*p+1,0] && IGtQ[m,-3]",
        desc: "Integration by parts and piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [f__, m_, d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [f__, m_, e__, p_, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && ltq!(n_, -1)
                && igtq!(Atom::num(2) * &p_, 0)
                && neq!(&m_ + Atom::num(2) * &p_ + Atom::num(1), 0)
                && igtq!(m_, -3)
        },
        rhs: {
            let scaled = &f__ * x_;
            let quadratic = &d__ + &e__ * x_.pow(2);
            let denominator = Atom::num(1) - c__.pow(2) * x_.pow(2);
            let argument = &a__ + &b__ * (&c__ * x_).acos();
            let ratio = rubi_simp(&(quadratic.pow(&p_) / denominator.pow(&p_)), x_);
            let recursive_1 = scaled.pow(&m_ - Atom::num(1))
                * denominator.pow(&p_ - half_integer_atom(1))
                * argument.pow(&n_ + Atom::num(1));
            let recursive_2 = scaled.pow(&m_ + Atom::num(1))
                * denominator.pow(&p_ - half_integer_atom(1))
                * argument.pow(&n_ + Atom::num(1));
            rubi_simp(&(-scaled.pow(&m_) * denominator.sqrt() * quadratic.pow(&p_) * argument.pow(&n_ + Atom::num(1))
                    / (&b__ * &c__ * (&n_ + Atom::num(1)))), x_)
                    + rubi_star(&f__ * &m_ / (&b__ * &c__ * (&n_ + Atom::num(1))) * &ratio, rubi_rhs_int(&recursive_1, x_))
                    - rubi_star(&c__ * (&m_ + Atom::num(2) * &p_ + Atom::num(1))
                            / (&b__ * &f__ * (&n_ + Atom::num(1)))
                            * ratio, rubi_rhs_int(&recursive_2, x_))
        },
    ));
}

fn push_rules_rule_5216(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5216,
        source: "Int[(f_.*x_)^m_*(a_.+b_.*ArcSin[c_.*x_])^n_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
          f*(f*x)^(m-1)*Sqrt[d+e*x^2]*(a+b*ArcSin[c*x])^n/(e*m) +
          b*f*n/(c*m)*Simp[Sqrt[1-c^2*x^2]/Sqrt[d+e*x^2]] \\[Star] Int[(f*x)^(m-1)*(a+b*ArcSin[c*x])^(n-1),x] +
          f^2*(m-1)/(c^2*m) \\[Star] Int[((f*x)^(m-2)*(a+b*ArcSin[c*x])^n)/Sqrt[d+e*x^2],x] /;
        FreeQ[{a,b,c,d,e,f},x] && EqQ[c^2*d+e,0] && GtQ[n,0] && IGtQ[m,1]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [f__, m_, a__, b__, c__, n_, d__, e__, x_],
        optional: [f__, a__, b__, c__, n_, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && gtq!(n_, 0)
                && igtq!(m_, 1)
        },
        rhs: {
            let scaled = &f__ * x_;
            let quadratic = &d__ + &e__ * x_.pow(2);
            let argument = &a__ + &b__ * (&c__ * x_).asin();
            let ratio = rubi_simp(
                &((Atom::num(1) - c__.pow(2) * x_.pow(2)).sqrt() / &quadratic.sqrt()),
                x_,
            );
            let recursive_1 = scaled.pow(&m_ - Atom::num(1)) * argument.pow(&n_ - Atom::num(1));
            let recursive_2 = scaled.pow(&m_ - Atom::num(2)) * argument.pow(&n_) / &quadratic.sqrt();
            rubi_simp(&(&f__ * scaled.pow(&m_ - Atom::num(1)) * quadratic.sqrt() * argument.pow(&n_) / (&e__ * &m_)), x_)
                    + rubi_star(&b__ * &f__ * &n_ / (&c__ * &m_) * ratio, rubi_rhs_int(&recursive_1, x_))
                    + rubi_star(f__.pow(2) * (&m_ - Atom::num(1)) / (c__.pow(2) * &m_), rubi_rhs_int(&recursive_2, x_))
        },
    ));
}

fn push_rules_rule_5217(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5217,
        source: "Int[(f_.*x_)^m_*(a_.+b_.*ArcCos[c_.*x_])^n_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
          f*(f*x)^(m-1)*Sqrt[d+e*x^2]*(a+b*ArcCos[c*x])^n/(e*m) -
          b*f*n/(c*m)*Simp[Sqrt[1-c^2*x^2]/Sqrt[d+e*x^2]] \\[Star] Int[(f*x)^(m-1)*(a+b*ArcCos[c*x])^(n-1),x] +
          f^2*(m-1)/(c^2*m) \\[Star] Int[((f*x)^(m-2)*(a+b*ArcCos[c*x])^n)/Sqrt[d+e*x^2],x] /;
        FreeQ[{a,b,c,d,e,f},x] && EqQ[c^2*d+e,0] && GtQ[n,0] && IGtQ[m,1]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [f__, m_, a__, b__, c__, n_, d__, e__, x_],
        optional: [f__, a__, b__, c__, n_, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && gtq!(n_, 0)
                && igtq!(m_, 1)
        },
        rhs: {
            let scaled = &f__ * x_;
            let quadratic = &d__ + &e__ * x_.pow(2);
            let argument = &a__ + &b__ * (&c__ * x_).acos();
            let ratio = rubi_simp(
                &((Atom::num(1) - c__.pow(2) * x_.pow(2)).sqrt() / &quadratic.sqrt()),
                x_,
            );
            let recursive_1 = scaled.pow(&m_ - Atom::num(1)) * argument.pow(&n_ - Atom::num(1));
            let recursive_2 = scaled.pow(&m_ - Atom::num(2)) * argument.pow(&n_) / &quadratic.sqrt();
            rubi_simp(&(&f__ * scaled.pow(&m_ - Atom::num(1)) * quadratic.sqrt() * argument.pow(&n_) / (&e__ * &m_)), x_)
                    - rubi_star(&b__ * &f__ * &n_ / (&c__ * &m_) * ratio, rubi_rhs_int(&recursive_1, x_))
                    + rubi_star(f__.pow(2) * (&m_ - Atom::num(1)) / (c__.pow(2) * &m_), rubi_rhs_int(&recursive_2, x_))
        },
    ));
}

fn push_rules_rule_5218(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5218,
        source: "Int[x_^m_*(a_.+b_.*ArcSin[c_.*x_])^n_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
          1/c^(m+1)*Simp[Sqrt[1-c^2*x^2]/Sqrt[d+e*x^2]] \\[Star] Subst[Int[(a+b*x)^n*Sin[x]^m,x],x,ArcSin[c*x]] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && IGtQ[n,0] && IntegerQ[m]",
        desc: "Piecewise constant extraction and integration by substitution",
        refs: [],
        pattern: x_.pow(m_) * (a__ + b__ * (c__ * x_).asin()).pow(n_) / (d__ + e__ * x_.pow(2)).sqrt(),
        with: [m_, a__, b__, c__, n_, d__, e__, x_],
        optional: [a__, b__, c__, n_, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && igtq!(n_, 0)
                && integerq!(m_)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let substitution_integrand = (&a__ + &b__ * &sub_atom).pow(&n_) * sub_atom.sin().pow(&m_);
            let substitution_primitive = rubi_rhs_int(&substitution_integrand, substitution_symbol);
            rubi_star(rubi_simp(
                    &((Atom::num(1) - c__.pow(2) * x_.pow(2)).sqrt()
                        / (&d__ + &e__ * x_.pow(2)).sqrt()),
                    x_,
                ) / c__.pow(&m_ + Atom::num(1)), rubi_subst(
                    &substitution_primitive,
                    substitution_symbol,
                    (&c__ * x_).asin(),
                ))
        },
    ));
}

fn push_rules_rule_5219(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5219,
        source: "Int[x_^m_*(a_.+b_.*ArcCos[c_.*x_])^n_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
          -1/c^(m+1)*Simp[Sqrt[1-c^2*x^2]/Sqrt[d+e*x^2]] \\[Star] Subst[Int[(a+b*x)^n*Cos[x]^m,x],x,ArcCos[c*x]] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && IGtQ[n,0] && IntegerQ[m]",
        desc: "Piecewise constant extraction and integration by substitution",
        refs: [],
        pattern: x_.pow(m_) * (a__ + b__ * (c__ * x_).acos()).pow(n_) / (d__ + e__ * x_.pow(2)).sqrt(),
        with: [m_, a__, b__, c__, n_, d__, e__, x_],
        optional: [a__, b__, c__, n_, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && igtq!(n_, 0)
                && integerq!(m_)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let substitution_integrand = (&a__ + &b__ * &sub_atom).pow(&n_) * sub_atom.cos().pow(&m_);
            let substitution_primitive = rubi_rhs_int(&substitution_integrand, substitution_symbol);
            rubi_star(-rubi_simp(
                    &((Atom::num(1) - c__.pow(2) * x_.pow(2)).sqrt()
                        / (&d__ + &e__ * x_.pow(2)).sqrt()),
                    x_,
                ) / c__.pow(&m_ + Atom::num(1)), rubi_subst(
                    &substitution_primitive,
                    substitution_symbol,
                    (&c__ * x_).acos(),
                ))
        },
    ));
}

fn push_rules_rule_5220(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, x_);
    rules.push(rubi_rule!(
        order: 5220,
        source: "Int[(f_.*x_)^m_*(a_.+b_.*ArcSin[c_.*x_])/Sqrt[d_+e_.*x_^2],x_Symbol] :=
          (f*x)^(m+1)/(f*(m+1))*Simp[Sqrt[1-c^2*x^2]/Sqrt[d+e*x^2]]*(a+b*ArcSin[c*x])*
            Hypergeometric2F1[1/2,(1+m)/2,(3+m)/2,c^2*x^2] -
          b*c*(f*x)^(m+2)/(f^2*(m+1)*(m+2))*Simp[Sqrt[1-c^2*x^2]/Sqrt[d+e*x^2]]*
            HypergeometricPFQ[{1,1+m/2,1+m/2},{3/2+m/2,2+m/2},c^2*x^2] /;
        FreeQ[{a,b,c,d,e,f,m},x] && EqQ[c^2*d+e,0] && Not[IntegerQ[m]]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern: (f__ * x_).pow(m_) * (a__ + b__ * (c__ * x_).asin()) / (d__ + e__ * x_.pow(2)).sqrt(),
        with: [f__, m_, a__, b__, c__, d__, e__, x_],
        optional: [f__, a__, b__, c__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && !integerq!(m_)
        },
        rhs: {
            let scaled = &f__ * x_;
            let quadratic = &d__ + &e__ * x_.pow(2);
            let argument = &a__ + &b__ * (&c__ * x_).asin();
            let ratio = rubi_simp(
                &((Atom::num(1) - c__.pow(2) * x_.pow(2)).sqrt() / quadratic.sqrt()),
                x_,
            );
            let z = c__.pow(2) * x_.pow(2);
            rubi_simp(&(scaled.pow(&m_ + Atom::num(1))
                    / (&f__ * (&m_ + Atom::num(1)))
                    * &ratio
                    * argument
                    * rubi_hypergeometric2f1(
                        Atom::num(1) / Atom::num(2),
                        (&m_ + Atom::num(1)) / Atom::num(2),
                        (&m_ + Atom::num(3)) / Atom::num(2),
                        &z,
                    )), x_)
                    - rubi_simp(&(&b__ * &c__ * scaled.pow(&m_ + Atom::num(2))
                        / (f__.pow(2) * (&m_ + Atom::num(1)) * (&m_ + Atom::num(2)))
                        * ratio
                        * rubi_symbols().hypergeometric_pfq.call((
                            Atom::num(1),
                            Atom::num(1) + &m_ / Atom::num(2),
                            Atom::num(1) + &m_ / Atom::num(2),
                            Atom::num(3) / Atom::num(2) + &m_ / Atom::num(2),
                            Atom::num(2) + &m_ / Atom::num(2),
                            z,
                        ))), x_)
        },
    ));
}

fn push_rules_rule_5221(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, x_);
    rules.push(rubi_rule!(
        order: 5221,
        source: "Int[(f_.*x_)^m_*(a_.+b_.*ArcCos[c_.*x_])/Sqrt[d_+e_.*x_^2],x_Symbol] :=
          (f*x)^(m+1)/(f*(m+1))*(a+b*ArcCos[c*x])*Simp[Sqrt[1-c^2*x^2]/Sqrt[d+e*x^2]]*
            Hypergeometric2F1[1/2,(1+m)/2,(3+m)/2,c^2*x^2] +
          b*c*(f*x)^(m+2)/(f^2*(m+1)*(m+2))*Simp[Sqrt[1-c^2*x^2]/Sqrt[d+e*x^2]]*
            HypergeometricPFQ[{1,1+m/2,1+m/2},{3/2+m/2,2+m/2},c^2*x^2] /;
        FreeQ[{a,b,c,d,e,f,m},x] && EqQ[c^2*d+e,0] && Not[IntegerQ[m]]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern: (f__ * x_).pow(m_) * (a__ + b__ * (c__ * x_).acos()) / (d__ + e__ * x_.pow(2)).sqrt(),
        with: [f__, m_, a__, b__, c__, d__, e__, x_],
        optional: [f__, a__, b__, c__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && !integerq!(m_)
        },
        rhs: {
            let scaled = &f__ * x_;
            let quadratic = &d__ + &e__ * x_.pow(2);
            let argument = &a__ + &b__ * (&c__ * x_).acos();
            let ratio = rubi_simp(
                &((Atom::num(1) - c__.pow(2) * x_.pow(2)).sqrt() / quadratic.sqrt()),
                x_,
            );
            let z = c__.pow(2) * x_.pow(2);
            rubi_simp(&(scaled.pow(&m_ + Atom::num(1))
                    / (&f__ * (&m_ + Atom::num(1)))
                    * argument
                    * &ratio
                    * rubi_hypergeometric2f1(
                        Atom::num(1) / Atom::num(2),
                        (&m_ + Atom::num(1)) / Atom::num(2),
                        (&m_ + Atom::num(3)) / Atom::num(2),
                        &z,
                    )), x_)
                    + rubi_simp(&(&b__ * &c__ * scaled.pow(&m_ + Atom::num(2))
                        / (f__.pow(2) * (&m_ + Atom::num(1)) * (&m_ + Atom::num(2)))
                        * ratio
                        * rubi_symbols().hypergeometric_pfq.call((
                            Atom::num(1),
                            Atom::num(1) + &m_ / Atom::num(2),
                            Atom::num(1) + &m_ / Atom::num(2),
                            Atom::num(3) / Atom::num(2) + &m_ / Atom::num(2),
                            Atom::num(2) + &m_ / Atom::num(2),
                            z,
                        ))), x_)
        },
    ));
}

fn push_rules_rule_5222(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5222,
        source: "Int[(f_.*x_)^m_.*(a_.+b_.*ArcSin[c_.*x_])^n_/Sqrt[d_+e_.*x_^2],x_Symbol] :=
          (f*x)^m/(b*c*(n+1))*Simp[Sqrt[1-c^2*x^2]/Sqrt[d+e*x^2]]*(a+b*ArcSin[c*x])^(n+1) -
          f*m/(b*c*(n+1))*Simp[Sqrt[1-c^2*x^2]/Sqrt[d+e*x^2]] \\[Star] Int[(f*x)^(m-1)*(a+b*ArcSin[c*x])^(n+1),x] /;
        FreeQ[{a,b,c,d,e,f,m},x] && EqQ[c^2*d+e,0] && LtQ[n,-1]",
        desc: "Integration by parts and piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [f__, m_, a__, b__, c__, n_, d__, e__, x_],
        optional: [f__, m_, a__, b__, c__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && ltq!(n_, -1)
        },
        rhs: {
            let scaled = &f__ * x_;
            let argument = &a__ + &b__ * (&c__ * x_).asin();
            let ratio = rubi_simp(
                &((Atom::num(1) - c__.pow(2) * x_.pow(2)).sqrt()
                    / (&d__ + &e__ * x_.pow(2)).sqrt()),
                x_,
            );
            let recursive = scaled.pow(&m_ - Atom::num(1)) * argument.pow(&n_ + Atom::num(1));
            rubi_simp(&(scaled.pow(&m_) / (&b__ * &c__ * (&n_ + Atom::num(1))) * &ratio * argument.pow(&n_ + Atom::num(1))), x_)
                    - rubi_star(&f__ * &m_ / (&b__ * &c__ * (&n_ + Atom::num(1))) * ratio, rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_5223(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5223,
        source: "Int[(f_.*x_)^m_.*(a_.+b_.*ArcCos[c_.*x_])^n_/Sqrt[d_+e_.*x_^2],x_Symbol] :=
          -(f*x)^m/(b*c*(n+1))*Simp[Sqrt[1-c^2*x^2]/Sqrt[d+e*x^2]]*(a+b*ArcCos[c*x])^(n+1) +
          f*m/(b*c*(n+1))*Simp[Sqrt[1-c^2*x^2]/Sqrt[d+e*x^2]] \\[Star] Int[(f*x)^(m-1)*(a+b*ArcCos[c*x])^(n+1),x] /;
        FreeQ[{a,b,c,d,e,f,m},x] && EqQ[c^2*d+e,0] && LtQ[n,-1]",
        desc: "Integration by parts and piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [f__, m_, a__, b__, c__, n_, d__, e__, x_],
        optional: [f__, m_, a__, b__, c__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && ltq!(n_, -1)
        },
        rhs: {
            let scaled = &f__ * x_;
            let argument = &a__ + &b__ * (&c__ * x_).acos();
            let ratio = rubi_simp(
                &((Atom::num(1) - c__.pow(2) * x_.pow(2)).sqrt()
                    / (&d__ + &e__ * x_.pow(2)).sqrt()),
                x_,
            );
            let recursive = scaled.pow(&m_ - Atom::num(1)) * argument.pow(&n_ + Atom::num(1));
            rubi_simp(&(-scaled.pow(&m_) / (&b__ * &c__ * (&n_ + Atom::num(1))) * &ratio * argument.pow(&n_ + Atom::num(1))), x_)
                    + rubi_star(&f__ * &m_ / (&b__ * &c__ * (&n_ + Atom::num(1))) * ratio, rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_5224(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5224,
        source: "Int[x_^m_.*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
          1/(b*c^(m+1))*Simp[(d+e*x^2)^p/(1-c^2*x^2)^p] \\[Star]
            Subst[Int[x^n*Sin[-a/b+x/b]^m*Cos[-a/b+x/b]^(2*p+1),x],x,a+b*ArcSin[c*x]] /;
        FreeQ[{a,b,c,d,e,n},x] && EqQ[c^2*d+e,0] && IGtQ[2*p+2,0] && IGtQ[m,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: x_.pow(m_) * (d__ + e__ * x_.pow(2)).pow(p_) * (a__ + b__ * (c__ * x_).asin()).pow(n_),
        with: [m_, d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [m_, e__, p_, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, n_], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && igtq!(Atom::num(2) * &p_ + Atom::num(2), 0)
                && igtq!(m_, 0)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let hyper_arg = -&a__ / &b__ + &sub_atom / &b__;
            let substitution_integrand =
                sub_atom.pow(&n_) * &hyper_arg.sin().pow(&m_) * hyper_arg.cos().pow(Atom::num(2) * &p_ + Atom::num(1));
            let substitution_primitive = rubi_rhs_int(&substitution_integrand, substitution_symbol);
            rubi_star(rubi_simp(
                    &((&d__ + &e__ * x_.pow(2)).pow(&p_)
                        / (Atom::num(1) - c__.pow(2) * x_.pow(2)).pow(&p_)),
                    x_,
                ) / (&b__ * c__.pow(&m_ + Atom::num(1))), rubi_subst(
                    &substitution_primitive,
                    substitution_symbol,
                    &a__ + &b__ * (&c__ * x_).asin(),
                ))
        },
    ));
}

fn push_rules_rule_5225(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5225,
        source: "Int[x_^m_.*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
          -1/(b*c^(m+1))*Simp[(d+e*x^2)^p/(1-c^2*x^2)^p] \\[Star]
            Subst[Int[x^n*Cos[-a/b+x/b]^m*Sin[-a/b+x/b]^(2*p+1),x],x,a+b*ArcCos[c*x]] /;
        FreeQ[{a,b,c,d,e,n},x] && EqQ[c^2*d+e,0] && IGtQ[2*p+2,0] && IGtQ[m,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: x_.pow(m_) * (d__ + e__ * x_.pow(2)).pow(p_) * (a__ + b__ * (c__ * x_).acos()).pow(n_),
        with: [m_, d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [m_, e__, p_, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, n_], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && igtq!(Atom::num(2) * &p_ + Atom::num(2), 0)
                && igtq!(m_, 0)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let hyper_arg = -&a__ / &b__ + &sub_atom / &b__;
            let substitution_integrand =
                sub_atom.pow(&n_) * &hyper_arg.cos().pow(&m_) * hyper_arg.sin().pow(Atom::num(2) * &p_ + Atom::num(1));
            let substitution_primitive = rubi_rhs_int(&substitution_integrand, substitution_symbol);
            rubi_star(-rubi_simp(
                    &((&d__ + &e__ * x_.pow(2)).pow(&p_)
                        / (Atom::num(1) - c__.pow(2) * x_.pow(2)).pow(&p_)),
                    x_,
                ) / (&b__ * c__.pow(&m_ + Atom::num(1))), rubi_subst(
                    &substitution_primitive,
                    substitution_symbol,
                    &a__ + &b__ * (&c__ * x_).acos(),
                ))
        },
    ));
}

fn push_rules_rule_5226(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5226,
        source: "Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
          Int[ExpandIntegrand[(a+b*ArcSin[c*x])^n/Sqrt[d+e*x^2],(f*x)^m*(d+e*x^2)^(p+1/2),x],x] /;
        FreeQ[{a,b,c,d,e,f,m,n},x] && EqQ[c^2*d+e,0] && IGtQ[p+1/2,0] && Not[IGtQ[(m+1)/2,0]] && (EqQ[m,-1] || EqQ[m,-2])",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [f__, m_, d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [f__, e__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && igtq!(&p_ + half_integer_atom(1), 0)
                && !igtq!((&m_ + Atom::num(1)) / Atom::num(2), 0)
                && (eqq!(m_, -1) || eqq!(m_, -2))
        },
        rhs: {
            let quadratic = &d__ + &e__ * x_.pow(2);
            let argument = &a__ + &b__ * (&c__ * x_).asin();
            let u = argument.pow(&n_) / &quadratic.sqrt();
            let v = (&f__ * x_).pow(&m_) * quadratic.pow(&p_ + half_integer_atom(1));
            let expanded = rubi_expand_integrand_product(&u, &v, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_5227(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5227,
        source: "Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
          Int[ExpandIntegrand[(a+b*ArcCos[c*x])^n/Sqrt[d+e*x^2],(f*x)^m*(d+e*x^2)^(p+1/2),x],x] /;
        FreeQ[{a,b,c,d,e,f,m,n},x] && EqQ[c^2*d+e,0] && IGtQ[p+1/2,0] && Not[IGtQ[(m+1)/2,0]] && (EqQ[m,-1] || EqQ[m,-2])",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [f__, m_, d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [f__, e__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && igtq!(&p_ + half_integer_atom(1), 0)
                && !igtq!((&m_ + Atom::num(1)) / Atom::num(2), 0)
                && (eqq!(m_, -1) || eqq!(m_, -2))
        },
        rhs: {
            let quadratic = &d__ + &e__ * x_.pow(2);
            let argument = &a__ + &b__ * (&c__ * x_).acos();
            let u = argument.pow(&n_) / &quadratic.sqrt();
            let v = (&f__ * x_).pow(&m_) * quadratic.pow(&p_ + half_integer_atom(1));
            let expanded = rubi_expand_integrand_product(&u, &v, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_5228(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, p_, x_);
    rules.push(rubi_rule!(
        order: 5228,
        source: "Int[x_*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_.*x_]),x_Symbol] :=
          (d+e*x^2)^(p+1)*(a+b*ArcSin[c*x])/(2*e*(p+1)) - b*c/(2*e*(p+1)) \\[Star] Int[(d+e*x^2)^(p+1)/Sqrt[1-c^2*x^2],x] /;
        FreeQ[{a,b,c,d,e,p},x] && NeQ[c^2*d+e,0] && NeQ[p,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern: x_ * (d__ + e__ * x_.pow(2)).pow(p_) * (a__ + b__ * (c__ * x_).asin()),
        with: [d__, e__, p_, a__, b__, c__, x_],
        optional: [e__, p_, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__, p_], x_) && neq!(c__.pow(2) * &d__ + &e__, 0) && neq!(p_, -1)
        },
        rhs: {
            let quadratic = &d__ + &e__ * x_.pow(2);
            let argument = &a__ + &b__ * (&c__ * x_).asin();
            let recursive = quadratic.pow(&p_ + Atom::num(1)) / (Atom::num(1) - c__.pow(2) * x_.pow(2)).sqrt();
            rubi_simp(&(quadratic.pow(&p_ + Atom::num(1)) * argument / (Atom::num(2) * &e__ * (&p_ + Atom::num(1)))), x_)
                    - rubi_star(&b__ * &c__ / (Atom::num(2) * &e__ * (&p_ + Atom::num(1))), rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_5229(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, p_, x_);
    rules.push(rubi_rule!(
        order: 5229,
        source: "Int[x_*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_.*x_]),x_Symbol] :=
          (d+e*x^2)^(p+1)*(a+b*ArcCos[c*x])/(2*e*(p+1)) + b*c/(2*e*(p+1)) \\[Star] Int[(d+e*x^2)^(p+1)/Sqrt[1-c^2*x^2],x] /;
        FreeQ[{a,b,c,d,e,p},x] && NeQ[c^2*d+e,0] && NeQ[p,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern: x_ * (d__ + e__ * x_.pow(2)).pow(p_) * (a__ + b__ * (c__ * x_).acos()),
        with: [d__, e__, p_, a__, b__, c__, x_],
        optional: [e__, p_, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__, p_], x_) && neq!(c__.pow(2) * &d__ + &e__, 0) && neq!(p_, -1)
        },
        rhs: {
            let quadratic = &d__ + &e__ * x_.pow(2);
            let argument = &a__ + &b__ * (&c__ * x_).acos();
            let recursive = quadratic.pow(&p_ + Atom::num(1)) / (Atom::num(1) - c__.pow(2) * x_.pow(2)).sqrt();
            rubi_simp(&(quadratic.pow(&p_ + Atom::num(1)) * argument / (Atom::num(2) * &e__ * (&p_ + Atom::num(1)))), x_)
                    + rubi_star(&b__ * &c__ / (Atom::num(2) * &e__ * (&p_ + Atom::num(1))), rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_5230(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 5230,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_.*x_]),x_Symbol] :=
          With[{u=IntHide[(f*x)^m*(d+e*x^2)^p,x]},
          (a+b*ArcSin[c*x]) \\[Star] u - b*c \\[Star] Int[SimplifyIntegrand[u/Sqrt[1-c^2*x^2],x],x]] /;
        FreeQ[{a,b,c,d,e,f,m},x] && NeQ[c^2*d+e,0] && IntegerQ[p] && (GtQ[p,0] || IGtQ[(m-1)/2,0] && LeQ[m+p,0])",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [f__, m_, d__, e__, p_, a__, b__, c__, x_],
        optional: [f__, m_, e__, p_, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_], x_)
                && neq!(c__.pow(2) * &d__ + &e__, 0)
                && integerq!(p_)
                && (gtq!(p_, 0) || (igtq!((&m_ - Atom::num(1)) / Atom::num(2), 0) && leq!(&m_ + &p_, 0)))
        },
        rhs: {
            let argument = &a__ + &b__ * (&c__ * x_).asin();
            let u = rubi_int_hide(&((&f__ * x_).pow(&m_) * (&d__ + &e__ * x_.pow(2)).pow(&p_)), x_).rubi_rhs();
            let recursive = rubi_simplify_integrand(&(&u / (Atom::num(1) - c__.pow(2) * x_.pow(2)).sqrt()), x_);
            rubi_star(argument, u) - rubi_star(&b__ * &c__, rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_5231(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 5231,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_.*x_]),x_Symbol] :=
          With[{u=IntHide[(f*x)^m*(d+e*x^2)^p,x]},
          (a+b*ArcCos[c*x]) \\[Star] u + b*c \\[Star] Int[SimplifyIntegrand[u/Sqrt[1-c^2*x^2],x],x]] /;
        FreeQ[{a,b,c,d,e,f,m},x] && NeQ[c^2*d+e,0] && IntegerQ[p] && (GtQ[p,0] || IGtQ[(m-1)/2,0] && LeQ[m+p,0])",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [f__, m_, d__, e__, p_, a__, b__, c__, x_],
        optional: [f__, m_, e__, p_, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_], x_)
                && neq!(c__.pow(2) * &d__ + &e__, 0)
                && integerq!(p_)
                && (gtq!(p_, 0) || (igtq!((&m_ - Atom::num(1)) / Atom::num(2), 0) && leq!(&m_ + &p_, 0)))
        },
        rhs: {
            let argument = &a__ + &b__ * (&c__ * x_).acos();
            let u = rubi_int_hide(&((&f__ * x_).pow(&m_) * (&d__ + &e__ * x_.pow(2)).pow(&p_)), x_).rubi_rhs();
            let recursive = rubi_simplify_integrand(&(&u / (Atom::num(1) - c__.pow(2) * x_.pow(2)).sqrt()), x_);
            rubi_star(argument, u) + rubi_star(&b__ * &c__, rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_5232(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5232,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
          Int[ExpandIntegrand[(a+b*ArcSin[c*x])^n,(f*x)^m*(d+e*x^2)^p,x],x] /;
        FreeQ[{a,b,c,d,e,f},x] && NeQ[c^2*d+e,0] && IGtQ[n,0] && IntegerQ[p] && IntegerQ[m]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [f__, m_, d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [f__, m_, e__, p_, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && neq!(c__.pow(2) * &d__ + &e__, 0)
                && igtq!(n_, 0)
                && integerq!(p_)
                && integerq!(m_)
        },
        rhs: {
            let argument = &a__ + &b__ * (&c__ * x_).asin();
            let u = argument.pow(&n_);
            let v = (&f__ * x_).pow(&m_) * (&d__ + &e__ * x_.pow(2)).pow(&p_);
            let expanded = rubi_expand_integrand_product(&u, &v, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_5233(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5233,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
          Int[ExpandIntegrand[(a+b*ArcCos[c*x])^n,(f*x)^m*(d+e*x^2)^p,x],x] /;
        FreeQ[{a,b,c,d,e,f},x] && NeQ[c^2*d+e,0] && IGtQ[n,0] && IntegerQ[p] && IntegerQ[m]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [f__, m_, d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [f__, m_, e__, p_, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && neq!(c__.pow(2) * &d__ + &e__, 0)
                && igtq!(n_, 0)
                && integerq!(p_)
                && integerq!(m_)
        },
        rhs: {
            let argument = &a__ + &b__ * (&c__ * x_).acos();
            let u = argument.pow(&n_);
            let v = (&f__ * x_).pow(&m_) * (&d__ + &e__ * x_.pow(2)).pow(&p_);
            let expanded = rubi_expand_integrand_product(&u, &v, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_5234(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5234,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
          Unintegrable[(f*x)^m*(d+e*x^2)^p*(a+b*ArcSin[c*x])^n,x] /;
        FreeQ[{a,b,c,d,e,f,m,n,p},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [f__, m_, d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [f__, m_, e__, p_, a__, b__, c__, n_],
        when: { freeq!([a__, b__, c__, d__, e__, f__, m_, n_, p_], x_) },
        rhs: {
            let integrand = (&f__ * x_).pow(&m_)
                * (&d__ + &e__ * x_.pow(2)).pow(&p_)
                * (&a__ + &b__ * (&c__ * x_).asin()).pow(&n_);
            rubi_unintegrable(integrand, x_)
        },
    ));
}

fn push_rules_rule_5235(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5235,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
          Unintegrable[(f*x)^m*(d+e*x^2)^p*(a+b*ArcCos[c*x])^n,x] /;
        FreeQ[{a,b,c,d,e,f,m,n,p},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [f__, m_, d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [f__, m_, e__, p_, a__, b__, c__, n_],
        when: { freeq!([a__, b__, c__, d__, e__, f__, m_, n_, p_], x_) },
        rhs: {
            let integrand = (&f__ * x_).pow(&m_)
                * (&d__ + &e__ * x_.pow(2)).pow(&p_)
                * (&a__ + &b__ * (&c__ * x_).acos()).pow(&n_);
            rubi_unintegrable(integrand, x_)
        },
    ));
}

fn push_rules_rule_5236(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, h__, m_, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 5236,
        source: "Int[(h_.*x_)^m_.*(d_+e_.*x_)^p_*(f_+g_.*x_)^q_*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
          (-d^2*g/e)^q \\[Star] Int[(h*x)^m*(d+e*x)^(p-q)*(1-c^2*x^2)^q*(a+b*ArcSin[c*x])^n,x] /;
        FreeQ[{a,b,c,d,e,f,g,h,m,n},x] && EqQ[e*f+d*g,0] && EqQ[c^2*d^2-e^2,0] && HalfIntegerQ[p,q] && GeQ[p-q,0] && GtQ[d,0] && LtQ[g/e,0]",
        desc: "Algebraic normalization",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [h__, m_, d__, e__, p_, f__, g__, q_, a__, b__, c__, n_, x_],
        optional: [h__, m_, e__, g__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__, m_, n_], x_)
                && eqq!(&e__ * &f__ + &d__ * &g__, 0)
                && eqq!(c__.pow(2) * d__.pow(2) - e__.pow(2), 0)
                && half_integer_numerator(&p_).is_some()
                && half_integer_numerator(&q_).is_some()
                && geq!(&p_ - &q_, 0)
                && gtq!(d__, 0)
                && ltq!(&g__ / &e__, 0)
        },
        rhs: {
            let transformed = (&h__ * x_).pow(&m_)
                * (&d__ + &e__ * x_).pow(&p_ - &q_)
                * (Atom::num(1) - c__.pow(2) * x_.pow(2)).pow(&q_)
                * (&a__ + &b__ * (&c__ * x_).asin()).pow(&n_);
            rubi_star((-d__.pow(2) * &g__ / &e__).pow(&q_), rubi_rhs_int(&transformed, x_))
        },
    ));
}

fn push_rules_rule_5237(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, h__, m_, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 5237,
        source: "Int[(h_.*x_)^m_.*(d_+e_.*x_)^p_*(f_+g_.*x_)^q_*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
          (-d^2*g/e)^q \\[Star] Int[(h*x)^m*(d+e*x)^(p-q)*(1-c^2*x^2)^q*(a+b*ArcCos[c*x])^n,x] /;
        FreeQ[{a,b,c,d,e,f,g,h,m,n},x] && EqQ[e*f+d*g,0] && EqQ[c^2*d^2-e^2,0] && HalfIntegerQ[p,q] && GeQ[p-q,0] && GtQ[d,0] && LtQ[g/e,0]",
        desc: "Algebraic normalization",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [h__, m_, d__, e__, p_, f__, g__, q_, a__, b__, c__, n_, x_],
        optional: [h__, m_, e__, g__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__, m_, n_], x_)
                && eqq!(&e__ * &f__ + &d__ * &g__, 0)
                && eqq!(c__.pow(2) * d__.pow(2) - e__.pow(2), 0)
                && half_integer_numerator(&p_).is_some()
                && half_integer_numerator(&q_).is_some()
                && geq!(&p_ - &q_, 0)
                && gtq!(d__, 0)
                && ltq!(&g__ / &e__, 0)
        },
        rhs: {
            let transformed = (&h__ * x_).pow(&m_)
                * (&d__ + &e__ * x_).pow(&p_ - &q_)
                * (Atom::num(1) - c__.pow(2) * x_.pow(2)).pow(&q_)
                * (&a__ + &b__ * (&c__ * x_).acos()).pow(&n_);
            rubi_star((-d__.pow(2) * &g__ / &e__).pow(&q_), rubi_rhs_int(&transformed, x_))
        },
    ));
}

fn push_rules_rule_5238(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, h__, m_, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 5238,
        source: "Int[(h_.*x_)^m_.*(d_+e_.*x_)^p_*(f_+g_.*x_)^q_*(a_.+b_.*ArcSin[c_.*x_])^n_.,x_Symbol] :=
          (-d^2*g/e)^IntPart[q]*(d+e*x)^FracPart[q]*(f+g*x)^FracPart[q]/(1-c^2*x^2)^FracPart[q] \\[Star]
            Int[(h*x)^m*(d+e*x)^(p-q)*(1-c^2*x^2)^q*(a+b*ArcSin[c*x])^n,x] /;
        FreeQ[{a,b,c,d,e,f,g,h,m,n},x] && EqQ[e*f+d*g,0] && EqQ[c^2*d^2-e^2,0] && HalfIntegerQ[p,q] && GeQ[p-q,0]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [h__, m_, d__, e__, p_, f__, g__, q_, a__, b__, c__, n_, x_],
        optional: [h__, m_, e__, g__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__, m_, n_], x_)
                && eqq!(&e__ * &f__ + &d__ * &g__, 0)
                && eqq!(c__.pow(2) * d__.pow(2) - e__.pow(2), 0)
                && half_integer_numerator(&p_).is_some()
                && half_integer_numerator(&q_).is_some()
                && geq!(&p_ - &q_, 0)
        },
        rhs: {
            let int_q = rubi_int_part(&q_);
            let frac_q = rubi_frac_part(&q_);
            let unit = Atom::num(1) - c__.pow(2) * x_.pow(2);
            let transformed = (&h__ * x_).pow(&m_)
                * (&d__ + &e__ * x_).pow(&p_ - &q_)
                * unit.pow(&q_)
                * (&a__ + &b__ * (&c__ * x_).asin()).pow(&n_);
            rubi_star((-d__.pow(2) * &g__ / &e__).pow(int_q)
                    * (&d__ + &e__ * x_).pow(&frac_q)
                    * (&f__ + &g__ * x_).pow(&frac_q)
                    / unit.pow(&frac_q), rubi_rhs_int(&transformed, x_))
        },
    ));
}

fn push_rules_rule_5239(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, h__, m_, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 5239,
        source: "Int[(h_.*x_)^m_.*(d_+e_.*x_)^p_*(f_+g_.*x_)^q_*(a_.+b_.*ArcCos[c_.*x_])^n_.,x_Symbol] :=
          (-d^2*g/e)^IntPart[q]*(d+e*x)^FracPart[q]*(f+g*x)^FracPart[q]/(1-c^2*x^2)^FracPart[q] \\[Star]
            Int[(h*x)^m*(d+e*x)^(p-q)*(1-c^2*x^2)^q*(a+b*ArcCos[c*x])^n,x] /;
        FreeQ[{a,b,c,d,e,f,g,h,m,n},x] && EqQ[e*f+d*g,0] && EqQ[c^2*d^2-e^2,0] && HalfIntegerQ[p,q] && GeQ[p-q,0]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [h__, m_, d__, e__, p_, f__, g__, q_, a__, b__, c__, n_, x_],
        optional: [h__, m_, e__, g__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__, m_, n_], x_)
                && eqq!(&e__ * &f__ + &d__ * &g__, 0)
                && eqq!(c__.pow(2) * d__.pow(2) - e__.pow(2), 0)
                && half_integer_numerator(&p_).is_some()
                && half_integer_numerator(&q_).is_some()
                && geq!(&p_ - &q_, 0)
        },
        rhs: {
            let int_q = rubi_int_part(&q_);
            let frac_q = rubi_frac_part(&q_);
            let unit = Atom::num(1) - c__.pow(2) * x_.pow(2);
            let transformed = (&h__ * x_).pow(&m_)
                * (&d__ + &e__ * x_).pow(&p_ - &q_)
                * unit.pow(&q_)
                * (&a__ + &b__ * (&c__ * x_).acos()).pow(&n_);
            rubi_star((-d__.pow(2) * &g__ / &e__).pow(int_q)
                    * (&d__ + &e__ * x_).pow(&frac_q)
                    * (&f__ + &g__ * x_).pow(&frac_q)
                    / unit.pow(&frac_q), rubi_rhs_int(&transformed, x_))
        },
    ));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn downvalues_5180_through_5192_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .filter(|order| (5180..=5192).contains(order))
            .collect::<Vec<_>>();
        assert_eq!(orders, (5180..=5192).collect::<Vec<_>>());
    }

    #[test]
    fn global_downvalues_5143_through_5192_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        crate::rules::push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .filter(|order| (5143..=5192).contains(order))
            .collect::<Vec<_>>();
        assert_eq!(orders, (5143..=5192).collect::<Vec<_>>());
    }

    #[test]
    fn downvalues_5193_through_5239_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .filter(|order| (5193..=5239).contains(order))
            .collect::<Vec<_>>();
        assert_eq!(orders, (5193..=5239).collect::<Vec<_>>());
    }
}

// Generated shared pattern builders.

#[inline(never)]
fn rubi_shared_pattern_0(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    (f__ * x_).pow(m_) * (a__ + b__ * (c__ * x_).acos()).pow(n_) / (d__ + e__ * x_.pow(2)).sqrt()
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    (f__ * x_).pow(m_) * (a__ + b__ * (c__ * x_).asin()).pow(n_) / (d__ + e__ * x_.pow(2)).sqrt()
}

#[inline(never)]
fn rubi_shared_pattern_2(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (f__ * x_).pow(m_) * (d__ + e__ * x_.pow(2)).pow(p_) * (a__ + b__ * (c__ * x_).acos())
}

#[inline(never)]
fn rubi_shared_pattern_3(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (f__ * x_).pow(m_) * (d__ + e__ * x_.pow(2)).pow(p_) * (a__ + b__ * (c__ * x_).acos()).pow(n_)
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
    (f__ * x_).pow(m_) * (d__ + e__ * x_.pow(2)).pow(p_) * (a__ + b__ * (c__ * x_).asin())
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
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (f__ * x_).pow(m_) * (d__ + e__ * x_.pow(2)).pow(p_) * (a__ + b__ * (c__ * x_).asin()).pow(n_)
}

#[inline(never)]
fn rubi_shared_pattern_6(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    (f__ * x_).pow(m_) * (d__ + e__ * x_.pow(2)).sqrt() * (a__ + b__ * (c__ * x_).acos()).pow(n_)
}

#[inline(never)]
fn rubi_shared_pattern_7(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    (f__ * x_).pow(m_) * (d__ + e__ * x_.pow(2)).sqrt() * (a__ + b__ * (c__ * x_).asin()).pow(n_)
}

#[inline(never)]
fn rubi_shared_pattern_8(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let g__ = symbols.g__;
    let h__ = symbols.h__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let q_ = symbols.q_;
    let x_ = symbols.x_;
    (h__ * x_).pow(m_)
        * (d__ + e__ * x_).pow(p_)
        * (f__ + g__ * x_).pow(q_)
        * (a__ + b__ * (c__ * x_).acos()).pow(n_)
}

#[inline(never)]
fn rubi_shared_pattern_9(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let g__ = symbols.g__;
    let h__ = symbols.h__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let q_ = symbols.q_;
    let x_ = symbols.x_;
    (h__ * x_).pow(m_)
        * (d__ + e__ * x_).pow(p_)
        * (f__ + g__ * x_).pow(q_)
        * (a__ + b__ * (c__ * x_).asin()).pow(n_)
}
