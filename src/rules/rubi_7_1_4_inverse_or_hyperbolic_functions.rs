use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_6212(rules);
    push_rules_rule_6213(rules);
    push_rules_rule_6214(rules);
    push_rules_rule_6215(rules);
    push_rules_rule_6216(rules);
    push_rules_rule_6217(rules);
    push_rules_rule_6218(rules);
    push_rules_rule_6219(rules);
    push_rules_rule_6220(rules);
    push_rules_rule_6221(rules);
    push_rules_rule_6222(rules);
    push_rules_rule_6223(rules);
    push_rules_rule_6224(rules);
    push_rules_rule_6225(rules);
    push_rules_rule_6226(rules);
    push_rules_rule_6227(rules);
    push_rules_rule_6228(rules);
    push_rules_rule_6229(rules);
    // Block 19 is disabled in the Rubi source embedded in docs/rubi_pdf_rules.md.

    push_rules_rule_6230(rules);
    push_rules_rule_6231(rules);
    push_rules_rule_6232(rules);
    push_rules_rule_6233(rules);
    push_rules_rule_6234(rules);
    push_rules_rule_6235(rules);
    push_rules_rule_6236(rules);
    push_rules_rule_6237(rules);
    push_rules_rule_6238(rules);
    push_rules_rule_6239(rules);
    push_rules_rule_6240(rules);
    push_rules_rule_6241(rules);
}

fn push_rules_rule_6212(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 6212,
        source: "Int[x_*(a_.+b_.*ArcSinh[c_.*x_])^n_./(d_+e_.*x_^2),x_Symbol] :=
          1/e \\[Star] Subst[Int[(a+b*x)^n*Tanh[x],x],x,ArcSinh[c*x]] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[e,c^2*d] && IGtQ[n,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: x_ * (a__ + b__ * (c__ * x_).asinh()).pow(n_) / (d__ + e__ * x_.pow(2)),
        with: [a__, b__, c__, n_, d__, e__, x_],
        optional: [a__, b__, c__, e__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(e__, c__.pow(2) * &d__)
                && igtq!(n_, 0)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let substitution_integrand = (&a__ + &b__ * &sub_atom).pow(&n_) * sub_atom.tanh();
            let substitution_primitive =
                rubi_rhs_int(&substitution_integrand, substitution_symbol);
            let substituted = rubi_subst(
                &substitution_primitive,
                substitution_symbol,
                (&c__ * x_).asinh(),
            );
            rubi_star(Atom::num(1) / &e__, substituted)
        },
    ));
}

fn push_rules_rule_6213(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6213,
        source: "Int[x_*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
          (d+e*x^2)^(p+1)*(a+b*ArcSinh[c*x])^n/(2*e*(p+1)) -
          b*n/(2*c*(p+1))*Simp[(d+e*x^2)^p/(1+c^2*x^2)^p] \\[Star] Int[(1+c^2*x^2)^(p+1/2)*(a+b*ArcSinh[c*x])^(n-1),x] /;
        FreeQ[{a,b,c,d,e,p},x] && EqQ[e,c^2*d] && GtQ[n,0] && NeQ[p,-1]",
        desc: "Integration by parts and piecewise constant extraction",
        refs: [],
        pattern: x_ * (d__ + e__ * x_.pow(2)).pow(p_) * (a__ + b__ * (c__ * x_).asinh()).pow(n_),
        with: [d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [e__, a__, b__, c__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, p_], x_)
                && eqq!(e__, c__.pow(2) * &d__)
                && gtq!(n_, 0)
                && neq!(p_, -1)
        },
        rhs: {
            let quadratic_x = &d__ + &e__ * x_.pow(2);
            let unit_x = Atom::num(1) + c__.pow(2) * x_.pow(2);
            let argument = &a__ + &b__ * (&c__ * x_).asinh();
            let recursive_integrand = unit_x

                .pow(&p_ + Atom::num(1) / Atom::num(2))
                * argument.pow(&n_ - Atom::num(1));
            let coefficient = &b__ * &n_ / (Atom::num(2) * &c__ * (&p_ + Atom::num(1)))
                * rubi_simp(&(quadratic_x.pow(&p_) / unit_x.pow(&p_)), x_);
            rubi_simp(&(quadratic_x.pow(&p_ + Atom::num(1)) * argument.pow(&n_)
                    / (Atom::num(2) * &e__ * (&p_ + Atom::num(1)))), x_)
                    - rubi_star(coefficient, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_6214(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 6214,
        source: "Int[(a_.+b_.*ArcSinh[c_.*x_])^n_./(x_*(d_+e_.*x_^2)),x_Symbol] :=
          1/d \\[Star] Subst[Int[(a+b*x)^n/(Cosh[x]*Sinh[x]),x],x,ArcSinh[c*x]] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[e,c^2*d] && IGtQ[n,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (a__ + b__ * (c__ * x_).asinh()).pow(n_) / (x_ * (d__ + e__ * x_.pow(2))),
        with: [a__, b__, c__, n_, d__, e__, x_],
        optional: [a__, b__, c__, e__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(e__, c__.pow(2) * &d__)
                && igtq!(n_, 0)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let substitution_integrand =
                (&a__ + &b__ * &sub_atom).pow(&n_) / (sub_atom.cosh() * sub_atom.sinh());
            let substitution_primitive =
                rubi_rhs_int(&substitution_integrand, substitution_symbol);
            let substituted = rubi_subst(
                &substitution_primitive,
                substitution_symbol,
                (&c__ * x_).asinh(),
            );
            rubi_star(Atom::num(1) / &d__, substituted)
        },
    ));
}

fn push_rules_rule_6215(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6215,
        source: "Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
          (f*x)^(m+1)*(d+e*x^2)^(p+1)*(a+b*ArcSinh[c*x])^n/(d*f*(m+1)) -
          b*c*n/(f*(m+1))*Simp[(d+e*x^2)^p/(1+c^2*x^2)^p] \\[Star] Int[(f*x)^(m+1)*(1+c^2*x^2)^(p+1/2)*(a+b*ArcSinh[c*x])^(n-1),x] /;
        FreeQ[{a,b,c,d,e,f,m,p},x] && EqQ[e,c^2*d] && GtQ[n,0] && EqQ[m+2*p+3,0] && NeQ[m,-1]",
        desc: "Integration by parts and piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [f__, m_, d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [f__, e__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, p_], x_)
                && eqq!(e__, c__.pow(2) * &d__)
                && gtq!(n_, 0)
                && eqq!(&m_ + Atom::num(2) * &p_ + 3, 0)
                && neq!(m_, -1)
        },
        rhs: {
            let scaled = &f__ * x_;
            let quadratic_x = &d__ + &e__ * x_.pow(2);
            let unit_x = Atom::num(1) + c__.pow(2) * x_.pow(2);
            let argument = &a__ + &b__ * (&c__ * x_).asinh();
            let recursive_integrand = scaled.pow(&m_ + Atom::num(1))
                * unit_x.pow(&p_ + Atom::num(1) / Atom::num(2))
                * argument.pow(&n_ - Atom::num(1));
            let coefficient = &b__ * &c__ * &n_ / (&f__ * (&m_ + Atom::num(1)))
                * rubi_simp(&(quadratic_x.pow(&p_) / unit_x.pow(&p_)), x_);
            rubi_simp(&(scaled.pow(&m_ + Atom::num(1))
                    * quadratic_x.pow(&p_ + Atom::num(1))
                    * argument.pow(&n_)
                    / (&d__ * &f__ * (&m_ + Atom::num(1)))), x_)
                    - rubi_star(coefficient, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_6216(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, p_, x_);
    rules.push(rubi_rule!(
        order: 6216,
        source: "Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSinh[c_.*x_])/x_,x_Symbol] :=
          (d+e*x^2)^p*(a+b*ArcSinh[c*x])/(2*p) -
          b*c*d^p/(2*p) \\[Star] Int[(1+c^2*x^2)^(p-1/2),x] +
          d \\[Star] Int[(d+e*x^2)^(p-1)*(a+b*ArcSinh[c*x])/x,x] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[e,c^2*d] && IGtQ[p,0]",
        desc: "Inverted integration by parts",
        refs: [],
        pattern: (d__ + e__ * x_.pow(2)).pow(p_) * (a__ + b__ * (c__ * x_).asinh()) / x_,
        with: [d__, e__, p_, a__, b__, c__, x_],
        optional: [e__, a__, b__, c__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(e__, c__.pow(2) * &d__)
                && igtq!(p_, 0)
        },
        rhs: {
            let quadratic_x = &d__ + &e__ * x_.pow(2);
            let argument = &a__ + &b__ * (&c__ * x_).asinh();
            let recursive_1 =
                (Atom::num(1) + c__.pow(2) * x_.pow(2)).pow(&p_ - Atom::num(1) / Atom::num(2));
            let recursive_2 = quadratic_x.pow(&p_ - Atom::num(1)) * &argument / x_;
            rubi_simp(&(quadratic_x.pow(&p_) * argument / (Atom::num(2) * &p_)), x_)
                    - rubi_star(&b__ * &c__ * d__.pow(&p_) / (Atom::num(2) * &p_), rubi_rhs_int(&recursive_1, x_))
                    + rubi_star(d__, rubi_rhs_int(&recursive_2, x_))
        },
    ));
}

fn push_rules_rule_6217(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 6217,
        source: "Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSinh[c_.*x_]),x_Symbol] :=
          (f*x)^(m+1)*(d+e*x^2)^p*(a+b*ArcSinh[c*x])/(f*(m+1)) -
          b*c*d^p/(f*(m+1)) \\[Star] Int[(f*x)^(m+1)*(1+c^2*x^2)^(p-1/2),x] -
          2*e*p/(f^2*(m+1)) \\[Star] Int[(f*x)^(m+2)*(d+e*x^2)^(p-1)*(a+b*ArcSinh[c*x]),x] /;
        FreeQ[{a,b,c,d,e,f},x] && EqQ[e,c^2*d] && IGtQ[p,0] && ILtQ[(m+1)/2,0]",
        desc: "Inverted integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [f__, m_, d__, e__, p_, a__, b__, c__, x_],
        optional: [f__, e__, p_, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && eqq!(e__, c__.pow(2) * &d__)
                && igtq!(p_, 0)
                && iltq!((&m_ + Atom::num(1)) / Atom::num(2), 0)
        },
        rhs: {
            let scaled = &f__ * x_;
            let quadratic_x = &d__ + &e__ * x_.pow(2);
            let argument = &a__ + &b__ * (&c__ * x_).asinh();
            let recursive_1 = scaled.pow(&m_ + Atom::num(1))
                * (Atom::num(1) + c__.pow(2) * x_.pow(2))
                    .pow(&p_ - Atom::num(1) / Atom::num(2));
            let recursive_2 = scaled.pow(&m_ + Atom::num(2))
                * quadratic_x.pow(&p_ - Atom::num(1))
                * &argument;
            rubi_simp(&(scaled.pow(&m_ + Atom::num(1)) * quadratic_x.pow(&p_) * argument
                    / (&f__ * (&m_ + Atom::num(1)))), x_)
                    - rubi_star(&b__ * &c__ * d__.pow(&p_) / (&f__ * (&m_ + Atom::num(1))), rubi_rhs_int(&recursive_1, x_))
                    - rubi_star(Atom::num(2) * &e__ * &p_
                            / (f__.pow(2) * (&m_ + Atom::num(1))), rubi_rhs_int(&recursive_2, x_))
        },
    ));
}

fn push_rules_rule_6218(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 6218,
        source: "Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSinh[c_.*x_]),x_Symbol] :=
          With[{u=IntHide[(f*x)^m*(d+e*x^2)^p,x]},
          (a+b*ArcSinh[c*x]) \\[Star] u - b*c \\[Star] Int[SimplifyIntegrand[u/Sqrt[1+c^2*x^2],x],x]] /;
        FreeQ[{a,b,c,d,e,f,m},x] && EqQ[e,c^2*d] && IGtQ[p,0]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [f__, m_, d__, e__, p_, a__, b__, c__, x_],
        optional: [f__, e__, p_, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_], x_)
                && eqq!(e__, c__.pow(2) * &d__)
                && igtq!(p_, 0)
        },
        rhs: {
            let argument = &a__ + &b__ * (&c__ * x_).asinh();
            let u = rubi_int_hide(
                &((&f__ * x_).pow(&m_) * (&d__ + &e__ * x_.pow(2)).pow(&p_)),
                x_,
            ).rubi_rhs();
            let recursive = rubi_simplify_integrand(
                &(&u / (Atom::num(1) + c__.pow(2) * x_.pow(2)).sqrt()),
                x_,
            );
            rubi_star(argument, u)
                    - rubi_star(&b__ * &c__, rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_6219(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 6219,
        source: "Int[x_^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSinh[c_.*x_]),x_Symbol] :=
          With[{u=IntHide[x^m*(d+e*x^2)^p,x]},
          (a+b*ArcSinh[c*x]) \\[Star] u -
          b*c*Simp[Sqrt[d+e*x^2]/Sqrt[1+c^2*x^2]] \\[Star] Int[SimplifyIntegrand[u/Sqrt[d+e*x^2],x],x]] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[e,c^2*d] && IntegerQ[p-1/2] && NeQ[p,-1/2] && (IGtQ[(m+1)/2,0] || ILtQ[(m+2*p+3)/2,0])",
        desc: "Integration by parts and piecewise constant extraction",
        refs: [],
        pattern: x_.pow(m_) * (d__ + e__ * x_.pow(2)).pow(p_) * (a__ + b__ * (c__ * x_).asinh()),
        with: [m_, d__, e__, p_, a__, b__, c__, x_],
        optional: [e__, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(e__, c__.pow(2) * &d__)
                && integerq!(&p_ - Atom::num(1) / Atom::num(2))
                && neq!(p_, -(Atom::num(1) / Atom::num(2)))
                && (igtq!((&m_ + Atom::num(1)) / Atom::num(2), 0)
                    || iltq!((&m_ + Atom::num(2) * &p_ + 3) / Atom::num(2), 0))
        },
        rhs: {
            let quadratic_x = &d__ + &e__ * x_.pow(2);
            let argument = &a__ + &b__ * (&c__ * x_).asinh();
            let u = rubi_int_hide(&(x_.pow(&m_) * quadratic_x.pow(&p_)), x_).rubi_rhs();
            let recursive = rubi_simplify_integrand(&(&u / quadratic_x.sqrt()), x_);
            let coefficient = &b__
                * &c__
                * rubi_simp(
                    &(quadratic_x.sqrt()
                        / (Atom::num(1) + c__.pow(2) * x_.pow(2)).sqrt()),
                    x_,
                );
            rubi_star(argument, u)
                    - rubi_star(coefficient, rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_6220(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 6220,
        source: "Int[(f_.*x_)^m_*Sqrt[d_+e_.*x_^2]*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
          (f*x)^(m+1)*Sqrt[d+e*x^2]*(a+b*ArcSinh[c*x])^n/(f*(m+1)) -
          b*c*n/(f*(m+1))*Simp[Sqrt[d+e*x^2]/Sqrt[1+c^2*x^2]] \\[Star] Int[(f*x)^(m+1)*(a+b*ArcSinh[c*x])^(n-1),x] -
          c^2/(f^2*(m+1))*Simp[Sqrt[d+e*x^2]/Sqrt[1+c^2*x^2]] \\[Star] Int[(f*x)^(m+2)*(a+b*ArcSinh[c*x])^n/Sqrt[1+c^2*x^2],x] /;
        FreeQ[{a,b,c,d,e,f},x] && EqQ[e,c^2*d] && GtQ[n,0] && LtQ[m,-1]",
        desc: "Inverted integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [f__, m_, d__, e__, a__, b__, c__, n_, x_],
        optional: [f__, e__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && eqq!(e__, c__.pow(2) * &d__)
                && gtq!(n_, 0)
                && ltq!(m_, -1)
        },
        rhs: {
            let scaled = &f__ * x_;
            let quadratic_x = &d__ + &e__ * x_.pow(2);
            let unit_x = Atom::num(1) + c__.pow(2) * x_.pow(2);
            let argument = &a__ + &b__ * (&c__ * x_).asinh();
            let ratio_1 = rubi_simp(&(quadratic_x.sqrt() / unit_x.sqrt()), x_);
            let ratio_2 = rubi_simp(&(quadratic_x.sqrt() / unit_x.sqrt()), x_);
            let recursive_1 = scaled.pow(&m_ + Atom::num(1))
                * argument.pow(&n_ - Atom::num(1));
            let recursive_2 =
                scaled.pow(&m_ + Atom::num(2)) * argument.pow(&n_) / unit_x.sqrt();
            rubi_simp(&(scaled.pow(&m_ + Atom::num(1)) * quadratic_x.sqrt() * argument.pow(&n_)
                    / (&f__ * (&m_ + Atom::num(1)))), x_)
                    - rubi_star(&b__ * &c__ * &n_ / (&f__ * (&m_ + Atom::num(1))) * ratio_1, rubi_rhs_int(&recursive_1, x_))
                    - rubi_star(c__.pow(2) / (f__.pow(2) * (&m_ + Atom::num(1))) * ratio_2, rubi_rhs_int(&recursive_2, x_))
        },
    ));
}

fn push_rules_rule_6221(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 6221,
        source: "Int[(f_.*x_)^m_*Sqrt[d_+e_.*x_^2]*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
          (f*x)^(m+1)*Sqrt[d+e*x^2]*(a+b*ArcSinh[c*x])^n/(f*(m+2)) -
          b*c*n/(f*(m+2))*Simp[Sqrt[d+e*x^2]/Sqrt[1+c^2*x^2]] \\[Star] Int[(f*x)^(m+1)*(a+b*ArcSinh[c*x])^(n-1),x] +
          1/(m+2)*Simp[Sqrt[d+e*x^2]/Sqrt[1+c^2*x^2]] \\[Star] Int[(f*x)^m*(a+b*ArcSinh[c*x])^n/Sqrt[1+c^2*x^2],x] /;
        FreeQ[{a,b,c,d,e,f,m},x] && EqQ[e,c^2*d] && IGtQ[n,0] && (IGtQ[m,-2] || EqQ[n,1])",
        desc: "Inverted integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [f__, m_, d__, e__, a__, b__, c__, n_, x_],
        optional: [f__, e__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_], x_)
                && eqq!(e__, c__.pow(2) * &d__)
                && igtq!(n_, 0)
                && (igtq!(m_, -2) || eqq!(n_, 1))
        },
        rhs: {
            let scaled = &f__ * x_;
            let quadratic_x = &d__ + &e__ * x_.pow(2);
            let unit_x = Atom::num(1) + c__.pow(2) * x_.pow(2);
            let argument = &a__ + &b__ * (&c__ * x_).asinh();
            let ratio_1 = rubi_simp(&(quadratic_x.sqrt() / unit_x.sqrt()), x_);
            let ratio_2 = rubi_simp(&(quadratic_x.sqrt() / unit_x.sqrt()), x_);
            let recursive_1 = scaled.pow(&m_ + Atom::num(1))
                * argument.pow(&n_ - Atom::num(1));
            let recursive_2 = scaled.pow(&m_) * argument.pow(&n_) / unit_x.sqrt();
            rubi_simp(&(scaled.pow(&m_ + Atom::num(1)) * quadratic_x.sqrt() * argument.pow(&n_)
                    / (&f__ * (&m_ + Atom::num(2)))), x_)
                    - rubi_star(&b__ * &c__ * &n_ / (&f__ * (&m_ + Atom::num(2))) * ratio_1, rubi_rhs_int(&recursive_1, x_))
                    + rubi_star(ratio_2 / (&m_ + Atom::num(2)), rubi_rhs_int(&recursive_2, x_))
        },
    ));
}

fn push_rules_rule_6222(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6222,
        source: "Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
          (f*x)^(m+1)*(d+e*x^2)^p*(a+b*ArcSinh[c*x])^n/(f*(m+1)) -
          2*e*p/(f^2*(m+1)) \\[Star] Int[(f*x)^(m+2)*(d+e*x^2)^(p-1)*(a+b*ArcSinh[c*x])^n,x] -
          b*c*n/(f*(m+1))*Simp[(d+e*x^2)^p/(1+c^2*x^2)^p] \\[Star] Int[(f*x)^(m+1)*(1+c^2*x^2)^(p-1/2)*(a+b*ArcSinh[c*x])^(n-1),x] /;
        FreeQ[{a,b,c,d,e,f},x] && EqQ[e,c^2*d] && GtQ[n,0] && GtQ[p,0] && LtQ[m,-1]",
        desc: "Inverted integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [f__, m_, d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [f__, e__, p_, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && eqq!(e__, c__.pow(2) * &d__)
                && gtq!(n_, 0)
                && gtq!(p_, 0)
                && ltq!(m_, -1)
        },
        rhs: {
            let scaled = &f__ * x_;
            let quadratic = &d__ + &e__ * x_.pow(2);
            let unit = Atom::num(1) + c__.pow(2) * x_.pow(2);
            let argument = &a__ + &b__ * (&c__ * x_).asinh();
            let recursive_1 = scaled.pow(&m_ + Atom::num(2))
                * quadratic.pow(&p_ - Atom::num(1))
                * argument.pow(&n_);
            let recursive_2 = scaled.pow(&m_ + Atom::num(1))
                * unit.pow(&p_ - Atom::num(1) / Atom::num(2))
                * argument.pow(&n_ - Atom::num(1));
            let coefficient_1 = Atom::num(2) * &e__ * &p_
                / (f__.pow(2) * (&m_ + Atom::num(1)));
            let coefficient_2 = &b__ * &c__ * &n_
                / (&f__ * (&m_ + Atom::num(1)))
                * rubi_simp(&(quadratic.pow(&p_) / unit.pow(&p_)), x_);
            rubi_simp(&(scaled.pow(&m_ + Atom::num(1))
                    * quadratic.pow(&p_)
                    * argument.pow(&n_)
                    / (&f__ * (&m_ + Atom::num(1)))), x_)
                    - rubi_star(coefficient_1, rubi_rhs_int(&recursive_1, x_))
                    - rubi_star(coefficient_2, rubi_rhs_int(&recursive_2, x_))
        },
    ));
}

fn push_rules_rule_6223(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6223,
        source: "Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
          (f*x)^(m+1)*(d+e*x^2)^p*(a+b*ArcSinh[c*x])^n/(f*(m+2*p+1)) +
          2*d*p/(m+2*p+1) \\[Star] Int[(f*x)^m*(d+e*x^2)^(p-1)*(a+b*ArcSinh[c*x])^n,x] -
          b*c*n/(f*(m+2*p+1))*Simp[(d+e*x^2)^p/(1+c^2*x^2)^p] \\[Star] Int[(f*x)^(m+1)*(1+c^2*x^2)^(p-1/2)*(a+b*ArcSinh[c*x])^(n-1),x] /;
        FreeQ[{a,b,c,d,e,f,m},x] && EqQ[e,c^2*d] && GtQ[n,0] && GtQ[p,0] && Not[LtQ[m,-1]]",
        desc: "Inverted integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [f__, m_, d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [f__, e__, p_, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_], x_)
                && eqq!(e__, c__.pow(2) * &d__)
                && gtq!(n_, 0)
                && gtq!(p_, 0)
                && !ltq!(m_, -1)
        },
        rhs: {
            let scaled = &f__ * x_;
            let quadratic = &d__ + &e__ * x_.pow(2);
            let unit = Atom::num(1) + c__.pow(2) * x_.pow(2);
            let argument = &a__ + &b__ * (&c__ * x_).asinh();
            let denominator = &m_ + Atom::num(2) * &p_ + 1;
            let recursive_1 = scaled.pow(&m_)
                * quadratic.pow(&p_ - Atom::num(1))
                * argument.pow(&n_);
            let recursive_2 = scaled.pow(&m_ + Atom::num(1))
                * unit.pow(&p_ - Atom::num(1) / Atom::num(2))
                * argument.pow(&n_ - Atom::num(1));
            let coefficient_1 = Atom::num(2) * &d__ * &p_ / &denominator;
            let coefficient_2 = &b__ * &c__ * &n_ / (&f__ * &denominator)
                * rubi_simp(&(quadratic.pow(&p_) / unit.pow(&p_)), x_);
            rubi_simp(&(scaled.pow(&m_ + Atom::num(1))
                    * quadratic.pow(&p_)
                    * argument.pow(&n_)
                    / (&f__ * &denominator)), x_)
                    + rubi_star(coefficient_1, rubi_rhs_int(&recursive_1, x_))
                    - rubi_star(coefficient_2, rubi_rhs_int(&recursive_2, x_))
        },
    ));
}

fn push_rules_rule_6224(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6224,
        source: "Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
          (f*x)^(m+1)*(d+e*x^2)^(p+1)*(a+b*ArcSinh[c*x])^n/(d*f*(m+1)) -
          c^2*(m+2*p+3)/(f^2*(m+1)) \\[Star] Int[(f*x)^(m+2)*(d+e*x^2)^p*(a+b*ArcSinh[c*x])^n,x] -
          b*c*n/(f*(m+1))*Simp[(d+e*x^2)^p/(1+c^2*x^2)^p] \\[Star] Int[(f*x)^(m+1)*(1+c^2*x^2)^(p+1/2)*(a+b*ArcSinh[c*x])^(n-1),x] /;
        FreeQ[{a,b,c,d,e,f,p},x] && EqQ[e,c^2*d] && GtQ[n,0] && ILtQ[m,-1]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [f__, m_, d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [f__, e__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, p_], x_)
                && eqq!(e__, c__.pow(2) * &d__)
                && gtq!(n_, 0)
                && iltq!(m_, -1)
        },
        rhs: {
            let scaled = &f__ * x_;
            let quadratic = &d__ + &e__ * x_.pow(2);
            let unit = Atom::num(1) + c__.pow(2) * x_.pow(2);
            let argument = &a__ + &b__ * (&c__ * x_).asinh();
            let recursive_1 = scaled.pow(&m_ + Atom::num(2))
                * quadratic.pow(&p_)
                * argument.pow(&n_);
            let recursive_2 = scaled.pow(&m_ + Atom::num(1))
                * unit.pow(&p_ + Atom::num(1) / Atom::num(2))
                * argument.pow(&n_ - Atom::num(1));
            let coefficient_1 = c__.pow(2) * (&m_ + Atom::num(2) * &p_ + 3)
                / (f__.pow(2) * (&m_ + Atom::num(1)));
            let coefficient_2 = &b__ * &c__ * &n_
                / (&f__ * (&m_ + Atom::num(1)))
                * rubi_simp(&(quadratic.pow(&p_) / unit.pow(&p_)), x_);
            rubi_simp(&(scaled.pow(&m_ + Atom::num(1))
                    * quadratic.pow(&p_ + Atom::num(1))
                    * argument.pow(&n_)
                    / (&d__ * &f__ * (&m_ + Atom::num(1)))), x_)
                    - rubi_star(coefficient_1, rubi_rhs_int(&recursive_1, x_))
                    - rubi_star(coefficient_2, rubi_rhs_int(&recursive_2, x_))
        },
    ));
}

fn push_rules_rule_6225(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6225,
        source: "Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
          f*(f*x)^(m-1)*(d+e*x^2)^(p+1)*(a+b*ArcSinh[c*x])^n/(2*e*(p+1)) -
          f^2*(m-1)/(2*e*(p+1)) \\[Star] Int[(f*x)^(m-2)*(d+e*x^2)^(p+1)*(a+b*ArcSinh[c*x])^n,x] -
          b*f*n/(2*c*(p+1))*Simp[(d+e*x^2)^p/(1+c^2*x^2)^p] \\[Star] Int[(f*x)^(m-1)*(1+c^2*x^2)^(p+1/2)*(a+b*ArcSinh[c*x])^(n-1),x] /;
        FreeQ[{a,b,c,d,e,f},x] && EqQ[e,c^2*d] && GtQ[n,0] && LtQ[p,-1] && IGtQ[m,1]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [f__, m_, d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [f__, e__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && eqq!(e__, c__.pow(2) * &d__)
                && gtq!(n_, 0)
                && ltq!(p_, -1)
                && igtq!(m_, 1)
        },
        rhs: {
            let scaled = &f__ * x_;
            let quadratic = &d__ + &e__ * x_.pow(2);
            let unit = Atom::num(1) + c__.pow(2) * x_.pow(2);
            let argument = &a__ + &b__ * (&c__ * x_).asinh();
            let recursive_1 = scaled.pow(&m_ - Atom::num(2))
                * quadratic.pow(&p_ + Atom::num(1))
                * argument.pow(&n_);
            let recursive_2 = scaled.pow(&m_ - Atom::num(1))
                * unit.pow(&p_ + Atom::num(1) / Atom::num(2))
                * argument.pow(&n_ - Atom::num(1));
            let coefficient_1 = f__.pow(2) * (&m_ - Atom::num(1))
                / (Atom::num(2) * &e__ * (&p_ + Atom::num(1)));
            let coefficient_2 = &b__ * &f__ * &n_
                / (Atom::num(2) * &c__ * (&p_ + Atom::num(1)))
                * rubi_simp(&(quadratic.pow(&p_) / unit.pow(&p_)), x_);
            rubi_simp(&(&f__ * scaled.pow(&m_ - Atom::num(1))
                    * quadratic.pow(&p_ + Atom::num(1))
                    * argument.pow(&n_)
                    / (Atom::num(2) * &e__ * (&p_ + Atom::num(1)))), x_)
                    - rubi_star(coefficient_1, rubi_rhs_int(&recursive_1, x_))
                    - rubi_star(coefficient_2, rubi_rhs_int(&recursive_2, x_))
        },
    ));
}

fn push_rules_rule_6226(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6226,
        source: "Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
          -(f*x)^(m+1)*(d+e*x^2)^(p+1)*(a+b*ArcSinh[c*x])^n/(2*d*f*(p+1)) +
          (m+2*p+3)/(2*d*(p+1)) \\[Star] Int[(f*x)^m*(d+e*x^2)^(p+1)*(a+b*ArcSinh[c*x])^n,x] +
          b*c*n/(2*f*(p+1))*Simp[(d+e*x^2)^p/(1+c^2*x^2)^p] \\[Star] Int[(f*x)^(m+1)*(1+c^2*x^2)^(p+1/2)*(a+b*ArcSinh[c*x])^(n-1),x] /;
        FreeQ[{a,b,c,d,e,f,m},x] && EqQ[e,c^2*d] && GtQ[n,0] && LtQ[p,-1] && Not[GtQ[m,1]] && (IntegerQ[m] || IntegerQ[p] || EqQ[n,1])",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [f__, m_, d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [f__, e__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_], x_)
                && eqq!(e__, c__.pow(2) * &d__)
                && gtq!(n_, 0)
                && ltq!(p_, -1)
                && !gtq!(m_, 1)
                && (integerq!(m_) || integerq!(p_) || eqq!(n_, 1))
        },
        rhs: {
            let scaled = &f__ * x_;
            let quadratic = &d__ + &e__ * x_.pow(2);
            let unit = Atom::num(1) + c__.pow(2) * x_.pow(2);
            let argument = &a__ + &b__ * (&c__ * x_).asinh();
            let recursive_1 = scaled.pow(&m_)
                * quadratic.pow(&p_ + Atom::num(1))
                * argument.pow(&n_);
            let recursive_2 = scaled.pow(&m_ + Atom::num(1))
                * unit.pow(&p_ + Atom::num(1) / Atom::num(2))
                * argument.pow(&n_ - Atom::num(1));
            let coefficient_1 = (&m_ + Atom::num(2) * &p_ + 3)
                / (Atom::num(2) * &d__ * (&p_ + Atom::num(1)));
            let coefficient_2 = &b__ * &c__ * &n_
                / (Atom::num(2) * &f__ * (&p_ + Atom::num(1)))
                * rubi_simp(&(quadratic.pow(&p_) / unit.pow(&p_)), x_);
            rubi_simp(&(-scaled.pow(&m_ + Atom::num(1))
                    * quadratic.pow(&p_ + Atom::num(1))
                    * argument.pow(&n_)
                    / (Atom::num(2) * &d__ * &f__ * (&p_ + Atom::num(1)))), x_)
                    + rubi_star(coefficient_1, rubi_rhs_int(&recursive_1, x_))
                    + rubi_star(coefficient_2, rubi_rhs_int(&recursive_2, x_))
        },
    ));
}

fn push_rules_rule_6227(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6227,
        source: "Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
          f*(f*x)^(m-1)*(d+e*x^2)^(p+1)*(a+b*ArcSinh[c*x])^n/(e*(m+2*p+1)) -
          f^2*(m-1)/(c^2*(m+2*p+1)) \\[Star] Int[(f*x)^(m-2)*(d+e*x^2)^p*(a+b*ArcSinh[c*x])^n,x] -
          b*f*n/(c*(m+2*p+1))*Simp[(d+e*x^2)^p/(1+c^2*x^2)^p] \\[Star] Int[(f*x)^(m-1)*(1+c^2*x^2)^(p+1/2)*(a+b*ArcSinh[c*x])^(n-1),x] /;
        FreeQ[{a,b,c,d,e,f,p},x] && EqQ[e,c^2*d] && GtQ[n,0] && IGtQ[m,1] && NeQ[m+2*p+1,0]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [f__, m_, d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [f__, e__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, p_], x_)
                && eqq!(e__, c__.pow(2) * &d__)
                && gtq!(n_, 0)
                && igtq!(m_, 1)
                && neq!(&m_ + Atom::num(2) * &p_ + 1, 0)
        },
        rhs: {
            let scaled = &f__ * x_;
            let quadratic = &d__ + &e__ * x_.pow(2);
            let unit = Atom::num(1) + c__.pow(2) * x_.pow(2);
            let argument = &a__ + &b__ * (&c__ * x_).asinh();
            let denominator = &m_ + Atom::num(2) * &p_ + 1;
            let recursive_1 = scaled.pow(&m_ - Atom::num(2))
                * quadratic.pow(&p_)
                * argument.pow(&n_);
            let recursive_2 = scaled.pow(&m_ - Atom::num(1))
                * unit.pow(&p_ + Atom::num(1) / Atom::num(2))
                * argument.pow(&n_ - Atom::num(1));
            let coefficient_1 = f__.pow(2) * (&m_ - Atom::num(1))
                / (c__.pow(2) * &denominator);
            let coefficient_2 = &b__ * &f__ * &n_ / (&c__ * &denominator)
                * rubi_simp(&(quadratic.pow(&p_) / unit.pow(&p_)), x_);
            rubi_simp(&(&f__ * scaled.pow(&m_ - Atom::num(1))
                    * quadratic.pow(&p_ + Atom::num(1))
                    * argument.pow(&n_)
                    / (&e__ * &denominator)), x_)
                    - rubi_star(coefficient_1, rubi_rhs_int(&recursive_1, x_))
                    - rubi_star(coefficient_2, rubi_rhs_int(&recursive_2, x_))
        },
    ));
}

fn push_rules_rule_6228(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6228,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSinh[c_.*x_])^n_,x_Symbol] :=
          (f*x)^m*Sqrt[1+c^2*x^2]*(d+e*x^2)^p*(a+b*ArcSinh[c*x])^(n+1)/(b*c*(n+1)) -
          f*m/(b*c*(n+1))*Simp[(d+e*x^2)^p/(1+c^2*x^2)^p] \\[Star] Int[(f*x)^(m-1)*(1+c^2*x^2)^(p-1/2)*(a+b*ArcSinh[c*x])^(n+1),x] /;
        FreeQ[{a,b,c,d,e,f,m,p},x] && EqQ[e,c^2*d] && LtQ[n,-1] && EqQ[m+2*p+1,0]",
        desc: "Integration by parts and piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [f__, m_, d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [f__, m_, e__, p_, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, p_], x_)
                && eqq!(e__, c__.pow(2) * &d__)
                && ltq!(n_, -1)
                && eqq!(&m_ + Atom::num(2) * &p_ + 1, 0)
        },
        rhs: {
            let scaled = &f__ * x_;
            let quadratic = &d__ + &e__ * x_.pow(2);
            let unit = Atom::num(1) + c__.pow(2) * x_.pow(2);
            let argument = &a__ + &b__ * (&c__ * x_).asinh();
            let recursive = scaled.pow(&m_ - Atom::num(1))
                * unit.pow(&p_ - Atom::num(1) / Atom::num(2))
                * argument.pow(&n_ + Atom::num(1));
            let coefficient = &f__ * &m_ / (&b__ * &c__ * (&n_ + Atom::num(1)))
                * rubi_simp(&(quadratic.pow(&p_) / unit.pow(&p_)), x_);
            rubi_simp(&(scaled.pow(&m_)
                    * unit.sqrt()
                    * quadratic.pow(&p_)
                    * argument.pow(&n_ + Atom::num(1))
                    / (&b__ * &c__ * (&n_ + Atom::num(1)))), x_)
                    - rubi_star(coefficient, rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_6229(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6229,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSinh[c_.*x_])^n_,x_Symbol] :=
          (f*x)^m*Sqrt[1+c^2*x^2]*(d+e*x^2)^p*(a+b*ArcSinh[c*x])^(n+1)/(b*c*(n+1)) -
          f*m/(b*c*(n+1))*Simp[(d+e*x^2)^p/(1+c^2*x^2)^p] \\[Star] Int[(f*x)^(m-1)*(1+c^2*x^2)^(p-1/2)*(a+b*ArcSinh[c*x])^(n+1),x] -
          c*(m+2*p+1)/(b*f*(n+1))*Simp[(d+e*x^2)^p/(1+c^2*x^2)^p] \\[Star] Int[(f*x)^(m+1)*(1+c^2*x^2)^(p-1/2)*(a+b*ArcSinh[c*x])^(n+1),x] /;
        FreeQ[{a,b,c,d,e,f},x] && EqQ[e,c^2*d] && LtQ[n,-1] && IGtQ[2*p,0] && NeQ[m+2*p+1,0] && IGtQ[m,-3]",
        desc: "Integration by parts and piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [f__, m_, d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [f__, m_, e__, p_, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && eqq!(e__, c__.pow(2) * &d__)
                && ltq!(n_, -1)
                && igtq!(Atom::num(2) * &p_, 0)
                && neq!(&m_ + Atom::num(2) * &p_ + 1, 0)
                && igtq!(m_, -3)
        },
        rhs: {
            let scaled = &f__ * x_;
            let quadratic = &d__ + &e__ * x_.pow(2);
            let unit = Atom::num(1) + c__.pow(2) * x_.pow(2);
            let argument = &a__ + &b__ * (&c__ * x_).asinh();
            let recursive_1 = scaled.pow(&m_ - Atom::num(1))
                * unit.pow(&p_ - Atom::num(1) / Atom::num(2))
                * argument.pow(&n_ + Atom::num(1));
            let recursive_2 = scaled.pow(&m_ + Atom::num(1))
                * unit.pow(&p_ - Atom::num(1) / Atom::num(2))
                * argument.pow(&n_ + Atom::num(1));
            let coefficient_1 = &f__ * &m_ / (&b__ * &c__ * (&n_ + Atom::num(1)))
                * rubi_simp(
                    &(quadratic.pow(&p_) / unit.pow(&p_)),
                    x_,
                );
            let coefficient_2 = &c__ * (&m_ + Atom::num(2) * &p_ + 1)
                / (&b__ * &f__ * (&n_ + Atom::num(1)))
                * rubi_simp(
                    &(quadratic.pow(&p_) / unit.pow(&p_)),
                    x_,
                );
            rubi_simp(&(scaled.pow(&m_)
                    * unit.sqrt()
                    * quadratic.pow(&p_)
                    * argument.pow(&n_ + Atom::num(1))
                    / (&b__ * &c__ * (&n_ + Atom::num(1)))), x_)
                    - rubi_star(coefficient_1, rubi_rhs_int(&recursive_1, x_))
                    - rubi_star(coefficient_2, rubi_rhs_int(&recursive_2, x_))
        },
    ));
}

fn push_rules_rule_6230(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 6230,
        source: "Int[(f_.*x_)^m_*(a_.+b_.*ArcSinh[c_.*x_])^n_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
          f*(f*x)^(m-1)*Sqrt[d+e*x^2]*(a+b*ArcSinh[c*x])^n/(e*m) -
          b*f*n/(c*m)*Simp[Sqrt[1+c^2*x^2]/Sqrt[d+e*x^2]] \\[Star] Int[(f*x)^(m-1)*(a+b*ArcSinh[c*x])^(n-1),x] -
          f^2*(m-1)/(c^2*m) \\[Star] Int[((f*x)^(m-2)*(a+b*ArcSinh[c*x])^n)/Sqrt[d+e*x^2],x] /;
        FreeQ[{a,b,c,d,e,f},x] && EqQ[e,c^2*d] && GtQ[n,0] && IGtQ[m,1]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [f__, m_, a__, b__, c__, n_, d__, e__, x_],
        optional: [f__, a__, b__, c__, n_, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && eqq!(e__, c__.pow(2) * &d__)
                && gtq!(n_, 0)
                && igtq!(m_, 1)
        },
        rhs: {
            let scaled = &f__ * x_;
            let quadratic_x = &d__ + &e__ * x_.pow(2);
            let argument = &a__ + &b__ * (&c__ * x_).asinh();
            let recursive_1 = scaled.pow(&m_ - Atom::num(1)) * argument.pow(&n_ - Atom::num(1));
            let recursive_2 = scaled.pow(&m_ - Atom::num(2)) * argument.pow(&n_) / &quadratic_x.sqrt();
            let coefficient_1 = &b__ * &f__ * &n_ / (&c__ * &m_)
                * rubi_simp(
                    &((Atom::num(1) + c__.pow(2) * x_.pow(2)).sqrt()
                        / quadratic_x.sqrt()),
                    x_,
                );
            let coefficient_2 = f__.pow(2) * (&m_ - Atom::num(1)) / (c__.pow(2) * &m_);
            rubi_simp(&(&f__ * scaled.pow(&m_ - Atom::num(1)) * quadratic_x.sqrt() * argument.pow(&n_)
                    / (&e__ * &m_)), x_)
                    - rubi_star(coefficient_1, rubi_rhs_int(&recursive_1, x_))
                    - rubi_star(coefficient_2, rubi_rhs_int(&recursive_2, x_))
        },
    ));
}

fn push_rules_rule_6231(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 6231,
        source: "Int[x_^m_*(a_.+b_.*ArcSinh[c_.*x_])^n_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
          1/c^(m+1)*Simp[Sqrt[1+c^2*x^2]/Sqrt[d+e*x^2]] \\[Star] Subst[Int[(a+b*x)^n*Sinh[x]^m,x],x,ArcSinh[c*x]] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[e,c^2*d] && IGtQ[n,0] && IntegerQ[m]",
        desc: "Piecewise constant extraction and integration by substitution",
        refs: [],
        pattern: x_.pow(m_) * (a__ + b__ * (c__ * x_).asinh()).pow(n_) / (d__ + e__ * x_.pow(2)).sqrt(),
        with: [m_, a__, b__, c__, n_, d__, e__, x_],
        optional: [a__, b__, c__, e__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(e__, c__.pow(2) * &d__)
                && igtq!(n_, 0)
                && integerq!(m_)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let substitution_integrand = (&a__ + &b__ * &sub_atom).pow(&n_) * sub_atom.sinh().pow(&m_);
            let substitution_primitive =
                rubi_rhs_int(&substitution_integrand, substitution_symbol);
            let coefficient = Atom::num(1) / c__.pow(&m_ + Atom::num(1))
                * rubi_simp(
                    &((Atom::num(1) + c__.pow(2) * x_.pow(2)).sqrt()
                        / (&d__ + &e__ * x_.pow(2)).sqrt()),
                    x_,
                );
            let substituted = rubi_subst(
                &substitution_primitive,
                substitution_symbol,
                (&c__ * x_).asinh(),
            );
            rubi_star(coefficient, substituted)
        },
    ));
}

fn push_rules_rule_6232(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, x_);
    rules.push(rubi_rule!(
        order: 6232,
        source: "Int[(f_.*x_)^m_*(a_.+b_.*ArcSinh[c_.*x_])/Sqrt[d_+e_.*x_^2],x_Symbol] :=
          (f*x)^(m+1)/(f*(m+1))*Simp[Sqrt[1+c^2*x^2]/Sqrt[d+e*x^2]]*(a+b*ArcSinh[c*x])*
            Hypergeometric2F1[1/2,(1+m)/2,(3+m)/2,-c^2*x^2] -
          b*c*(f*x)^(m+2)/(f^2*(m+1)*(m+2))*Simp[Sqrt[1+c^2*x^2]/Sqrt[d+e*x^2]]*
            HypergeometricPFQ[{1,1+m/2,1+m/2},{3/2+m/2,2+m/2},-c^2*x^2] /;
        FreeQ[{a,b,c,d,e,f,m},x] && EqQ[e,c^2*d] && Not[IntegerQ[m]]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern: (f__ * x_).pow(m_) * (a__ + b__ * (c__ * x_).asinh()) / (d__ + e__ * x_.pow(2)).sqrt(),
        with: [f__, m_, a__, b__, c__, d__, e__, x_],
        optional: [f__, a__, b__, c__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_], x_)
                && eqq!(e__, c__.pow(2) * &d__)
                && !integerq!(m_)
        },
        rhs: {
            let scaled = &f__ * x_;
            let quadratic_x = &d__ + &e__ * x_.pow(2);
            let argument = &a__ + &b__ * (&c__ * x_).asinh();
            let ratio_1 = rubi_simp(
                &((Atom::num(1) + c__.pow(2) * x_.pow(2)).sqrt() / quadratic_x.sqrt()),
                x_,
            );
            let ratio_2 = rubi_simp(
                &((Atom::num(1) + c__.pow(2) * x_.pow(2)).sqrt() / quadratic_x.sqrt()),
                x_,
            );
            let z = -c__.pow(2) * x_.pow(2);
            rubi_simp(&(scaled.pow(&m_ + Atom::num(1))
                    / (&f__ * (&m_ + Atom::num(1)))
                    * ratio_1
                    * argument
                    * rubi_hypergeometric2f1(
                        Atom::num(1) / Atom::num(2),
                        (&m_ + Atom::num(1)) / Atom::num(2),
                        (&m_ + Atom::num(3)) / Atom::num(2),
                        &z,
                    )), x_)
                    - rubi_simp(&(&b__ * &c__ * scaled.pow(&m_ + Atom::num(2))
                        / (f__.pow(2) * (&m_ + Atom::num(1)) * (&m_ + Atom::num(2)))
                        * ratio_2
                        * rubi_hypergeometric_pfq_3_2(
                            Atom::num(1),
                            Atom::num(1) + &m_ / Atom::num(2),
                            Atom::num(1) + &m_ / Atom::num(2),
                            Atom::num(3) / Atom::num(2) + &m_ / Atom::num(2),
                            Atom::num(2) + &m_ / Atom::num(2),
                            z,
                        )), x_)
        },
    ));
}

fn push_rules_rule_6233(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 6233,
        source: "Int[(f_.*x_)^m_.*(a_.+b_.*ArcSinh[c_.*x_])^n_/Sqrt[d_+e_.*x_^2],x_Symbol] :=
          (f*x)^m/(b*c*(n+1))*Simp[Sqrt[1+c^2*x^2]/Sqrt[d+e*x^2]]*(a+b*ArcSinh[c*x])^(n+1) -
          f*m/(b*c*(n+1))*Simp[Sqrt[1+c^2*x^2]/Sqrt[d+e*x^2]] \\[Star] Int[(f*x)^(m-1)*(a+b*ArcSinh[c*x])^(n+1),x] /;
        FreeQ[{a,b,c,d,e,f,m},x] && EqQ[e,c^2*d] && LtQ[n,-1]",
        desc: "Integration by parts and piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [f__, m_, a__, b__, c__, n_, d__, e__, x_],
        optional: [f__, m_, a__, b__, c__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_], x_)
                && eqq!(e__, c__.pow(2) * &d__)
                && ltq!(n_, -1)
        },
        rhs: {
            let scaled = &f__ * x_;
            let argument = &a__ + &b__ * (&c__ * x_).asinh();
            let ratio_1 = rubi_simp(
                &((Atom::num(1) + c__.pow(2) * x_.pow(2)).sqrt()
                    / (&d__ + &e__ * x_.pow(2)).sqrt()),
                x_,
            );
            let ratio_2 = rubi_simp(
                &((Atom::num(1) + c__.pow(2) * x_.pow(2)).sqrt()
                    / (&d__ + &e__ * x_.pow(2)).sqrt()),
                x_,
            );
            let recursive =
                scaled.pow(&m_ - Atom::num(1)) * argument.pow(&n_ + Atom::num(1));
            let coefficient = &f__ * &m_ / (&b__ * &c__ * (&n_ + Atom::num(1))) * ratio_2;
            rubi_simp(&(scaled.pow(&m_) / (&b__ * &c__ * (&n_ + Atom::num(1)))
                    * ratio_1
                    * argument.pow(&n_ + Atom::num(1))), x_)
                    - rubi_star(coefficient, rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_6234(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6234,
        source: "Int[x_^m_.*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
          1/(b*c^(m+1))*Simp[(d+e*x^2)^p/(1+c^2*x^2)^p] \\[Star]
            Subst[Int[x^n*Sinh[-a/b+x/b]^m*Cosh[-a/b+x/b]^(2*p+1),x],x,a+b*ArcSinh[c*x]] /;
        FreeQ[{a,b,c,d,e,n},x] && EqQ[e,c^2*d] && IGtQ[2*p+2,0] && IGtQ[m,0]",
        desc: "Piecewise constant extraction and integration by substitution",
        refs: [],
        pattern: x_.pow(m_) * (d__ + e__ * x_.pow(2)).pow(p_) * (a__ + b__ * (c__ * x_).asinh()).pow(n_),
        with: [m_, d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [m_, e__, p_, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, n_], x_)
                && eqq!(e__, c__.pow(2) * &d__)
                && igtq!(Atom::num(2) * &p_ + 2, 0)
                && igtq!(m_, 0)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let hyper_arg = -&a__ / &b__ + &sub_atom / &b__;
            let substitution_integrand =
                sub_atom.pow(&n_) * &hyper_arg.sinh().pow(&m_) * hyper_arg.cosh().pow(Atom::num(2) * &p_ + 1);
            let substitution_primitive =
                rubi_rhs_int(&substitution_integrand, substitution_symbol);
            let coefficient = Atom::num(1) / (&b__ * c__.pow(&m_ + Atom::num(1)))
                * rubi_simp(
                    &((&d__ + &e__ * x_.pow(2)).pow(&p_)
                        / (Atom::num(1) + c__.pow(2) * x_.pow(2)).pow(&p_)),
                    x_,
                );
            let substituted = rubi_subst(
                &substitution_primitive,
                substitution_symbol,
                &a__ + &b__ * (&c__ * x_).asinh(),
            );
            rubi_star(coefficient, substituted)
        },
    ));
}

fn push_rules_rule_6235(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6235,
        source: "Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
          Int[ExpandIntegrand[(a+b*ArcSinh[c*x])^n/Sqrt[d+e*x^2],(f*x)^m*(d+e*x^2)^(p+1/2),x],x] /;
        FreeQ[{a,b,c,d,e,f,m,n},x] && EqQ[e,c^2*d] && IGtQ[p+1/2,0] && Not[IGtQ[(m+1)/2,0]] && (EqQ[m,-1] || EqQ[m,-2])",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [f__, m_, d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [f__, e__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_], x_)
                && eqq!(e__, c__.pow(2) * &d__)
                && igtq!(&p_ + Atom::num(1) / Atom::num(2), 0)
                && !igtq!((&m_ + Atom::num(1)) / Atom::num(2), 0)
                && (eqq!(m_, -1) || eqq!(m_, -2))
        },
        rhs: {
            let quadratic_x = &d__ + &e__ * x_.pow(2);
            let argument = &a__ + &b__ * (&c__ * x_).asinh();
            let u = argument.pow(&n_) / quadratic_x.sqrt();
            let v = (&f__ * x_).pow(&m_)
                * quadratic_x.pow(&p_ + Atom::num(1) / Atom::num(2));
            let expanded = rubi_expand_integrand_product(&u, &v, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_6236(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, p_, x_);
    rules.push(rubi_rule!(
        order: 6236,
        source: "Int[x_*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSinh[c_.*x_]),x_Symbol] :=
          (d+e*x^2)^(p+1)*(a+b*ArcSinh[c*x])/(2*e*(p+1)) - b*c/(2*e*(p+1)) \\[Star] Int[(d+e*x^2)^(p+1)/Sqrt[1+c^2*x^2],x] /;
        FreeQ[{a,b,c,d,e,p},x] && NeQ[e,c^2*d] && NeQ[p,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern: x_ * (d__ + e__ * x_.pow(2)).pow(p_) * (a__ + b__ * (c__ * x_).asinh()),
        with: [d__, e__, p_, a__, b__, c__, x_],
        optional: [e__, a__, b__, c__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, p_], x_)
                && neq!(e__, c__.pow(2) * &d__)
                && neq!(p_, -1)
        },
        rhs: {
            let quadratic_x = &d__ + &e__ * x_.pow(2);
            let argument = &a__ + &b__ * (&c__ * x_).asinh();
            let recursive =
                quadratic_x.pow(&p_ + Atom::num(1)) / (Atom::num(1) + c__.pow(2) * x_.pow(2)).sqrt();
            rubi_simp(&(quadratic_x.pow(&p_ + Atom::num(1)) * argument
                    / (Atom::num(2) * &e__ * (&p_ + Atom::num(1)))), x_)
                    - rubi_star(&b__ * &c__ / (Atom::num(2) * &e__ * (&p_ + Atom::num(1))), rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_6237(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 6237,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSinh[c_.*x_]),x_Symbol] :=
          With[{u=IntHide[(f*x)^m*(d+e*x^2)^p,x]},
          (a+b*ArcSinh[c*x]) \\[Star] u - b*c \\[Star] Int[SimplifyIntegrand[u/Sqrt[1+c^2*x^2],x],x]] /;
        FreeQ[{a,b,c,d,e,f,m},x] && NeQ[e,c^2*d] && IntegerQ[p] && (GtQ[p,0] || IGtQ[(m-1)/2,0] && LeQ[m+p,0])",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [f__, m_, d__, e__, p_, a__, b__, c__, x_],
        optional: [f__, m_, e__, p_, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_], x_)
                && neq!(e__, c__.pow(2) * &d__)
                && integerq!(p_)
                && (gtq!(p_, 0)
                    || (igtq!((&m_ - Atom::num(1)) / Atom::num(2), 0) && leq!(&m_ + &p_, 0)))
        },
        rhs: {
            let argument = &a__ + &b__ * (&c__ * x_).asinh();
            let u = rubi_int_hide(
                &((&f__ * x_).pow(&m_) * (&d__ + &e__ * x_.pow(2)).pow(&p_)),
                x_,
            ).rubi_rhs();
            let recursive = rubi_simplify_integrand(
                &(&u / (Atom::num(1) + c__.pow(2) * x_.pow(2)).sqrt()),
                x_,
            );
            rubi_star(argument, u)
                    - rubi_star(&b__ * &c__, rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_6238(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6238,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
          Int[ExpandIntegrand[(a+b*ArcSinh[c*x])^n,(f*x)^m*(d+e*x^2)^p,x],x] /;
        FreeQ[{a,b,c,d,e,f},x] && NeQ[e,c^2*d] && IGtQ[n,0] && IntegerQ[p] && IntegerQ[m]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [f__, m_, d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [f__, m_, e__, p_, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && neq!(e__, c__.pow(2) * &d__)
                && igtq!(n_, 0)
                && integerq!(p_)
                && integerq!(m_)
        },
        rhs: {
            let argument = &a__ + &b__ * (&c__ * x_).asinh();
            let u = argument.pow(&n_);
            let v = (&f__ * x_).pow(&m_) * (&d__ + &e__ * x_.pow(2)).pow(&p_);
            let expanded = rubi_expand_integrand_product(&u, &v, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_6239(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6239,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
          Unintegrable[(f*x)^m*(d+e*x^2)^p*(a+b*ArcSinh[c*x])^n,x] /;
        FreeQ[{a,b,c,d,e,f,m,n,p},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [f__, m_, d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [f__, m_, e__, p_, a__, b__, c__, n_],
        when: { freeq!([a__, b__, c__, d__, e__, f__, m_, n_, p_], x_) },
        rhs: {
            let integrand = (&f__ * x_).pow(&m_)
                * (&d__ + &e__ * x_.pow(2)).pow(&p_)
                * (&a__ + &b__ * (&c__ * x_).asinh()).pow(&n_);
            rubi_unintegrable(integrand, x_)
        },
    ));
}

fn push_rules_rule_6240(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, h__, m_, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 6240,
        source: "Int[(h_.*x_)^m_.*(d_+e_.*x_)^p_*(f_+g_.*x_)^q_*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
          (-d^2*g/e)^q \\[Star] Int[(h*x)^m*(d+e*x)^(p-q)*(1+c^2*x^2)^q*(a+b*ArcSinh[c*x])^n,x] /;
        FreeQ[{a,b,c,d,e,f,g,h,m,n},x] && EqQ[e*f+d*g,0] && EqQ[c^2*d^2+e^2,0] && HalfIntegerQ[p,q] && GeQ[p-q,0] && GtQ[d,0] && LtQ[g/e,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [h__, m_, d__, e__, p_, f__, g__, q_, a__, b__, c__, n_, x_],
        optional: [h__, m_, e__, g__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__, m_, n_], x_)
                && eqq!(&e__ * &f__ + &d__ * &g__, 0)
                && eqq!(c__.pow(2) * d__.pow(2) + e__.pow(2), 0)
                && half_integer_numerator(&p_).is_some()
                && half_integer_numerator(&q_).is_some()
                && geq!(&p_ - &q_, 0)
                && gtq!(d__, 0)
                && ltq!(&g__ / &e__, 0)
        },
        rhs: {
            let transformed = (&h__ * x_).pow(&m_)
                * (&d__ + &e__ * x_).pow(&p_ - &q_)
                * (Atom::num(1) + c__.pow(2) * x_.pow(2)).pow(&q_)
                * (&a__ + &b__ * (&c__ * x_).asinh()).pow(&n_);
            let primitive = rubi_rhs_int(&transformed, x_);

            rubi_star((-d__.pow(2) * &g__ / &e__).pow(&q_), primitive)
        },
    ));
}

fn push_rules_rule_6241(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, h__, m_, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 6241,
        source: "Int[(h_.*x_)^m_.*(d_+e_.*x_)^p_*(f_+g_.*x_)^q_*(a_.+b_.*ArcSinh[c_.*x_])^n_.,x_Symbol] :=
          (-d^2*g/e)^IntPart[q]*(d+e*x)^FracPart[q]*(f+g*x)^FracPart[q]/(1+c^2*x^2)^FracPart[q] \\[Star]
            Int[(h*x)^m*(d+e*x)^(p-q)*(1+c^2*x^2)^q*(a+b*ArcSinh[c*x])^n,x] /;
        FreeQ[{a,b,c,d,e,f,g,h,m,n},x] && EqQ[e*f+d*g,0] && EqQ[c^2*d^2+e^2,0] && HalfIntegerQ[p,q] && GeQ[p-q,0]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [h__, m_, d__, e__, p_, f__, g__, q_, a__, b__, c__, n_, x_],
        optional: [h__, m_, e__, g__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__, m_, n_], x_)
                && eqq!(&e__ * &f__ + &d__ * &g__, 0)
                && eqq!(c__.pow(2) * d__.pow(2) + e__.pow(2), 0)
                && half_integer_numerator(&p_).is_some()
                && half_integer_numerator(&q_).is_some()
                && geq!(&p_ - &q_, 0)
        },
        rhs: {
            let int_q = rubi_int_part(&q_);
            let frac_q = rubi_frac_part(&q_);
            let transformed = (&h__ * x_).pow(&m_)
                * (&d__ + &e__ * x_).pow(&p_ - &q_)
                * (Atom::num(1) + c__.pow(2) * x_.pow(2)).pow(&q_)
                * (&a__ + &b__ * (&c__ * x_).asinh()).pow(&n_);
            let multiplier = (-d__.pow(2) * &g__ / &e__).pow(int_q)
                * (&d__ + &e__ * x_).pow(&frac_q)
                * (&f__ + &g__ * x_).pow(&frac_q)
                / (Atom::num(1) + c__.pow(2) * x_.pow(2)).pow(&frac_q);
            let primitive = rubi_rhs_int(&transformed, x_);

            rubi_star(multiplier, primitive)
        },
    ));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn downvalues_6212_through_6241_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .filter(|order| (6212..=6241).contains(order))
            .collect::<Vec<_>>();
        assert_eq!(orders, (6212..=6241).collect::<Vec<_>>());
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
    (f__ * x_).pow(m_) * (a__ + b__ * (c__ * x_).asinh()).pow(n_) / (d__ + e__ * x_.pow(2)).sqrt()
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
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (f__ * x_).pow(m_) * (d__ + e__ * x_.pow(2)).pow(p_) * (a__ + b__ * (c__ * x_).asinh())
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
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (f__ * x_).pow(m_) * (d__ + e__ * x_.pow(2)).pow(p_) * (a__ + b__ * (c__ * x_).asinh()).pow(n_)
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
    let x_ = symbols.x_;
    (f__ * x_).pow(m_) * (d__ + e__ * x_.pow(2)).sqrt() * (a__ + b__ * (c__ * x_).asinh()).pow(n_)
}

#[inline(never)]
fn rubi_shared_pattern_4(symbols: &RubiSymbols) -> Atom {
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
        * (a__ + b__ * (c__ * x_).asinh()).pow(n_)
}
