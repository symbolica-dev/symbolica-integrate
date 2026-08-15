use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_6327(rules);
    push_rules_rule_6328(rules);
    push_rules_rule_6329(rules);
    push_rules_rule_6330(rules);
    push_rules_rule_6331(rules);
    push_rules_rule_6332(rules);
    push_rules_rule_6333(rules);
    push_rules_rule_6334(rules);
    push_rules_rule_6335(rules);
    push_rules_rule_6336(rules);
    push_rules_rule_6337(rules);
    push_rules_rule_6338(rules);
    push_rules_rule_6339(rules);
    push_rules_rule_6340(rules);
    push_rules_rule_6341(rules);
    push_rules_rule_6342(rules);
    push_rules_rule_6343(rules);
    push_rules_rule_6344(rules);
    // Blocks 13 and 14 are disabled in the Rubi source embedded in docs/rubi_pdf_rules.md.

    push_rules_rule_6345(rules);
    push_rules_rule_6346(rules);
    push_rules_rule_6347(rules);
    push_rules_rule_6348(rules);
    push_rules_rule_6349(rules);
    push_rules_rule_6350(rules);
    push_rules_rule_6351(rules);
    push_rules_rule_6352(rules);
    push_rules_rule_6353(rules);
    push_rules_rule_6354(rules);
    push_rules_rule_6355(rules);
    push_rules_rule_6356(rules);
    push_rules_rule_6357(rules);
    push_rules_rule_6358(rules);
    // Block 22 is disabled in the Rubi source embedded in docs/rubi_pdf_rules.md.

    push_rules_rule_6359(rules);
    push_rules_rule_6360(rules);
    push_rules_rule_6361(rules);
    push_rules_rule_6362(rules);
    push_rules_rule_6363(rules);
    push_rules_rule_6364(rules);
    push_rules_rule_6365(rules);
    push_rules_rule_6366(rules);
    push_rules_rule_6367(rules);
    push_rules_rule_6368(rules);
    push_rules_rule_6369(rules);
    push_rules_rule_6370(rules);
    push_rules_rule_6371(rules);
    push_rules_rule_6372(rules);
    push_rules_rule_6373(rules);
    // Block 32 is disabled in the Rubi source embedded in docs/rubi_pdf_rules.md.

    push_rules_rule_6374(rules);
    push_rules_rule_6375(rules);
    push_rules_rule_6376(rules);
}

fn push_rules_rule_6327(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, f__, d1__, e1__, d2__, e2__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6327,
        source: "Int[(f_.*x_)^m_.*(d1_+e1_.*x_)^p_.*(d2_+e2_.*x_)^p_.*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
          Int[(f*x)^m*(d1*d2+e1*e2*x^2)^p*(a+b*ArcCosh[c*x])^n,x] /;
        FreeQ[{a,b,c,d1,e1,d2,e2,f,m,n},x] && EqQ[d2*e1+d1*e2,0] && IntegerQ[p]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [f__, m_, d1__, e1__, p_, d2__, e2__, a__, b__, c__, n_, x_],
        optional: [f__, m_, e1__, e2__, a__, b__, c__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d1__, e1__, d2__, e2__, f__, m_, n_], x_)
                && eqq!(&d2__ * &e1__ + &d1__ * &e2__, 0)
                && integerq!(p_)
        },
        rhs: {
            let transformed = (&f__ * x_).pow(&m_)
                * (&d1__ * &d2__ + &e1__ * &e2__ * x_.pow(2)).pow(&p_)
                * (&a__ + &b__ * (&c__ * x_).acosh()).pow(&n_);
            rubi_rhs_int(&transformed, x_)
        },
    ));
}

fn push_rules_rule_6328(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 6328,
        source: "Int[x_*(a_.+b_.*ArcCosh[c_.*x_])^n_./(d_+e_.*x_^2),x_Symbol] :=
          1/e \\[Star] Subst[Int[(a+b*x)^n*Coth[x],x],x,ArcCosh[c*x]] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && IGtQ[n,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: x_ * (a__ + b__ * (c__ * x_).acosh()).pow(n_) / (d__ + e__ * x_.pow(2)),
        with: [a__, b__, c__, n_, d__, e__, x_],
        optional: [a__, b__, c__, e__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && igtq!(n_, 0)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let payload = (&a__ + &b__ * &sub_atom).pow(&n_) * sub_atom.coth();
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            let substituted = rubi_subst(&primitive, substitution_symbol, (&c__ * x_).acosh());
            rubi_star(Atom::num(1) / &e__, substituted)
        },
    ));
}

fn push_rules_rule_6329(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6329,
        source: "Int[x_*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
          (d+e*x^2)^(p+1)*(a+b*ArcCosh[c*x])^n/(2*e*(p+1)) -
          b*n/(2*c*(p+1))*Simp[(d+e*x^2)^p/((1+c*x)^p*(-1+c*x)^p)] \\[Star]
            Int[(1+c*x)^(p+1/2)*(-1+c*x)^(p+1/2)*(a+b*ArcCosh[c*x])^(n-1),x] /;
        FreeQ[{a,b,c,d,e,p},x] && EqQ[c^2*d+e,0] && GtQ[n,0] && NeQ[p,-1]",
        desc: "Integration by parts and piecewise constant extraction",
        refs: [],
        pattern: x_ * (d__ + e__ * x_.pow(2)).pow(p_) * (a__ + b__ * (c__ * x_).acosh()).pow(n_),
        with: [d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [e__, a__, b__, c__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, p_], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && gtq!(n_, 0)
                && neq!(p_, -1)
        },
        rhs: {
            let quadratic_x = &d__ + &e__ * x_.pow(2);
            let unit1 = Atom::num(1) + &c__ * x_;
            let unit2 = -Atom::num(1) + &c__ * x_;
            let argument = &a__ + &b__ * (&c__ * x_).acosh();
            let recursive = unit1.pow(&p_ + Atom::num(1) / Atom::num(2))
                * unit2.pow(&p_ + Atom::num(1) / Atom::num(2))
                * argument.pow(&n_ - Atom::num(1));
            rubi_simp(&(quadratic_x.pow(&p_ + Atom::num(1)) * argument.pow(&n_)
                    / (Atom::num(2) * &e__ * (&p_ + Atom::num(1)))), x_)
                    - rubi_star(&b__ * &n_
                            / (Atom::num(2) * &c__ * (&p_ + Atom::num(1)))
                            * rubi_simp(
                                &(quadratic_x.pow(&p_)
                                    / (unit1.pow(&p_) * unit2.pow(&p_))),
                                x_,
                            ), rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_6330(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d1__, e1__, d2__, e2__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6330,
        source: "Int[x_*(d1_+e1_.*x_)^p_*(d2_+e2_.*x_)^p_*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
          (d1+e1*x)^(p+1)*(d2+e2*x)^(p+1)*(a+b*ArcCosh[c*x])^n/(2*e1*e2*(p+1)) -
          b*n/(2*c*(p+1))*Simp[(d1+e1*x)^p/(1+c*x)^p]*Simp[(d2+e2*x)^p/(-1+c*x)^p] \\[Star]
            Int[(1+c*x)^(p+1/2)*(-1+c*x)^(p+1/2)*(a+b*ArcCosh[c*x])^(n-1),x] /;
        FreeQ[{a,b,c,d1,e1,d2,e2,p},x] && EqQ[e1,c*d1] && EqQ[e2,-c*d2] && GtQ[n,0] && NeQ[p,-1]",
        desc: "Integration by parts and piecewise constant extraction",
        refs: [],
        pattern: x_ * (d1__ + e1__ * x_).pow(p_) * (d2__ + e2__ * x_).pow(p_) * (a__ + b__ * (c__ * x_).acosh()).pow(n_),
        with: [d1__, e1__, p_, d2__, e2__, a__, b__, c__, n_, x_],
        optional: [e1__, e2__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d1__, e1__, d2__, e2__, p_], x_)
                && eqq!(e1__, &c__ * &d1__)
                && eqq!(e2__, -&c__ * &d2__)
                && gtq!(n_, 0)
                && neq!(p_, -1)
        },
        rhs: {
            let l1 = &d1__ + &e1__ * x_;
            let l2 = &d2__ + &e2__ * x_;
            let unit1 = Atom::num(1) + &c__ * x_;
            let unit2 = -Atom::num(1) + &c__ * x_;
            let argument = &a__ + &b__ * (&c__ * x_).acosh();
            let recursive = unit1.pow(&p_ + Atom::num(1) / Atom::num(2))
                * unit2.pow(&p_ + Atom::num(1) / Atom::num(2))
                * argument.pow(&n_ - Atom::num(1));
            rubi_simp(&(l1.pow(&p_ + Atom::num(1))
                    * l2.pow(&p_ + Atom::num(1))
                    * argument.pow(&n_)
                    / (Atom::num(2) * &e1__ * &e2__ * (&p_ + Atom::num(1)))), x_)
                    - rubi_star(&b__ * &n_
                            / (Atom::num(2) * &c__ * (&p_ + Atom::num(1)))
                            * rubi_simp(&(l1.pow(&p_) / unit1.pow(&p_)), x_)
                            * rubi_simp(&(l2.pow(&p_) / unit2.pow(&p_)), x_), rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_6331(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 6331,
        source: "Int[(a_.+b_.*ArcCosh[c_.*x_])^n_./(x_*(d_+e_.*x_^2)),x_Symbol] :=
          -1/d \\[Star] Subst[Int[(a+b*x)^n/(Cosh[x]*Sinh[x]),x],x,ArcCosh[c*x]] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && IGtQ[n,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (a__ + b__ * (c__ * x_).acosh()).pow(n_) / (x_ * (d__ + e__ * x_.pow(2))),
        with: [a__, b__, c__, n_, d__, e__, x_],
        optional: [a__, b__, c__, e__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && igtq!(n_, 0)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let payload = (&a__ + &b__ * &sub_atom).pow(&n_) / (sub_atom.cosh() * sub_atom.sinh());
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            let substituted = rubi_subst(&primitive, substitution_symbol, (&c__ * x_).acosh());
            rubi_star(-Atom::num(1) / &d__, substituted)
        },
    ));
}

fn push_rules_rule_6332(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6332,
        source: "Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
          (f*x)^(m+1)*(d+e*x^2)^(p+1)*(a+b*ArcCosh[c*x])^n/(d*f*(m+1)) +
          b*c*n/(f*(m+1))*Simp[(d+e*x^2)^p/((1+c*x)^p*(-1+c*x)^p)] \\[Star]
            Int[(f*x)^(m+1)*(1+c*x)^(p+1/2)*(-1+c*x)^(p+1/2)*(a+b*ArcCosh[c*x])^(n-1),x] /;
        FreeQ[{a,b,c,d,e,f,m,p},x] && EqQ[c^2*d+e,0] && GtQ[n,0] && EqQ[m+2*p+3,0] && NeQ[m,-1]",
        desc: "Integration by parts and piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [f__, m_, d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [f__, e__, a__, b__, c__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, p_], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && gtq!(n_, 0)
                && eqq!(&m_ + Atom::num(2) * &p_ + 3, 0)
                && neq!(m_, -1)
        },
        rhs: {
            let scaled = &f__ * x_;
            let quadratic_x = &d__ + &e__ * x_.pow(2);
            let unit1 = Atom::num(1) + &c__ * x_;
            let unit2 = -Atom::num(1) + &c__ * x_;
            let argument = &a__ + &b__ * (&c__ * x_).acosh();
            let recursive = scaled.pow(&m_ + Atom::num(1))
                * unit1.pow(&p_ + Atom::num(1) / Atom::num(2))
                * unit2.pow(&p_ + Atom::num(1) / Atom::num(2))
                * argument.pow(&n_ - Atom::num(1));
            rubi_simp(&(scaled.pow(&m_ + Atom::num(1))
                    * quadratic_x.pow(&p_ + Atom::num(1))
                    * argument.pow(&n_)
                    / (&d__ * &f__ * (&m_ + Atom::num(1)))), x_)
                    + rubi_star(&b__ * &c__ * &n_ / (&f__ * (&m_ + Atom::num(1)))
                            * rubi_simp(
                                &(quadratic_x.pow(&p_)
                                    / (unit1.pow(&p_) * unit2.pow(&p_))),
                                x_,
                            ), rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_6333(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, f__, d1__, e1__, d2__, e2__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6333,
        source: "Int[(f_.*x_)^m_*(d1_+e1_.*x_)^p_*(d2_+e2_.*x_)^p_*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
          (f*x)^(m+1)*(d1+e1*x)^(p+1)*(d2+e2*x)^(p+1)*(a+b*ArcCosh[c*x])^n/(d1*d2*f*(m+1)) +
          b*c*n/(f*(m+1))*Simp[(d1+e1*x)^p/(1+c*x)^p]*Simp[(d2+e2*x)^p/(-1+c*x)^p] \\[Star]
            Int[(f*x)^(m+1)*(1+c*x)^(p+1/2)*(-1+c*x)^(p+1/2)*(a+b*ArcCosh[c*x])^(n-1),x] /;
        FreeQ[{a,b,c,d1,e1,d2,e2,f,m,p},x] && EqQ[e1,c*d1] && EqQ[e2,-c*d2] && GtQ[n,0] && EqQ[m+2*p+3,0] && NeQ[p,-1]",
        desc: "Integration by parts and piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [f__, m_, d1__, e1__, p_, d2__, e2__, a__, b__, c__, n_, x_],
        optional: [f__, e1__, e2__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d1__, e1__, d2__, e2__, f__, m_, p_], x_)
                && eqq!(e1__, &c__ * &d1__)
                && eqq!(e2__, -&c__ * &d2__)
                && gtq!(n_, 0)
                && eqq!(&m_ + Atom::num(2) * &p_ + 3, 0)
                && neq!(p_, -1)
        },
        rhs: {
            let scaled = &f__ * x_;
            let l1 = &d1__ + &e1__ * x_;
            let l2 = &d2__ + &e2__ * x_;
            let unit1 = Atom::num(1) + &c__ * x_;
            let unit2 = -Atom::num(1) + &c__ * x_;
            let argument = &a__ + &b__ * (&c__ * x_).acosh();
            let recursive = scaled.pow(&m_ + Atom::num(1))
                * unit1.pow(&p_ + Atom::num(1) / Atom::num(2))
                * unit2.pow(&p_ + Atom::num(1) / Atom::num(2))
                * argument.pow(&n_ - Atom::num(1));
            rubi_simp(&(scaled.pow(&m_ + Atom::num(1))
                    * l1.pow(&p_ + Atom::num(1))
                    * l2.pow(&p_ + Atom::num(1))
                    * argument.pow(&n_)
                    / (&d1__ * &d2__ * &f__ * (&m_ + Atom::num(1)))), x_)
                    + rubi_star(&b__ * &c__ * &n_ / (&f__ * (&m_ + Atom::num(1)))
                            * rubi_simp(&(l1.pow(&p_) / unit1.pow(&p_)), x_)
                            * rubi_simp(&(l2.pow(&p_) / unit2.pow(&p_)), x_), rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_6334(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, p_, x_);
    rules.push(rubi_rule!(
        order: 6334,
        source: "Int[(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCosh[c_.*x_])/x_,x_Symbol] :=
          (d+e*x^2)^p*(a+b*ArcCosh[c*x])/(2*p) -
          b*c*(-d)^p/(2*p) \\[Star] Int[(1+c*x)^(p-1/2)*(-1+c*x)^(p-1/2),x] +
          d \\[Star] Int[(d+e*x^2)^(p-1)*(a+b*ArcCosh[c*x])/x,x] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && IGtQ[p,0]",
        desc: "Inverted integration by parts",
        refs: [],
        pattern: (d__ + e__ * x_.pow(2)).pow(p_) * (a__ + b__ * (c__ * x_).acosh()) / x_,
        with: [d__, e__, p_, a__, b__, c__, x_],
        optional: [e__, a__, b__, c__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && igtq!(p_, 0)
        },
        rhs: {
            let quadratic_x = &d__ + &e__ * x_.pow(2);
            let argument = &a__ + &b__ * (&c__ * x_).acosh();
            let unit1 = Atom::num(1) + &c__ * x_;
            let unit2 = -Atom::num(1) + &c__ * x_;
            let recursive_1 =
                unit1.pow(&p_ - Atom::num(1) / Atom::num(2)) * unit2.pow(&p_ - Atom::num(1) / Atom::num(2));
            let recursive_2 = quadratic_x.pow(&p_ - Atom::num(1)) * &argument / x_;
            rubi_simp(&(quadratic_x.pow(&p_) * argument / (Atom::num(2) * &p_)), x_)
                    - rubi_star(&b__ * &c__ * (-&d__).pow(&p_) / (Atom::num(2) * &p_), rubi_rhs_int(&recursive_1, x_))
                    + rubi_star(d__, rubi_rhs_int(&recursive_2, x_))
        },
    ));
}

fn push_rules_rule_6335(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 6335,
        source: "Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCosh[c_.*x_]),x_Symbol] :=
          (f*x)^(m+1)*(d+e*x^2)^p*(a+b*ArcCosh[c*x])/(f*(m+1)) -
          b*c*(-d)^p/(f*(m+1)) \\[Star] Int[(f*x)^(m+1)*(1+c*x)^(p-1/2)*(-1+c*x)^(p-1/2),x] -
          2*e*p/(f^2*(m+1)) \\[Star] Int[(f*x)^(m+2)*(d+e*x^2)^(p-1)*(a+b*ArcCosh[c*x]),x] /;
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
            let quadratic_x = &d__ + &e__ * x_.pow(2);
            let unit1 = Atom::num(1) + &c__ * x_;
            let unit2 = -Atom::num(1) + &c__ * x_;
            let argument = &a__ + &b__ * (&c__ * x_).acosh();
            let recursive_1 = scaled.pow(&m_ + Atom::num(1))
                * unit1.pow(&p_ - Atom::num(1) / Atom::num(2))
                * unit2.pow(&p_ - Atom::num(1) / Atom::num(2));
            let recursive_2 = scaled.pow(&m_ + Atom::num(2))
                * quadratic_x.pow(&p_ - Atom::num(1))
                * &argument;
            rubi_simp(&(scaled.pow(&m_ + Atom::num(1)) * quadratic_x.pow(&p_) * argument
                    / (&f__ * (&m_ + Atom::num(1)))), x_)
                    - rubi_star(&b__ * &c__ * (-&d__).pow(&p_)
                            / (&f__ * (&m_ + Atom::num(1))), rubi_rhs_int(&recursive_1, x_))
                    - rubi_star(Atom::num(2) * &e__ * &p_
                            / (f__.pow(2) * (&m_ + Atom::num(1))), rubi_rhs_int(&recursive_2, x_))
        },
    ));
}

fn push_rules_rule_6336(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 6336,
        source: "Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCosh[c_.*x_]),x_Symbol] :=
          With[{u=IntHide[(f*x)^m*(d+e*x^2)^p,x]},
          (a+b*ArcCosh[c*x]) \\[Star] u - b*c \\[Star] Int[SimplifyIntegrand[u/(Sqrt[1+c*x]*Sqrt[-1+c*x]),x],x]] /;
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
            let argument = &a__ + &b__ * (&c__ * x_).acosh();
            let u = rubi_int_hide(
                &((&f__ * x_).pow(&m_) * (&d__ + &e__ * x_.pow(2)).pow(&p_)),
                x_,
            ).rubi_rhs();
            let denominator = (Atom::num(1) + &c__ * x_).sqrt()
                * (-Atom::num(1) + &c__ * x_).sqrt();
            let recursive = rubi_simplify_integrand(&(&u / denominator), x_);
            rubi_star(argument, u)
                    - rubi_star(&b__ * &c__, rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_6337(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 6337,
        source: "Int[x_^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCosh[c_.*x_]),x_Symbol] :=
          With[{u=IntHide[x^m*(d+e*x^2)^p,x]},
          (a+b*ArcCosh[c*x]) \\[Star] u -
          b*c*Simp[Sqrt[d+e*x^2]/(Sqrt[1+c*x]*Sqrt[-1+c*x])] \\[Star] Int[SimplifyIntegrand[u/Sqrt[d+e*x^2],x],x]] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && IntegerQ[p-1/2] && NeQ[p,-1/2] && (IGtQ[(m+1)/2,0] || ILtQ[(m+2*p+3)/2,0])",
        desc: "Integration by parts and piecewise constant extraction",
        refs: [],
        pattern: x_.pow(m_) * (d__ + e__ * x_.pow(2)).pow(p_) * (a__ + b__ * (c__ * x_).acosh()),
        with: [m_, d__, e__, p_, a__, b__, c__, x_],
        optional: [e__, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && integerq!(&p_ - Atom::num(1) / Atom::num(2))
                && neq!(p_, -(Atom::num(1) / Atom::num(2)))
                && (igtq!((&m_ + Atom::num(1)) / Atom::num(2), 0)
                    || iltq!((&m_ + Atom::num(2) * &p_ + 3) / Atom::num(2), 0))
        },
        rhs: {
            let quadratic_x = &d__ + &e__ * x_.pow(2);
            let argument = &a__ + &b__ * (&c__ * x_).acosh();
            let u = rubi_int_hide(&(x_.pow(&m_) * quadratic_x.pow(&p_)), x_).rubi_rhs();
            let denominator = (Atom::num(1) + &c__ * x_).sqrt()
                * (-Atom::num(1) + &c__ * x_).sqrt();
            let recursive = rubi_simplify_integrand(&(&u / &quadratic_x.sqrt()), x_);
            rubi_star(argument, u)
                    - rubi_star(&b__
                            * &c__
                            * rubi_simp(&(quadratic_x.sqrt() / denominator), x_), rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_6338(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d1__, e1__, d2__, e2__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 6338,
        source: "Int[x_^m_*(d1_+e1_.*x_)^p_*(d2_+e2_.*x_)^p_*(a_.+b_.*ArcCosh[c_.*x_]),x_Symbol] :=
          With[{u=IntHide[x^m*(d1+e1*x)^p*(d2+e2*x)^p,x]},
          (a+b*ArcCosh[c*x]) \\[Star] u -
          b*c*Simp[Sqrt[d1+e1*x]*Sqrt[d2+e2*x]/(Sqrt[1+c*x]*Sqrt[-1+c*x])] \\[Star] Int[SimplifyIntegrand[u/(Sqrt[d1+e1*x]*Sqrt[d2+e2*x]),x],x]] /;
        FreeQ[{a,b,c,d1,e1,d2,e2},x] && EqQ[e1,c*d1] && EqQ[e2,-c*d2] && IntegerQ[p-1/2] && NeQ[p,-1/2] && (IGtQ[(m+1)/2,0] || ILtQ[(m+2*p+3)/2,0])",
        desc: "Integration by parts and piecewise constant extraction",
        refs: [],
        pattern: x_.pow(m_) * (d1__ + e1__ * x_).pow(p_) * (d2__ + e2__ * x_).pow(p_) * (a__ + b__ * (c__ * x_).acosh()),
        with: [m_, d1__, e1__, p_, d2__, e2__, a__, b__, c__, x_],
        optional: [e1__, e2__, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d1__, e1__, d2__, e2__], x_)
                && eqq!(e1__, &c__ * &d1__)
                && eqq!(e2__, -&c__ * &d2__)
                && integerq!(&p_ - Atom::num(1) / Atom::num(2))
                && neq!(p_, -(Atom::num(1) / Atom::num(2)))
                && (igtq!((&m_ + Atom::num(1)) / Atom::num(2), 0)
                    || iltq!((&m_ + Atom::num(2) * &p_ + 3) / Atom::num(2), 0))
        },
        rhs: {
            let l1 = &d1__ + &e1__ * x_;
            let l2 = &d2__ + &e2__ * x_;
            let argument = &a__ + &b__ * (&c__ * x_).acosh();
            let u = rubi_int_hide(&(x_.pow(&m_) * l1.pow(&p_) * l2.pow(&p_)), x_).rubi_rhs();
            let denominator = (Atom::num(1) + &c__ * x_).sqrt()
                * (-Atom::num(1) + &c__ * x_).sqrt();
            let recursive = rubi_simplify_integrand(&(&u / (&l1.sqrt() * &l2.sqrt())), x_);
            rubi_star(argument, u)
                    - rubi_star(&b__
                            * &c__
                            * rubi_simp(&(l1.sqrt() * l2.sqrt() / denominator), x_), rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_6339(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 6339,
        source: "Int[(f_.*x_)^m_*Sqrt[d_+e_.*x_^2]*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
          (f*x)^(m+1)*Sqrt[d+e*x^2]*(a+b*ArcCosh[c*x])^n/(f*(m+1)) -
          b*c*n/(f*(m+1))*Simp[Sqrt[d+e*x^2]/(Sqrt[1+c*x]*Sqrt[-1+c*x])] \\[Star]
            Int[(f*x)^(m+1)*(a+b*ArcCosh[c*x])^(n-1),x] -
          c^2/(f^2*(m+1))*Simp[Sqrt[d+e*x^2]/(Sqrt[1+c*x]*Sqrt[-1+c*x])] \\[Star]
            Int[(f*x)^(m+2)*(a+b*ArcCosh[c*x])^n/(Sqrt[1+c*x]*Sqrt[-1+c*x]),x] /;
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
            let unit1 = Atom::num(1) + &c__ * x_;
            let unit2 = -Atom::num(1) + &c__ * x_;
            let argument = &a__ + &b__ * (&c__ * x_).acosh();
            let ratio_1 = rubi_simp(
                &(&quadratic.sqrt()
                    / (&unit1.sqrt() * &unit2.sqrt())),
                x_,
            );
            let ratio_2 = rubi_simp(
                &(&quadratic.sqrt()
                    / (&unit1.sqrt() * &unit2.sqrt())),
                x_,
            );
            let recursive_1 = scaled.pow(&m_ + Atom::num(1))
                * argument.pow(&n_ - Atom::num(1));
            let recursive_2 = scaled.pow(&m_ + Atom::num(2))
                * argument.pow(&n_)
                / (unit1.sqrt() * unit2.sqrt());
            rubi_simp(&(scaled.pow(&m_ + Atom::num(1)) * quadratic.sqrt() * argument.pow(&n_)
                    / (&f__ * (&m_ + Atom::num(1)))), x_)
                    - rubi_star(&b__ * &c__ * &n_ / (&f__ * (&m_ + Atom::num(1)))
                            * ratio_1, rubi_rhs_int(&recursive_1, x_))
                    - rubi_star(c__.pow(2) / (f__.pow(2) * (&m_ + Atom::num(1))) * ratio_2, rubi_rhs_int(&recursive_2, x_))
        },
    ));
}

fn push_rules_rule_6340(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, f__, d1__, e1__, d2__, e2__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 6340,
        source: "Int[(f_.*x_)^m_*Sqrt[d1_+e1_.*x_]*Sqrt[d2_+e2_.*x_]*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
          (f*x)^(m+1)*Sqrt[d1+e1*x]*Sqrt[d2+e2*x]*(a+b*ArcCosh[c*x])^n/(f*(m+1)) -
          b*c*n/(f*(m+1))*Simp[Sqrt[d1+e1*x]/Sqrt[1+c*x]]*Simp[Sqrt[d2+e2*x]/Sqrt[-1+c*x]] \\[Star]
            Int[(f*x)^(m+1)*(a+b*ArcCosh[c*x])^(n-1),x] -
          c^2/(f^2*(m+1))*Simp[Sqrt[d1+e1*x]/Sqrt[1+c*x]]*Simp[Sqrt[d2+e2*x]/Sqrt[-1+c*x]] \\[Star]
            Int[((f*x)^(m+2)*(a+b*ArcCosh[c*x])^n)/(Sqrt[1+c*x]*Sqrt[-1+c*x]),x] /;
        FreeQ[{a,b,c,d1,e1,d2,e2,f},x] && EqQ[e1,c*d1] && EqQ[e2,-c*d2] && GtQ[n,0] && LtQ[m,-1]",
        desc: "Inverted integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [f__, m_, d1__, e1__, d2__, e2__, a__, b__, c__, n_, x_],
        optional: [f__, e1__, e2__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d1__, e1__, d2__, e2__, f__], x_)
                && eqq!(e1__, &c__ * &d1__)
                && eqq!(e2__, -&c__ * &d2__)
                && gtq!(n_, 0)
                && ltq!(m_, -1)
        },
        rhs: {
            let scaled = &f__ * x_;
            let l1 = &d1__ + &e1__ * x_;
            let l2 = &d2__ + &e2__ * x_;
            let unit1 = Atom::num(1) + &c__ * x_;
            let unit2 = -Atom::num(1) + &c__ * x_;
            let argument = &a__ + &b__ * (&c__ * x_).acosh();
            let ratio_1 = rubi_simp(&(&l1.sqrt() / &unit1.sqrt()), x_)
                * rubi_simp(&(&l2.sqrt() / &unit2.sqrt()), x_);
            let ratio_2 = rubi_simp(&(&l1.sqrt() / &unit1.sqrt()), x_)
                * rubi_simp(&(&l2.sqrt() / &unit2.sqrt()), x_);
            let recursive_1 = scaled.pow(&m_ + Atom::num(1))
                * argument.pow(&n_ - Atom::num(1));
            let recursive_2 = scaled.pow(&m_ + Atom::num(2))
                * argument.pow(&n_)
                / (unit1.sqrt() * unit2.sqrt());
            rubi_simp(&(scaled.pow(&m_ + Atom::num(1)) * l1.sqrt() * l2.sqrt() * argument.pow(&n_)
                    / (&f__ * (&m_ + Atom::num(1)))), x_)
                    - rubi_star(&b__ * &c__ * &n_ / (&f__ * (&m_ + Atom::num(1)))
                            * ratio_1, rubi_rhs_int(&recursive_1, x_))
                    - rubi_star(c__.pow(2) / (f__.pow(2) * (&m_ + Atom::num(1))) * ratio_2, rubi_rhs_int(&recursive_2, x_))
        },
    ));
}

fn push_rules_rule_6341(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 6341,
        source: "Int[(f_.*x_)^m_*Sqrt[d_+e_.*x_^2]*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
          (f*x)^(m+1)*Sqrt[d+e*x^2]*(a+b*ArcCosh[c*x])^n/(f*(m+2)) -
          b*c*n/(f*(m+2))*Simp[Sqrt[d+e*x^2]/(Sqrt[1+c*x]*Sqrt[-1+c*x])] \\[Star]
            Int[(f*x)^(m+1)*(a+b*ArcCosh[c*x])^(n-1),x] -
          1/(m+2)*Simp[Sqrt[d+e*x^2]/(Sqrt[1+c*x]*Sqrt[-1+c*x])] \\[Star]
            Int[(f*x)^m*(a+b*ArcCosh[c*x])^n/(Sqrt[1+c*x]*Sqrt[-1+c*x]),x] /;
        FreeQ[{a,b,c,d,e,f,m},x] && EqQ[c^2*d+e,0] && IGtQ[n,0] && (IGtQ[m,-2] || EqQ[n,1])",
        desc: "Inverted integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [f__, m_, d__, e__, a__, b__, c__, n_, x_],
        optional: [f__, e__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && igtq!(n_, 0)
                && (igtq!(m_, -2) || eqq!(n_, 1))
        },
        rhs: {
            let scaled = &f__ * x_;
            let quadratic = &d__ + &e__ * x_.pow(2);
            let unit1 = Atom::num(1) + &c__ * x_;
            let unit2 = -Atom::num(1) + &c__ * x_;
            let argument = &a__ + &b__ * (&c__ * x_).acosh();
            let ratio_1 = rubi_simp(
                &(&quadratic.sqrt()
                    / (&unit1.sqrt() * &unit2.sqrt())),
                x_,
            );
            let ratio_2 = rubi_simp(
                &(&quadratic.sqrt()
                    / (&unit1.sqrt() * &unit2.sqrt())),
                x_,
            );
            let recursive_1 = scaled.pow(&m_ + Atom::num(1))
                * argument.pow(&n_ - Atom::num(1));
            let recursive_2 = scaled.pow(&m_) * argument.pow(&n_)
                / (unit1.sqrt() * unit2.sqrt());
            rubi_simp(&(scaled.pow(&m_ + Atom::num(1)) * quadratic.sqrt() * argument.pow(&n_)
                    / (&f__ * (&m_ + Atom::num(2)))), x_)
                    - rubi_star(&b__ * &c__ * &n_ / (&f__ * (&m_ + Atom::num(2)))
                            * ratio_1, rubi_rhs_int(&recursive_1, x_))
                    - rubi_star(ratio_2 / (&m_ + Atom::num(2)), rubi_rhs_int(&recursive_2, x_))
        },
    ));
}

fn push_rules_rule_6342(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, f__, d1__, e1__, d2__, e2__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 6342,
        source: "Int[(f_.*x_)^m_*Sqrt[d1_+e1_.*x_]*Sqrt[d2_+e2_.*x_]*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
          (f*x)^(m+1)*Sqrt[d1+e1*x]*Sqrt[d2+e2*x]*(a+b*ArcCosh[c*x])^n/(f*(m+2)) -
          b*c*n/(f*(m+2))*Simp[Sqrt[d1+e1*x]/Sqrt[1+c*x]]*Simp[Sqrt[d2+e2*x]/Sqrt[-1+c*x]] \\[Star]
            Int[(f*x)^(m+1)*(a+b*ArcCosh[c*x])^(n-1),x] -
          1/(m+2)*Simp[Sqrt[d1+e1*x]/Sqrt[1+c*x]]*Simp[Sqrt[d2+e2*x]/Sqrt[-1+c*x]] \\[Star]
            Int[(f*x)^m*(a+b*ArcCosh[c*x])^n/(Sqrt[1+c*x]*Sqrt[-1+c*x]),x] /;
        FreeQ[{a,b,c,d1,e1,d2,e2,f,m},x] && EqQ[e1,c*d1] && EqQ[e2,-c*d2] && IGtQ[n,0] && (IGtQ[m,-2] || EqQ[n,1])",
        desc: "Inverted integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [f__, m_, d1__, e1__, d2__, e2__, a__, b__, c__, n_, x_],
        optional: [f__, e1__, e2__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d1__, e1__, d2__, e2__, f__, m_], x_)
                && eqq!(e1__, &c__ * &d1__)
                && eqq!(e2__, -&c__ * &d2__)
                && igtq!(n_, 0)
                && (igtq!(m_, -2) || eqq!(n_, 1))
        },
        rhs: {
            let scaled = &f__ * x_;
            let l1 = &d1__ + &e1__ * x_;
            let l2 = &d2__ + &e2__ * x_;
            let unit1 = Atom::num(1) + &c__ * x_;
            let unit2 = -Atom::num(1) + &c__ * x_;
            let argument = &a__ + &b__ * (&c__ * x_).acosh();
            let ratio_1 = rubi_simp(&(&l1.sqrt() / &unit1.sqrt()), x_)
                * rubi_simp(&(&l2.sqrt() / &unit2.sqrt()), x_);
            let ratio_2 = rubi_simp(&(&l1.sqrt() / &unit1.sqrt()), x_)
                * rubi_simp(&(&l2.sqrt() / &unit2.sqrt()), x_);
            let recursive_1 = scaled.pow(&m_ + Atom::num(1))
                * argument.pow(&n_ - Atom::num(1));
            let recursive_2 = scaled.pow(&m_) * argument.pow(&n_)
                / (unit1.sqrt() * unit2.sqrt());
            rubi_simp(&(scaled.pow(&m_ + Atom::num(1)) * l1.sqrt() * l2.sqrt() * argument.pow(&n_)
                    / (&f__ * (&m_ + Atom::num(2)))), x_)
                    - rubi_star(&b__ * &c__ * &n_ / (&f__ * (&m_ + Atom::num(2)))
                            * ratio_1, rubi_rhs_int(&recursive_1, x_))
                    - rubi_star(ratio_2 / (&m_ + Atom::num(2)), rubi_rhs_int(&recursive_2, x_))
        },
    ));
}

fn push_rules_rule_6343(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6343,
        source: "Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
          (f*x)^(m+1)*(d+e*x^2)^p*(a+b*ArcCosh[c*x])^n/(f*(m+1)) -
          2*e*p/(f^2*(m+1)) \\[Star] Int[(f*x)^(m+2)*(d+e*x^2)^(p-1)*(a+b*ArcCosh[c*x])^n,x] -
          b*c*n/(f*(m+1))*Simp[(d+e*x^2)^p/((1+c*x)^p*(-1+c*x)^p)] \\[Star]
            Int[(f*x)^(m+1)*(1+c*x)^(p-1/2)*(-1+c*x)^(p-1/2)*(a+b*ArcCosh[c*x])^(n-1),x] /;
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
            let a__ = &a__;
            let b__ = &b__;
            let c__ = &c__;
            let d__ = &d__;
            let e__ = &e__;
            let f__ = &f__;
            let m = &m_;
            let n = &n_;
            let p = &p_;
            let scaled = f__ * x_;
            let quadratic = d__ + e__ * x_.pow(2);
            let unit1 = Atom::num(1) + c__ * x_;
            let unit2 = -Atom::num(1) + c__ * x_;
            let argument = a__ + b__ * (c__ * x_).acosh();
            let recursive_1 = scaled.pow(m + Atom::num(2))
                * quadratic.pow(p - Atom::num(1))
                * argument.pow(n);
            let recursive_2 = scaled.pow(m + Atom::num(1))
                * unit1.pow(p - Atom::num(1) / Atom::num(2))
                * unit2.pow(p - Atom::num(1) / Atom::num(2))
                * argument.pow(n - Atom::num(1));
            rubi_simp(&(scaled.pow(m + Atom::num(1)) * quadratic.pow(p) * argument.pow(n)
                    / (f__ * (m + Atom::num(1)))), x_)
                    - rubi_star(Atom::num(2) * e__ * p / (f__.pow(2) * (m + Atom::num(1))), rubi_rhs_int(&recursive_1, x_))
                    - rubi_star(b__ * c__ * n / (f__ * (m + Atom::num(1)))
                            * rubi_simp(&(quadratic.pow(p) / (unit1.pow(p) * unit2.pow(p))), x_), rubi_rhs_int(&recursive_2, x_))
        },
    ));
}

fn push_rules_rule_6344(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, f__, d1__, e1__, d2__, e2__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6344,
        source: "Int[(f_.*x_)^m_*(d1_+e1_.*x_)^p_*(d2_+e2_.*x_)^p_*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
          (f*x)^(m+1)*(d1+e1*x)^p*(d2+e2*x)^p*(a+b*ArcCosh[c*x])^n/(f*(m+1)) -
          2*e1*e2*p/(f^2*(m+1)) \\[Star] Int[(f*x)^(m+2)*(d1+e1*x)^(p-1)*(d2+e2*x)^(p-1)*(a+b*ArcCosh[c*x])^n,x] -
          b*c*n/(f*(m+1))*Simp[(d1+e1*x)^p/(1+c*x)^p]*Simp[(d2+e2*x)^p/(-1+c*x)^p] \\[Star]
            Int[(f*x)^(m+1)*(1+c*x)^(p-1/2)*(-1+c*x)^(p-1/2)*(a+b*ArcCosh[c*x])^(n-1),x] /;
        FreeQ[{a,b,c,d1,e1,d2,e2,f},x] && EqQ[e1,c*d1] && EqQ[e2,-c*d2] && GtQ[n,0] && GtQ[p,0] && LtQ[m,-1]",
        desc: "Inverted integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [f__, m_, d1__, e1__, p_, d2__, e2__, a__, b__, c__, n_, x_],
        optional: [f__, e1__, e2__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d1__, e1__, d2__, e2__, f__], x_)
                && eqq!(e1__, &c__ * &d1__)
                && eqq!(e2__, -&c__ * &d2__)
                && gtq!(n_, 0)
                && gtq!(p_, 0)
                && ltq!(m_, -1)
        },
        rhs: {
            let a__ = &a__;
            let b__ = &b__;
            let c__ = &c__;
            let d1__ = &d1__;
            let e1__ = &e1__;
            let d2__ = &d2__;
            let e2__ = &e2__;
            let f__ = &f__;
            let m = &m_;
            let n = &n_;
            let p = &p_;
            let scaled = f__ * x_;
            let l1 = d1__ + e1__ * x_;
            let l2 = d2__ + e2__ * x_;
            let unit1 = Atom::num(1) + c__ * x_;
            let unit2 = -Atom::num(1) + c__ * x_;
            let argument = a__ + b__ * (c__ * x_).acosh();
            let recursive_1 = scaled.pow(m + Atom::num(2))
                * l1.pow(p - Atom::num(1))
                * l2.pow(p - Atom::num(1))
                * argument.pow(n);
            let recursive_2 = scaled.pow(m + Atom::num(1))
                * unit1.pow(p - Atom::num(1) / Atom::num(2))
                * unit2.pow(p - Atom::num(1) / Atom::num(2))
                * argument.pow(n - Atom::num(1));
            rubi_simp(&(scaled.pow(m + Atom::num(1)) * l1.pow(p) * l2.pow(p) * argument.pow(n)
                    / (f__ * (m + Atom::num(1)))), x_)
                    - rubi_star(Atom::num(2) * e1__ * e2__ * p / (f__.pow(2) * (m + Atom::num(1))), rubi_rhs_int(&recursive_1, x_))
                    - rubi_star(b__ * c__ * n / (f__ * (m + Atom::num(1)))
                            * rubi_simp(&(l1.pow(p) / unit1.pow(p)), x_)
                            * rubi_simp(&(l2.pow(p) / unit2.pow(p)), x_), rubi_rhs_int(&recursive_2, x_))
        },
    ));
}

fn push_rules_rule_6345(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6345,
        source: "Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
          (f*x)^(m+1)*(d+e*x^2)^p*(a+b*ArcCosh[c*x])^n/(f*(m+2*p+1)) +
          2*d*p/(m+2*p+1) \\[Star] Int[(f*x)^m*(d+e*x^2)^(p-1)*(a+b*ArcCosh[c*x])^n,x] -
          b*c*n/(f*(m+2*p+1))*Simp[(d+e*x^2)^p/((1+c*x)^p*(-1+c*x)^p)] \\[Star]
            Int[(f*x)^(m+1)*(1+c*x)^(p-1/2)*(-1+c*x)^(p-1/2)*(a+b*ArcCosh[c*x])^(n-1),x] /;
        FreeQ[{a,b,c,d,e,f,m},x] && EqQ[c^2*d+e,0] && GtQ[n,0] && GtQ[p,0] && Not[LtQ[m,-1]]",
        desc: "Simplify the integrand and continue with the simpler form.",
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
            let a__ = &a__;
            let b__ = &b__;
            let c__ = &c__;
            let d__ = &d__;
            let e__ = &e__;
            let f__ = &f__;
            let m = &m_;
            let n = &n_;
            let p = &p_;
            let scaled = f__ * x_;
            let quadratic = d__ + e__ * x_.pow(2);
            let unit1 = Atom::num(1) + c__ * x_;
            let unit2 = -Atom::num(1) + c__ * x_;
            let argument = a__ + b__ * (c__ * x_).acosh();
            let denominator = m + Atom::num(2) * p + 1;
            let recursive_1 = scaled.pow(m)
                * quadratic.pow(p - Atom::num(1))
                * argument.pow(n);
            let recursive_2 = scaled.pow(m + Atom::num(1))
                * unit1.pow(p - Atom::num(1) / Atom::num(2))
                * unit2.pow(p - Atom::num(1) / Atom::num(2))
                * argument.pow(n - Atom::num(1));
            rubi_simp(&(scaled.pow(m + Atom::num(1)) * quadratic.pow(p) * argument.pow(n)
                    / (f__ * &denominator)), x_)
                    + rubi_star(Atom::num(2) * d__ * p / &denominator, rubi_rhs_int(&recursive_1, x_))
                    - rubi_star(b__ * c__ * n / (f__ * &denominator)
                            * rubi_simp(&(quadratic.pow(p) / (unit1.pow(p) * unit2.pow(p))), x_), rubi_rhs_int(&recursive_2, x_))
        },
    ));
}

fn push_rules_rule_6346(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, f__, d1__, e1__, d2__, e2__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6346,
        source: "Int[(f_.*x_)^m_*(d1_+e1_.*x_)^p_*(d2_+e2_.*x_)^p_*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
          (f*x)^(m+1)*(d1+e1*x)^p*(d2+e2*x)^p*(a+b*ArcCosh[c*x])^n/(f*(m+2*p+1)) +
          2*d1*d2*p/(m+2*p+1) \\[Star] Int[(f*x)^m*(d1+e1*x)^(p-1)*(d2+e2*x)^(p-1)*(a+b*ArcCosh[c*x])^n,x] -
          b*c*n/(f*(m+2*p+1))*Simp[(d1+e1*x)^p/(1+c*x)^p]*Simp[(d2+e2*x)^p/(-1+c*x)^p] \\[Star]
            Int[(f*x)^(m+1)*(1+c*x)^(p-1/2)*(-1+c*x)^(p-1/2)*(a+b*ArcCosh[c*x])^(n-1),x] /;
        FreeQ[{a,b,c,d1,e1,d2,e2,f,m},x] && EqQ[e1,c*d1] && EqQ[e2,-c*d2] && GtQ[n,0] && GtQ[p,0] && Not[LtQ[m,-1]]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [f__, m_, d1__, e1__, p_, d2__, e2__, a__, b__, c__, n_, x_],
        optional: [f__, e1__, e2__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d1__, e1__, d2__, e2__, f__, m_], x_)
                && eqq!(e1__, &c__ * &d1__)
                && eqq!(e2__, -&c__ * &d2__)
                && gtq!(n_, 0)
                && gtq!(p_, 0)
                && !ltq!(m_, -1)
        },
        rhs: {
            let a__ = &a__;
            let b__ = &b__;
            let c__ = &c__;
            let d1__ = &d1__;
            let e1__ = &e1__;
            let d2__ = &d2__;
            let e2__ = &e2__;
            let f__ = &f__;
            let m = &m_;
            let n = &n_;
            let p = &p_;
            let scaled = f__ * x_;
            let l1 = d1__ + e1__ * x_;
            let l2 = d2__ + e2__ * x_;
            let unit1 = Atom::num(1) + c__ * x_;
            let unit2 = -Atom::num(1) + c__ * x_;
            let argument = a__ + b__ * (c__ * x_).acosh();
            let denominator = m + Atom::num(2) * p + 1;
            let recursive_1 = scaled.pow(m)
                * l1.pow(p - Atom::num(1))
                * l2.pow(p - Atom::num(1))
                * argument.pow(n);
            let recursive_2 = scaled.pow(m + Atom::num(1))
                * unit1.pow(p - Atom::num(1) / Atom::num(2))
                * unit2.pow(p - Atom::num(1) / Atom::num(2))
                * argument.pow(n - Atom::num(1));
            rubi_simp(&(scaled.pow(m + Atom::num(1)) * l1.pow(p) * l2.pow(p) * argument.pow(n)
                    / (f__ * &denominator)), x_)
                    + rubi_star(Atom::num(2) * d1__ * d2__ * p / &denominator, rubi_rhs_int(&recursive_1, x_))
                    - rubi_star(b__ * c__ * n / (f__ * &denominator)
                            * rubi_simp(&(l1.pow(p) / unit1.pow(p)), x_)
                            * rubi_simp(&(l2.pow(p) / unit2.pow(p)), x_), rubi_rhs_int(&recursive_2, x_))
        },
    ));
}

fn push_rules_rule_6347(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6347,
        source: "Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
          (f*x)^(m+1)*(d+e*x^2)^(p+1)*(a+b*ArcCosh[c*x])^n/(d*f*(m+1)) +
          c^2*(m+2*p+3)/(f^2*(m+1)) \\[Star] Int[(f*x)^(m+2)*(d+e*x^2)^p*(a+b*ArcCosh[c*x])^n,x] +
          b*c*n/(f*(m+1))*Simp[(d+e*x^2)^p/((1+c*x)^p*(-1+c*x)^p)] \\[Star]
            Int[(f*x)^(m+1)*(1+c*x)^(p+1/2)*(-1+c*x)^(p+1/2)*(a+b*ArcCosh[c*x])^(n-1),x] /;
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
            let a__ = &a__;
            let b__ = &b__;
            let c__ = &c__;
            let d__ = &d__;
            let e__ = &e__;
            let f__ = &f__;
            let m = &m_;
            let n = &n_;
            let p = &p_;
            let scaled = f__ * x_;
            let quadratic = d__ + e__ * x_.pow(2);
            let unit1 = Atom::num(1) + c__ * x_;
            let unit2 = -Atom::num(1) + c__ * x_;
            let argument = a__ + b__ * (c__ * x_).acosh();
            let recursive_1 = scaled.pow(m + Atom::num(2))
                * quadratic.pow(p)
                * argument.pow(n);
            let recursive_2 = scaled.pow(m + Atom::num(1))
                * unit1.pow(p + Atom::num(1) / Atom::num(2))
                * unit2.pow(p + Atom::num(1) / Atom::num(2))
                * argument.pow(n - Atom::num(1));
            rubi_simp(&(scaled.pow(m + Atom::num(1))
                    * quadratic.pow(p + Atom::num(1))
                    * argument.pow(n)
                    / (d__ * f__ * (m + Atom::num(1)))), x_)
                    + rubi_star(c__.pow(2) * (m + Atom::num(2) * p + 3) / (f__.pow(2) * (m + Atom::num(1))), rubi_rhs_int(&recursive_1, x_))
                    + rubi_star(b__ * c__ * n / (f__ * (m + Atom::num(1)))
                            * rubi_simp(&(quadratic.pow(p) / (unit1.pow(p) * unit2.pow(p))), x_), rubi_rhs_int(&recursive_2, x_))
        },
    ));
}

fn push_rules_rule_6348(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, f__, d1__, e1__, d2__, e2__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6348,
        source: "Int[(f_.*x_)^m_*(d1_+e1_.*x_)^p_*(d2_+e2_.*x_)^p_*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
          (f*x)^(m+1)*(d1+e1*x)^(p+1)*(d2+e2*x)^(p+1)*(a+b*ArcCosh[c*x])^n/(d1*d2*f*(m+1)) +
          c^2*(m+2*p+3)/(f^2*(m+1)) \\[Star] Int[(f*x)^(m+2)*(d1+e1*x)^p*(d2+e2*x)^p*(a+b*ArcCosh[c*x])^n,x] +
          b*c*n/(f*(m+1))*Simp[(d1+e1*x)^p/(1+c*x)^p]*Simp[(d2+e2*x)^p/(-1+c*x)^p] \\[Star]
            Int[(f*x)^(m+1)*(1+c*x)^(p+1/2)*(-1+c*x)^(p+1/2)*(a+b*ArcCosh[c*x])^(n-1),x] /;
        FreeQ[{a,b,c,d1,e1,d2,e2,f,p},x] && EqQ[e1,c*d1] && EqQ[e2,-c*d2] && GtQ[n,0] && ILtQ[m,-1]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [f__, m_, d1__, e1__, p_, d2__, e2__, a__, b__, c__, n_, x_],
        optional: [f__, e1__, e2__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d1__, e1__, d2__, e2__, f__, p_], x_)
                && eqq!(e1__, &c__ * &d1__)
                && eqq!(e2__, -&c__ * &d2__)
                && gtq!(n_, 0)
                && iltq!(m_, -1)
        },
        rhs: {
            let a__ = &a__;
            let b__ = &b__;
            let c__ = &c__;
            let d1__ = &d1__;
            let e1__ = &e1__;
            let d2__ = &d2__;
            let e2__ = &e2__;
            let f__ = &f__;
            let m = &m_;
            let n = &n_;
            let p = &p_;
            let scaled = f__ * x_;
            let l1 = d1__ + e1__ * x_;
            let l2 = d2__ + e2__ * x_;
            let unit1 = Atom::num(1) + c__ * x_;
            let unit2 = -Atom::num(1) + c__ * x_;
            let argument = a__ + b__ * (c__ * x_).acosh();
            let recursive_1 = scaled.pow(m + Atom::num(2))
                * l1.pow(p)
                * l2.pow(p)
                * argument.pow(n);
            let recursive_2 = scaled.pow(m + Atom::num(1))
                * unit1.pow(p + Atom::num(1) / Atom::num(2))
                * unit2.pow(p + Atom::num(1) / Atom::num(2))
                * argument.pow(n - Atom::num(1));
            rubi_simp(&(scaled.pow(m + Atom::num(1))
                    * l1.pow(p + Atom::num(1))
                    * l2.pow(p + Atom::num(1))
                    * argument.pow(n)
                    / (d1__ * d2__ * f__ * (m + Atom::num(1)))), x_)
                    + rubi_star(c__.pow(2) * (m + Atom::num(2) * p + 3) / (f__.pow(2) * (m + Atom::num(1))), rubi_rhs_int(&recursive_1, x_))
                    + rubi_star(b__ * c__ * n / (f__ * (m + Atom::num(1)))
                            * rubi_simp(&(l1.pow(p) / unit1.pow(p)), x_)
                            * rubi_simp(&(l2.pow(p) / unit2.pow(p)), x_), rubi_rhs_int(&recursive_2, x_))
        },
    ));
}

fn push_rules_rule_6349(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6349,
        source: "Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
          f*(f*x)^(m-1)*(d+e*x^2)^(p+1)*(a+b*ArcCosh[c*x])^n/(2*e*(p+1)) -
          f^2*(m-1)/(2*e*(p+1)) \\[Star] Int[(f*x)^(m-2)*(d+e*x^2)^(p+1)*(a+b*ArcCosh[c*x])^n,x] -
          b*f*n/(2*c*(p+1))*Simp[(d+e*x^2)^p/((1+c*x)^p*(-1+c*x)^p)] \\[Star]
            Int[(f*x)^(m-1)*(1+c*x)^(p+1/2)*(-1+c*x)^(p+1/2)*(a+b*ArcCosh[c*x])^(n-1),x] /;
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
            let a__ = &a__;
            let b__ = &b__;
            let c__ = &c__;
            let d__ = &d__;
            let e__ = &e__;
            let f__ = &f__;
            let m = &m_;
            let n = &n_;
            let p = &p_;
            let scaled = f__ * x_;
            let quadratic = d__ + e__ * x_.pow(2);
            let unit1 = Atom::num(1) + c__ * x_;
            let unit2 = -Atom::num(1) + c__ * x_;
            let argument = a__ + b__ * (c__ * x_).acosh();
            let recursive_1 = scaled.pow(m - Atom::num(2))
                * quadratic.pow(p + Atom::num(1))
                * argument.pow(n);
            let recursive_2 = scaled.pow(m - Atom::num(1))
                * unit1.pow(p + Atom::num(1) / Atom::num(2))
                * unit2.pow(p + Atom::num(1) / Atom::num(2))
                * argument.pow(n - Atom::num(1));
            rubi_simp(&(f__ * scaled.pow(m - Atom::num(1))
                    * quadratic.pow(p + Atom::num(1))
                    * argument.pow(n)
                    / (Atom::num(2) * e__ * (p + Atom::num(1)))), x_)
                    - rubi_star(f__.pow(2) * (m - Atom::num(1)) / (Atom::num(2) * e__ * (p + Atom::num(1))), rubi_rhs_int(&recursive_1, x_))
                    - rubi_star(b__ * f__ * n / (Atom::num(2) * c__ * (p + Atom::num(1)))
                            * rubi_simp(&(quadratic.pow(p) / (unit1.pow(p) * unit2.pow(p))), x_), rubi_rhs_int(&recursive_2, x_))
        },
    ));
}

fn push_rules_rule_6350(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, f__, d1__, e1__, d2__, e2__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6350,
        source: "Int[(f_.*x_)^m_*(d1_+e1_.*x_)^p_*(d2_+e2_.*x_)^p_*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
          f*(f*x)^(m-1)*(d1+e1*x)^(p+1)*(d2+e2*x)^(p+1)*(a+b*ArcCosh[c*x])^n/(2*e1*e2*(p+1)) -
          f^2*(m-1)/(2*e1*e2*(p+1)) \\[Star] Int[(f*x)^(m-2)*(d1+e1*x)^(p+1)*(d2+e2*x)^(p+1)*(a+b*ArcCosh[c*x])^n,x] -
          b*f*n/(2*c*(p+1))*Simp[(d1+e1*x)^p/(1+c*x)^p]*Simp[(d2+e2*x)^p/(-1+c*x)^p] \\[Star]
            Int[(f*x)^(m-1)*(1+c*x)^(p+1/2)*(-1+c*x)^(p+1/2)*(a+b*ArcCosh[c*x])^(n-1),x] /;
        FreeQ[{a,b,c,d1,e1,d2,e2,f},x] && EqQ[e1,c*d1] && EqQ[e2,-c*d2] && GtQ[n,0] && LtQ[p,-1] && IGtQ[m,1]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [f__, m_, d1__, e1__, p_, d2__, e2__, a__, b__, c__, n_, x_],
        optional: [f__, e1__, e2__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d1__, e1__, d2__, e2__, f__], x_)
                && eqq!(e1__, &c__ * &d1__)
                && eqq!(e2__, -&c__ * &d2__)
                && gtq!(n_, 0)
                && ltq!(p_, -1)
                && igtq!(m_, 1)
        },
        rhs: {
            let a__ = &a__;
            let b__ = &b__;
            let c__ = &c__;
            let d1__ = &d1__;
            let e1__ = &e1__;
            let d2__ = &d2__;
            let e2__ = &e2__;
            let f__ = &f__;
            let m = &m_;
            let n = &n_;
            let p = &p_;
            let scaled = f__ * x_;
            let l1 = d1__ + e1__ * x_;
            let l2 = d2__ + e2__ * x_;
            let unit1 = Atom::num(1) + c__ * x_;
            let unit2 = -Atom::num(1) + c__ * x_;
            let argument = a__ + b__ * (c__ * x_).acosh();
            let recursive_1 = scaled.pow(m - Atom::num(2))
                * l1.pow(p + Atom::num(1))
                * l2.pow(p + Atom::num(1))
                * argument.pow(n);
            let recursive_2 = scaled.pow(m - Atom::num(1))
                * unit1.pow(p + Atom::num(1) / Atom::num(2))
                * unit2.pow(p + Atom::num(1) / Atom::num(2))
                * argument.pow(n - Atom::num(1));
            rubi_simp(&(f__ * scaled.pow(m - Atom::num(1))
                    * l1.pow(p + Atom::num(1))
                    * l2.pow(p + Atom::num(1))
                    * argument.pow(n)
                    / (Atom::num(2) * e1__ * e2__ * (p + Atom::num(1)))), x_)
                    - rubi_star(f__.pow(2) * (m - Atom::num(1))
                            / (Atom::num(2) * e1__ * e2__ * (p + Atom::num(1))), rubi_rhs_int(&recursive_1, x_))
                    - rubi_star(b__ * f__ * n / (Atom::num(2) * c__ * (p + Atom::num(1)))
                            * rubi_simp(&(l1.pow(p) / unit1.pow(p)), x_)
                            * rubi_simp(&(l2.pow(p) / unit2.pow(p)), x_), rubi_rhs_int(&recursive_2, x_))
        },
    ));
}

fn push_rules_rule_6351(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6351,
        source: "Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
          -(f*x)^(m+1)*(d+e*x^2)^(p+1)*(a+b*ArcCosh[c*x])^n/(2*d*f*(p+1)) +
          (m+2*p+3)/(2*d*(p+1)) \\[Star] Int[(f*x)^m*(d+e*x^2)^(p+1)*(a+b*ArcCosh[c*x])^n,x] -
          b*c*n/(2*f*(p+1))*Simp[(d+e*x^2)^p/((1+c*x)^p*(-1+c*x)^p)] \\[Star]
            Int[(f*x)^(m+1)*(1+c*x)^(p+1/2)*(-1+c*x)^(p+1/2)*(a+b*ArcCosh[c*x])^(n-1),x] /;
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
            let a__ = &a__;
            let b__ = &b__;
            let c__ = &c__;
            let d__ = &d__;
            let e__ = &e__;
            let f__ = &f__;
            let m = &m_;
            let n = &n_;
            let p = &p_;
            let scaled = f__ * x_;
            let quadratic = d__ + e__ * x_.pow(2);
            let unit1 = Atom::num(1) + c__ * x_;
            let unit2 = -Atom::num(1) + c__ * x_;
            let argument = a__ + b__ * (c__ * x_).acosh();
            let recursive_1 = scaled.pow(m)
                * quadratic.pow(p + Atom::num(1))
                * argument.pow(n);
            let recursive_2 = scaled.pow(m + Atom::num(1))
                * unit1.pow(p + Atom::num(1) / Atom::num(2))
                * unit2.pow(p + Atom::num(1) / Atom::num(2))
                * argument.pow(n - Atom::num(1));
            rubi_simp(&(-scaled.pow(m + Atom::num(1))
                    * quadratic.pow(p + Atom::num(1))
                    * argument.pow(n)
                    / (Atom::num(2) * d__ * f__ * (p + Atom::num(1)))), x_)
                    + rubi_star((m + Atom::num(2) * p + 3) / (Atom::num(2) * d__ * (p + Atom::num(1))), rubi_rhs_int(&recursive_1, x_))
                    - rubi_star(b__ * c__ * n / (Atom::num(2) * f__ * (p + Atom::num(1)))
                            * rubi_simp(&(quadratic.pow(p) / (unit1.pow(p) * unit2.pow(p))), x_), rubi_rhs_int(&recursive_2, x_))
        },
    ));
}

fn push_rules_rule_6352(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, f__, d1__, e1__, d2__, e2__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6352,
        source: "Int[(f_.*x_)^m_*(d1_+e1_.*x_)^p_*(d2_+e2_.*x_)^p_*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
          -(f*x)^(m+1)*(d1+e1*x)^(p+1)*(d2+e2*x)^(p+1)*(a+b*ArcCosh[c*x])^n/(2*d1*d2*f*(p+1)) +
          (m+2*p+3)/(2*d1*d2*(p+1)) \\[Star] Int[(f*x)^m*(d1+e1*x)^(p+1)*(d2+e2*x)^(p+1)*(a+b*ArcCosh[c*x])^n,x] -
          b*c*n/(2*f*(p+1))*Simp[(d1+e1*x)^p/(1+c*x)^p]*Simp[(d2+e2*x)^p/(-1+c*x)^p] \\[Star]
            Int[(f*x)^(m+1)*(1+c*x)^(p+1/2)*(-1+c*x)^(p+1/2)*(a+b*ArcCosh[c*x])^(n-1),x] /;
        FreeQ[{a,b,c,d1,e1,d2,e2,f,m},x] && EqQ[e1,c*d1] && EqQ[e2,-c*d2] && GtQ[n,0] && LtQ[p,-1] && Not[GtQ[m,1]] && (IntegerQ[m] || EqQ[n,1])",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [f__, m_, d1__, e1__, p_, d2__, e2__, a__, b__, c__, n_, x_],
        optional: [f__, e1__, e2__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d1__, e1__, d2__, e2__, f__, m_], x_)
                && eqq!(e1__, &c__ * &d1__)
                && eqq!(e2__, -&c__ * &d2__)
                && gtq!(n_, 0)
                && ltq!(p_, -1)
                && !gtq!(m_, 1)
                && (integerq!(m_) || eqq!(n_, 1))
        },
        rhs: {
            let a__ = &a__;
            let b__ = &b__;
            let c__ = &c__;
            let d1__ = &d1__;
            let e1__ = &e1__;
            let d2__ = &d2__;
            let e2__ = &e2__;
            let f__ = &f__;
            let m = &m_;
            let n = &n_;
            let p = &p_;
            let scaled = f__ * x_;
            let l1 = d1__ + e1__ * x_;
            let l2 = d2__ + e2__ * x_;
            let unit1 = Atom::num(1) + c__ * x_;
            let unit2 = -Atom::num(1) + c__ * x_;
            let argument = a__ + b__ * (c__ * x_).acosh();
            let recursive_1 = scaled.pow(m)
                * l1.pow(p + Atom::num(1))
                * l2.pow(p + Atom::num(1))
                * argument.pow(n);
            let recursive_2 = scaled.pow(m + Atom::num(1))
                * unit1.pow(p + Atom::num(1) / Atom::num(2))
                * unit2.pow(p + Atom::num(1) / Atom::num(2))
                * argument.pow(n - Atom::num(1));
            rubi_simp(&(-scaled.pow(m + Atom::num(1))
                    * l1.pow(p + Atom::num(1))
                    * l2.pow(p + Atom::num(1))
                    * argument.pow(n)
                    / (Atom::num(2) * d1__ * d2__ * f__ * (p + Atom::num(1)))), x_)
                    + rubi_star((m + Atom::num(2) * p + 3)
                            / (Atom::num(2) * d1__ * d2__ * (p + Atom::num(1))), rubi_rhs_int(&recursive_1, x_))
                    - rubi_star(b__ * c__ * n / (Atom::num(2) * f__ * (p + Atom::num(1)))
                            * rubi_simp(&(l1.pow(p) / unit1.pow(p)), x_)
                            * rubi_simp(&(l2.pow(p) / unit2.pow(p)), x_), rubi_rhs_int(&recursive_2, x_))
        },
    ));
}

fn push_rules_rule_6353(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6353,
        source: "Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
          f*(f*x)^(m-1)*(d+e*x^2)^(p+1)*(a+b*ArcCosh[c*x])^n/(e*(m+2*p+1)) +
          f^2*(m-1)/(c^2*(m+2*p+1)) \\[Star] Int[(f*x)^(m-2)*(d+e*x^2)^p*(a+b*ArcCosh[c*x])^n,x] -
          b*f*n/(c*(m+2*p+1))*Simp[(d+e*x^2)^p/((1+c*x)^p*(-1+c*x)^p)] \\[Star]
            Int[(f*x)^(m-1)*(1+c*x)^(p+1/2)*(-1+c*x)^(p+1/2)*(a+b*ArcCosh[c*x])^(n-1),x] /;
        FreeQ[{a,b,c,d,e,f,p},x] && EqQ[c^2*d+e,0] && GtQ[n,0] && IGtQ[m,1] && NeQ[m+2*p+1,0]",
        desc: "Inverted integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [f__, m_, d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [f__, e__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, p_], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && gtq!(n_, 0)
                && igtq!(m_, 1)
                && neq!(&m_ + Atom::num(2) * &p_ + 1, 0)
        },
        rhs: {
            let a__ = &a__;
            let b__ = &b__;
            let c__ = &c__;
            let d__ = &d__;
            let e__ = &e__;
            let f__ = &f__;
            let m = &m_;
            let n = &n_;
            let p = &p_;
            let scaled = f__ * x_;
            let quadratic = d__ + e__ * x_.pow(2);
            let unit1 = Atom::num(1) + c__ * x_;
            let unit2 = -Atom::num(1) + c__ * x_;
            let argument = a__ + b__ * (c__ * x_).acosh();
            let denominator = m + Atom::num(2) * p + 1;
            let recursive_1 = scaled.pow(m - Atom::num(2))
                * quadratic.pow(p)
                * argument.pow(n);
            let recursive_2 = scaled.pow(m - Atom::num(1))
                * unit1.pow(p + Atom::num(1) / Atom::num(2))
                * unit2.pow(p + Atom::num(1) / Atom::num(2))
                * argument.pow(n - Atom::num(1));
            rubi_simp(&(f__ * scaled.pow(m - Atom::num(1))
                    * quadratic.pow(p + Atom::num(1))
                    * argument.pow(n)
                    / (e__ * &denominator)), x_)
                    + rubi_star(f__.pow(2) * (m - Atom::num(1)) / (c__.pow(2) * &denominator), rubi_rhs_int(&recursive_1, x_))
                    - rubi_star(b__ * f__ * n / (c__ * &denominator)
                            * rubi_simp(&(quadratic.pow(p) / (unit1.pow(p) * unit2.pow(p))), x_), rubi_rhs_int(&recursive_2, x_))
        },
    ));
}

fn push_rules_rule_6354(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, f__, d1__, e1__, d2__, e2__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6354,
        source: "Int[(f_.*x_)^m_*(d1_+e1_.*x_)^p_*(d2_+e2_.*x_)^p_*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
          f*(f*x)^(m-1)*(d1+e1*x)^(p+1)*(d2+e2*x)^(p+1)*(a+b*ArcCosh[c*x])^n/(e1*e2*(m+2*p+1)) +
          f^2*(m-1)/(c^2*(m+2*p+1)) \\[Star] Int[(f*x)^(m-2)*(d1+e1*x)^p*(d2+e2*x)^p*(a+b*ArcCosh[c*x])^n,x] -
          b*f*n/(c*(m+2*p+1))*Simp[(d1+e1*x)^p/(1+c*x)^p]*Simp[(d2+e2*x)^p/(-1+c*x)^p] \\[Star]
            Int[(f*x)^(m-1)*(1+c*x)^(p+1/2)*(-1+c*x)^(p+1/2)*(a+b*ArcCosh[c*x])^(n-1),x] /;
        FreeQ[{a,b,c,d1,e1,d2,e2,f,p},x] && EqQ[e1,c*d1] && EqQ[e2,-c*d2] && GtQ[n,0] && IGtQ[m,1] && NeQ[m+2*p+1,0]",
        desc: "Inverted integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [f__, m_, d1__, e1__, p_, d2__, e2__, a__, b__, c__, n_, x_],
        optional: [f__, e1__, e2__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d1__, e1__, d2__, e2__, f__, p_], x_)
                && eqq!(e1__, &c__ * &d1__)
                && eqq!(e2__, -&c__ * &d2__)
                && gtq!(n_, 0)
                && igtq!(m_, 1)
                && neq!(&m_ + Atom::num(2) * &p_ + 1, 0)
        },
        rhs: {
            let a__ = &a__;
            let b__ = &b__;
            let c__ = &c__;
            let d1__ = &d1__;
            let e1__ = &e1__;
            let d2__ = &d2__;
            let e2__ = &e2__;
            let f__ = &f__;
            let m = &m_;
            let n = &n_;
            let p = &p_;
            let scaled = f__ * x_;
            let l1 = d1__ + e1__ * x_;
            let l2 = d2__ + e2__ * x_;
            let unit1 = Atom::num(1) + c__ * x_;
            let unit2 = -Atom::num(1) + c__ * x_;
            let argument = a__ + b__ * (c__ * x_).acosh();
            let denominator = m + Atom::num(2) * p + 1;
            let recursive_1 = scaled.pow(m - Atom::num(2))
                * l1.pow(p)
                * l2.pow(p)
                * argument.pow(n);
            let recursive_2 = scaled.pow(m - Atom::num(1))
                * unit1.pow(p + Atom::num(1) / Atom::num(2))
                * unit2.pow(p + Atom::num(1) / Atom::num(2))
                * argument.pow(n - Atom::num(1));
            rubi_simp(&(f__ * scaled.pow(m - Atom::num(1))
                    * l1.pow(p + Atom::num(1))
                    * l2.pow(p + Atom::num(1))
                    * argument.pow(n)
                    / (e1__ * e2__ * &denominator)), x_)
                    + rubi_star(f__.pow(2) * (m - Atom::num(1)) / (c__.pow(2) * &denominator), rubi_rhs_int(&recursive_1, x_))
                    - rubi_star(b__ * f__ * n / (c__ * &denominator)
                            * rubi_simp(&(l1.pow(p) / unit1.pow(p)), x_)
                            * rubi_simp(&(l2.pow(p) / unit2.pow(p)), x_), rubi_rhs_int(&recursive_2, x_))
        },
    ));
}

fn push_rules_rule_6355(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6355,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCosh[c_.*x_])^n_,x_Symbol] :=
          (f*x)^m*Simp[Sqrt[1+c*x]*Sqrt[-1+c*x]*(d+e*x^2)^p]*(a+b*ArcCosh[c*x])^(n+1)/(b*c*(n+1)) +
          f*m/(b*c*(n+1))*Simp[(d+e*x^2)^p/((1+c*x)^p*(-1+c*x)^p)] \\[Star]
            Int[(f*x)^(m-1)*(1+c*x)^(p-1/2)*(-1+c*x)^(p-1/2)*(a+b*ArcCosh[c*x])^(n+1),x] /;
        FreeQ[{a,b,c,d,e,f,m,p},x] && EqQ[c^2*d+e,0] && LtQ[n,-1] && EqQ[m+2*p+1,0]",
        desc: "Integration by parts and piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [f__, m_, d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [f__, m_, e__, p_, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, p_], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && ltq!(n_, -1)
                && eqq!(&m_ + Atom::num(2) * &p_ + 1, 0)
        },
        rhs: {
            let a__ = &a__;
            let b__ = &b__;
            let c__ = &c__;
            let d__ = &d__;
            let e__ = &e__;
            let f__ = &f__;
            let m = &m_;
            let n = &n_;
            let p = &p_;
            let scaled = f__ * x_;
            let quadratic = d__ + e__ * x_.pow(2);
            let unit1 = Atom::num(1) + c__ * x_;
            let unit2 = -Atom::num(1) + c__ * x_;
            let argument = a__ + b__ * (c__ * x_).acosh();
            let common = rubi_simp(
                &(quadratic.pow(p) / (unit1.pow(p) * unit2.pow(p))),
                x_,
            );
            let recursive = scaled.pow(m - Atom::num(1))
                * unit1.pow(p - Atom::num(1) / Atom::num(2))
                * unit2.pow(p - Atom::num(1) / Atom::num(2))
                * argument.pow(n + Atom::num(1));
            rubi_simp(&(scaled.pow(m)
                    * rubi_simp(&(unit1.sqrt() * unit2.sqrt() * quadratic.pow(p)), x_)
                    * argument.pow(n + Atom::num(1))
                    / (b__ * c__ * (n + Atom::num(1)))), x_)
                    + rubi_star(f__ * m / (b__ * c__ * (n + Atom::num(1))) * common, rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_6356(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, f__, d1__, e1__, d2__, e2__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6356,
        source: "Int[(f_.*x_)^m_.*(d1_+e1_.*x_)^p_*(d2_+e2_.*x_)^p_*(a_.+b_.*ArcCosh[c_.*x_])^n_,x_Symbol] :=
          (f*x)^m*Simp[Sqrt[1+c*x]*Sqrt[-1+c*x]*(d1+e1*x)^p]*(d2+e2*x)^p*(a+b*ArcCosh[c*x])^(n+1)/(b*c*(n+1)) +
          f*m/(b*c*(n+1))*Simp[(d1+e1*x)^p/(1+c*x)^p]*Simp[(d2+e2*x)^p/(-1+c*x)^p] \\[Star]
            Int[(f*x)^(m-1)*(1+c*x)^(p-1/2)*(-1+c*x)^(p-1/2)*(a+b*ArcCosh[c*x])^(n+1),x] /;
        FreeQ[{a,b,c,d1,e1,d2,e2,f,m,p},x] && EqQ[e1,c*d1] && EqQ[e2,-c*d2] && LtQ[n,-1] && EqQ[m+2*p+1,0]",
        desc: "Integration by parts and piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [f__, m_, d1__, e1__, p_, d2__, e2__, a__, b__, c__, n_, x_],
        optional: [f__, m_, e1__, e2__, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d1__, e1__, d2__, e2__, f__, m_, p_], x_)
                && eqq!(e1__, &c__ * &d1__)
                && eqq!(e2__, -&c__ * &d2__)
                && ltq!(n_, -1)
                && eqq!(&m_ + Atom::num(2) * &p_ + 1, 0)
        },
        rhs: {
            let a__ = &a__;
            let b__ = &b__;
            let c__ = &c__;
            let d1__ = &d1__;
            let e1__ = &e1__;
            let d2__ = &d2__;
            let e2__ = &e2__;
            let f__ = &f__;
            let m = &m_;
            let n = &n_;
            let p = &p_;
            let scaled = f__ * x_;
            let l1 = d1__ + e1__ * x_;
            let l2 = d2__ + e2__ * x_;
            let unit1 = Atom::num(1) + c__ * x_;
            let unit2 = -Atom::num(1) + c__ * x_;
            let argument = a__ + b__ * (c__ * x_).acosh();
            let common = rubi_simp(&(l1.pow(p) / unit1.pow(p)), x_)
                * rubi_simp(&(l2.pow(p) / unit2.pow(p)), x_);
            let recursive = scaled.pow(m - Atom::num(1))
                * unit1.pow(p - Atom::num(1) / Atom::num(2))
                * unit2.pow(p - Atom::num(1) / Atom::num(2))
                * argument.pow(n + Atom::num(1));
            rubi_simp(&(scaled.pow(m)
                    * rubi_simp(&(unit1.sqrt() * unit2.sqrt() * l1.pow(p)), x_)
                    * l2.pow(p)
                    * argument.pow(n + Atom::num(1))
                    / (b__ * c__ * (n + Atom::num(1)))), x_)
                    + rubi_star(f__ * m / (b__ * c__ * (n + Atom::num(1))) * common, rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_6357(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6357,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCosh[c_.*x_])^n_,x_Symbol] :=
          (f*x)^m*Simp[Sqrt[1+c*x]*Sqrt[-1+c*x]*(d+e*x^2)^p]*(a+b*ArcCosh[c*x])^(n+1)/(b*c*(n+1)) +
          f*m/(b*c*(n+1))*Simp[(d+e*x^2)^p/((1+c*x)^p*(-1+c*x)^p)] \\[Star]
            Int[(f*x)^(m-1)*(1+c*x)^(p-1/2)*(-1+c*x)^(p-1/2)*(a+b*ArcCosh[c*x])^(n+1),x] -
          c*(m+2*p+1)/(b*f*(n+1))*Simp[(d+e*x^2)^p/((1+c*x)^p*(-1+c*x)^p)] \\[Star]
            Int[(f*x)^(m+1)*(1+c*x)^(p-1/2)*(-1+c*x)^(p-1/2)*(a+b*ArcCosh[c*x])^(n+1),x] /;
        FreeQ[{a,b,c,d,e,f,m,p},x] && EqQ[c^2*d+e,0] && LtQ[n,-1] && IGtQ[2*p,0] && NeQ[m+2*p+1,0] && IGtQ[m,-3]",
        desc: "Integration by parts and piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [f__, m_, d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [f__, m_, e__, p_, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, p_], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && ltq!(n_, -1)
                && igtq!(Atom::num(2) * &p_, 0)
                && neq!(&m_ + Atom::num(2) * &p_ + 1, 0)
                && igtq!(m_, -3)
        },
        rhs: {
            let a__ = &a__;
            let b__ = &b__;
            let c__ = &c__;
            let d__ = &d__;
            let e__ = &e__;
            let f__ = &f__;
            let m = &m_;
            let n = &n_;
            let p = &p_;
            let scaled = f__ * x_;
            let quadratic = d__ + e__ * x_.pow(2);
            let unit1 = Atom::num(1) + c__ * x_;
            let unit2 = -Atom::num(1) + c__ * x_;
            let argument = a__ + b__ * (c__ * x_).acosh();
            let common_1 = rubi_simp(
                &(quadratic.pow(p) / (unit1.pow(p) * unit2.pow(p))),
                x_,
            );
            let common_2 = rubi_simp(
                &(quadratic.pow(p) / (unit1.pow(p) * unit2.pow(p))),
                x_,
            );
            let recursive_1 = scaled.pow(m - Atom::num(1))
                * unit1.pow(p - Atom::num(1) / Atom::num(2))
                * unit2.pow(p - Atom::num(1) / Atom::num(2))
                * argument.pow(n + Atom::num(1));
            let recursive_2 = scaled.pow(m + Atom::num(1))
                * unit1.pow(p - Atom::num(1) / Atom::num(2))
                * unit2.pow(p - Atom::num(1) / Atom::num(2))
                * argument.pow(n + Atom::num(1));
            rubi_simp(&(scaled.pow(m)
                    * rubi_simp(&(unit1.sqrt() * unit2.sqrt() * quadratic.pow(p)), x_)
                    * argument.pow(n + Atom::num(1))
                    / (b__ * c__ * (n + Atom::num(1)))), x_)
                    + rubi_star(f__ * m / (b__ * c__ * (n + Atom::num(1))) * common_1, rubi_rhs_int(&recursive_1, x_))
                    - rubi_star(c__ * (m + Atom::num(2) * p + 1) / (b__ * f__ * (n + Atom::num(1)))
                            * common_2, rubi_rhs_int(&recursive_2, x_))
        },
    ));
}

fn push_rules_rule_6358(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, f__, d1__, e1__, d2__, e2__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6358,
        source: "Int[(f_.*x_)^m_.*(d1_+e1_.*x_)^p_*(d2_+e2_.*x_)^p_*(a_.+b_.*ArcCosh[c_.*x_])^n_,x_Symbol] :=
          (f*x)^m*Sqrt[1+c*x]*Sqrt[-1+c*x]*(d1+e1*x)^p*(d2+e2*x)^p*(a+b*ArcCosh[c*x])^(n+1)/(b*c*(n+1)) +
          f*m/(b*c*(n+1))*Simp[(d1+e1*x)^p/(1+c*x)^p]*Simp[(d2+e2*x)^p/(-1+c*x)^p] \\[Star]
            Int[(f*x)^(m-1)*(-1+c^2*x^2)^(p-1/2)*(a+b*ArcCosh[c*x])^(n+1),x] -
          c*(m+2*p+1)/(b*f*(n+1))*Simp[(d1+e1*x)^p/(1+c*x)^p]*Simp[(d2+e2*x)^p/(-1+c*x)^p] \\[Star]
            Int[(f*x)^(m+1)*(-1+c^2*x^2)^(p-1/2)*(a+b*ArcCosh[c*x])^(n+1),x] /;
        FreeQ[{a,b,c,d1,e1,d2,e2,f,m,p},x] && EqQ[e1,c*d1] && EqQ[e2,-c*d2] && LtQ[n,-1] && IGtQ[p+1/2,0] && NeQ[m+2*p+1,0] && IGtQ[m,-3]",
        desc: "Integration by parts and piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [f__, m_, d1__, e1__, p_, d2__, e2__, a__, b__, c__, n_, x_],
        optional: [f__, m_, e1__, e2__, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d1__, e1__, d2__, e2__, f__, m_, p_], x_)
                && eqq!(e1__, &c__ * &d1__)
                && eqq!(e2__, -&c__ * &d2__)
                && ltq!(n_, -1)
                && igtq!(&p_ + Atom::num(1) / Atom::num(2), 0)
                && neq!(&m_ + Atom::num(2) * &p_ + 1, 0)
                && igtq!(m_, -3)
        },
        rhs: {
            let a__ = &a__;
            let b__ = &b__;
            let c__ = &c__;
            let d1__ = &d1__;
            let e1__ = &e1__;
            let d2__ = &d2__;
            let e2__ = &e2__;
            let f__ = &f__;
            let m = &m_;
            let n = &n_;
            let p = &p_;
            let scaled = f__ * x_;
            let l1 = d1__ + e1__ * x_;
            let l2 = d2__ + e2__ * x_;
            let unit1 = Atom::num(1) + c__ * x_;
            let unit2 = -Atom::num(1) + c__ * x_;
            let argument = a__ + b__ * (c__ * x_).acosh();
            let common_1 = rubi_simp(&(l1.pow(p) / unit1.pow(p)), x_)
                * rubi_simp(&(l2.pow(p) / unit2.pow(p)), x_);
            let common_2 = rubi_simp(&(l1.pow(p) / unit1.pow(p)), x_)
                * rubi_simp(&(l2.pow(p) / unit2.pow(p)), x_);
            let kernel =
                (-Atom::num(1) + c__.pow(2) * x_.pow(2)).pow(p - Atom::num(1) / Atom::num(2));
            let recursive_1 = scaled.pow(m - Atom::num(1))
                * &kernel
                * argument.pow(n + Atom::num(1));
            let recursive_2 =
                scaled.pow(m + Atom::num(1)) * kernel * argument.pow(n + Atom::num(1));
            rubi_simp(&(scaled.pow(m)
                    * (Atom::num(1) + c__ * x_).sqrt()
                    * (-Atom::num(1) + c__ * x_).sqrt()
                    * l1.pow(p)
                    * l2.pow(p)
                    * argument.pow(n + Atom::num(1))
                    / (b__ * c__ * (n + Atom::num(1)))), x_)
                    + rubi_star(f__ * m / (b__ * c__ * (n + Atom::num(1))) * common_1, rubi_rhs_int(&recursive_1, x_))
                    - rubi_star(c__ * (m + Atom::num(2) * p + 1) / (b__ * f__ * (n + Atom::num(1)))
                            * common_2, rubi_rhs_int(&recursive_2, x_))
        },
    ));
}

fn push_rules_rule_6359(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 6359,
        source: "Int[(f_.*x_)^m_*(a_.+b_.*ArcCosh[c_.*x_])^n_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
          f*(f*x)^(m-1)*Sqrt[d+e*x^2]*(a+b*ArcCosh[c*x])^n/(e*m) -
          b*f*n/(c*m)*Simp[Sqrt[1+c*x]*Sqrt[-1+c*x]/Sqrt[d+e*x^2]] \\[Star] Int[(f*x)^(m-1)*(a+b*ArcCosh[c*x])^(n-1),x] +
          f^2*(m-1)/(c^2*m) \\[Star] Int[(f*x)^(m-2)*(a+b*ArcCosh[c*x])^n/Sqrt[d+e*x^2],x] /;
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
            let a__ = &a__;
            let b__ = &b__;
            let c__ = &c__;
            let d__ = &d__;
            let e__ = &e__;
            let f__ = &f__;
            let m = &m_;
            let n = &n_;
            let scaled = f__ * x_;
            let quadratic = d__ + e__ * x_.pow(2);
            let unit1 = Atom::num(1) + c__ * x_;
            let unit2 = -Atom::num(1) + c__ * x_;
            let argument = a__ + b__ * (c__ * x_).acosh();
            let ratio = rubi_simp(&(unit1.sqrt() * unit2.sqrt() / &quadratic.sqrt()), x_);
            let recursive_1 =
                scaled.pow(m - Atom::num(1)) * argument.pow(n - Atom::num(1));
            let recursive_2 = scaled.pow(m - Atom::num(2)) * argument.pow(n)
                / &quadratic.sqrt();
            rubi_simp(&(f__ * scaled.pow(m - Atom::num(1)) * quadratic.sqrt() * argument.pow(n) / (e__ * m)), x_)
                    - rubi_star(b__ * f__ * n / (c__ * m) * ratio, rubi_rhs_int(&recursive_1, x_))
                    + rubi_star(f__.pow(2) * (m - Atom::num(1)) / (c__.pow(2) * m), rubi_rhs_int(&recursive_2, x_))
        },
    ));
}

fn push_rules_rule_6360(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, f__, d1__, e1__, d2__, e2__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 6360,
        source: "Int[(f_.*x_)^m_*(a_.+b_.*ArcCosh[c_.*x_])^n_./(Sqrt[d1_+e1_.*x_]*Sqrt[d2_+e2_.*x_]),x_Symbol] :=
          f*(f*x)^(m-1)*Sqrt[d1+e1*x]*Sqrt[d2+e2*x]*(a+b*ArcCosh[c*x])^n/(e1*e2*m) -
          b*f*n/(c*m)*Simp[Sqrt[1+c*x]/Sqrt[d1+e1*x]]*Simp[Sqrt[-1+c*x]/Sqrt[d2+e2*x]] \\[Star]
            Int[(f*x)^(m-1)*(a+b*ArcCosh[c*x])^(n-1),x] +
          f^2*(m-1)/(c^2*m) \\[Star] Int[(f*x)^(m-2)*(a+b*ArcCosh[c*x])^n/(Sqrt[d1+e1*x]*Sqrt[d2+e2*x]),x] /;
        FreeQ[{a,b,c,d1,e1,d2,e2,f},x] && EqQ[e1,c*d1] && EqQ[e2,-c*d2] && GtQ[n,0] && IGtQ[m,1]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [f__, m_, a__, b__, c__, n_, d1__, e1__, d2__, e2__, x_],
        optional: [f__, a__, b__, c__, n_, e1__, e2__],
        when: {
            freeq!([a__, b__, c__, d1__, e1__, d2__, e2__, f__], x_)
                && eqq!(e1__, &c__ * &d1__)
                && eqq!(e2__, -&c__ * &d2__)
                && gtq!(n_, 0)
                && igtq!(m_, 1)
        },
        rhs: {
            let a__ = &a__;
            let b__ = &b__;
            let c__ = &c__;
            let d1__ = &d1__;
            let e1__ = &e1__;
            let d2__ = &d2__;
            let e2__ = &e2__;
            let f__ = &f__;
            let m = &m_;
            let n = &n_;
            let scaled = f__ * x_;
            let l1 = d1__ + e1__ * x_;
            let l2 = d2__ + e2__ * x_;
            let unit1 = Atom::num(1) + c__ * x_;
            let unit2 = -Atom::num(1) + c__ * x_;
            let argument = a__ + b__ * (c__ * x_).acosh();
            let ratio = rubi_simp(&(unit1.sqrt() / &l1.sqrt()), x_)
                * rubi_simp(&(unit2.sqrt() / &l2.sqrt()), x_);
            let recursive_1 =
                scaled.pow(m - Atom::num(1)) * argument.pow(n - Atom::num(1));
            let recursive_2 = scaled.pow(m - Atom::num(2)) * argument.pow(n)
                / (&l1.sqrt() * &l2.sqrt());
            rubi_simp(&(f__ * scaled.pow(m - Atom::num(1)) * l1.sqrt() * l2.sqrt() * argument.pow(n)
                    / (e1__ * e2__ * m)), x_)
                    - rubi_star(b__ * f__ * n / (c__ * m) * ratio, rubi_rhs_int(&recursive_1, x_))
                    + rubi_star(f__.pow(2) * (m - Atom::num(1)) / (c__.pow(2) * m), rubi_rhs_int(&recursive_2, x_))
        },
    ));
}

fn push_rules_rule_6361(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 6361,
        source: "Int[x_^m_*(a_.+b_.*ArcCosh[c_.*x_])^n_./Sqrt[d_+e_.*x_^2],x_Symbol] :=
          1/c^(m+1)*Simp[Sqrt[1+c*x]*Sqrt[-1+c*x]/Sqrt[d+e*x^2]] \\[Star]
            Subst[Int[(a+b*x)^n*Cosh[x]^m,x],x,ArcCosh[c*x]] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[c^2*d+e,0] && IGtQ[n,0] && IntegerQ[m]",
        desc: "Piecewise constant extraction and integration by substitution",
        refs: [],
        pattern: x_.pow(m_) * (a__ + b__ * (c__ * x_).acosh()).pow(n_) / (d__ + e__ * x_.pow(2)).sqrt(),
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
            let payload = (&a__ + &b__ * &sub_atom).pow(&n_) * sub_atom.cosh().pow(&m_);
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            let ratio = rubi_simp(
                &((Atom::num(1) + &c__ * x_).sqrt() * (-Atom::num(1) + &c__ * x_).sqrt()
                    / (&d__ + &e__ * x_.pow(2)).sqrt()),
                x_,
            );
            let substituted = rubi_subst(&primitive, substitution_symbol, (&c__ * x_).acosh());
            rubi_star(ratio / c__.pow(&m_ + Atom::num(1)), substituted)
        },
    ));
}

fn push_rules_rule_6362(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d1__, e1__, d2__, e2__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 6362,
        source: "Int[x_^m_*(a_.+b_.*ArcCosh[c_.*x_])^n_./(Sqrt[d1_+e1_.*x_]*Sqrt[d2_+e2_.*x_]),x_Symbol] :=
          1/c^(m+1)*Simp[Sqrt[1+c*x]/Sqrt[d1+e1*x]]*Simp[Sqrt[-1+c*x]/Sqrt[d2+e2*x]] \\[Star]
            Subst[Int[(a+b*x)^n*Cosh[x]^m,x],x,ArcCosh[c*x]] /;
        FreeQ[{a,b,c,d1,e1,d2,e2},x] && EqQ[e1,c*d1] && EqQ[e2,-c*d2] && IGtQ[n,0] && IntegerQ[m]",
        desc: "Piecewise constant extraction and integration by substitution",
        refs: [],
        pattern: x_.pow(m_) * (a__ + b__ * (c__ * x_).acosh()).pow(n_) / ((d1__ + e1__ * x_).sqrt() * (d2__ + e2__ * x_).sqrt()),
        with: [m_, a__, b__, c__, n_, d1__, e1__, d2__, e2__, x_],
        optional: [a__, b__, c__, n_, e1__, e2__],
        when: {
            freeq!([a__, b__, c__, d1__, e1__, d2__, e2__], x_)
                && eqq!(e1__, &c__ * &d1__)
                && eqq!(e2__, -&c__ * &d2__)
                && igtq!(n_, 0)
                && integerq!(m_)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let payload = (&a__ + &b__ * &sub_atom).pow(&n_) * sub_atom.cosh().pow(&m_);
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            let ratio = rubi_simp(
                &((Atom::num(1) + &c__ * x_).sqrt() / (&d1__ + &e1__ * x_).sqrt()),
                x_,
            ) * rubi_simp(
                &((-Atom::num(1) + &c__ * x_).sqrt() / (&d2__ + &e2__ * x_).sqrt()),
                x_,
            );
            let substituted = rubi_subst(&primitive, substitution_symbol, (&c__ * x_).acosh());
            rubi_star(ratio / c__.pow(&m_ + Atom::num(1)), substituted)
        },
    ));
}

fn push_rules_rule_6363(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, x_);
    rules.push(rubi_rule!(
        order: 6363,
        source: "Int[(f_.*x_)^m_*(a_.+b_.*ArcCosh[c_.*x_])/Sqrt[d_+e_.*x_^2],x_Symbol] :=
          (f*x)^(m+1)/(f*(m+1))*Simp[Sqrt[1-c^2*x^2]/Sqrt[d+e*x^2]]*
            (a+b*ArcCosh[c*x])*Hypergeometric2F1[1/2,(1+m)/2,(3+m)/2,c^2*x^2] +
          b*c*(f*x)^(m+2)/(f^2*(m+1)*(m+2))*Simp[Sqrt[1+c*x]*Sqrt[-1+c*x]/Sqrt[d+e*x^2]]*
            HypergeometricPFQ[{1,1+m/2,1+m/2},{3/2+m/2,2+m/2},c^2*x^2] /;
        FreeQ[{a,b,c,d,e,f,m},x] && EqQ[c^2*d+e,0] && Not[IntegerQ[m]]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern: (f__ * x_).pow(m_) * (a__ + b__ * (c__ * x_).acosh()) / (d__ + e__ * x_.pow(2)).sqrt(),
        with: [f__, m_, a__, b__, c__, d__, e__, x_],
        optional: [f__, a__, b__, c__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && !integerq!(m_)
        },
        rhs: {
            let a__ = &a__;
            let b__ = &b__;
            let c__ = &c__;
            let d__ = &d__;
            let e__ = &e__;
            let f__ = &f__;
            let m = &m_;
            let scaled = f__ * x_;
            let z = c__.pow(2) * x_.pow(2);
            let ratio1 = rubi_simp(
                &((Atom::num(1) - c__.pow(2) * x_.pow(2)).sqrt()
                    / (d__ + e__ * x_.pow(2)).sqrt()),
                x_,
            );
            let ratio2 = rubi_simp(
                &((Atom::num(1) + c__ * x_).sqrt() * (-Atom::num(1) + c__ * x_).sqrt()
                    / (d__ + e__ * x_.pow(2)).sqrt()),
                x_,
            );
            rubi_simp(&(scaled.pow(m + Atom::num(1)) / (f__ * (m + Atom::num(1)))
                    * ratio1
                    * (a__ + b__ * (c__ * x_).acosh())
                    * rubi_hypergeometric2f1(
                        Atom::num(1) / Atom::num(2),
                        (Atom::num(1) + m) / Atom::num(2),
                        (Atom::num(3) + m) / Atom::num(2),
                        &z,
                    )), x_)
                    + rubi_simp(&(b__ * c__ * scaled.pow(m + Atom::num(2))
                        / (f__.pow(2) * (m + Atom::num(1)) * (m + Atom::num(2)))
                        * ratio2
                        * rubi_hypergeometric_pfq_3_2(
                            Atom::num(1),
                            Atom::num(1) + m / Atom::num(2),
                            Atom::num(1) + m / Atom::num(2),
                            Atom::num(3) / Atom::num(2) + m / Atom::num(2),
                            Atom::num(2) + m / Atom::num(2),
                            z,
                        )), x_)
        },
    ));
}

fn push_rules_rule_6364(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, f__, d1__, e1__, d2__, e2__, m_, x_);
    rules.push(rubi_rule!(
        order: 6364,
        source: "Int[(f_.*x_)^m_*(a_.+b_.*ArcCosh[c_.*x_])/(Sqrt[d1_+e1_.*x_]*Sqrt[d2_+e2_.*x_]),x_Symbol] :=
          (f*x)^(m+1)/(f*(m+1))*Simp[Sqrt[1-c^2*x^2]/(Sqrt[d1+e1*x]*Sqrt[d2+e2*x])]*
            (a+b*ArcCosh[c*x])*Hypergeometric2F1[1/2,(1+m)/2,(3+m)/2,c^2*x^2] +
          b*c*(f*x)^(m+2)/(f^2*(m+1)*(m+2))*Simp[Sqrt[1+c*x]/Sqrt[d1+e1*x]]*Simp[Sqrt[-1+c*x]/Sqrt[d2+e2*x]]*
            HypergeometricPFQ[{1,1+m/2,1+m/2},{3/2+m/2,2+m/2},c^2*x^2] /;
        FreeQ[{a,b,c,d1,e1,d2,e2,f,m},x] && EqQ[e1,c*d1] && EqQ[e2,-c*d2] && Not[IntegerQ[m]]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern: (f__ * x_).pow(m_) * (a__ + b__ * (c__ * x_).acosh()) / ((d1__ + e1__ * x_).sqrt() * (d2__ + e2__ * x_).sqrt()),
        with: [f__, m_, a__, b__, c__, d1__, e1__, d2__, e2__, x_],
        optional: [f__, a__, b__, c__, e1__, e2__],
        when: {
            freeq!([a__, b__, c__, d1__, e1__, d2__, e2__, f__, m_], x_)
                && eqq!(e1__, &c__ * &d1__)
                && eqq!(e2__, -&c__ * &d2__)
                && !integerq!(m_)
        },
        rhs: {
            let a__ = &a__;
            let b__ = &b__;
            let c__ = &c__;
            let d1__ = &d1__;
            let e1__ = &e1__;
            let d2__ = &d2__;
            let e2__ = &e2__;
            let f__ = &f__;
            let m = &m_;
            let scaled = f__ * x_;
            let l1 = d1__ + e1__ * x_;
            let l2 = d2__ + e2__ * x_;
            let z = c__.pow(2) * x_.pow(2);
            let ratio1 = rubi_simp(
                &((Atom::num(1) - c__.pow(2) * x_.pow(2)).sqrt()
                    / (&l1.sqrt() * &l2.sqrt())),
                x_,
            );
            let ratio2 = rubi_simp(&((Atom::num(1) + c__ * x_).sqrt() / l1.sqrt()), x_)
                * rubi_simp(&((-Atom::num(1) + c__ * x_).sqrt() / l2.sqrt()), x_);
            rubi_simp(&(scaled.pow(m + Atom::num(1)) / (f__ * (m + Atom::num(1)))
                    * ratio1
                    * (a__ + b__ * (c__ * x_).acosh())
                    * rubi_hypergeometric2f1(
                        Atom::num(1) / Atom::num(2),
                        (Atom::num(1) + m) / Atom::num(2),
                        (Atom::num(3) + m) / Atom::num(2),
                        &z,
                    )), x_)
                    + rubi_simp(&(b__ * c__ * scaled.pow(m + Atom::num(2))
                        / (f__.pow(2) * (m + Atom::num(1)) * (m + Atom::num(2)))
                        * ratio2
                        * rubi_hypergeometric_pfq_3_2(
                            Atom::num(1),
                            Atom::num(1) + m / Atom::num(2),
                            Atom::num(1) + m / Atom::num(2),
                            Atom::num(3) / Atom::num(2) + m / Atom::num(2),
                            Atom::num(2) + m / Atom::num(2),
                            z,
                        )), x_)
        },
    ));
}

fn push_rules_rule_6365(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 6365,
        source: "Int[(f_.*x_)^m_.*(a_.+b_.*ArcCosh[c_.*x_])^n_/Sqrt[d_+e_.*x_^2],x_Symbol] :=
          (f*x)^m*(a+b*ArcCosh[c*x])^(n+1)/(b*c*(n+1))*Simp[Sqrt[1+c*x]*Sqrt[-1+c*x]/Sqrt[d+e*x^2]] -
          f*m/(b*c*(n+1))*Simp[Sqrt[1+c*x]*Sqrt[-1+c*x]/Sqrt[d+e*x^2]] \\[Star] Int[(f*x)^(m-1)*(a+b*ArcCosh[c*x])^(n+1),x] /;
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
            let a__ = &a__;
            let b__ = &b__;
            let c__ = &c__;
            let d__ = &d__;
            let e__ = &e__;
            let f__ = &f__;
            let m = &m_;
            let n = &n_;
            let scaled = f__ * x_;
            let argument = a__ + b__ * (c__ * x_).acosh();
            let ratio_1 = rubi_simp(
                &((Atom::num(1) + c__ * x_).sqrt() * (-Atom::num(1) + c__ * x_).sqrt()
                    / (d__ + e__ * x_.pow(2)).sqrt()),
                x_,
            );
            let ratio_2 = rubi_simp(
                &((Atom::num(1) + c__ * x_).sqrt() * (-Atom::num(1) + c__ * x_).sqrt()
                    / (d__ + e__ * x_.pow(2)).sqrt()),
                x_,
            );
            let recursive =
                scaled.pow(m - Atom::num(1)) * argument.pow(n + Atom::num(1));
            rubi_simp(&(scaled.pow(m) * argument.pow(n + Atom::num(1)) / (b__ * c__ * (n + Atom::num(1)))
                    * ratio_1), x_)
                    - rubi_star(f__ * m / (b__ * c__ * (n + Atom::num(1))) * ratio_2, rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_6366(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, f__, d1__, e1__, d2__, e2__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 6366,
        source: "Int[(f_.*x_)^m_.*(a_.+b_.*ArcCosh[c_.*x_])^n_/(Sqrt[d1_+e1_.*x_]*Sqrt[d2_+e2_.*x_]),x_Symbol] :=
          (f*x)^m*(a+b*ArcCosh[c*x])^(n+1)/(b*c*(n+1))*Simp[Sqrt[1+c*x]/Sqrt[d1+e1*x]]*Simp[Sqrt[-1+c*x]/Sqrt[d2+e2*x]] -
          f*m/(b*c*(n+1))*Simp[Sqrt[1+c*x]/Sqrt[d1+e1*x]]*Simp[Sqrt[-1+c*x]/Sqrt[d2+e2*x]] \\[Star]
            Int[(f*x)^(m-1)*(a+b*ArcCosh[c*x])^(n+1),x] /;
        FreeQ[{a,b,c,d1,e1,d2,e2,f,m},x] && EqQ[e1,c*d1] && EqQ[e2,-c*d2] && LtQ[n,-1]",
        desc: "Integration by parts and piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [f__, m_, a__, b__, c__, n_, d1__, e1__, d2__, e2__, x_],
        optional: [f__, m_, a__, b__, c__, e1__, e2__],
        when: {
            freeq!([a__, b__, c__, d1__, e1__, d2__, e2__, f__, m_], x_)
                && eqq!(e1__, &c__ * &d1__)
                && eqq!(e2__, -&c__ * &d2__)
                && ltq!(n_, -1)
        },
        rhs: {
            let a__ = &a__;
            let b__ = &b__;
            let c__ = &c__;
            let d1__ = &d1__;
            let e1__ = &e1__;
            let d2__ = &d2__;
            let e2__ = &e2__;
            let f__ = &f__;
            let m = &m_;
            let n = &n_;
            let scaled = f__ * x_;
            let l1 = d1__ + e1__ * x_;
            let l2 = d2__ + e2__ * x_;
            let argument = a__ + b__ * (c__ * x_).acosh();
            let ratio_1 = rubi_simp(&((Atom::num(1) + c__ * x_).sqrt() / l1.sqrt()), x_)
                * rubi_simp(&((-Atom::num(1) + c__ * x_).sqrt() / l2.sqrt()), x_);
            let ratio_2 = rubi_simp(&((Atom::num(1) + c__ * x_).sqrt() / l1.sqrt()), x_)
                * rubi_simp(&((-Atom::num(1) + c__ * x_).sqrt() / l2.sqrt()), x_);
            let recursive =
                scaled.pow(m - Atom::num(1)) * argument.pow(n + Atom::num(1));
            rubi_simp(&(scaled.pow(m) * argument.pow(n + Atom::num(1)) / (b__ * c__ * (n + Atom::num(1)))
                    * ratio_1), x_)
                    - rubi_star(f__ * m / (b__ * c__ * (n + Atom::num(1))) * ratio_2, rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_6367(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6367,
        source: "Int[x_^m_.*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
          1/(b*c^(m+1))*Simp[(d+e*x^2)^p/((1+c*x)^p*(-1+c*x)^p)] \\[Star]
            Subst[Int[x^n*Cosh[-a/b+x/b]^m*Sinh[-a/b+x/b]^(2*p+1),x],x,a+b*ArcCosh[c*x]] /;
        FreeQ[{a,b,c,d,e,n},x] && EqQ[c^2*d+e,0] && IGtQ[2*p+2,0] && IGtQ[m,0]",
        desc: "Piecewise constant extraction and integration by substitution",
        refs: [],
        pattern: x_.pow(m_) * (d__ + e__ * x_.pow(2)).pow(p_) * (a__ + b__ * (c__ * x_).acosh()).pow(n_),
        with: [m_, d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [m_, e__, p_, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, n_], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && igtq!(Atom::num(2) * &p_ + 2, 0)
                && igtq!(m_, 0)
        },
        rhs: {
            let a__ = &a__;
            let b__ = &b__;
            let c__ = &c__;
            let d__ = &d__;
            let e__ = &e__;
            let m = &m_;
            let n = &n_;
            let p = &p_;
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let hyper_arg = -a__ / b__ + &sub_atom / b__;
            let payload = sub_atom.pow(n)
                * &hyper_arg.cosh().pow(m)
                * hyper_arg.sinh().pow(Atom::num(2) * p + 1);
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            let unit1 = Atom::num(1) + c__ * x_;
            let unit2 = -Atom::num(1) + c__ * x_;
            let substituted = rubi_subst(
                &primitive,
                substitution_symbol,
                a__ + b__ * (c__ * x_).acosh(),
            );
            let coefficient = rubi_simp(
                &((d__ + e__ * x_.pow(2)).pow(p) / (unit1.pow(p) * unit2.pow(p))),
                x_,
            ) / (b__ * c__.pow(m + Atom::num(1)));
            rubi_star(coefficient, substituted)
        },
    ));
}

fn push_rules_rule_6368(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d1__, e1__, d2__, e2__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6368,
        source: "Int[x_^m_.*(d1_+e1_.*x_)^p_.*(d2_+e2_.*x_)^p_.*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
          1/(b*c^(m+1))*Simp[(d1+e1*x)^p/(1+c*x)^p]*Simp[(d2+e2*x)^p/(-1+c*x)^p] \\[Star]
            Subst[Int[x^n*Cosh[-a/b+x/b]^m*Sinh[-a/b+x/b]^(2*p+1),x],x,a+b*ArcCosh[c*x]] /;
        FreeQ[{a,b,c,d1,e1,d2,e2,n},x] && EqQ[e1,c*d1] && EqQ[e2,-c*d2] && IGtQ[p+3/2,0] && IGtQ[m,0]",
        desc: "Piecewise constant extraction and integration by substitution",
        refs: [],
        pattern: x_.pow(m_) * (d1__ + e1__ * x_).pow(p_) * (d2__ + e2__ * x_).pow(p_) * (a__ + b__ * (c__ * x_).acosh()).pow(n_),
        with: [m_, d1__, e1__, p_, d2__, e2__, a__, b__, c__, n_, x_],
        optional: [m_, e1__, p_, e2__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d1__, e1__, d2__, e2__, n_], x_)
                && eqq!(e1__, &c__ * &d1__)
                && eqq!(e2__, -&c__ * &d2__)
                && igtq!(&p_ + Atom::num(3) / Atom::num(2), 0)
                && igtq!(m_, 0)
        },
        rhs: {
            let a__ = &a__;
            let b__ = &b__;
            let c__ = &c__;
            let d1__ = &d1__;
            let e1__ = &e1__;
            let d2__ = &d2__;
            let e2__ = &e2__;
            let m = &m_;
            let n = &n_;
            let p = &p_;
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let hyper_arg = -a__ / b__ + &sub_atom / b__;
            let payload = sub_atom.pow(n)
                * &hyper_arg.cosh().pow(m)
                * hyper_arg.sinh().pow(Atom::num(2) * p + 1);
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            let unit1 = Atom::num(1) + c__ * x_;
            let unit2 = -Atom::num(1) + c__ * x_;
            let l1 = d1__ + e1__ * x_;
            let l2 = d2__ + e2__ * x_;
            let substituted = rubi_subst(
                &primitive,
                substitution_symbol,
                a__ + b__ * (c__ * x_).acosh(),
            );
            let coefficient = rubi_simp(&(l1.pow(p) / unit1.pow(p)), x_)
                * rubi_simp(&(l2.pow(p) / unit2.pow(p)), x_)
                / (b__ * c__.pow(m + Atom::num(1)));
            rubi_star(coefficient, substituted)
        },
    ));
}

fn push_rules_rule_6369(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6369,
        source: "Int[(f_.*x_)^m_*(d_+e_.*x_^2)^p_*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
          Int[ExpandIntegrand[(a+b*ArcCosh[c*x])^n/Sqrt[d+e*x^2],(f*x)^m*(d+e*x^2)^(p+1/2),x],x] /;
        FreeQ[{a,b,c,d,e,f,m,n},x] && EqQ[c^2*d+e,0] && IGtQ[p+1/2,0] && Not[IGtQ[(m+1)/2,0]] && (EqQ[m,-1] || EqQ[m,-2])",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [f__, m_, d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [f__, e__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_], x_)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && igtq!(&p_ + Atom::num(1) / Atom::num(2), 0)
                && !igtq!((&m_ + Atom::num(1)) / Atom::num(2), 0)
                && (eqq!(m_, -1) || eqq!(m_, -2))
        },
        rhs: {
            let quadratic_x = &d__ + &e__ * x_.pow(2);
            let argument = &a__ + &b__ * (&c__ * x_).acosh();
            let u = argument.pow(&n_) / &quadratic_x.sqrt();
            let v = (&f__ * x_).pow(&m_) * quadratic_x.pow(&p_ + Atom::num(1) / Atom::num(2));
            let expanded = rubi_expand_integrand_product(&u, &v, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_6370(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, f__, d1__, e1__, d2__, e2__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6370,
        source: "Int[(f_.*x_)^m_*(d1_+e1_.*x_)^p_*(d2_+e2_.*x_)^p_*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
          Int[ExpandIntegrand[(a+b*ArcCosh[c*x])^n/(Sqrt[d1+e1*x]*Sqrt[d2+e2*x]),(f*x)^m*(d1+e1*x)^(p+1/2)*(d2+e2*x)^(p+1/2),x],x] /;
        FreeQ[{a,b,c,d1,e1,d2,e2,f,m,n},x] && EqQ[e1,c*d1] && EqQ[e2,-c*d2] && GtQ[d1,0] && LtQ[d2,0] && IGtQ[p+1/2,0] && Not[IGtQ[(m+1)/2,0]] &&
          (EqQ[m,-1] || EqQ[m,-2])",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [f__, m_, d1__, e1__, p_, d2__, e2__, a__, b__, c__, n_, x_],
        optional: [f__, e1__, e2__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d1__, e1__, d2__, e2__, f__, m_, n_], x_)
                && eqq!(e1__, &c__ * &d1__)
                && eqq!(e2__, -&c__ * &d2__)
                && gtq!(d1__, 0)
                && ltq!(d2__, 0)
                && igtq!(&p_ + Atom::num(1) / Atom::num(2), 0)
                && !igtq!((&m_ + Atom::num(1)) / Atom::num(2), 0)
                && (eqq!(m_, -1) || eqq!(m_, -2))
        },
        rhs: {
            let l1 = &d1__ + &e1__ * x_;
            let l2 = &d2__ + &e2__ * x_;
            let argument = &a__ + &b__ * (&c__ * x_).acosh();
            let u = argument.pow(&n_) / (&l1.sqrt() * &l2.sqrt());
            let v = (&f__ * x_).pow(&m_)
                * l1.pow(&p_ + Atom::num(1) / Atom::num(2))
                * l2.pow(&p_ + Atom::num(1) / Atom::num(2));
            let expanded = rubi_expand_integrand_product(&u, &v, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_6371(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, x_);
    rules.push(rubi_rule!(
        order: 6371,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^2)*(a_.+b_.*ArcCosh[c_.*x_]),x_Symbol] :=
          d*(f*x)^(m+1)*(a+b*ArcCosh[c*x])/(f*(m+1)) +
          e*(f*x)^(m+3)*(a+b*ArcCosh[c*x])/(f^3*(m+3)) -
          b*c/(f*(m+1)*(m+3)) \\[Star] Int[(f*x)^(m+1)*(d*(m+3)+e*(m+1)*x^2)/(Sqrt[1+c*x]*Sqrt[-1+c*x]),x] /;
        FreeQ[{a,b,c,d,e,f,m},x] && NeQ[c^2*d+e,0] && NeQ[m,-1] && NeQ[m,-3]",
        desc: "Integration by parts",
        refs: [],
        pattern: (f__ * x_).pow(m_) * (d__ + e__ * x_.pow(2)) * (a__ + b__ * (c__ * x_).acosh()),
        with: [f__, m_, d__, e__, a__, b__, c__, x_],
        optional: [f__, m_, e__, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_], x_)
                && neq!(c__.pow(2) * &d__ + &e__, 0)
                && neq!(m_, -1)
                && neq!(m_, -3)
        },
        rhs: {
            let scaled = &f__ * x_;
            let argument = &a__ + &b__ * (&c__ * x_).acosh();
            let denominator =
                (Atom::num(1) + &c__ * x_).sqrt() * (-Atom::num(1) + &c__ * x_).sqrt();
            let recursive = scaled.pow(&m_ + Atom::num(1))
                * (&d__ * (&m_ + Atom::num(3)) + &e__ * (&m_ + Atom::num(1)) * x_.pow(2))
                / denominator;
            rubi_simp(&(&d__ * scaled.pow(&m_ + Atom::num(1)) * &argument
                    / (&f__ * (&m_ + Atom::num(1)))), x_)
                    + rubi_simp(&(&e__ * scaled.pow(&m_ + Atom::num(3)) * argument
                        / (f__.pow(3) * (&m_ + Atom::num(3)))), x_)
                    - rubi_star(&b__ * &c__ / (&f__ * (&m_ + Atom::num(1)) * (&m_ + Atom::num(3))), rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_6372(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, p_, x_);
    rules.push(rubi_rule!(
        order: 6372,
        source: "Int[x_*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCosh[c_.*x_]),x_Symbol] :=
          (d+e*x^2)^(p+1)*(a+b*ArcCosh[c*x])/(2*e*(p+1)) - b*c/(2*e*(p+1)) \\[Star] Int[(d+e*x^2)^(p+1)/(Sqrt[1+c*x]*Sqrt[-1+c*x]),x] /;
        FreeQ[{a,b,c,d,e,p},x] && NeQ[c^2*d+e,0] && NeQ[p,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern: x_ * (d__ + e__ * x_.pow(2)).pow(p_) * (a__ + b__ * (c__ * x_).acosh()),
        with: [d__, e__, p_, a__, b__, c__, x_],
        optional: [e__, p_, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__, p_], x_)
                && neq!(c__.pow(2) * &d__ + &e__, 0)
                && neq!(p_, -1)
        },
        rhs: {
            let quadratic_x = &d__ + &e__ * x_.pow(2);
            let argument = &a__ + &b__ * (&c__ * x_).acosh();
            let recursive = quadratic_x.pow(&p_ + Atom::num(1))
                / ((Atom::num(1) + &c__ * x_).sqrt() * (-Atom::num(1) + &c__ * x_).sqrt());
            rubi_simp(&(quadratic_x.pow(&p_ + Atom::num(1)) * argument
                    / (Atom::num(2) * &e__ * (&p_ + Atom::num(1)))), x_)
                    - rubi_star(&b__ * &c__ / (Atom::num(2) * &e__ * (&p_ + Atom::num(1))), rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_6373(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 6373,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCosh[c_.*x_]),x_Symbol] :=
          With[{u=IntHide[(f*x)^m*(d+e*x^2)^p,x]},
          (a+b*ArcCosh[c*x]) \\[Star] u - b*c \\[Star] Int[SimplifyIntegrand[u/(Sqrt[1+c*x]*Sqrt[-1+c*x]),x],x]] /;
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
                && (gtq!(p_, 0)
                    || (igtq!((&m_ - Atom::num(1)) / Atom::num(2), 0) && leq!(&m_ + &p_, 0)))
        },
        rhs: {
            let argument = &a__ + &b__ * (&c__ * x_).acosh();
            let u = rubi_int_hide(
                &((&f__ * x_).pow(&m_) * (&d__ + &e__ * x_.pow(2)).pow(&p_)),
                x_,
            ).rubi_rhs();
            let denominator =
                (Atom::num(1) + &c__ * x_).sqrt() * (-Atom::num(1) + &c__ * x_).sqrt();
            let recursive = rubi_simplify_integrand(&(&u / denominator), x_);
            rubi_star(argument, u)
                    - rubi_star(&b__ * &c__, rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_6374(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6374,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
          Int[ExpandIntegrand[(a+b*ArcCosh[c*x])^n,(f*x)^m*(d+e*x^2)^p,x],x] /;
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
            let u = (&a__ + &b__ * (&c__ * x_).acosh()).pow(&n_);
            let v = (&f__ * x_).pow(&m_) * (&d__ + &e__ * x_.pow(2)).pow(&p_);
            let expanded = rubi_expand_integrand_product(&u, &v, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_6375(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6375,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^p_.*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
          Unintegrable[(f*x)^m*(d+e*x^2)^p*(a+b*ArcCosh[c*x])^n,x] /;
        FreeQ[{a,b,c,d,e,f,m,n,p},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [f__, m_, d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [f__, m_, e__, p_, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_, p_], x_)
        },
        rhs: {
            let integrand = (&f__ * x_).pow(&m_)
                * (&d__ + &e__ * x_.pow(2)).pow(&p_)
                * (&a__ + &b__ * (&c__ * x_).acosh()).pow(&n_);
            rubi_unintegrable(integrand, x_)
        },
    ));
}

fn push_rules_rule_6376(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, f__, d1__, e1__, d2__, e2__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6376,
        source: "Int[(f_.*x_)^m_.*(d1_+e1_.*x_)^p_.*(d2_+e2_.*x_)^p_.*(a_.+b_.*ArcCosh[c_.*x_])^n_.,x_Symbol] :=
          Unintegrable[(f*x)^m*(d1+e1*x)^p*(d2+e2*x)^p*(a+b*ArcCosh[c*x])^n,x] /;
        FreeQ[{a,b,c,d1,e1,d2,e2,f,m,n,p},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [f__, m_, d1__, e1__, p_, d2__, e2__, a__, b__, c__, n_, x_],
        optional: [f__, m_, e1__, p_, e2__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d1__, e1__, d2__, e2__, f__, m_, n_, p_], x_)
        },
        rhs: {
            let integrand = (&f__ * x_).pow(&m_)
                * (&d1__ + &e1__ * x_).pow(&p_)
                * (&d2__ + &e2__ * x_).pow(&p_)
                * (&a__ + &b__ * (&c__ * x_).acosh()).pow(&n_);
            rubi_unintegrable(integrand, x_)
        },
    ));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn downvalues_6327_through_6376_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .filter(|order| (6327..=6376).contains(order))
            .collect::<Vec<_>>();
        assert_eq!(orders, (6327..=6376).collect::<Vec<_>>());
    }
}

// Generated shared pattern builders.

#[inline(never)]
fn rubi_shared_pattern_0(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d1__ = symbols.d1__;
    let d2__ = symbols.d2__;
    let e1__ = symbols.e1__;
    let e2__ = symbols.e2__;
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    (f__ * x_).pow(m_) * (a__ + b__ * (c__ * x_).acosh()).pow(n_)
        / ((d1__ + e1__ * x_).sqrt() * (d2__ + e2__ * x_).sqrt())
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
    (f__ * x_).pow(m_) * (a__ + b__ * (c__ * x_).acosh()).pow(n_) / (d__ + e__ * x_.pow(2)).sqrt()
}

#[inline(never)]
fn rubi_shared_pattern_2(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d1__ = symbols.d1__;
    let d2__ = symbols.d2__;
    let e1__ = symbols.e1__;
    let e2__ = symbols.e2__;
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (f__ * x_).pow(m_)
        * (d1__ + e1__ * x_).pow(p_)
        * (d2__ + e2__ * x_).pow(p_)
        * (a__ + b__ * (c__ * x_).acosh()).pow(n_)
}

#[inline(never)]
fn rubi_shared_pattern_3(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d1__ = symbols.d1__;
    let d2__ = symbols.d2__;
    let e1__ = symbols.e1__;
    let e2__ = symbols.e2__;
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    (f__ * x_).pow(m_)
        * (d1__ + e1__ * x_).sqrt()
        * (d2__ + e2__ * x_).sqrt()
        * (a__ + b__ * (c__ * x_).acosh()).pow(n_)
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
    (f__ * x_).pow(m_) * (d__ + e__ * x_.pow(2)).pow(p_) * (a__ + b__ * (c__ * x_).acosh())
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
    (f__ * x_).pow(m_) * (d__ + e__ * x_.pow(2)).pow(p_) * (a__ + b__ * (c__ * x_).acosh()).pow(n_)
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
    (f__ * x_).pow(m_) * (d__ + e__ * x_.pow(2)).sqrt() * (a__ + b__ * (c__ * x_).acosh()).pow(n_)
}
