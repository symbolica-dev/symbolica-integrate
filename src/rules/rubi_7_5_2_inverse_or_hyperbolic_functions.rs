use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_6867(rules);
    push_rules_rule_6868(rules);
    push_rules_rule_6869(rules);
    push_rules_rule_6870(rules);
    push_rules_rule_6871(rules);
    push_rules_rule_6872(rules);
    push_rules_rule_6873(rules);
    push_rules_rule_6874(rules);
    // Blocks 6 and 7 are disabled comments in docs/rubi_pdf_rules.md.

    push_rules_rule_6875(rules);
    push_rules_rule_6876(rules);
    push_rules_rule_6877(rules);
    push_rules_rule_6878(rules);
    push_rules_rule_6879(rules);
    push_rules_rule_6880(rules);
    push_rules_rule_6881(rules);
    push_rules_rule_6882(rules);
    push_rules_rule_6883(rules);
    push_rules_rule_6884(rules);
    push_rules_rule_6885(rules);
    push_rules_rule_6886(rules);
    push_rules_rule_6887(rules);
    push_rules_rule_6888(rules);
    push_rules_rule_6889(rules);
    push_rules_rule_6890(rules);
    push_rules_rule_6891(rules);
    push_rules_rule_6892(rules);
    push_rules_rule_6893(rules);
    push_rules_rule_6894(rules);
    push_rules_rule_6895(rules);
    push_rules_rule_6896(rules);
    push_rules_rule_6897(rules);
    push_rules_rule_6898(rules);
    push_rules_rule_6899(rules);
    push_rules_rule_6900(rules);
    push_rules_rule_6901(rules);
    push_rules_rule_6902(rules);
}

fn push_rules_rule_6867(rules: &mut Vec<RubiRule>) {
    rubi_symb!(c_, d__, x_);
    rules.push(rubi_rule!(
        order: 6867,
        source: "Int[ArcSech[c_+d_.*x_],x_Symbol] :=
          (c+d*x)*ArcSech[c+d*x]/d +
          Int[Sqrt[(1-c-d*x)/(1+c+d*x)]/(1-c-d*x),x] /;
        FreeQ[{c,d},x]",
        desc: "Integration by parts",
        refs: ["CRC 591, A&S 4.6.47"],
        pattern: (c_ + d__ * x_).asech(),
        with: [c_, d__, x_],
        optional: [d__],
        when: { freeq!([c_, d__], x_) },
        rhs: {
            let affine = &c_ + &d__ * x_;
            let recursive = ((Atom::num(1) - &affine) / (Atom::num(1) + &affine)).sqrt()
                / (Atom::num(1) - &affine);
            rubi_simp(&(&affine * affine.asech() / &d__), x_) + rubi_rhs_int(&recursive, x_)
        },
    ));
}

fn push_rules_rule_6868(rules: &mut Vec<RubiRule>) {
    rubi_symb!(c_, d__, x_);
    rules.push(rubi_rule!(
        order: 6868,
        source: "Int[ArcCsch[c_+d_.*x_],x_Symbol] :=
          (c+d*x)*ArcCsch[c+d*x]/d +
          Int[1/((c+d*x)*Sqrt[1+1/(c+d*x)^2]),x] /;
        FreeQ[{c,d},x]",
        desc: "Integration by parts",
        refs: ["CRC 594, A&S 4.6.46"],
        pattern: (c_ + d__ * x_).acsch(),
        with: [c_, d__, x_],
        optional: [d__],
        when: { freeq!([c_, d__], x_) },
        rhs: {
            let affine = &c_ + &d__ * x_;
            let recursive = Atom::num(1)
                / (&affine * (Atom::num(1) + Atom::num(1) / affine.pow(2)).sqrt());
            rubi_simp(&((&c_ + &d__ * x_) * (&c_ + &d__ * x_).acsch() / &d__), x_) + rubi_rhs_int(&recursive, x_)
        },
    ));
}

fn push_rules_rule_6869(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c_, d__, p_, x_);
    rules.push(rubi_rule!(
        order: 6869,
        source: "Int[(a_.+b_.*ArcSech[c_+d_.*x_])^p_.,x_Symbol] :=
          1/d \\[Star] Subst[Int[(a+b*ArcSech[x])^p,x],x,c+d*x] /;
        FreeQ[{a,b,c,d},x] && IGtQ[p,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c_, d__, p_, x_],
        optional: [a__, b__, d__, p_],
        when: { freeq!([a__, b__, c_, d__], x_) && igtq!(p_, 0) },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let payload = (&a__ + &b__ * sub_atom.asech()).pow(&p_);
            let primitive = rubi_rhs_int(&payload, sub);
            rubi_star(Atom::num(1) / &d__, rubi_subst(&primitive, sub, &c_ + &d__ * x_))
        },
    ));
}

fn push_rules_rule_6870(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c_, d__, p_, x_);
    rules.push(rubi_rule!(
        order: 6870,
        source: "Int[(a_.+b_.*ArcCsch[c_+d_.*x_])^p_.,x_Symbol] :=
          1/d \\[Star] Subst[Int[(a+b*ArcCsch[x])^p,x],x,c+d*x] /;
        FreeQ[{a,b,c,d},x] && IGtQ[p,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c_, d__, p_, x_],
        optional: [a__, b__, d__, p_],
        when: { freeq!([a__, b__, c_, d__], x_) && igtq!(p_, 0) },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let payload = (&a__ + &b__ * sub_atom.acsch()).pow(&p_);
            let primitive = rubi_rhs_int(&payload, sub);
            rubi_star(Atom::num(1) / &d__, rubi_subst(&primitive, sub, &c_ + &d__ * x_))
        },
    ));
}

fn push_rules_rule_6871(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c_, d__, p_, x_);
    rules.push(rubi_rule!(
        order: 6871,
        source: "Int[(a_.+b_.*ArcSech[c_+d_.*x_])^p_,x_Symbol] :=
          Unintegrable[(a+b*ArcSech[c+d*x])^p,x] /;
        FreeQ[{a,b,c,d,p},x] && Not[IGtQ[p,0]]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c_, d__, p_, x_],
        optional: [a__, b__, d__],
        when: { freeq!([a__, b__, c_, d__, p_], x_) && !igtq!(p_, 0) },
        rhs: {
            rubi_unintegrable(
                (&a__ + &b__ * (&c_ + &d__ * x_).asech()).pow(&p_),
                x_,
            )
        },
    ));
}

fn push_rules_rule_6872(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c_, d__, p_, x_);
    rules.push(rubi_rule!(
        order: 6872,
        source: "Int[(a_.+b_.*ArcCsch[c_+d_.*x_])^p_,x_Symbol] :=
          Unintegrable[(a+b*ArcCsch[c+d*x])^p,x] /;
        FreeQ[{a,b,c,d,p},x] && Not[IGtQ[p,0]]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c_, d__, p_, x_],
        optional: [a__, b__, d__],
        when: { freeq!([a__, b__, c_, d__, p_], x_) && !igtq!(p_, 0) },
        rhs: {
            rubi_unintegrable(
                (&a__ + &b__ * (&c_ + &d__ * x_).acsch()).pow(&p_),
                x_,
            )
        },
    ));
}

fn push_rules_rule_6873(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c_, d__, e__, f__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 6873,
        source: "Int[(e_.+f_.*x_)^m_.*(a_.+b_.*ArcSech[c_+d_.*x_])^p_.,x_Symbol] :=
          1/d \\[Star] Subst[Int[(f*x/d)^m*(a+b*ArcSech[x])^p,x],x,c+d*x] /;
        FreeQ[{a,b,c,d,e,f,m},x] && EqQ[d*e-c*f,0] && IGtQ[p,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [e__, f__, m_, a__, b__, c_, d__, p_, x_],
        optional: [e__, f__, m_, a__, b__, d__, p_],
        when: {
            freeq!([a__, b__, c_, d__, e__, f__, m_], x_)
                && eqq!(&d__ * &e__ - &c_ * &f__, 0)
                && igtq!(p_, 0)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let payload = (&f__ * &sub_atom / &d__).pow(&m_) * (&a__ + &b__ * sub_atom.asech()).pow(&p_);
            let primitive = rubi_rhs_int(&payload, sub);
            rubi_star(Atom::num(1) / &d__, rubi_subst(&primitive, sub, &c_ + &d__ * x_))
        },
    ));
}

fn push_rules_rule_6874(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c_, d__, e__, f__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 6874,
        source: "Int[(e_.+f_.*x_)^m_.*(a_.+b_.*ArcCsch[c_+d_.*x_])^p_.,x_Symbol] :=
          1/d \\[Star] Subst[Int[(f*x/d)^m*(a+b*ArcCsch[x])^p,x],x,c+d*x] /;
        FreeQ[{a,b,c,d,e,f,m},x] && EqQ[d*e-c*f,0] && IGtQ[p,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [e__, f__, m_, a__, b__, c_, d__, p_, x_],
        optional: [e__, f__, m_, a__, b__, d__, p_],
        when: {
            freeq!([a__, b__, c_, d__, e__, f__, m_], x_)
                && eqq!(&d__ * &e__ - &c_ * &f__, 0)
                && igtq!(p_, 0)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let payload = (&f__ * &sub_atom / &d__).pow(&m_) * (&a__ + &b__ * sub_atom.acsch()).pow(&p_);
            let primitive = rubi_rhs_int(&payload, sub);
            rubi_star(Atom::num(1) / &d__, rubi_subst(&primitive, sub, &c_ + &d__ * x_))
        },
    ));
}

fn push_rules_rule_6875(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c_, d__, e__, f__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 6875,
        source: "Int[(e_.+f_.*x_)^m_.*(a_.+b_.*ArcSech[c_+d_.*x_])^p_.,x_Symbol] :=
          -1/d^(m+1) \\[Star] Subst[Int[(a+b*x)^p*Sech[x]*Tanh[x]*(d*e-c*f+f*Sech[x])^m,x],x,ArcSech[c+d*x]] /;
        FreeQ[{a,b,c,d,e,f},x] && IGtQ[p,0] && IntegerQ[m]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [e__, f__, m_, a__, b__, c_, d__, p_, x_],
        optional: [e__, f__, m_, a__, b__, d__, p_],
        when: {
            freeq!([a__, b__, c_, d__, e__, f__], x_) && igtq!(p_, 0) && integerq!(m_)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let payload = (&a__ + &b__ * &sub_atom).pow(&p_)
                * sub_atom.sech()
                * sub_atom.tanh()
                * (&d__ * &e__ - &c_ * &f__ + &f__ * sub_atom.sech()).pow(&m_);
            let primitive = rubi_rhs_int(&payload, sub);
            rubi_star(-(Atom::num(1) / d__.pow(&m_ + 1)), rubi_subst(&primitive, sub, (&c_ + &d__ * x_).asech()))
        },
    ));
}

fn push_rules_rule_6876(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c_, d__, e__, f__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 6876,
        source: "Int[(e_.+f_.*x_)^m_.*(a_.+b_.*ArcCsch[c_+d_.*x_])^p_.,x_Symbol] :=
          -1/d^(m+1) \\[Star] Subst[Int[(a+b*x)^p*Csch[x]*Coth[x]*(d*e-c*f+f*Csch[x])^m,x],x,ArcCsch[c+d*x]] /;
        FreeQ[{a,b,c,d,e,f},x] && IGtQ[p,0] && IntegerQ[m]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [e__, f__, m_, a__, b__, c_, d__, p_, x_],
        optional: [e__, f__, m_, a__, b__, d__, p_],
        when: {
            freeq!([a__, b__, c_, d__, e__, f__], x_) && igtq!(p_, 0) && integerq!(m_)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let payload = (&a__ + &b__ * &sub_atom).pow(&p_)
                * sub_atom.csch()
                * sub_atom.coth()
                * (&d__ * &e__ - &c_ * &f__ + &f__ * sub_atom.csch()).pow(&m_);
            let primitive = rubi_rhs_int(&payload, sub);
            rubi_star(-(Atom::num(1) / d__.pow(&m_ + 1)), rubi_subst(&primitive, sub, (&c_ + &d__ * x_).acsch()))
        },
    ));
}

fn push_rules_rule_6877(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c_, d__, e__, f__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 6877,
        source: "Int[(e_.+f_.*x_)^m_.*(a_.+b_.*ArcSech[c_+d_.*x_])^p_.,x_Symbol] :=
          1/d \\[Star] Subst[Int[((d*e-c*f)/d+f*x/d)^m*(a+b*ArcSech[x])^p,x],x,c+d*x] /;
        FreeQ[{a,b,c,d,e,f,m},x] && IGtQ[p,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [e__, f__, m_, a__, b__, c_, d__, p_, x_],
        optional: [e__, f__, m_, a__, b__, d__, p_],
        when: {
            freeq!([a__, b__, c_, d__, e__, f__, m_], x_) && igtq!(p_, 0)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let payload = ((&d__ * &e__ - &c_ * &f__) / &d__ + &f__ * &sub_atom / &d__).pow(&m_)
                * (&a__ + &b__ * sub_atom.asech()).pow(&p_);
            let primitive = rubi_rhs_int(&payload, sub);
            rubi_star(Atom::num(1) / &d__, rubi_subst(&primitive, sub, &c_ + &d__ * x_))
        },
    ));
}

fn push_rules_rule_6878(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c_, d__, e__, f__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 6878,
        source: "Int[(e_.+f_.*x_)^m_.*(a_.+b_.*ArcCsch[c_+d_.*x_])^p_.,x_Symbol] :=
          1/d \\[Star] Subst[Int[((d*e-c*f)/d+f*x/d)^m*(a+b*ArcCsch[x])^p,x],x,c+d*x] /;
        FreeQ[{a,b,c,d,e,f,m},x] && IGtQ[p,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [e__, f__, m_, a__, b__, c_, d__, p_, x_],
        optional: [e__, f__, m_, a__, b__, d__, p_],
        when: {
            freeq!([a__, b__, c_, d__, e__, f__, m_], x_) && igtq!(p_, 0)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let payload = ((&d__ * &e__ - &c_ * &f__) / &d__ + &f__ * &sub_atom / &d__).pow(&m_)
                * (&a__ + &b__ * sub_atom.acsch()).pow(&p_);
            let primitive = rubi_rhs_int(&payload, sub);
            rubi_star(Atom::num(1) / &d__, rubi_subst(&primitive, sub, &c_ + &d__ * x_))
        },
    ));
}

fn push_rules_rule_6879(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c_, d__, e__, f__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 6879,
        source: "Int[(e_.+f_.*x_)^m_.*(a_.+b_.*ArcSech[c_+d_.*x_])^p_,x_Symbol] :=
          Unintegrable[(e+f*x)^m*(a+b*ArcSech[c+d*x])^p,x] /;
        FreeQ[{a,b,c,d,e,f,m,p},x] && Not[IGtQ[p,0]]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [e__, f__, m_, a__, b__, c_, d__, p_, x_],
        optional: [e__, f__, m_, a__, b__, d__],
        when: { freeq!([a__, b__, c_, d__, e__, f__, m_, p_], x_) && !igtq!(p_, 0) },
        rhs: {
            rubi_unintegrable(
                (&e__ + &f__ * x_).pow(&m_) * (&a__ + &b__ * (&c_ + &d__ * x_).asech()).pow(&p_),
                x_,
            )
        },
    ));
}

fn push_rules_rule_6880(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c_, d__, e__, f__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 6880,
        source: "Int[(e_.+f_.*x_)^m_.*(a_.+b_.*ArcCsch[c_+d_.*x_])^p_,x_Symbol] :=
          Unintegrable[(e+f*x)^m*(a+b*ArcCsch[c+d*x])^p,x] /;
        FreeQ[{a,b,c,d,e,f,m,p},x] && Not[IGtQ[p,0]]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [e__, f__, m_, a__, b__, c_, d__, p_, x_],
        optional: [e__, f__, m_, a__, b__, d__],
        when: { freeq!([a__, b__, c_, d__, e__, f__, m_, p_], x_) && !igtq!(p_, 0) },
        rhs: {
            rubi_unintegrable(
                (&e__ + &f__ * x_).pow(&m_) * (&a__ + &b__ * (&c_ + &d__ * x_).acsch()).pow(&p_),
                x_,
            )
        },
    ));
}

fn push_rules_rule_6881(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, m_, n_, u__, x_);
    rules.push(rubi_rule!(
        order: 6881,
        source: "Int[u_.*ArcSech[c_./(a_.+b_.*x_^n_.)]^m_.,x_Symbol] :=
          Int[u*ArcCosh[a/c+b*x^n/c]^m,x] /;
        FreeQ[{a,b,c,n,m},x]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: u__ * (c__ / (a__ + b__ * x_.pow(n_))).asech().pow(m_),
        with: [u__, c__, a__, b__, n_, m_, x_],
        optional: [u__, c__, a__, b__, n_, m_],
        when: { freeq!([a__, b__, c__, n_, m_], x_) },
        rhs: {
            rubi_rhs_int(&(&u__ * (&a__ / &c__ + &b__ * x_.pow(&n_) / &c__).acosh().pow(&m_)), x_)
        },
    ));
}

fn push_rules_rule_6882(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, m_, n_, u__, x_);
    rules.push(rubi_rule!(
        order: 6882,
        source: "Int[u_.*ArcCsch[c_./(a_.+b_.*x_^n_.)]^m_.,x_Symbol] :=
          Int[u*ArcSinh[a/c+b*x^n/c]^m,x] /;
        FreeQ[{a,b,c,n,m},x]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: u__ * (c__ / (a__ + b__ * x_.pow(n_))).acsch().pow(m_),
        with: [u__, c__, a__, b__, n_, m_, x_],
        optional: [u__, c__, a__, b__, n_, m_],
        when: { freeq!([a__, b__, c__, n_, m_], x_) },
        rhs: {
            rubi_rhs_int(&(&u__ * (&a__ / &c__ + &b__ * x_.pow(&n_) / &c__).asinh().pow(&m_)), x_)
        },
    ));
}

fn push_rules_rule_6883(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, x_);
    rules.push(rubi_rule!(
        order: 6883,
        source: "Int[E^ArcSech[a_.*x_], x_Symbol] :=
          x*E^ArcSech[a*x] + Log[x]/a + 1/a \\[Star] Int[1/(x*(1-a*x))*Sqrt[(1-a*x)/(1+a*x)],x] /;
        FreeQ[a,x]",
        desc: "Integration by parts",
        refs: [],
        pattern: (a__ * x_).asech().exp(),
        with: [a__, x_],
        optional: [a__],
        when: { freeq!(a__, x_) },
        rhs: {
            let argument = &a__ * x_;
            rubi_simp(&(x_ * &argument.asech().exp()), x_)
                    + rubi_simp(&(x_.log() / &a__), x_)
                    + rubi_star(Atom::num(1) / a__, rubi_rhs_int(
                        &(Atom::num(1) / (x_ * (Atom::num(1) - &argument))
                            * ((Atom::num(1) - &argument) / (Atom::num(1) + &argument)).sqrt()),
                        x_,
                    ))
        },
    ));
}

fn push_rules_rule_6884(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, p_, x_);
    rules.push(rubi_rule!(
        order: 6884,
        source: "Int[E^ArcSech[a_.*x_^p_], x_Symbol] :=
          x*E^ArcSech[a*x^p] +
          p/a \\[Star] Int[1/x^p,x] +
          p*Sqrt[1+a*x^p]/a*Sqrt[1/(1+a*x^p)] \\[Star] Int[1/(x^p*Sqrt[1+a*x^p]*Sqrt[1-a*x^p]),x] /;
        FreeQ[{a,p},x]",
        desc: "Integration by parts, piecewise constant extraction and algebraic simplification",
        refs: [],
        pattern: (a__ * x_.pow(p_)).asech().exp(),
        with: [a__, p_, x_],
        optional: [a__],
        when: { freeq!([a__, p_], x_) },
        rhs: {
            let monomial = x_.pow(&p_);
            let argument = &a__ * &monomial;
            let sqrt_plus = (Atom::num(1) + &argument).sqrt();
            rubi_simp(&(x_ * &argument.asech().exp()), x_)
                    + rubi_star(&p_, rubi_rhs_int(&(Atom::num(1) / &monomial), x_) / &a__)
                    + rubi_star(&p_ * &sqrt_plus * (Atom::num(1) / (Atom::num(1) + &argument)).sqrt() / a__, rubi_rhs_int(
                            &(Atom::num(1)
                                / (monomial * sqrt_plus * (Atom::num(1) - &argument).sqrt())),
                            x_,
                        ))
        },
    ));
}

fn push_rules_rule_6885(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, p_, x_);
    rules.push(rubi_rule!(
        order: 6885,
        source: "Int[E^ArcCsch[a_.*x_^p_.], x_Symbol] :=
          1/a \\[Star] Int[1/x^p,x] + Int[Sqrt[1+1/(a^2*x^(2*p))],x] /;
        FreeQ[{a,p},x]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: (a__ * x_.pow(p_)).acsch().exp(),
        with: [a__, p_, x_],
        optional: [a__, p_],
        when: { freeq!([a__, p_], x_) },
        rhs: {
            let monomial = x_.pow(&p_);
            rubi_star(Atom::num(1) / &a__, rubi_rhs_int(&(Atom::num(1) / &monomial), x_))
                    + rubi_rhs_int(
                        &(Atom::num(1) + Atom::num(1) / (a__.pow(2) * monomial.pow(2))).sqrt(),
                        x_,
                    )
        },
    ));
}

fn push_rules_rule_6886(rules: &mut Vec<RubiRule>) {
    rubi_symb!(n_, u_);
    rules.push(rubi_rule!(
        order: 6886,
        source: "Int[E^(n_.*ArcSech[u_]), x_Symbol] :=
          Int[(1/u + Sqrt[(1-u)/(1+u)] + 1/u*Sqrt[(1-u)/(1+u)])^n,x] /;
        IntegerQ[n]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: (n_ * Atom::var(u_).asech()).exp(),
        with: [n_, u_, x_],
        optional: [n_],
        when: { integerq!(n_) },
        rhs: {
            let converted = Atom::num(1) / &u_
                + ((Atom::num(1) - &u_) / (Atom::num(1) + &u_)).sqrt()
                + Atom::num(1) / &u_ * ((Atom::num(1) - &u_) / (Atom::num(1) + &u_)).sqrt();
            rubi_rhs_int(&converted.pow(&n_), x_)
        },
    ));
}

fn push_rules_rule_6887(rules: &mut Vec<RubiRule>) {
    rubi_symb!(n_, u_);
    rules.push(rubi_rule!(
        order: 6887,
        source: "Int[E^(n_.*ArcCsch[u_]), x_Symbol] :=
          Int[(1/u + Sqrt[1+1/u^2])^n,x] /;
        IntegerQ[n]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: (n_ * Atom::var(u_).acsch()).exp(),
        with: [n_, u_, x_],
        optional: [n_],
        when: { integerq!(n_) },
        rhs: {
            let converted = Atom::num(1) / &u_ + (Atom::num(1) + Atom::num(1) / u_.pow(2)).sqrt();
            rubi_rhs_int(&converted.pow(&n_), x_)
        },
    ));
}

fn push_rules_rule_6888(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, p_, x_);
    rules.push(rubi_rule!(
        order: 6888,
        source: "Int[E^ArcSech[a_.*x_^p_.]/x_, x_Symbol] :=
          -1/(a*p*x^p) +
          Sqrt[1+a*x^p]/a*Sqrt[1/(1+a*x^p)] \\[Star] Int[Sqrt[1+a*x^p]*Sqrt[1-a*x^p]/x^(p+1),x] /;
        FreeQ[{a,p},x]",
        desc: "Algebraic simplification, piecewise constant extraction and algebraic simplification",
        refs: [],
        pattern: (a__ * x_.pow(p_)).asech().exp() / x_,
        with: [a__, p_, x_],
        optional: [a__, p_],
        when: { freeq!([a__, p_], x_) },
        rhs: {
            let monomial = x_.pow(&p_);
            let argument = &a__ * &monomial;
            rubi_simp(&(-Atom::num(1) / (&a__ * &p_ * &monomial)), x_)
                    + rubi_star((Atom::num(1) + &argument).sqrt() * (Atom::num(1) / (Atom::num(1) + &argument)).sqrt() / a__, rubi_rhs_int(
                            &((Atom::num(1) + &argument).sqrt()
                                * (Atom::num(1) - &argument).sqrt()
                                / x_.pow(&p_ + 1)),
                            x_,
                        ))
        },
    ));
}

fn push_rules_rule_6889(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 6889,
        source: "Int[x_^m_.*E^ArcSech[a_.*x_^p_.], x_Symbol] :=
          x^(m+1)*E^ArcSech[a*x^p]/(m+1) +
          p/(a*(m+1)) \\[Star] Int[x^(m-p),x] +
          p*Sqrt[1+a*x^p]/(a*(m+1))*Sqrt[1/(1+a*x^p)] \\[Star] Int[x^(m-p)/(Sqrt[1+a*x^p]*Sqrt[1-a*x^p]),x] /;
        FreeQ[{a,m,p},x] && NeQ[m,-1]",
        desc: "Integration by parts, piecewise constant extraction and algebraic simplification",
        refs: [],
        pattern: x_.pow(m_) * (a__ * x_.pow(p_)).asech().exp(),
        with: [m_, a__, p_, x_],
        optional: [a__, p_, m_],
        when: { freeq!([a__, m_, p_], x_) && neq!(m_, -1) },
        rhs: {
            let monomial = x_.pow(&p_);
            let argument = &a__ * &monomial;
            let sqrt_plus = (Atom::num(1) + &argument).sqrt();
            rubi_simp(&(x_.pow(&m_ + 1) * &argument.asech().exp() / (&m_ + 1)), x_)
                    + rubi_star(&p_, rubi_rhs_int(&(x_.pow(&m_ - &p_)), x_) / (&a__ * (&m_ + 1)))
                    + rubi_star(&p_ * &sqrt_plus * (Atom::num(1) / (Atom::num(1) + &argument)).sqrt() / (&a__ * (&m_ + 1)), rubi_rhs_int(
                            &(x_.pow(&m_ - &p_)
                                / (sqrt_plus * (Atom::num(1) - &argument).sqrt())),
                            x_,
                        ))
        },
    ));
}

fn push_rules_rule_6890(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 6890,
        source: "Int[x_^m_.*E^ArcCsch[a_.*x_^p_.], x_Symbol] :=
          1/a \\[Star] Int[x^(m-p),x] + Int[x^m*Sqrt[1+1/(a^2*x^(2*p))],x] /;
        FreeQ[{a,m,p},x]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: x_.pow(m_) * (a__ * x_.pow(p_)).acsch().exp(),
        with: [m_, a__, p_, x_],
        optional: [a__, p_, m_],
        when: { freeq!([a__, m_, p_], x_) },
        rhs: {
            rubi_star(Atom::num(1) / &a__, rubi_rhs_int(&(x_.pow(&m_ - &p_)), x_))
                    + rubi_rhs_int(
                        &(x_.pow(&m_)
                            * (Atom::num(1) + Atom::num(1) / (a__.pow(2) * x_.pow(Atom::num(2) * &p_))).sqrt()),
                        x_,
                    )
        },
    ));
}

fn push_rules_rule_6891(rules: &mut Vec<RubiRule>) {
    rubi_symb!(m_, n_, u_, x_);
    rules.push(rubi_rule!(
        order: 6891,
        source: "Int[x_^m_.*E^(n_.*ArcSech[u_]), x_Symbol] :=
          Int[x^m*(1/u + Sqrt[(1-u)/(1+u)] + 1/u*Sqrt[(1-u)/(1+u)])^n,x] /;
        FreeQ[m,x] && IntegerQ[n]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: x_.pow(m_) * (n_ * Atom::var(u_).asech()).exp(),
        with: [m_, n_, u_, x_],
        optional: [m_, n_],
        when: { freeq!(m_, x_) && integerq!(n_) },
        rhs: {
            let converted = Atom::num(1) / &u_
                + ((Atom::num(1) - &u_) / (Atom::num(1) + &u_)).sqrt()
                + Atom::num(1) / &u_ * ((Atom::num(1) - &u_) / (Atom::num(1) + &u_)).sqrt();
            rubi_rhs_int(&(x_.pow(&m_) * converted.pow(&n_)), x_)
        },
    ));
}

fn push_rules_rule_6892(rules: &mut Vec<RubiRule>) {
    rubi_symb!(m_, n_, u_, x_);
    rules.push(rubi_rule!(
        order: 6892,
        source: "Int[x_^m_.*E^(n_.*ArcCsch[u_]), x_Symbol] :=
          Int[x^m*(1/u + Sqrt[1+1/u^2])^n,x] /;
        FreeQ[m,x] && IntegerQ[n]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: x_.pow(m_) * (n_ * Atom::var(u_).acsch()).exp(),
        with: [m_, n_, u_, x_],
        optional: [m_, n_],
        when: { freeq!(m_, x_) && integerq!(n_) },
        rhs: {
            let converted = Atom::num(1) / &u_ + (Atom::num(1) + Atom::num(1) / u_.pow(2)).sqrt();
            rubi_rhs_int(&(x_.pow(&m_) * converted.pow(&n_)), x_)
        },
    ));
}

fn push_rules_rule_6893(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a_, b__, c__, x_);
    rules.push(rubi_rule!(
        order: 6893,
        source: "Int[E^(ArcSech[c_.*x_])/(a_+b_.*x_^2), x_Symbol] :=
          1/(a*c) \\[Star] Int[Sqrt[1/(1+c*x)]/(x*Sqrt[1-c*x]),x] + 1/c \\[Star] Int[1/(x*(a+b*x^2)),x] /;
        FreeQ[{a,b,c},x] && EqQ[b+a*c^2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (c__ * x_).asech().exp() / (a_ + b__ * x_.pow(2)),
        with: [c__, a_, b__, x_],
        optional: [c__, b__],
        when: { freeq!([a_, b__, c__], x_) && eqq!(&b__ + &a_ * c__.pow(2), 0) },
        rhs: {
            rubi_star(Atom::num(1) / (&a_ * &c__), rubi_rhs_int(
                    &((Atom::num(1) / (Atom::num(1) + &c__ * x_)).sqrt()
                        / (x_ * (Atom::num(1) - &c__ * x_).sqrt())),
                    x_,
                ))
                    + rubi_star(Atom::num(1) / c__, rubi_rhs_int(&(Atom::num(1) / (x_ * (&a_ + &b__ * x_.pow(2)))), x_))
        },
    ));
}

fn push_rules_rule_6894(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a_, b__, c__, x_);
    rules.push(rubi_rule!(
        order: 6894,
        source: "Int[E^(ArcCsch[c_.*x_])/(a_+b_.*x_^2), x_Symbol] :=
          1/(a*c^2) \\[Star] Int[1/(x^2*Sqrt[1+1/(c^2*x^2)]),x] + 1/c \\[Star] Int[1/(x*(a+b*x^2)),x] /;
        FreeQ[{a,b,c},x] && EqQ[b-a*c^2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (c__ * x_).acsch().exp() / (a_ + b__ * x_.pow(2)),
        with: [c__, a_, b__, x_],
        optional: [c__, b__],
        when: { freeq!([a_, b__, c__], x_) && eqq!(&b__ - &a_ * c__.pow(2), 0) },
        rhs: {
            rubi_star(Atom::num(1) / (&a_ * c__.pow(2)), rubi_rhs_int(
                    &(Atom::num(1)
                        / (x_.pow(2)
                            * (Atom::num(1) + Atom::num(1) / (c__.pow(2) * x_.pow(2))).sqrt())),
                    x_,
                ))
                    + rubi_star(Atom::num(1) / c__, rubi_rhs_int(&(Atom::num(1) / (x_ * (&a_ + &b__ * x_.pow(2)))), x_))
        },
    ));
}

fn push_rules_rule_6895(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a_, b__, c__, d__, m_, x_);
    rules.push(rubi_rule!(
        order: 6895,
        source: "Int[(d_.*x_)^m_.*E^(ArcSech[c_.*x_])/(a_+b_.*x_^2), x_Symbol] :=
          d/(a*c) \\[Star] Int[(d*x)^(m-1)*Sqrt[1/(1+c*x)]/Sqrt[1-c*x],x] + d/c \\[Star] Int[(d*x)^(m-1)/(a+b*x^2),x] /;
        FreeQ[{a,b,c,d,m},x] && EqQ[b+a*c^2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (d__ * x_).pow(m_) * (c__ * x_).asech().exp() / (a_ + b__ * x_.pow(2)),
        with: [d__, m_, c__, a_, b__, x_],
        optional: [d__, m_, c__, b__],
        when: { freeq!([a_, b__, c__, d__, m_], x_) && eqq!(&b__ + &a_ * c__.pow(2), 0) },
        rhs: {
            rubi_star(&d__, rubi_rhs_int(
                    &((&d__ * x_).pow(&m_ - 1)
                        * (Atom::num(1) / (Atom::num(1) + &c__ * x_)).sqrt()
                        / (Atom::num(1) - &c__ * x_).sqrt()),
                    x_,
                ) / (&a_ * &c__))
                    + rubi_star(&d__, rubi_rhs_int(
                        &((&d__ * x_).pow(&m_ - 1) / (&a_ + &b__ * x_.pow(2))),
                        x_,
                    ) / c__)
        },
    ));
}

fn push_rules_rule_6896(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a_, b__, c__, d__, m_, x_);
    rules.push(rubi_rule!(
        order: 6896,
        source: "Int[(d_.*x_)^m_.*E^(ArcCsch[c_.*x_])/(a_+b_.*x_^2), x_Symbol] :=
          d^2/(a*c^2) \\[Star] Int[(d*x)^(m-2)/Sqrt[1+1/(c^2*x^2)],x] + d/c \\[Star] Int[(d*x)^(m-1)/(a+b*x^2),x] /;
        FreeQ[{a,b,c,d,m},x] && EqQ[b-a*c^2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (d__ * x_).pow(m_) * (c__ * x_).acsch().exp() / (a_ + b__ * x_.pow(2)),
        with: [d__, m_, c__, a_, b__, x_],
        optional: [d__, m_, c__, b__],
        when: { freeq!([a_, b__, c__, d__, m_], x_) && eqq!(&b__ - &a_ * c__.pow(2), 0) },
        rhs: {
            rubi_star(d__.pow(2), rubi_rhs_int(
                        &((&d__ * x_).pow(&m_ - 2)
                            / (Atom::num(1) + Atom::num(1) / (c__.pow(2) * x_.pow(2))).sqrt()),
                        x_,
                    )
                    / (&a_ * c__.pow(2)))
                    + rubi_star(&d__, rubi_rhs_int(
                        &((&d__ * x_).pow(&m_ - 1) / (&a_ + &b__ * x_.pow(2))),
                        x_,
                    ) / c__)
        },
    ));
}

fn push_rules_rule_6897(rules: &mut Vec<RubiRule>) {
    rubi_symb!(u_);
    rules.push(rubi_rule!(
        order: 6897,
        source: "Int[ArcSech[u_],x_Symbol] :=
          x*ArcSech[u] +
          Sqrt[1-u^2]/(u*Sqrt[-1+1/u]*Sqrt[1+1/u]) \\[Star] Int[SimplifyIntegrand[x*D[u,x]/(u*Sqrt[1-u^2]),x],x] /;
        InverseFunctionFreeQ[u,x] && Not[FunctionOfExponentialQ[u,x]]",
        desc: "Integration by parts and piecewise constant extraction",
        refs: [],
        pattern: Atom::var(u_).asech(),
        with: [u_, x_],
        when: { rubi_inverse_function_free_q(&u_, x_) && !rubi_function_of_exponential_q(u_.as_view(), x_) },
        rhs: {
            let radical = (Atom::num(1) - u_.pow(2)).sqrt();
            let multiplier = &radical
                / (&u_
                    * (-Atom::num(1) + Atom::num(1) / &u_).sqrt()
                    * (Atom::num(1) + Atom::num(1) / &u_).sqrt());
            let recursive = rubi_simplify_integrand(&(x_ * u_.derivative(x_) / (&u_ * radical)), x_);
            rubi_simp(&(x_ * u_.asech()), x_) + rubi_star(multiplier, rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_6898(rules: &mut Vec<RubiRule>) {
    rubi_symb!(u_);
    rules.push(rubi_rule!(
        order: 6898,
        source: "Int[ArcCsch[u_],x_Symbol] :=
          x*ArcCsch[u] -
          u/Sqrt[-u^2] \\[Star] Int[SimplifyIntegrand[x*D[u,x]/(u*Sqrt[-1-u^2]),x],x] /;
        InverseFunctionFreeQ[u,x] && Not[FunctionOfExponentialQ[u,x]]",
        desc: "Integration by parts and piecewise constant extraction",
        refs: [],
        pattern: Atom::var(u_).acsch(),
        with: [u_, x_],
        when: { rubi_inverse_function_free_q(&u_, x_) && !rubi_function_of_exponential_q(u_.as_view(), x_) },
        rhs: {
            let recursive = rubi_simplify_integrand(
                &(x_ * u_.derivative(x_) / (&u_ * (-Atom::num(1) - u_.pow(2)).sqrt())),
                x_,
            );
            rubi_simp(&(x_ * u_.acsch()), x_) - rubi_star(&u_, rubi_rhs_int(&recursive, x_) / (-u_.pow(2)).sqrt())
        },
    ));
}

fn push_rules_rule_6899(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, u_, x_);
    rules.push(rubi_rule!(
        order: 6899,
        source: "Int[(c_.+d_.*x_)^m_.*(a_.+b_.*ArcSech[u_]),x_Symbol] :=
          (c+d*x)^(m+1)*(a+b*ArcSech[u])/(d*(m+1)) +
          b*Sqrt[1-u^2]/(d*(m+1)*u*Sqrt[-1+1/u]*Sqrt[1+1/u]) \\[Star] Int[SimplifyIntegrand[(c+d*x)^(m+1)*D[u,x]/(u*Sqrt[1-u^2]),x],x] /;
        FreeQ[{a,b,c,d,m},x] && NeQ[m,-1] && InverseFunctionFreeQ[u,x] && Not[FunctionOfQ[(c+d*x)^(m+1),u,x]] && Not[FunctionOfExponentialQ[u,x]]",
        desc: "Integration by parts and piecewise constant extraction",
        refs: [],
        pattern: (c__ + d__ * x_).pow(m_) * (a__ + b__ * Atom::var(u_).asech()),
        with: [c__, d__, m_, a__, b__, u_, x_],
        optional: [c__, d__, m_, a__, b__],
        when: {
            freeq!([a__, b__, c__, d__, m_], x_)
                && neq!(m_, -1)
                && rubi_inverse_function_free_q(&u_, x_)
                && !rubi_function_of_q(&(&c__ + &d__ * x_).pow(&m_ + 1), &u_, x_)
                && !rubi_function_of_exponential_q(u_.as_view(), x_)
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let argument = &a__ + &b__ * u_.asech();
            let radical = (Atom::num(1) - u_.pow(2)).sqrt();
            let multiplier = &b__ * &radical
                / (&d__
                    * (&m_ + 1)
                    * &u_
                    * (-Atom::num(1) + Atom::num(1) / &u_).sqrt()
                    * (Atom::num(1) + Atom::num(1) / &u_).sqrt());
            let recursive = rubi_simplify_integrand(
                &(linear.pow(&m_ + 1) * u_.derivative(x_) / (&u_ * radical)),
                x_,
            );
            rubi_simp(&(linear.pow(&m_ + 1) * argument / (&d__ * (&m_ + 1))), x_) + rubi_star(multiplier, rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_6900(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, u_, x_);
    rules.push(rubi_rule!(
        order: 6900,
        source: "Int[(c_.+d_.*x_)^m_.*(a_.+b_.*ArcCsch[u_]),x_Symbol] :=
          (c+d*x)^(m+1)*(a+b*ArcCsch[u])/(d*(m+1)) -
          b*u/(d*(m+1)*Sqrt[-u^2]) \\[Star] Int[SimplifyIntegrand[(c+d*x)^(m+1)*D[u,x]/(u*Sqrt[-1-u^2]),x],x] /;
        FreeQ[{a,b,c,d,m},x] && NeQ[m,-1] && InverseFunctionFreeQ[u,x] && Not[FunctionOfQ[(c+d*x)^(m+1),u,x]] && Not[FunctionOfExponentialQ[u,x]]",
        desc: "Integration by parts and piecewise constant extraction",
        refs: [],
        pattern: (c__ + d__ * x_).pow(m_) * (a__ + b__ * Atom::var(u_).acsch()),
        with: [c__, d__, m_, a__, b__, u_, x_],
        optional: [c__, d__, m_, a__, b__],
        when: {
            freeq!([a__, b__, c__, d__, m_], x_)
                && neq!(m_, -1)
                && rubi_inverse_function_free_q(&u_, x_)
                && !rubi_function_of_q(&(&c__ + &d__ * x_).pow(&m_ + 1), &u_, x_)
                && !rubi_function_of_exponential_q(u_.as_view(), x_)
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let argument = &a__ + &b__ * u_.acsch();
            let recursive = rubi_simplify_integrand(
                &(linear.pow(&m_ + 1) * u_.derivative(x_)
                    / (&u_ * (-Atom::num(1) - u_.pow(2)).sqrt())),
                x_,
            );
            rubi_simp(&(linear.pow(&m_ + 1) * argument / (&d__ * (&m_ + 1))), x_)
                    - rubi_star(&b__ * &u_ / (&d__ * (&m_ + 1) * (-u_.pow(2)).sqrt()), rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_6901(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, u_, v_);
    rules.push(rubi_rule!(
        order: 6901,
        source: "Int[v_*(a_.+b_.*ArcSech[u_]),x_Symbol] :=
          With[{w=IntHide[v,x]},
          (a+b*ArcSech[u]) \\[Star] w + b*Sqrt[1-u^2]/(u*Sqrt[-1+1/u]*Sqrt[1+1/u]) \\[Star] Int[SimplifyIntegrand[w*D[u,x]/(u*Sqrt[1-u^2]),x],x] /;
         InverseFunctionFreeQ[w,x]] /;
        FreeQ[{a,b},x] && InverseFunctionFreeQ[u,x] && Not[MatchQ[v, (c_.+d_.*x)^m_. /; FreeQ[{c,d,m},x]]]",
        desc: "Integration by parts and piecewise constant extraction",
        refs: [],
        pattern: Atom::var(v_) * (a__ + b__ * Atom::var(u_).asech()),
        with: [v_, a__, b__, u_, x_],
        optional: [a__, b__],
        when: {
            freeq!([a__, b__], x_)
                && rubi_inverse_function_free_q(&u_, x_)
                && !rubi_linear_power_q(&v_, x_)
                && rubi_int_hide_inverse_function_free_q(&v_, x_)
        },
        rhs: {
            let hidden = rubi_int_hide(&v_, x_).rubi_rhs();
            let argument = &a__ + &b__ * u_.asech();
            let radical = (Atom::num(1) - u_.pow(2)).sqrt();
            let multiplier = &b__ * &radical
                / (&u_
                    * (-Atom::num(1) + Atom::num(1) / &u_).sqrt()
                    * (Atom::num(1) + Atom::num(1) / &u_).sqrt());
            let recursive = rubi_simplify_integrand(&(&hidden * u_.derivative(x_) / (&u_ * radical)), x_);
            rubi_star(argument, hidden) + rubi_star(multiplier, rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_6902(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, u_, v_);
    rules.push(rubi_rule!(
        order: 6902,
        source: "Int[v_*(a_.+b_.*ArcCsch[u_]),x_Symbol] :=
          With[{w=IntHide[v,x]},
          (a+b*ArcCsch[u]) \\[Star] w - b*u/Sqrt[-u^2] \\[Star] Int[SimplifyIntegrand[w*D[u,x]/(u*Sqrt[-1-u^2]),x],x] /;
         InverseFunctionFreeQ[w,x]] /;
        FreeQ[{a,b},x] && InverseFunctionFreeQ[u,x] && Not[MatchQ[v, (c_.+d_.*x)^m_. /; FreeQ[{c,d,m},x]]]",
        desc: "Integration by parts and piecewise constant extraction",
        refs: [],
        pattern: Atom::var(v_) * (a__ + b__ * Atom::var(u_).acsch()),
        with: [v_, a__, b__, u_, x_],
        optional: [a__, b__],
        when: {
            freeq!([a__, b__], x_)
                && rubi_inverse_function_free_q(&u_, x_)
                && !rubi_linear_power_q(&v_, x_)
                && rubi_int_hide_inverse_function_free_q(&v_, x_)
        },
        rhs: {
            let hidden = rubi_int_hide(&v_, x_).rubi_rhs();
            let argument = &a__ + &b__ * u_.acsch();
            let recursive = rubi_simplify_integrand(
                &(&hidden * u_.derivative(x_) / (&u_ * (-Atom::num(1) - u_.pow(2)).sqrt())),
                x_,
            );
            rubi_star(argument, hidden) - rubi_star(&b__ * &u_ / (-u_.pow(2)).sqrt(), rubi_rhs_int(&recursive, x_))
        },
    ));
}

// Generated shared pattern builders.

#[inline(never)]
fn rubi_shared_pattern_0(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c_ = symbols.c_;
    let d__ = symbols.d__;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (a__ + b__ * (c_ + d__ * x_).acsch()).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c_ = symbols.c_;
    let d__ = symbols.d__;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (a__ + b__ * (c_ + d__ * x_).asech()).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_2(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c_ = symbols.c_;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (e__ + f__ * x_).pow(m_) * (a__ + b__ * (c_ + d__ * x_).acsch()).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_3(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c_ = symbols.c_;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (e__ + f__ * x_).pow(m_) * (a__ + b__ * (c_ + d__ * x_).asech()).pow(p_)
}
