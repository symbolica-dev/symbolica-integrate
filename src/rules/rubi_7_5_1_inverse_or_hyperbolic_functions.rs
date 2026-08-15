use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_6831(rules);
    push_rules_rule_6832(rules);
    push_rules_rule_6833(rules);
    push_rules_rule_6834(rules);
    push_rules_rule_6835(rules);
    push_rules_rule_6836(rules);
    push_rules_rule_6837(rules);
    push_rules_rule_6838(rules);
    push_rules_rule_6839(rules);
    push_rules_rule_6840(rules);
    push_rules_rule_6841(rules);
    push_rules_rule_6842(rules);
    push_rules_rule_6843(rules);
    push_rules_rule_6844(rules);
    push_rules_rule_6845(rules);
    push_rules_rule_6846(rules);
    push_rules_rule_6847(rules);
    push_rules_rule_6848(rules);
    push_rules_rule_6849(rules);
    push_rules_rule_6850(rules);
    push_rules_rule_6851(rules);
    push_rules_rule_6852(rules);
    push_rules_rule_6853(rules);
    push_rules_rule_6854(rules);
    push_rules_rule_6855(rules);
    push_rules_rule_6856(rules);
    push_rules_rule_6857(rules);
    push_rules_rule_6858(rules);
    push_rules_rule_6859(rules);
    push_rules_rule_6860(rules);
    push_rules_rule_6861(rules);
    push_rules_rule_6862(rules);
    push_rules_rule_6863(rules);
    push_rules_rule_6864(rules);
    push_rules_rule_6865(rules);
    push_rules_rule_6866(rules);
}

fn push_rules_rule_6831(rules: &mut Vec<RubiRule>) {
    rubi_symb!(c__, x_);
    rules.push(rubi_rule!(
        order: 6831,
        source: "Int[ArcSech[c_.*x_],x_Symbol] :=
          x*ArcSech[c*x] + Sqrt[1+c*x]*Sqrt[1/(1+c*x)] \\[Star] Int[1/Sqrt[1-c^2*x^2],x] /;
        FreeQ[c,x]",
        desc: "Integration by parts and piecewise constant extraction",
        refs: ["CRC 591, A&S 4.6.47"],
        pattern: (c__ * x_).asech(),
        with: [c__, x_],
        optional: [c__],
        when: { freeq!(c__, x_) },
        rhs: {
            let argument = &c__ * x_;
            rubi_simp(&(x_ * &argument.asech()), x_)
                    + rubi_star((Atom::num(1) + &argument).sqrt() * (Atom::num(1) / (Atom::num(1) + &argument)).sqrt(), rubi_rhs_int(
                            &(Atom::num(1)
                                / (Atom::num(1) - c__.pow(2) * x_.pow(2)).sqrt()),
                            x_,
                        ))
        },
    ));
}

fn push_rules_rule_6832(rules: &mut Vec<RubiRule>) {
    rubi_symb!(c__, x_);
    rules.push(rubi_rule!(
        order: 6832,
        source: "Int[ArcCsch[c_.*x_],x_Symbol] :=
          x*ArcCsch[c*x] + 1/c \\[Star] Int[1/(x*Sqrt[1+1/(c^2*x^2)]),x] /;
        FreeQ[c,x]",
        desc: "Integration by parts",
        refs: ["CRC 594, A&S 4.6.46"],
        pattern: (c__ * x_).acsch(),
        with: [c__, x_],
        optional: [c__],
        when: { freeq!(c__, x_) },
        rhs: {
            let argument = &c__ * x_;
            rubi_simp(&(x_ * argument.acsch()), x_)
                    + rubi_star(Atom::num(1) / &c__, rubi_rhs_int(
                        &(Atom::num(1)
                            / (x_
                                * (Atom::num(1)
                                    + Atom::num(1) / (c__.pow(2) * x_.pow(2)))
                                .sqrt())),
                        x_,
                    ))
        },
    ));
}

fn push_rules_rule_6833(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, n_, x_);
    rules.push(rubi_rule!(
        order: 6833,
        source: "Int[(a_.+b_.*ArcSech[c_.*x_])^n_,x_Symbol] :=
          -1/c \\[Star] Subst[Int[(a+b*x)^n*Sech[x]*Tanh[x],x],x,ArcSech[c*x]] /;
        FreeQ[{a,b,c,n},x] && IGtQ[n,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (a__ + b__ * (c__ * x_).asech()).pow(n_),
        with: [a__, b__, c__, n_, x_],
        optional: [a__, b__, c__],
        when: { freeq!([a__, b__, c__, n_], x_) && igtq!(n_, 0) },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let transformed = (&a__ + &b__ * &sub_atom).pow(&n_) * sub_atom.sech() * sub_atom.tanh();
            let primitive = rubi_rhs_int(&transformed, substitution_symbol);
            rubi_star(-(Atom::num(1) / &c__), rubi_subst(&primitive, substitution_symbol, (&c__ * x_).asech()))
        },
    ));
}

fn push_rules_rule_6834(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, n_, x_);
    rules.push(rubi_rule!(
        order: 6834,
        source: "Int[(a_.+b_.*ArcCsch[c_.*x_])^n_,x_Symbol] :=
          -1/c \\[Star] Subst[Int[(a+b*x)^n*Csch[x]*Coth[x],x],x,ArcCsch[c*x]] /;
        FreeQ[{a,b,c,n},x] && IGtQ[n,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (a__ + b__ * (c__ * x_).acsch()).pow(n_),
        with: [a__, b__, c__, n_, x_],
        optional: [a__, b__, c__],
        when: { freeq!([a__, b__, c__, n_], x_) && igtq!(n_, 0) },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let transformed = (&a__ + &b__ * &sub_atom).pow(&n_) * sub_atom.csch() * sub_atom.coth();
            let primitive = rubi_rhs_int(&transformed, substitution_symbol);
            rubi_star(-(Atom::num(1) / &c__), rubi_subst(&primitive, substitution_symbol, (&c__ * x_).acsch()))
        },
    ));
}

fn push_rules_rule_6835(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, x_);
    rules.push(rubi_rule!(
        order: 6835,
        source: "Int[(a_.+b_.*ArcSech[c_.*x_])/x_,x_Symbol] :=
          -Subst[Int[(a+b*ArcCosh[x/c])/x,x],x,1/x] /;
        FreeQ[{a,b,c},x]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (a__ + b__ * (c__ * x_).asech()) / x_,
        with: [a__, b__, c__, x_],
        optional: [a__, b__, c__],
        when: { freeq!([a__, b__, c__], x_) },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let transformed = (&a__ + &b__ * (&sub_atom / &c__).acosh()) / &sub_atom;
            let primitive = rubi_rhs_int(&transformed, substitution_symbol);
            -rubi_subst(&primitive, substitution_symbol, Atom::num(1) / x_)
        },
    ));
}

fn push_rules_rule_6836(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, x_);
    rules.push(rubi_rule!(
        order: 6836,
        source: "Int[(a_.+b_.*ArcCsch[c_.*x_])/x_,x_Symbol] :=
          -Subst[Int[(a+b*ArcSinh[x/c])/x,x],x,1/x] /;
        FreeQ[{a,b,c},x]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (a__ + b__ * (c__ * x_).acsch()) / x_,
        with: [a__, b__, c__, x_],
        optional: [a__, b__, c__],
        when: { freeq!([a__, b__, c__], x_) },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let transformed = (&a__ + &b__ * (&sub_atom / &c__).asinh()) / &sub_atom;
            let primitive = rubi_rhs_int(&transformed, substitution_symbol);
            -rubi_subst(&primitive, substitution_symbol, Atom::num(1) / x_)
        },
    ));
}

fn push_rules_rule_6837(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, x_);
    rules.push(rubi_rule!(
        order: 6837,
        source: "Int[(d_.*x_)^m_.*(a_.+b_.*ArcSech[c_.*x_]),x_Symbol] :=
          (d*x)^(m+1)*(a+b*ArcSech[c*x])/(d*(m+1)) +
          b*Sqrt[1+c*x]/(m+1)*Sqrt[1/(1+c*x)] \\[Star] Int[(d*x)^m/(Sqrt[1-c*x]*Sqrt[1+c*x]),x] /;
        FreeQ[{a,b,c,d,m},x] && NeQ[m,-1]",
        desc: "Integration by parts and piecewise constant extraction",
        refs: ["CRC 593', A&S 4.6.58'"],
        pattern: (d__ * x_).pow(m_) * (a__ + b__ * (c__ * x_).asech()),
        with: [d__, m_, a__, b__, c__, x_],
        optional: [d__, m_, a__, b__, c__],
        when: { freeq!([a__, b__, c__, d__, m_], x_) && neq!(m_, -1) },
        rhs: {
            let scaled_x = &d__ * x_;
            let argument = &a__ + &b__ * (&c__ * x_).asech();
            let sqrt_plus = (Atom::num(1) + &c__ * x_).sqrt();
            let recursive = scaled_x.pow(&m_)
                / ((Atom::num(1) - &c__ * x_).sqrt() * &sqrt_plus);
            rubi_simp(&(scaled_x.pow(&m_ + 1) * argument / (&d__ * (&m_ + 1))), x_)
                    + rubi_star(&b__ * sqrt_plus * (Atom::num(1) / (Atom::num(1) + &c__ * x_)).sqrt() / (&m_ + 1), rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_6838(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, x_);
    rules.push(rubi_rule!(
        order: 6838,
        source: "Int[(d_.*x_)^m_.*(a_.+b_.*ArcCsch[c_.*x_]),x_Symbol] :=
          (d*x)^(m+1)*(a+b*ArcCsch[c*x])/(d*(m+1)) +
          b*d/(c*(m+1)) \\[Star] Int[(d*x)^(m-1)/Sqrt[1+1/(c^2*x^2)],x] /;
        FreeQ[{a,b,c,d,m},x] && NeQ[m,-1]",
        desc: "Integration by parts",
        refs: ["CRC 596, A&S 4.6.56"],
        pattern: (d__ * x_).pow(m_) * (a__ + b__ * (c__ * x_).acsch()),
        with: [d__, m_, a__, b__, c__, x_],
        optional: [d__, m_, a__, b__, c__],
        when: { freeq!([a__, b__, c__, d__, m_], x_) && neq!(m_, -1) },
        rhs: {
            let scaled_x = &d__ * x_;
            let argument = &a__ + &b__ * (&c__ * x_).acsch();
            let recursive = scaled_x.pow(&m_ - 1)
                / (Atom::num(1) + Atom::num(1) / (c__.pow(2) * x_.pow(2))).sqrt();
            rubi_simp(&(scaled_x.pow(&m_ + 1) * argument / (&d__ * (&m_ + 1))), x_)
                    + rubi_star(&b__ * &d__ / (&c__ * (&m_ + 1)), rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_6839(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 6839,
        source: "Int[x_^m_.*(a_.+b_.*ArcSech[c_.*x_])^n_,x_Symbol] :=
          -1/c^(m+1) \\[Star] Subst[Int[(a+b*x)^n*Sech[x]^(m+1)*Tanh[x],x],x,ArcSech[c*x]] /;
        FreeQ[{a,b,c},x] && IntegerQ[n] && IntegerQ[m] && (GtQ[n,0] || LtQ[m,-1])",
        desc: "Integration by substitution",
        refs: [],
        pattern: x_.pow(m_) * (a__ + b__ * (c__ * x_).asech()).pow(n_),
        with: [m_, a__, b__, c__, n_, x_],
        optional: [m_, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__], x_)
                && integerq!(n_)
                && integerq!(m_)
                && (gtq!(n_, 0) || ltq!(m_, -1))
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let transformed = (&a__ + &b__ * &sub_atom).pow(&n_)
                * sub_atom.sech().pow(&m_ + 1)
                * sub_atom.tanh();
            let primitive = rubi_rhs_int(&transformed, substitution_symbol);
            rubi_star(-(Atom::num(1) / c__.pow(&m_ + 1)), rubi_subst(&primitive, substitution_symbol, (&c__ * x_).asech()))
        },
    ));
}

fn push_rules_rule_6840(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 6840,
        source: "Int[x_^m_.*(a_.+b_.*ArcCsch[c_.*x_])^n_,x_Symbol] :=
          -1/c^(m+1) \\[Star] Subst[Int[(a+b*x)^n*Csch[x]^(m+1)*Coth[x],x],x,ArcCsch[c*x]] /;
        FreeQ[{a,b,c},x] && IntegerQ[n] && IntegerQ[m] && (GtQ[n,0] || LtQ[m,-1])",
        desc: "Integration by substitution",
        refs: [],
        pattern: x_.pow(m_) * (a__ + b__ * (c__ * x_).acsch()).pow(n_),
        with: [m_, a__, b__, c__, n_, x_],
        optional: [m_, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__], x_)
                && integerq!(n_)
                && integerq!(m_)
                && (gtq!(n_, 0) || ltq!(m_, -1))
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let transformed = (&a__ + &b__ * &sub_atom).pow(&n_)
                * sub_atom.csch().pow(&m_ + 1)
                * sub_atom.coth();
            let primitive = rubi_rhs_int(&transformed, substitution_symbol);
            rubi_star(-(Atom::num(1) / c__.pow(&m_ + 1)), rubi_subst(&primitive, substitution_symbol, (&c__ * x_).acsch()))
        },
    ));
}

fn push_rules_rule_6841(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 6841,
        source: "Int[(a_.+b_.*ArcSech[c_.*x_])/(d_.+e_.*x_),x_Symbol] :=
          (a+b*ArcSech[c*x])*Log[1+(e-Sqrt[-c^2*d^2+e^2])/(c*d*E^ArcSech[c*x])]/e +
          (a+b*ArcSech[c*x])*Log[1+(e+Sqrt[-c^2*d^2+e^2])/(c*d*E^ArcSech[c*x])]/e -
          (a+b*ArcSech[c*x])*Log[1+1/E^(2*ArcSech[c*x])]/e +
          b/e \\[Star] Int[(Sqrt[(1-c*x)/(1+c*x)]*Log[1+(e-Sqrt[-c^2*d^2+e^2])/(c*d*E^ArcSech[c*x])])/(x*(1-c*x)),x] +
          b/e \\[Star] Int[(Sqrt[(1-c*x)/(1+c*x)]*Log[1+(e+Sqrt[-c^2*d^2+e^2])/(c*d*E^ArcSech[c*x])])/(x*(1-c*x)),x] -
          b/e \\[Star] Int[(Sqrt[(1-c*x)/(1+c*x)]*Log[1+1/E^(2*ArcSech[c*x])])/(x*(1-c*x)),x] /;
        FreeQ[{a,b,c,d,e},x]",
        desc: "Integration by parts",
        refs: [],
        pattern: (a__ + b__ * (c__ * x_).asech()) / (d__ + e__ * x_),
        with: [a__, b__, c__, d__, e__, x_],
        optional: [a__, b__, c__, d__, e__],
        when: { freeq!([a__, b__, c__, d__, e__], x_) },
        rhs: {
            let inverse = (&c__ * x_).asech();
            let argument = &a__ + &b__ * &inverse;
            let discriminant = (e__.pow(2) - c__.pow(2) * d__.pow(2)).sqrt();
            let exp_inverse = inverse.exp();
            let log_minus =
                (Atom::num(1) + (&e__ - &discriminant) / (&c__ * &d__ * &exp_inverse)).log();
            let log_plus =
                (Atom::num(1) + (&e__ + &discriminant) / (&c__ * &d__ * &exp_inverse)).log();
            let log_double = (Atom::num(1) + Atom::num(1) / (Atom::num(2) * inverse).exp()).log();
            let sqrt_ratio = ((Atom::num(1) - &c__ * x_) / (Atom::num(1) + &c__ * x_)).sqrt();
            let denominator = x_ * (Atom::num(1) - &c__ * x_);
            rubi_simp(&(&argument * &log_minus / &e__), x_)
                    + rubi_simp(&(&argument * &log_plus / &e__), x_)
                    - rubi_simp(&(argument * &log_double / &e__), x_)
                    + rubi_star(&b__, rubi_rhs_int(&(&sqrt_ratio * log_minus / &denominator), x_) / &e__)
                    + rubi_star(&b__, rubi_rhs_int(&(&sqrt_ratio * log_plus / &denominator), x_) / &e__)
                    - rubi_star(b__, rubi_rhs_int(&(sqrt_ratio * log_double / denominator), x_) / e__)
        },
    ));
}

fn push_rules_rule_6842(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, x_);
    rules.push(rubi_rule!(
        order: 6842,
        source: "Int[(d_.+e_.*x_)^m_.*(a_.+b_.*ArcSech[c_.*x_]),x_Symbol] :=
          (d+e*x)^(m+1)*(a+b*ArcSech[c*x])/(e*(m+1)) +
          b*Sqrt[1+c*x]/(e*(m+1))*Sqrt[1/(1+c*x)] \\[Star] Int[(d+e*x)^(m+1)/(x*Sqrt[1-c^2*x^2]),x] /;
        FreeQ[{a,b,c,d,e,m},x] && NeQ[m,-1]",
        desc: "Integration by parts and piecewise constant extraction",
        refs: [],
        pattern: (d__ + e__ * x_).pow(m_) * (a__ + b__ * (c__ * x_).asech()),
        with: [d__, e__, m_, a__, b__, c__, x_],
        optional: [d__, e__, m_, a__, b__, c__],
        when: { freeq!([a__, b__, c__, d__, e__, m_], x_) && neq!(m_, -1) },
        rhs: {
            let linear = &d__ + &e__ * x_;
            let inverse = (&c__ * x_).asech();
            let argument = &a__ + &b__ * inverse;
            let sqrt_plus = (Atom::num(1) + &c__ * x_).sqrt();
            let recursive = linear.pow(&m_ + 1)
                / (x_ * (Atom::num(1) - c__.pow(2) * x_.pow(2)).sqrt());
            rubi_simp(&(linear.pow(&m_ + 1) * argument / (&e__ * (&m_ + 1))), x_)
                    + rubi_star(&b__ * sqrt_plus * (Atom::num(1) / (Atom::num(1) + &c__ * x_)).sqrt() / (&e__ * (&m_ + 1)), rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_6843(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 6843,
        source: "Int[(a_.+b_.*ArcCsch[c_.*x_])/(d_.+e_.*x_),x_Symbol] :=
          (a+b*ArcCsch[c*x])*Log[1-(e-Sqrt[c^2*d^2+e^2])*E^ArcCsch[c*x]/(c*d)]/e +
          (a+b*ArcCsch[c*x])*Log[1-(e+Sqrt[c^2*d^2+e^2])*E^ArcCsch[c*x]/(c*d)]/e -
          (a+b*ArcCsch[c*x])*Log[1-E^(2*ArcCsch[c*x])]/e +
          b/(c*e) \\[Star] Int[Log[1-(e-Sqrt[c^2*d^2+e^2])*E^ArcCsch[c*x]/(c*d)]/(x^2*Sqrt[1+1/(c^2*x^2)]),x] +
          b/(c*e) \\[Star] Int[Log[1-(e+Sqrt[c^2*d^2+e^2])*E^ArcCsch[c*x]/(c*d)]/(x^2*Sqrt[1+1/(c^2*x^2)]),x] -
          b/(c*e) \\[Star] Int[Log[1-E^(2*ArcCsch[c*x])]/(x^2*Sqrt[1+1/(c^2*x^2)]),x] /;
        FreeQ[{a,b,c,d,e},x]",
        desc: "Integration by parts",
        refs: [],
        pattern: (a__ + b__ * (c__ * x_).acsch()) / (d__ + e__ * x_),
        with: [a__, b__, c__, d__, e__, x_],
        optional: [a__, b__, c__, d__, e__],
        when: { freeq!([a__, b__, c__, d__, e__], x_) },
        rhs: {
            let inverse = (&c__ * x_).acsch();
            let argument = &a__ + &b__ * &inverse;
            let discriminant = (c__.pow(2) * d__.pow(2) + e__.pow(2)).sqrt();
            let exp_inverse = inverse.exp();
            let log_minus =
                (Atom::num(1) - (&e__ - &discriminant) * &exp_inverse / (&c__ * &d__)).log();
            let log_plus =
                (Atom::num(1) - (&e__ + &discriminant) * &exp_inverse / (&c__ * &d__)).log();
            let log_double = (Atom::num(1) - (Atom::num(2) * inverse).exp()).log();
            let denominator = x_.pow(2)
                * (Atom::num(1) + Atom::num(1) / (c__.pow(2) * x_.pow(2))).sqrt();
            rubi_simp(&(&argument * &log_minus / &e__), x_)
                    + rubi_simp(&(&argument * &log_plus / &e__), x_)
                    - rubi_simp(&(argument * &log_double / &e__), x_)
                    + rubi_star(&b__, rubi_rhs_int(&(log_minus / &denominator), x_) / (&c__ * &e__))
                    + rubi_star(&b__, rubi_rhs_int(&(log_plus / &denominator), x_) / (&c__ * &e__))
                    - rubi_star(b__, rubi_rhs_int(&(log_double / denominator), x_) / (&c__ * e__))
        },
    ));
}

fn push_rules_rule_6844(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, x_);
    rules.push(rubi_rule!(
        order: 6844,
        source: "Int[(d_.+e_.*x_)^m_.*(a_.+b_.*ArcCsch[c_.*x_]),x_Symbol] :=
          (d+e*x)^(m+1)*(a+b*ArcCsch[c*x])/(e*(m+1)) +
          b/(c*e*(m+1)) \\[Star] Int[(d+e*x)^(m+1)/(x^2*Sqrt[1+1/(c^2*x^2)]),x] /;
        FreeQ[{a,b,c,d,e,m},x] && NeQ[m,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern: (d__ + e__ * x_).pow(m_) * (a__ + b__ * (c__ * x_).acsch()),
        with: [d__, e__, m_, a__, b__, c__, x_],
        optional: [d__, e__, m_, a__, b__, c__],
        when: { freeq!([a__, b__, c__, d__, e__, m_], x_) && neq!(m_, -1) },
        rhs: {
            let linear = &d__ + &e__ * x_;
            let inverse = (&c__ * x_).acsch();
            let argument = &a__ + &b__ * inverse;
            let recursive = linear.pow(&m_ + 1)
                / (x_.pow(2)
                    * (Atom::num(1) + Atom::num(1) / (c__.pow(2) * x_.pow(2))).sqrt());
            rubi_simp(&(linear.pow(&m_ + 1) * argument / (&e__ * (&m_ + 1))), x_)
                    + rubi_star(b__, rubi_rhs_int(&recursive, x_) / (&c__ * &e__ * (&m_ + 1)))
        },
    ));
}

fn push_rules_rule_6845(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, p_, x_);
    rules.push(rubi_rule!(
        order: 6845,
        source: "Int[(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcSech[c_.*x_]),x_Symbol] :=
          With[{u=IntHide[(d+e*x^2)^p,x]},
          (a+b*ArcSech[c*x]) \\[Star] u + b*Sqrt[1+c*x]*Sqrt[1/(1+c*x)] \\[Star] Int[SimplifyIntegrand[u/(x*Sqrt[1-c*x]*Sqrt[1+c*x]),x],x]] /;
        FreeQ[{a,b,c,d,e},x] && (IGtQ[p,0] || ILtQ[p+1/2,0])",
        desc: "Integration by parts and piecewise constant extraction",
        refs: [],
        pattern: (d__ + e__ * x_.pow(2)).pow(p_) * (a__ + b__ * (c__ * x_).asech()),
        with: [d__, e__, p_, a__, b__, c__, x_],
        optional: [d__, e__, p_, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && (igtq!(p_, 0) || iltq!(&p_ + Atom::num(1) / 2, 0))
        },
        rhs: {
            let hidden = rubi_int_hide(&(&d__ + &e__ * x_.pow(2)).pow(&p_), x_).rubi_rhs();
            let argument = &a__ + &b__ * (&c__ * x_).asech();
            let sqrt_plus = (Atom::num(1) + &c__ * x_).sqrt();
            let recursive = rubi_simplify_integrand(
                &(&hidden
                    / (x_ * (Atom::num(1) - &c__ * x_).sqrt() * &sqrt_plus)),
                x_,
            );
            rubi_star(argument, hidden)
                    + rubi_star(&b__ * sqrt_plus * (Atom::num(1) / (Atom::num(1) + &c__ * x_)).sqrt(), rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_6846(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, p_, x_);
    rules.push(rubi_rule!(
        order: 6846,
        source: "Int[(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcCsch[c_.*x_]),x_Symbol] :=
          With[{u=IntHide[(d+e*x^2)^p,x]},
          (a+b*ArcCsch[c*x]) \\[Star] u - b*c*x/Sqrt[-c^2*x^2] \\[Star] Int[SimplifyIntegrand[u/(x*Sqrt[-1-c^2*x^2]),x],x]] /;
        FreeQ[{a,b,c,d,e},x] && (IGtQ[p,0] || ILtQ[p+1/2,0])",
        desc: "Integration by parts and piecewise constant extraction",
        refs: [],
        pattern: (d__ + e__ * x_.pow(2)).pow(p_) * (a__ + b__ * (c__ * x_).acsch()),
        with: [d__, e__, p_, a__, b__, c__, x_],
        optional: [d__, e__, p_, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && (igtq!(p_, 0) || iltq!(&p_ + Atom::num(1) / 2, 0))
        },
        rhs: {
            let hidden = rubi_int_hide(&(&d__ + &e__ * x_.pow(2)).pow(&p_), x_).rubi_rhs();
            let argument = &a__ + &b__ * (&c__ * x_).acsch();
            let recursive = rubi_simplify_integrand(
                &(&hidden / (x_ * (-Atom::num(1) - c__.pow(2) * x_.pow(2)).sqrt())),
                x_,
            );
            rubi_star(argument, hidden)
                    - rubi_star(&b__ * &c__ * x_ / (-(c__.pow(2) * x_.pow(2))).sqrt(), rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_6847(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6847,
        source: "Int[(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcSech[c_.*x_])^n_.,x_Symbol] :=
          -Subst[Int[(e+d*x^2)^p*(a+b*ArcCosh[x/c])^n/x^(2*(p+1)),x],x,1/x] /;
        FreeQ[{a,b,c,d,e,n},x] && IGtQ[n,0] && IntegerQ[p]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [d__, e__, p_, a__, b__, c__, n_],
        when: { freeq!([a__, b__, c__, d__, e__, n_], x_) && igtq!(n_, 0) && integerq!(p_) },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let transformed = (&e__ + &d__ * sub_atom.pow(2)).pow(&p_)
                * (&a__ + &b__ * (&sub_atom / &c__).acosh()).pow(&n_)
                / sub_atom.pow(Atom::num(2) * (&p_ + 1));
            let primitive = rubi_rhs_int(&transformed, substitution_symbol);
            -rubi_subst(&primitive, substitution_symbol, Atom::num(1) / x_)
        },
    ));
}

fn push_rules_rule_6848(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6848,
        source: "Int[(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcCsch[c_.*x_])^n_.,x_Symbol] :=
          -Subst[Int[(e+d*x^2)^p*(a+b*ArcSinh[x/c])^n/x^(2*(p+1)),x],x,1/x] /;
        FreeQ[{a,b,c,d,e,n},x] && IGtQ[n,0] && IntegerQ[p]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [d__, e__, p_, a__, b__, c__, n_],
        when: { freeq!([a__, b__, c__, d__, e__, n_], x_) && igtq!(n_, 0) && integerq!(p_) },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let transformed = (&e__ + &d__ * sub_atom.pow(2)).pow(&p_)
                * (&a__ + &b__ * (&sub_atom / &c__).asinh()).pow(&n_)
                / sub_atom.pow(Atom::num(2) * (&p_ + 1));
            let primitive = rubi_rhs_int(&transformed, substitution_symbol);
            -rubi_subst(&primitive, substitution_symbol, Atom::num(1) / x_)
        },
    ));
}

fn push_rules_rule_6849(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6849,
        source: "Int[(d_.+e_.*x_^2)^p_*(a_.+b_.*ArcSech[c_.*x_])^n_.,x_Symbol] :=
          -Sqrt[x^2]/x \\[Star] Subst[Int[(e+d*x^2)^p*(a+b*ArcCosh[x/c])^n/x^(2*(p+1)),x],x,1/x] /;
        FreeQ[{a,b,c,d,e,n},x] && IGtQ[n,0] && EqQ[c^2*d+e,0] && IntegerQ[p+1/2] && GtQ[e,0] && LtQ[d,0]",
        desc: "Piecewise constant extraction and integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [d__, e__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, n_], x_)
                && igtq!(n_, 0)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && integerq!(&p_ + Atom::num(1) / 2)
                && gtq!(e__, 0)
                && ltq!(d__, 0)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let transformed = (&e__ + &d__ * sub_atom.pow(2)).pow(&p_)
                * (&a__ + &b__ * (&sub_atom / &c__).acosh()).pow(&n_)
                / sub_atom.pow(Atom::num(2) * (&p_ + 1));
            let primitive = rubi_rhs_int(&transformed, substitution_symbol);
            rubi_star(Atom::num(-1) * x_.pow(2).sqrt(), rubi_subst(&primitive, substitution_symbol, Atom::num(1) / x_)
                    / x_)
        },
    ));
}

fn push_rules_rule_6850(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6850,
        source: "Int[(d_.+e_.*x_^2)^p_*(a_.+b_.*ArcCsch[c_.*x_])^n_.,x_Symbol] :=
          -Sqrt[x^2]/x \\[Star] Subst[Int[(e+d*x^2)^p*(a+b*ArcSinh[x/c])^n/x^(2*(p+1)),x],x,1/x] /;
        FreeQ[{a,b,c,d,e,n},x] && IGtQ[n,0] && EqQ[e-c^2*d,0] && IntegerQ[p+1/2] && GtQ[e,0] && LtQ[d,0]",
        desc: "Piecewise constant extraction and integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [d__, e__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, n_], x_)
                && igtq!(n_, 0)
                && eqq!(&e__ - c__.pow(2) * &d__, 0)
                && integerq!(&p_ + Atom::num(1) / 2)
                && gtq!(e__, 0)
                && ltq!(d__, 0)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let transformed = (&e__ + &d__ * sub_atom.pow(2)).pow(&p_)
                * (&a__ + &b__ * (&sub_atom / &c__).asinh()).pow(&n_)
                / sub_atom.pow(Atom::num(2) * (&p_ + 1));
            let primitive = rubi_rhs_int(&transformed, substitution_symbol);
            rubi_star(Atom::num(-1) * x_.pow(2).sqrt(), rubi_subst(&primitive, substitution_symbol, Atom::num(1) / x_)
                    / x_)
        },
    ));
}

fn push_rules_rule_6851(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6851,
        source: "Int[(d_.+e_.*x_^2)^p_*(a_.+b_.*ArcSech[c_.*x_])^n_.,x_Symbol] :=
          -Sqrt[d+e*x^2]/(x*Sqrt[e+d/x^2]) \\[Star] Subst[Int[(e+d*x^2)^p*(a+b*ArcCosh[x/c])^n/x^(2*(p+1)),x],x,1/x] /;
        FreeQ[{a,b,c,d,e,n},x] && IGtQ[n,0] && EqQ[c^2*d+e,0] && IntegerQ[p+1/2] && Not[GtQ[e,0] && LtQ[d,0]]",
        desc: "Piecewise constant extraction and integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [d__, e__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, n_], x_)
                && igtq!(n_, 0)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && integerq!(&p_ + Atom::num(1) / 2)
                && !(gtq!(e__, 0) && ltq!(d__, 0))
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let transformed = (&e__ + &d__ * sub_atom.pow(2)).pow(&p_)
                * (&a__ + &b__ * (&sub_atom / &c__).acosh()).pow(&n_)
                / sub_atom.pow(Atom::num(2) * (&p_ + 1));
            let primitive = rubi_rhs_int(&transformed, substitution_symbol);
            let multiplier = -(&d__ + &e__ * x_.pow(2)).sqrt()
                / (x_ * (&e__ + &d__ / x_.pow(2)).sqrt());
            rubi_star(multiplier, rubi_subst(&primitive, substitution_symbol, Atom::num(1) / x_))
        },
    ));
}

fn push_rules_rule_6852(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6852,
        source: "Int[(d_.+e_.*x_^2)^p_*(a_.+b_.*ArcCsch[c_.*x_])^n_.,x_Symbol] :=
          -Sqrt[d+e*x^2]/(x*Sqrt[e+d/x^2]) \\[Star] Subst[Int[(e+d*x^2)^p*(a+b*ArcSinh[x/c])^n/x^(2*(p+1)),x],x,1/x] /;
        FreeQ[{a,b,c,d,e,n},x] && IGtQ[n,0] && EqQ[e-c^2*d,0] && IntegerQ[p+1/2] && Not[GtQ[e,0] && LtQ[d,0]]",
        desc: "Piecewise constant extraction and integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [d__, e__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, n_], x_)
                && igtq!(n_, 0)
                && eqq!(&e__ - c__.pow(2) * &d__, 0)
                && integerq!(&p_ + Atom::num(1) / 2)
                && !(gtq!(e__, 0) && ltq!(d__, 0))
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let transformed = (&e__ + &d__ * sub_atom.pow(2)).pow(&p_)
                * (&a__ + &b__ * (&sub_atom / &c__).asinh()).pow(&n_)
                / sub_atom.pow(Atom::num(2) * (&p_ + 1));
            let primitive = rubi_rhs_int(&transformed, substitution_symbol);
            let multiplier = -(&d__ + &e__ * x_.pow(2)).sqrt()
                / (x_ * (&e__ + &d__ / x_.pow(2)).sqrt());
            rubi_star(multiplier, rubi_subst(&primitive, substitution_symbol, Atom::num(1) / x_))
        },
    ));
}

fn push_rules_rule_6853(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, p_, x_);
    rules.push(rubi_rule!(
        order: 6853,
        source: "Int[x_*(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcSech[c_.*x_]),x_Symbol] :=
          (d+e*x^2)^(p+1)*(a+b*ArcSech[c*x])/(2*e*(p+1)) +
          b*Sqrt[1+c*x]/(2*e*(p+1))*Sqrt[1/(1+c*x)] \\[Star] Int[(d+e*x^2)^(p+1)/(x*Sqrt[1-c*x]*Sqrt[1+c*x]),x] /;
        FreeQ[{a,b,c,d,e,p},x] && NeQ[p,-1]",
        desc: "Integration by parts and piecewise constant extraction",
        refs: [],
        pattern: x_ * (d__ + e__ * x_.pow(2)).pow(p_) * (a__ + b__ * (c__ * x_).asech()),
        with: [d__, e__, p_, a__, b__, c__, x_],
        optional: [d__, e__, p_, a__, b__, c__],
        when: { freeq!([a__, b__, c__, d__, e__, p_], x_) && neq!(p_, -1) },
        rhs: {
            let quadratic = &d__ + &e__ * x_.pow(2);
            let argument = &a__ + &b__ * (&c__ * x_).asech();
            let sqrt_plus = (Atom::num(1) + &c__ * x_).sqrt();
            let recursive = quadratic.pow(&p_ + 1)
                / (x_ * (Atom::num(1) - &c__ * x_).sqrt() * &sqrt_plus);
            rubi_simp(&(quadratic.pow(&p_ + 1) * argument / (Atom::num(2) * &e__ * (&p_ + 1))), x_)
                    + rubi_star(&b__ * sqrt_plus * (Atom::num(1) / (Atom::num(1) + &c__ * x_)).sqrt() / (Atom::num(2) * &e__ * (&p_ + 1)), rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_6854(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, p_, x_);
    rules.push(rubi_rule!(
        order: 6854,
        source: "Int[x_*(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcCsch[c_.*x_]),x_Symbol] :=
          (d+e*x^2)^(p+1)*(a+b*ArcCsch[c*x])/(2*e*(p+1)) -
          b*c*x/(2*e*(p+1)*Sqrt[-c^2*x^2]) \\[Star] Int[(d+e*x^2)^(p+1)/(x*Sqrt[-1-c^2*x^2]),x] /;
        FreeQ[{a,b,c,d,e,p},x] && NeQ[p,-1]",
        desc: "Integration by parts and piecewise constant extraction",
        refs: [],
        pattern: x_ * (d__ + e__ * x_.pow(2)).pow(p_) * (a__ + b__ * (c__ * x_).acsch()),
        with: [d__, e__, p_, a__, b__, c__, x_],
        optional: [d__, e__, p_, a__, b__, c__],
        when: { freeq!([a__, b__, c__, d__, e__, p_], x_) && neq!(p_, -1) },
        rhs: {
            let quadratic = &d__ + &e__ * x_.pow(2);
            let argument = &a__ + &b__ * (&c__ * x_).acsch();
            let recursive = quadratic.pow(&p_ + 1)
                / (x_ * (-Atom::num(1) - c__.pow(2) * x_.pow(2)).sqrt());
            rubi_simp(&(quadratic.pow(&p_ + 1) * argument / (Atom::num(2) * &e__ * (&p_ + 1))), x_)
                    - rubi_star(&b__ * &c__ * x_ / (Atom::num(2)
                            * &e__
                            * (&p_ + 1)
                            * (-(c__.pow(2) * x_.pow(2))).sqrt()), rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_6855(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 6855,
        source: "Int[(f_.*x_)^m_.*(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcSech[c_.*x_]),x_Symbol] :=
          With[{u=IntHide[(f*x)^m*(d+e*x^2)^p,x]},
          (a+b*ArcSech[c*x]) \\[Star] u + b*Sqrt[1+c*x]*Sqrt[1/(1+c*x)] \\[Star] Int[SimplifyIntegrand[u/(x*Sqrt[1-c*x]*Sqrt[1+c*x]),x],x]] /;
        FreeQ[{a,b,c,d,e,f,m,p},x] && (
          IGtQ[p,0] && Not[ILtQ[(m-1)/2,0] && GtQ[m+2*p+3,0]] ||
          IGtQ[(m+1)/2,0] && Not[ILtQ[p,0] && GtQ[m+2*p+3,0]] ||
          ILtQ[(m+2*p+1)/2,0] && Not[ILtQ[(m-1)/2,0]])",
        desc: "Integration by parts and piecewise constant extraction",
        refs: [],
        pattern: (f__ * x_).pow(m_)
            * (d__ + e__ * x_.pow(2)).pow(p_)
            * (a__ + b__ * (c__ * x_).asech()),
        with: [f__, m_, d__, e__, p_, a__, b__, c__, x_],
        optional: [f__, m_, d__, e__, p_, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, p_], x_)
                && (igtq!(p_, 0)
                    && !(iltq!((&m_ - 1) / 2, 0) && gtq!(&m_ + Atom::num(2) * &p_ + 3, 0))
                    || igtq!((&m_ + 1) / 2, 0)
                        && !(iltq!(p_, 0) && gtq!(&m_ + Atom::num(2) * &p_ + 3, 0))
                    || iltq!((&m_ + Atom::num(2) * &p_ + 1) / 2, 0) && !iltq!((&m_ - 1) / 2, 0))
        },
        rhs: {
            let hidden = rubi_int_hide(
                &((&f__ * x_).pow(&m_) * (&d__ + &e__ * x_.pow(2)).pow(&p_)),
                x_,
            ).rubi_rhs();
            let argument = &a__ + &b__ * (&c__ * x_).asech();
            let sqrt_plus = (Atom::num(1) + &c__ * x_).sqrt();
            let recursive = rubi_simplify_integrand(
                &(&hidden
                    / (x_ * (Atom::num(1) - &c__ * x_).sqrt() * &sqrt_plus)),
                x_,
            );
            rubi_star(argument, hidden)
                    + rubi_star(&b__ * sqrt_plus * (Atom::num(1) / (Atom::num(1) + &c__ * x_)).sqrt(), rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_6856(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 6856,
        source: "Int[(f_.*x_)^m_.*(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcCsch[c_.*x_]),x_Symbol] :=
          With[{u=IntHide[(f*x)^m*(d+e*x^2)^p,x]},
          (a+b*ArcCsch[c*x]) \\[Star] u - b*c*x/Sqrt[-c^2*x^2] \\[Star] Int[SimplifyIntegrand[u/(x*Sqrt[-1-c^2*x^2]),x],x]] /;
        FreeQ[{a,b,c,d,e,f,m,p},x] && (
          IGtQ[p,0] && Not[ILtQ[(m-1)/2,0] && GtQ[m+2*p+3,0]] ||
          IGtQ[(m+1)/2,0] && Not[ILtQ[p,0] && GtQ[m+2*p+3,0]] ||
          ILtQ[(m+2*p+1)/2,0] && Not[ILtQ[(m-1)/2,0]] )",
        desc: "Integration by parts and piecewise constant extraction",
        refs: [],
        pattern: (f__ * x_).pow(m_)
            * (d__ + e__ * x_.pow(2)).pow(p_)
            * (a__ + b__ * (c__ * x_).acsch()),
        with: [f__, m_, d__, e__, p_, a__, b__, c__, x_],
        optional: [f__, m_, d__, e__, p_, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, p_], x_)
                && (igtq!(p_, 0)
                    && !(iltq!((&m_ - 1) / 2, 0) && gtq!(&m_ + Atom::num(2) * &p_ + 3, 0))
                    || igtq!((&m_ + 1) / 2, 0)
                        && !(iltq!(p_, 0) && gtq!(&m_ + Atom::num(2) * &p_ + 3, 0))
                    || iltq!((&m_ + Atom::num(2) * &p_ + 1) / 2, 0) && !iltq!((&m_ - 1) / 2, 0))
        },
        rhs: {
            let hidden = rubi_int_hide(
                &((&f__ * x_).pow(&m_) * (&d__ + &e__ * x_.pow(2)).pow(&p_)),
                x_,
            ).rubi_rhs();
            let argument = &a__ + &b__ * (&c__ * x_).acsch();
            let recursive = rubi_simplify_integrand(
                &(&hidden / (x_ * (-Atom::num(1) - c__.pow(2) * x_.pow(2)).sqrt())),
                x_,
            );
            rubi_star(argument, hidden)
                    - rubi_star(&b__ * &c__ * x_ / (-(c__.pow(2) * x_.pow(2))).sqrt(), rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_6857(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6857,
        source: "Int[x_^m_.*(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcSech[c_.*x_])^n_.,x_Symbol] :=
          -Subst[Int[(e+d*x^2)^p*(a+b*ArcCosh[x/c])^n/x^(m+2*(p+1)),x],x,1/x] /;
        FreeQ[{a,b,c,d,e,n},x] && IGtQ[n,0] && IntegersQ[m,p]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [m_, d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [m_, d__, e__, p_, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, n_], x_) && igtq!(n_, 0) && integersq!([m_, p_])
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let transformed = (&e__ + &d__ * sub_atom.pow(2)).pow(&p_)
                * (&a__ + &b__ * (&sub_atom / &c__).acosh()).pow(&n_)
                / sub_atom.pow(&m_ + Atom::num(2) * (&p_ + 1));
            let primitive = rubi_rhs_int(&transformed, substitution_symbol);
            -rubi_subst(&primitive, substitution_symbol, Atom::num(1) / x_)
        },
    ));
}

fn push_rules_rule_6858(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6858,
        source: "Int[x_^m_.*(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcCsch[c_.*x_])^n_.,x_Symbol] :=
          -Subst[Int[(e+d*x^2)^p*(a+b*ArcSinh[x/c])^n/x^(m+2*(p+1)),x],x,1/x] /;
        FreeQ[{a,b,c,d,e,n},x] && IGtQ[n,0] && IntegersQ[m,p]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [m_, d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [m_, d__, e__, p_, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, n_], x_) && igtq!(n_, 0) && integersq!([m_, p_])
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let transformed = (&e__ + &d__ * sub_atom.pow(2)).pow(&p_)
                * (&a__ + &b__ * (&sub_atom / &c__).asinh()).pow(&n_)
                / sub_atom.pow(&m_ + Atom::num(2) * (&p_ + 1));
            let primitive = rubi_rhs_int(&transformed, substitution_symbol);
            -rubi_subst(&primitive, substitution_symbol, Atom::num(1) / x_)
        },
    ));
}

fn push_rules_rule_6859(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6859,
        source: "Int[x_^m_.*(d_.+e_.*x_^2)^p_*(a_.+b_.*ArcSech[c_.*x_])^n_.,x_Symbol] :=
          -Sqrt[x^2]/x \\[Star] Subst[Int[(e+d*x^2)^p*(a+b*ArcCosh[x/c])^n/x^(m+2*(p+1)),x],x,1/x] /;
        FreeQ[{a,b,c,d,e,n},x] && IGtQ[n,0] && EqQ[c^2*d+e,0] && IntegerQ[m] && IntegerQ[p+1/2] && GtQ[e,0] && LtQ[d,0]",
        desc: "Piecewise constant extraction and integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [m_, d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [m_, d__, e__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, n_], x_)
                && igtq!(n_, 0)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && integerq!(m_)
                && integerq!(&p_ + Atom::num(1) / 2)
                && gtq!(e__, 0)
                && ltq!(d__, 0)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let transformed = (&e__ + &d__ * sub_atom.pow(2)).pow(&p_)
                * (&a__ + &b__ * (&sub_atom / &c__).acosh()).pow(&n_)
                / sub_atom.pow(&m_ + Atom::num(2) * (&p_ + 1));
            let primitive = rubi_rhs_int(&transformed, substitution_symbol);
            rubi_star(Atom::num(-1) * x_.pow(2).sqrt(), rubi_subst(&primitive, substitution_symbol, Atom::num(1) / x_)
                    / x_)
        },
    ));
}

fn push_rules_rule_6860(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6860,
        source: "Int[x_^m_.*(d_.+e_.*x_^2)^p_*(a_.+b_.*ArcCsch[c_.*x_])^n_.,x_Symbol] :=
          -Sqrt[x^2]/x \\[Star] Subst[Int[(e+d*x^2)^p*(a+b*ArcSinh[x/c])^n/x^(m+2*(p+1)),x],x,1/x] /;
        FreeQ[{a,b,c,d,e,n},x] && IGtQ[n,0] && EqQ[e-c^2*d,0] && IntegerQ[m] && IntegerQ[p+1/2] && GtQ[e,0] && LtQ[d,0]",
        desc: "Piecewise constant extraction and integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [m_, d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [m_, d__, e__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, n_], x_)
                && igtq!(n_, 0)
                && eqq!(&e__ - c__.pow(2) * &d__, 0)
                && integerq!(m_)
                && integerq!(&p_ + Atom::num(1) / 2)
                && gtq!(e__, 0)
                && ltq!(d__, 0)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let transformed = (&e__ + &d__ * sub_atom.pow(2)).pow(&p_)
                * (&a__ + &b__ * (&sub_atom / &c__).asinh()).pow(&n_)
                / sub_atom.pow(&m_ + Atom::num(2) * (&p_ + 1));
            let primitive = rubi_rhs_int(&transformed, substitution_symbol);
            rubi_star(Atom::num(-1) * x_.pow(2).sqrt(), rubi_subst(&primitive, substitution_symbol, Atom::num(1) / x_)
                    / x_)
        },
    ));
}

fn push_rules_rule_6861(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6861,
        source: "Int[x_^m_.*(d_.+e_.*x_^2)^p_*(a_.+b_.*ArcSech[c_.*x_])^n_.,x_Symbol] :=
          -Sqrt[d+e*x^2]/(x*Sqrt[e+d/x^2]) \\[Star] Subst[Int[(e+d*x^2)^p*(a+b*ArcCosh[x/c])^n/x^(m+2*(p+1)),x],x,1/x] /;
        FreeQ[{a,b,c,d,e,n},x] && IGtQ[n,0] && EqQ[c^2*d+e,0] && IntegerQ[m] && IntegerQ[p+1/2] && Not[GtQ[e,0] && LtQ[d,0]]",
        desc: "Piecewise constant extraction and integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [m_, d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [m_, d__, e__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, n_], x_)
                && igtq!(n_, 0)
                && eqq!(c__.pow(2) * &d__ + &e__, 0)
                && integerq!(m_)
                && integerq!(&p_ + Atom::num(1) / 2)
                && !(gtq!(e__, 0) && ltq!(d__, 0))
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let transformed = (&e__ + &d__ * sub_atom.pow(2)).pow(&p_)
                * (&a__ + &b__ * (&sub_atom / &c__).acosh()).pow(&n_)
                / sub_atom.pow(&m_ + Atom::num(2) * (&p_ + 1));
            let primitive = rubi_rhs_int(&transformed, substitution_symbol);
            let multiplier = -(&d__ + &e__ * x_.pow(2)).sqrt()
                / (x_ * (&e__ + &d__ / x_.pow(2)).sqrt());
            rubi_star(multiplier, rubi_subst(&primitive, substitution_symbol, Atom::num(1) / x_))
        },
    ));
}

fn push_rules_rule_6862(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6862,
        source: "Int[x_^m_.*(d_.+e_.*x_^2)^p_*(a_.+b_.*ArcCsch[c_.*x_])^n_.,x_Symbol] :=
          -Sqrt[d+e*x^2]/(x*Sqrt[e+d/x^2]) \\[Star] Subst[Int[(e+d*x^2)^p*(a+b*ArcSinh[x/c])^n/x^(m+2*(p+1)),x],x,1/x] /;
        FreeQ[{a,b,c,d,e,n},x] && IGtQ[n,0] && EqQ[e-c^2*d,0] && IntegerQ[m] && IntegerQ[p+1/2] && Not[GtQ[e,0] && LtQ[d,0]]",
        desc: "Piecewise constant extraction and integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [m_, d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [m_, d__, e__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, n_], x_)
                && igtq!(n_, 0)
                && eqq!(&e__ - c__.pow(2) * &d__, 0)
                && integerq!(m_)
                && integerq!(&p_ + Atom::num(1) / 2)
                && !(gtq!(e__, 0) && ltq!(d__, 0))
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let transformed = (&e__ + &d__ * sub_atom.pow(2)).pow(&p_)
                * (&a__ + &b__ * (&sub_atom / &c__).asinh()).pow(&n_)
                / sub_atom.pow(&m_ + Atom::num(2) * (&p_ + 1));
            let primitive = rubi_rhs_int(&transformed, substitution_symbol);
            let multiplier = -(&d__ + &e__ * x_.pow(2)).sqrt()
                / (x_ * (&e__ + &d__ / x_.pow(2)).sqrt());
            rubi_star(multiplier, rubi_subst(&primitive, substitution_symbol, Atom::num(1) / x_))
        },
    ));
}

fn push_rules_rule_6863(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, u__, x_);
    rules.push(rubi_rule!(
        order: 6863,
        source: "Int[u_*(a_.+b_.*ArcSech[c_.*x_]),x_Symbol] :=
          With[{v=IntHide[u,x]},
          (a+b*ArcSech[c*x]) \\[Star] v +
          b*Sqrt[1-c^2*x^2]/(c*x*Sqrt[-1+1/(c*x)]*Sqrt[1+1/(c*x)]) \\[Star]
            Int[SimplifyIntegrand[v/(x*Sqrt[1-c^2*x^2]),x],x] /;
         InverseFunctionFreeQ[v,x]] /;
        FreeQ[{a,b,c},x]",
        desc: "Integration by parts and piecewise constant extraction",
        refs: [],
        pattern: u__ * (a__ + b__ * (c__ * x_).asech()),
        with: [u__, a__, b__, c__, x_],
        optional: [a__, b__, c__],
        when: {
            freeq!([a__, b__, c__], x_)
                && rubi_int_hide_inverse_function_free_q(&u__, x_)
        },
        rhs: {
            let v = rubi_int_hide(&u__, x_).rubi_rhs();
            let argument = &a__ + &b__ * (&c__ * x_).asech();
            let recursive = rubi_simplify_integrand(
                &(&v / (x_ * (Atom::num(1) - c__.pow(2) * x_.pow(2)).sqrt())),
                x_,
            );
            rubi_star(argument, v)
                    + rubi_star(&b__ * (Atom::num(1) - c__.pow(2) * x_.pow(2)).sqrt() / (&c__
                            * x_
                            * (-Atom::num(1) + Atom::num(1) / (&c__ * x_)).sqrt()
                            * (Atom::num(1) + Atom::num(1) / (&c__ * x_)).sqrt()), rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_6864(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, u__, x_);
    rules.push(rubi_rule!(
        order: 6864,
        source: "Int[u_*(a_.+b_.*ArcCsch[c_.*x_]),x_Symbol] :=
          With[{v=IntHide[u,x]},
          (a+b*ArcCsch[c*x]) \\[Star] v +
          b/c \\[Star] Int[SimplifyIntegrand[v/(x^2*Sqrt[1+1/(c^2*x^2)]),x],x] /;
         InverseFunctionFreeQ[v,x]] /;
        FreeQ[{a,b,c},x]",
        desc: "Integration by parts",
        refs: [],
        pattern: u__ * (a__ + b__ * (c__ * x_).acsch()),
        with: [u__, a__, b__, c__, x_],
        optional: [a__, b__, c__],
        when: {
            freeq!([a__, b__, c__], x_)
                && rubi_int_hide_inverse_function_free_q(&u__, x_)
        },
        rhs: {
            let v = rubi_int_hide(&u__, x_).rubi_rhs();
            let argument = &a__ + &b__ * (&c__ * x_).acsch();
            let recursive = rubi_simplify_integrand(
                &(&v / (x_.pow(2) * (Atom::num(1) + Atom::num(1) / (c__.pow(2) * x_.pow(2))).sqrt())),
                x_,
            );
            rubi_star(argument, v) + rubi_star(&b__ / c__, rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_6865(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, n_, u__, x_);
    rules.push(rubi_rule!(
        order: 6865,
        source: "Int[u_.*(a_.+b_.*ArcSech[c_.*x_])^n_.,x_Symbol] :=
          Unintegrable[u*(a+b*ArcSech[c*x])^n,x] /;
        FreeQ[{a,b,c,n},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern: u__ * (a__ + b__ * (c__ * x_).asech()).pow(n_),
        with: [u__, a__, b__, c__, n_, x_],
        optional: [u__, a__, b__, c__, n_],
        when: { freeq!([a__, b__, c__, n_], x_) },
        rhs: {
            rubi_unintegrable(
                u__ * (&a__ + &b__ * (&c__ * x_).asech()).pow(&n_),
                x_,
            )
        },
    ));
}

fn push_rules_rule_6866(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, n_, u__, x_);
    rules.push(rubi_rule!(
        order: 6866,
        source: "Int[u_.*(a_.+b_.*ArcCsch[c_.*x_])^n_.,x_Symbol] :=
          Unintegrable[u*(a+b*ArcCsch[c*x])^n,x] /;
        FreeQ[{a,b,c,n},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern: u__ * (a__ + b__ * (c__ * x_).acsch()).pow(n_),
        with: [u__, a__, b__, c__, n_, x_],
        optional: [u__, a__, b__, c__, n_],
        when: { freeq!([a__, b__, c__, n_], x_) },
        rhs: {
            rubi_unintegrable(
                u__ * (&a__ + &b__ * (&c__ * x_).acsch()).pow(&n_),
                x_,
            )
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
    let e__ = symbols.e__;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (d__ + e__ * x_.pow(2)).pow(p_) * (a__ + b__ * (c__ * x_).acsch()).pow(n_)
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (d__ + e__ * x_.pow(2)).pow(p_) * (a__ + b__ * (c__ * x_).asech()).pow(n_)
}

#[inline(never)]
fn rubi_shared_pattern_2(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    x_.pow(m_) * (d__ + e__ * x_.pow(2)).pow(p_) * (a__ + b__ * (c__ * x_).acsch()).pow(n_)
}

#[inline(never)]
fn rubi_shared_pattern_3(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    x_.pow(m_) * (d__ + e__ * x_.pow(2)).pow(p_) * (a__ + b__ * (c__ * x_).asech()).pow(n_)
}
