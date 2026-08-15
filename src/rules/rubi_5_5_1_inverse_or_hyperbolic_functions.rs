use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_5737(rules);
    push_rules_rule_5738(rules);
    push_rules_rule_5739(rules);
    push_rules_rule_5740(rules);
    push_rules_rule_5741(rules);
    push_rules_rule_5742(rules);
    push_rules_rule_5743(rules);
    push_rules_rule_5744(rules);
    push_rules_rule_5745(rules);
    push_rules_rule_5746(rules);
    push_rules_rule_5747(rules);
    push_rules_rule_5748(rules);
    push_rules_rule_5749(rules);
    push_rules_rule_5750(rules);
    push_rules_rule_5751(rules);
    push_rules_rule_5752(rules);
    push_rules_rule_5753(rules);
    push_rules_rule_5754(rules);
    push_rules_rule_5755(rules);
    push_rules_rule_5756(rules);
    push_rules_rule_5757(rules);
    push_rules_rule_5758(rules);
    push_rules_rule_5759(rules);
    push_rules_rule_5760(rules);
    push_rules_rule_5761(rules);
    push_rules_rule_5762(rules);
    push_rules_rule_5763(rules);
    push_rules_rule_5764(rules);
    push_rules_rule_5765(rules);
    push_rules_rule_5766(rules);
    push_rules_rule_5767(rules);
    push_rules_rule_5768(rules);
    push_rules_rule_5769(rules);
    push_rules_rule_5770(rules);
    push_rules_rule_5771(rules);
    push_rules_rule_5772(rules);
}

fn push_rules_rule_5737(rules: &mut Vec<RubiRule>) {
    rubi_symb!(c__, x_);
    rules.push(rubi_rule!(
        order: 5737,
        source: "Int[ArcSec[c_.*x_],x_Symbol] :=
          x*ArcSec[c*x] - 1/c \\[Star] Int[1/(x*Sqrt[1-1/(c^2*x^2)]),x] /;
        FreeQ[c,x]",
        desc: "Integration by parts",
        refs: ["G&R 2.821.2, CRC 445, A&S 4.4.62", "G&R 2.821.1, CRC 446, A&S 4.4.61"],
        pattern: (c__ * x_).asec(),
        with: [c__, x_],
        optional: [c__],
        when: { freeq!(c__, x_) },
        rhs: {
            let argument = &c__ * x_;
            let radical = (Atom::num(1) - Atom::num(1) / (c__.pow(2) * x_.pow(2))).sqrt();
            rubi_simp(&(x_ * argument.asec()), x_)
                    - rubi_star(Atom::num(1) / &c__, rubi_rhs_int(&(Atom::num(1) / (x_ * radical)), x_))
        },
    ));
}

fn push_rules_rule_5738(rules: &mut Vec<RubiRule>) {
    rubi_symb!(c__, x_);
    rules.push(rubi_rule!(
        order: 5738,
        source: "Int[ArcCsc[c_.*x_],x_Symbol] :=
          x*ArcCsc[c*x] + 1/c \\[Star] Int[1/(x*Sqrt[1-1/(c^2*x^2)]),x] /;
        FreeQ[c,x]",
        desc: "Integration by parts",
        refs: ["G&R 2.821.2, CRC 445, A&S 4.4.62", "G&R 2.821.1, CRC 446, A&S 4.4.61"],
        pattern: (c__ * x_).acsc(),
        with: [c__, x_],
        optional: [c__],
        when: { freeq!(c__, x_) },
        rhs: {
            let argument = &c__ * x_;
            let radical = (Atom::num(1) - Atom::num(1) / (c__.pow(2) * x_.pow(2))).sqrt();
            rubi_simp(&(x_ * argument.acsc()), x_)
                    + rubi_star(Atom::num(1) / &c__, rubi_rhs_int(&(Atom::num(1) / (x_ * radical)), x_))
        },
    ));
}

fn push_rules_rule_5739(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, n_, x_);
    rules.push(rubi_rule!(
        order: 5739,
        source: "Int[(a_.+b_.*ArcSec[c_.*x_])^n_,x_Symbol] :=
          1/c \\[Star] Subst[Int[(a+b*x)^n*Sec[x]*Tan[x],x],x,ArcSec[c*x]] /;
        FreeQ[{a,b,c,n},x] && IGtQ[n,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (a__ + b__ * (c__ * x_).asec()).pow(n_),
        with: [a__, b__, c__, n_, x_],
        optional: [a__, b__, c__],
        when: { freeq!([a__, b__, c__, n_], x_) && igtq!(n_, 0) },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let transformed = (&a__ + &b__ * &sub_atom).pow(&n_) * sub_atom.sec() * sub_atom.tan();
            let primitive = rubi_rhs_int(&transformed, substitution_symbol);
            let substituted = rubi_subst(
                &primitive,
                substitution_symbol,
                (&c__ * x_).asec(),
            );
            rubi_star(Atom::num(1) / &c__, substituted)
        },
    ));
}

fn push_rules_rule_5740(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, n_, x_);
    rules.push(rubi_rule!(
        order: 5740,
        source: "Int[(a_.+b_.*ArcCsc[c_.*x_])^n_,x_Symbol] :=
          -1/c \\[Star] Subst[Int[(a+b*x)^n*Csc[x]*Cot[x],x],x,ArcCsc[c*x]] /;
        FreeQ[{a,b,c,n},x] && IGtQ[n,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (a__ + b__ * (c__ * x_).acsc()).pow(n_),
        with: [a__, b__, c__, n_, x_],
        optional: [a__, b__, c__],
        when: { freeq!([a__, b__, c__, n_], x_) && igtq!(n_, 0) },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let transformed = (&a__ + &b__ * &sub_atom).pow(&n_) * sub_atom.csc() * sub_atom.cot();
            let primitive = rubi_rhs_int(&transformed, substitution_symbol);
            let substituted = rubi_subst(
                &primitive,
                substitution_symbol,
                (&c__ * x_).acsc(),
            );
            rubi_star(-Atom::num(1) / &c__, substituted)
        },
    ));
}

fn push_rules_rule_5741(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, x_);
    rules.push(rubi_rule!(
        order: 5741,
        source: "Int[(a_.+b_.*ArcSec[c_.*x_])/x_,x_Symbol] :=
          -Subst[Int[(a+b*ArcCos[x/c])/x,x],x,1/x] /;
        FreeQ[{a,b,c},x]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (a__ + b__ * (c__ * x_).asec()) / x_,
        with: [a__, b__, c__, x_],
        optional: [a__, b__, c__],
        when: { freeq!([a__, b__, c__], x_) },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let transformed = (&a__ + &b__ * (&sub_atom / &c__).acos()) / &sub_atom;
            let primitive = rubi_rhs_int(&transformed, substitution_symbol);
            -rubi_subst(&primitive, substitution_symbol, Atom::num(1) / x_)
        },
    ));
}

fn push_rules_rule_5742(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, x_);
    rules.push(rubi_rule!(
        order: 5742,
        source: "Int[(a_.+b_.*ArcCsc[c_.*x_])/x_,x_Symbol] :=
          -Subst[Int[(a+b*ArcSin[x/c])/x,x],x,1/x] /;
        FreeQ[{a,b,c},x]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (a__ + b__ * (c__ * x_).acsc()) / x_,
        with: [a__, b__, c__, x_],
        optional: [a__, b__, c__],
        when: { freeq!([a__, b__, c__], x_) },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let transformed = (&a__ + &b__ * (&sub_atom / &c__).asin()) / &sub_atom;
            let primitive = rubi_rhs_int(&transformed, substitution_symbol);
            -rubi_subst(&primitive, substitution_symbol, Atom::num(1) / x_)
        },
    ));
}

fn push_rules_rule_5743(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, x_);
    rules.push(rubi_rule!(
        order: 5743,
        source: "Int[(d_.*x_)^m_.*(a_.+b_.*ArcSec[c_.*x_]),x_Symbol] :=
          (d*x)^(m+1)*(a+b*ArcSec[c*x])/(d*(m+1)) -
          b*d/(c*(m+1)) \\[Star] Int[(d*x)^(m-1)/Sqrt[1-1/(c^2*x^2)],x] /;
        FreeQ[{a,b,c,d,m},x] && NeQ[m,-1]",
        desc: "Integration by parts",
        refs: ["CRC 474", "CRC 477"],
        pattern: (d__ * x_).pow(m_) * (a__ + b__ * (c__ * x_).asec()),
        with: [d__, m_, a__, b__, c__, x_],
        optional: [d__, m_, a__, b__, c__],
        when: { freeq!([a__, b__, c__, d__, m_], x_) && neq!(m_, -1) },
        rhs: {
            let scaled_x = &d__ * x_;
            let argument = &a__ + &b__ * (&c__ * x_).asec();
            let radical = (Atom::num(1) - Atom::num(1) / (c__.pow(2) * x_.pow(2))).sqrt();
            rubi_simp(&(scaled_x.pow(&m_ + 1) * argument / (&d__ * (&m_ + 1))), x_)
                    - rubi_star(&b__ * &d__ / (&c__ * (&m_ + 1)), rubi_rhs_int(&(scaled_x.pow(&m_ - 1) / radical), x_))
        },
    ));
}

fn push_rules_rule_5744(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, x_);
    rules.push(rubi_rule!(
        order: 5744,
        source: "Int[(d_.*x_)^m_.*(a_.+b_.*ArcCsc[c_.*x_]),x_Symbol] :=
          (d*x)^(m+1)*(a+b*ArcCsc[c*x])/(d*(m+1)) +
          b*d/(c*(m+1)) \\[Star] Int[(d*x)^(m-1)/Sqrt[1-1/(c^2*x^2)],x] /;
        FreeQ[{a,b,c,d,m},x] && NeQ[m,-1]",
        desc: "Integration by parts",
        refs: ["CRC 474", "CRC 477"],
        pattern: (d__ * x_).pow(m_) * (a__ + b__ * (c__ * x_).acsc()),
        with: [d__, m_, a__, b__, c__, x_],
        optional: [d__, m_, a__, b__, c__],
        when: { freeq!([a__, b__, c__, d__, m_], x_) && neq!(m_, -1) },
        rhs: {
            let scaled_x = &d__ * x_;
            let argument = &a__ + &b__ * (&c__ * x_).acsc();
            let radical = (Atom::num(1) - Atom::num(1) / (c__.pow(2) * x_.pow(2))).sqrt();
            rubi_simp(&(scaled_x.pow(&m_ + 1) * argument / (&d__ * (&m_ + 1))), x_)
                    + rubi_star(&b__ * &d__ / (&c__ * (&m_ + 1)), rubi_rhs_int(&(scaled_x.pow(&m_ - 1) / radical), x_))
        },
    ));
}

fn push_rules_rule_5745(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5745,
        source: "Int[x_^m_.*(a_.+b_.*ArcSec[c_.*x_])^n_,x_Symbol] :=
          1/c^(m+1) \\[Star] Subst[Int[(a+b*x)^n*Sec[x]^(m+1)*Tan[x],x],x,ArcSec[c*x]] /;
        FreeQ[{a,b,c},x] && IntegerQ[n] && IntegerQ[m] && (GtQ[n,0] || LtQ[m,-1])",
        desc: "Integration by substitution",
        refs: [],
        pattern: x_.pow(m_) * (a__ + b__ * (c__ * x_).asec()).pow(n_),
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
                * sub_atom.sec().pow(&m_ + 1)
                * sub_atom.tan();
            let primitive = rubi_rhs_int(&transformed, substitution_symbol);
            let substituted = rubi_subst(
                &primitive,
                substitution_symbol,
                (&c__ * x_).asec(),
            );
            rubi_star(Atom::num(1) / c__.pow(&m_ + 1), substituted)
        },
    ));
}

fn push_rules_rule_5746(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5746,
        source: "Int[x_^m_.*(a_.+b_.*ArcCsc[c_.*x_])^n_,x_Symbol] :=
          -1/c^(m+1) \\[Star] Subst[Int[(a+b*x)^n*Csc[x]^(m+1)*Cot[x],x],x,ArcCsc[c*x]] /;
        FreeQ[{a,b,c},x] && IntegerQ[n] && IntegerQ[m] && (GtQ[n,0] || LtQ[m,-1])",
        desc: "Integration by substitution",
        refs: [],
        pattern: x_.pow(m_) * (a__ + b__ * (c__ * x_).acsc()).pow(n_),
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
                * sub_atom.csc().pow(&m_ + 1)
                * sub_atom.cot();
            let primitive = rubi_rhs_int(&transformed, substitution_symbol);
            let substituted = rubi_subst(
                &primitive,
                substitution_symbol,
                (&c__ * x_).acsc(),
            );
            rubi_star(-Atom::num(1) / c__.pow(&m_ + 1), substituted)
        },
    ));
}

fn push_rules_rule_5747(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 5747,
        source: "Int[(a_.+b_.*ArcSec[c_.*x_])/(d_.+e_.*x_),x_Symbol] :=
          (a+b*ArcSec[c*x])*Log[1+(e-Sqrt[-c^2*d^2+e^2])*E^(I*ArcSec[c*x])/(c*d)]/e +
          (a+b*ArcSec[c*x])*Log[1+(e+Sqrt[-c^2*d^2+e^2])*E^(I*ArcSec[c*x])/(c*d)]/e -
          (a+b*ArcSec[c*x])*Log[1+E^(2*I*ArcSec[c*x])]/e -
          b/(c*e) \\[Star] Int[Log[1+(e-Sqrt[-c^2*d^2+e^2])*E^(I*ArcSec[c*x])/(c*d)]/(x^2*Sqrt[1-1/(c^2*x^2)]),x] -
          b/(c*e) \\[Star] Int[Log[1+(e+Sqrt[-c^2*d^2+e^2])*E^(I*ArcSec[c*x])/(c*d)]/(x^2*Sqrt[1-1/(c^2*x^2)]),x] +
          b/(c*e) \\[Star] Int[Log[1+E^(2*I*ArcSec[c*x])]/(x^2*Sqrt[1-1/(c^2*x^2)]),x] /;
        FreeQ[{a,b,c,d,e},x]",
        desc: "Integration by parts",
        refs: [],
        pattern: (a__ + b__ * (c__ * x_).asec()) / (d__ + e__ * x_),
        with: [a__, b__, c__, d__, e__, x_],
        optional: [a__, b__, c__, d__, e__],
        when: { freeq!([a__, b__, c__, d__, e__], x_) },
        rhs: {
            let i = Atom::i();
            let inverse = (&c__ * x_).asec();
            let argument = &a__ + &b__ * &inverse;
            let discriminant = (-(c__.pow(2)) * d__.pow(2) + e__.pow(2)).sqrt();
            let exp_inverse = (&i * &inverse).exp();
            let log_minus =
                (Atom::num(1) + (&e__ - &discriminant) * &exp_inverse / (&c__ * &d__)).log();
            let log_plus =
                (Atom::num(1) + (&e__ + &discriminant) * &exp_inverse / (&c__ * &d__)).log();
            let log_double = (Atom::num(1) + (Atom::num(2) * &i * inverse).exp()).log();
            let radical = (Atom::num(1) - Atom::num(1) / (c__.pow(2) * x_.pow(2))).sqrt();
            let denominator = x_.pow(2) * radical;
            rubi_simp(&(&argument * &log_minus / &e__), x_)
                    + rubi_simp(&(&argument * &log_plus / &e__), x_)
                    - rubi_simp(&(argument * &log_double / &e__), x_)
                    - rubi_star(&b__ / (&c__ * &e__), rubi_rhs_int(&(log_minus / &denominator), x_))
                    - rubi_star(&b__ / (&c__ * &e__), rubi_rhs_int(&(log_plus / &denominator), x_))
                    + rubi_star(&b__ / (&c__ * &e__), rubi_rhs_int(&(log_double / denominator), x_))
        },
    ));
}

fn push_rules_rule_5748(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 5748,
        source: "Int[(a_.+b_.*ArcCsc[c_.*x_])/(d_.+e_.*x_),x_Symbol] :=
          (a+b*ArcCsc[c*x])*Log[1-I*(e-Sqrt[-c^2*d^2+e^2])*E^(I*ArcCsc[c*x])/(c*d)]/e +
          (a+b*ArcCsc[c*x])*Log[1-I*(e+Sqrt[-c^2*d^2+e^2])*E^(I*ArcCsc[c*x])/(c*d)]/e -
          (a+b*ArcCsc[c*x])*Log[1-E^(2*I*ArcCsc[c*x])]/e +
          b/(c*e) \\[Star] Int[Log[1-I*(e-Sqrt[-c^2*d^2+e^2])*E^(I*ArcCsc[c*x])/(c*d)]/(x^2*Sqrt[1-1/(c^2*x^2)]),x] +
          b/(c*e) \\[Star] Int[Log[1-I*(e+Sqrt[-c^2*d^2+e^2])*E^(I*ArcCsc[c*x])/(c*d)]/(x^2*Sqrt[1-1/(c^2*x^2)]),x] -
          b/(c*e) \\[Star] Int[Log[1-E^(2*I*ArcCsc[c*x])]/(x^2*Sqrt[1-1/(c^2*x^2)]),x] /;
        FreeQ[{a,b,c,d,e},x]",
        desc: "Integration by parts",
        refs: [],
        pattern: (a__ + b__ * (c__ * x_).acsc()) / (d__ + e__ * x_),
        with: [a__, b__, c__, d__, e__, x_],
        optional: [a__, b__, c__, d__, e__],
        when: { freeq!([a__, b__, c__, d__, e__], x_) },
        rhs: {
            let i = Atom::i();
            let inverse = (&c__ * x_).acsc();
            let argument = &a__ + &b__ * &inverse;
            let discriminant = (-(c__.pow(2)) * d__.pow(2) + e__.pow(2)).sqrt();
            let exp_inverse = (&i * &inverse).exp();
            let log_minus =
                (Atom::num(1) - &i * (&e__ - &discriminant) * &exp_inverse / (&c__ * &d__)).log();
            let log_plus =
                (Atom::num(1) - &i * (&e__ + &discriminant) * &exp_inverse / (&c__ * &d__)).log();
            let log_double = (Atom::num(1) - (Atom::num(2) * &i * inverse).exp()).log();
            let radical = (Atom::num(1) - Atom::num(1) / (c__.pow(2) * x_.pow(2))).sqrt();
            let denominator = x_.pow(2) * radical;
            rubi_simp(&(&argument * &log_minus / &e__), x_)
                    + rubi_simp(&(&argument * &log_plus / &e__), x_)
                    - rubi_simp(&(argument * &log_double / &e__), x_)
                    + rubi_star(&b__ / (&c__ * &e__), rubi_rhs_int(&(log_minus / &denominator), x_))
                    + rubi_star(&b__ / (&c__ * &e__), rubi_rhs_int(&(log_plus / &denominator), x_))
                    - rubi_star(&b__ / (&c__ * &e__), rubi_rhs_int(&(log_double / denominator), x_))
        },
    ));
}

fn push_rules_rule_5749(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, x_);
    rules.push(rubi_rule!(
        order: 5749,
        source: "Int[(d_.+e_.*x_)^m_.*(a_.+b_.*ArcSec[c_.*x_]),x_Symbol] :=
          (d+e*x)^(m+1)*(a+b*ArcSec[c*x])/(e*(m+1)) -
          b/(c*e*(m+1)) \\[Star] Int[(d+e*x)^(m+1)/(x^2*Sqrt[1-1/(c^2*x^2)]),x] /;
        FreeQ[{a,b,c,d,e,m},x] && NeQ[m,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern: (d__ + e__ * x_).pow(m_) * (a__ + b__ * (c__ * x_).asec()),
        with: [d__, e__, m_, a__, b__, c__, x_],
        optional: [d__, e__, m_, a__, b__, c__],
        when: { freeq!([a__, b__, c__, d__, e__, m_], x_) && neq!(m_, -1) },
        rhs: {
            let linear = &d__ + &e__ * x_;
            let inverse = (&c__ * x_).asec();
            let argument = &a__ + &b__ * inverse;
            let radical = (Atom::num(1) - Atom::num(1) / (c__.pow(2) * x_.pow(2))).sqrt();
            let recursive = linear.pow(&m_ + 1) / (x_.pow(2) * radical);
            rubi_simp(&(linear.pow(&m_ + 1) * argument / (&e__ * (&m_ + 1))), x_)
                    - rubi_star(&b__ / (&c__ * &e__ * (&m_ + 1)), rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_5750(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, x_);
    rules.push(rubi_rule!(
        order: 5750,
        source: "Int[(d_.+e_.*x_)^m_.*(a_.+b_.*ArcCsc[c_.*x_]),x_Symbol] :=
          (d+e*x)^(m+1)*(a+b*ArcCsc[c*x])/(e*(m+1)) +
          b/(c*e*(m+1)) \\[Star] Int[(d+e*x)^(m+1)/(x^2*Sqrt[1-1/(c^2*x^2)]),x] /;
        FreeQ[{a,b,c,d,e,m},x] && NeQ[m,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern: (d__ + e__ * x_).pow(m_) * (a__ + b__ * (c__ * x_).acsc()),
        with: [d__, e__, m_, a__, b__, c__, x_],
        optional: [d__, e__, m_, a__, b__, c__],
        when: { freeq!([a__, b__, c__, d__, e__, m_], x_) && neq!(m_, -1) },
        rhs: {
            let linear = &d__ + &e__ * x_;
            let inverse = (&c__ * x_).acsc();
            let argument = &a__ + &b__ * inverse;
            let radical = (Atom::num(1) - Atom::num(1) / (c__.pow(2) * x_.pow(2))).sqrt();
            let recursive = linear.pow(&m_ + 1) / (x_.pow(2) * radical);
            rubi_simp(&(linear.pow(&m_ + 1) * argument / (&e__ * (&m_ + 1))), x_)
                    + rubi_star(&b__ / (&c__ * &e__ * (&m_ + 1)), rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_5751(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, p_, x_);
    rules.push(rubi_rule!(
        order: 5751,
        source: "Int[(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcSec[c_.*x_]),x_Symbol] :=
          With[{u=IntHide[(d+e*x^2)^p,x]},
          (a+b*ArcSec[c*x]) \\[Star] u - b*c*x/Sqrt[c^2*x^2] \\[Star] Int[SimplifyIntegrand[u/(x*Sqrt[c^2*x^2-1]),x],x]] /;
        FreeQ[{a,b,c,d,e},x] && (IGtQ[p,0] || ILtQ[p+1/2,0])",
        desc: "Integration by parts and piecewise constant extraction",
        refs: [],
        pattern: (d__ + e__ * x_.pow(2)).pow(p_) * (a__ + b__ * (c__ * x_).asec()),
        with: [d__, e__, p_, a__, b__, c__, x_],
        optional: [d__, e__, p_, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && (igtq!(p_, 0) || iltq!(&p_ + Atom::num(1) / 2, 0))
        },
        rhs: {
            let hidden = rubi_int_hide(&(&d__ + &e__ * x_.pow(2)).pow(&p_), x_).rubi_rhs();
            let argument = &a__ + &b__ * (&c__ * x_).asec();
            let radical = (c__.pow(2) * x_.pow(2) - 1).sqrt();
            let recursive = rubi_simplify_integrand(&(&hidden / (x_ * radical)), x_);
            rubi_star(argument, hidden)
                    - rubi_star(&b__ * &c__ * x_ / (c__.pow(2) * x_.pow(2)).sqrt(), rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_5752(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, p_, x_);
    rules.push(rubi_rule!(
        order: 5752,
        source: "Int[(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcCsc[c_.*x_]),x_Symbol] :=
          With[{u=IntHide[(d+e*x^2)^p,x]},
          (a+b*ArcCsc[c*x]) \\[Star] u + b*c*x/Sqrt[c^2*x^2] \\[Star] Int[SimplifyIntegrand[u/(x*Sqrt[c^2*x^2-1]),x],x]] /;
        FreeQ[{a,b,c,d,e},x] && (IGtQ[p,0] || ILtQ[p+1/2,0])",
        desc: "Integration by parts and piecewise constant extraction",
        refs: [],
        pattern: (d__ + e__ * x_.pow(2)).pow(p_) * (a__ + b__ * (c__ * x_).acsc()),
        with: [d__, e__, p_, a__, b__, c__, x_],
        optional: [d__, e__, p_, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && (igtq!(p_, 0) || iltq!(&p_ + Atom::num(1) / 2, 0))
        },
        rhs: {
            let hidden = rubi_int_hide(&(&d__ + &e__ * x_.pow(2)).pow(&p_), x_).rubi_rhs();
            let argument = &a__ + &b__ * (&c__ * x_).acsc();
            let radical = (c__.pow(2) * x_.pow(2) - 1).sqrt();
            let recursive = rubi_simplify_integrand(&(&hidden / (x_ * radical)), x_);
            rubi_star(argument, hidden)
                    + rubi_star(&b__ * &c__ * x_ / (c__.pow(2) * x_.pow(2)).sqrt(), rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_5753(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5753,
        source: "Int[(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcSec[c_.*x_])^n_.,x_Symbol] :=
          -Subst[Int[(e+d*x^2)^p*(a+b*ArcCos[x/c])^n/x^(2*(p+1)),x],x,1/x] /;
        FreeQ[{a,b,c,d,e,n},x] && IGtQ[n,0] && IntegerQ[p]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [d__, e__, p_, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, n_], x_)
                && igtq!(n_, 0)
                && integerq!(p_)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let transformed = (&e__ + &d__ * sub_atom.pow(2)).pow(&p_)
                * (&a__ + &b__ * (&sub_atom / &c__).acos()).pow(&n_)
                / sub_atom.pow(Atom::num(2) * (&p_ + 1));
            let primitive = rubi_rhs_int(&transformed, substitution_symbol);
            -rubi_subst(&primitive, substitution_symbol, Atom::num(1) / x_)
        },
    ));
}

fn push_rules_rule_5754(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5754,
        source: "Int[(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcCsc[c_.*x_])^n_.,x_Symbol] :=
          -Subst[Int[(e+d*x^2)^p*(a+b*ArcSin[x/c])^n/x^(2*(p+1)),x],x,1/x] /;
        FreeQ[{a,b,c,d,e,n},x] && IGtQ[n,0] && IntegerQ[p]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [d__, e__, p_, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, n_], x_)
                && igtq!(n_, 0)
                && integerq!(p_)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let transformed = (&e__ + &d__ * sub_atom.pow(2)).pow(&p_)
                * (&a__ + &b__ * (&sub_atom / &c__).asin()).pow(&n_)
                / sub_atom.pow(Atom::num(2) * (&p_ + 1));
            let primitive = rubi_rhs_int(&transformed, substitution_symbol);
            -rubi_subst(&primitive, substitution_symbol, Atom::num(1) / x_)
        },
    ));
}

fn push_rules_rule_5755(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5755,
        source: "Int[(d_.+e_.*x_^2)^p_*(a_.+b_.*ArcSec[c_.*x_])^n_.,x_Symbol] :=
          -Sqrt[x^2]/x \\[Star] Subst[Int[(e+d*x^2)^p*(a+b*ArcCos[x/c])^n/x^(2*(p+1)),x],x,1/x] /;
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
                * (&a__ + &b__ * (&sub_atom / &c__).acos()).pow(&n_)
                / sub_atom.pow(Atom::num(2) * (&p_ + 1));
            let primitive = rubi_rhs_int(&transformed, substitution_symbol);
            let substituted =
                rubi_subst(&primitive, substitution_symbol, Atom::num(1) / x_);
            rubi_star(Atom::num(-1) * x_.pow(2).sqrt() / x_, substituted)
        },
    ));
}

fn push_rules_rule_5756(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5756,
        source: "Int[(d_.+e_.*x_^2)^p_*(a_.+b_.*ArcCsc[c_.*x_])^n_.,x_Symbol] :=
          -Sqrt[x^2]/x \\[Star] Subst[Int[(e+d*x^2)^p*(a+b*ArcSin[x/c])^n/x^(2*(p+1)),x],x,1/x] /;
        FreeQ[{a,b,c,d,e,n},x] && IGtQ[n,0] && EqQ[c^2*d+e,0] && IntegerQ[p+1/2] && GtQ[e,0] && LtQ[d,0]",
        desc: "Piecewise constant extraction and integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
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
                * (&a__ + &b__ * (&sub_atom / &c__).asin()).pow(&n_)
                / sub_atom.pow(Atom::num(2) * (&p_ + 1));
            let primitive = rubi_rhs_int(&transformed, substitution_symbol);
            let substituted =
                rubi_subst(&primitive, substitution_symbol, Atom::num(1) / x_);
            rubi_star(Atom::num(-1) * x_.pow(2).sqrt() / x_, substituted)
        },
    ));
}

fn push_rules_rule_5757(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5757,
        source: "Int[(d_.+e_.*x_^2)^p_*(a_.+b_.*ArcSec[c_.*x_])^n_.,x_Symbol] :=
          -Sqrt[d+e*x^2]/(x*Sqrt[e+d/x^2]) \\[Star] Subst[Int[(e+d*x^2)^p*(a+b*ArcCos[x/c])^n/x^(2*(p+1)),x],x,1/x] /;
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
                * (&a__ + &b__ * (&sub_atom / &c__).acos()).pow(&n_)
                / sub_atom.pow(Atom::num(2) * (&p_ + 1));
            let primitive = rubi_rhs_int(&transformed, substitution_symbol);
            let substituted =
                rubi_subst(&primitive, substitution_symbol, Atom::num(1) / x_);
            rubi_star(-(&d__ + &e__ * x_.pow(2)).sqrt()
                    / (x_ * (&e__ + &d__ / x_.pow(2)).sqrt()), substituted)
        },
    ));
}

fn push_rules_rule_5758(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5758,
        source: "Int[(d_.+e_.*x_^2)^p_*(a_.+b_.*ArcCsc[c_.*x_])^n_.,x_Symbol] :=
          -Sqrt[d+e*x^2]/(x*Sqrt[e+d/x^2]) \\[Star] Subst[Int[(e+d*x^2)^p*(a+b*ArcSin[x/c])^n/x^(2*(p+1)),x],x,1/x] /;
        FreeQ[{a,b,c,d,e,n},x] && IGtQ[n,0] && EqQ[c^2*d+e,0] && IntegerQ[p+1/2] && Not[GtQ[e,0] && LtQ[d,0]]",
        desc: "Piecewise constant extraction and integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
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
                * (&a__ + &b__ * (&sub_atom / &c__).asin()).pow(&n_)
                / sub_atom.pow(Atom::num(2) * (&p_ + 1));
            let primitive = rubi_rhs_int(&transformed, substitution_symbol);
            let substituted =
                rubi_subst(&primitive, substitution_symbol, Atom::num(1) / x_);
            rubi_star(-(&d__ + &e__ * x_.pow(2)).sqrt()
                    / (x_ * (&e__ + &d__ / x_.pow(2)).sqrt()), substituted)
        },
    ));
}

fn push_rules_rule_5759(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, p_, x_);
    rules.push(rubi_rule!(
        order: 5759,
        source: "Int[x_*(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcSec[c_.*x_]),x_Symbol] :=
          (d+e*x^2)^(p+1)*(a+b*ArcSec[c*x])/(2*e*(p+1)) -
          b*c*x/(2*e*(p+1)*Sqrt[c^2*x^2]) \\[Star] Int[(d+e*x^2)^(p+1)/(x*Sqrt[c^2*x^2-1]),x] /;
        FreeQ[{a,b,c,d,e,p},x] && NeQ[p,-1]",
        desc: "Integration by parts and piecewise constant extraction",
        refs: [],
        pattern: x_ * (d__ + e__ * x_.pow(2)).pow(p_) * (a__ + b__ * (c__ * x_).asec()),
        with: [d__, e__, p_, a__, b__, c__, x_],
        optional: [d__, e__, p_, a__, b__, c__],
        when: { freeq!([a__, b__, c__, d__, e__, p_], x_) && neq!(p_, -1) },
        rhs: {
            let quadratic = &d__ + &e__ * x_.pow(2);
            let argument = &a__ + &b__ * (&c__ * x_).asec();
            let radical = (c__.pow(2) * x_.pow(2) - 1).sqrt();
            let recursive = quadratic.pow(&p_ + 1) / (x_ * radical);
            rubi_simp(&(quadratic.pow(&p_ + 1) * argument / (Atom::num(2) * &e__ * (&p_ + 1))), x_)
                    - rubi_star(&b__ * &c__ * x_
                            / (Atom::num(2)
                                * &e__
                                * (&p_ + 1)
                                * (c__.pow(2) * x_.pow(2)).sqrt()), rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_5760(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, p_, x_);
    rules.push(rubi_rule!(
        order: 5760,
        source: "Int[x_*(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcCsc[c_.*x_]),x_Symbol] :=
          (d+e*x^2)^(p+1)*(a+b*ArcCsc[c*x])/(2*e*(p+1)) +
          b*c*x/(2*e*(p+1)*Sqrt[c^2*x^2]) \\[Star] Int[(d+e*x^2)^(p+1)/(x*Sqrt[c^2*x^2-1]),x] /;
        FreeQ[{a,b,c,d,e,p},x] && NeQ[p,-1]",
        desc: "Integration by parts and piecewise constant extraction",
        refs: [],
        pattern: x_ * (d__ + e__ * x_.pow(2)).pow(p_) * (a__ + b__ * (c__ * x_).acsc()),
        with: [d__, e__, p_, a__, b__, c__, x_],
        optional: [d__, e__, p_, a__, b__, c__],
        when: { freeq!([a__, b__, c__, d__, e__, p_], x_) && neq!(p_, -1) },
        rhs: {
            let quadratic = &d__ + &e__ * x_.pow(2);
            let argument = &a__ + &b__ * (&c__ * x_).acsc();
            let radical = (c__.pow(2) * x_.pow(2) - 1).sqrt();
            let recursive = quadratic.pow(&p_ + 1) / (x_ * radical);
            rubi_simp(&(quadratic.pow(&p_ + 1) * argument / (Atom::num(2) * &e__ * (&p_ + 1))), x_)
                    + rubi_star(&b__ * &c__ * x_
                            / (Atom::num(2)
                                * &e__
                                * (&p_ + 1)
                                * (c__.pow(2) * x_.pow(2)).sqrt()), rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_5761(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 5761,
        source: "Int[(f_.*x_)^m_.*(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcSec[c_.*x_]),x_Symbol] :=
          With[{u=IntHide[(f*x)^m*(d+e*x^2)^p,x]},
          (a+b*ArcSec[c*x]) \\[Star] u - b*c*x/Sqrt[c^2*x^2] \\[Star] Int[SimplifyIntegrand[u/(x*Sqrt[c^2*x^2-1]),x],x]] /;
        FreeQ[{a,b,c,d,e,f,m,p},x] && (
          IGtQ[p,0] && Not[ILtQ[(m-1)/2,0] && GtQ[m+2*p+3,0]] ||
          IGtQ[(m+1)/2,0] && Not[ILtQ[p,0] && GtQ[m+2*p+3,0]] ||
          ILtQ[(m+2*p+1)/2,0] && Not[ILtQ[(m-1)/2,0]])",
        desc: "Integration by parts and piecewise constant extraction",
        refs: [],
        pattern: (f__ * x_).pow(m_) * (d__ + e__ * x_.pow(2)).pow(p_) * (a__ + b__ * (c__ * x_).asec()),
        with: [f__, m_, d__, e__, p_, a__, b__, c__, x_],
        optional: [f__, m_, d__, e__, p_, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, p_], x_)
                && (igtq!(p_, 0)
                    && !(iltq!((&m_ - 1) / 2, 0) && gtq!(&m_ + Atom::num(2) * &p_ + 3, 0))
                    || igtq!((&m_ + 1) / 2, 0)
                        && !(iltq!(p_, 0) && gtq!(&m_ + Atom::num(2) * &p_ + 3, 0))
                    || iltq!((&m_ + Atom::num(2) * &p_ + 1) / 2, 0)
                        && !iltq!((&m_ - 1) / 2, 0))
        },
        rhs: {
            let hidden = rubi_int_hide(
                &((&f__ * x_).pow(&m_) * (&d__ + &e__ * x_.pow(2)).pow(&p_)),
                x_,
            ).rubi_rhs();
            let argument = &a__ + &b__ * (&c__ * x_).asec();
            let radical = (c__.pow(2) * x_.pow(2) - 1).sqrt();
            let recursive = rubi_simplify_integrand(&(&hidden / (x_ * radical)), x_);
            rubi_star(argument, hidden)
                    - rubi_star(&b__ * &c__ * x_ / (c__.pow(2) * x_.pow(2)).sqrt(), rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_5762(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 5762,
        source: "Int[(f_.*x_)^m_.*(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcCsc[c_.*x_]),x_Symbol] :=
          With[{u=IntHide[(f*x)^m*(d+e*x^2)^p,x]},
          (a+b*ArcCsc[c*x]) \\[Star] u + b*c*x/Sqrt[c^2*x^2] \\[Star] Int[SimplifyIntegrand[u/(x*Sqrt[c^2*x^2-1]),x],x]] /;
        FreeQ[{a,b,c,d,e,f,m,p},x] && (
          IGtQ[p,0] && Not[ILtQ[(m-1)/2,0] && GtQ[m+2*p+3,0]] ||
          IGtQ[(m+1)/2,0] && Not[ILtQ[p,0] && GtQ[m+2*p+3,0]] ||
          ILtQ[(m+2*p+1)/2,0] && Not[ILtQ[(m-1)/2,0]])",
        desc: "Integration by parts and piecewise constant extraction",
        refs: [],
        pattern: (f__ * x_).pow(m_) * (d__ + e__ * x_.pow(2)).pow(p_) * (a__ + b__ * (c__ * x_).acsc()),
        with: [f__, m_, d__, e__, p_, a__, b__, c__, x_],
        optional: [f__, m_, d__, e__, p_, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, p_], x_)
                && (igtq!(p_, 0)
                    && !(iltq!((&m_ - 1) / 2, 0) && gtq!(&m_ + Atom::num(2) * &p_ + 3, 0))
                    || igtq!((&m_ + 1) / 2, 0)
                        && !(iltq!(p_, 0) && gtq!(&m_ + Atom::num(2) * &p_ + 3, 0))
                    || iltq!((&m_ + Atom::num(2) * &p_ + 1) / 2, 0)
                        && !iltq!((&m_ - 1) / 2, 0))
        },
        rhs: {
            let hidden = rubi_int_hide(
                &((&f__ * x_).pow(&m_) * (&d__ + &e__ * x_.pow(2)).pow(&p_)),
                x_,
            ).rubi_rhs();
            let argument = &a__ + &b__ * (&c__ * x_).acsc();
            let radical = (c__.pow(2) * x_.pow(2) - 1).sqrt();
            let recursive = rubi_simplify_integrand(&(&hidden / (x_ * radical)), x_);
            rubi_star(argument, hidden)
                    + rubi_star(&b__ * &c__ * x_ / (c__.pow(2) * x_.pow(2)).sqrt(), rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_5763(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5763,
        source: "Int[x_^m_.*(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcSec[c_.*x_])^n_.,x_Symbol] :=
          -Subst[Int[(e+d*x^2)^p*(a+b*ArcCos[x/c])^n/x^(m+2*(p+1)),x],x,1/x] /;
        FreeQ[{a,b,c,d,e,n},x] && IGtQ[n,0] && IntegerQ[m] && IntegerQ[p]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [m_, d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [m_, d__, e__, p_, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, n_], x_)
                && igtq!(n_, 0)
                && integerq!(m_)
                && integerq!(p_)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let transformed = (&e__ + &d__ * sub_atom.pow(2)).pow(&p_)
                * (&a__ + &b__ * (&sub_atom / &c__).acos()).pow(&n_)
                / sub_atom.pow(&m_ + Atom::num(2) * (&p_ + 1));
            let primitive = rubi_rhs_int(&transformed, substitution_symbol);
            -rubi_subst(&primitive, substitution_symbol, Atom::num(1) / x_)
        },
    ));
}

fn push_rules_rule_5764(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5764,
        source: "Int[x_^m_.*(d_.+e_.*x_^2)^p_.*(a_.+b_.*ArcCsc[c_.*x_])^n_.,x_Symbol] :=
          -Subst[Int[(e+d*x^2)^p*(a+b*ArcSin[x/c])^n/x^(m+2*(p+1)),x],x,1/x] /;
        FreeQ[{a,b,c,d,e,n},x] && IGtQ[n,0] && IntegerQ[m] && IntegerQ[p]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [m_, d__, e__, p_, a__, b__, c__, n_, x_],
        optional: [m_, d__, e__, p_, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, n_], x_)
                && igtq!(n_, 0)
                && integerq!(m_)
                && integerq!(p_)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let transformed = (&e__ + &d__ * sub_atom.pow(2)).pow(&p_)
                * (&a__ + &b__ * (&sub_atom / &c__).asin()).pow(&n_)
                / sub_atom.pow(&m_ + Atom::num(2) * (&p_ + 1));
            let primitive = rubi_rhs_int(&transformed, substitution_symbol);
            -rubi_subst(&primitive, substitution_symbol, Atom::num(1) / x_)
        },
    ));
}

fn push_rules_rule_5765(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5765,
        source: "Int[x_^m_.*(d_.+e_.*x_^2)^p_*(a_.+b_.*ArcSec[c_.*x_])^n_.,x_Symbol] :=
          -Sqrt[x^2]/x \\[Star] Subst[Int[(e+d*x^2)^p*(a+b*ArcCos[x/c])^n/x^(m+2*(p+1)),x],x,1/x] /;
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
                * (&a__ + &b__ * (&sub_atom / &c__).acos()).pow(&n_)
                / sub_atom.pow(&m_ + Atom::num(2) * (&p_ + 1));
            let primitive = rubi_rhs_int(&transformed, substitution_symbol);
            let substituted =
                rubi_subst(&primitive, substitution_symbol, Atom::num(1) / x_);
            rubi_star(Atom::num(-1) * x_.pow(2).sqrt() / x_, substituted)
        },
    ));
}

fn push_rules_rule_5766(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5766,
        source: "Int[x_^m_.*(d_.+e_.*x_^2)^p_*(a_.+b_.*ArcCsc[c_.*x_])^n_.,x_Symbol] :=
          -Sqrt[x^2]/x \\[Star] Subst[Int[(e+d*x^2)^p*(a+b*ArcSin[x/c])^n/x^(m+2*(p+1)),x],x,1/x] /;
        FreeQ[{a,b,c,d,e,n},x] && IGtQ[n,0] && EqQ[c^2*d+e,0] && IntegerQ[m] && IntegerQ[p+1/2] && GtQ[e,0] && LtQ[d,0]",
        desc: "Piecewise constant extraction and integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
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
                * (&a__ + &b__ * (&sub_atom / &c__).asin()).pow(&n_)
                / sub_atom.pow(&m_ + Atom::num(2) * (&p_ + 1));
            let primitive = rubi_rhs_int(&transformed, substitution_symbol);
            let substituted =
                rubi_subst(&primitive, substitution_symbol, Atom::num(1) / x_);
            rubi_star(Atom::num(-1) * x_.pow(2).sqrt() / x_, substituted)
        },
    ));
}

fn push_rules_rule_5767(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5767,
        source: "Int[x_^m_.*(d_.+e_.*x_^2)^p_*(a_.+b_.*ArcSec[c_.*x_])^n_.,x_Symbol] :=
          -Sqrt[d+e*x^2]/(x*Sqrt[e+d/x^2]) \\[Star] Subst[Int[(e+d*x^2)^p*(a+b*ArcCos[x/c])^n/x^(m+2*(p+1)),x],x,1/x] /;
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
                * (&a__ + &b__ * (&sub_atom / &c__).acos()).pow(&n_)
                / sub_atom.pow(&m_ + Atom::num(2) * (&p_ + 1));
            let primitive = rubi_rhs_int(&transformed, substitution_symbol);
            let substituted =
                rubi_subst(&primitive, substitution_symbol, Atom::num(1) / x_);
            rubi_star(-(&d__ + &e__ * x_.pow(2)).sqrt()
                    / (x_ * (&e__ + &d__ / x_.pow(2)).sqrt()), substituted)
        },
    ));
}

fn push_rules_rule_5768(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5768,
        source: "Int[x_^m_.*(d_.+e_.*x_^2)^p_*(a_.+b_.*ArcCsc[c_.*x_])^n_.,x_Symbol] :=
          -Sqrt[d+e*x^2]/(x*Sqrt[e+d/x^2]) \\[Star] Subst[Int[(e+d*x^2)^p*(a+b*ArcSin[x/c])^n/x^(m+2*(p+1)),x],x,1/x] /;
        FreeQ[{a,b,c,d,e,n},x] && IGtQ[n,0] && EqQ[c^2*d+e,0] && IntegerQ[m] && IntegerQ[p+1/2] && Not[GtQ[e,0] && LtQ[d,0]]",
        desc: "Piecewise constant extraction and integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
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
                * (&a__ + &b__ * (&sub_atom / &c__).asin()).pow(&n_)
                / sub_atom.pow(&m_ + Atom::num(2) * (&p_ + 1));
            let primitive = rubi_rhs_int(&transformed, substitution_symbol);
            let substituted =
                rubi_subst(&primitive, substitution_symbol, Atom::num(1) / x_);
            rubi_star(-(&d__ + &e__ * x_.pow(2)).sqrt()
                    / (x_ * (&e__ + &d__ / x_.pow(2)).sqrt()), substituted)
        },
    ));
}

fn push_rules_rule_5769(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, u__, x_);
    rules.push(rubi_rule!(
        order: 5769,
        source: "Int[u_*(a_.+b_.*ArcSec[c_.*x_]),x_Symbol] :=
          With[{v=IntHide[u,x]},
          (a+b*ArcSec[c*x]) \\[Star] v -
          b/c \\[Star] Int[SimplifyIntegrand[v/(x^2*Sqrt[1-1/(c^2*x^2)]),x],x] /;
         InverseFunctionFreeQ[v,x]] /;
        FreeQ[{a,b,c},x]",
        desc: "Integration by parts",
        refs: [],
        pattern: u__ * (a__ + b__ * (c__ * x_).asec()),
        with: [u__, a__, b__, c__, x_],
        optional: [a__, b__, c__],
        when: {
            freeq!([a__, b__, c__], x_)
                && rubi_int_hide_inverse_function_free_q(&u__, x_)
        },
        rhs: {
            let hidden = rubi_int_hide(&u__, x_).rubi_rhs();
            let argument = &a__ + &b__ * (&c__ * x_).asec();
            let radical = (Atom::num(1) - Atom::num(1) / (c__.pow(2) * x_.pow(2))).sqrt();
            let recursive = rubi_simplify_integrand(&(&hidden / (x_.pow(2) * radical)), x_);
            rubi_star(argument, hidden)
                    - rubi_star(&b__ / &c__, rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_5770(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, u__, x_);
    rules.push(rubi_rule!(
        order: 5770,
        source: "Int[u_*(a_.+b_.*ArcCsc[c_.*x_]),x_Symbol] :=
          With[{v=IntHide[u,x]},
          (a+b*ArcCsc[c*x]) \\[Star] v +
          b/c \\[Star] Int[SimplifyIntegrand[v/(x^2*Sqrt[1-1/(c^2*x^2)]),x],x] /;
         InverseFunctionFreeQ[v,x]] /;
        FreeQ[{a,b,c},x]",
        desc: "Integration by parts",
        refs: [],
        pattern: u__ * (a__ + b__ * (c__ * x_).acsc()),
        with: [u__, a__, b__, c__, x_],
        optional: [a__, b__, c__],
        when: {
            freeq!([a__, b__, c__], x_)
                && rubi_int_hide_inverse_function_free_q(&u__, x_)
        },
        rhs: {
            let hidden = rubi_int_hide(&u__, x_).rubi_rhs();
            let argument = &a__ + &b__ * (&c__ * x_).acsc();
            let radical = (Atom::num(1) - Atom::num(1) / (c__.pow(2) * x_.pow(2))).sqrt();
            let recursive = rubi_simplify_integrand(&(&hidden / (x_.pow(2) * radical)), x_);
            rubi_star(argument, hidden)
                    + rubi_star(&b__ / &c__, rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_5771(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, n_, u__, x_);
    rules.push(rubi_rule!(
        order: 5771,
        source: "Int[u_.*(a_.+b_.*ArcSec[c_.*x_])^n_.,x_Symbol] :=
          Unintegrable[u*(a+b*ArcSec[c*x])^n,x] /;
        FreeQ[{a,b,c,n},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern: u__ * (a__ + b__ * (c__ * x_).asec()).pow(n_),
        with: [u__, a__, b__, c__, n_, x_],
        optional: [u__, a__, b__, c__, n_],
        when: { freeq!([a__, b__, c__, n_], x_) },
        rhs: {
            rubi_unintegrable(
                u__ * (&a__ + &b__ * (&c__ * x_).asec()).pow(&n_),
                x_,
            )
        },
    ));
}

fn push_rules_rule_5772(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, n_, u__, x_);
    rules.push(rubi_rule!(
        order: 5772,
        source: "Int[u_.*(a_.+b_.*ArcCsc[c_.*x_])^n_.,x_Symbol] :=
          Unintegrable[u*(a+b*ArcCsc[c*x])^n,x] /;
        FreeQ[{a,b,c,n},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern: u__ * (a__ + b__ * (c__ * x_).acsc()).pow(n_),
        with: [u__, a__, b__, c__, n_, x_],
        optional: [u__, a__, b__, c__, n_],
        when: { freeq!([a__, b__, c__, n_], x_) },
        rhs: {
            rubi_unintegrable(
                u__ * (&a__ + &b__ * (&c__ * x_).acsc()).pow(&n_),
                x_,
            )
        },
    ));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn downvalues_5737_through_5742_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .filter(|order| (5737..=5742).contains(order))
            .collect::<Vec<_>>();
        assert_eq!(orders, (5737..=5742).collect::<Vec<_>>());
    }

    #[test]
    fn downvalues_5743_through_5772_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .filter(|order| (5743..=5772).contains(order))
            .collect::<Vec<_>>();
        assert_eq!(orders, (5743..=5772).collect::<Vec<_>>());
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
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (d__ + e__ * x_.pow(2)).pow(p_) * (a__ + b__ * (c__ * x_).acsc()).pow(n_)
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
    (d__ + e__ * x_.pow(2)).pow(p_) * (a__ + b__ * (c__ * x_).asec()).pow(n_)
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
    x_.pow(m_) * (d__ + e__ * x_.pow(2)).pow(p_) * (a__ + b__ * (c__ * x_).acsc()).pow(n_)
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
    x_.pow(m_) * (d__ + e__ * x_.pow(2)).pow(p_) * (a__ + b__ * (c__ * x_).asec()).pow(n_)
}
