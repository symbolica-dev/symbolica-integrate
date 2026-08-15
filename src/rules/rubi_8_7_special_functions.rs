use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_7135(rules);
    push_rules_rule_7136(rules);
    push_rules_rule_7137(rules);
    push_rules_rule_7138(rules);
    push_rules_rule_7139(rules);
}

fn push_rules_rule_7135(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, x_);
    rules.push(rubi_rule!(
        order: 7135,
        source: "Int[Zeta[2,a_.+b_.*x_],x_Symbol] :=
          Int[PolyGamma[1,a+b*x],x] /;
        FreeQ[{a,b},x]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: rubi_zeta(Atom::num(2), a__ + b__ * x_),
        with: [a__, b__, x_],
        optional: [a__, b__],
        when: { freeq!([a__, b__], x_) },
        rhs: {
            let argument = &a__ + &b__ * x_;
            rubi_rhs_int(&argument.polygamma(1), x_)
        },
    ));
}

fn push_rules_rule_7136(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, s_, x_);
    rules.push(rubi_rule!(
        order: 7136,
        source: "Int[Zeta[s_,a_.+b_.*x_],x_Symbol] :=
          -Zeta[s-1,a+b*x]/(b*(s-1)) /;
        FreeQ[{a,b,s},x] && NeQ[s,1] && NeQ[s,2]",
        desc: "Primitive rule",
        refs: [],
        pattern: rubi_zeta(Atom::var(s_), a__ + b__ * x_),
        with: [s_, a__, b__, x_],
        optional: [a__, b__],
        when: { freeq!([a__, b__, s_], x_) && neq!(s_, 1) && neq!(s_, 2) },
        rhs: {
            let argument = &a__ + &b__ * x_;
            rubi_simp(&(-rubi_zeta(&s_ - 1, argument) / (&b__ * (&s_ - 1))), x_)
        },
    ));
}

fn push_rules_rule_7137(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, x_);
    rules.push(rubi_rule!(
        order: 7137,
        source: "Int[(c_.+d_.*x_)^m_.*Zeta[2,a_.+b_.*x_],x_Symbol] :=
          Int[(c+d*x)^m*PolyGamma[1,a+b*x],x] /;
        FreeQ[{a,b,c,d},x] && RationalQ[m]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: (c__ + d__ * x_).pow(m_) * rubi_zeta(Atom::num(2), a__ + b__ * x_),
        with: [c__, d__, m_, a__, b__, x_],
        optional: [c__, d__, m_, a__, b__],
        when: { freeq!([a__, b__, c__, d__], x_) && rationalq!(m_) },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let argument = &a__ + &b__ * x_;
            rubi_rhs_int(&(linear.pow(&m_) * argument.polygamma(1)), x_)
        },
    ));
}

fn push_rules_rule_7138(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, s_, x_);
    rules.push(rubi_rule!(
        order: 7138,
        source: "Int[(c_.+d_.*x_)^m_.*Zeta[s_,a_.+b_.*x_],x_Symbol] :=
          -(c+d*x)^m*Zeta[s-1,a+b*x]/(b*(s-1)) +
          d*m/(b*(s-1)) \\[Star] Int[(c+d*x)^(m-1)*Zeta[s-1,a+b*x],x] /;
        FreeQ[{a,b,c,d,s},x] && NeQ[s,1] && NeQ[s,2] && GtQ[m,0]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [c__, d__, m_, s_, a__, b__, x_],
        optional: [c__, d__, m_, a__, b__],
        when: {
            freeq!([a__, b__, c__, d__, s_], x_)
                && neq!(s_, 1)
                && neq!(s_, 2)
                && gtq!(m_, 0)
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let argument = &a__ + &b__ * x_;
            rubi_simp(&(-linear.pow(&m_) * rubi_zeta(&s_ - 1, &argument) / (&b__ * (&s_ - 1))), x_)
                    + rubi_star(&d__ * &m_ / (&b__ * (&s_ - 1)), rubi_rhs_int(&(linear.pow(&m_ - 1) * rubi_zeta(&s_ - 1, argument)), x_))
        },
    ));
}

fn push_rules_rule_7139(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, s_, x_);
    rules.push(rubi_rule!(
        order: 7139,
        source: "Int[(c_.+d_.*x_)^m_.*Zeta[s_,a_.+b_.*x_],x_Symbol] :=
          (c+d*x)^(m+1)*Zeta[s,a+b*x]/(d*(m+1)) +
          b*s/(d*(m+1)) \\[Star] Int[(c+d*x)^(m+1)*Zeta[s+1,a+b*x],x] /;
        FreeQ[{a,b,c,d,s},x] && NeQ[s,1] && NeQ[s,2] && LtQ[m,-1]",
        desc: "Inverted integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [c__, d__, m_, s_, a__, b__, x_],
        optional: [c__, d__, m_, a__, b__],
        when: {
            freeq!([a__, b__, c__, d__, s_], x_)
                && neq!(s_, 1)
                && neq!(s_, 2)
                && ltq!(m_, -1)
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let argument = &a__ + &b__ * x_;
            rubi_simp(&(linear.pow(&m_ + 1) * rubi_zeta(&s_, &argument) / (&d__ * (&m_ + 1))), x_)
                    + rubi_star(&b__ * &s_ / (&d__ * (&m_ + 1)), rubi_rhs_int(&(linear.pow(&m_ + 1) * rubi_zeta(&s_ + 1, argument)), x_))
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
    let m_ = symbols.m_;
    let s_ = symbols.s_;
    let x_ = symbols.x_;
    (c__ + d__ * x_).pow(m_) * rubi_zeta(Atom::var(s_), a__ + b__ * x_)
}
