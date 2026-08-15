use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_6972(rules);
    push_rules_rule_6973(rules);
    push_rules_rule_6974(rules);
    push_rules_rule_6975(rules);
    push_rules_rule_6976(rules);
    push_rules_rule_6977(rules);
    push_rules_rule_6978(rules);
    push_rules_rule_6979(rules);
    push_rules_rule_6980(rules);
    push_rules_rule_6981(rules);
    push_rules_rule_6982(rules);
    push_rules_rule_6983(rules);
    push_rules_rule_6984(rules);
    push_rules_rule_6985(rules);
    push_rules_rule_6986(rules);
    push_rules_rule_6987(rules);
    push_rules_rule_6988(rules);
    push_rules_rule_6989(rules);
    push_rules_rule_6990(rules);
    push_rules_rule_6991(rules);
    push_rules_rule_6992(rules);
    push_rules_rule_6993(rules);
    push_rules_rule_6994(rules);
    push_rules_rule_6995(rules);
    push_rules_rule_6996(rules);
    push_rules_rule_6997(rules);
    push_rules_rule_6998(rules);
    push_rules_rule_6999(rules);
    push_rules_rule_7000(rules);
    push_rules_rule_7001(rules);
    push_rules_rule_7002(rules);
    push_rules_rule_7003(rules);
    push_rules_rule_7004(rules);
    push_rules_rule_7005(rules);
    push_rules_rule_7006(rules);
    push_rules_rule_7007(rules);
    push_rules_rule_7008(rules);
    push_rules_rule_7009(rules);
    push_rules_rule_7010(rules);
    push_rules_rule_7011(rules);
    push_rules_rule_7012(rules);
    push_rules_rule_7013(rules);
    push_rules_rule_7014(rules);
    push_rules_rule_7015(rules);
    push_rules_rule_7016(rules);
    push_rules_rule_7017(rules);
    push_rules_rule_7018(rules);
    push_rules_rule_7019(rules);
    push_rules_rule_7020(rules);
    push_rules_rule_7021(rules);
    push_rules_rule_7022(rules);
    push_rules_rule_7023(rules);
    push_rules_rule_7024(rules);
    push_rules_rule_7025(rules);
    push_rules_rule_7026(rules);
}

fn push_rules_rule_6972(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, x_);
    rules.push(rubi_rule!(
        order: 6972,
        source: "Int[FresnelS[a_.+b_.*x_],x_Symbol] :=
          (a+b*x)*FresnelS[a+b*x]/b + Cos[Pi/2*(a+b*x)^2]/(b*Pi) /;
        FreeQ[{a,b},x]",
        desc: "Integration by parts",
        refs: [],
        pattern: rubi_fresnel_s(a__ + b__ * x_),
        with: [a__, b__, x_],
        optional: [a__, b__],
        when: { freeq!([a__, b__], x_) },
        rhs: {
            let argument = &a__ + &b__ * x_;
            let pi = Atom::var(Symbol::PI);
            rubi_simp(&(&argument * rubi_fresnel_s(&argument) / &b__), x_) + rubi_simp(&(((&pi / 2) * argument.pow(2)).cos() / (&b__ * pi)), x_)
        },
    ));
}

fn push_rules_rule_6973(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, x_);
    rules.push(rubi_rule!(
        order: 6973,
        source: "Int[FresnelC[a_.+b_.*x_],x_Symbol] :=
          (a+b*x)*FresnelC[a+b*x]/b - Sin[Pi/2*(a+b*x)^2]/(b*Pi) /;
        FreeQ[{a,b},x]",
        desc: "Integration by parts",
        refs: [],
        pattern: rubi_fresnel_c(a__ + b__ * x_),
        with: [a__, b__, x_],
        optional: [a__, b__],
        when: { freeq!([a__, b__], x_) },
        rhs: {
            let argument = &a__ + &b__ * x_;
            let pi = Atom::var(Symbol::PI);
            rubi_simp(&(&argument * rubi_fresnel_c(&argument) / &b__), x_) - rubi_simp(&(((&pi / 2) * argument.pow(2)).sin() / (&b__ * pi)), x_)
        },
    ));
}

fn push_rules_rule_6974(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, x_);
    rules.push(rubi_rule!(
        order: 6974,
        source: "Int[FresnelS[a_.+b_.*x_]^2,x_Symbol] :=
          (a+b*x)*FresnelS[a+b*x]^2/b -
          2 \\[Star] Int[(a+b*x)*Sin[Pi/2*(a+b*x)^2]*FresnelS[a+b*x],x] /;
        FreeQ[{a,b},x]",
        desc: "Integration by parts",
        refs: [],
        pattern: rubi_fresnel_s(a__ + b__ * x_).pow(2),
        with: [a__, b__, x_],
        optional: [a__, b__],
        when: { freeq!([a__, b__], x_) },
        rhs: {
            let argument = &a__ + &b__ * x_;
            let pi = Atom::var(Symbol::PI);
            rubi_simp(&(&argument * rubi_fresnel_s(&argument).pow(2) / &b__), x_)
                    - rubi_star(Atom::num(2), rubi_rhs_int(&(&argument * ((pi / 2) * argument.pow(2)).sin() * rubi_fresnel_s(argument)), x_))
        },
    ));
}

fn push_rules_rule_6975(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, x_);
    rules.push(rubi_rule!(
        order: 6975,
        source: "Int[FresnelC[a_.+b_.*x_]^2,x_Symbol] :=
          (a+b*x)*FresnelC[a+b*x]^2/b -
          2 \\[Star] Int[(a+b*x)*Cos[Pi/2*(a+b*x)^2]*FresnelC[a+b*x],x] /;
        FreeQ[{a,b},x]",
        desc: "Integration by parts",
        refs: [],
        pattern: rubi_fresnel_c(a__ + b__ * x_).pow(2),
        with: [a__, b__, x_],
        optional: [a__, b__],
        when: { freeq!([a__, b__], x_) },
        rhs: {
            let argument = &a__ + &b__ * x_;
            let pi = Atom::var(Symbol::PI);
            rubi_simp(&(&argument * rubi_fresnel_c(&argument).pow(2) / &b__), x_)
                    - rubi_star(Atom::num(2), rubi_rhs_int(&(&argument * ((pi / 2) * argument.pow(2)).cos() * rubi_fresnel_c(argument)), x_))
        },
    ));
}

fn push_rules_rule_6976(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, n_, x_);
    rules.push(rubi_rule!(
        order: 6976,
        source: "Int[FresnelS[a_.+b_.*x_]^n_,x_Symbol] :=
          Unintegrable[FresnelS[a+b*x]^n,x] /;
        FreeQ[{a,b,n},x] && NeQ[n,1] && NeQ[n,2]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern: rubi_fresnel_s(a__ + b__ * x_).pow(n_),
        with: [a__, b__, n_, x_],
        optional: [a__, b__],
        when: { freeq!([a__, b__, n_], x_) && neq!(n_, 1) && neq!(n_, 2) },
        rhs: {
            let argument = &a__ + &b__ * x_;
            rubi_unintegrable(rubi_fresnel_s(argument).pow(&n_), x_)
        },
    ));
}

fn push_rules_rule_6977(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, n_, x_);
    rules.push(rubi_rule!(
        order: 6977,
        source: "Int[FresnelC[a_.+b_.*x_]^n_,x_Symbol] :=
          Unintegrable[FresnelC[a+b*x]^n,x] /;
        FreeQ[{a,b,n},x] && NeQ[n,1] && NeQ[n,2]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern: rubi_fresnel_c(a__ + b__ * x_).pow(n_),
        with: [a__, b__, n_, x_],
        optional: [a__, b__],
        when: { freeq!([a__, b__, n_], x_) && neq!(n_, 1) && neq!(n_, 2) },
        rhs: {
            let argument = &a__ + &b__ * x_;
            rubi_unintegrable(rubi_fresnel_c(argument).pow(&n_), x_)
        },
    ));
}

fn push_rules_rule_6978(rules: &mut Vec<RubiRule>) {
    rubi_symb!(b__, x_);
    rules.push(rubi_rule!(
        order: 6978,
        source: "Int[FresnelS[b_.*x_]/x_,x_Symbol] :=
          (1+I)/4 \\[Star] Int[Erf[Sqrt[Pi]/2*(1+I)*b*x]/x,x] + (1-I)/4 \\[Star] Int[Erf[Sqrt[Pi]/2*(1-I)*b*x]/x,x] /;
        FreeQ[b,x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: rubi_fresnel_s(b__ * x_) / x_,
        with: [b__, x_],
        optional: [b__],
        when: { freeq!(b__, x_) },
        rhs: {
            let i = Atom::i();
            let pi = Atom::var(Symbol::PI);
            let plus = pi.sqrt() * (Atom::num(1) + &i) * &b__ * x_ / 2;
            let minus = pi.sqrt() * (Atom::num(1) - &i) * &b__ * x_ / 2;
            rubi_star(Atom::num(1) + &i, rubi_rhs_int(&(plus.erf() / x_), x_) / 4)
                    + rubi_star(Atom::num(1) - i, rubi_rhs_int(&(minus.erf() / x_), x_) / 4)
        },
    ));
}

fn push_rules_rule_6979(rules: &mut Vec<RubiRule>) {
    rubi_symb!(b__, x_);
    rules.push(rubi_rule!(
        order: 6979,
        source: "Int[FresnelC[b_.*x_]/x_,x_Symbol] :=
          (1-I)/4 \\[Star] Int[Erf[Sqrt[Pi]/2*(1+I)*b*x]/x,x] + (1+I)/4 \\[Star] Int[Erf[Sqrt[Pi]/2*(1-I)*b*x]/x,x] /;
        FreeQ[b,x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: rubi_fresnel_c(b__ * x_) / x_,
        with: [b__, x_],
        optional: [b__],
        when: { freeq!(b__, x_) },
        rhs: {
            let i = Atom::i();
            let pi = Atom::var(Symbol::PI);
            let plus = pi.sqrt() * (Atom::num(1) + &i) * &b__ * x_ / 2;
            let minus = pi.sqrt() * (Atom::num(1) - &i) * &b__ * x_ / 2;
            rubi_star(Atom::num(1) - &i, rubi_rhs_int(&(plus.erf() / x_), x_) / 4)
                    + rubi_star(Atom::num(1) + i, rubi_rhs_int(&(minus.erf() / x_), x_) / 4)
        },
    ));
}

fn push_rules_rule_6980(rules: &mut Vec<RubiRule>) {
    rubi_symb!(b__, d__, m_, x_);
    rules.push(rubi_rule!(
        order: 6980,
        source: "Int[(d_.*x_)^m_.*FresnelS[b_.*x_],x_Symbol] :=
          (d*x)^(m+1)*FresnelS[b*x]/(d*(m+1)) - b/(d*(m+1)) \\[Star] Int[(d*x)^(m+1)*Sin[Pi/2*b^2*x^2],x] /;
        FreeQ[{b,d,m},x] && NeQ[m,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern: (d__ * x_).pow(m_) * rubi_fresnel_s(b__ * x_),
        with: [d__, m_, b__, x_],
        optional: [d__, m_, b__],
        when: { freeq!([b__, d__, m_], x_) && neq!(m_, -1) },
        rhs: {
            let pi = Atom::var(Symbol::PI);
            let scaled = &d__ * x_;
            let argument = &b__ * x_;
            rubi_simp(&(scaled.pow(&m_ + 1) * rubi_fresnel_s(argument) / (&d__ * (&m_ + 1))), x_)
                    - rubi_star(&b__, rubi_rhs_int(&(scaled.pow(&m_ + 1) * ((&pi / 2) * b__.pow(2) * x_.pow(2)).sin()), x_)
                        / (&d__ * (&m_ + 1)))
        },
    ));
}

fn push_rules_rule_6981(rules: &mut Vec<RubiRule>) {
    rubi_symb!(b__, d__, m_, x_);
    rules.push(rubi_rule!(
        order: 6981,
        source: "Int[(d_.*x_)^m_.*FresnelC[b_.*x_],x_Symbol] :=
          (d*x)^(m+1)*FresnelC[b*x]/(d*(m+1)) - b/(d*(m+1)) \\[Star] Int[(d*x)^(m+1)*Cos[Pi/2*b^2*x^2],x] /;
        FreeQ[{b,d,m},x] && NeQ[m,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern: (d__ * x_).pow(m_) * rubi_fresnel_c(b__ * x_),
        with: [d__, m_, b__, x_],
        optional: [d__, m_, b__],
        when: { freeq!([b__, d__, m_], x_) && neq!(m_, -1) },
        rhs: {
            let pi = Atom::var(Symbol::PI);
            let scaled = &d__ * x_;
            let argument = &b__ * x_;
            rubi_simp(&(scaled.pow(&m_ + 1) * rubi_fresnel_c(argument) / (&d__ * (&m_ + 1))), x_)
                    - rubi_star(&b__, rubi_rhs_int(&(scaled.pow(&m_ + 1) * ((&pi / 2) * b__.pow(2) * x_.pow(2)).cos()), x_)
                        / (&d__ * (&m_ + 1)))
        },
    ));
}

fn push_rules_rule_6982(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, x_);
    rules.push(rubi_rule!(
        order: 6982,
        source: "Int[(c_.+d_.*x_)^m_.*FresnelS[a_.+b_.*x_],x_Symbol] :=
          (c+d*x)^(m+1)*FresnelS[a+b*x]/(d*(m+1)) -
          b/(d*(m+1)) \\[Star] Int[(c+d*x)^(m+1)*Sin[Pi/2*(a+b*x)^2],x] /;
        FreeQ[{a,b,c,d},x] && IGtQ[m,0]",
        desc: "Integration by parts",
        refs: [],
        pattern: (c__ + d__ * x_).pow(m_) * rubi_fresnel_s(a__ + b__ * x_),
        with: [c__, d__, m_, a__, b__, x_],
        optional: [c__, d__, m_, a__, b__],
        when: { freeq!([a__, b__, c__, d__], x_) && igtq!(m_, 0) },
        rhs: {
            let pi = Atom::var(Symbol::PI);
            let linear = &c__ + &d__ * x_;
            let argument = &a__ + &b__ * x_;
            rubi_simp(&(linear.pow(&m_ + 1) * rubi_fresnel_s(&argument) / (&d__ * (&m_ + 1))), x_)
                    - rubi_star(b__, rubi_rhs_int(&(linear.pow(&m_ + 1) * ((&pi / 2) * argument.pow(2)).sin()), x_)
                        / (&d__ * (&m_ + 1)))
        },
    ));
}

fn push_rules_rule_6983(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, x_);
    rules.push(rubi_rule!(
        order: 6983,
        source: "Int[(c_.+d_.*x_)^m_.*FresnelC[a_.+b_.*x_],x_Symbol] :=
          (c+d*x)^(m+1)*FresnelC[a+b*x]/(d*(m+1)) -
          b/(d*(m+1)) \\[Star] Int[(c+d*x)^(m+1)*Cos[Pi/2*(a+b*x)^2],x] /;
        FreeQ[{a,b,c,d},x] && IGtQ[m,0]",
        desc: "Integration by parts",
        refs: [],
        pattern: (c__ + d__ * x_).pow(m_) * rubi_fresnel_c(a__ + b__ * x_),
        with: [c__, d__, m_, a__, b__, x_],
        optional: [c__, d__, m_, a__, b__],
        when: { freeq!([a__, b__, c__, d__], x_) && igtq!(m_, 0) },
        rhs: {
            let pi = Atom::var(Symbol::PI);
            let linear = &c__ + &d__ * x_;
            let argument = &a__ + &b__ * x_;
            rubi_simp(&(linear.pow(&m_ + 1) * rubi_fresnel_c(&argument) / (&d__ * (&m_ + 1))), x_)
                    - rubi_star(b__, rubi_rhs_int(&(linear.pow(&m_ + 1) * ((&pi / 2) * argument.pow(2)).cos()), x_)
                        / (&d__ * (&m_ + 1)))
        },
    ));
}

fn push_rules_rule_6984(rules: &mut Vec<RubiRule>) {
    rubi_symb!(b__, m_, x_);
    rules.push(rubi_rule!(
        order: 6984,
        source: "Int[x_^m_.*FresnelS[b_.*x_]^2,x_Symbol] :=
          x^(m+1)*FresnelS[b*x]^2/(m+1) -
          2*b/(m+1) \\[Star] Int[x^(m+1)*Sin[Pi/2*b^2*x^2]*FresnelS[b*x],x] /;
        FreeQ[b,x] && IntegerQ[m] && NeQ[m,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern: x_.pow(m_) * rubi_fresnel_s(b__ * x_).pow(2),
        with: [m_, b__, x_],
        optional: [m_, b__],
        when: { freeq!(b__, x_) && integerq!(m_) && neq!(m_, -1) },
        rhs: {
            let pi = Atom::var(Symbol::PI);
            let argument = &b__ * x_;
            rubi_simp(&(x_.pow(&m_ + 1) * rubi_fresnel_s(&argument).pow(2) / (&m_ + 1)), x_)
                    - rubi_star(Atom::num(2) * &b__ / (&m_ + 1), rubi_rhs_int(&(x_.pow(&m_ + 1) * ((&pi / 2) * b__.pow(2) * x_.pow(2)).sin() * rubi_fresnel_s(argument)), x_))
        },
    ));
}

fn push_rules_rule_6985(rules: &mut Vec<RubiRule>) {
    rubi_symb!(b__, m_, x_);
    rules.push(rubi_rule!(
        order: 6985,
        source: "Int[x_^m_.*FresnelC[b_.*x_]^2,x_Symbol] :=
          x^(m+1)*FresnelC[b*x]^2/(m+1) -
          2*b/(m+1) \\[Star] Int[x^(m+1)*Cos[Pi/2*b^2*x^2]*FresnelC[b*x],x] /;
        FreeQ[b,x] && IntegerQ[m] && NeQ[m,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern: x_.pow(m_) * rubi_fresnel_c(b__ * x_).pow(2),
        with: [m_, b__, x_],
        optional: [m_, b__],
        when: { freeq!(b__, x_) && integerq!(m_) && neq!(m_, -1) },
        rhs: {
            let pi = Atom::var(Symbol::PI);
            let argument = &b__ * x_;
            rubi_simp(&(x_.pow(&m_ + 1) * rubi_fresnel_c(&argument).pow(2) / (&m_ + 1)), x_)
                    - rubi_star(Atom::num(2) * &b__ / (&m_ + 1), rubi_rhs_int(&(x_.pow(&m_ + 1) * ((&pi / 2) * b__.pow(2) * x_.pow(2)).cos() * rubi_fresnel_c(argument)), x_))
        },
    ));
}

fn push_rules_rule_6986(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a_, b__, c__, d__, m_, x_);
    rules.push(rubi_rule!(
        order: 6986,
        source: "Int[(c_.+d_.*x_)^m_.*FresnelS[a_+b_.*x_]^2,x_Symbol] :=
          1/b^(m+1) \\[Star] Subst[Int[ExpandIntegrand[FresnelS[x]^2,(b*c-a*d+d*x)^m,x],x],x,a+b*x] /;
        FreeQ[{a,b,c,d},x] && IGtQ[m,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (c__ + d__ * x_).pow(m_) * rubi_fresnel_s(a_ + b__ * x_).pow(2),
        with: [c__, d__, m_, a_, b__, x_],
        optional: [c__, d__, m_, b__],
        when: { freeq!([a_, b__, c__, d__], x_) && igtq!(m_, 0) },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let linear = &b__ * &c__ - &a_ * &d__ + &d__ * &sub_atom;
            let expanded = rubi_expand_integrand(&(rubi_fresnel_s(sub_atom).pow(2) * linear.pow(&m_)), sub);
            let primitive = rubi_rhs_int(&expanded, sub);
            rubi_star(Atom::num(1) / b__.pow(&m_ + 1), rubi_subst(&primitive, sub, &a_ + &b__ * x_))
        },
    ));
}

fn push_rules_rule_6987(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a_, b__, c__, d__, m_, x_);
    rules.push(rubi_rule!(
        order: 6987,
        source: "Int[(c_.+d_.*x_)^m_.*FresnelC[a_+b_.*x_]^2,x_Symbol] :=
          1/b^(m+1) \\[Star] Subst[Int[ExpandIntegrand[FresnelC[x]^2,(b*c-a*d+d*x)^m,x],x],x,a+b*x] /;
        FreeQ[{a,b,c,d},x] && IGtQ[m,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (c__ + d__ * x_).pow(m_) * rubi_fresnel_c(a_ + b__ * x_).pow(2),
        with: [c__, d__, m_, a_, b__, x_],
        optional: [c__, d__, m_, b__],
        when: { freeq!([a_, b__, c__, d__], x_) && igtq!(m_, 0) },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let linear = &b__ * &c__ - &a_ * &d__ + &d__ * &sub_atom;
            let expanded = rubi_expand_integrand(&(rubi_fresnel_c(sub_atom).pow(2) * linear.pow(&m_)), sub);
            let primitive = rubi_rhs_int(&expanded, sub);
            rubi_star(Atom::num(1) / b__.pow(&m_ + 1), rubi_subst(&primitive, sub, &a_ + &b__ * x_))
        },
    ));
}

fn push_rules_rule_6988(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 6988,
        source: "Int[(c_.+d_.*x_)^m_.*FresnelS[a_.+b_.*x_]^n_.,x_Symbol] :=
          Unintegrable[(c+d*x)^m*FresnelS[a+b*x]^n,x] /;
        FreeQ[{a,b,c,d,m,n},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern: (c__ + d__ * x_).pow(m_) * rubi_fresnel_s(a__ + b__ * x_).pow(n_),
        with: [c__, d__, m_, a__, b__, n_, x_],
        optional: [c__, d__, m_, a__, b__, n_],
        when: { freeq!([a__, b__, c__, d__, m_, n_], x_) },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let argument = &a__ + &b__ * x_;
            rubi_unintegrable(linear.pow(&m_) * rubi_fresnel_s(argument).pow(&n_), x_)
        },
    ));
}

fn push_rules_rule_6989(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 6989,
        source: "Int[(c_.+d_.*x_)^m_.*FresnelC[a_.+b_.*x_]^n_.,x_Symbol] :=
          Unintegrable[(c+d*x)^m*FresnelC[a+b*x]^n,x] /;
        FreeQ[{a,b,c,d,m,n},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern: (c__ + d__ * x_).pow(m_) * rubi_fresnel_c(a__ + b__ * x_).pow(n_),
        with: [c__, d__, m_, a__, b__, n_, x_],
        optional: [c__, d__, m_, a__, b__, n_],
        when: { freeq!([a__, b__, c__, d__, m_, n_], x_) },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let argument = &a__ + &b__ * x_;
            rubi_unintegrable(linear.pow(&m_) * rubi_fresnel_c(argument).pow(&n_), x_)
        },
    ));
}

fn push_rules_rule_6990(rules: &mut Vec<RubiRule>) {
    rubi_symb!(b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 6990,
        source: "Int[E^(c_.+d_.*x_^2)*FresnelS[b_.*x_],x_Symbol] :=
          (1+I)/4 \\[Star] Int[E^(c+d*x^2)*Erf[Sqrt[Pi]/2*(1+I)*b*x],x] + (1-I)/4 \\[Star] Int[E^(c+d*x^2)*Erf[Sqrt[Pi]/2*(1-I)*b*x],x] /;
        FreeQ[{b,c,d},x] && EqQ[d^2,-Pi^2/4*b^4]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (c__ + d__ * x_.pow(2)).exp() * rubi_fresnel_s(b__ * x_),
        with: [c__, d__, b__, x_],
        optional: [c__, d__, b__],
        when: {
            freeq!([b__, c__, d__], x_)
                && eqq!(d__.pow(2) + Atom::var(Symbol::PI).pow(2) * b__.pow(4) / 4, 0)
        },
        rhs: {
            let i = Atom::i();
            let pi = Atom::var(Symbol::PI);
            let gaussian = (&c__ + &d__ * x_.pow(2)).exp();
            let plus = pi.sqrt() * (Atom::num(1) + &i) * &b__ * x_ / 2;
            let minus = pi.sqrt() * (Atom::num(1) - &i) * &b__ * x_ / 2;
            rubi_star(Atom::num(1) + &i, rubi_rhs_int(&(&gaussian * plus.erf()), x_) / 4)
                    + rubi_star(Atom::num(1) - i, rubi_rhs_int(&(gaussian * minus.erf()), x_) / 4)
        },
    ));
}

fn push_rules_rule_6991(rules: &mut Vec<RubiRule>) {
    rubi_symb!(b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 6991,
        source: "Int[E^(c_.+d_.*x_^2)*FresnelC[b_.*x_],x_Symbol] :=
          (1-I)/4 \\[Star] Int[E^(c+d*x^2)*Erf[Sqrt[Pi]/2*(1+I)*b*x],x] + (1+I)/4 \\[Star] Int[E^(c+d*x^2)*Erf[Sqrt[Pi]/2*(1-I)*b*x],x] /;
        FreeQ[{b,c,d},x] && EqQ[d^2,-Pi^2/4*b^4]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (c__ + d__ * x_.pow(2)).exp() * rubi_fresnel_c(b__ * x_),
        with: [c__, d__, b__, x_],
        optional: [c__, d__, b__],
        when: {
            freeq!([b__, c__, d__], x_)
                && eqq!(d__.pow(2) + Atom::var(Symbol::PI).pow(2) * b__.pow(4) / 4, 0)
        },
        rhs: {
            let i = Atom::i();
            let pi = Atom::var(Symbol::PI);
            let gaussian = (&c__ + &d__ * x_.pow(2)).exp();
            let plus = pi.sqrt() * (Atom::num(1) + &i) * &b__ * x_ / 2;
            let minus = pi.sqrt() * (Atom::num(1) - &i) * &b__ * x_ / 2;
            rubi_star(Atom::num(1) - &i, rubi_rhs_int(&(&gaussian * plus.erf()), x_) / 4)
                    + rubi_star(Atom::num(1) + i, rubi_rhs_int(&(gaussian * minus.erf()), x_) / 4)
        },
    ));
}

fn push_rules_rule_6992(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 6992,
        source: "Int[E^(c_.+d_.*x_^2)*FresnelS[a_.+b_.*x_]^n_.,x_Symbol] :=
          Unintegrable[E^(c+d*x^2)*FresnelS[a+b*x]^n,x] /;
        FreeQ[{a,b,c,d,n},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern: (c__ + d__ * x_.pow(2)).exp() * rubi_fresnel_s(a__ + b__ * x_).pow(n_),
        with: [c__, d__, a__, b__, n_, x_],
        optional: [c__, d__, a__, b__, n_],
        when: { freeq!([a__, b__, c__, d__, n_], x_) },
        rhs: {
            let gaussian = (&c__ + &d__ * x_.pow(2)).exp();
            let argument = &a__ + &b__ * x_;
            rubi_unintegrable(gaussian * rubi_fresnel_s(argument).pow(&n_), x_)
        },
    ));
}

fn push_rules_rule_6993(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 6993,
        source: "Int[E^(c_.+d_.*x_^2)*FresnelC[a_.+b_.*x_]^n_.,x_Symbol] :=
          Unintegrable[E^(c+d*x^2)*FresnelC[a+b*x]^n,x] /;
        FreeQ[{a,b,c,d,n},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern: (c__ + d__ * x_.pow(2)).exp() * rubi_fresnel_c(a__ + b__ * x_).pow(n_),
        with: [c__, d__, a__, b__, n_, x_],
        optional: [c__, d__, a__, b__, n_],
        when: { freeq!([a__, b__, c__, d__, n_], x_) },
        rhs: {
            let gaussian = (&c__ + &d__ * x_.pow(2)).exp();
            let argument = &a__ + &b__ * x_;
            rubi_unintegrable(gaussian * rubi_fresnel_c(argument).pow(&n_), x_)
        },
    ));
}

fn push_rules_rule_6994(rules: &mut Vec<RubiRule>) {
    rubi_symb!(b__, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 6994,
        source: "Int[Sin[d_.*x_^2]*FresnelS[b_.*x_]^n_.,x_Symbol] :=
          Pi*b/(2*d) \\[Star] Subst[Int[x^n,x],x,FresnelS[b*x]] /;
        FreeQ[{b,d,n},x] && EqQ[d^2,Pi^2/4*b^4]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (d__ * x_.pow(2)).sin() * rubi_fresnel_s(b__ * x_).pow(n_),
        with: [d__, b__, n_, x_],
        optional: [d__, b__, n_],
        when: {
            freeq!([b__, d__, n_], x_)
                && eqq!(d__.pow(2) - Atom::var(Symbol::PI).pow(2) * b__.pow(4) / 4, 0)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let primitive = rubi_rhs_int(&sub_atom.pow(&n_), sub);
            let replacement = rubi_fresnel_s(&b__ * x_);
            rubi_star(Atom::var(Symbol::PI) * &b__ / (Atom::num(2) * &d__), rubi_subst(&primitive, sub, replacement))
        },
    ));
}

fn push_rules_rule_6995(rules: &mut Vec<RubiRule>) {
    rubi_symb!(b__, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 6995,
        source: "Int[Cos[d_.*x_^2]*FresnelC[b_.*x_]^n_.,x_Symbol] :=
          Pi*b/(2*d) \\[Star] Subst[Int[x^n,x],x,FresnelC[b*x]] /;
        FreeQ[{b,d,n},x] && EqQ[d^2,Pi^2/4*b^4]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (d__ * x_.pow(2)).cos() * rubi_fresnel_c(b__ * x_).pow(n_),
        with: [d__, b__, n_, x_],
        optional: [d__, b__, n_],
        when: {
            freeq!([b__, d__, n_], x_)
                && eqq!(d__.pow(2) - Atom::var(Symbol::PI).pow(2) * b__.pow(4) / 4, 0)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let primitive = rubi_rhs_int(&sub_atom.pow(&n_), sub);
            let replacement = rubi_fresnel_c(&b__ * x_);
            rubi_star(Atom::var(Symbol::PI) * &b__ / (Atom::num(2) * &d__), rubi_subst(&primitive, sub, replacement))
        },
    ));
}

fn push_rules_rule_6996(rules: &mut Vec<RubiRule>) {
    rubi_symb!(b__, c_, d__, x_);
    rules.push(rubi_rule!(
        order: 6996,
        source: "Int[Sin[c_+d_.*x_^2]*FresnelS[b_.*x_],x_Symbol] :=
          Sin[c] \\[Star] Int[Cos[d*x^2]*FresnelS[b*x],x] + Cos[c] \\[Star] Int[Sin[d*x^2]*FresnelS[b*x],x] /;
        FreeQ[{b,c,d},x] && EqQ[d^2,Pi^2/4*b^4]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (c_ + d__ * x_.pow(2)).sin() * rubi_fresnel_s(b__ * x_),
        with: [c_, d__, b__, x_],
        optional: [d__, b__],
        when: {
            freeq!([b__, c_, d__], x_)
                && eqq!(d__.pow(2) - Atom::var(Symbol::PI).pow(2) * b__.pow(4) / 4, 0)
        },
        rhs: {
            let quadratic = &d__ * x_.pow(2);
            let argument = &b__ * x_;
            rubi_star(c_.sin(), rubi_rhs_int(&(&quadratic.cos() * rubi_fresnel_s(&argument)), x_)) + rubi_star(c_.cos(), rubi_rhs_int(&(quadratic.sin() * rubi_fresnel_s(argument)), x_))
        },
    ));
}

fn push_rules_rule_6997(rules: &mut Vec<RubiRule>) {
    rubi_symb!(b__, c_, d__, x_);
    rules.push(rubi_rule!(
        order: 6997,
        source: "Int[Cos[c_+d_.*x_^2]*FresnelC[b_.*x_],x_Symbol] :=
          Cos[c] \\[Star] Int[Cos[d*x^2]*FresnelC[b*x],x] - Sin[c] \\[Star] Int[Sin[d*x^2]*FresnelC[b*x],x] /;
        FreeQ[{b,c,d},x] && EqQ[d^2,Pi^2/4*b^4]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (c_ + d__ * x_.pow(2)).cos() * rubi_fresnel_c(b__ * x_),
        with: [c_, d__, b__, x_],
        optional: [d__, b__],
        when: {
            freeq!([b__, c_, d__], x_)
                && eqq!(d__.pow(2) - Atom::var(Symbol::PI).pow(2) * b__.pow(4) / 4, 0)
        },
        rhs: {
            let quadratic = &d__ * x_.pow(2);
            let argument = &b__ * x_;
            rubi_star(c_.cos(), rubi_rhs_int(&(&quadratic.cos() * rubi_fresnel_c(&argument)), x_)) - rubi_star(c_.sin(), rubi_rhs_int(&(quadratic.sin() * rubi_fresnel_c(argument)), x_))
        },
    ));
}

fn push_rules_rule_6998(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 6998,
        source: "Int[Sin[c_.+d_.*x_^2]*FresnelS[a_.+b_.*x_]^n_.,x_Symbol] :=
          Unintegrable[Sin[c+d*x^2]*FresnelS[a+b*x]^n,x] /;
        FreeQ[{a,b,c,d,n},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern: (c__ + d__ * x_.pow(2)).sin() * rubi_fresnel_s(a__ + b__ * x_).pow(n_),
        with: [c__, d__, a__, b__, n_, x_],
        optional: [c__, d__, a__, b__, n_],
        when: { freeq!([a__, b__, c__, d__, n_], x_) },
        rhs: {
            let trig = (&c__ + &d__ * x_.pow(2)).sin();
            let argument = &a__ + &b__ * x_;
            rubi_unintegrable(trig * rubi_fresnel_s(argument).pow(&n_), x_)
        },
    ));
}

fn push_rules_rule_6999(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 6999,
        source: "Int[Cos[c_.+d_.*x_^2]*FresnelC[a_.+b_.*x_]^n_.,x_Symbol] :=
          Unintegrable[Cos[c+d*x^2]*FresnelC[a+b*x]^n,x] /;
        FreeQ[{a,b,c,d,n},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern: (c__ + d__ * x_.pow(2)).cos() * rubi_fresnel_c(a__ + b__ * x_).pow(n_),
        with: [c__, d__, a__, b__, n_, x_],
        optional: [c__, d__, a__, b__, n_],
        when: { freeq!([a__, b__, c__, d__, n_], x_) },
        rhs: {
            let trig = (&c__ + &d__ * x_.pow(2)).cos();
            let argument = &a__ + &b__ * x_;
            rubi_unintegrable(trig * rubi_fresnel_c(argument).pow(&n_), x_)
        },
    ));
}

fn push_rules_rule_7000(rules: &mut Vec<RubiRule>) {
    rubi_symb!(b__, d__, x_);
    rules.push(rubi_rule!(
        order: 7000,
        source: "Int[Cos[d_.*x_^2]*FresnelS[b_.*x_],x_Symbol] :=
          FresnelC[b*x]*FresnelS[b*x]/(2*b) -
          1/8*I*b*x^2*HypergeometricPFQ[{1,1},{3/2,2},-1/2*I*b^2*Pi*x^2] +
          1/8*I*b*x^2*HypergeometricPFQ[{1,1},{3/2,2},1/2*I*b^2*Pi*x^2] /;
        FreeQ[{b,d},x] && EqQ[d^2,Pi^2/4*b^4]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (d__ * x_.pow(2)).cos() * rubi_fresnel_s(b__ * x_),
        with: [d__, b__, x_],
        optional: [d__, b__],
        when: {
            freeq!([b__, d__], x_)
                && eqq!(d__.pow(2) - Atom::var(Symbol::PI).pow(2) * b__.pow(4) / 4, 0)
        },
        rhs: {
            let i = Atom::i();
            let pi = Atom::var(Symbol::PI);
            let argument = &b__ * x_;
            let base = rubi_fresnel_c(&argument) * rubi_fresnel_s(argument) / (Atom::num(2) * &b__);
            let negative_hyper = rubi_hypergeometric_pfq_2_2(
                Atom::num(1),
                Atom::num(1),
                Atom::num(3) / 2,
                Atom::num(2),
                -&i * b__.pow(2) * &pi * x_.pow(2) / 2,
            );
            let positive_hyper = rubi_hypergeometric_pfq_2_2(
                Atom::num(1),
                Atom::num(1),
                Atom::num(3) / 2,
                Atom::num(2),
                &i * b__.pow(2) * pi * x_.pow(2) / 2,
            );
            rubi_simp(&(base), x_) - rubi_simp(&(&i * &b__ * x_.pow(2) * negative_hyper / 8), x_) + rubi_simp(&(i * &b__ * x_.pow(2) * positive_hyper / 8), x_)
        },
    ));
}

fn push_rules_rule_7001(rules: &mut Vec<RubiRule>) {
    rubi_symb!(b__, d__, x_);
    rules.push(rubi_rule!(
        order: 7001,
        source: "Int[Sin[d_.*x_^2]*FresnelC[b_.*x_],x_Symbol] :=
          b*Pi*FresnelC[b*x]*FresnelS[b*x]/(4*d) +
          1/8*I*b*x^2*HypergeometricPFQ[{1,1},{3/2,2},-I*d*x^2] -
          1/8*I*b*x^2*HypergeometricPFQ[{1,1},{3/2,2},I*d*x^2] /;
        FreeQ[{b,d},x] && EqQ[d^2,Pi^2/4*b^4]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (d__ * x_.pow(2)).sin() * rubi_fresnel_c(b__ * x_),
        with: [d__, b__, x_],
        optional: [d__, b__],
        when: {
            freeq!([b__, d__], x_)
                && eqq!(d__.pow(2) - Atom::var(Symbol::PI).pow(2) * b__.pow(4) / 4, 0)
        },
        rhs: {
            let i = Atom::i();
            let pi = Atom::var(Symbol::PI);
            let argument = &b__ * x_;
            let base = &b__ * &pi * rubi_fresnel_c(&argument) * rubi_fresnel_s(argument) / (Atom::num(4) * &d__);
            let negative_hyper = rubi_hypergeometric_pfq_2_2(
                Atom::num(1),
                Atom::num(1),
                Atom::num(3) / 2,
                Atom::num(2),
                -&i * &d__ * x_.pow(2),
            );
            let positive_hyper = rubi_hypergeometric_pfq_2_2(
                Atom::num(1),
                Atom::num(1),
                Atom::num(3) / 2,
                Atom::num(2),
                &i * &d__ * x_.pow(2),
            );
            rubi_simp(&(base), x_) + rubi_simp(&(&i * &b__ * x_.pow(2) * negative_hyper / 8), x_) - rubi_simp(&(i * &b__ * x_.pow(2) * positive_hyper / 8), x_)
        },
    ));
}

fn push_rules_rule_7002(rules: &mut Vec<RubiRule>) {
    rubi_symb!(b__, c_, d__, x_);
    rules.push(rubi_rule!(
        order: 7002,
        source: "Int[Cos[c_+d_.*x_^2]*FresnelS[b_.*x_],x_Symbol] :=
          Cos[c] \\[Star] Int[Cos[d*x^2]*FresnelS[b*x],x] - Sin[c] \\[Star] Int[Sin[d*x^2]*FresnelS[b*x],x] /;
        FreeQ[{b,c,d},x] && EqQ[d^2,Pi^2/4*b^4]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (c_ + d__ * x_.pow(2)).cos() * rubi_fresnel_s(b__ * x_),
        with: [c_, d__, b__, x_],
        optional: [d__, b__],
        when: {
            freeq!([b__, c_, d__], x_)
                && eqq!(d__.pow(2) - Atom::var(Symbol::PI).pow(2) * b__.pow(4) / 4, 0)
        },
        rhs: {
            let quadratic = &d__ * x_.pow(2);
            let argument = &b__ * x_;
            rubi_star(c_.cos(), rubi_rhs_int(&(&quadratic.cos() * rubi_fresnel_s(&argument)), x_)) - rubi_star(c_.sin(), rubi_rhs_int(&(quadratic.sin() * rubi_fresnel_s(argument)), x_))
        },
    ));
}

fn push_rules_rule_7003(rules: &mut Vec<RubiRule>) {
    rubi_symb!(b__, c_, d__, x_);
    rules.push(rubi_rule!(
        order: 7003,
        source: "Int[Sin[c_+d_.*x_^2]*FresnelC[b_.*x_],x_Symbol] :=
          Sin[c] \\[Star] Int[Cos[d*x^2]*FresnelC[b*x],x] + Cos[c] \\[Star] Int[Sin[d*x^2]*FresnelC[b*x],x] /;
        FreeQ[{b,c,d},x] && EqQ[d^2,Pi^2/4*b^4]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (c_ + d__ * x_.pow(2)).sin() * rubi_fresnel_c(b__ * x_),
        with: [c_, d__, b__, x_],
        optional: [d__, b__],
        when: {
            freeq!([b__, c_, d__], x_)
                && eqq!(d__.pow(2) - Atom::var(Symbol::PI).pow(2) * b__.pow(4) / 4, 0)
        },
        rhs: {
            let quadratic = &d__ * x_.pow(2);
            let argument = &b__ * x_;
            rubi_star(c_.sin(), rubi_rhs_int(&(&quadratic.cos() * rubi_fresnel_c(&argument)), x_)) + rubi_star(c_.cos(), rubi_rhs_int(&(quadratic.sin() * rubi_fresnel_c(argument)), x_))
        },
    ));
}

fn push_rules_rule_7004(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 7004,
        source: "Int[Cos[c_.+d_.*x_^2]*FresnelS[a_.+b_.*x_]^n_.,x_Symbol] :=
          Unintegrable[Cos[c+d*x^2]*FresnelS[a+b*x]^n,x] /;
        FreeQ[{a,b,c,d,n},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern: (c__ + d__ * x_.pow(2)).cos() * rubi_fresnel_s(a__ + b__ * x_).pow(n_),
        with: [c__, d__, a__, b__, n_, x_],
        optional: [c__, d__, a__, b__, n_],
        when: { freeq!([a__, b__, c__, d__, n_], x_) },
        rhs: {
            let trig = (&c__ + &d__ * x_.pow(2)).cos();
            let argument = &a__ + &b__ * x_;
            rubi_unintegrable(trig * rubi_fresnel_s(argument).pow(&n_), x_)
        },
    ));
}

fn push_rules_rule_7005(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 7005,
        source: "Int[Sin[c_.+d_.*x_^2]*FresnelC[a_.+b_.*x_]^n_.,x_Symbol] :=
          Unintegrable[Sin[c+d*x^2]*FresnelC[a+b*x]^n,x] /;
        FreeQ[{a,b,c,d,n},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern: (c__ + d__ * x_.pow(2)).sin() * rubi_fresnel_c(a__ + b__ * x_).pow(n_),
        with: [c__, d__, a__, b__, n_, x_],
        optional: [c__, d__, a__, b__, n_],
        when: { freeq!([a__, b__, c__, d__, n_], x_) },
        rhs: {
            let trig = (&c__ + &d__ * x_.pow(2)).sin();
            let argument = &a__ + &b__ * x_;
            rubi_unintegrable(trig * rubi_fresnel_c(argument).pow(&n_), x_)
        },
    ));
}

fn push_rules_rule_7006(rules: &mut Vec<RubiRule>) {
    rubi_symb!(b__, d__, x_);
    rules.push(rubi_rule!(
        order: 7006,
        source: "Int[x_*Sin[d_.*x_^2]*FresnelS[b_.*x_],x_Symbol] :=
          -Cos[d*x^2]*FresnelS[b*x]/(2*d) + 1/(2*b*Pi) \\[Star] Int[Sin[2*d*x^2],x] /;
        FreeQ[{b,d},x] && EqQ[d^2,Pi^2/4*b^4]",
        desc: "Integration by parts and algebraic simplification",
        refs: [],
        pattern: x_ * (d__ * x_.pow(2)).sin() * rubi_fresnel_s(b__ * x_),
        with: [d__, b__, x_],
        optional: [d__, b__],
        when: {
            freeq!([b__, d__], x_)
                && eqq!(d__.pow(2) - Atom::var(Symbol::PI).pow(2) * b__.pow(4) / 4, 0)
        },
        rhs: {
            let quadratic = &d__ * x_.pow(2);
            rubi_simp(&(-&quadratic.cos() * rubi_fresnel_s(&b__ * x_) / (Atom::num(2) * &d__)), x_)
                    + rubi_star(Atom::num(1) / (Atom::num(2) * &b__ * Atom::var(Symbol::PI)), rubi_rhs_int(&((Atom::num(2) * quadratic).sin()), x_))
        },
    ));
}

fn push_rules_rule_7007(rules: &mut Vec<RubiRule>) {
    rubi_symb!(b__, d__, x_);
    rules.push(rubi_rule!(
        order: 7007,
        source: "Int[x_*Cos[d_.*x_^2]*FresnelC[b_.*x_],x_Symbol] :=
          Sin[d*x^2]*FresnelC[b*x]/(2*d) - b/(4*d) \\[Star] Int[Sin[2*d*x^2],x] /;
        FreeQ[{b,d},x] && EqQ[d^2,Pi^2/4*b^4]",
        desc: "Integration by parts and algebraic simplification",
        refs: [],
        pattern: x_ * (d__ * x_.pow(2)).cos() * rubi_fresnel_c(b__ * x_),
        with: [d__, b__, x_],
        optional: [d__, b__],
        when: {
            freeq!([b__, d__], x_)
                && eqq!(d__.pow(2) - Atom::var(Symbol::PI).pow(2) * b__.pow(4) / 4, 0)
        },
        rhs: {
            let quadratic = &d__ * x_.pow(2);
            rubi_simp(&(&quadratic.sin() * rubi_fresnel_c(&b__ * x_) / (Atom::num(2) * &d__)), x_)
                    - rubi_star(b__, rubi_rhs_int(&((Atom::num(2) * quadratic).sin()), x_) / (Atom::num(4) * &d__))
        },
    ));
}

fn push_rules_rule_7008(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; b__, d__, m_, x_);
    rules.push(rubi_rule!(
        order: 7008,
        source: "Int[x_^m_*Sin[d_.*x_^2]*FresnelS[b_.*x_],x_Symbol] :=
          -x^(m-1)*Cos[d*x^2]*FresnelS[b*x]/(2*d) +
          1/(2*b*Pi) \\[Star] Int[x^(m-1)*Sin[2*d*x^2],x] +
          (m-1)/(2*d) \\[Star] Int[x^(m-2)*Cos[d*x^2]*FresnelS[b*x],x] /;
        FreeQ[{b,d},x] && EqQ[d^2,Pi^2/4*b^4] && IGtQ[m,1]",
        desc: "Integration by parts and algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [m_, d__, b__, x_],
        optional: [d__, b__],
        when: {
            freeq!([b__, d__], x_)
                && eqq!(d__.pow(2) - Atom::var(Symbol::PI).pow(2) * b__.pow(4) / 4, 0)
                && igtq!(m_, 1)
        },
        rhs: {
            let quadratic = &d__ * x_.pow(2);
            rubi_simp(&(Atom::num(-1) * x_.pow(&m_ - 1) * &quadratic.cos() * rubi_fresnel_s(&b__ * x_) / (Atom::num(2) * &d__)), x_)
                    + rubi_star(Atom::num(1) / (Atom::num(2) * &b__ * Atom::var(Symbol::PI)), rubi_rhs_int(&(x_.pow(&m_ - 1) * (Atom::num(2) * &quadratic).sin()), x_))
                    + rubi_star(&m_ - 1, rubi_rhs_int(&(x_.pow(&m_ - 2) * quadratic.cos() * rubi_fresnel_s(&b__ * x_)), x_)
                        / (Atom::num(2) * &d__))
        },
    ));
}

fn push_rules_rule_7009(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; b__, d__, m_, x_);
    rules.push(rubi_rule!(
        order: 7009,
        source: "Int[x_^m_*Cos[d_.*x_^2]*FresnelC[b_.*x_],x_Symbol] :=
          x^(m-1)*Sin[d*x^2]*FresnelC[b*x]/(2*d) -
          b/(4*d) \\[Star] Int[x^(m-1)*Sin[2*d*x^2],x] -
          (m-1)/(2*d) \\[Star] Int[x^(m-2)*Sin[d*x^2]*FresnelC[b*x],x] /;
        FreeQ[{b,d},x] && EqQ[d^2,Pi^2/4*b^4] && IGtQ[m,1]",
        desc: "Integration by parts and algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [m_, d__, b__, x_],
        optional: [d__, b__],
        when: {
            freeq!([b__, d__], x_)
                && eqq!(d__.pow(2) - Atom::var(Symbol::PI).pow(2) * b__.pow(4) / 4, 0)
                && igtq!(m_, 1)
        },
        rhs: {
            let quadratic = &d__ * x_.pow(2);
            rubi_simp(&(x_.pow(&m_ - 1) * &quadratic.sin() * rubi_fresnel_c(&b__ * x_) / (Atom::num(2) * &d__)), x_)
                    - rubi_star(&b__, rubi_rhs_int(&(x_.pow(&m_ - 1) * (Atom::num(2) * &quadratic).sin()), x_)
                        / (Atom::num(4) * &d__))
                    - rubi_star(&m_ - 1, rubi_rhs_int(&(x_.pow(&m_ - 2) * quadratic.sin() * rubi_fresnel_c(&b__ * x_)), x_)
                        / (Atom::num(2) * &d__))
        },
    ));
}

fn push_rules_rule_7010(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; b__, d__, m_, x_);
    rules.push(rubi_rule!(
        order: 7010,
        source: "Int[x_^m_*Sin[d_.*x_^2]*FresnelS[b_.*x_],x_Symbol] :=
          x^(m+1)*Sin[d*x^2]*FresnelS[b*x]/(m+1) -
          d*x^(m+2)/(Pi*b*(m+1)*(m+2)) +
          d/(Pi*b*(m+1)) \\[Star] Int[x^(m+1)*Cos[2*d*x^2],x] -
          2*d/(m+1) \\[Star] Int[x^(m+2)*Cos[d*x^2]*FresnelS[b*x],x] /;
        FreeQ[{b,d},x] && EqQ[d^2,Pi^2/4*b^4] && ILtQ[m,-2]",
        desc: "Inverted integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [m_, d__, b__, x_],
        optional: [d__, b__],
        when: {
            freeq!([b__, d__], x_)
                && eqq!(d__.pow(2) - Atom::var(Symbol::PI).pow(2) * b__.pow(4) / 4, 0)
                && iltq!(m_, -2)
        },
        rhs: {
            let quadratic = &d__ * x_.pow(2);
            rubi_simp(&(x_.pow(&m_ + 1) * &quadratic.sin() * rubi_fresnel_s(&b__ * x_) / (&m_ + 1)), x_)
                    - rubi_simp(&(&d__ * x_.pow(&m_ + 2) / (Atom::var(Symbol::PI) * &b__ * (&m_ + 1) * (&m_ + 2))), x_)
                    + rubi_star(&d__, rubi_rhs_int(&(x_.pow(&m_ + 1) * (Atom::num(2) * &quadratic).cos()), x_)
                        / (Atom::var(Symbol::PI) * &b__ * (&m_ + 1)))
                    - rubi_star(Atom::num(2) * &d__ / (&m_ + 1), rubi_rhs_int(&(x_.pow(&m_ + 2) * quadratic.cos() * rubi_fresnel_s(&b__ * x_)), x_))
        },
    ));
}

fn push_rules_rule_7011(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; b__, d__, m_, x_);
    rules.push(rubi_rule!(
        order: 7011,
        source: "Int[x_^m_*Cos[d_.*x_^2]*FresnelC[b_.*x_],x_Symbol] :=
          x^(m+1)*Cos[d*x^2]*FresnelC[b*x]/(m+1) -
          b*x^(m+2)/(2*(m+1)*(m+2)) -
          b/(2*(m+1)) \\[Star] Int[x^(m+1)*Cos[2*d*x^2],x] +
          2*d/(m+1) \\[Star] Int[x^(m+2)*Sin[d*x^2]*FresnelC[b*x],x] /;
        FreeQ[{b,d},x] && EqQ[d^2,Pi^2/4*b^4] && ILtQ[m,-2]",
        desc: "Inverted integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [m_, d__, b__, x_],
        optional: [d__, b__],
        when: {
            freeq!([b__, d__], x_)
                && eqq!(d__.pow(2) - Atom::var(Symbol::PI).pow(2) * b__.pow(4) / 4, 0)
                && iltq!(m_, -2)
        },
        rhs: {
            let quadratic = &d__ * x_.pow(2);
            rubi_simp(&(x_.pow(&m_ + 1) * &quadratic.cos() * rubi_fresnel_c(&b__ * x_) / (&m_ + 1)), x_)
                    - rubi_simp(&(&b__ * x_.pow(&m_ + 2) / (Atom::num(2) * (&m_ + 1) * (&m_ + 2))), x_)
                    - rubi_star(&b__, rubi_rhs_int(&(x_.pow(&m_ + 1) * (Atom::num(2) * &quadratic).cos()), x_)
                        / (Atom::num(2) * (&m_ + 1)))
                    + rubi_star(Atom::num(2) * &d__ / (&m_ + 1), rubi_rhs_int(&(x_.pow(&m_ + 2) * quadratic.sin() * rubi_fresnel_c(&b__ * x_)), x_))
        },
    ));
}

fn push_rules_rule_7012(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 7012,
        source: "Int[(e_.*x_)^m_.*Sin[c_.+d_.*x_^2]*FresnelS[a_.+b_.*x_]^n_.,x_Symbol] :=
          Unintegrable[(e*x)^m*Sin[c+d*x^2]*FresnelS[a+b*x]^n,x] /;
        FreeQ[{a,b,c,d,e,m,n},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern: (e__ * x_).pow(m_) * (c__ + d__ * x_.pow(2)).sin() * rubi_fresnel_s(a__ + b__ * x_).pow(n_),
        with: [e__, m_, c__, d__, a__, b__, n_, x_],
        optional: [e__, m_, c__, d__, a__, b__, n_],
        when: { freeq!([a__, b__, c__, d__, e__, m_, n_], x_) },
        rhs: {
            let scaled = &e__ * x_;
            let trig = (&c__ + &d__ * x_.pow(2)).sin();
            let argument = &a__ + &b__ * x_;
            rubi_unintegrable(scaled.pow(&m_) * trig * rubi_fresnel_s(argument).pow(&n_), x_)
        },
    ));
}

fn push_rules_rule_7013(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 7013,
        source: "Int[(e_.*x_)^m_.*Cos[c_.+d_.*x_^2]*FresnelC[a_.+b_.*x_]^n_.,x_Symbol] :=
          Unintegrable[(e*x)^m*Cos[c+d*x^2]*FresnelC[a+b*x]^n,x] /;
        FreeQ[{a,b,c,d,e,m,n},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern: (e__ * x_).pow(m_) * (c__ + d__ * x_.pow(2)).cos() * rubi_fresnel_c(a__ + b__ * x_).pow(n_),
        with: [e__, m_, c__, d__, a__, b__, n_, x_],
        optional: [e__, m_, c__, d__, a__, b__, n_],
        when: { freeq!([a__, b__, c__, d__, e__, m_, n_], x_) },
        rhs: {
            let scaled = &e__ * x_;
            let trig = (&c__ + &d__ * x_.pow(2)).cos();
            let argument = &a__ + &b__ * x_;
            rubi_unintegrable(scaled.pow(&m_) * trig * rubi_fresnel_c(argument).pow(&n_), x_)
        },
    ));
}

fn push_rules_rule_7014(rules: &mut Vec<RubiRule>) {
    rubi_symb!(b__, d__, x_);
    rules.push(rubi_rule!(
        order: 7014,
        source: "Int[x_*Cos[d_.*x_^2]*FresnelS[b_.*x_],x_Symbol] :=
          Sin[d*x^2]*FresnelS[b*x]/(2*d) - 1/(Pi*b) \\[Star] Int[Sin[d*x^2]^2,x] /;
        FreeQ[{b,d},x] && EqQ[d^2,Pi^2/4*b^4]",
        desc: "Integration by parts and algebraic simplification",
        refs: [],
        pattern: x_ * (d__ * x_.pow(2)).cos() * rubi_fresnel_s(b__ * x_),
        with: [d__, b__, x_],
        optional: [d__, b__],
        when: {
            freeq!([b__, d__], x_)
                && eqq!(d__.pow(2) - Atom::var(Symbol::PI).pow(2) * b__.pow(4) / 4, 0)
        },
        rhs: {
            let quadratic = &d__ * x_.pow(2);
            rubi_simp(&(&quadratic.sin() * rubi_fresnel_s(&b__ * x_) / (Atom::num(2) * &d__)), x_)
                    - rubi_star(Atom::num(1) / (Atom::var(Symbol::PI) * &b__), rubi_rhs_int(&(quadratic.sin().pow(2)), x_))
        },
    ));
}

fn push_rules_rule_7015(rules: &mut Vec<RubiRule>) {
    rubi_symb!(b__, d__, x_);
    rules.push(rubi_rule!(
        order: 7015,
        source: "Int[x_*Sin[d_.*x_^2]*FresnelC[b_.*x_],x_Symbol] :=
          -Cos[d*x^2]*FresnelC[b*x]/(2*d) + b/(2*d) \\[Star] Int[Cos[d*x^2]^2,x] /;
        FreeQ[{b,d},x] && EqQ[d^2,Pi^2/4*b^4]",
        desc: "Integration by parts and algebraic simplification",
        refs: [],
        pattern: x_ * (d__ * x_.pow(2)).sin() * rubi_fresnel_c(b__ * x_),
        with: [d__, b__, x_],
        optional: [d__, b__],
        when: {
            freeq!([b__, d__], x_)
                && eqq!(d__.pow(2) - Atom::var(Symbol::PI).pow(2) * b__.pow(4) / 4, 0)
        },
        rhs: {
            let quadratic = &d__ * x_.pow(2);
            rubi_simp(&(-&quadratic.cos() * rubi_fresnel_c(&b__ * x_) / (Atom::num(2) * &d__)), x_)
                    + rubi_star(b__, rubi_rhs_int(&(quadratic.cos().pow(2)), x_) / (Atom::num(2) * &d__))
        },
    ));
}

fn push_rules_rule_7016(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; b__, d__, m_, x_);
    rules.push(rubi_rule!(
        order: 7016,
        source: "Int[x_^m_*Cos[d_.*x_^2]*FresnelS[b_.*x_],x_Symbol] :=
          x^(m-1)*Sin[d*x^2]*FresnelS[b*x]/(2*d) -
          1/(Pi*b) \\[Star] Int[x^(m-1)*Sin[d*x^2]^2,x] -
          (m-1)/(2*d) \\[Star] Int[x^(m-2)*Sin[d*x^2]*FresnelS[b*x],x] /;
        FreeQ[{b,d},x] && EqQ[d^2,Pi^2/4*b^4] && IGtQ[m,1]",
        desc: "Integration by parts and algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [m_, d__, b__, x_],
        optional: [d__, b__],
        when: {
            freeq!([b__, d__], x_)
                && eqq!(d__.pow(2) - Atom::var(Symbol::PI).pow(2) * b__.pow(4) / 4, 0)
                && igtq!(m_, 1)
        },
        rhs: {
            let quadratic = &d__ * x_.pow(2);
            rubi_simp(&(x_.pow(&m_ - 1) * &quadratic.sin() * rubi_fresnel_s(&b__ * x_) / (Atom::num(2) * &d__)), x_)
                    - rubi_star(Atom::num(1) / (Atom::var(Symbol::PI) * &b__), rubi_rhs_int(&(x_.pow(&m_ - 1) * &quadratic.sin().pow(2)), x_))
                    - rubi_star(&m_ - 1, rubi_rhs_int(&(x_.pow(&m_ - 2) * quadratic.sin() * rubi_fresnel_s(&b__ * x_)), x_)
                        / (Atom::num(2) * &d__))
        },
    ));
}

fn push_rules_rule_7017(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; b__, d__, m_, x_);
    rules.push(rubi_rule!(
        order: 7017,
        source: "Int[x_^m_*Sin[d_.*x_^2]*FresnelC[b_.*x_],x_Symbol] :=
          -x^(m-1)*Cos[d*x^2]*FresnelC[b*x]/(2*d) +
          b/(2*d) \\[Star] Int[x^(m-1)*Cos[d*x^2]^2,x] +
          (m-1)/(2*d) \\[Star] Int[x^(m-2)*Cos[d*x^2]*FresnelC[b*x],x] /;
        FreeQ[{b,d},x] && EqQ[d^2,Pi^2/4*b^4] && IGtQ[m,1]",
        desc: "Integration by parts and algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [m_, d__, b__, x_],
        optional: [d__, b__],
        when: {
            freeq!([b__, d__], x_)
                && eqq!(d__.pow(2) - Atom::var(Symbol::PI).pow(2) * b__.pow(4) / 4, 0)
                && igtq!(m_, 1)
        },
        rhs: {
            let quadratic = &d__ * x_.pow(2);
            rubi_simp(&(Atom::num(-1) * x_.pow(&m_ - 1) * &quadratic.cos() * rubi_fresnel_c(&b__ * x_) / (Atom::num(2) * &d__)), x_)
                    + rubi_star(&b__, rubi_rhs_int(&(x_.pow(&m_ - 1) * &quadratic.cos().pow(2)), x_)
                        / (Atom::num(2) * &d__))
                    + rubi_star(&m_ - 1, rubi_rhs_int(&(x_.pow(&m_ - 2) * quadratic.cos() * rubi_fresnel_c(&b__ * x_)), x_)
                        / (Atom::num(2) * &d__))
        },
    ));
}

fn push_rules_rule_7018(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; b__, d__, m_, x_);
    rules.push(rubi_rule!(
        order: 7018,
        source: "Int[x_^m_*Cos[d_.*x_^2]*FresnelS[b_.*x_],x_Symbol] :=
          x^(m+1)*Cos[d*x^2]*FresnelS[b*x]/(m+1) -
          d/(Pi*b*(m+1)) \\[Star] Int[x^(m+1)*Sin[2*d*x^2],x] +
          2*d/(m+1) \\[Star] Int[x^(m+2)*Sin[d*x^2]*FresnelS[b*x],x] /;
        FreeQ[{b,d},x] && EqQ[d^2,Pi^2/4*b^4] && ILtQ[m,-1]",
        desc: "Inverted integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [m_, d__, b__, x_],
        optional: [d__, b__],
        when: {
            freeq!([b__, d__], x_)
                && eqq!(d__.pow(2) - Atom::var(Symbol::PI).pow(2) * b__.pow(4) / 4, 0)
                && iltq!(m_, -1)
        },
        rhs: {
            let quadratic = &d__ * x_.pow(2);
            rubi_simp(&(x_.pow(&m_ + 1) * &quadratic.cos() * rubi_fresnel_s(&b__ * x_) / (&m_ + 1)), x_)
                    - rubi_star(&d__, rubi_rhs_int(&(x_.pow(&m_ + 1) * (Atom::num(2) * &quadratic).sin()), x_)
                        / (Atom::var(Symbol::PI) * &b__ * (&m_ + 1)))
                    + rubi_star(Atom::num(2) * &d__ / (&m_ + 1), rubi_rhs_int(&(x_.pow(&m_ + 2) * quadratic.sin() * rubi_fresnel_s(&b__ * x_)), x_))
        },
    ));
}

fn push_rules_rule_7019(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; b__, d__, m_, x_);
    rules.push(rubi_rule!(
        order: 7019,
        source: "Int[x_^m_*Sin[d_.*x_^2]*FresnelC[b_.*x_],x_Symbol] :=
          x^(m+1)*Sin[d*x^2]*FresnelC[b*x]/(m+1) -
          b/(2*(m+1)) \\[Star] Int[x^(m+1)*Sin[2*d*x^2],x] -
          2*d/(m+1) \\[Star] Int[x^(m+2)*Cos[d*x^2]*FresnelC[b*x],x] /;
        FreeQ[{b,d},x] && EqQ[d^2,Pi^2/4*b^4] && ILtQ[m,-1]",
        desc: "Inverted integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [m_, d__, b__, x_],
        optional: [d__, b__],
        when: {
            freeq!([b__, d__], x_)
                && eqq!(d__.pow(2) - Atom::var(Symbol::PI).pow(2) * b__.pow(4) / 4, 0)
                && iltq!(m_, -1)
        },
        rhs: {
            let quadratic = &d__ * x_.pow(2);
            rubi_simp(&(x_.pow(&m_ + 1) * &quadratic.sin() * rubi_fresnel_c(&b__ * x_) / (&m_ + 1)), x_)
                    - rubi_star(&b__, rubi_rhs_int(&(x_.pow(&m_ + 1) * (Atom::num(2) * &quadratic).sin()), x_)
                        / (Atom::num(2) * (&m_ + 1)))
                    - rubi_star(Atom::num(2) * &d__ / (&m_ + 1), rubi_rhs_int(&(x_.pow(&m_ + 2) * quadratic.cos() * rubi_fresnel_c(&b__ * x_)), x_))
        },
    ));
}

fn push_rules_rule_7020(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 7020,
        source: "Int[(e_.*x_)^m_.*Cos[c_.+d_.*x_^2]*FresnelS[a_.+b_.*x_]^n_.,x_Symbol] :=
          Unintegrable[(e*x)^m*Cos[c+d*x^2]*FresnelS[a+b*x]^n,x] /;
        FreeQ[{a,b,c,d,e,m,n},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern: (e__ * x_).pow(m_) * (c__ + d__ * x_.pow(2)).cos() * rubi_fresnel_s(a__ + b__ * x_).pow(n_),
        with: [e__, m_, c__, d__, a__, b__, n_, x_],
        optional: [e__, m_, c__, d__, a__, b__, n_],
        when: { freeq!([a__, b__, c__, d__, e__, m_, n_], x_) },
        rhs: {
            let scaled = &e__ * x_;
            let trig = (&c__ + &d__ * x_.pow(2)).cos();
            let argument = &a__ + &b__ * x_;
            rubi_unintegrable(scaled.pow(&m_) * trig * rubi_fresnel_s(argument).pow(&n_), x_)
        },
    ));
}

fn push_rules_rule_7021(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 7021,
        source: "Int[(e_.*x_)^m_.*Sin[c_.+d_.*x_^2]*FresnelC[a_.+b_.*x_]^n_.,x_Symbol] :=
          Unintegrable[(e*x)^m*Sin[c+d*x^2]*FresnelC[a+b*x]^n,x] /;
        FreeQ[{a,b,c,d,e,m,n},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern: (e__ * x_).pow(m_) * (c__ + d__ * x_.pow(2)).sin() * rubi_fresnel_c(a__ + b__ * x_).pow(n_),
        with: [e__, m_, c__, d__, a__, b__, n_, x_],
        optional: [e__, m_, c__, d__, a__, b__, n_],
        when: { freeq!([a__, b__, c__, d__, e__, m_, n_], x_) },
        rhs: {
            let scaled = &e__ * x_;
            let trig = (&c__ + &d__ * x_.pow(2)).sin();
            let argument = &a__ + &b__ * x_;
            rubi_unintegrable(scaled.pow(&m_) * trig * rubi_fresnel_c(argument).pow(&n_), x_)
        },
    ));
}

fn push_rules_rule_7022(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 7022,
        source: "Int[FresnelS[d_.*(a_.+b_.*Log[c_.*x_^n_.])],x_Symbol] :=
          x*FresnelS[d*(a+b*Log[c*x^n])] - b*d*n \\[Star] Int[Sin[Pi/2*(d*(a+b*Log[c*x^n]))^2],x] /;
        FreeQ[{a,b,c,d,n},x]",
        desc: "Integration by parts",
        refs: [],
        pattern: rubi_fresnel_s(d__ * (a__ + b__ * (c__ * x_.pow(n_)).log())),
        with: [d__, a__, b__, c__, n_, x_],
        optional: [d__, a__, b__, c__, n_],
        when: { freeq!([a__, b__, c__, d__, n_], x_) },
        rhs: {
            let pi = Atom::var(Symbol::PI);
            let argument = &d__ * (&a__ + &b__ * (&c__ * x_.pow(&n_)).log());
            rubi_simp(&(x_ * rubi_fresnel_s(&argument)), x_)
                    - rubi_star(&b__ * &d__ * &n_, rubi_rhs_int(&((pi / 2 * argument.pow(2)).sin()), x_))
        },
    ));
}

fn push_rules_rule_7023(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 7023,
        source: "Int[FresnelC[d_.*(a_.+b_.*Log[c_.*x_^n_.])],x_Symbol] :=
          x*FresnelC[d*(a+b*Log[c*x^n])] - b*d*n \\[Star] Int[Cos[Pi/2*(d*(a+b*Log[c*x^n]))^2],x] /;
        FreeQ[{a,b,c,d,n},x]",
        desc: "Integration by parts",
        refs: [],
        pattern: rubi_fresnel_c(d__ * (a__ + b__ * (c__ * x_.pow(n_)).log())),
        with: [d__, a__, b__, c__, n_, x_],
        optional: [d__, a__, b__, c__, n_],
        when: { freeq!([a__, b__, c__, d__, n_], x_) },
        rhs: {
            let pi = Atom::var(Symbol::PI);
            let argument = &d__ * (&a__ + &b__ * (&c__ * x_.pow(&n_)).log());
            rubi_simp(&(x_ * rubi_fresnel_c(&argument)), x_)
                    - rubi_star(&b__ * &d__ * &n_, rubi_rhs_int(&((pi / 2 * argument.pow(2)).cos()), x_))
        },
    ));
}

fn push_rules_rule_7024(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_f_, a__, b__, c__, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 7024,
        source: "Int[F_[d_.*(a_.+b_.*Log[c_.*x_^n_.])]/x_,x_Symbol] :=
          1/n \\[Star] Subst[F[d*(a+b*x)],x,Log[c*x^n]] /;
        FreeQ[{a,b,c,d,n},x] && MemberQ[{FresnelS,FresnelC},F]",
        desc: "Integration by substitution",
        refs: [],
        pattern: capital_f_.call(d__ * (a__ + b__ * (c__ * x_.pow(n_)).log()))
            / x_,
        with: [capital_f_, d__, a__, b__, c__, n_, x_],
        optional: [d__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, n_], x_)
                && rubi_function_head_member_q(
                    &capital_f_,
                    &[rubi_symbols().fresnel_s, rubi_symbols().fresnel_c],
                )
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let payload =
                rubi_function_head_symbol(&capital_f_).rubi_rhs().call(&d__ * (&a__ + &b__ * sub_atom));
            rubi_star(Atom::num(1) / &n_, rubi_subst(&payload, sub, (&c__ * x_.pow(&n_)).log()))
        },
    ));
}

fn push_rules_rule_7025(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 7025,
        source: "Int[(e_.*x_)^m_.*FresnelS[d_.*(a_.+b_.*Log[c_.*x_^n_.])],x_Symbol] :=
          (e*x)^(m+1)*FresnelS[d*(a+b*Log[c*x^n])]/(e*(m+1)) -
          b*d*n/(m+1) \\[Star] Int[(e*x)^m*Sin[Pi/2*(d*(a+b*Log[c*x^n]))^2],x] /;
        FreeQ[{a,b,c,d,e,m,n},x] && NeQ[m,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern: (e__ * x_).pow(m_) * rubi_fresnel_s(d__ * (a__ + b__ * (c__ * x_.pow(n_)).log())),
        with: [e__, m_, d__, a__, b__, c__, n_, x_],
        optional: [e__, m_, d__, a__, b__, c__, n_],
        when: { freeq!([a__, b__, c__, d__, e__, m_, n_], x_) && neq!(m_, -1) },
        rhs: {
            let scaled = &e__ * x_;
            let pi = Atom::var(Symbol::PI);
            let argument = &d__ * (&a__ + &b__ * (&c__ * x_.pow(&n_)).log());
            rubi_simp(&(scaled.pow(&m_ + 1) * rubi_fresnel_s(&argument) / (&e__ * (&m_ + 1))), x_)
                    - rubi_star(&b__ * &d__ * &n_ / (&m_ + 1), rubi_rhs_int(&(scaled.pow(&m_) * (pi / 2 * argument.pow(2)).sin()), x_))
        },
    ));
}

fn push_rules_rule_7026(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 7026,
        source: "Int[(e_.*x_)^m_.*FresnelC[d_.*(a_.+b_.*Log[c_.*x_^n_.])],x_Symbol] :=
          (e*x)^(m+1)*FresnelC[d*(a+b*Log[c*x^n])]/(e*(m+1)) -
          b*d*n/(m+1) \\[Star] Int[(e*x)^m*Cos[Pi/2*(d*(a+b*Log[c*x^n]))^2],x] /;
        FreeQ[{a,b,c,d,e,m,n},x] && NeQ[m,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern: (e__ * x_).pow(m_) * rubi_fresnel_c(d__ * (a__ + b__ * (c__ * x_.pow(n_)).log())),
        with: [e__, m_, d__, a__, b__, c__, n_, x_],
        optional: [e__, m_, d__, a__, b__, c__, n_],
        when: { freeq!([a__, b__, c__, d__, e__, m_, n_], x_) && neq!(m_, -1) },
        rhs: {
            let scaled = &e__ * x_;
            let pi = Atom::var(Symbol::PI);
            let argument = &d__ * (&a__ + &b__ * (&c__ * x_.pow(&n_)).log());
            rubi_simp(&(scaled.pow(&m_ + 1) * rubi_fresnel_c(&argument) / (&e__ * (&m_ + 1))), x_)
                    - rubi_star(&b__ * &d__ * &n_ / (&m_ + 1), rubi_rhs_int(&(scaled.pow(&m_) * (pi / 2 * argument.pow(2)).cos()), x_))
        },
    ));
}

// Generated shared pattern builders.

#[inline(never)]
fn rubi_shared_pattern_0(symbols: &RubiSymbols) -> Atom {
    let b__ = symbols.b__;
    let d__ = symbols.d__;
    let m_ = symbols.m_;
    let x_ = symbols.x_;
    x_.pow(m_) * (d__ * x_.pow(2)).cos() * rubi_fresnel_c(b__ * x_)
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let b__ = symbols.b__;
    let d__ = symbols.d__;
    let m_ = symbols.m_;
    let x_ = symbols.x_;
    x_.pow(m_) * (d__ * x_.pow(2)).cos() * rubi_fresnel_s(b__ * x_)
}

#[inline(never)]
fn rubi_shared_pattern_2(symbols: &RubiSymbols) -> Atom {
    let b__ = symbols.b__;
    let d__ = symbols.d__;
    let m_ = symbols.m_;
    let x_ = symbols.x_;
    x_.pow(m_) * (d__ * x_.pow(2)).sin() * rubi_fresnel_c(b__ * x_)
}

#[inline(never)]
fn rubi_shared_pattern_3(symbols: &RubiSymbols) -> Atom {
    let b__ = symbols.b__;
    let d__ = symbols.d__;
    let m_ = symbols.m_;
    let x_ = symbols.x_;
    x_.pow(m_) * (d__ * x_.pow(2)).sin() * rubi_fresnel_s(b__ * x_)
}
