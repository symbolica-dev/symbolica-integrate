use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_6903(rules);
    push_rules_rule_6904(rules);
    push_rules_rule_6905(rules);
    push_rules_rule_6906(rules);
    push_rules_rule_6907(rules);
    push_rules_rule_6908(rules);
    push_rules_rule_6909(rules);
    push_rules_rule_6910(rules);
    push_rules_rule_6911(rules);
    push_rules_rule_6912(rules);
    push_rules_rule_6913(rules);
    push_rules_rule_6914(rules);
    push_rules_rule_6915(rules);
    push_rules_rule_6916(rules);
    push_rules_rule_6917(rules);
    push_rules_rule_6918(rules);
    push_rules_rule_6919(rules);
    push_rules_rule_6920(rules);
    push_rules_rule_6921(rules);
    push_rules_rule_6922(rules);
    push_rules_rule_6923(rules);
    push_rules_rule_6924(rules);
    push_rules_rule_6925(rules);
    push_rules_rule_6926(rules);
    push_rules_rule_6927(rules);
    push_rules_rule_6928(rules);
    push_rules_rule_6929(rules);
    push_rules_rule_6930(rules);
    push_rules_rule_6931(rules);
    push_rules_rule_6932(rules);
    push_rules_rule_6933(rules);
    push_rules_rule_6934(rules);
    push_rules_rule_6935(rules);
    push_rules_rule_6936(rules);
    push_rules_rule_6937(rules);
    push_rules_rule_6938(rules);
    push_rules_rule_6939(rules);
    push_rules_rule_6940(rules);
    push_rules_rule_6941(rules);
    push_rules_rule_6942(rules);
    push_rules_rule_6943(rules);
    push_rules_rule_6944(rules);
    push_rules_rule_6945(rules);
    push_rules_rule_6946(rules);
    push_rules_rule_6947(rules);
    push_rules_rule_6948(rules);
    push_rules_rule_6949(rules);
    push_rules_rule_6950(rules);
    push_rules_rule_6951(rules);
    push_rules_rule_6952(rules);
    push_rules_rule_6953(rules);
    push_rules_rule_6954(rules);
    push_rules_rule_6955(rules);
    push_rules_rule_6956(rules);
    push_rules_rule_6957(rules);
    push_rules_rule_6958(rules);
    push_rules_rule_6959(rules);
    push_rules_rule_6960(rules);
    push_rules_rule_6961(rules);
    push_rules_rule_6962(rules);
    push_rules_rule_6963(rules);
    push_rules_rule_6964(rules);
    push_rules_rule_6965(rules);
    push_rules_rule_6966(rules);
    push_rules_rule_6967(rules);
    push_rules_rule_6968(rules);
    push_rules_rule_6969(rules);
    push_rules_rule_6970(rules);
    push_rules_rule_6971(rules);
}

fn push_rules_rule_6903(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, x_);
    rules.push(rubi_rule!(
        order: 6903,
        source: "Int[Erf[a_.+b_.*x_],x_Symbol] :=
          (a+b*x)*Erf[a+b*x]/b + 1/(b*Sqrt[Pi]*E^(a+b*x)^2) /;
        FreeQ[{a,b},x]",
        desc: "Integration by parts",
        refs: ["G&R 5.41"],
        pattern: (a__ + b__ * x_).erf(),
        with: [a__, b__, x_],
        optional: [a__, b__],
        when: { freeq!([a__, b__], x_) },
        rhs: {
            let argument = &a__ + &b__ * x_;
            rubi_simp(&(&argument * argument.erf() / &b__), x_) + rubi_simp(&(Atom::num(1) / (&b__ * Atom::var(Symbol::PI).sqrt() * argument.pow(2).exp())), x_)
        },
    ));
}

fn push_rules_rule_6904(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, x_);
    rules.push(rubi_rule!(
        order: 6904,
        source: "Int[Erfc[a_.+b_.*x_],x_Symbol] :=
          (a+b*x)*Erfc[a+b*x]/b - 1/(b*Sqrt[Pi]*E^(a+b*x)^2) /;
        FreeQ[{a,b},x]",
        desc: "Integration by parts",
        refs: ["G&R 5.41"],
        pattern: rubi_erfc(a__ + b__ * x_),
        with: [a__, b__, x_],
        optional: [a__, b__],
        when: { freeq!([a__, b__], x_) },
        rhs: {
            let argument = &a__ + &b__ * x_;
            rubi_simp(&(&argument * rubi_erfc(&argument) / &b__), x_) - rubi_simp(&(Atom::num(1) / (&b__ * Atom::var(Symbol::PI).sqrt() * argument.pow(2).exp())), x_)
        },
    ));
}

fn push_rules_rule_6905(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, x_);
    rules.push(rubi_rule!(
        order: 6905,
        source: "Int[Erfi[a_.+b_.*x_],x_Symbol] :=
          (a+b*x)*Erfi[a+b*x]/b - E^(a+b*x)^2/(b*Sqrt[Pi]) /;
        FreeQ[{a,b},x]",
        desc: "Integration by parts",
        refs: ["G&R 5.41"],
        pattern: rubi_erfi(a__ + b__ * x_),
        with: [a__, b__, x_],
        optional: [a__, b__],
        when: { freeq!([a__, b__], x_) },
        rhs: {
            let argument = &a__ + &b__ * x_;
            rubi_simp(&(&argument * rubi_erfi(&argument) / &b__), x_) - rubi_simp(&(argument.pow(2).exp() / (&b__ * Atom::var(Symbol::PI).sqrt())), x_)
        },
    ));
}

fn push_rules_rule_6906(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, x_);
    rules.push(rubi_rule!(
        order: 6906,
        source: "Int[Erf[a_.+b_.*x_]^2,x_Symbol] :=
          (a+b*x)*Erf[a+b*x]^2/b -
          4/Sqrt[Pi] \\[Star] Int[(a+b*x)*Erf[a+b*x]/E^(a+b*x)^2,x] /;
        FreeQ[{a,b},x]",
        desc: "Integration by parts",
        refs: [],
        pattern: (a__ + b__ * x_).erf().pow(2),
        with: [a__, b__, x_],
        optional: [a__, b__],
        when: { freeq!([a__, b__], x_) },
        rhs: {
            let argument = &a__ + &b__ * x_;
            rubi_simp(&(&argument * &argument.erf().pow(2) / &b__), x_)
                    - rubi_star(Atom::num(4), rubi_rhs_int(&(&argument * argument.erf() / argument.pow(2).exp()), x_)
                        / Atom::var(Symbol::PI).sqrt())
        },
    ));
}

fn push_rules_rule_6907(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, x_);
    rules.push(rubi_rule!(
        order: 6907,
        source: "Int[Erfc[a_.+b_.*x_]^2,x_Symbol] :=
          (a+b*x)*Erfc[a+b*x]^2/b +
          4/Sqrt[Pi] \\[Star] Int[(a+b*x)*Erfc[a+b*x]/E^(a+b*x)^2,x] /;
        FreeQ[{a,b},x]",
        desc: "Integration by parts",
        refs: [],
        pattern: rubi_erfc(a__ + b__ * x_).pow(2),
        with: [a__, b__, x_],
        optional: [a__, b__],
        when: { freeq!([a__, b__], x_) },
        rhs: {
            let argument = &a__ + &b__ * x_;
            rubi_simp(&(&argument * rubi_erfc(&argument).pow(2) / &b__), x_)
                    + rubi_star(Atom::num(4), rubi_rhs_int(&(&argument * rubi_erfc(&argument) / argument.pow(2).exp()), x_)
                        / Atom::var(Symbol::PI).sqrt())
        },
    ));
}

fn push_rules_rule_6908(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, x_);
    rules.push(rubi_rule!(
        order: 6908,
        source: "Int[Erfi[a_.+b_.*x_]^2,x_Symbol] :=
          (a+b*x)*Erfi[a+b*x]^2/b -
          4/Sqrt[Pi] \\[Star] Int[(a+b*x)*E^(a+b*x)^2*Erfi[a+b*x],x] /;
        FreeQ[{a,b},x]",
        desc: "Integration by parts",
        refs: [],
        pattern: rubi_erfi(a__ + b__ * x_).pow(2),
        with: [a__, b__, x_],
        optional: [a__, b__],
        when: { freeq!([a__, b__], x_) },
        rhs: {
            let argument = &a__ + &b__ * x_;
            rubi_simp(&(&argument * rubi_erfi(&argument).pow(2) / &b__), x_)
                    - rubi_star(Atom::num(4), rubi_rhs_int(&(&argument * argument.pow(2).exp() * rubi_erfi(argument)), x_)
                        / Atom::var(Symbol::PI).sqrt())
        },
    ));
}

fn push_rules_rule_6909(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, n_, x_);
    rules.push(rubi_rule!(
        order: 6909,
        source: "Int[Erf[a_.+b_.*x_]^n_,x_Symbol] :=
          Unintegrable[Erf[a+b*x]^n,x] /;
        FreeQ[{a,b,n},x] && NeQ[n,1] && NeQ[n,2]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern: (a__ + b__ * x_).erf().pow(n_),
        with: [a__, b__, n_, x_],
        optional: [a__, b__],
        when: { freeq!([a__, b__, n_], x_) && neq!(n_, 1) && neq!(n_, 2) },
        rhs: {
            let argument = &a__ + &b__ * x_;
            rubi_unintegrable(argument.erf().pow(&n_), x_)
        },
    ));
}

fn push_rules_rule_6910(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, n_, x_);
    rules.push(rubi_rule!(
        order: 6910,
        source: "Int[Erfc[a_.+b_.*x_]^n_,x_Symbol] :=
          Unintegrable[Erfc[a+b*x]^n,x] /;
        FreeQ[{a,b,n},x] && NeQ[n,1] && NeQ[n,2]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern: rubi_erfc(a__ + b__ * x_).pow(n_),
        with: [a__, b__, n_, x_],
        optional: [a__, b__],
        when: { freeq!([a__, b__, n_], x_) && neq!(n_, 1) && neq!(n_, 2) },
        rhs: {
            let argument = &a__ + &b__ * x_;
            rubi_unintegrable(rubi_erfc(argument).pow(&n_), x_)
        },
    ));
}

fn push_rules_rule_6911(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, n_, x_);
    rules.push(rubi_rule!(
        order: 6911,
        source: "Int[Erfi[a_.+b_.*x_]^n_,x_Symbol] :=
          Unintegrable[Erfi[a+b*x]^n,x] /;
        FreeQ[{a,b,n},x] && NeQ[n,1] && NeQ[n,2]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern: rubi_erfi(a__ + b__ * x_).pow(n_),
        with: [a__, b__, n_, x_],
        optional: [a__, b__],
        when: { freeq!([a__, b__, n_], x_) && neq!(n_, 1) && neq!(n_, 2) },
        rhs: {
            let argument = &a__ + &b__ * x_;
            rubi_unintegrable(rubi_erfi(argument).pow(&n_), x_)
        },
    ));
}

fn push_rules_rule_6912(rules: &mut Vec<RubiRule>) {
    rubi_symb!(b__, x_);
    rules.push(rubi_rule!(
        order: 6912,
        source: "Int[Erf[b_.*x_]/x_,x_Symbol] :=
          2*b*x/Sqrt[Pi]*HypergeometricPFQ[{1/2,1/2},{3/2,3/2},-b^2*x^2] /;
        FreeQ[b,x]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: (b__ * x_).erf() / x_,
        with: [b__, x_],
        optional: [b__],
        when: { freeq!(b__, x_) },
        rhs: {
            rubi_simp(&(Atom::num(2) * &b__ * x_
                    * rubi_hypergeometric_pfq_2_2(
                        Atom::num(1) / 2,
                        Atom::num(1) / 2,
                        Atom::num(3) / 2,
                        Atom::num(3) / 2,
                        -b__.pow(2) * x_.pow(2),
                    )
                    / Atom::var(Symbol::PI).sqrt()), x_)
        },
    ));
}

fn push_rules_rule_6913(rules: &mut Vec<RubiRule>) {
    rubi_symb!(b__, x_);
    rules.push(rubi_rule!(
        order: 6913,
        source: "Int[Erfc[b_.*x_]/x_,x_Symbol] :=
          Log[x] - Int[Erf[b*x]/x,x] /;
        FreeQ[b,x]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern: rubi_erfc(b__ * x_) / x_,
        with: [b__, x_],
        optional: [b__],
        when: { freeq!(b__, x_) },
        rhs: {
            rubi_simp(&(x_.log()), x_) - rubi_rhs_int(&((&b__ * x_).erf() / x_), x_)
        },
    ));
}

fn push_rules_rule_6914(rules: &mut Vec<RubiRule>) {
    rubi_symb!(b__, x_);
    rules.push(rubi_rule!(
        order: 6914,
        source: "Int[Erfi[b_.*x_]/x_,x_Symbol] :=
          2*b*x/Sqrt[Pi]*HypergeometricPFQ[{1/2,1/2},{3/2,3/2},b^2*x^2] /;
        FreeQ[b,x]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: rubi_erfi(b__ * x_) / x_,
        with: [b__, x_],
        optional: [b__],
        when: { freeq!(b__, x_) },
        rhs: {
            rubi_simp(&(Atom::num(2) * &b__ * x_
                    * rubi_hypergeometric_pfq_2_2(
                        Atom::num(1) / 2,
                        Atom::num(1) / 2,
                        Atom::num(3) / 2,
                        Atom::num(3) / 2,
                        b__.pow(2) * x_.pow(2),
                    )
                    / Atom::var(Symbol::PI).sqrt()), x_)
        },
    ));
}

fn push_rules_rule_6915(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, x_);
    rules.push(rubi_rule!(
        order: 6915,
        source: "Int[(c_.+d_.*x_)^m_.*Erf[a_.+b_.*x_],x_Symbol] :=
          (c+d*x)^(m+1)*Erf[a+b*x]/(d*(m+1)) -
          2*b/(Sqrt[Pi]*d*(m+1)) \\[Star] Int[(c+d*x)^(m+1)/E^(a+b*x)^2,x] /;
        FreeQ[{a,b,c,d,m},x] && NeQ[m,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern: (c__ + d__ * x_).pow(m_) * (a__ + b__ * x_).erf(),
        with: [c__, d__, m_, a__, b__, x_],
        optional: [c__, d__, m_, a__, b__],
        when: { freeq!([a__, b__, c__, d__, m_], x_) && neq!(m_, -1) },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let argument = &a__ + &b__ * x_;
            rubi_simp(&(linear.pow(&m_ + 1) * &argument.erf() / (&d__ * (&m_ + 1))), x_)
                    - rubi_star(Atom::num(2) * &b__ / (Atom::var(Symbol::PI).sqrt() * &d__ * (&m_ + 1)), rubi_rhs_int(&(linear.pow(&m_ + 1) / argument.pow(2).exp()), x_))
        },
    ));
}

fn push_rules_rule_6916(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, x_);
    rules.push(rubi_rule!(
        order: 6916,
        source: "Int[(c_.+d_.*x_)^m_.*Erfc[a_.+b_.*x_],x_Symbol] :=
          (c+d*x)^(m+1)*Erfc[a+b*x]/(d*(m+1)) +
          2*b/(Sqrt[Pi]*d*(m+1)) \\[Star] Int[(c+d*x)^(m+1)/E^(a+b*x)^2,x] /;
        FreeQ[{a,b,c,d,m},x] && NeQ[m,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern: (c__ + d__ * x_).pow(m_) * rubi_erfc(a__ + b__ * x_),
        with: [c__, d__, m_, a__, b__, x_],
        optional: [c__, d__, m_, a__, b__],
        when: { freeq!([a__, b__, c__, d__, m_], x_) && neq!(m_, -1) },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let argument = &a__ + &b__ * x_;
            rubi_simp(&(linear.pow(&m_ + 1) * rubi_erfc(&argument) / (&d__ * (&m_ + 1))), x_)
                    + rubi_star(Atom::num(2) * &b__ / (Atom::var(Symbol::PI).sqrt() * &d__ * (&m_ + 1)), rubi_rhs_int(&(linear.pow(&m_ + 1) / argument.pow(2).exp()), x_))
        },
    ));
}

fn push_rules_rule_6917(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, x_);
    rules.push(rubi_rule!(
        order: 6917,
        source: "Int[(c_.+d_.*x_)^m_.*Erfi[a_.+b_.*x_],x_Symbol] :=
          (c+d*x)^(m+1)*Erfi[a+b*x]/(d*(m+1)) -
          2*b/(Sqrt[Pi]*d*(m+1)) \\[Star] Int[(c+d*x)^(m+1)*E^(a+b*x)^2,x] /;
        FreeQ[{a,b,c,d,m},x] && NeQ[m,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern: (c__ + d__ * x_).pow(m_) * rubi_erfi(a__ + b__ * x_),
        with: [c__, d__, m_, a__, b__, x_],
        optional: [c__, d__, m_, a__, b__],
        when: { freeq!([a__, b__, c__, d__, m_], x_) && neq!(m_, -1) },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let argument = &a__ + &b__ * x_;
            rubi_simp(&(linear.pow(&m_ + 1) * rubi_erfi(&argument) / (&d__ * (&m_ + 1))), x_)
                    - rubi_star(Atom::num(2) * &b__ / (Atom::var(Symbol::PI).sqrt() * &d__ * (&m_ + 1)), rubi_rhs_int(&(linear.pow(&m_ + 1) * argument.pow(2).exp()), x_))
        },
    ));
}

fn push_rules_rule_6918(rules: &mut Vec<RubiRule>) {
    rubi_symb!(b__, m_, x_);
    rules.push(rubi_rule!(
        order: 6918,
        source: "Int[x_^m_.*Erf[b_.*x_]^2,x_Symbol] :=
          x^(m+1)*Erf[b*x]^2/(m+1) -
          4*b/(Sqrt[Pi]*(m+1)) \\[Star] Int[x^(m+1)*E^(-b^2*x^2)*Erf[b*x],x] /;
        FreeQ[b,x] && (IGtQ[m,0] || ILtQ[(m+1)/2,0])",
        desc: "Integration by parts",
        refs: [],
        pattern: x_.pow(m_) * (b__ * x_).erf().pow(2),
        with: [m_, b__, x_],
        optional: [m_, b__],
        when: {
            freeq!(b__, x_) && (igtq!(m_, 0) || iltq!((&m_ + 1) / 2, 0))
        },
        rhs: {
            let argument = &b__ * x_;
            rubi_simp(&(x_.pow(&m_ + 1) * &argument.erf().pow(2) / (&m_ + 1)), x_)
                    - rubi_star(Atom::num(4) * &b__ / (Atom::var(Symbol::PI).sqrt() * (&m_ + 1)), rubi_rhs_int(
                            &(x_.pow(&m_ + 1) * (-b__.pow(2) * x_.pow(2)).exp() * argument.erf()),
                            x_,
                        ))
        },
    ));
}

fn push_rules_rule_6919(rules: &mut Vec<RubiRule>) {
    rubi_symb!(b__, m_, x_);
    rules.push(rubi_rule!(
        order: 6919,
        source: "Int[x_^m_.*Erfc[b_.*x_]^2,x_Symbol] :=
          x^(m+1)*Erfc[b*x]^2/(m+1) +
          4*b/(Sqrt[Pi]*(m+1)) \\[Star] Int[x^(m+1)*E^(-b^2*x^2)*Erfc[b*x],x] /;
        FreeQ[b,x] && (IGtQ[m,0] || ILtQ[(m+1)/2,0])",
        desc: "Integration by parts",
        refs: [],
        pattern: x_.pow(m_) * rubi_erfc(b__ * x_).pow(2),
        with: [m_, b__, x_],
        optional: [m_, b__],
        when: {
            freeq!(b__, x_) && (igtq!(m_, 0) || iltq!((&m_ + 1) / 2, 0))
        },
        rhs: {
            let argument = &b__ * x_;
            rubi_simp(&(x_.pow(&m_ + 1) * rubi_erfc(&argument).pow(2) / (&m_ + 1)), x_)
                    + rubi_star(Atom::num(4) * &b__ / (Atom::var(Symbol::PI).sqrt() * (&m_ + 1)), rubi_rhs_int(
                            &(x_.pow(&m_ + 1) * (-b__.pow(2) * x_.pow(2)).exp() * rubi_erfc(argument)),
                            x_,
                        ))
        },
    ));
}

fn push_rules_rule_6920(rules: &mut Vec<RubiRule>) {
    rubi_symb!(b__, m_, x_);
    rules.push(rubi_rule!(
        order: 6920,
        source: "Int[x_^m_.*Erfi[b_.*x_]^2,x_Symbol] :=
          x^(m+1)*Erfi[b*x]^2/(m+1) -
          4*b/(Sqrt[Pi]*(m+1)) \\[Star] Int[x^(m+1)*E^(b^2*x^2)*Erfi[b*x],x] /;
        FreeQ[b,x] && (IGtQ[m,0] || ILtQ[(m+1)/2,0])",
        desc: "Integration by parts",
        refs: [],
        pattern: x_.pow(m_) * rubi_erfi(b__ * x_).pow(2),
        with: [m_, b__, x_],
        optional: [m_, b__],
        when: {
            freeq!(b__, x_) && (igtq!(m_, 0) || iltq!((&m_ + 1) / 2, 0))
        },
        rhs: {
            let argument = &b__ * x_;
            rubi_simp(&(x_.pow(&m_ + 1) * rubi_erfi(&argument).pow(2) / (&m_ + 1)), x_)
                    - rubi_star(Atom::num(4) * &b__ / (Atom::var(Symbol::PI).sqrt() * (&m_ + 1)), rubi_rhs_int(
                            &(x_.pow(&m_ + 1) * (b__.pow(2) * x_.pow(2)).exp() * rubi_erfi(argument)),
                            x_,
                        ))
        },
    ));
}

fn push_rules_rule_6921(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a_, b__, c__, d__, m_, x_);
    rules.push(rubi_rule!(
        order: 6921,
        source: "Int[(c_.+d_.*x_)^m_.*Erf[a_+b_.*x_]^2,x_Symbol] :=
          1/b^(m+1) \\[Star] Subst[Int[ExpandIntegrand[Erf[x]^2,(b*c-a*d+d*x)^m,x],x],x,a+b*x] /;
        FreeQ[{a,b,c,d},x] && IGtQ[m,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (c__ + d__ * x_).pow(m_) * (a_ + b__ * x_).erf().pow(2),
        with: [c__, d__, m_, a_, b__, x_],
        optional: [c__, d__, m_, b__],
        when: { freeq!([a_, b__, c__, d__], x_) && igtq!(m_, 0) },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let linear = &b__ * &c__ - &a_ * &d__ + &d__ * &sub_atom;
            let expanded = rubi_expand_integrand(&(sub_atom.erf().pow(2) * linear.pow(&m_)), sub);
            let primitive = rubi_rhs_int(&expanded, sub);
            rubi_star(Atom::num(1) / b__.pow(&m_ + 1), rubi_subst(&primitive, sub, &a_ + &b__ * x_))
        },
    ));
}

fn push_rules_rule_6922(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a_, b__, c__, d__, m_, x_);
    rules.push(rubi_rule!(
        order: 6922,
        source: "Int[(c_.+d_.*x_)^m_.*Erfc[a_+b_.*x_]^2,x_Symbol] :=
          1/b^(m+1) \\[Star] Subst[Int[ExpandIntegrand[Erfc[x]^2,(b*c-a*d+d*x)^m,x],x],x,a+b*x] /;
        FreeQ[{a,b,c,d},x] && IGtQ[m,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (c__ + d__ * x_).pow(m_) * rubi_erfc(a_ + b__ * x_).pow(2),
        with: [c__, d__, m_, a_, b__, x_],
        optional: [c__, d__, m_, b__],
        when: { freeq!([a_, b__, c__, d__], x_) && igtq!(m_, 0) },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let linear = &b__ * &c__ - &a_ * &d__ + &d__ * &sub_atom;
            let expanded = rubi_expand_integrand(&(rubi_erfc(sub_atom).pow(2) * linear.pow(&m_)), sub);
            let primitive = rubi_rhs_int(&expanded, sub);
            rubi_star(Atom::num(1) / b__.pow(&m_ + 1), rubi_subst(&primitive, sub, &a_ + &b__ * x_))
        },
    ));
}

fn push_rules_rule_6923(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a_, b__, c__, d__, m_, x_);
    rules.push(rubi_rule!(
        order: 6923,
        source: "Int[(c_.+d_.*x_)^m_.*Erfi[a_+b_.*x_]^2,x_Symbol] :=
          1/b^(m+1) \\[Star] Subst[Int[ExpandIntegrand[Erfi[x]^2,(b*c-a*d+d*x)^m,x],x],x,a+b*x] /;
        FreeQ[{a,b,c,d},x] && IGtQ[m,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (c__ + d__ * x_).pow(m_) * rubi_erfi(a_ + b__ * x_).pow(2),
        with: [c__, d__, m_, a_, b__, x_],
        optional: [c__, d__, m_, b__],
        when: { freeq!([a_, b__, c__, d__], x_) && igtq!(m_, 0) },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let linear = &b__ * &c__ - &a_ * &d__ + &d__ * &sub_atom;
            let expanded = rubi_expand_integrand(&(rubi_erfi(sub_atom).pow(2) * linear.pow(&m_)), sub);
            let primitive = rubi_rhs_int(&expanded, sub);
            rubi_star(Atom::num(1) / b__.pow(&m_ + 1), rubi_subst(&primitive, sub, &a_ + &b__ * x_))
        },
    ));
}

fn push_rules_rule_6924(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 6924,
        source: "Int[(c_.+d_.*x_)^m_.*Erf[a_.+b_.*x_]^n_.,x_Symbol] :=
          Unintegrable[(c+d*x)^m*Erf[a+b*x]^n,x] /;
        FreeQ[{a,b,c,d,m,n},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern: (c__ + d__ * x_).pow(m_) * (a__ + b__ * x_).erf().pow(n_),
        with: [c__, d__, m_, a__, b__, n_, x_],
        optional: [c__, d__, m_, a__, b__, n_],
        when: { freeq!([a__, b__, c__, d__, m_, n_], x_) },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let argument = &a__ + &b__ * x_;
            rubi_unintegrable(linear.pow(&m_) * argument.erf().pow(&n_), x_)
        },
    ));
}

fn push_rules_rule_6925(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 6925,
        source: "Int[(c_.+d_.*x_)^m_.*Erfc[a_.+b_.*x_]^n_.,x_Symbol] :=
          Unintegrable[(c+d*x)^m*Erfc[a+b*x]^n,x] /;
        FreeQ[{a,b,c,d,m,n},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern: (c__ + d__ * x_).pow(m_) * rubi_erfc(a__ + b__ * x_).pow(n_),
        with: [c__, d__, m_, a__, b__, n_, x_],
        optional: [c__, d__, m_, a__, b__, n_],
        when: { freeq!([a__, b__, c__, d__, m_, n_], x_) },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let argument = &a__ + &b__ * x_;
            rubi_unintegrable(linear.pow(&m_) * rubi_erfc(argument).pow(&n_), x_)
        },
    ));
}

fn push_rules_rule_6926(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 6926,
        source: "Int[(c_.+d_.*x_)^m_.*Erfi[a_.+b_.*x_]^n_.,x_Symbol] :=
          Unintegrable[(c+d*x)^m*Erfi[a+b*x]^n,x] /;
        FreeQ[{a,b,c,d,m,n},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern: (c__ + d__ * x_).pow(m_) * rubi_erfi(a__ + b__ * x_).pow(n_),
        with: [c__, d__, m_, a__, b__, n_, x_],
        optional: [c__, d__, m_, a__, b__, n_],
        when: { freeq!([a__, b__, c__, d__, m_, n_], x_) },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let argument = &a__ + &b__ * x_;
            rubi_unintegrable(linear.pow(&m_) * rubi_erfi(argument).pow(&n_), x_)
        },
    ));
}

fn push_rules_rule_6927(rules: &mut Vec<RubiRule>) {
    rubi_symb!(b__, c__, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 6927,
        source: "Int[E^(c_.+d_.*x_^2)*Erf[b_.*x_]^n_.,x_Symbol] :=
          E^c*Sqrt[Pi]/(2*b) \\[Star] Subst[Int[x^n,x],x,Erf[b*x]] /;
        FreeQ[{b,c,d,n},x] && EqQ[d,-b^2]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (c__ + d__ * x_.pow(2)).exp() * (b__ * x_).erf().pow(n_),
        with: [c__, d__, b__, n_, x_],
        optional: [c__, d__, b__, n_],
        when: { freeq!([b__, c__, d__, n_], x_) && eqq!(&d__ + b__.pow(2), 0) },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let primitive = rubi_rhs_int(&sub_atom.pow(&n_), sub);
            let replacement = (&b__ * x_).erf();
            rubi_star(c__.exp() * Atom::var(Symbol::PI).sqrt() / (Atom::num(2) * &b__), rubi_subst(&primitive, sub, replacement))
        },
    ));
}

fn push_rules_rule_6928(rules: &mut Vec<RubiRule>) {
    rubi_symb!(b__, c__, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 6928,
        source: "Int[E^(c_.+d_.*x_^2)*Erfc[b_.*x_]^n_.,x_Symbol] :=
          -E^c*Sqrt[Pi]/(2*b) \\[Star] Subst[Int[x^n,x],x,Erfc[b*x]] /;
        FreeQ[{b,c,d,n},x] && EqQ[d,-b^2]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (c__ + d__ * x_.pow(2)).exp() * rubi_erfc(b__ * x_).pow(n_),
        with: [c__, d__, b__, n_, x_],
        optional: [c__, d__, b__, n_],
        when: { freeq!([b__, c__, d__, n_], x_) && eqq!(&d__ + b__.pow(2), 0) },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let primitive = rubi_rhs_int(&sub_atom.pow(&n_), sub);
            let replacement = rubi_erfc(&b__ * x_);
            rubi_star(-c__.exp() * Atom::var(Symbol::PI).sqrt() / (Atom::num(2) * &b__), rubi_subst(&primitive, sub, replacement))
        },
    ));
}

fn push_rules_rule_6929(rules: &mut Vec<RubiRule>) {
    rubi_symb!(b__, c__, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 6929,
        source: "Int[E^(c_.+d_.*x_^2)*Erfi[b_.*x_]^n_.,x_Symbol] :=
          E^c*Sqrt[Pi]/(2*b) \\[Star] Subst[Int[x^n,x],x,Erfi[b*x]] /;
        FreeQ[{b,c,d,n},x] && EqQ[d,b^2]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (c__ + d__ * x_.pow(2)).exp() * rubi_erfi(b__ * x_).pow(n_),
        with: [c__, d__, b__, n_, x_],
        optional: [c__, d__, b__, n_],
        when: { freeq!([b__, c__, d__, n_], x_) && eqq!(&d__ - b__.pow(2), 0) },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let primitive = rubi_rhs_int(&sub_atom.pow(&n_), sub);
            let replacement = rubi_erfi(&b__ * x_);
            rubi_star(c__.exp() * Atom::var(Symbol::PI).sqrt() / (Atom::num(2) * &b__), rubi_subst(&primitive, sub, replacement))
        },
    ));
}

fn push_rules_rule_6930(rules: &mut Vec<RubiRule>) {
    rubi_symb!(b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 6930,
        source: "Int[E^(c_.+d_.*x_^2)*Erf[b_.*x_],x_Symbol] :=
          b*E^c*x^2/Sqrt[Pi]*HypergeometricPFQ[{1,1},{3/2,2},b^2*x^2] /;
        FreeQ[{b,c,d},x] && EqQ[d,b^2]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: (c__ + d__ * x_.pow(2)).exp() * (b__ * x_).erf(),
        with: [c__, d__, b__, x_],
        optional: [c__, d__, b__],
        when: { freeq!([b__, c__, d__], x_) && eqq!(&d__ - b__.pow(2), 0) },
        rhs: {
            rubi_simp(&(&b__ * c__.exp()
                    * x_.pow(2)
                    * rubi_hypergeometric_pfq_2_2(
                        Atom::num(1),
                        Atom::num(1),
                        Atom::num(3) / 2,
                        Atom::num(2),
                        b__.pow(2) * x_.pow(2),
                    )
                    / Atom::var(Symbol::PI).sqrt()), x_)
        },
    ));
}

fn push_rules_rule_6931(rules: &mut Vec<RubiRule>) {
    rubi_symb!(b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 6931,
        source: "Int[E^(c_.+d_.*x_^2)*Erfc[b_.*x_],x_Symbol] :=
          Int[E^(c+d*x^2),x] - Int[E^(c+d*x^2)*Erf[b*x],x] /;
        FreeQ[{b,c,d},x] && EqQ[d,b^2]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern: (c__ + d__ * x_.pow(2)).exp() * rubi_erfc(b__ * x_),
        with: [c__, d__, b__, x_],
        optional: [c__, d__, b__],
        when: { freeq!([b__, c__, d__], x_) && eqq!(&d__ - b__.pow(2), 0) },
        rhs: {
            let gaussian = (&c__ + &d__ * x_.pow(2)).exp();
            rubi_rhs_int(&gaussian, x_) - rubi_rhs_int(&(gaussian * (&b__ * x_).erf()), x_)
        },
    ));
}

fn push_rules_rule_6932(rules: &mut Vec<RubiRule>) {
    rubi_symb!(b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 6932,
        source: "Int[E^(c_.+d_.*x_^2)*Erfi[b_.*x_],x_Symbol] :=
          b*E^c*x^2/Sqrt[Pi]*HypergeometricPFQ[{1,1},{3/2,2},-b^2*x^2] /;
        FreeQ[{b,c,d},x] && EqQ[d,-b^2]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: (c__ + d__ * x_.pow(2)).exp() * rubi_erfi(b__ * x_),
        with: [c__, d__, b__, x_],
        optional: [c__, d__, b__],
        when: { freeq!([b__, c__, d__], x_) && eqq!(&d__ + b__.pow(2), 0) },
        rhs: {
            rubi_simp(&(&b__ * c__.exp()
                    * x_.pow(2)
                    * rubi_hypergeometric_pfq_2_2(
                        Atom::num(1),
                        Atom::num(1),
                        Atom::num(3) / 2,
                        Atom::num(2),
                        -b__.pow(2) * x_.pow(2),
                    )
                    / Atom::var(Symbol::PI).sqrt()), x_)
        },
    ));
}

fn push_rules_rule_6933(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 6933,
        source: "Int[E^(c_.+d_.*x_^2)*Erf[a_.+b_.*x_]^n_.,x_Symbol] :=
          Unintegrable[E^(c+d*x^2)*Erf[a+b*x]^n,x] /;
        FreeQ[{a,b,c,d,n},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern: (c__ + d__ * x_.pow(2)).exp() * (a__ + b__ * x_).erf().pow(n_),
        with: [c__, d__, a__, b__, n_, x_],
        optional: [c__, d__, a__, b__, n_],
        when: { freeq!([a__, b__, c__, d__, n_], x_) },
        rhs: {
            let gaussian = (&c__ + &d__ * x_.pow(2)).exp();
            let argument = &a__ + &b__ * x_;
            rubi_unintegrable(gaussian * argument.erf().pow(&n_), x_)
        },
    ));
}

fn push_rules_rule_6934(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 6934,
        source: "Int[E^(c_.+d_.*x_^2)*Erfc[a_.+b_.*x_]^n_.,x_Symbol] :=
          Unintegrable[E^(c+d*x^2)*Erfc[a+b*x]^n,x] /;
        FreeQ[{a,b,c,d,n},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern: (c__ + d__ * x_.pow(2)).exp() * rubi_erfc(a__ + b__ * x_).pow(n_),
        with: [c__, d__, a__, b__, n_, x_],
        optional: [c__, d__, a__, b__, n_],
        when: { freeq!([a__, b__, c__, d__, n_], x_) },
        rhs: {
            let gaussian = (&c__ + &d__ * x_.pow(2)).exp();
            let argument = &a__ + &b__ * x_;
            rubi_unintegrable(gaussian * rubi_erfc(argument).pow(&n_), x_)
        },
    ));
}

fn push_rules_rule_6935(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 6935,
        source: "Int[E^(c_.+d_.*x_^2)*Erfi[a_.+b_.*x_]^n_.,x_Symbol] :=
          Unintegrable[E^(c+d*x^2)*Erfi[a+b*x]^n,x] /;
        FreeQ[{a,b,c,d,n},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern: (c__ + d__ * x_.pow(2)).exp() * rubi_erfi(a__ + b__ * x_).pow(n_),
        with: [c__, d__, a__, b__, n_, x_],
        optional: [c__, d__, a__, b__, n_],
        when: { freeq!([a__, b__, c__, d__, n_], x_) },
        rhs: {
            let gaussian = (&c__ + &d__ * x_.pow(2)).exp();
            let argument = &a__ + &b__ * x_;
            rubi_unintegrable(gaussian * rubi_erfi(argument).pow(&n_), x_)
        },
    ));
}

fn push_rules_rule_6936(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 6936,
        source: "Int[x_*E^(c_.+d_.*x_^2)*Erf[a_.+b_.*x_],x_Symbol] :=
          E^(c+d*x^2)*Erf[a+b*x]/(2*d) -
          b/(d*Sqrt[Pi]) \\[Star] Int[E^(-a^2+c-2*a*b*x-(b^2-d)*x^2),x] /;
        FreeQ[{a,b,c,d},x]",
        desc: "Integration by parts",
        refs: [],
        pattern: x_ * (c__ + d__ * x_.pow(2)).exp() * (a__ + b__ * x_).erf(),
        with: [c__, d__, a__, b__, x_],
        optional: [c__, d__, a__, b__],
        when: { freeq!([a__, b__, c__, d__], x_) },
        rhs: {
            let argument = &a__ + &b__ * x_;
            let gaussian = (&c__ + &d__ * x_.pow(2)).exp();
            let recursive_exp = (-a__.pow(2) + &c__ - Atom::num(2) * &a__ * &b__ * x_
                - (b__.pow(2) - &d__) * x_.pow(2))
            .exp();
            rubi_simp(&(gaussian * argument.erf() / (Atom::num(2) * &d__)), x_) - rubi_star(b__, rubi_rhs_int(&recursive_exp, x_) / (&d__ * Atom::var(Symbol::PI).sqrt()))
        },
    ));
}

fn push_rules_rule_6937(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 6937,
        source: "Int[x_*E^(c_.+d_.*x_^2)*Erfc[a_.+b_.*x_],x_Symbol] :=
          E^(c+d*x^2)*Erfc[a+b*x]/(2*d) +
          b/(d*Sqrt[Pi]) \\[Star] Int[E^(-a^2+c-2*a*b*x-(b^2-d)*x^2),x] /;
        FreeQ[{a,b,c,d},x]",
        desc: "Integration by parts",
        refs: [],
        pattern: x_ * (c__ + d__ * x_.pow(2)).exp() * rubi_erfc(a__ + b__ * x_),
        with: [c__, d__, a__, b__, x_],
        optional: [c__, d__, a__, b__],
        when: { freeq!([a__, b__, c__, d__], x_) },
        rhs: {
            let argument = &a__ + &b__ * x_;
            let gaussian = (&c__ + &d__ * x_.pow(2)).exp();
            let recursive_exp = (-a__.pow(2) + &c__ - Atom::num(2) * &a__ * &b__ * x_
                - (b__.pow(2) - &d__) * x_.pow(2))
            .exp();
            rubi_simp(&(gaussian * rubi_erfc(argument) / (Atom::num(2) * &d__)), x_) + rubi_star(b__, rubi_rhs_int(&recursive_exp, x_) / (&d__ * Atom::var(Symbol::PI).sqrt()))
        },
    ));
}

fn push_rules_rule_6938(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 6938,
        source: "Int[x_*E^(c_.+d_.*x_^2)*Erfi[a_.+b_.*x_],x_Symbol] :=
          E^(c+d*x^2)*Erfi[a+b*x]/(2*d) -
          b/(d*Sqrt[Pi]) \\[Star] Int[E^(a^2+c+2*a*b*x+(b^2+d)*x^2),x] /;
        FreeQ[{a,b,c,d},x]",
        desc: "Integration by parts",
        refs: [],
        pattern: x_ * (c__ + d__ * x_.pow(2)).exp() * rubi_erfi(a__ + b__ * x_),
        with: [c__, d__, a__, b__, x_],
        optional: [c__, d__, a__, b__],
        when: { freeq!([a__, b__, c__, d__], x_) },
        rhs: {
            let argument = &a__ + &b__ * x_;
            let gaussian = (&c__ + &d__ * x_.pow(2)).exp();
            let recursive_exp = (a__.pow(2) + &c__ + Atom::num(2) * &a__ * &b__ * x_
                + (b__.pow(2) + &d__) * x_.pow(2))
            .exp();
            rubi_simp(&(gaussian * rubi_erfi(argument) / (Atom::num(2) * &d__)), x_) - rubi_star(b__, rubi_rhs_int(&recursive_exp, x_) / (&d__ * Atom::var(Symbol::PI).sqrt()))
        },
    ));
}

fn push_rules_rule_6939(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, x_);
    rules.push(rubi_rule!(
        order: 6939,
        source: "Int[x_^m_*E^(c_.+d_.*x_^2)*Erf[a_.+b_.*x_],x_Symbol] :=
          x^(m-1)*E^(c+d*x^2)*Erf[a+b*x]/(2*d) -
          b/(d*Sqrt[Pi]) \\[Star] Int[x^(m-1)*E^(-a^2+c-2*a*b*x-(b^2-d)*x^2),x] -
          (m-1)/(2*d) \\[Star] Int[x^(m-2)*E^(c+d*x^2)*Erf[a+b*x],x] /;
        FreeQ[{a,b,c,d},x] && IGtQ[m,1]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [m_, c__, d__, a__, b__, x_],
        optional: [c__, d__, a__, b__],
        when: { freeq!([a__, b__, c__, d__], x_) && igtq!(m_, 1) },
        rhs: {
            let argument = &a__ + &b__ * x_;
            let gaussian = (&c__ + &d__ * x_.pow(2)).exp();
            let recursive_exp = (-a__.pow(2) + &c__ - Atom::num(2) * &a__ * &b__ * x_
                - (b__.pow(2) - &d__) * x_.pow(2))
            .exp();
            let side_integrand = x_.pow(&m_ - 1) * recursive_exp;
            let recursive_integrand =
                x_.pow(&m_ - 2) * &gaussian * &argument.erf();
            rubi_simp(&(x_.pow(&m_ - 1) * gaussian * argument.erf() / (Atom::num(2) * &d__)), x_)
                    - rubi_star(b__, rubi_rhs_int(&side_integrand, x_) / (&d__ * Atom::var(Symbol::PI).sqrt()))
                    - rubi_star(&m_ - 1, rubi_rhs_int(&recursive_integrand, x_) / (Atom::num(2) * &d__))
        },
    ));
}

fn push_rules_rule_6940(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, x_);
    rules.push(rubi_rule!(
        order: 6940,
        source: "Int[x_^m_*E^(c_.+d_.*x_^2)*Erfc[a_.+b_.*x_],x_Symbol] :=
          x^(m-1)*E^(c+d*x^2)*Erfc[a+b*x]/(2*d) +
          b/(d*Sqrt[Pi]) \\[Star] Int[x^(m-1)*E^(-a^2+c-2*a*b*x-(b^2-d)*x^2),x] -
          (m-1)/(2*d) \\[Star] Int[x^(m-2)*E^(c+d*x^2)*Erfc[a+b*x],x] /;
        FreeQ[{a,b,c,d},x] && IGtQ[m,1]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [m_, c__, d__, a__, b__, x_],
        optional: [c__, d__, a__, b__],
        when: { freeq!([a__, b__, c__, d__], x_) && igtq!(m_, 1) },
        rhs: {
            let argument = &a__ + &b__ * x_;
            let gaussian = (&c__ + &d__ * x_.pow(2)).exp();
            let recursive_exp = (-a__.pow(2) + &c__ - Atom::num(2) * &a__ * &b__ * x_
                - (b__.pow(2) - &d__) * x_.pow(2))
            .exp();
            let side_integrand = x_.pow(&m_ - 1) * recursive_exp;
            let recursive_integrand =
                x_.pow(&m_ - 2) * &gaussian * rubi_erfc(&argument);
            rubi_simp(&(x_.pow(&m_ - 1) * gaussian * rubi_erfc(argument) / (Atom::num(2) * &d__)), x_)
                    + rubi_star(b__, rubi_rhs_int(&side_integrand, x_) / (&d__ * Atom::var(Symbol::PI).sqrt()))
                    - rubi_star(&m_ - 1, rubi_rhs_int(&recursive_integrand, x_) / (Atom::num(2) * &d__))
        },
    ));
}

fn push_rules_rule_6941(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, x_);
    rules.push(rubi_rule!(
        order: 6941,
        source: "Int[x_^m_*E^(c_.+d_.*x_^2)*Erfi[a_.+b_.*x_],x_Symbol] :=
          x^(m-1)*E^(c+d*x^2)*Erfi[a+b*x]/(2*d) -
          b/(d*Sqrt[Pi]) \\[Star] Int[x^(m-1)*E^(a^2+c+2*a*b*x+(b^2+d)*x^2),x] -
          (m-1)/(2*d) \\[Star] Int[x^(m-2)*E^(c+d*x^2)*Erfi[a+b*x],x] /;
        FreeQ[{a,b,c,d},x] && IGtQ[m,1]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [m_, c__, d__, a__, b__, x_],
        optional: [c__, d__, a__, b__],
        when: { freeq!([a__, b__, c__, d__], x_) && igtq!(m_, 1) },
        rhs: {
            let argument = &a__ + &b__ * x_;
            let gaussian = (&c__ + &d__ * x_.pow(2)).exp();
            let recursive_exp = (a__.pow(2) + &c__ + Atom::num(2) * &a__ * &b__ * x_
                + (b__.pow(2) + &d__) * x_.pow(2))
            .exp();
            let side_integrand = x_.pow(&m_ - 1) * recursive_exp;
            let recursive_integrand =
                x_.pow(&m_ - 2) * &gaussian * rubi_erfi(&argument);
            rubi_simp(&(x_.pow(&m_ - 1) * gaussian * rubi_erfi(argument) / (Atom::num(2) * &d__)), x_)
                    - rubi_star(b__, rubi_rhs_int(&side_integrand, x_) / (&d__ * Atom::var(Symbol::PI).sqrt()))
                    - rubi_star(&m_ - 1, rubi_rhs_int(&recursive_integrand, x_) / (Atom::num(2) * &d__))
        },
    ));
}

fn push_rules_rule_6942(rules: &mut Vec<RubiRule>) {
    rubi_symb!(b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 6942,
        source: "Int[E^(c_.+d_.*x_^2)*Erf[b_.*x_]/x_,x_Symbol] :=
          2*b*E^c*x/Sqrt[Pi]*HypergeometricPFQ[{1/2,1},{3/2,3/2},b^2*x^2] /;
        FreeQ[{b,c,d},x] && EqQ[d,b^2]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: (c__ + d__ * x_.pow(2)).exp() * (b__ * x_).erf() / x_,
        with: [c__, d__, b__, x_],
        optional: [c__, d__, b__],
        when: { freeq!([b__, c__, d__], x_) && eqq!(&d__ - b__.pow(2), 0) },
        rhs: {
            rubi_simp(&(Atom::num(2) * &b__
                    * c__.exp()
                    * x_
                    * rubi_hypergeometric_pfq_2_2(
                        Atom::num(1) / 2,
                        Atom::num(1),
                        Atom::num(3) / 2,
                        Atom::num(3) / 2,
                        b__.pow(2) * x_.pow(2),
                    )
                    / Atom::var(Symbol::PI).sqrt()), x_)
        },
    ));
}

fn push_rules_rule_6943(rules: &mut Vec<RubiRule>) {
    rubi_symb!(b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 6943,
        source: "Int[E^(c_.+d_.*x_^2)*Erfc[b_.*x_]/x_,x_Symbol] :=
          Int[E^(c+d*x^2)/x,x] - Int[E^(c+d*x^2)*Erf[b*x]/x,x] /;
        FreeQ[{b,c,d},x] && EqQ[d,b^2]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern: (c__ + d__ * x_.pow(2)).exp() * rubi_erfc(b__ * x_) / x_,
        with: [c__, d__, b__, x_],
        optional: [c__, d__, b__],
        when: { freeq!([b__, c__, d__], x_) && eqq!(&d__ - b__.pow(2), 0) },
        rhs: {
            let gaussian = (&c__ + &d__ * x_.pow(2)).exp();
            rubi_rhs_int(&(&gaussian / x_), x_) - rubi_rhs_int(&(gaussian * (&b__ * x_).erf() / x_), x_)
        },
    ));
}

fn push_rules_rule_6944(rules: &mut Vec<RubiRule>) {
    rubi_symb!(b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 6944,
        source: "Int[E^(c_.+d_.*x_^2)*Erfi[b_.*x_]/x_,x_Symbol] :=
          2*b*E^c*x/Sqrt[Pi]*HypergeometricPFQ[{1/2,1},{3/2,3/2},-b^2*x^2] /;
        FreeQ[{b,c,d},x] && EqQ[d,-b^2]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: (c__ + d__ * x_.pow(2)).exp() * rubi_erfi(b__ * x_) / x_,
        with: [c__, d__, b__, x_],
        optional: [c__, d__, b__],
        when: { freeq!([b__, c__, d__], x_) && eqq!(&d__ + b__.pow(2), 0) },
        rhs: {
            rubi_simp(&(Atom::num(2) * &b__
                    * c__.exp()
                    * x_
                    * rubi_hypergeometric_pfq_2_2(
                        Atom::num(1) / 2,
                        Atom::num(1),
                        Atom::num(3) / 2,
                        Atom::num(3) / 2,
                        -b__.pow(2) * x_.pow(2),
                    )
                    / Atom::var(Symbol::PI).sqrt()), x_)
        },
    ));
}

fn push_rules_rule_6945(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, x_);
    rules.push(rubi_rule!(
        order: 6945,
        source: "Int[x_^m_*E^(c_.+d_.*x_^2)*Erf[a_.+b_.*x_],x_Symbol] :=
          x^(m+1)*E^(c+d*x^2)*Erf[a+b*x]/(m+1) -
          2*b/((m+1)*Sqrt[Pi]) \\[Star] Int[x^(m+1)*E^(-a^2+c-2*a*b*x-(b^2-d)*x^2),x] -
          2*d/(m+1) \\[Star] Int[x^(m+2)*E^(c+d*x^2)*Erf[a+b*x],x] /;
        FreeQ[{a,b,c,d},x] && ILtQ[m,-1]",
        desc: "Inverted integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [m_, c__, d__, a__, b__, x_],
        optional: [c__, d__, a__, b__],
        when: { freeq!([a__, b__, c__, d__], x_) && iltq!(m_, -1) },
        rhs: {
            let argument = &a__ + &b__ * x_;
            let gaussian = (&c__ + &d__ * x_.pow(2)).exp();
            let recursive_exp = (-a__.pow(2) + &c__ - Atom::num(2) * &a__ * &b__ * x_
                - (b__.pow(2) - &d__) * x_.pow(2))
            .exp();
            let side_integrand = x_.pow(&m_ + 1) * recursive_exp;
            let recursive_integrand =
                x_.pow(&m_ + 2) * &gaussian * &argument.erf();
            rubi_simp(&(x_.pow(&m_ + 1) * gaussian * argument.erf() / (&m_ + 1)), x_)
                    - rubi_star(Atom::num(2) * &b__ / ((&m_ + 1) * Atom::var(Symbol::PI).sqrt()), rubi_rhs_int(&side_integrand, x_))
                    - rubi_star(Atom::num(2) * &d__ / (&m_ + 1), rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_6946(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, x_);
    rules.push(rubi_rule!(
        order: 6946,
        source: "Int[x_^m_*E^(c_.+d_.*x_^2)*Erfc[a_.+b_.*x_],x_Symbol] :=
          x^(m+1)*E^(c+d*x^2)*Erfc[a+b*x]/(m+1) +
          2*b/((m+1)*Sqrt[Pi]) \\[Star] Int[x^(m+1)*E^(-a^2+c-2*a*b*x-(b^2-d)*x^2),x] -
          2*d/(m+1) \\[Star] Int[x^(m+2)*E^(c+d*x^2)*Erfc[a+b*x],x] /;
        FreeQ[{a,b,c,d},x] && ILtQ[m,-1]",
        desc: "Inverted integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [m_, c__, d__, a__, b__, x_],
        optional: [c__, d__, a__, b__],
        when: { freeq!([a__, b__, c__, d__], x_) && iltq!(m_, -1) },
        rhs: {
            let argument = &a__ + &b__ * x_;
            let gaussian = (&c__ + &d__ * x_.pow(2)).exp();
            let recursive_exp = (-a__.pow(2) + &c__ - Atom::num(2) * &a__ * &b__ * x_
                - (b__.pow(2) - &d__) * x_.pow(2))
            .exp();
            let side_integrand = x_.pow(&m_ + 1) * recursive_exp;
            let recursive_integrand =
                x_.pow(&m_ + 2) * &gaussian * rubi_erfc(&argument);
            rubi_simp(&(x_.pow(&m_ + 1) * gaussian * rubi_erfc(argument) / (&m_ + 1)), x_)
                    + rubi_star(Atom::num(2) * &b__ / ((&m_ + 1) * Atom::var(Symbol::PI).sqrt()), rubi_rhs_int(&side_integrand, x_))
                    - rubi_star(Atom::num(2) * &d__ / (&m_ + 1), rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_6947(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, x_);
    rules.push(rubi_rule!(
        order: 6947,
        source: "Int[x_^m_*E^(c_.+d_.*x_^2)*Erfi[a_.+b_.*x_],x_Symbol] :=
          x^(m+1)*E^(c+d*x^2)*Erfi[a+b*x]/(m+1) -
          2*b/((m+1)*Sqrt[Pi]) \\[Star] Int[x^(m+1)*E^(a^2+c+2*a*b*x+(b^2+d)*x^2),x] -
          2*d/(m+1) \\[Star] Int[x^(m+2)*E^(c+d*x^2)*Erfi[a+b*x],x] /;
        FreeQ[{a,b,c,d},x] && ILtQ[m,-1]",
        desc: "Inverted integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [m_, c__, d__, a__, b__, x_],
        optional: [c__, d__, a__, b__],
        when: { freeq!([a__, b__, c__, d__], x_) && iltq!(m_, -1) },
        rhs: {
            let argument = &a__ + &b__ * x_;
            let gaussian = (&c__ + &d__ * x_.pow(2)).exp();
            let recursive_exp = (a__.pow(2) + &c__ + Atom::num(2) * &a__ * &b__ * x_
                + (b__.pow(2) + &d__) * x_.pow(2))
            .exp();
            let side_integrand = x_.pow(&m_ + 1) * recursive_exp;
            let recursive_integrand =
                x_.pow(&m_ + 2) * &gaussian * rubi_erfi(&argument);
            rubi_simp(&(x_.pow(&m_ + 1) * gaussian * rubi_erfi(argument) / (&m_ + 1)), x_)
                    - rubi_star(Atom::num(2) * &b__ / ((&m_ + 1) * Atom::var(Symbol::PI).sqrt()), rubi_rhs_int(&side_integrand, x_))
                    - rubi_star(Atom::num(2) * &d__ / (&m_ + 1), rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_6948(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 6948,
        source: "Int[(e_.*x_)^m_.*E^(c_.+d_.*x_^2)*Erf[a_.+b_.*x_]^n_.,x_Symbol] :=
          Unintegrable[(e*x)^m*E^(c+d*x^2)*Erf[a+b*x]^n,x] /;
        FreeQ[{a,b,c,d,e,m,n},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern: (e__ * x_).pow(m_) * (c__ + d__ * x_.pow(2)).exp() * (a__ + b__ * x_).erf().pow(n_),
        with: [e__, m_, c__, d__, a__, b__, n_, x_],
        optional: [e__, m_, c__, d__, a__, b__, n_],
        when: { freeq!([a__, b__, c__, d__, e__, m_, n_], x_) },
        rhs: {
            let scaled = &e__ * x_;
            let gaussian = (&c__ + &d__ * x_.pow(2)).exp();
            let argument = &a__ + &b__ * x_;
            rubi_unintegrable(scaled.pow(&m_) * gaussian * argument.erf().pow(&n_), x_)
        },
    ));
}

fn push_rules_rule_6949(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 6949,
        source: "Int[(e_.*x_)^m_.*E^(c_.+d_.*x_^2)*Erfc[a_.+b_.*x_]^n_.,x_Symbol] :=
          Unintegrable[(e*x)^m*E^(c+d*x^2)*Erfc[a+b*x]^n,x] /;
        FreeQ[{a,b,c,d,e,m,n},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern: (e__ * x_).pow(m_) * (c__ + d__ * x_.pow(2)).exp() * rubi_erfc(a__ + b__ * x_).pow(n_),
        with: [e__, m_, c__, d__, a__, b__, n_, x_],
        optional: [e__, m_, c__, d__, a__, b__, n_],
        when: { freeq!([a__, b__, c__, d__, e__, m_, n_], x_) },
        rhs: {
            let scaled = &e__ * x_;
            let gaussian = (&c__ + &d__ * x_.pow(2)).exp();
            let argument = &a__ + &b__ * x_;
            rubi_unintegrable(scaled.pow(&m_) * gaussian * rubi_erfc(argument).pow(&n_), x_)
        },
    ));
}

fn push_rules_rule_6950(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 6950,
        source: "Int[(e_.*x_)^m_.*E^(c_.+d_.*x_^2)*Erfi[a_.+b_.*x_]^n_.,x_Symbol] :=
          Unintegrable[(e*x)^m*E^(c+d*x^2)*Erfi[a+b*x]^n,x] /;
        FreeQ[{a,b,c,d,e,m,n},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern: (e__ * x_).pow(m_) * (c__ + d__ * x_.pow(2)).exp() * rubi_erfi(a__ + b__ * x_).pow(n_),
        with: [e__, m_, c__, d__, a__, b__, n_, x_],
        optional: [e__, m_, c__, d__, a__, b__, n_],
        when: { freeq!([a__, b__, c__, d__, e__, m_, n_], x_) },
        rhs: {
            let scaled = &e__ * x_;
            let gaussian = (&c__ + &d__ * x_.pow(2)).exp();
            let argument = &a__ + &b__ * x_;
            rubi_unintegrable(scaled.pow(&m_) * gaussian * rubi_erfi(argument).pow(&n_), x_)
        },
    ));
}

fn push_rules_rule_6951(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 6951,
        source: "Int[Erf[d_.*(a_.+b_.*Log[c_.*x_^n_.])],x_Symbol] :=
          x*Erf[d*(a+b*Log[c*x^n])] - 2*b*d*n/(Sqrt[Pi]) \\[Star] Int[1/E^(d*(a+b*Log[c*x^n]))^2,x] /;
        FreeQ[{a,b,c,d,n},x]",
        desc: "Integration by parts",
        refs: [],
        pattern: (d__ * (a__ + b__ * (c__ * x_.pow(n_)).log())).erf(),
        with: [d__, a__, b__, c__, n_, x_],
        optional: [d__, a__, b__, c__, n_],
        when: { freeq!([a__, b__, c__, d__, n_], x_) },
        rhs: {
            let argument = &d__ * (&a__ + &b__ * (&c__ * x_.pow(&n_)).log());
            rubi_simp(&(x_ * &argument.erf()), x_)
                    - rubi_star(Atom::num(2) * &b__ * &d__ * &n_ / Atom::var(Symbol::PI).sqrt(), rubi_rhs_int(&(Atom::num(1) / argument.pow(2).exp()), x_))
        },
    ));
}

fn push_rules_rule_6952(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 6952,
        source: "Int[Erfc[d_.*(a_.+b_.*Log[c_.*x_^n_.])],x_Symbol] :=
          x*Erfc[d*(a+b*Log[c*x^n])] + 2*b*d*n/(Sqrt[Pi]) \\[Star] Int[1/E^(d*(a+b*Log[c*x^n]))^2,x] /;
        FreeQ[{a,b,c,d,n},x]",
        desc: "Integration by parts",
        refs: [],
        pattern: rubi_erfc(d__ * (a__ + b__ * (c__ * x_.pow(n_)).log())),
        with: [d__, a__, b__, c__, n_, x_],
        optional: [d__, a__, b__, c__, n_],
        when: { freeq!([a__, b__, c__, d__, n_], x_) },
        rhs: {
            let argument = &d__ * (&a__ + &b__ * (&c__ * x_.pow(&n_)).log());
            rubi_simp(&(x_ * rubi_erfc(&argument)), x_)
                    + rubi_star(Atom::num(2) * &b__ * &d__ * &n_ / Atom::var(Symbol::PI).sqrt(), rubi_rhs_int(&(Atom::num(1) / argument.pow(2).exp()), x_))
        },
    ));
}

fn push_rules_rule_6953(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 6953,
        source: "Int[Erfi[d_.*(a_.+b_.*Log[c_.*x_^n_.])],x_Symbol] :=
          x*Erfi[d*(a+b*Log[c*x^n])] - 2*b*d*n/(Sqrt[Pi]) \\[Star] Int[E^(d*(a+b*Log[c*x^n]))^2,x] /;
        FreeQ[{a,b,c,d,n},x]",
        desc: "Integration by parts",
        refs: [],
        pattern: rubi_erfi(d__ * (a__ + b__ * (c__ * x_.pow(n_)).log())),
        with: [d__, a__, b__, c__, n_, x_],
        optional: [d__, a__, b__, c__, n_],
        when: { freeq!([a__, b__, c__, d__, n_], x_) },
        rhs: {
            let argument = &d__ * (&a__ + &b__ * (&c__ * x_.pow(&n_)).log());
            rubi_simp(&(x_ * rubi_erfi(&argument)), x_)
                    - rubi_star(Atom::num(2) * &b__ * &d__ * &n_ / Atom::var(Symbol::PI).sqrt(), rubi_rhs_int(&argument.pow(2).exp(), x_))
        },
    ));
}

fn push_rules_rule_6954(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_f_, a__, b__, c__, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 6954,
        source: "Int[F_[d_.*(a_.+b_.*Log[c_.*x_^n_.])]/x_,x_Symbol] :=
          1/n \\[Star] Subst[F[d*(a+b*x)],x,Log[c*x^n]] /;
        FreeQ[{a,b,c,d,n},x] && MemberQ[{Erf,Erfc,Erfi},F]",
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
                    &[
                        symbolica::transcendental::erf(),
                        rubi_symbols().erfc,
                        rubi_symbols().erfi,
                    ],
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

fn push_rules_rule_6955(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 6955,
        source: "Int[(e_.*x_)^m_.*Erf[d_.*(a_.+b_.*Log[c_.*x_^n_.])],x_Symbol] :=
          (e*x)^(m+1)*Erf[d*(a+b*Log[c*x^n])]/(e*(m+1)) -
          2*b*d*n/(Sqrt[Pi]*(m+1)) \\[Star] Int[(e*x)^m/E^(d*(a+b*Log[c*x^n]))^2,x] /;
        FreeQ[{a,b,c,d,e,m,n},x] && NeQ[m,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern: (e__ * x_).pow(m_) * (d__ * (a__ + b__ * (c__ * x_.pow(n_)).log())).erf(),
        with: [e__, m_, d__, a__, b__, c__, n_, x_],
        optional: [e__, m_, d__, a__, b__, c__, n_],
        when: { freeq!([a__, b__, c__, d__, e__, m_, n_], x_) && neq!(m_, -1) },
        rhs: {
            let scaled = &e__ * x_;
            let argument = &d__ * (&a__ + &b__ * (&c__ * x_.pow(&n_)).log());
            rubi_simp(&(scaled.pow(&m_ + 1) * &argument.erf() / (&e__ * (&m_ + 1))), x_)
                    - rubi_star(Atom::num(2) * &b__ * &d__ * &n_ / (Atom::var(Symbol::PI).sqrt() * (&m_ + 1)), rubi_rhs_int(&(scaled.pow(&m_) / argument.pow(2).exp()), x_))
        },
    ));
}

fn push_rules_rule_6956(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 6956,
        source: "Int[(e_.*x_)^m_.*Erfc[d_.*(a_.+b_.*Log[c_.*x_^n_.])],x_Symbol] :=
          (e*x)^(m+1)*Erfc[d*(a+b*Log[c*x^n])]/(e*(m+1)) +
          2*b*d*n/(Sqrt[Pi]*(m+1)) \\[Star] Int[(e*x)^m/E^(d*(a+b*Log[c*x^n]))^2,x] /;
        FreeQ[{a,b,c,d,e,m,n},x] && NeQ[m,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern: (e__ * x_).pow(m_) * rubi_erfc(d__ * (a__ + b__ * (c__ * x_.pow(n_)).log())),
        with: [e__, m_, d__, a__, b__, c__, n_, x_],
        optional: [e__, m_, d__, a__, b__, c__, n_],
        when: { freeq!([a__, b__, c__, d__, e__, m_, n_], x_) && neq!(m_, -1) },
        rhs: {
            let scaled = &e__ * x_;
            let argument = &d__ * (&a__ + &b__ * (&c__ * x_.pow(&n_)).log());
            rubi_simp(&(scaled.pow(&m_ + 1) * rubi_erfc(&argument) / (&e__ * (&m_ + 1))), x_)
                    + rubi_star(Atom::num(2) * &b__ * &d__ * &n_ / (Atom::var(Symbol::PI).sqrt() * (&m_ + 1)), rubi_rhs_int(&(scaled.pow(&m_) / argument.pow(2).exp()), x_))
        },
    ));
}

fn push_rules_rule_6957(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 6957,
        source: "Int[(e_.*x_)^m_.*Erfi[d_.*(a_.+b_.*Log[c_.*x_^n_.])],x_Symbol] :=
          (e*x)^(m+1)*Erfi[d*(a+b*Log[c*x^n])]/(e*(m+1)) -
          2*b*d*n/(Sqrt[Pi]*(m+1)) \\[Star] Int[(e*x)^m*E^(d*(a+b*Log[c*x^n]))^2,x] /;
        FreeQ[{a,b,c,d,e,m,n},x] && NeQ[m,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern: (e__ * x_).pow(m_) * rubi_erfi(d__ * (a__ + b__ * (c__ * x_.pow(n_)).log())),
        with: [e__, m_, d__, a__, b__, c__, n_, x_],
        optional: [e__, m_, d__, a__, b__, c__, n_],
        when: { freeq!([a__, b__, c__, d__, e__, m_, n_], x_) && neq!(m_, -1) },
        rhs: {
            let scaled = &e__ * x_;
            let argument = &d__ * (&a__ + &b__ * (&c__ * x_.pow(&n_)).log());
            rubi_simp(&(scaled.pow(&m_ + 1) * rubi_erfi(&argument) / (&e__ * (&m_ + 1))), x_)
                    - rubi_star(Atom::num(2) * &b__ * &d__ * &n_ / (Atom::var(Symbol::PI).sqrt() * (&m_ + 1)), rubi_rhs_int(&(scaled.pow(&m_) * argument.pow(2).exp()), x_))
        },
    ));
}

fn push_rules_rule_6958(rules: &mut Vec<RubiRule>) {
    rubi_symb!(b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 6958,
        source: "Int[Sin[c_.+d_.*x_^2]*Erf[b_.*x_],x_Symbol] :=
          I/2 \\[Star] Int[E^(-I*c-I*d*x^2)*Erf[b*x],x] - I/2 \\[Star] Int[E^(I*c+I*d*x^2)*Erf[b*x],x] /;
        FreeQ[{b,c,d},x] && EqQ[d^2,-b^4]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (c__ + d__ * x_.pow(2)).sin() * (b__ * x_).erf(),
        with: [c__, d__, b__, x_],
        optional: [c__, d__, b__],
        when: { freeq!([b__, c__, d__], x_) && eqq!(d__.pow(2) + b__.pow(4), 0) },
        rhs: {
            let i = Atom::i();
            let argument = &b__ * x_;
            let negative_exp = (-&i * &c__ - &i * &d__ * x_.pow(2)).exp();
            let positive_exp = (&i * &c__ + &i * &d__ * x_.pow(2)).exp();
            rubi_star(&i, rubi_rhs_int(&(negative_exp * &argument.erf()), x_) / 2) - rubi_star(i, rubi_rhs_int(&(positive_exp * argument.erf()), x_) / 2)
        },
    ));
}

fn push_rules_rule_6959(rules: &mut Vec<RubiRule>) {
    rubi_symb!(b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 6959,
        source: "Int[Sin[c_.+d_.*x_^2]*Erfc[b_.*x_],x_Symbol] :=
          I/2 \\[Star] Int[E^(-I*c-I*d*x^2)*Erfc[b*x],x] - I/2 \\[Star] Int[E^(I*c+I*d*x^2)*Erfc[b*x],x] /;
        FreeQ[{b,c,d},x] && EqQ[d^2,-b^4]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (c__ + d__ * x_.pow(2)).sin() * rubi_erfc(b__ * x_),
        with: [c__, d__, b__, x_],
        optional: [c__, d__, b__],
        when: { freeq!([b__, c__, d__], x_) && eqq!(d__.pow(2) + b__.pow(4), 0) },
        rhs: {
            let i = Atom::i();
            let argument = &b__ * x_;
            let negative_exp = (-&i * &c__ - &i * &d__ * x_.pow(2)).exp();
            let positive_exp = (&i * &c__ + &i * &d__ * x_.pow(2)).exp();
            rubi_star(&i, rubi_rhs_int(&(negative_exp * rubi_erfc(&argument)), x_) / 2) - rubi_star(i, rubi_rhs_int(&(positive_exp * rubi_erfc(argument)), x_) / 2)
        },
    ));
}

fn push_rules_rule_6960(rules: &mut Vec<RubiRule>) {
    rubi_symb!(b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 6960,
        source: "Int[Sin[c_.+d_.*x_^2]*Erfi[b_.*x_],x_Symbol] :=
          I/2 \\[Star] Int[E^(-I*c-I*d*x^2)*Erfi[b*x],x] - I/2 \\[Star] Int[E^(I*c+I*d*x^2)*Erfi[b*x],x] /;
        FreeQ[{b,c,d},x] && EqQ[d^2,-b^4]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (c__ + d__ * x_.pow(2)).sin() * rubi_erfi(b__ * x_),
        with: [c__, d__, b__, x_],
        optional: [c__, d__, b__],
        when: { freeq!([b__, c__, d__], x_) && eqq!(d__.pow(2) + b__.pow(4), 0) },
        rhs: {
            let i = Atom::i();
            let argument = &b__ * x_;
            let negative_exp = (-&i * &c__ - &i * &d__ * x_.pow(2)).exp();
            let positive_exp = (&i * &c__ + &i * &d__ * x_.pow(2)).exp();
            rubi_star(&i, rubi_rhs_int(&(negative_exp * rubi_erfi(&argument)), x_) / 2) - rubi_star(i, rubi_rhs_int(&(positive_exp * rubi_erfi(argument)), x_) / 2)
        },
    ));
}

fn push_rules_rule_6961(rules: &mut Vec<RubiRule>) {
    rubi_symb!(b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 6961,
        source: "Int[Cos[c_.+d_.*x_^2]*Erf[b_.*x_],x_Symbol] :=
          1/2 \\[Star] Int[E^(-I*c-I*d*x^2)*Erf[b*x],x] + 1/2 \\[Star] Int[E^(I*c+I*d*x^2)*Erf[b*x],x] /;
        FreeQ[{b,c,d},x] && EqQ[d^2,-b^4]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (c__ + d__ * x_.pow(2)).cos() * (b__ * x_).erf(),
        with: [c__, d__, b__, x_],
        optional: [c__, d__, b__],
        when: { freeq!([b__, c__, d__], x_) && eqq!(d__.pow(2) + b__.pow(4), 0) },
        rhs: {
            let i = Atom::i();
            let argument = &b__ * x_;
            let negative_exp = (-&i * &c__ - &i * &d__ * x_.pow(2)).exp();
            let positive_exp = (&i * &c__ + &i * &d__ * x_.pow(2)).exp();
            rubi_star(Atom::num(1) / 2, rubi_rhs_int(&(negative_exp * &argument.erf()), x_)) + rubi_star(Atom::num(1) / 2, rubi_rhs_int(&(positive_exp * argument.erf()), x_))
        },
    ));
}

fn push_rules_rule_6962(rules: &mut Vec<RubiRule>) {
    rubi_symb!(b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 6962,
        source: "Int[Cos[c_.+d_.*x_^2]*Erfc[b_.*x_],x_Symbol] :=
          1/2 \\[Star] Int[E^(-I*c-I*d*x^2)*Erfc[b*x],x] + 1/2 \\[Star] Int[E^(I*c+I*d*x^2)*Erfc[b*x],x] /;
        FreeQ[{b,c,d},x] && EqQ[d^2,-b^4]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (c__ + d__ * x_.pow(2)).cos() * rubi_erfc(b__ * x_),
        with: [c__, d__, b__, x_],
        optional: [c__, d__, b__],
        when: { freeq!([b__, c__, d__], x_) && eqq!(d__.pow(2) + b__.pow(4), 0) },
        rhs: {
            let i = Atom::i();
            let argument = &b__ * x_;
            let negative_exp = (-&i * &c__ - &i * &d__ * x_.pow(2)).exp();
            let positive_exp = (&i * &c__ + &i * &d__ * x_.pow(2)).exp();
            rubi_star(Atom::num(1) / 2, rubi_rhs_int(&(negative_exp * rubi_erfc(&argument)), x_)) + rubi_star(Atom::num(1) / 2, rubi_rhs_int(&(positive_exp * rubi_erfc(argument)), x_))
        },
    ));
}

fn push_rules_rule_6963(rules: &mut Vec<RubiRule>) {
    rubi_symb!(b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 6963,
        source: "Int[Cos[c_.+d_.*x_^2]*Erfi[b_.*x_],x_Symbol] :=
          1/2 \\[Star] Int[E^(-I*c-I*d*x^2)*Erfi[b*x],x] + 1/2 \\[Star] Int[E^(I*c+I*d*x^2)*Erfi[b*x],x] /;
        FreeQ[{b,c,d},x] && EqQ[d^2,-b^4]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (c__ + d__ * x_.pow(2)).cos() * rubi_erfi(b__ * x_),
        with: [c__, d__, b__, x_],
        optional: [c__, d__, b__],
        when: { freeq!([b__, c__, d__], x_) && eqq!(d__.pow(2) + b__.pow(4), 0) },
        rhs: {
            let i = Atom::i();
            let argument = &b__ * x_;
            let negative_exp = (-&i * &c__ - &i * &d__ * x_.pow(2)).exp();
            let positive_exp = (&i * &c__ + &i * &d__ * x_.pow(2)).exp();
            rubi_star(Atom::num(1) / 2, rubi_rhs_int(&(negative_exp * rubi_erfi(&argument)), x_)) + rubi_star(Atom::num(1) / 2, rubi_rhs_int(&(positive_exp * rubi_erfi(argument)), x_))
        },
    ));
}

fn push_rules_rule_6964(rules: &mut Vec<RubiRule>) {
    rubi_symb!(b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 6964,
        source: "Int[Sinh[c_.+d_.*x_^2]*Erf[b_.*x_],x_Symbol] :=
          1/2 \\[Star] Int[E^(c+d*x^2)*Erf[b*x],x] - 1/2 \\[Star] Int[E^(-c-d*x^2)*Erf[b*x],x] /;
        FreeQ[{b,c,d},x] && EqQ[d^2,b^4]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (c__ + d__ * x_.pow(2)).sinh() * (b__ * x_).erf(),
        with: [c__, d__, b__, x_],
        optional: [c__, d__, b__],
        when: { freeq!([b__, c__, d__], x_) && eqq!(d__.pow(2) - b__.pow(4), 0) },
        rhs: {
            let argument = &b__ * x_;
            let positive_exp = (&c__ + &d__ * x_.pow(2)).exp();
            let negative_exp = (-&c__ - &d__ * x_.pow(2)).exp();
            rubi_star(Atom::num(1) / 2, rubi_rhs_int(&(positive_exp * &argument.erf()), x_)) - rubi_star(Atom::num(1) / 2, rubi_rhs_int(&(negative_exp * argument.erf()), x_))
        },
    ));
}

fn push_rules_rule_6965(rules: &mut Vec<RubiRule>) {
    rubi_symb!(b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 6965,
        source: "Int[Sinh[c_.+d_.*x_^2]*Erfc[b_.*x_],x_Symbol] :=
          1/2 \\[Star] Int[E^(c+d*x^2)*Erfc[b*x],x] - 1/2 \\[Star] Int[E^(-c-d*x^2)*Erfc[b*x],x] /;
        FreeQ[{b,c,d},x] && EqQ[d^2,b^4]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (c__ + d__ * x_.pow(2)).sinh() * rubi_erfc(b__ * x_),
        with: [c__, d__, b__, x_],
        optional: [c__, d__, b__],
        when: { freeq!([b__, c__, d__], x_) && eqq!(d__.pow(2) - b__.pow(4), 0) },
        rhs: {
            let argument = &b__ * x_;
            let positive_exp = (&c__ + &d__ * x_.pow(2)).exp();
            let negative_exp = (-&c__ - &d__ * x_.pow(2)).exp();
            rubi_star(Atom::num(1) / 2, rubi_rhs_int(&(positive_exp * rubi_erfc(&argument)), x_)) - rubi_star(Atom::num(1) / 2, rubi_rhs_int(&(negative_exp * rubi_erfc(argument)), x_))
        },
    ));
}

fn push_rules_rule_6966(rules: &mut Vec<RubiRule>) {
    rubi_symb!(b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 6966,
        source: "Int[Sinh[c_.+d_.*x_^2]*Erfi[b_.*x_],x_Symbol] :=
          1/2 \\[Star] Int[E^(c+d*x^2)*Erfi[b*x],x] - 1/2 \\[Star] Int[E^(-c-d*x^2)*Erfi[b*x],x] /;
        FreeQ[{b,c,d},x] && EqQ[d^2,b^4]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (c__ + d__ * x_.pow(2)).sinh() * rubi_erfi(b__ * x_),
        with: [c__, d__, b__, x_],
        optional: [c__, d__, b__],
        when: { freeq!([b__, c__, d__], x_) && eqq!(d__.pow(2) - b__.pow(4), 0) },
        rhs: {
            let argument = &b__ * x_;
            let positive_exp = (&c__ + &d__ * x_.pow(2)).exp();
            let negative_exp = (-&c__ - &d__ * x_.pow(2)).exp();
            rubi_star(Atom::num(1) / 2, rubi_rhs_int(&(positive_exp * rubi_erfi(&argument)), x_)) - rubi_star(Atom::num(1) / 2, rubi_rhs_int(&(negative_exp * rubi_erfi(argument)), x_))
        },
    ));
}

fn push_rules_rule_6967(rules: &mut Vec<RubiRule>) {
    rubi_symb!(b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 6967,
        source: "Int[Cosh[c_.+d_.*x_^2]*Erf[b_.*x_],x_Symbol] :=
          1/2 \\[Star] Int[E^(c+d*x^2)*Erf[b*x],x] + 1/2 \\[Star] Int[E^(-c-d*x^2)*Erf[b*x],x] /;
        FreeQ[{b,c,d},x] && EqQ[d^2,b^4]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (c__ + d__ * x_.pow(2)).cosh() * (b__ * x_).erf(),
        with: [c__, d__, b__, x_],
        optional: [c__, d__, b__],
        when: { freeq!([b__, c__, d__], x_) && eqq!(d__.pow(2) - b__.pow(4), 0) },
        rhs: {
            let argument = &b__ * x_;
            let positive_exp = (&c__ + &d__ * x_.pow(2)).exp();
            let negative_exp = (-&c__ - &d__ * x_.pow(2)).exp();
            rubi_star(Atom::num(1) / 2, rubi_rhs_int(&(positive_exp * &argument.erf()), x_)) + rubi_star(Atom::num(1) / 2, rubi_rhs_int(&(negative_exp * argument.erf()), x_))
        },
    ));
}

fn push_rules_rule_6968(rules: &mut Vec<RubiRule>) {
    rubi_symb!(b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 6968,
        source: "Int[Cosh[c_.+d_.*x_^2]*Erfc[b_.*x_],x_Symbol] :=
          1/2 \\[Star] Int[E^(c+d*x^2)*Erfc[b*x],x] + 1/2 \\[Star] Int[E^(-c-d*x^2)*Erfc[b*x],x] /;
        FreeQ[{b,c,d},x] && EqQ[d^2,b^4]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (c__ + d__ * x_.pow(2)).cosh() * rubi_erfc(b__ * x_),
        with: [c__, d__, b__, x_],
        optional: [c__, d__, b__],
        when: { freeq!([b__, c__, d__], x_) && eqq!(d__.pow(2) - b__.pow(4), 0) },
        rhs: {
            let argument = &b__ * x_;
            let positive_exp = (&c__ + &d__ * x_.pow(2)).exp();
            let negative_exp = (-&c__ - &d__ * x_.pow(2)).exp();
            rubi_star(Atom::num(1) / 2, rubi_rhs_int(&(positive_exp * rubi_erfc(&argument)), x_)) + rubi_star(Atom::num(1) / 2, rubi_rhs_int(&(negative_exp * rubi_erfc(argument)), x_))
        },
    ));
}

fn push_rules_rule_6969(rules: &mut Vec<RubiRule>) {
    rubi_symb!(b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 6969,
        source: "Int[Cosh[c_.+d_.*x_^2]*Erfi[b_.*x_],x_Symbol] :=
          1/2 \\[Star] Int[E^(c+d*x^2)*Erfi[b*x],x] + 1/2 \\[Star] Int[E^(-c-d*x^2)*Erfi[b*x],x] /;
        FreeQ[{b,c,d},x] && EqQ[d^2,b^4]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (c__ + d__ * x_.pow(2)).cosh() * rubi_erfi(b__ * x_),
        with: [c__, d__, b__, x_],
        optional: [c__, d__, b__],
        when: { freeq!([b__, c__, d__], x_) && eqq!(d__.pow(2) - b__.pow(4), 0) },
        rhs: {
            let argument = &b__ * x_;
            let positive_exp = (&c__ + &d__ * x_.pow(2)).exp();
            let negative_exp = (-&c__ - &d__ * x_.pow(2)).exp();
            rubi_star(Atom::num(1) / 2, rubi_rhs_int(&(positive_exp * rubi_erfi(&argument)), x_)) + rubi_star(Atom::num(1) / 2, rubi_rhs_int(&(negative_exp * rubi_erfi(argument)), x_))
        },
    ));
}

fn push_rules_rule_6970(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_f_, a__, b__, c__, d_, e__, f__, n_, x_);
    rules.push(rubi_rule!(
        order: 6970,
        source: "Int[F_[f_.*(a_.+b_.*Log[c_.*(d_+e_.*x_)^n_.])],x_Symbol] :=
          1/e \\[Star] Subst[Int[F[f*(a+b*Log[c*x^n])],x],x,d+e*x] /;
        FreeQ[{a,b,c,d,e,f,n},x] && MemberQ[{Erf,Erfc,Erfi,FresnelS,FresnelC,ExpIntegralEi,SinIntegral,CosIntegral,SinhIntegral,CoshIntegral},F]",
        desc: "Integration by substitution",
        refs: [],
        pattern: capital_f_
            .call(f__ * (a__ + b__ * (c__ * (d_ + e__ * x_).pow(n_)).log())),
        with: [capital_f_, f__, a__, b__, c__, d_, e__, n_, x_],
        optional: [f__, a__, b__, c__, e__, n_],
        when: {
            freeq!([a__, b__, c__, d_, e__, f__, n_], x_)
                && rubi_function_head_member_q(
                    &capital_f_,
                    &[
                        symbolica::transcendental::erf(),
                        rubi_symbols().erfc,
                        rubi_symbols().erfi,
                        rubi_symbols().fresnel_s,
                        rubi_symbols().fresnel_c,
                        rubi_symbols().exp_integral_ei,
                        rubi_symbols().sin_integral,
                        rubi_symbols().cos_integral,
                        rubi_symbols().sinh_integral,
                        rubi_symbols().cosh_integral,
                    ],
                )
        },
        rhs: {
            rubi_log_shift_subst(
                &capital_f_,
                &a__,
                &b__,
                &c__,
                &d_,
                &e__,
                &f__,
                &n_,
                x_,
            ).rubi_rhs()
        },
    ));
}

fn push_rules_rule_6971(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_f_, a__, b__, c__, d_, e__, f__, g_, h__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 6971,
        source: "Int[(g_+h_. x_)^m_.*F_[f_.*(a_.+b_.*Log[c_.*(d_+e_.*x_)^n_.])],x_Symbol] :=
          1/e \\[Star] Subst[Int[(g*x/d)^m*F[f*(a+b*Log[c*x^n])],x],x,d+e*x] /;
        FreeQ[{a,b,c,d,e,f,g,m,n},x] && EqQ[e*f-d*g,0] &&
          MemberQ[{Erf,Erfc,Erfi,FresnelS,FresnelC,ExpIntegralEi,SinIntegral,CosIntegral,SinhIntegral,CoshIntegral},F]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern: (g_ + h__ * x_).pow(m_)
            * capital_f_
                .call(f__ * (a__ + b__ * (c__ * (d_ + e__ * x_).pow(n_)).log())),
        with: [g_, h__, m_, capital_f_, f__, a__, b__, c__, d_, e__, n_, x_],
        optional: [h__, m_, f__, a__, b__, c__, e__, n_],
        when: {
            freeq!([a__, b__, c__, d_, e__, f__, g_, h__, m_, n_], x_)
                && eqq!(&e__ * &g_ - &d_ * &h__, 0)
                && rubi_function_head_member_q(
                    &capital_f_,
                    &[
                        symbolica::transcendental::erf(),
                        rubi_symbols().erfc,
                        rubi_symbols().erfi,
                        rubi_symbols().fresnel_s,
                        rubi_symbols().fresnel_c,
                        rubi_symbols().exp_integral_ei,
                        rubi_symbols().sin_integral,
                        rubi_symbols().cos_integral,
                        rubi_symbols().sinh_integral,
                        rubi_symbols().cosh_integral,
                    ],
                )
        },
        rhs: {
            rubi_log_shift_power_subst(
                &capital_f_,
                &a__,
                &b__,
                &c__,
                &d_,
                &e__,
                &f__,
                &g_,
                &m_,
                &n_,
                x_,
            ).rubi_rhs()
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
    let x_ = symbols.x_;
    x_.pow(m_) * (c__ + d__ * x_.pow(2)).exp() * (a__ + b__ * x_).erf()
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let m_ = symbols.m_;
    let x_ = symbols.x_;
    x_.pow(m_) * (c__ + d__ * x_.pow(2)).exp() * rubi_erfc(a__ + b__ * x_)
}

#[inline(never)]
fn rubi_shared_pattern_2(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let m_ = symbols.m_;
    let x_ = symbols.x_;
    x_.pow(m_) * (c__ + d__ * x_.pow(2)).exp() * rubi_erfi(a__ + b__ * x_)
}
