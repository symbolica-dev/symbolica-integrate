use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_7053(rules);
    push_rules_rule_7054(rules);
    push_rules_rule_7055(rules);
    push_rules_rule_7056(rules);
    push_rules_rule_7057(rules);
    push_rules_rule_7058(rules);
    push_rules_rule_7059(rules);
    push_rules_rule_7060(rules);
    push_rules_rule_7061(rules);
    push_rules_rule_7062(rules);
    push_rules_rule_7063(rules);
    push_rules_rule_7064(rules);
    // Rubi 8.4 block 7 is commented out in the markdown source.

    push_rules_rule_7065(rules);
    push_rules_rule_7066(rules);
    push_rules_rule_7067(rules);
    push_rules_rule_7068(rules);
    push_rules_rule_7069(rules);
    push_rules_rule_7070(rules);
    push_rules_rule_7071(rules);
    push_rules_rule_7072(rules);
    push_rules_rule_7073(rules);
    push_rules_rule_7074(rules);
    push_rules_rule_7075(rules);
    push_rules_rule_7076(rules);
    push_rules_rule_7077(rules);
    push_rules_rule_7078(rules);
    push_rules_rule_7079(rules);
    push_rules_rule_7080(rules);
    push_rules_rule_7081(rules);
}

fn push_rules_rule_7053(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, x_);
    rules.push(rubi_rule!(
        order: 7053,
        source: "Int[SinIntegral[a_.+b_.*x_],x_Symbol] :=
          (a+b*x)*SinIntegral[a+b*x]/b + Cos[a+b*x]/b/;
        FreeQ[{a,b},x]",
        desc: "Integration by parts",
        refs: [],
        pattern: rubi_sin_integral(a__ + b__ * x_),
        with: [a__, b__, x_],
        optional: [a__, b__],
        when: { freeq!([a__, b__], x_) },
        rhs: {
            let argument = &a__ + &b__ * x_;
            rubi_simp(&(&argument * rubi_sin_integral(&argument) / &b__), x_) + rubi_simp(&(argument.cos() / &b__), x_)
        },
    ));
}

fn push_rules_rule_7054(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, x_);
    rules.push(rubi_rule!(
        order: 7054,
        source: "Int[CosIntegral[a_.+b_.*x_],x_Symbol] :=
          (a+b*x)*CosIntegral[a+b*x]/b - Sin[a+b*x]/b /;
        FreeQ[{a,b},x]",
        desc: "Integration by parts",
        refs: [],
        pattern: rubi_cos_integral(a__ + b__ * x_),
        with: [a__, b__, x_],
        optional: [a__, b__],
        when: { freeq!([a__, b__], x_) },
        rhs: {
            let argument = &a__ + &b__ * x_;
            rubi_simp(&(&argument * rubi_cos_integral(&argument) / &b__), x_) - rubi_simp(&(argument.sin() / &b__), x_)
        },
    ));
}

fn push_rules_rule_7055(rules: &mut Vec<RubiRule>) {
    rubi_symb!(b__, x_);
    rules.push(rubi_rule!(
        order: 7055,
        source: "Int[SinIntegral[b_.*x_]/x_,x_Symbol] :=
          1/2*b*x*HypergeometricPFQ[{1,1,1},{2,2,2},-I*b*x] +
          1/2*b*x*HypergeometricPFQ[{1,1,1},{2,2,2},I*b*x] /;
        FreeQ[b,x]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: rubi_sin_integral(b__ * x_) / x_,
        with: [b__, x_],
        optional: [b__],
        when: { freeq!(b__, x_) },
        rhs: {
            let i = Atom::i();
            let scaled = &b__ * x_;
            rubi_simp(&(&scaled * rubi_hypergeometric_pfq_3_3(Atom::num(1), Atom::num(1), Atom::num(1), Atom::num(2), Atom::num(2), Atom::num(2), -&i * &scaled) / 2), x_)
                    + rubi_simp(&(&scaled * rubi_hypergeometric_pfq_3_3(Atom::num(1), Atom::num(1), Atom::num(1), Atom::num(2), Atom::num(2), Atom::num(2), i * &scaled) / 2), x_)
        },
    ));
}

fn push_rules_rule_7056(rules: &mut Vec<RubiRule>) {
    rubi_symb!(b__, x_);
    rules.push(rubi_rule!(
        order: 7056,
        source: "Int[CosIntegral[b_.*x_]/x_,x_Symbol] :=
          -1/2*I*b*x*HypergeometricPFQ[{1,1,1},{2,2,2},-I*b*x] +
          1/2*I*b*x*HypergeometricPFQ[{1,1,1},{2,2,2},I*b*x] +
          EulerGamma*Log[x] +
          1/2*Log[b*x]^2 /;
        FreeQ[b,x]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: rubi_cos_integral(b__ * x_) / x_,
        with: [b__, x_],
        optional: [b__],
        when: { freeq!(b__, x_) },
        rhs: {
            let i = Atom::i();
            let scaled = &b__ * x_;
            rubi_simp(&(-&i * &scaled * rubi_hypergeometric_pfq_3_3(Atom::num(1), Atom::num(1), Atom::num(1), Atom::num(2), Atom::num(2), Atom::num(2), -&i * &scaled) / 2), x_)
                    + rubi_simp(&(i * &scaled * rubi_hypergeometric_pfq_3_3(Atom::num(1), Atom::num(1), Atom::num(1), Atom::num(2), Atom::num(2), Atom::num(2), Atom::i() * &scaled) / 2), x_)
                    + rubi_simp(
                        &(Atom::var(symbolica::transcendental::euler_gamma()) * x_.log()),
                        x_,
                    )
                    + rubi_simp(&(scaled.log().pow(2) / 2), x_)
        },
    ));
}

fn push_rules_rule_7057(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, x_);
    rules.push(rubi_rule!(
        order: 7057,
        source: "Int[(c_.+d_.*x_)^m_.*SinIntegral[a_.+b_.*x_],x_Symbol] :=
          (c+d*x)^(m+1)*SinIntegral[a+b*x]/(d*(m+1)) -
          b/(d*(m+1)) \\[Star] Int[(c+d*x)^(m+1)*Sin[a+b*x]/(a+b*x),x] /;
        FreeQ[{a,b,c,d,m},x] && NeQ[m,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern: (c__ + d__ * x_).pow(m_) * rubi_sin_integral(a__ + b__ * x_),
        with: [c__, d__, m_, a__, b__, x_],
        optional: [c__, d__, m_, a__, b__],
        when: { freeq!([a__, b__, c__, d__, m_], x_) && neq!(m_, -1) },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let argument = &a__ + &b__ * x_;
            rubi_simp(&(linear.pow(&m_ + 1) * rubi_sin_integral(&argument) / (&d__ * (&m_ + 1))), x_)
                    - rubi_star(b__, rubi_rhs_int(&(linear.pow(&m_ + 1) * &argument.sin() / argument), x_) / (&d__ * (&m_ + 1)))
        },
    ));
}

fn push_rules_rule_7058(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, x_);
    rules.push(rubi_rule!(
        order: 7058,
        source: "Int[(c_.+d_.*x_)^m_.*CosIntegral[a_.+b_.*x_],x_Symbol] :=
          (c+d*x)^(m+1)*CosIntegral[a+b*x]/(d*(m+1)) -
          b/(d*(m+1)) \\[Star] Int[(c+d*x)^(m+1)*Cos[a+b*x]/(a+b*x),x] /;
        FreeQ[{a,b,c,d,m},x] && NeQ[m,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern: (c__ + d__ * x_).pow(m_) * rubi_cos_integral(a__ + b__ * x_),
        with: [c__, d__, m_, a__, b__, x_],
        optional: [c__, d__, m_, a__, b__],
        when: { freeq!([a__, b__, c__, d__, m_], x_) && neq!(m_, -1) },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let argument = &a__ + &b__ * x_;
            rubi_simp(&(linear.pow(&m_ + 1) * rubi_cos_integral(&argument) / (&d__ * (&m_ + 1))), x_)
                    - rubi_star(b__, rubi_rhs_int(&(linear.pow(&m_ + 1) * &argument.cos() / argument), x_) / (&d__ * (&m_ + 1)))
        },
    ));
}

fn push_rules_rule_7059(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, x_);
    rules.push(rubi_rule!(
        order: 7059,
        source: "Int[SinIntegral[a_.+b_.*x_]^2,x_Symbol] :=
          (a+b*x)*SinIntegral[a+b*x]^2/b -
          2 \\[Star] Int[Sin[a+b*x]*SinIntegral[a+b*x],x] /;
        FreeQ[{a,b},x]",
        desc: "Integration by parts",
        refs: [],
        pattern: rubi_sin_integral(a__ + b__ * x_).pow(2),
        with: [a__, b__, x_],
        optional: [a__, b__],
        when: { freeq!([a__, b__], x_) },
        rhs: {
            let argument = &a__ + &b__ * x_;
            rubi_simp(&(&argument * rubi_sin_integral(&argument).pow(2) / &b__), x_)
                    - rubi_star(Atom::num(2), rubi_rhs_int(&(&argument.sin() * rubi_sin_integral(argument)), x_))
        },
    ));
}

fn push_rules_rule_7060(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, x_);
    rules.push(rubi_rule!(
        order: 7060,
        source: "Int[CosIntegral[a_.+b_.*x_]^2,x_Symbol] :=
          (a+b*x)*CosIntegral[a+b*x]^2/b -
          2 \\[Star] Int[Cos[a+b*x]*CosIntegral[a+b*x],x] /;
        FreeQ[{a,b},x]",
        desc: "Integration by parts",
        refs: [],
        pattern: rubi_cos_integral(a__ + b__ * x_).pow(2),
        with: [a__, b__, x_],
        optional: [a__, b__],
        when: { freeq!([a__, b__], x_) },
        rhs: {
            let argument = &a__ + &b__ * x_;
            rubi_simp(&(&argument * rubi_cos_integral(&argument).pow(2) / &b__), x_)
                    - rubi_star(Atom::num(2), rubi_rhs_int(&(&argument.cos() * rubi_cos_integral(argument)), x_))
        },
    ));
}

fn push_rules_rule_7061(rules: &mut Vec<RubiRule>) {
    rubi_symb!(b__, m_, x_);
    rules.push(rubi_rule!(
        order: 7061,
        source: "Int[x_^m_.*SinIntegral[b_.*x_]^2,x_Symbol] :=
          x^(m+1)*SinIntegral[b*x]^2/(m+1) -
          2/(m+1) \\[Star] Int[x^m*Sin[b*x]*SinIntegral[b*x],x] /;
        FreeQ[b,x] && IGtQ[m,0]",
        desc: "Integration by parts",
        refs: [],
        pattern: x_.pow(m_) * rubi_sin_integral(b__ * x_).pow(2),
        with: [m_, b__, x_],
        optional: [m_, b__],
        when: { freeq!(b__, x_) && igtq!(m_, 0) },
        rhs: {
            let argument = &b__ * x_;
            rubi_simp(&(x_.pow(&m_ + 1) * rubi_sin_integral(&argument).pow(2) / (&m_ + 1)), x_)
                    - rubi_star(Atom::num(2), rubi_rhs_int(&(x_.pow(&m_) * &argument.sin() * rubi_sin_integral(argument)), x_) / (&m_ + 1))
        },
    ));
}

fn push_rules_rule_7062(rules: &mut Vec<RubiRule>) {
    rubi_symb!(b__, m_, x_);
    rules.push(rubi_rule!(
        order: 7062,
        source: "Int[x_^m_.*CosIntegral[b_.*x_]^2,x_Symbol] :=
          x^(m+1)*CosIntegral[b*x]^2/(m+1) -
          2/(m+1) \\[Star] Int[x^m*Cos[b*x]*CosIntegral[b*x],x] /;
        FreeQ[b,x] && IGtQ[m,0]",
        desc: "Integration by parts",
        refs: [],
        pattern: x_.pow(m_) * rubi_cos_integral(b__ * x_).pow(2),
        with: [m_, b__, x_],
        optional: [m_, b__],
        when: { freeq!(b__, x_) && igtq!(m_, 0) },
        rhs: {
            let argument = &b__ * x_;
            rubi_simp(&(x_.pow(&m_ + 1) * rubi_cos_integral(&argument).pow(2) / (&m_ + 1)), x_)
                    - rubi_star(Atom::num(2), rubi_rhs_int(&(x_.pow(&m_) * &argument.cos() * rubi_cos_integral(argument)), x_) / (&m_ + 1))
        },
    ));
}

fn push_rules_rule_7063(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a_, b__, c__, d__, m_, x_);
    rules.push(rubi_rule!(
        order: 7063,
        source: "Int[(c_.+d_.*x_)^m_.*SinIntegral[a_+b_.*x_]^2,x_Symbol] :=
          (a+b*x)*(c+d*x)^m*SinIntegral[a+b*x]^2/(b*(m+1)) -
          2/(m+1) \\[Star] Int[(c+d*x)^m*Sin[a+b*x]*SinIntegral[a+b*x],x] +
          (b*c-a*d)*m/(b*(m+1)) \\[Star] Int[(c+d*x)^(m-1)*SinIntegral[a+b*x]^2,x] /;
        FreeQ[{a,b,c,d},x] && IGtQ[m,0]",
        desc: "Iterated integration by parts",
        refs: [],
        pattern: (c__ + d__ * x_).pow(m_) * rubi_sin_integral(a_ + b__ * x_).pow(2),
        with: [c__, d__, m_, a_, b__, x_],
        optional: [c__, d__, m_, b__],
        when: { freeq!([a_, b__, c__, d__], x_) && igtq!(m_, 0) },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let argument = &a_ + &b__ * x_;
            rubi_simp(&(&argument * linear.pow(&m_) * rubi_sin_integral(&argument).pow(2) / (&b__ * (&m_ + 1))), x_)
                    - rubi_star(Atom::num(2), rubi_rhs_int(&(linear.pow(&m_) * &argument.sin() * rubi_sin_integral(&argument)), x_) / (&m_ + 1))
                    + rubi_star((&b__ * &c__ - &a_ * &d__) * &m_ / (&b__ * (&m_ + 1)), rubi_rhs_int(&(linear.pow(&m_ - 1) * rubi_sin_integral(argument).pow(2)), x_))
        },
    ));
}

fn push_rules_rule_7064(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a_, b__, c__, d__, m_, x_);
    rules.push(rubi_rule!(
        order: 7064,
        source: "Int[(c_.+d_.*x_)^m_.*CosIntegral[a_+b_.*x_]^2,x_Symbol] :=
          (a+b*x)*(c+d*x)^m*CosIntegral[a+b*x]^2/(b*(m+1)) -
          2/(m+1) \\[Star] Int[(c+d*x)^m*Cos[a+b*x]*CosIntegral[a+b*x],x] +
          (b*c-a*d)*m/(b*(m+1)) \\[Star] Int[(c+d*x)^(m-1)*CosIntegral[a+b*x]^2,x] /;
        FreeQ[{a,b,c,d},x] && IGtQ[m,0]",
        desc: "Iterated integration by parts",
        refs: [],
        pattern: (c__ + d__ * x_).pow(m_) * rubi_cos_integral(a_ + b__ * x_).pow(2),
        with: [c__, d__, m_, a_, b__, x_],
        optional: [c__, d__, m_, b__],
        when: { freeq!([a_, b__, c__, d__], x_) && igtq!(m_, 0) },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let argument = &a_ + &b__ * x_;
            rubi_simp(&(&argument * linear.pow(&m_) * rubi_cos_integral(&argument).pow(2) / (&b__ * (&m_ + 1))), x_)
                    - rubi_star(Atom::num(2), rubi_rhs_int(&(linear.pow(&m_) * &argument.cos() * rubi_cos_integral(&argument)), x_) / (&m_ + 1))
                    + rubi_star((&b__ * &c__ - &a_ * &d__) * &m_ / (&b__ * (&m_ + 1)), rubi_rhs_int(&(linear.pow(&m_ - 1) * rubi_cos_integral(argument).pow(2)), x_))
        },
    ));
}

fn push_rules_rule_7065(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 7065,
        source: "Int[Sin[a_.+b_.*x_]*SinIntegral[c_.+d_.*x_],x_Symbol] :=
          -Cos[a+b*x]*SinIntegral[c+d*x]/b +
          d/b \\[Star] Int[Cos[a+b*x]*Sin[c+d*x]/(c+d*x),x] /;
        FreeQ[{a,b,c,d},x]",
        desc: "Integration by parts",
        refs: ["G&R 5.32.2", "G&R 5.31.1"],
        pattern: (a__ + b__ * x_).sin() * rubi_sin_integral(c__ + d__ * x_),
        with: [a__, b__, c__, d__, x_],
        optional: [a__, b__, c__, d__],
        when: { freeq!([a__, b__, c__, d__], x_) },
        rhs: {
            let trig = &a__ + &b__ * x_;
            let argument = &c__ + &d__ * x_;
            rubi_simp(&(-&trig.cos() * rubi_sin_integral(&argument) / &b__), x_)
                    + rubi_star(d__, rubi_rhs_int(&(trig.cos() * &argument.sin() / argument), x_) / &b__)
        },
    ));
}

fn push_rules_rule_7066(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 7066,
        source: "Int[Cos[a_.+b_.*x_]*CosIntegral[c_.+d_.*x_],x_Symbol] :=
          Sin[a+b*x]*CosIntegral[c+d*x]/b -
          d/b \\[Star] Int[Sin[a+b*x]*Cos[c+d*x]/(c+d*x),x] /;
        FreeQ[{a,b,c,d},x]",
        desc: "Integration by parts",
        refs: ["G&R 5.32.2", "G&R 5.31.1"],
        pattern: (a__ + b__ * x_).cos() * rubi_cos_integral(c__ + d__ * x_),
        with: [a__, b__, c__, d__, x_],
        optional: [a__, b__, c__, d__],
        when: { freeq!([a__, b__, c__, d__], x_) },
        rhs: {
            let trig = &a__ + &b__ * x_;
            let argument = &c__ + &d__ * x_;
            rubi_simp(&(&trig.sin() * rubi_cos_integral(&argument) / &b__), x_)
                    - rubi_star(d__, rubi_rhs_int(&(trig.sin() * &argument.cos() / argument), x_) / &b__)
        },
    ));
}

fn push_rules_rule_7067(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, x_);
    rules.push(rubi_rule!(
        order: 7067,
        source: "Int[(e_.+f_.*x_)^m_.*Sin[a_.+b_.*x_]*SinIntegral[c_.+d_.*x_],x_Symbol] :=
          -(e+f*x)^m*Cos[a+b*x]*SinIntegral[c+d*x]/b +
          d/b \\[Star] Int[(e+f*x)^m*Cos[a+b*x]*Sin[c+d*x]/(c+d*x),x] +
          f*m/b \\[Star] Int[(e+f*x)^(m-1)*Cos[a+b*x]*SinIntegral[c+d*x],x] /;
        FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [e__, f__, m_, a__, b__, c__, d__, x_],
        optional: [e__, f__, m_, a__, b__, c__, d__],
        when: { freeq!([a__, b__, c__, d__, e__, f__], x_) && igtq!(m_, 0) },
        rhs: {
            let linear = &e__ + &f__ * x_;
            let trig = &a__ + &b__ * x_;
            let argument = &c__ + &d__ * x_;
            rubi_simp(&(-linear.pow(&m_) * &trig.cos() * rubi_sin_integral(&argument) / &b__), x_)
                    + rubi_star(d__, rubi_rhs_int(&(linear.pow(&m_) * &trig.cos() * &argument.sin() / &argument), x_) / &b__)
                    + rubi_star(&f__ * &m_ / &b__, rubi_rhs_int(&(linear.pow(&m_ - 1) * trig.cos() * rubi_sin_integral(argument)), x_))
        },
    ));
}

fn push_rules_rule_7068(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, x_);
    rules.push(rubi_rule!(
        order: 7068,
        source: "Int[(e_.+f_.*x_)^m_.*Cos[a_.+b_.*x_]*CosIntegral[c_.+d_.*x_],x_Symbol] :=
          (e+f*x)^m*Sin[a+b*x]*CosIntegral[c+d*x]/b -
          d/b \\[Star] Int[(e+f*x)^m*Sin[a+b*x]*Cos[c+d*x]/(c+d*x),x] -
          f*m/b \\[Star] Int[(e+f*x)^(m-1)*Sin[a+b*x]*CosIntegral[c+d*x],x] /;
        FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [e__, f__, m_, a__, b__, c__, d__, x_],
        optional: [e__, f__, m_, a__, b__, c__, d__],
        when: { freeq!([a__, b__, c__, d__, e__, f__], x_) && igtq!(m_, 0) },
        rhs: {
            let linear = &e__ + &f__ * x_;
            let trig = &a__ + &b__ * x_;
            let argument = &c__ + &d__ * x_;
            rubi_simp(&(linear.pow(&m_) * &trig.sin() * rubi_cos_integral(&argument) / &b__), x_)
                    - rubi_star(d__, rubi_rhs_int(&(linear.pow(&m_) * &trig.sin() * &argument.cos() / &argument), x_) / &b__)
                    - rubi_star(&f__ * &m_ / &b__, rubi_rhs_int(&(linear.pow(&m_ - 1) * trig.sin() * rubi_cos_integral(argument)), x_))
        },
    ));
}

fn push_rules_rule_7069(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, x_);
    rules.push(rubi_rule!(
        order: 7069,
        source: "Int[(e_.+f_.*x_)^m_*Sin[a_.+b_.*x_]*SinIntegral[c_.+d_.*x_],x_Symbol] :=
          (e+f*x)^(m+1)*Sin[a+b*x]*SinIntegral[c+d*x]/(f*(m+1)) -
          d/(f*(m+1)) \\[Star] Int[(e+f*x)^(m+1)*Sin[a+b*x]*Sin[c+d*x]/(c+d*x),x] -
          b/(f*(m+1)) \\[Star] Int[(e+f*x)^(m+1)*Cos[a+b*x]*SinIntegral[c+d*x],x] /;
        FreeQ[{a,b,c,d,e,f},x] && ILtQ[m,-1]",
        desc: "Inverted integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [e__, f__, m_, a__, b__, c__, d__, x_],
        optional: [e__, f__, a__, b__, c__, d__],
        when: { freeq!([a__, b__, c__, d__, e__, f__], x_) && iltq!(m_, -1) },
        rhs: {
            let linear = &e__ + &f__ * x_;
            let trig = &a__ + &b__ * x_;
            let argument = &c__ + &d__ * x_;
            rubi_simp(&(linear.pow(&m_ + 1) * &trig.sin() * rubi_sin_integral(&argument) / (&f__ * (&m_ + 1))), x_)
                    - rubi_star(d__, rubi_rhs_int(&(linear.pow(&m_ + 1) * &trig.sin() * &argument.sin() / &argument), x_) / (&f__ * (&m_ + 1)))
                    - rubi_star(b__, rubi_rhs_int(&(linear.pow(&m_ + 1) * trig.cos() * rubi_sin_integral(argument)), x_) / (&f__ * (&m_ + 1)))
        },
    ));
}

fn push_rules_rule_7070(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, x_);
    rules.push(rubi_rule!(
        order: 7070,
        source: "Int[(e_.+f_.*x_)^m_.*Cos[a_.+b_.*x_]*CosIntegral[c_.+d_.*x_],x_Symbol] :=
          (e+f*x)^(m+1)*Cos[a+b*x]*CosIntegral[c+d*x]/(f*(m+1)) -
          d/(f*(m+1)) \\[Star] Int[(e+f*x)^(m+1)*Cos[a+b*x]*Cos[c+d*x]/(c+d*x),x] +
          b/(f*(m+1)) \\[Star] Int[(e+f*x)^(m+1)*Sin[a+b*x]*CosIntegral[c+d*x],x] /;
        FreeQ[{a,b,c,d,e,f},x] && ILtQ[m,-1]",
        desc: "Inverted integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [e__, f__, m_, a__, b__, c__, d__, x_],
        optional: [e__, f__, m_, a__, b__, c__, d__],
        when: { freeq!([a__, b__, c__, d__, e__, f__], x_) && iltq!(m_, -1) },
        rhs: {
            let linear = &e__ + &f__ * x_;
            let trig = &a__ + &b__ * x_;
            let argument = &c__ + &d__ * x_;
            rubi_simp(&(linear.pow(&m_ + 1) * &trig.cos() * rubi_cos_integral(&argument) / (&f__ * (&m_ + 1))), x_)
                    - rubi_star(d__, rubi_rhs_int(&(linear.pow(&m_ + 1) * &trig.cos() * &argument.cos() / &argument), x_) / (&f__ * (&m_ + 1)))
                    + rubi_star(b__, rubi_rhs_int(&(linear.pow(&m_ + 1) * trig.sin() * rubi_cos_integral(argument)), x_) / (&f__ * (&m_ + 1)))
        },
    ));
}

fn push_rules_rule_7071(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 7071,
        source: "Int[Cos[a_.+b_.*x_]*SinIntegral[c_.+d_.*x_],x_Symbol] :=
          Sin[a+b*x]*SinIntegral[c+d*x]/b -
          d/b \\[Star] Int[Sin[a+b*x]*Sin[c+d*x]/(c+d*x),x] /;
        FreeQ[{a,b,c,d},x]",
        desc: "Integration by parts",
        refs: ["G&R 5.32.1", "G&R 5.31.2"],
        pattern: (a__ + b__ * x_).cos() * rubi_sin_integral(c__ + d__ * x_),
        with: [a__, b__, c__, d__, x_],
        optional: [a__, b__, c__, d__],
        when: { freeq!([a__, b__, c__, d__], x_) },
        rhs: {
            let trig = &a__ + &b__ * x_;
            let argument = &c__ + &d__ * x_;
            rubi_simp(&(&trig.sin() * rubi_sin_integral(&argument) / &b__), x_)
                    - rubi_star(d__, rubi_rhs_int(&(trig.sin() * &argument.sin() / argument), x_) / &b__)
        },
    ));
}

fn push_rules_rule_7072(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 7072,
        source: "Int[Sin[a_.+b_.*x_]*CosIntegral[c_.+d_.*x_],x_Symbol] :=
          -Cos[a+b*x]*CosIntegral[c+d*x]/b +
          d/b \\[Star] Int[Cos[a+b*x]*Cos[c+d*x]/(c+d*x),x] /;
        FreeQ[{a,b,c,d},x]",
        desc: "Integration by parts",
        refs: ["G&R 5.32.1", "G&R 5.31.2"],
        pattern: (a__ + b__ * x_).sin() * rubi_cos_integral(c__ + d__ * x_),
        with: [a__, b__, c__, d__, x_],
        optional: [a__, b__, c__, d__],
        when: { freeq!([a__, b__, c__, d__], x_) },
        rhs: {
            let trig = &a__ + &b__ * x_;
            let argument = &c__ + &d__ * x_;
            rubi_simp(&(-&trig.cos() * rubi_cos_integral(&argument) / &b__), x_)
                    + rubi_star(d__, rubi_rhs_int(&(trig.cos() * &argument.cos() / argument), x_) / &b__)
        },
    ));
}

fn push_rules_rule_7073(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, x_);
    rules.push(rubi_rule!(
        order: 7073,
        source: "Int[(e_.+f_.*x_)^m_.*Cos[a_.+b_.*x_]*SinIntegral[c_.+d_.*x_],x_Symbol] :=
          (e+f*x)^m*Sin[a+b*x]*SinIntegral[c+d*x]/b -
          d/b \\[Star] Int[(e+f*x)^m*Sin[a+b*x]*Sin[c+d*x]/(c+d*x),x] -
          f*m/b \\[Star] Int[(e+f*x)^(m-1)*Sin[a+b*x]*SinIntegral[c+d*x],x] /;
        FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [e__, f__, m_, a__, b__, c__, d__, x_],
        optional: [e__, f__, m_, a__, b__, c__, d__],
        when: { freeq!([a__, b__, c__, d__, e__, f__], x_) && igtq!(m_, 0) },
        rhs: {
            let linear = &e__ + &f__ * x_;
            let trig = &a__ + &b__ * x_;
            let argument = &c__ + &d__ * x_;
            rubi_simp(&(linear.pow(&m_) * &trig.sin() * rubi_sin_integral(&argument) / &b__), x_)
                    - rubi_star(d__, rubi_rhs_int(&(linear.pow(&m_) * &trig.sin() * &argument.sin() / &argument), x_) / &b__)
                    - rubi_star(&f__ * &m_ / &b__, rubi_rhs_int(&(linear.pow(&m_ - 1) * trig.sin() * rubi_sin_integral(argument)), x_))
        },
    ));
}

fn push_rules_rule_7074(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, x_);
    rules.push(rubi_rule!(
        order: 7074,
        source: "Int[(e_.+f_.*x_)^m_.*Sin[a_.+b_.*x_]*CosIntegral[c_.+d_.*x_],x_Symbol] :=
          -(e+f*x)^m*Cos[a+b*x]*CosIntegral[c+d*x]/b +
          d/b \\[Star] Int[(e+f*x)^m*Cos[a+b*x]*Cos[c+d*x]/(c+d*x),x] +
          f*m/b \\[Star] Int[(e+f*x)^(m-1)*Cos[a+b*x]*CosIntegral[c+d*x],x] /;
        FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [e__, f__, m_, a__, b__, c__, d__, x_],
        optional: [e__, f__, m_, a__, b__, c__, d__],
        when: { freeq!([a__, b__, c__, d__, e__, f__], x_) && igtq!(m_, 0) },
        rhs: {
            let linear = &e__ + &f__ * x_;
            let trig = &a__ + &b__ * x_;
            let argument = &c__ + &d__ * x_;
            rubi_simp(&(-linear.pow(&m_) * &trig.cos() * rubi_cos_integral(&argument) / &b__), x_)
                    + rubi_star(d__, rubi_rhs_int(&(linear.pow(&m_) * &trig.cos() * &argument.cos() / &argument), x_) / &b__)
                    + rubi_star(&f__ * &m_ / &b__, rubi_rhs_int(&(linear.pow(&m_ - 1) * trig.cos() * rubi_cos_integral(argument)), x_))
        },
    ));
}

fn push_rules_rule_7075(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, x_);
    rules.push(rubi_rule!(
        order: 7075,
        source: "Int[(e_.+f_.*x_)^m_.*Cos[a_.+b_.*x_]*SinIntegral[c_.+d_.*x_],x_Symbol] :=
          (e+f*x)^(m+1)*Cos[a+b*x]*SinIntegral[c+d*x]/(f*(m+1)) -
          d/(f*(m+1)) \\[Star] Int[(e+f*x)^(m+1)*Cos[a+b*x]*Sin[c+d*x]/(c+d*x),x] +
          b/(f*(m+1)) \\[Star] Int[(e+f*x)^(m+1)*Sin[a+b*x]*SinIntegral[c+d*x],x] /;
        FreeQ[{a,b,c,d,e,f},x] && ILtQ[m,-1]",
        desc: "Inverted integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [e__, f__, m_, a__, b__, c__, d__, x_],
        optional: [e__, f__, m_, a__, b__, c__, d__],
        when: { freeq!([a__, b__, c__, d__, e__, f__], x_) && iltq!(m_, -1) },
        rhs: {
            let linear = &e__ + &f__ * x_;
            let trig = &a__ + &b__ * x_;
            let argument = &c__ + &d__ * x_;
            rubi_simp(&(linear.pow(&m_ + 1) * &trig.cos() * rubi_sin_integral(&argument) / (&f__ * (&m_ + 1))), x_)
                    - rubi_star(d__, rubi_rhs_int(&(linear.pow(&m_ + 1) * &trig.cos() * &argument.sin() / &argument), x_) / (&f__ * (&m_ + 1)))
                    + rubi_star(b__, rubi_rhs_int(&(linear.pow(&m_ + 1) * trig.sin() * rubi_sin_integral(argument)), x_) / (&f__ * (&m_ + 1)))
        },
    ));
}

fn push_rules_rule_7076(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, x_);
    rules.push(rubi_rule!(
        order: 7076,
        source: "Int[(e_.+f_.*x_)^m_*Sin[a_.+b_.*x_]*CosIntegral[c_.+d_.*x_],x_Symbol] :=
          (e+f*x)^(m+1)*Sin[a+b*x]*CosIntegral[c+d*x]/(f*(m+1)) -
          d/(f*(m+1)) \\[Star] Int[(e+f*x)^(m+1)*Sin[a+b*x]*Cos[c+d*x]/(c+d*x),x] -
          b/(f*(m+1)) \\[Star] Int[(e+f*x)^(m+1)*Cos[a+b*x]*CosIntegral[c+d*x],x] /;
        FreeQ[{a,b,c,d,e,f},x] && ILtQ[m,-1]",
        desc: "Inverted integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [e__, f__, m_, a__, b__, c__, d__, x_],
        optional: [e__, f__, a__, b__, c__, d__],
        when: { freeq!([a__, b__, c__, d__, e__, f__], x_) && iltq!(m_, -1) },
        rhs: {
            let linear = &e__ + &f__ * x_;
            let trig = &a__ + &b__ * x_;
            let argument = &c__ + &d__ * x_;
            rubi_simp(&(linear.pow(&m_ + 1) * &trig.sin() * rubi_cos_integral(&argument) / (&f__ * (&m_ + 1))), x_)
                    - rubi_star(d__, rubi_rhs_int(&(linear.pow(&m_ + 1) * &trig.sin() * &argument.cos() / &argument), x_) / (&f__ * (&m_ + 1)))
                    - rubi_star(b__, rubi_rhs_int(&(linear.pow(&m_ + 1) * trig.cos() * rubi_cos_integral(argument)), x_) / (&f__ * (&m_ + 1)))
        },
    ));
}

fn push_rules_rule_7077(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 7077,
        source: "Int[SinIntegral[d_.*(a_.+b_.*Log[c_.*x_^n_.])],x_Symbol] :=
          x*SinIntegral[d*(a+b*Log[c*x^n])] - b*d*n \\[Star] Int[Sin[d*(a+b*Log[c*x^n])]/(d*(a+b*Log[c*x^n])),x] /;
        FreeQ[{a,b,c,d,n},x]",
        desc: "Integration by parts",
        refs: [],
        pattern: rubi_sin_integral(d__ * (a__ + b__ * (c__ * x_.pow(n_)).log())),
        with: [d__, a__, b__, c__, n_, x_],
        optional: [d__, a__, b__, c__, n_],
        when: { freeq!([a__, b__, c__, d__, n_], x_) },
        rhs: {
            let argument = &d__ * (&a__ + &b__ * (&c__ * x_.pow(&n_)).log());
            rubi_simp(&(x_ * rubi_sin_integral(&argument)), x_)
                    - rubi_star(&b__ * &d__ * &n_, rubi_rhs_int(&(&argument.sin() / argument), x_))
        },
    ));
}

fn push_rules_rule_7078(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 7078,
        source: "Int[CosIntegral[d_.*(a_.+b_.*Log[c_.*x_^n_.])],x_Symbol] :=
          x*CosIntegral[d*(a+b*Log[c*x^n])] - b*d*n \\[Star] Int[Cos[d*(a+b*Log[c*x^n])]/(d*(a+b*Log[c*x^n])),x] /;
        FreeQ[{a,b,c,d,n},x]",
        desc: "Integration by parts",
        refs: [],
        pattern: rubi_cos_integral(d__ * (a__ + b__ * (c__ * x_.pow(n_)).log())),
        with: [d__, a__, b__, c__, n_, x_],
        optional: [d__, a__, b__, c__, n_],
        when: { freeq!([a__, b__, c__, d__, n_], x_) },
        rhs: {
            let argument = &d__ * (&a__ + &b__ * (&c__ * x_.pow(&n_)).log());
            rubi_simp(&(x_ * rubi_cos_integral(&argument)), x_)
                    - rubi_star(&b__ * &d__ * &n_, rubi_rhs_int(&(&argument.cos() / argument), x_))
        },
    ));
}

fn push_rules_rule_7079(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_f_, a__, b__, c__, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 7079,
        source: "Int[F_[d_.*(a_.+b_.*Log[c_.*x_^n_.])]/x_,x_Symbol] :=
          1/n \\[Star] Subst[F[d*(a+b*x)],x,Log[c*x^n]] /;
        FreeQ[{a,b,c,d,n},x] && MemberQ[{SinIntegral,CosIntegral},x]",
        desc: "Integration by substitution",
        refs: [],
        pattern: capital_f_.call(d__ * (a__ + b__ * (c__ * x_.pow(n_)).log()))
            / x_,
        with: [capital_f_, d__, a__, b__, c__, n_, x_],
        optional: [d__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, n_], x_)
                && rubi_function_head_member_q(
                    x_,
                    &[
                        rubi_symbols().sin_integral,
                        rubi_symbols().cos_integral,
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

fn push_rules_rule_7080(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 7080,
        source: "Int[(e_.*x_)^m_.*SinIntegral[d_.*(a_.+b_.*Log[c_.*x_^n_.])],x_Symbol] :=
          (e*x)^(m+1)*SinIntegral[d*(a+b*Log[c*x^n])]/(e*(m+1)) -
          b*d*n/(m+1) \\[Star] Int[(e*x)^m*Sin[d*(a+b*Log[c*x^n])]/(d*(a+b*Log[c*x^n])),x] /;
        FreeQ[{a,b,c,d,e,m,n},x] && NeQ[m,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern: (e__ * x_).pow(m_) * rubi_sin_integral(d__ * (a__ + b__ * (c__ * x_.pow(n_)).log())),
        with: [e__, m_, d__, a__, b__, c__, n_, x_],
        optional: [e__, m_, d__, a__, b__, c__, n_],
        when: { freeq!([a__, b__, c__, d__, e__, m_, n_], x_) && neq!(m_, -1) },
        rhs: {
            let scaled = &e__ * x_;
            let argument = &d__ * (&a__ + &b__ * (&c__ * x_.pow(&n_)).log());
            rubi_simp(&(scaled.pow(&m_ + 1) * rubi_sin_integral(&argument) / (&e__ * (&m_ + 1))), x_)
                    - rubi_star(&b__ * &d__ * &n_ / (&m_ + 1), rubi_rhs_int(&(scaled.pow(&m_) * &argument.sin() / argument), x_))
        },
    ));
}

fn push_rules_rule_7081(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 7081,
        source: "Int[(e_.*x_)^m_.*CosIntegral[d_.*(a_.+b_.*Log[c_.*x_^n_.])],x_Symbol] :=
          (e*x)^(m+1)*CosIntegral[d*(a+b*Log[c*x^n])]/(e*(m+1)) -
          b*d*n/(m+1) \\[Star] Int[(e*x)^m*Cos[d*(a+b*Log[c*x^n])]/(d*(a+b*Log[c*x^n])),x] /;
        FreeQ[{a,b,c,d,e,m,n},x] && NeQ[m,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern: (e__ * x_).pow(m_) * rubi_cos_integral(d__ * (a__ + b__ * (c__ * x_.pow(n_)).log())),
        with: [e__, m_, d__, a__, b__, c__, n_, x_],
        optional: [e__, m_, d__, a__, b__, c__, n_],
        when: { freeq!([a__, b__, c__, d__, e__, m_, n_], x_) && neq!(m_, -1) },
        rhs: {
            let scaled = &e__ * x_;
            let argument = &d__ * (&a__ + &b__ * (&c__ * x_.pow(&n_)).log());
            rubi_simp(&(scaled.pow(&m_ + 1) * rubi_cos_integral(&argument) / (&e__ * (&m_ + 1))), x_)
                    - rubi_star(&b__ * &d__ * &n_ / (&m_ + 1), rubi_rhs_int(&(scaled.pow(&m_) * &argument.cos() / argument), x_))
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
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let x_ = symbols.x_;
    (e__ + f__ * x_).pow(m_) * (a__ + b__ * x_).cos() * rubi_cos_integral(c__ + d__ * x_)
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
    let x_ = symbols.x_;
    (e__ + f__ * x_).pow(m_) * (a__ + b__ * x_).cos() * rubi_sin_integral(c__ + d__ * x_)
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
    let x_ = symbols.x_;
    (e__ + f__ * x_).pow(m_) * (a__ + b__ * x_).sin() * rubi_cos_integral(c__ + d__ * x_)
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
    let x_ = symbols.x_;
    (e__ + f__ * x_).pow(m_) * (a__ + b__ * x_).sin() * rubi_sin_integral(c__ + d__ * x_)
}
