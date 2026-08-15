use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_7082(rules);
    push_rules_rule_7083(rules);
    push_rules_rule_7084(rules);
    push_rules_rule_7085(rules);
    push_rules_rule_7086(rules);
    push_rules_rule_7087(rules);
    push_rules_rule_7088(rules);
    push_rules_rule_7089(rules);
    push_rules_rule_7090(rules);
    push_rules_rule_7091(rules);
    push_rules_rule_7092(rules);
    push_rules_rule_7093(rules);
    // Rubi 8.5 block 7 is commented out in the markdown source.

    push_rules_rule_7094(rules);
    push_rules_rule_7095(rules);
    push_rules_rule_7096(rules);
    push_rules_rule_7097(rules);
    push_rules_rule_7098(rules);
    push_rules_rule_7099(rules);
    push_rules_rule_7100(rules);
    push_rules_rule_7101(rules);
    push_rules_rule_7102(rules);
    push_rules_rule_7103(rules);
    push_rules_rule_7104(rules);
    push_rules_rule_7105(rules);
    push_rules_rule_7106(rules);
    push_rules_rule_7107(rules);
    push_rules_rule_7108(rules);
    push_rules_rule_7109(rules);
    push_rules_rule_7110(rules);
}

fn push_rules_rule_7082(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, x_);
    rules.push(rubi_rule!(
        order: 7082,
        source: "Int[SinhIntegral[a_.+b_.*x_],x_Symbol] :=
          (a+b*x)*SinhIntegral[a+b*x]/b - Cosh[a+b*x]/b/;
        FreeQ[{a,b},x]",
        desc: "Integration by parts",
        refs: [],
        pattern: rubi_sinh_integral(a__ + b__ * x_),
        with: [a__, b__, x_],
        optional: [a__, b__],
        when: { freeq!([a__, b__], x_) },
        rhs: {
            let argument = &a__ + &b__ * x_;
            rubi_simp(&(&argument * rubi_sinh_integral(&argument) / &b__), x_) - rubi_simp(&(argument.cosh() / &b__), x_)
        },
    ));
}

fn push_rules_rule_7083(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, x_);
    rules.push(rubi_rule!(
        order: 7083,
        source: "Int[CoshIntegral[a_.+b_.*x_],x_Symbol] :=
          (a+b*x)*CoshIntegral[a+b*x]/b - Sinh[a+b*x]/b /;
        FreeQ[{a,b},x]",
        desc: "Integration by parts",
        refs: [],
        pattern: rubi_cosh_integral(a__ + b__ * x_),
        with: [a__, b__, x_],
        optional: [a__, b__],
        when: { freeq!([a__, b__], x_) },
        rhs: {
            let argument = &a__ + &b__ * x_;
            rubi_simp(&(&argument * rubi_cosh_integral(&argument) / &b__), x_) - rubi_simp(&(argument.sinh() / &b__), x_)
        },
    ));
}

fn push_rules_rule_7084(rules: &mut Vec<RubiRule>) {
    rubi_symb!(b__, x_);
    rules.push(rubi_rule!(
        order: 7084,
        source: "Int[SinhIntegral[b_.*x_]/x_,x_Symbol] :=
          1/2*b*x*HypergeometricPFQ[{1,1,1},{2,2,2},-b*x] +
          1/2*b*x*HypergeometricPFQ[{1,1,1},{2,2,2},b*x] /;
        FreeQ[b,x]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: rubi_sinh_integral(b__ * x_) / x_,
        with: [b__, x_],
        optional: [b__],
        when: { freeq!(b__, x_) },
        rhs: {
            let scaled = &b__ * x_;
            rubi_simp(&(&scaled * rubi_hypergeometric_pfq_3_3(Atom::num(1), Atom::num(1), Atom::num(1), Atom::num(2), Atom::num(2), Atom::num(2), -&scaled) / 2), x_)
                    + rubi_simp(&(&scaled * rubi_hypergeometric_pfq_3_3(Atom::num(1), Atom::num(1), Atom::num(1), Atom::num(2), Atom::num(2), Atom::num(2), &scaled) / 2), x_)
        },
    ));
}

fn push_rules_rule_7085(rules: &mut Vec<RubiRule>) {
    rubi_symb!(b__, x_);
    rules.push(rubi_rule!(
        order: 7085,
        source: "Int[CoshIntegral[b_.*x_]/x_,x_Symbol] :=
          -1/2*b*x*HypergeometricPFQ[{1,1,1},{2,2,2},-b*x] +
          1/2*b*x*HypergeometricPFQ[{1,1,1},{2,2,2},b*x] +
          EulerGamma*Log[x] +
          1/2*Log[b*x]^2 /;
        FreeQ[b,x]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: rubi_cosh_integral(b__ * x_) / x_,
        with: [b__, x_],
        optional: [b__],
        when: { freeq!(b__, x_) },
        rhs: {
            let scaled = &b__ * x_;
            rubi_simp(&(-&scaled * rubi_hypergeometric_pfq_3_3(Atom::num(1), Atom::num(1), Atom::num(1), Atom::num(2), Atom::num(2), Atom::num(2), -&scaled) / 2), x_)
                    + rubi_simp(&(&scaled * rubi_hypergeometric_pfq_3_3(Atom::num(1), Atom::num(1), Atom::num(1), Atom::num(2), Atom::num(2), Atom::num(2), &scaled) / 2), x_)
                    + rubi_simp(
                        &(Atom::var(symbolica::transcendental::euler_gamma()) * x_.log()),
                        x_,
                    )
                    + rubi_simp(&(scaled.log().pow(2) / 2), x_)
        },
    ));
}

fn push_rules_rule_7086(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, x_);
    rules.push(rubi_rule!(
        order: 7086,
        source: "Int[(c_.+d_.*x_)^m_.*SinhIntegral[a_.+b_.*x_],x_Symbol] :=
          (c+d*x)^(m+1)*SinhIntegral[a+b*x]/(d*(m+1)) -
          b/(d*(m+1)) \\[Star] Int[(c+d*x)^(m+1)*Sinh[a+b*x]/(a+b*x),x] /;
        FreeQ[{a,b,c,d,m},x] && NeQ[m,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern: (c__ + d__ * x_).pow(m_) * rubi_sinh_integral(a__ + b__ * x_),
        with: [c__, d__, m_, a__, b__, x_],
        optional: [c__, d__, m_, a__, b__],
        when: { freeq!([a__, b__, c__, d__, m_], x_) && neq!(m_, -1) },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let argument = &a__ + &b__ * x_;
            rubi_simp(&(linear.pow(&m_ + 1) * rubi_sinh_integral(&argument) / (&d__ * (&m_ + 1))), x_)
                    - rubi_star(b__, rubi_rhs_int(&(linear.pow(&m_ + 1) * &argument.sinh() / argument), x_) / (&d__ * (&m_ + 1)))
        },
    ));
}

fn push_rules_rule_7087(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, x_);
    rules.push(rubi_rule!(
        order: 7087,
        source: "Int[(c_.+d_.*x_)^m_.*CoshIntegral[a_.+b_.*x_],x_Symbol] :=
          (c+d*x)^(m+1)*CoshIntegral[a+b*x]/(d*(m+1)) -
          b/(d*(m+1)) \\[Star] Int[(c+d*x)^(m+1)*Cosh[a+b*x]/(a+b*x),x] /;
        FreeQ[{a,b,c,d,m},x] && NeQ[m,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern: (c__ + d__ * x_).pow(m_) * rubi_cosh_integral(a__ + b__ * x_),
        with: [c__, d__, m_, a__, b__, x_],
        optional: [c__, d__, m_, a__, b__],
        when: { freeq!([a__, b__, c__, d__, m_], x_) && neq!(m_, -1) },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let argument = &a__ + &b__ * x_;
            rubi_simp(&(linear.pow(&m_ + 1) * rubi_cosh_integral(&argument) / (&d__ * (&m_ + 1))), x_)
                    - rubi_star(b__, rubi_rhs_int(&(linear.pow(&m_ + 1) * &argument.cosh() / argument), x_) / (&d__ * (&m_ + 1)))
        },
    ));
}

fn push_rules_rule_7088(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, x_);
    rules.push(rubi_rule!(
        order: 7088,
        source: "Int[SinhIntegral[a_.+b_.*x_]^2,x_Symbol] :=
          (a+b*x)*SinhIntegral[a+b*x]^2/b -
          2 \\[Star] Int[Sinh[a+b*x]*SinhIntegral[a+b*x],x] /;
        FreeQ[{a,b},x]",
        desc: "Integration by parts",
        refs: [],
        pattern: rubi_sinh_integral(a__ + b__ * x_).pow(2),
        with: [a__, b__, x_],
        optional: [a__, b__],
        when: { freeq!([a__, b__], x_) },
        rhs: {
            let argument = &a__ + &b__ * x_;
            rubi_simp(&(&argument * rubi_sinh_integral(&argument).pow(2) / &b__), x_)
                    - rubi_star(Atom::num(2), rubi_rhs_int(&(&argument.sinh() * rubi_sinh_integral(argument)), x_))
        },
    ));
}

fn push_rules_rule_7089(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, x_);
    rules.push(rubi_rule!(
        order: 7089,
        source: "Int[CoshIntegral[a_.+b_.*x_]^2,x_Symbol] :=
          (a+b*x)*CoshIntegral[a+b*x]^2/b -
          2 \\[Star] Int[Cosh[a+b*x]*CoshIntegral[a+b*x],x] /;
        FreeQ[{a,b},x]",
        desc: "Integration by parts",
        refs: [],
        pattern: rubi_cosh_integral(a__ + b__ * x_).pow(2),
        with: [a__, b__, x_],
        optional: [a__, b__],
        when: { freeq!([a__, b__], x_) },
        rhs: {
            let argument = &a__ + &b__ * x_;
            rubi_simp(&(&argument * rubi_cosh_integral(&argument).pow(2) / &b__), x_)
                    - rubi_star(Atom::num(2), rubi_rhs_int(&(&argument.cosh() * rubi_cosh_integral(argument)), x_))
        },
    ));
}

fn push_rules_rule_7090(rules: &mut Vec<RubiRule>) {
    rubi_symb!(b__, m_, x_);
    rules.push(rubi_rule!(
        order: 7090,
        source: "Int[x_^m_.*SinhIntegral[b_.*x_]^2,x_Symbol] :=
          x^(m+1)*SinhIntegral[b*x]^2/(m+1) -
          2/(m+1) \\[Star] Int[x^m*Sinh[b*x]*SinhIntegral[b*x],x] /;
        FreeQ[b,x] && IGtQ[m,0]",
        desc: "Integration by parts",
        refs: [],
        pattern: x_.pow(m_) * rubi_sinh_integral(b__ * x_).pow(2),
        with: [m_, b__, x_],
        optional: [m_, b__],
        when: { freeq!(b__, x_) && igtq!(m_, 0) },
        rhs: {
            let argument = &b__ * x_;
            rubi_simp(&(x_.pow(&m_ + 1) * rubi_sinh_integral(&argument).pow(2) / (&m_ + 1)), x_)
                    - rubi_star(Atom::num(2), rubi_rhs_int(&(x_.pow(&m_) * &argument.sinh() * rubi_sinh_integral(argument)), x_) / (&m_ + 1))
        },
    ));
}

fn push_rules_rule_7091(rules: &mut Vec<RubiRule>) {
    rubi_symb!(b__, m_, x_);
    rules.push(rubi_rule!(
        order: 7091,
        source: "Int[x_^m_.*CoshIntegral[b_.*x_]^2,x_Symbol] :=
          x^(m+1)*CoshIntegral[b*x]^2/(m+1) -
          2/(m+1) \\[Star] Int[x^m*Cosh[b*x]*CoshIntegral[b*x],x] /;
        FreeQ[b,x] && IGtQ[m,0]",
        desc: "Integration by parts",
        refs: [],
        pattern: x_.pow(m_) * rubi_cosh_integral(b__ * x_).pow(2),
        with: [m_, b__, x_],
        optional: [m_, b__],
        when: { freeq!(b__, x_) && igtq!(m_, 0) },
        rhs: {
            let argument = &b__ * x_;
            rubi_simp(&(x_.pow(&m_ + 1) * rubi_cosh_integral(&argument).pow(2) / (&m_ + 1)), x_)
                    - rubi_star(Atom::num(2), rubi_rhs_int(&(x_.pow(&m_) * &argument.cosh() * rubi_cosh_integral(argument)), x_) / (&m_ + 1))
        },
    ));
}

fn push_rules_rule_7092(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a_, b__, c__, d__, m_, x_);
    rules.push(rubi_rule!(
        order: 7092,
        source: "Int[(c_.+d_.*x_)^m_.*SinhIntegral[a_+b_.*x_]^2,x_Symbol] :=
          (a+b*x)*(c+d*x)^m*SinhIntegral[a+b*x]^2/(b*(m+1)) -
          2/(m+1) \\[Star] Int[(c+d*x)^m*Sinh[a+b*x]*SinhIntegral[a+b*x],x] +
          (b*c-a*d)*m/(b*(m+1)) \\[Star] Int[(c+d*x)^(m-1)*SinhIntegral[a+b*x]^2,x] /;
        FreeQ[{a,b,c,d},x] && IGtQ[m,0]",
        desc: "Iterated integration by parts",
        refs: [],
        pattern: (c__ + d__ * x_).pow(m_) * rubi_sinh_integral(a_ + b__ * x_).pow(2),
        with: [c__, d__, m_, a_, b__, x_],
        optional: [c__, d__, m_, b__],
        when: { freeq!([a_, b__, c__, d__], x_) && igtq!(m_, 0) },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let argument = &a_ + &b__ * x_;
            rubi_simp(&(&argument * linear.pow(&m_) * rubi_sinh_integral(&argument).pow(2) / (&b__ * (&m_ + 1))), x_)
                    - rubi_star(Atom::num(2), rubi_rhs_int(&(linear.pow(&m_) * &argument.sinh() * rubi_sinh_integral(&argument)), x_) / (&m_ + 1))
                    + rubi_star((&b__ * &c__ - &a_ * &d__) * &m_ / (&b__ * (&m_ + 1)), rubi_rhs_int(&(linear.pow(&m_ - 1) * rubi_sinh_integral(argument).pow(2)), x_))
        },
    ));
}

fn push_rules_rule_7093(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a_, b__, c__, d__, m_, x_);
    rules.push(rubi_rule!(
        order: 7093,
        source: "Int[(c_.+d_.*x_)^m_.*CoshIntegral[a_+b_.*x_]^2,x_Symbol] :=
          (a+b*x)*(c+d*x)^m*CoshIntegral[a+b*x]^2/(b*(m+1)) -
          2/(m+1) \\[Star] Int[(c+d*x)^m*Cosh[a+b*x]*CoshIntegral[a+b*x],x] +
          (b*c-a*d)*m/(b*(m+1)) \\[Star] Int[(c+d*x)^(m-1)*CoshIntegral[a+b*x]^2,x] /;
        FreeQ[{a,b,c,d},x] && IGtQ[m,0]",
        desc: "Iterated integration by parts",
        refs: [],
        pattern: (c__ + d__ * x_).pow(m_) * rubi_cosh_integral(a_ + b__ * x_).pow(2),
        with: [c__, d__, m_, a_, b__, x_],
        optional: [c__, d__, m_, b__],
        when: { freeq!([a_, b__, c__, d__], x_) && igtq!(m_, 0) },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let argument = &a_ + &b__ * x_;
            rubi_simp(&(&argument * linear.pow(&m_) * rubi_cosh_integral(&argument).pow(2) / (&b__ * (&m_ + 1))), x_)
                    - rubi_star(Atom::num(2), rubi_rhs_int(&(linear.pow(&m_) * &argument.cosh() * rubi_cosh_integral(&argument)), x_) / (&m_ + 1))
                    + rubi_star((&b__ * &c__ - &a_ * &d__) * &m_ / (&b__ * (&m_ + 1)), rubi_rhs_int(&(linear.pow(&m_ - 1) * rubi_cosh_integral(argument).pow(2)), x_))
        },
    ));
}

fn push_rules_rule_7094(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 7094,
        source: "Int[Sinh[a_.+b_.*x_]*SinhIntegral[c_.+d_.*x_],x_Symbol] :=
          Cosh[a+b*x]*SinhIntegral[c+d*x]/b -
          d/b \\[Star] Int[Cosh[a+b*x]*Sinh[c+d*x]/(c+d*x),x] /;
        FreeQ[{a,b,c,d},x]",
        desc: "Integration by parts",
        refs: [],
        pattern: (a__ + b__ * x_).sinh() * rubi_sinh_integral(c__ + d__ * x_),
        with: [a__, b__, c__, d__, x_],
        optional: [a__, b__, c__, d__],
        when: { freeq!([a__, b__, c__, d__], x_) },
        rhs: {
            let trig = &a__ + &b__ * x_;
            let argument = &c__ + &d__ * x_;
            rubi_simp(&(&trig.cosh() * rubi_sinh_integral(&argument) / &b__), x_)
                    - rubi_star(d__, rubi_rhs_int(&(trig.cosh() * &argument.sinh() / argument), x_) / &b__)
        },
    ));
}

fn push_rules_rule_7095(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 7095,
        source: "Int[Cosh[a_.+b_.*x_]*CoshIntegral[c_.+d_.*x_],x_Symbol] :=
          Sinh[a+b*x]*CoshIntegral[c+d*x]/b -
          d/b \\[Star] Int[Sinh[a+b*x]*Cosh[c+d*x]/(c+d*x),x] /;
        FreeQ[{a,b,c,d},x]",
        desc: "Integration by parts",
        refs: [],
        pattern: (a__ + b__ * x_).cosh() * rubi_cosh_integral(c__ + d__ * x_),
        with: [a__, b__, c__, d__, x_],
        optional: [a__, b__, c__, d__],
        when: { freeq!([a__, b__, c__, d__], x_) },
        rhs: {
            let trig = &a__ + &b__ * x_;
            let argument = &c__ + &d__ * x_;
            rubi_simp(&(&trig.sinh() * rubi_cosh_integral(&argument) / &b__), x_)
                    - rubi_star(d__, rubi_rhs_int(&(trig.sinh() * &argument.cosh() / argument), x_) / &b__)
        },
    ));
}

fn push_rules_rule_7096(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, x_);
    rules.push(rubi_rule!(
        order: 7096,
        source: "Int[(e_.+f_.*x_)^m_.*Sinh[a_.+b_.*x_]*SinhIntegral[c_.+d_.*x_],x_Symbol] :=
          (e+f*x)^m*Cosh[a+b*x]*SinhIntegral[c+d*x]/b -
          d/b \\[Star] Int[(e+f*x)^m*Cosh[a+b*x]*Sinh[c+d*x]/(c+d*x),x] -
          f*m/b \\[Star] Int[(e+f*x)^(m-1)*Cosh[a+b*x]*SinhIntegral[c+d*x],x] /;
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
            rubi_simp(&(linear.pow(&m_) * &trig.cosh() * rubi_sinh_integral(&argument) / &b__), x_)
                    - rubi_star(d__, rubi_rhs_int(&(linear.pow(&m_) * &trig.cosh() * &argument.sinh() / &argument), x_) / &b__)
                    - rubi_star(&f__ * &m_ / &b__, rubi_rhs_int(&(linear.pow(&m_ - 1) * trig.cosh() * rubi_sinh_integral(argument)), x_))
        },
    ));
}

fn push_rules_rule_7097(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, x_);
    rules.push(rubi_rule!(
        order: 7097,
        source: "Int[(e_.+f_.*x_)^m_.*Cosh[a_.+b_.*x_]*CoshIntegral[c_.+d_.*x_],x_Symbol] :=
          (e+f*x)^m*Sinh[a+b*x]*CoshIntegral[c+d*x]/b -
          d/b \\[Star] Int[(e+f*x)^m*Sinh[a+b*x]*Cosh[c+d*x]/(c+d*x),x] -
          f*m/b \\[Star] Int[(e+f*x)^(m-1)*Sinh[a+b*x]*CoshIntegral[c+d*x],x] /;
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
            rubi_simp(&(linear.pow(&m_) * &trig.sinh() * rubi_cosh_integral(&argument) / &b__), x_)
                    - rubi_star(d__, rubi_rhs_int(&(linear.pow(&m_) * &trig.sinh() * &argument.cosh() / &argument), x_) / &b__)
                    - rubi_star(&f__ * &m_ / &b__, rubi_rhs_int(&(linear.pow(&m_ - 1) * trig.sinh() * rubi_cosh_integral(argument)), x_))
        },
    ));
}

fn push_rules_rule_7098(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, x_);
    rules.push(rubi_rule!(
        order: 7098,
        source: "Int[(e_.+f_.*x_)^m_*Sinh[a_.+b_.*x_]*SinhIntegral[c_.+d_.*x_],x_Symbol] :=
          (e+f*x)^(m+1)*Sinh[a+b*x]*SinhIntegral[c+d*x]/(f*(m+1)) -
          d/(f*(m+1)) \\[Star] Int[(e+f*x)^(m+1)*Sinh[a+b*x]*Sinh[c+d*x]/(c+d*x),x] -
          b/(f*(m+1)) \\[Star] Int[(e+f*x)^(m+1)*Cosh[a+b*x]*SinhIntegral[c+d*x],x] /;
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
            rubi_simp(&(linear.pow(&m_ + 1) * &trig.sinh() * rubi_sinh_integral(&argument) / (&f__ * (&m_ + 1))), x_)
                    - rubi_star(d__, rubi_rhs_int(&(linear.pow(&m_ + 1) * &trig.sinh() * &argument.sinh() / &argument), x_) / (&f__ * (&m_ + 1)))
                    - rubi_star(b__, rubi_rhs_int(&(linear.pow(&m_ + 1) * trig.cosh() * rubi_sinh_integral(argument)), x_) / (&f__ * (&m_ + 1)))
        },
    ));
}

fn push_rules_rule_7099(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, x_);
    rules.push(rubi_rule!(
        order: 7099,
        source: "Int[(e_.+f_.*x_)^m_.*Cosh[a_.+b_.*x_]*CoshIntegral[c_.+d_.*x_],x_Symbol] :=
          (e+f*x)^(m+1)*Cosh[a+b*x]*CoshIntegral[c+d*x]/(f*(m+1)) -
          d/(f*(m+1)) \\[Star] Int[(e+f*x)^(m+1)*Cosh[a+b*x]*Cosh[c+d*x]/(c+d*x),x] -
          b/(f*(m+1)) \\[Star] Int[(e+f*x)^(m+1)*Sinh[a+b*x]*CoshIntegral[c+d*x],x] /;
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
            rubi_simp(&(linear.pow(&m_ + 1) * &trig.cosh() * rubi_cosh_integral(&argument) / (&f__ * (&m_ + 1))), x_)
                    - rubi_star(d__, rubi_rhs_int(&(linear.pow(&m_ + 1) * &trig.cosh() * &argument.cosh() / &argument), x_) / (&f__ * (&m_ + 1)))
                    - rubi_star(b__, rubi_rhs_int(&(linear.pow(&m_ + 1) * trig.sinh() * rubi_cosh_integral(argument)), x_) / (&f__ * (&m_ + 1)))
        },
    ));
}

fn push_rules_rule_7100(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 7100,
        source: "Int[Cosh[a_.+b_.*x_]*SinhIntegral[c_.+d_.*x_],x_Symbol] :=
          Sinh[a+b*x]*SinhIntegral[c+d*x]/b -
          d/b \\[Star] Int[Sinh[a+b*x]*Sinh[c+d*x]/(c+d*x),x] /;
        FreeQ[{a,b,c,d},x]",
        desc: "Integration by parts",
        refs: [],
        pattern: (a__ + b__ * x_).cosh() * rubi_sinh_integral(c__ + d__ * x_),
        with: [a__, b__, c__, d__, x_],
        optional: [a__, b__, c__, d__],
        when: { freeq!([a__, b__, c__, d__], x_) },
        rhs: {
            let trig = &a__ + &b__ * x_;
            let argument = &c__ + &d__ * x_;
            rubi_simp(&(&trig.sinh() * rubi_sinh_integral(&argument) / &b__), x_)
                    - rubi_star(d__, rubi_rhs_int(&(trig.sinh() * &argument.sinh() / argument), x_) / &b__)
        },
    ));
}

fn push_rules_rule_7101(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 7101,
        source: "Int[Sinh[a_.+b_.*x_]*CoshIntegral[c_.+d_.*x_],x_Symbol] :=
          Cosh[a+b*x]*CoshIntegral[c+d*x]/b -
          d/b \\[Star] Int[Cosh[a+b*x]*Cosh[c+d*x]/(c+d*x),x] /;
        FreeQ[{a,b,c,d},x]",
        desc: "Integration by parts",
        refs: [],
        pattern: (a__ + b__ * x_).sinh() * rubi_cosh_integral(c__ + d__ * x_),
        with: [a__, b__, c__, d__, x_],
        optional: [a__, b__, c__, d__],
        when: { freeq!([a__, b__, c__, d__], x_) },
        rhs: {
            let trig = &a__ + &b__ * x_;
            let argument = &c__ + &d__ * x_;
            rubi_simp(&(&trig.cosh() * rubi_cosh_integral(&argument) / &b__), x_)
                    - rubi_star(d__, rubi_rhs_int(&(trig.cosh() * &argument.cosh() / argument), x_) / &b__)
        },
    ));
}

fn push_rules_rule_7102(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, x_);
    rules.push(rubi_rule!(
        order: 7102,
        source: "Int[(e_.+f_.*x_)^m_.*Cosh[a_.+b_.*x_]*SinhIntegral[c_.+d_.*x_],x_Symbol] :=
          (e+f*x)^m*Sinh[a+b*x]*SinhIntegral[c+d*x]/b -
          d/b \\[Star] Int[(e+f*x)^m*Sinh[a+b*x]*Sinh[c+d*x]/(c+d*x),x] -
          f*m/b \\[Star] Int[(e+f*x)^(m-1)*Sinh[a+b*x]*SinhIntegral[c+d*x],x] /;
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
            rubi_simp(&(linear.pow(&m_) * &trig.sinh() * rubi_sinh_integral(&argument) / &b__), x_)
                    - rubi_star(d__, rubi_rhs_int(&(linear.pow(&m_) * &trig.sinh() * &argument.sinh() / &argument), x_) / &b__)
                    - rubi_star(&f__ * &m_ / &b__, rubi_rhs_int(&(linear.pow(&m_ - 1) * trig.sinh() * rubi_sinh_integral(argument)), x_))
        },
    ));
}

fn push_rules_rule_7103(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, x_);
    rules.push(rubi_rule!(
        order: 7103,
        source: "Int[(e_.+f_.*x_)^m_.*Sinh[a_.+b_.*x_]*CoshIntegral[c_.+d_.*x_],x_Symbol] :=
          (e+f*x)^m*Cosh[a+b*x]*CoshIntegral[c+d*x]/b -
          d/b \\[Star] Int[(e+f*x)^m*Cosh[a+b*x]*Cosh[c+d*x]/(c+d*x),x] -
          f*m/b \\[Star] Int[(e+f*x)^(m-1)*Cosh[a+b*x]*CoshIntegral[c+d*x],x] /;
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
            rubi_simp(&(linear.pow(&m_) * &trig.cosh() * rubi_cosh_integral(&argument) / &b__), x_)
                    - rubi_star(d__, rubi_rhs_int(&(linear.pow(&m_) * &trig.cosh() * &argument.cosh() / &argument), x_) / &b__)
                    - rubi_star(&f__ * &m_ / &b__, rubi_rhs_int(&(linear.pow(&m_ - 1) * trig.cosh() * rubi_cosh_integral(argument)), x_))
        },
    ));
}

fn push_rules_rule_7104(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, x_);
    rules.push(rubi_rule!(
        order: 7104,
        source: "Int[(e_.+f_.*x_)^m_.*Cosh[a_.+b_.*x_]*SinhIntegral[c_.+d_.*x_],x_Symbol] :=
          (e+f*x)^(m+1)*Cosh[a+b*x]*SinhIntegral[c+d*x]/(f*(m+1)) -
          d/(f*(m+1)) \\[Star] Int[(e+f*x)^(m+1)*Cosh[a+b*x]*Sinh[c+d*x]/(c+d*x),x] -
          b/(f*(m+1)) \\[Star] Int[(e+f*x)^(m+1)*Sinh[a+b*x]*SinhIntegral[c+d*x],x] /;
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
            rubi_simp(&(linear.pow(&m_ + 1) * &trig.cosh() * rubi_sinh_integral(&argument) / (&f__ * (&m_ + 1))), x_)
                    - rubi_star(d__, rubi_rhs_int(&(linear.pow(&m_ + 1) * &trig.cosh() * &argument.sinh() / &argument), x_) / (&f__ * (&m_ + 1)))
                    - rubi_star(b__, rubi_rhs_int(&(linear.pow(&m_ + 1) * trig.sinh() * rubi_sinh_integral(argument)), x_) / (&f__ * (&m_ + 1)))
        },
    ));
}

fn push_rules_rule_7105(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, x_);
    rules.push(rubi_rule!(
        order: 7105,
        source: "Int[(e_.+f_.*x_)^m_*Sinh[a_.+b_.*x_]*CoshIntegral[c_.+d_.*x_],x_Symbol] :=
          (e+f*x)^(m+1)*Sinh[a+b*x]*CoshIntegral[c+d*x]/(f*(m+1)) -
          d/(f*(m+1)) \\[Star] Int[(e+f*x)^(m+1)*Sinh[a+b*x]*Cosh[c+d*x]/(c+d*x),x] -
          b/(f*(m+1)) \\[Star] Int[(e+f*x)^(m+1)*Cosh[a+b*x]*CoshIntegral[c+d*x],x] /;
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
            rubi_simp(&(linear.pow(&m_ + 1) * &trig.sinh() * rubi_cosh_integral(&argument) / (&f__ * (&m_ + 1))), x_)
                    - rubi_star(d__, rubi_rhs_int(&(linear.pow(&m_ + 1) * &trig.sinh() * &argument.cosh() / &argument), x_) / (&f__ * (&m_ + 1)))
                    - rubi_star(b__, rubi_rhs_int(&(linear.pow(&m_ + 1) * trig.cosh() * rubi_cosh_integral(argument)), x_) / (&f__ * (&m_ + 1)))
        },
    ));
}

fn push_rules_rule_7106(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 7106,
        source: "Int[SinhIntegral[d_.*(a_.+b_.*Log[c_.*x_^n_.])],x_Symbol] :=
          x*SinhIntegral[d*(a+b*Log[c*x^n])] - b*d*n \\[Star] Int[Sinh[d*(a+b*Log[c*x^n])]/(d*(a+b*Log[c*x^n])),x] /;
        FreeQ[{a,b,c,d,n},x]",
        desc: "Integration by parts",
        refs: [],
        pattern: rubi_sinh_integral(d__ * (a__ + b__ * (c__ * x_.pow(n_)).log())),
        with: [d__, a__, b__, c__, n_, x_],
        optional: [d__, a__, b__, c__, n_],
        when: { freeq!([a__, b__, c__, d__, n_], x_) },
        rhs: {
            let argument = &d__ * (&a__ + &b__ * (&c__ * x_.pow(&n_)).log());
            rubi_simp(&(x_ * rubi_sinh_integral(&argument)), x_)
                    - rubi_star(&b__ * &d__ * &n_, rubi_rhs_int(&(&argument.sinh() / argument), x_))
        },
    ));
}

fn push_rules_rule_7107(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 7107,
        source: "Int[CoshIntegral[d_.*(a_.+b_.*Log[c_.*x_^n_.])],x_Symbol] :=
          x*CoshIntegral[d*(a+b*Log[c*x^n])] - b*d*n \\[Star] Int[Cosh[d*(a+b*Log[c*x^n])]/(d*(a+b*Log[c*x^n])),x] /;
        FreeQ[{a,b,c,d,n},x]",
        desc: "Integration by parts",
        refs: [],
        pattern: rubi_cosh_integral(d__ * (a__ + b__ * (c__ * x_.pow(n_)).log())),
        with: [d__, a__, b__, c__, n_, x_],
        optional: [d__, a__, b__, c__, n_],
        when: { freeq!([a__, b__, c__, d__, n_], x_) },
        rhs: {
            let argument = &d__ * (&a__ + &b__ * (&c__ * x_.pow(&n_)).log());
            rubi_simp(&(x_ * rubi_cosh_integral(&argument)), x_)
                    - rubi_star(&b__ * &d__ * &n_, rubi_rhs_int(&(&argument.cosh() / argument), x_))
        },
    ));
}

fn push_rules_rule_7108(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_f_, a__, b__, c__, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 7108,
        source: "Int[F_[d_.*(a_.+b_.*Log[c_.*x_^n_.])]/x_,x_Symbol] :=
          1/n \\[Star] Subst[F[d*(a+b*x)],x,Log[c*x^n]] /;
        FreeQ[{a,b,c,d,n},x] && MemberQ[{SinhIntegral,CoshIntegral},x]",
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
                        rubi_symbols().sinh_integral,
                        rubi_symbols().cosh_integral,
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

fn push_rules_rule_7109(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 7109,
        source: "Int[(e_.*x_)^m_.*SinhIntegral[d_.*(a_.+b_.*Log[c_.*x_^n_.])],x_Symbol] :=
          (e*x)^(m+1)*SinhIntegral[d*(a+b*Log[c*x^n])]/(e*(m+1)) -
          b*d*n/(m+1) \\[Star] Int[(e*x)^m*Sinh[d*(a+b*Log[c*x^n])]/(d*(a+b*Log[c*x^n])),x] /;
        FreeQ[{a,b,c,d,e,m,n},x] && NeQ[m,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern: (e__ * x_).pow(m_) * rubi_sinh_integral(d__ * (a__ + b__ * (c__ * x_.pow(n_)).log())),
        with: [e__, m_, d__, a__, b__, c__, n_, x_],
        optional: [e__, m_, d__, a__, b__, c__, n_],
        when: { freeq!([a__, b__, c__, d__, e__, m_, n_], x_) && neq!(m_, -1) },
        rhs: {
            let scaled = &e__ * x_;
            let argument = &d__ * (&a__ + &b__ * (&c__ * x_.pow(&n_)).log());
            rubi_simp(&(scaled.pow(&m_ + 1) * rubi_sinh_integral(&argument) / (&e__ * (&m_ + 1))), x_)
                    - rubi_star(&b__ * &d__ * &n_ / (&m_ + 1), rubi_rhs_int(&(scaled.pow(&m_) * &argument.sinh() / argument), x_))
        },
    ));
}

fn push_rules_rule_7110(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 7110,
        source: "Int[(e_.*x_)^m_.*CoshIntegral[d_.*(a_.+b_.*Log[c_.*x_^n_.])],x_Symbol] :=
          (e*x)^(m+1)*CoshIntegral[d*(a+b*Log[c*x^n])]/(e*(m+1)) -
          b*d*n/(m+1) \\[Star] Int[(e*x)^m*Cosh[d*(a+b*Log[c*x^n])]/(d*(a+b*Log[c*x^n])),x] /;
        FreeQ[{a,b,c,d,e,m,n},x] && NeQ[m,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern: (e__ * x_).pow(m_) * rubi_cosh_integral(d__ * (a__ + b__ * (c__ * x_.pow(n_)).log())),
        with: [e__, m_, d__, a__, b__, c__, n_, x_],
        optional: [e__, m_, d__, a__, b__, c__, n_],
        when: { freeq!([a__, b__, c__, d__, e__, m_, n_], x_) && neq!(m_, -1) },
        rhs: {
            let scaled = &e__ * x_;
            let argument = &d__ * (&a__ + &b__ * (&c__ * x_.pow(&n_)).log());
            rubi_simp(&(scaled.pow(&m_ + 1) * rubi_cosh_integral(&argument) / (&e__ * (&m_ + 1))), x_)
                    - rubi_star(&b__ * &d__ * &n_ / (&m_ + 1), rubi_rhs_int(&(scaled.pow(&m_) * &argument.cosh() / argument), x_))
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
    (e__ + f__ * x_).pow(m_) * (a__ + b__ * x_).cosh() * rubi_cosh_integral(c__ + d__ * x_)
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
    (e__ + f__ * x_).pow(m_) * (a__ + b__ * x_).cosh() * rubi_sinh_integral(c__ + d__ * x_)
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
    (e__ + f__ * x_).pow(m_) * (a__ + b__ * x_).sinh() * rubi_cosh_integral(c__ + d__ * x_)
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
    (e__ + f__ * x_).pow(m_) * (a__ + b__ * x_).sinh() * rubi_sinh_integral(c__ + d__ * x_)
}
