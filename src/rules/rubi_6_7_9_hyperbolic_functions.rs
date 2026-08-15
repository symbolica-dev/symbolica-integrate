use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_6091(rules);
    push_rules_rule_6092(rules);
    push_rules_rule_6093(rules);
    push_rules_rule_6094(rules);
    push_rules_rule_6095(rules);
    push_rules_rule_6096(rules);
    push_rules_rule_6097(rules);
    push_rules_rule_6098(rules);
    push_rules_rule_6099(rules);
    push_rules_rule_6100(rules);
    push_rules_rule_6101(rules);
    push_rules_rule_6102(rules);
    push_rules_rule_6103(rules);
    push_rules_rule_6104(rules);
    push_rules_rule_6105(rules);
    push_rules_rule_6106(rules);
    push_rules_rule_6107(rules);
    push_rules_rule_6108(rules);
    push_rules_rule_6109(rules);
    push_rules_rule_6110(rules);
    push_rules_rule_6111(rules);
    push_rules_rule_6112(rules);
    push_rules_rule_6113(rules);
    push_rules_rule_6114(rules);
    push_rules_rule_6115(rules);
    push_rules_rule_6116(rules);
    push_rules_rule_6117(rules);
    push_rules_rule_6118(rules);
    push_rules_rule_6119(rules);
    push_rules_rule_6120(rules);
    push_rules_rule_6121(rules);
    push_rules_rule_6122(rules);
    push_rules_rule_6123(rules);
    push_rules_rule_6124(rules);
    push_rules_rule_6125(rules);
    push_rules_rule_6126(rules);
    push_rules_rule_6127(rules);
    push_rules_rule_6128(rules);
    push_rules_rule_6129(rules);
    push_rules_rule_6130(rules);
    push_rules_rule_6131(rules);
    push_rules_rule_6132(rules);
    push_rules_rule_6133(rules);
    push_rules_rule_6134(rules);
    push_rules_rule_6135(rules);
    push_rules_rule_6136(rules);
    push_rules_rule_6137(rules);
    push_rules_rule_6138(rules);
    push_rules_rule_6139(rules);
    push_rules_rule_6140(rules);
    push_rules_rule_6141(rules);
    push_rules_rule_6142(rules);
    push_rules_rule_6143(rules);
    push_rules_rule_6144(rules);
    push_rules_rule_6145(rules);
    push_rules_rule_6146(rules);
    push_rules_rule_6147(rules);
    push_rules_rule_6148(rules);
    push_rules_rule_6149(rules);
    push_rules_rule_6150(rules);
    push_rules_rule_6151(rules);
    push_rules_rule_6152(rules);
    push_rules_rule_6153(rules);
    push_rules_rule_6154(rules);
    push_rules_rule_6155(rules);
    push_rules_rule_6156(rules);
    push_rules_rule_6157(rules);
    push_rules_rule_6158(rules);
    push_rules_rule_6159(rules);
    push_rules_rule_6160(rules);
    push_rules_rule_6161(rules);
    push_rules_rule_6162(rules);
    push_rules_rule_6163(rules);
    push_rules_rule_6164(rules);
    push_rules_rule_6165(rules);
    push_rules_rule_6166(rules);
    push_rules_rule_6167(rules);
    push_rules_rule_6168(rules);
    push_rules_rule_6169(rules);
    push_rules_rule_6170(rules);
    push_rules_rule_6171(rules);
    push_rules_rule_6172(rules);
    push_rules_rule_6173(rules);
    push_rules_rule_6174(rules);
    push_rules_rule_6175(rules);
    push_rules_rule_6176(rules);
    push_rules_rule_6177(rules);
    push_rules_rule_6178(rules);
    push_rules_rule_6179(rules);
    push_rules_rule_6180(rules);
    push_rules_rule_6181(rules);
    push_rules_rule_6182(rules);
    push_rules_rule_6183(rules);
    push_rules_rule_6184(rules);
    push_rules_rule_6185(rules);
    push_rules_rule_6186(rules);
}

fn push_rules_rule_6091(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 6091,
        source: "Int[(e_.+f_.*x_)^m_.*Sinh[c_.+d_.*x_]^n_./(a_+b_.*Sinh[c_.+d_.*x_]),x_Symbol] :=
          1/b \\[Star] Int[(e+f*x)^m*Sinh[c+d*x]^(n-1),x] - a/b \\[Star] Int[(e+f*x)^m*Sinh[c+d*x]^(n-1)/(a+b*Sinh[c+d*x]),x] /;
        FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && IGtQ[n,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (e__ + f__ * x_).pow(m_) * (c__ + d__ * x_).sinh().pow(n_)
            / (a__ + b__ * (c__ + d__ * x_).sinh()),
        with: [e__, f__, m_, c__, d__, n_, a__, b__, x_],
        optional: [e__, f__, m_, c__, d__, n_, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && igtq!(m_, 0)
                && igtq!(n_, 0)
        },
        rhs: {
            let linear = &e__ + &f__ * x_;
            let angle = &c__ + &d__ * x_;
            let hyper = angle.sinh();
            let reduced = linear.pow(&m_) * hyper.pow(&n_ - 1);
            let first = rubi_rhs_int(&reduced, x_);
            let second = rubi_rhs_int(&(reduced / (&a__ + &b__ * hyper)), x_);

            rubi_star(Atom::num(1) / &b__, first)
                    - rubi_star(&a__ / &b__, second)
        },
    ));
}

fn push_rules_rule_6092(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 6092,
        source: "Int[(e_.+f_.*x_)^m_.*Cosh[c_.+d_.*x_]^n_./(a_+b_.*Cosh[c_.+d_.*x_]),x_Symbol] :=
          1/b \\[Star] Int[(e+f*x)^m*Cosh[c+d*x]^(n-1),x] - a/b \\[Star] Int[(e+f*x)^m*Cosh[c+d*x]^(n-1)/(a+b*Cosh[c+d*x]),x] /;
        FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && IGtQ[n,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (e__ + f__ * x_).pow(m_) * (c__ + d__ * x_).cosh().pow(n_)
            / (a__ + b__ * (c__ + d__ * x_).cosh()),
        with: [e__, f__, m_, c__, d__, n_, a__, b__, x_],
        optional: [e__, f__, m_, c__, d__, n_, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && igtq!(m_, 0)
                && igtq!(n_, 0)
        },
        rhs: {
            let linear = &e__ + &f__ * x_;
            let angle = &c__ + &d__ * x_;
            let hyper = angle.cosh();
            let reduced = linear.pow(&m_) * hyper.pow(&n_ - 1);
            let first = rubi_rhs_int(&reduced, x_);
            let second = rubi_rhs_int(&(reduced / (&a__ + &b__ * hyper)), x_);

            rubi_star(Atom::num(1) / &b__, first)
                    - rubi_star(&a__ / &b__, second)
        },
    ));
}

fn push_rules_rule_6093(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, x_);
    rules.push(rubi_rule!(
        order: 6093,
        source: "Int[(e_.+f_.*x_)^m_.*Cosh[c_.+d_.*x_]/(a_+b_.*Sinh[c_.+d_.*x_]),x_Symbol] :=
          -(e+f*x)^(m+1)/(b*f*(m+1)) + 2 \\[Star] Int[(e+f*x)^m*E^(c+d*x)/(a+b*E^(c+d*x)),x] /;
        FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && EqQ[a^2+b^2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [e__, f__, m_, c__, d__, a__, b__, x_],
        optional: [e__, f__, m_, c__, d__, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && igtq!(m_, 0)
                && eqq!(a__.pow(2) + b__.pow(2), 0)
        },
        rhs: {
            let linear = &e__ + &f__ * x_;
            let exponential = (&c__ + &d__ * x_).exp();
            let recursive = rubi_rhs_int(
                &(linear.pow(&m_) * &exponential / (&a__ + &b__ * exponential)),
                x_,
            );

            rubi_simp(&(-linear.pow(&m_ + 1) / (&b__ * &f__ * (&m_ + 1))), x_)
                    + rubi_star(Atom::num(2), recursive)
        },
    ));
}

fn push_rules_rule_6094(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, x_);
    rules.push(rubi_rule!(
        order: 6094,
        source: "Int[(e_.+f_.*x_)^m_.*Sinh[c_.+d_.*x_]/(a_+b_.*Cosh[c_.+d_.*x_]),x_Symbol] :=
          -(e+f*x)^(m+1)/(b*f*(m+1)) + 2 \\[Star] Int[(e+f*x)^m*E^(c+d*x)/(a+b*E^(c+d*x)),x] /;
        FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && EqQ[a^2-b^2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [e__, f__, m_, c__, d__, a__, b__, x_],
        optional: [e__, f__, m_, c__, d__, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && igtq!(m_, 0)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
        },
        rhs: {
            let linear = &e__ + &f__ * x_;
            let exponential = (&c__ + &d__ * x_).exp();
            let recursive = rubi_rhs_int(
                &(linear.pow(&m_) * &exponential / (&a__ + &b__ * exponential)),
                x_,
            );

            rubi_simp(&(-linear.pow(&m_ + 1) / (&b__ * &f__ * (&m_ + 1))), x_)
                    + rubi_star(Atom::num(2), recursive)
        },
    ));
}

fn push_rules_rule_6095(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, x_);
    rules.push(rubi_rule!(
        order: 6095,
        source: "Int[(e_.+f_.*x_)^m_.*Cosh[c_.+d_.*x_]/(a_+b_.*Sinh[c_.+d_.*x_]),x_Symbol] :=
          -(e+f*x)^(m+1)/(b*f*(m+1)) +
          Int[(e+f*x)^m*E^(c+d*x)/(a-Rt[a^2+b^2,2]+b*E^(c+d*x)),x] +
          Int[(e+f*x)^m*E^(c+d*x)/(a+Rt[a^2+b^2,2]+b*E^(c+d*x)),x] /;
        FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && NeQ[a^2+b^2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [e__, f__, m_, c__, d__, a__, b__, x_],
        optional: [e__, f__, m_, c__, d__, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && igtq!(m_, 0)
                && neq!(a__.pow(2) + b__.pow(2), 0)
        },
        rhs: {
            let linear = &e__ + &f__ * x_;
            let exponential = (&c__ + &d__ * x_).exp();
            let root = rubi_rt(&(a__.pow(2) + b__.pow(2)), 2);
            let first = rubi_rhs_int(
                &(linear.pow(&m_) * &exponential / (&a__ - &root + &b__ * &exponential)),
                x_,
            );
            let second = rubi_rhs_int(
                &(linear.pow(&m_) * &exponential / (&a__ + &root + &b__ * exponential)),
                x_,
            );

            rubi_simp(&(-linear.pow(&m_ + 1) / (&b__ * &f__ * (&m_ + 1))), x_) + first + second
        },
    ));
}

fn push_rules_rule_6096(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, x_);
    rules.push(rubi_rule!(
        order: 6096,
        source: "Int[(e_.+f_.*x_)^m_.*Sinh[c_.+d_.*x_]/(a_+b_.*Cosh[c_.+d_.*x_]),x_Symbol] :=
          -(e+f*x)^(m+1)/(b*f*(m+1)) +
          Int[(e+f*x)^m*E^(c+d*x)/(a-Rt[a^2-b^2,2]+b*E^(c+d*x)),x] +
          Int[(e+f*x)^m*E^(c+d*x)/(a+Rt[a^2-b^2,2]+b*E^(c+d*x)),x] /;
        FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && NeQ[a^2-b^2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [e__, f__, m_, c__, d__, a__, b__, x_],
        optional: [e__, f__, m_, c__, d__, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && igtq!(m_, 0)
                && neq!(a__.pow(2) - b__.pow(2), 0)
        },
        rhs: {
            let linear = &e__ + &f__ * x_;
            let exponential = (&c__ + &d__ * x_).exp();
            let root = rubi_rt(&(a__.pow(2) - b__.pow(2)), 2);
            let first = rubi_rhs_int(
                &(linear.pow(&m_) * &exponential / (&a__ - &root + &b__ * &exponential)),
                x_,
            );
            let second = rubi_rhs_int(
                &(linear.pow(&m_) * &exponential / (&a__ + &root + &b__ * exponential)),
                x_,
            );

            rubi_simp(&(-linear.pow(&m_ + 1) / (&b__ * &f__ * (&m_ + 1))), x_) + first + second
        },
    ));
}

fn push_rules_rule_6097(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 6097,
        source: "Int[(e_.+f_.*x_)^m_.*Cosh[c_.+d_.*x_]^n_/(a_+b_.*Sinh[c_.+d_.*x_]),x_Symbol] :=
          1/a \\[Star] Int[(e+f*x)^m*Cosh[c+d*x]^(n-2),x] +
          1/b \\[Star] Int[(e+f*x)^m*Cosh[c+d*x]^(n-2)*Sinh[c+d*x],x] /;
        FreeQ[{a,b,c,d,e,f,m},x] && IGtQ[n,1] && EqQ[a^2+b^2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [e__, f__, m_, c__, d__, n_, a__, b__, x_],
        optional: [e__, f__, m_, c__, d__, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_], x_)
                && igtq!(n_, 1)
                && eqq!(a__.pow(2) + b__.pow(2), 0)
        },
        rhs: {
            let linear = &e__ + &f__ * x_;
            let angle = &c__ + &d__ * x_;
            let reduced = linear.pow(&m_) * angle.cosh().pow(&n_ - 2);
            let first = rubi_rhs_int(&reduced, x_);
            let second = rubi_rhs_int(&(reduced * angle.sinh()), x_);

            rubi_star(Atom::num(1) / &a__, first)
                    + rubi_star(Atom::num(1) / &b__, second)
        },
    ));
}

fn push_rules_rule_6098(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 6098,
        source: "Int[(e_.+f_.*x_)^m_.*Sinh[c_.+d_.*x_]^n_/(a_+b_.*Cosh[c_.+d_.*x_]),x_Symbol] :=
          -1/a \\[Star] Int[(e+f*x)^m*Sinh[c+d*x]^(n-2),x] +
          1/b \\[Star] Int[(e+f*x)^m*Sinh[c+d*x]^(n-2)*Cosh[c+d*x],x] /;
        FreeQ[{a,b,c,d,e,f,m},x] && IGtQ[n,1] && EqQ[a^2-b^2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [e__, f__, m_, c__, d__, n_, a__, b__, x_],
        optional: [e__, f__, m_, c__, d__, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_], x_)
                && igtq!(n_, 1)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
        },
        rhs: {
            let linear = &e__ + &f__ * x_;
            let angle = &c__ + &d__ * x_;
            let reduced = linear.pow(&m_) * angle.sinh().pow(&n_ - 2);
            let first = rubi_rhs_int(&reduced, x_);
            let second = rubi_rhs_int(&(reduced * angle.cosh()), x_);

            rubi_star(-Atom::num(1) / &a__, first)
                    + rubi_star(Atom::num(1) / &b__, second)
        },
    ));
}

fn push_rules_rule_6099(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 6099,
        source: "Int[(e_.+f_.*x_)^m_.*Cosh[c_.+d_.*x_]^n_/(a_+b_.*Sinh[c_.+d_.*x_]),x_Symbol] :=
          -a/b^2 \\[Star] Int[(e+f*x)^m*Cosh[c+d*x]^(n-2),x] +
          1/b \\[Star] Int[(e+f*x)^m*Cosh[c+d*x]^(n-2)*Sinh[c+d*x],x] +
          (a^2+b^2)/b^2 \\[Star] Int[(e+f*x)^m*Cosh[c+d*x]^(n-2)/(a+b*Sinh[c+d*x]),x] /;
        FreeQ[{a,b,c,d,e,f},x] && IGtQ[n,1] && NeQ[a^2+b^2,0] && IGtQ[m,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [e__, f__, m_, c__, d__, n_, a__, b__, x_],
        optional: [e__, f__, m_, c__, d__, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && igtq!(n_, 1)
                && neq!(a__.pow(2) + b__.pow(2), 0)
                && igtq!(m_, 0)
        },
        rhs: {
            let linear = &e__ + &f__ * x_;
            let angle = &c__ + &d__ * x_;
            let cosh_reduced = angle.cosh().pow(&n_ - 2);
            let reduced = linear.pow(&m_) * &cosh_reduced;
            let first = rubi_rhs_int(&reduced, x_);
            let second = rubi_rhs_int(&(&reduced * angle.sinh()), x_);
            let third = rubi_rhs_int(&(reduced / (&a__ + &b__ * angle.sinh())), x_);

            rubi_star(-&a__ / b__.pow(2), first)
                    + rubi_star(Atom::num(1) / &b__, second)
                    + rubi_star((a__.pow(2) + b__.pow(2)) / b__.pow(2), third)
        },
    ));
}

fn push_rules_rule_6100(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 6100,
        source: "Int[(e_.+f_.*x_)^m_.*Sinh[c_.+d_.*x_]^n_/(a_+b_.*Cosh[c_.+d_.*x_]),x_Symbol] :=
          -a/b^2 \\[Star] Int[(e+f*x)^m*Sinh[c+d*x]^(n-2),x] +
          1/b \\[Star] Int[(e+f*x)^m*Sinh[c+d*x]^(n-2)*Cosh[c+d*x],x] +
          (a^2-b^2)/b^2 \\[Star] Int[(e+f*x)^m*Sinh[c+d*x]^(n-2)/(a+b*Cosh[c+d*x]),x] /;
        FreeQ[{a,b,c,d,e,f},x] && IGtQ[n,1] && NeQ[a^2-b^2,0] && IGtQ[m,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [e__, f__, m_, c__, d__, n_, a__, b__, x_],
        optional: [e__, f__, m_, c__, d__, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && igtq!(n_, 1)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && igtq!(m_, 0)
        },
        rhs: {
            let linear = &e__ + &f__ * x_;
            let angle = &c__ + &d__ * x_;
            let sinh_reduced = angle.sinh().pow(&n_ - 2);
            let reduced = linear.pow(&m_) * &sinh_reduced;
            let first = rubi_rhs_int(&reduced, x_);
            let second = rubi_rhs_int(&(&reduced * angle.cosh()), x_);
            let third = rubi_rhs_int(&(reduced / (&a__ + &b__ * angle.cosh())), x_);

            rubi_star(-&a__ / b__.pow(2), first)
                    + rubi_star(Atom::num(1) / &b__, second)
                    + rubi_star((a__.pow(2) - b__.pow(2)) / b__.pow(2), third)
        },
    ));
}

fn push_rules_rule_6101(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 6101,
        source: "Int[(e_.+f_.*x_)^m_.*Tanh[c_.+d_.*x_]^n_./(a_+b_.*Sinh[c_.+d_.*x_]),x_Symbol] :=
          1/b \\[Star] Int[(e+f*x)^m*Sech[c+d*x]*Tanh[c+d*x]^(n-1),x] - a/b \\[Star] Int[(e+f*x)^m*Sech[c+d*x]*Tanh[c+d*x]^(n-1)/(a+b*Sinh[c+d*x]),x] /;
        FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && IGtQ[n,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (e__ + f__ * x_).pow(m_) * (c__ + d__ * x_).tanh().pow(n_)
            / (a__ + b__ * (c__ + d__ * x_).sinh()),
        with: [e__, f__, m_, c__, d__, n_, a__, b__, x_],
        optional: [e__, f__, m_, c__, d__, n_, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && igtq!(m_, 0)
                && igtq!(n_, 0)
        },
        rhs: {
            let linear = &e__ + &f__ * x_;
            let angle = &c__ + &d__ * x_;
            let reduced = linear.pow(&m_) * &angle.sech() * &angle.tanh().pow(&n_ - 1);
            let first = rubi_rhs_int(&reduced, x_);
            let second = rubi_rhs_int(&(reduced / (&a__ + &b__ * angle.sinh())), x_);

            rubi_star(Atom::num(1) / &b__, first)
                    - rubi_star(&a__ / &b__, second)
        },
    ));
}

fn push_rules_rule_6102(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 6102,
        source: "Int[(e_.+f_.*x_)^m_.*Coth[c_.+d_.*x_]^n_./(a_+b_.*Cosh[c_.+d_.*x_]),x_Symbol] :=
          1/b \\[Star] Int[(e+f*x)^m*Csch[c+d*x]*Coth[c+d*x]^(n-1),x] - a/b \\[Star] Int[(e+f*x)^m*Csch[c+d*x]*Coth[c+d*x]^(n-1)/(a+b*Cosh[c+d*x]),x] /;
        FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && IGtQ[n,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (e__ + f__ * x_).pow(m_) * (c__ + d__ * x_).coth().pow(n_)
            / (a__ + b__ * (c__ + d__ * x_).cosh()),
        with: [e__, f__, m_, c__, d__, n_, a__, b__, x_],
        optional: [e__, f__, m_, c__, d__, n_, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && igtq!(m_, 0)
                && igtq!(n_, 0)
        },
        rhs: {
            let linear = &e__ + &f__ * x_;
            let angle = &c__ + &d__ * x_;
            let reduced = linear.pow(&m_) * &angle.csch() * &angle.coth().pow(&n_ - 1);
            let first = rubi_rhs_int(&reduced, x_);
            let second = rubi_rhs_int(&(reduced / (&a__ + &b__ * angle.cosh())), x_);

            rubi_star(Atom::num(1) / &b__, first)
                    - rubi_star(&a__ / &b__, second)
        },
    ));
}

fn push_rules_rule_6103(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 6103,
        source: "Int[(e_.+f_.*x_)^m_.*Coth[c_.+d_.*x_]^n_./(a_+b_.*Sinh[c_.+d_.*x_]),x_Symbol] :=
          1/a \\[Star] Int[(e+f*x)^m*Coth[c+d*x]^n,x] - b/a \\[Star] Int[(e+f*x)^m*Cosh[c+d*x]*Coth[c+d*x]^(n-1)/(a+b*Sinh[c+d*x]),x] /;
        FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && IGtQ[n,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (e__ + f__ * x_).pow(m_) * (c__ + d__ * x_).coth().pow(n_)
            / (a__ + b__ * (c__ + d__ * x_).sinh()),
        with: [e__, f__, m_, c__, d__, n_, a__, b__, x_],
        optional: [e__, f__, m_, c__, d__, n_, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && igtq!(m_, 0)
                && igtq!(n_, 0)
        },
        rhs: {
            let linear = &e__ + &f__ * x_;
            let angle = &c__ + &d__ * x_;
            let first_integrand = linear.pow(&m_) * &angle.coth().pow(&n_);
            let second_integrand = linear.pow(&m_) * &angle.cosh() * &angle.coth().pow(&n_ - 1)
                / (&a__ + &b__ * angle.sinh());
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(Atom::num(1) / &a__, first)
                    - rubi_star(&b__ / &a__, second)
        },
    ));
}

fn push_rules_rule_6104(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 6104,
        source: "Int[(e_.+f_.*x_)^m_.*Tanh[c_.+d_.*x_]^n_./(a_+b_.*Cosh[c_.+d_.*x_]),x_Symbol] :=
          1/a \\[Star] Int[(e+f*x)^m*Tanh[c+d*x]^n,x] - b/a \\[Star] Int[(e+f*x)^m*Sinh[c+d*x]*Tanh[c+d*x]^(n-1)/(a+b*Cosh[c+d*x]),x] /;
        FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && IGtQ[n,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (e__ + f__ * x_).pow(m_) * (c__ + d__ * x_).tanh().pow(n_)
            / (a__ + b__ * (c__ + d__ * x_).cosh()),
        with: [e__, f__, m_, c__, d__, n_, a__, b__, x_],
        optional: [e__, f__, m_, c__, d__, n_, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && igtq!(m_, 0)
                && igtq!(n_, 0)
        },
        rhs: {
            let linear = &e__ + &f__ * x_;
            let angle = &c__ + &d__ * x_;
            let first_integrand = linear.pow(&m_) * &angle.tanh().pow(&n_);
            let second_integrand = linear.pow(&m_) * &angle.sinh() * &angle.tanh().pow(&n_ - 1)
                / (&a__ + &b__ * angle.cosh());
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(Atom::num(1) / &a__, first)
                    - rubi_star(&b__ / &a__, second)
        },
    ));
}

fn push_rules_rule_6105(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 6105,
        source: "Int[(e_.+f_.*x_)^m_.*Sech[c_.+d_.*x_]^n_./(a_+b_.*Sinh[c_.+d_.*x_]),x_Symbol] :=
          1/a \\[Star] Int[(e+f*x)^m*Sech[c+d*x]^(n+2),x] +
          1/b \\[Star] Int[(e+f*x)^m*Sech[c+d*x]^(n+1)*Tanh[c+d*x],x] /;
        FreeQ[{a,b,c,d,e,f,n},x] && IGtQ[m,0] && EqQ[a^2+b^2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [e__, f__, m_, c__, d__, n_, a__, b__, x_],
        optional: [e__, f__, m_, c__, d__, n_, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, n_], x_)
                && igtq!(m_, 0)
                && eqq!(a__.pow(2) + b__.pow(2), 0)
        },
        rhs: {
            let linear = &e__ + &f__ * x_;
            let angle = &c__ + &d__ * x_;
            let first = rubi_rhs_int(&(linear.pow(&m_) * &angle.sech().pow(&n_ + 2)), x_);
            let second = rubi_rhs_int(
                &(linear.pow(&m_) * &angle.sech().pow(&n_ + 1) * angle.tanh()),
                x_,
            );

            rubi_star(Atom::num(1) / &a__, first)
                    + rubi_star(Atom::num(1) / &b__, second)
        },
    ));
}

fn push_rules_rule_6106(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 6106,
        source: "Int[(e_.+f_.*x_)^m_.*Csch[c_.+d_.*x_]^n_./(a_+b_.*Cosh[c_.+d_.*x_]),x_Symbol] :=
          -1/a \\[Star] Int[(e+f*x)^m*Csch[c+d*x]^(n+2),x] +
          1/b \\[Star] Int[(e+f*x)^m*Csch[c+d*x]^(n+1)*Coth[c+d*x],x] /;
        FreeQ[{a,b,c,d,e,f,n},x] && IGtQ[m,0] && EqQ[a^2-b^2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [e__, f__, m_, c__, d__, n_, a__, b__, x_],
        optional: [e__, f__, m_, c__, d__, n_, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, n_], x_)
                && igtq!(m_, 0)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
        },
        rhs: {
            let linear = &e__ + &f__ * x_;
            let angle = &c__ + &d__ * x_;
            let first = rubi_rhs_int(&(linear.pow(&m_) * &angle.csch().pow(&n_ + 2)), x_);
            let second = rubi_rhs_int(
                &(linear.pow(&m_) * &angle.csch().pow(&n_ + 1) * angle.coth()),
                x_,
            );

            rubi_star(-Atom::num(1) / &a__, first)
                    + rubi_star(Atom::num(1) / &b__, second)
        },
    ));
}

fn push_rules_rule_6107(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 6107,
        source: "Int[(e_.+f_.*x_)^m_.*Sech[c_.+d_.*x_]^n_./(a_+b_.*Sinh[c_.+d_.*x_]),x_Symbol] :=
          b^2/(a^2+b^2) \\[Star] Int[(e+f*x)^m*Sech[c+d*x]^(n-2)/(a+b*Sinh[c+d*x]),x] +
          1/(a^2+b^2) \\[Star] Int[(e+f*x)^m*Sech[c+d*x]^n*(a-b*Sinh[c+d*x]),x] /;
        FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && NeQ[a^2+b^2,0] && IGtQ[n,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [e__, f__, m_, c__, d__, n_, a__, b__, x_],
        optional: [e__, f__, m_, c__, d__, n_, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && igtq!(m_, 0)
                && neq!(a__.pow(2) + b__.pow(2), 0)
                && igtq!(n_, 0)
        },
        rhs: {
            let linear = &e__ + &f__ * x_;
            let angle = &c__ + &d__ * x_;
            let denominator = a__.pow(2) + b__.pow(2);
            let first = rubi_rhs_int(
                &(linear.pow(&m_) * &angle.sech().pow(&n_ - 2) / (&a__ + &b__ * &angle.sinh())),
                x_,
            );
            let second = rubi_rhs_int(
                &(linear.pow(&m_) * &angle.sech().pow(&n_) * (&a__ - &b__ * angle.sinh())),
                x_,
            );

            rubi_star(b__.pow(2) / &denominator, first)
                    + rubi_star(Atom::num(1) / denominator, second)
        },
    ));
}

fn push_rules_rule_6108(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 6108,
        source: "Int[(e_.+f_.*x_)^m_.*Csch[c_.+d_.*x_]^n_./(a_+b_.*Cosh[c_.+d_.*x_]),x_Symbol] :=
          b^2/(a^2-b^2) \\[Star] Int[(e+f*x)^m*Csch[c+d*x]^(n-2)/(a+b*Cosh[c+d*x]),x] +
          1/(a^2-b^2) \\[Star] Int[(e+f*x)^m*Csch[c+d*x]^n*(a-b*Cosh[c+d*x]),x] /;
        FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && NeQ[a^2-b^2,0] && IGtQ[n,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [e__, f__, m_, c__, d__, n_, a__, b__, x_],
        optional: [e__, f__, m_, c__, d__, n_, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && igtq!(m_, 0)
                && neq!(a__.pow(2) - b__.pow(2), 0)
                && igtq!(n_, 0)
        },
        rhs: {
            let linear = &e__ + &f__ * x_;
            let angle = &c__ + &d__ * x_;
            let denominator = a__.pow(2) - b__.pow(2);
            let first = rubi_rhs_int(
                &(linear.pow(&m_) * &angle.csch().pow(&n_ - 2) / (&a__ + &b__ * &angle.cosh())),
                x_,
            );
            let second = rubi_rhs_int(
                &(linear.pow(&m_) * &angle.csch().pow(&n_) * (&a__ - &b__ * angle.cosh())),
                x_,
            );

            rubi_star(b__.pow(2) / &denominator, first)
                    + rubi_star(Atom::num(1) / denominator, second)
        },
    ));
}

fn push_rules_rule_6109(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 6109,
        source: "Int[(e_.+f_.*x_)^m_.*Csch[c_.+d_.*x_]^n_./(a_+b_.*Sinh[c_.+d_.*x_]),x_Symbol] :=
          1/a \\[Star] Int[(e+f*x)^m*Csch[c+d*x]^n,x] - b/a \\[Star] Int[(e+f*x)^m*Csch[c+d*x]^(n-1)/(a+b*Sinh[c+d*x]),x] /;
        FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && IGtQ[n,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (e__ + f__ * x_).pow(m_) * (c__ + d__ * x_).csch().pow(n_)
            / (a__ + b__ * (c__ + d__ * x_).sinh()),
        with: [e__, f__, m_, c__, d__, n_, a__, b__, x_],
        optional: [e__, f__, m_, c__, d__, n_, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && igtq!(m_, 0)
                && igtq!(n_, 0)
        },
        rhs: {
            let linear = &e__ + &f__ * x_;
            let angle = &c__ + &d__ * x_;
            let first_integrand = linear.pow(&m_) * &angle.csch().pow(&n_);
            let second_integrand = linear.pow(&m_) * &angle.csch().pow(&n_ - 1)
                / (&a__ + &b__ * angle.sinh());
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(Atom::num(1) / &a__, first)
                    - rubi_star(&b__ / &a__, second)
        },
    ));
}

fn push_rules_rule_6110(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 6110,
        source: "Int[(e_.+f_.*x_)^m_.*Sech[c_.+d_.*x_]^n_./(a_+b_.*Cosh[c_.+d_.*x_]),x_Symbol] :=
          1/a \\[Star] Int[(e+f*x)^m*Sech[c+d*x]^n,x] - b/a \\[Star] Int[(e+f*x)^m*Sech[c+d*x]^(n-1)/(a+b*Cosh[c+d*x]),x] /;
        FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && IGtQ[n,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (e__ + f__ * x_).pow(m_) * (c__ + d__ * x_).sech().pow(n_)
            / (a__ + b__ * (c__ + d__ * x_).cosh()),
        with: [e__, f__, m_, c__, d__, n_, a__, b__, x_],
        optional: [e__, f__, m_, c__, d__, n_, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && igtq!(m_, 0)
                && igtq!(n_, 0)
        },
        rhs: {
            let linear = &e__ + &f__ * x_;
            let angle = &c__ + &d__ * x_;
            let first_integrand = linear.pow(&m_) * &angle.sech().pow(&n_);
            let second_integrand = linear.pow(&m_) * &angle.sech().pow(&n_ - 1)
                / (&a__ + &b__ * angle.cosh());
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(Atom::num(1) / &a__, first)
                    - rubi_star(&b__ / &a__, second)
        },
    ));
}

fn push_rules_rule_6111(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, capital_f_, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 6111,
        source: "Int[(e_.+f_.*x_)^m_.*F_[c_.+d_.*x_]^n_./(a_+b_.*Sinh[c_.+d_.*x_]),x_Symbol] :=
          Unintegrable[(e+f*x)^m*F[c+d*x]^n/(a+b*Sinh[c+d*x]),x] /;
        FreeQ[{a,b,c,d,e,f,m,n},x] && HyperbolicQ[F]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern: (e__ + f__ * x_).pow(m_) * capital_f_.call(c__ + d__ * x_).pow(n_)
            / (a__ + b__ * (c__ + d__ * x_).sinh()),
        with: [e__, f__, m_, capital_f_, c__, d__, n_, a__, b__, x_],
        optional: [e__, f__, m_, c__, d__, n_, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_], x_)
                && rubi_hyperbolic_head_q(&capital_f_)
        },
        rhs: {
            let linear = &e__ + &f__ * x_;
            let angle = &c__ + &d__ * x_;
            let capital_f_ = rubi_function_head_symbol(&capital_f_).unwrap();
            let integrand = linear.pow(&m_) * capital_f_.call(&angle).pow(&n_)
                / (&a__ + &b__ * angle.sinh());

            rubi_unintegrable(integrand, x_)
        },
    ));
}

fn push_rules_rule_6112(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, capital_f_, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 6112,
        source: "Int[(e_.+f_.*x_)^m_.*F_[c_.+d_.*x_]^n_./(a_+b_.*Cosh[c_.+d_.*x_]),x_Symbol] :=
          Unintegrable[(e+f*x)^m*F[c+d*x]^n/(a+b*Cosh[c+d*x]),x] /;
        FreeQ[{a,b,c,d,e,f,m,n},x] && HyperbolicQ[F]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern: (e__ + f__ * x_).pow(m_) * capital_f_.call(c__ + d__ * x_).pow(n_)
            / (a__ + b__ * (c__ + d__ * x_).cosh()),
        with: [e__, f__, m_, capital_f_, c__, d__, n_, a__, b__, x_],
        optional: [e__, f__, m_, c__, d__, n_, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_], x_)
                && rubi_hyperbolic_head_q(&capital_f_)
        },
        rhs: {
            let linear = &e__ + &f__ * x_;
            let angle = &c__ + &d__ * x_;
            let capital_f_ = rubi_function_head_symbol(&capital_f_).unwrap();
            let integrand = linear.pow(&m_) * capital_f_.call(&angle).pow(&n_)
                / (&a__ + &b__ * angle.cosh());

            rubi_unintegrable(integrand, x_)
        },
    ));
}

fn push_rules_rule_6113(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6113,
        source: "Int[(e_.+f_.*x_)^m_.*Cosh[c_.+d_.*x_]^p_.*Sinh[c_.+d_.*x_]^n_./(a_+b_.*Sinh[c_.+d_.*x_]),x_Symbol] :=
          1/b \\[Star] Int[(e+f*x)^m*Cosh[c+d*x]^p*Sinh[c+d*x]^(n-1),x] -
          a/b \\[Star] Int[(e+f*x)^m*Cosh[c+d*x]^p*Sinh[c+d*x]^(n-1)/(a+b*Sinh[c+d*x]),x] /;
        FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && IGtQ[n,0] && IGtQ[p,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (e__ + f__ * x_).pow(m_) * (c__ + d__ * x_).cosh().pow(p_) * (c__ + d__ * x_).sinh().pow(n_)
            / (a__ + b__ * (c__ + d__ * x_).sinh()),
        with: [e__, f__, m_, c__, d__, p_, n_, a__, b__, x_],
        optional: [e__, f__, m_, c__, d__, p_, n_, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && igtq!(m_, 0)
                && igtq!(n_, 0)
                && igtq!(p_, 0)
        },
        rhs: {
            let linear = &e__ + &f__ * x_;
            let angle = &c__ + &d__ * x_;
            let reduced = linear.pow(&m_) * &angle.cosh().pow(&p_) * &angle.sinh().pow(&n_ - 1);
            let first = rubi_rhs_int(&reduced, x_);
            let second = rubi_rhs_int(&(reduced / (&a__ + &b__ * angle.sinh())), x_);

            rubi_star(Atom::num(1) / &b__, first)
                    - rubi_star(&a__ / &b__, second)
        },
    ));
}

fn push_rules_rule_6114(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6114,
        source: "Int[(e_.+f_.*x_)^m_.*Sinh[c_.+d_.*x_]^p_.*Cosh[c_.+d_.*x_]^n_./(a_+b_.*Cosh[c_.+d_.*x_]),x_Symbol] :=
          1/b \\[Star] Int[(e+f*x)^m*Sinh[c+d*x]^p*Cosh[c+d*x]^(n-1),x] -
          a/b \\[Star] Int[(e+f*x)^m*Sinh[c+d*x]^p*Cosh[c+d*x]^(n-1)/(a+b*Cosh[c+d*x]),x] /;
        FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && IGtQ[n,0] && IGtQ[p,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (e__ + f__ * x_).pow(m_) * (c__ + d__ * x_).sinh().pow(p_) * (c__ + d__ * x_).cosh().pow(n_)
            / (a__ + b__ * (c__ + d__ * x_).cosh()),
        with: [e__, f__, m_, c__, d__, p_, n_, a__, b__, x_],
        optional: [e__, f__, m_, c__, d__, p_, n_, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && igtq!(m_, 0)
                && igtq!(n_, 0)
                && igtq!(p_, 0)
        },
        rhs: {
            let linear = &e__ + &f__ * x_;
            let angle = &c__ + &d__ * x_;
            let reduced = linear.pow(&m_) * &angle.sinh().pow(&p_) * &angle.cosh().pow(&n_ - 1);
            let first = rubi_rhs_int(&reduced, x_);
            let second = rubi_rhs_int(&(reduced / (&a__ + &b__ * angle.cosh())), x_);

            rubi_star(Atom::num(1) / &b__, first)
                    - rubi_star(&a__ / &b__, second)
        },
    ));
}

fn push_rules_rule_6115(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6115,
        source: "Int[(e_.+f_.*x_)^m_.*Sinh[c_.+d_.*x_]^p_.*Tanh[c_.+d_.*x_]^n_./(a_+b_.*Sinh[c_.+d_.*x_]),x_Symbol] :=
          1/b \\[Star] Int[(e+f*x)^m*Sinh[c+d*x]^(p-1)*Tanh[c+d*x]^n,x] -
          a/b \\[Star] Int[(e+f*x)^m*Sinh[c+d*x]^(p-1)*Tanh[c+d*x]^n/(a+b*Sinh[c+d*x]),x] /;
        FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && IGtQ[n,0] && IGtQ[p,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (e__ + f__ * x_).pow(m_) * (c__ + d__ * x_).sinh().pow(p_) * (c__ + d__ * x_).tanh().pow(n_)
            / (a__ + b__ * (c__ + d__ * x_).sinh()),
        with: [e__, f__, m_, c__, d__, p_, n_, a__, b__, x_],
        optional: [e__, f__, m_, c__, d__, p_, n_, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && igtq!(m_, 0)
                && igtq!(n_, 0)
                && igtq!(p_, 0)
        },
        rhs: {
            let linear = &e__ + &f__ * x_;
            let angle = &c__ + &d__ * x_;
            let reduced = linear.pow(&m_) * &angle.sinh().pow(&p_ - 1) * &angle.tanh().pow(&n_);
            let first = rubi_rhs_int(&reduced, x_);
            let second = rubi_rhs_int(&(reduced / (&a__ + &b__ * angle.sinh())), x_);

            rubi_star(Atom::num(1) / &b__, first)
                    - rubi_star(&a__ / &b__, second)
        },
    ));
}

fn push_rules_rule_6116(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6116,
        source: "Int[(e_.+f_.*x_)^m_.*Cosh[c_.+d_.*x_]^p_.*Coth[c_.+d_.*x_]^n_./(a_+b_.*Cosh[c_.+d_.*x_]),x_Symbol] :=
          1/b \\[Star] Int[(e+f*x)^m*Cosh[c+d*x]^(p-1)*Coth[c+d*x]^n,x] -
          a/b \\[Star] Int[(e+f*x)^m*Cosh[c+d*x]^(p-1)*Coth[c+d*x]^n/(a+b*Cosh[c+d*x]),x] /;
        FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && IGtQ[n,0] && IGtQ[p,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (e__ + f__ * x_).pow(m_) * (c__ + d__ * x_).cosh().pow(p_) * (c__ + d__ * x_).coth().pow(n_)
            / (a__ + b__ * (c__ + d__ * x_).cosh()),
        with: [e__, f__, m_, c__, d__, p_, n_, a__, b__, x_],
        optional: [e__, f__, m_, c__, d__, p_, n_, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && igtq!(m_, 0)
                && igtq!(n_, 0)
                && igtq!(p_, 0)
        },
        rhs: {
            let linear = &e__ + &f__ * x_;
            let angle = &c__ + &d__ * x_;
            let reduced = linear.pow(&m_) * &angle.cosh().pow(&p_ - 1) * &angle.coth().pow(&n_);
            let first = rubi_rhs_int(&reduced, x_);
            let second = rubi_rhs_int(&(reduced / (&a__ + &b__ * angle.cosh())), x_);

            rubi_star(Atom::num(1) / &b__, first)
                    - rubi_star(&a__ / &b__, second)
        },
    ));
}

fn push_rules_rule_6117(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6117,
        source: "Int[(e_.+f_.*x_)^m_.*Sech[c_.+d_.*x_]^p_.*Tanh[c_.+d_.*x_]^n_./(a_+b_.*Sinh[c_.+d_.*x_]),x_Symbol] :=
          1/b \\[Star] Int[(e+f*x)^m*Sech[c+d*x]^(p+1)*Tanh[c+d*x]^(n-1),x] -
          a/b \\[Star] Int[(e+f*x)^m*Sech[c+d*x]^(p+1)*Tanh[c+d*x]^(n-1)/(a+b*Sinh[c+d*x]),x] /;
        FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && IGtQ[n,0] && IGtQ[p,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (e__ + f__ * x_).pow(m_) * (c__ + d__ * x_).sech().pow(p_) * (c__ + d__ * x_).tanh().pow(n_)
            / (a__ + b__ * (c__ + d__ * x_).sinh()),
        with: [e__, f__, m_, c__, d__, p_, n_, a__, b__, x_],
        optional: [e__, f__, m_, c__, d__, p_, n_, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && igtq!(m_, 0)
                && igtq!(n_, 0)
                && igtq!(p_, 0)
        },
        rhs: {
            let linear = &e__ + &f__ * x_;
            let angle = &c__ + &d__ * x_;
            let reduced = linear.pow(&m_) * &angle.sech().pow(&p_ + 1) * &angle.tanh().pow(&n_ - 1);
            let first = rubi_rhs_int(&reduced, x_);
            let second = rubi_rhs_int(&(reduced / (&a__ + &b__ * angle.sinh())), x_);

            rubi_star(Atom::num(1) / &b__, first)
                    - rubi_star(&a__ / &b__, second)
        },
    ));
}

fn push_rules_rule_6118(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6118,
        source: "Int[(e_.+f_.*x_)^m_.*Csch[c_.+d_.*x_]^p_.*Coth[c_.+d_.*x_]^n_./(a_+b_.*Cosh[c_.+d_.*x_]),x_Symbol] :=
          1/b \\[Star] Int[(e+f*x)^m*Csch[c+d*x]^(p+1)*Coth[c+d*x]^(n-1),x] -
          a/b \\[Star] Int[(e+f*x)^m*Csch[c+d*x]^(p+1)*Coth[c+d*x]^(n-1)/(a+b*Cosh[c+d*x]),x] /;
        FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && IGtQ[n,0] && IGtQ[p,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (e__ + f__ * x_).pow(m_) * (c__ + d__ * x_).csch().pow(p_) * (c__ + d__ * x_).coth().pow(n_)
            / (a__ + b__ * (c__ + d__ * x_).cosh()),
        with: [e__, f__, m_, c__, d__, p_, n_, a__, b__, x_],
        optional: [e__, f__, m_, c__, d__, p_, n_, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && igtq!(m_, 0)
                && igtq!(n_, 0)
                && igtq!(p_, 0)
        },
        rhs: {
            let linear = &e__ + &f__ * x_;
            let angle = &c__ + &d__ * x_;
            let reduced = linear.pow(&m_) * &angle.csch().pow(&p_ + 1) * &angle.coth().pow(&n_ - 1);
            let first = rubi_rhs_int(&reduced, x_);
            let second = rubi_rhs_int(&(reduced / (&a__ + &b__ * angle.cosh())), x_);

            rubi_star(Atom::num(1) / &b__, first)
                    - rubi_star(&a__ / &b__, second)
        },
    ));
}

fn push_rules_rule_6119(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6119,
        source: "Int[(e_.+f_.*x_)^m_.*Cosh[c_.+d_.*x_]^p_.*Coth[c_.+d_.*x_]^n_./(a_+b_.*Sinh[c_.+d_.*x_]),x_Symbol] :=
          1/a \\[Star] Int[(e+f*x)^m*Cosh[c+d*x]^p*Coth[c+d*x]^n,x] -
          b/a \\[Star] Int[(e+f*x)^m*Cosh[c+d*x]^(p+1)*Coth[c+d*x]^(n-1)/(a+b*Sinh[c+d*x]),x] /;
        FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && IGtQ[n,0] && IGtQ[p,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (e__ + f__ * x_).pow(m_) * (c__ + d__ * x_).cosh().pow(p_) * (c__ + d__ * x_).coth().pow(n_)
            / (a__ + b__ * (c__ + d__ * x_).sinh()),
        with: [e__, f__, m_, c__, d__, p_, n_, a__, b__, x_],
        optional: [e__, f__, m_, c__, d__, p_, n_, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && igtq!(m_, 0)
                && igtq!(n_, 0)
                && igtq!(p_, 0)
        },
        rhs: {
            let linear = &e__ + &f__ * x_;
            let angle = &c__ + &d__ * x_;
            let first_integrand = linear.pow(&m_) * &angle.cosh().pow(&p_) * &angle.coth().pow(&n_);
            let second_integrand = linear.pow(&m_) * &angle.cosh().pow(&p_ + 1) * &angle.coth().pow(&n_ - 1)
                / (&a__ + &b__ * angle.sinh());
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(Atom::num(1) / &a__, first)
                    - rubi_star(&b__ / &a__, second)
        },
    ));
}

fn push_rules_rule_6120(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6120,
        source: "Int[(e_.+f_.*x_)^m_.*Sinh[c_.+d_.*x_]^p_.*Tanh[c_.+d_.*x_]^n_./(a_+b_.*Cosh[c_.+d_.*x_]),x_Symbol] :=
          1/a \\[Star] Int[(e+f*x)^m*Sinh[c+d*x]^p*Tanh[c+d*x]^n,x] -
          b/a \\[Star] Int[(e+f*x)^m*Sinh[c+d*x]^(p+1)*Tanh[c+d*x]^(n-1)/(a+b*Cosh[c+d*x]),x] /;
        FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && IGtQ[n,0] && IGtQ[p,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (e__ + f__ * x_).pow(m_) * (c__ + d__ * x_).sinh().pow(p_) * (c__ + d__ * x_).tanh().pow(n_)
            / (a__ + b__ * (c__ + d__ * x_).cosh()),
        with: [e__, f__, m_, c__, d__, p_, n_, a__, b__, x_],
        optional: [e__, f__, m_, c__, d__, p_, n_, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && igtq!(m_, 0)
                && igtq!(n_, 0)
                && igtq!(p_, 0)
        },
        rhs: {
            let linear = &e__ + &f__ * x_;
            let angle = &c__ + &d__ * x_;
            let first_integrand = linear.pow(&m_) * &angle.sinh().pow(&p_) * &angle.tanh().pow(&n_);
            let second_integrand = linear.pow(&m_) * &angle.sinh().pow(&p_ + 1) * &angle.tanh().pow(&n_ - 1)
                / (&a__ + &b__ * angle.cosh());
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(Atom::num(1) / &a__, first)
                    - rubi_star(&b__ / &a__, second)
        },
    ));
}

fn push_rules_rule_6121(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6121,
        source: "Int[(e_.+f_.*x_)^m_.*Csch[c_.+d_.*x_]^p_.*Coth[c_.+d_.*x_]^n_./(a_+b_.*Sinh[c_.+d_.*x_]),x_Symbol] :=
          1/a \\[Star] Int[(e+f*x)^m*Csch[c+d*x]^p*Coth[c+d*x]^n,x] -
          b/a \\[Star] Int[(e+f*x)^m*Csch[c+d*x]^(p-1)*Coth[c+d*x]^n/(a+b*Sinh[c+d*x]),x] /;
        FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && IGtQ[n,0] && IGtQ[p,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (e__ + f__ * x_).pow(m_) * (c__ + d__ * x_).csch().pow(p_) * (c__ + d__ * x_).coth().pow(n_)
            / (a__ + b__ * (c__ + d__ * x_).sinh()),
        with: [e__, f__, m_, c__, d__, p_, n_, a__, b__, x_],
        optional: [e__, f__, m_, c__, d__, p_, n_, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && igtq!(m_, 0)
                && igtq!(n_, 0)
                && igtq!(p_, 0)
        },
        rhs: {
            let linear = &e__ + &f__ * x_;
            let angle = &c__ + &d__ * x_;
            let first_integrand = linear.pow(&m_) * &angle.csch().pow(&p_) * &angle.coth().pow(&n_);
            let second_integrand = linear.pow(&m_) * &angle.csch().pow(&p_ - 1) * &angle.coth().pow(&n_)
                / (&a__ + &b__ * angle.sinh());
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(Atom::num(1) / &a__, first)
                    - rubi_star(&b__ / &a__, second)
        },
    ));
}

fn push_rules_rule_6122(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6122,
        source: "Int[(e_.+f_.*x_)^m_.*Sech[c_.+d_.*x_]^p_.*Tanh[c_.+d_.*x_]^n_./(a_+b_.*Cosh[c_.+d_.*x_]),x_Symbol] :=
          1/a \\[Star] Int[(e+f*x)^m*Sech[c+d*x]^p*Tanh[c+d*x]^n,x] -
          b/a \\[Star] Int[(e+f*x)^m*Sech[c+d*x]^(p-1)*Tanh[c+d*x]^n/(a+b*Cosh[c+d*x]),x] /;
        FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && IGtQ[n,0] && IGtQ[p,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (e__ + f__ * x_).pow(m_) * (c__ + d__ * x_).sech().pow(p_) * (c__ + d__ * x_).tanh().pow(n_)
            / (a__ + b__ * (c__ + d__ * x_).cosh()),
        with: [e__, f__, m_, c__, d__, p_, n_, a__, b__, x_],
        optional: [e__, f__, m_, c__, d__, p_, n_, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && igtq!(m_, 0)
                && igtq!(n_, 0)
                && igtq!(p_, 0)
        },
        rhs: {
            let linear = &e__ + &f__ * x_;
            let angle = &c__ + &d__ * x_;
            let first_integrand = linear.pow(&m_) * &angle.sech().pow(&p_) * &angle.tanh().pow(&n_);
            let second_integrand = linear.pow(&m_) * &angle.sech().pow(&p_ - 1) * &angle.tanh().pow(&n_)
                / (&a__ + &b__ * angle.cosh());
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(Atom::num(1) / &a__, first)
                    - rubi_star(&b__ / &a__, second)
        },
    ));
}

fn push_rules_rule_6123(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6123,
        source: "Int[(e_.+f_.*x_)^m_.*Sech[c_.+d_.*x_]^p_.*Csch[c_.+d_.*x_]^n_./(a_+b_.*Sinh[c_.+d_.*x_]),x_Symbol] :=
          1/a \\[Star] Int[(e+f*x)^m*Sech[c+d*x]^p*Csch[c+d*x]^n,x] -
          b/a \\[Star] Int[(e+f*x)^m*Sech[c+d*x]^p*Csch[c+d*x]^(n-1)/(a+b*Sinh[c+d*x]),x] /;
        FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && IGtQ[n,0] && IGtQ[p,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (e__ + f__ * x_).pow(m_) * (c__ + d__ * x_).sech().pow(p_) * (c__ + d__ * x_).csch().pow(n_)
            / (a__ + b__ * (c__ + d__ * x_).sinh()),
        with: [e__, f__, m_, c__, d__, p_, n_, a__, b__, x_],
        optional: [e__, f__, m_, c__, d__, p_, n_, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && igtq!(m_, 0)
                && igtq!(n_, 0)
                && igtq!(p_, 0)
        },
        rhs: {
            let linear = &e__ + &f__ * x_;
            let angle = &c__ + &d__ * x_;
            let first_integrand = linear.pow(&m_) * &angle.sech().pow(&p_) * &angle.csch().pow(&n_);
            let second_integrand = linear.pow(&m_) * &angle.sech().pow(&p_) * &angle.csch().pow(&n_ - 1)
                / (&a__ + &b__ * angle.sinh());
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(Atom::num(1) / &a__, first)
                    - rubi_star(&b__ / &a__, second)
        },
    ));
}

fn push_rules_rule_6124(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6124,
        source: "Int[(e_.+f_.*x_)^m_.*Csch[c_.+d_.*x_]^p_.*Sech[c_.+d_.*x_]^n_./(a_+b_.*Cosh[c_.+d_.*x_]),x_Symbol] :=
          1/a \\[Star] Int[(e+f*x)^m*Csch[c+d*x]^p*Sech[c+d*x]^n,x] -
          b/a \\[Star] Int[(e+f*x)^m*Csch[c+d*x]^p*Sech[c+d*x]^(n-1)/(a+b*Cosh[c+d*x]),x] /;
        FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && IGtQ[n,0] && IGtQ[p,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (e__ + f__ * x_).pow(m_) * (c__ + d__ * x_).csch().pow(p_) * (c__ + d__ * x_).sech().pow(n_)
            / (a__ + b__ * (c__ + d__ * x_).cosh()),
        with: [e__, f__, m_, c__, d__, p_, n_, a__, b__, x_],
        optional: [e__, f__, m_, c__, d__, p_, n_, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && igtq!(m_, 0)
                && igtq!(n_, 0)
                && igtq!(p_, 0)
        },
        rhs: {
            let linear = &e__ + &f__ * x_;
            let angle = &c__ + &d__ * x_;
            let first_integrand = linear.pow(&m_) * &angle.csch().pow(&p_) * &angle.sech().pow(&n_);
            let second_integrand = linear.pow(&m_) * &angle.csch().pow(&p_) * &angle.sech().pow(&n_ - 1)
                / (&a__ + &b__ * angle.cosh());
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(Atom::num(1) / &a__, first)
                    - rubi_star(&b__ / &a__, second)
        },
    ));
}

fn push_rules_rule_6125(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        a__, b__, c__, d__, e__, f__, capital_f_, capital_g_, m_, n_, p_, x_
    );
    rules.push(rubi_rule!(
        order: 6125,
        source: "Int[(e_.+f_.*x_)^m_.*F_[c_.+d_.*x_]^n_.*G_[c_.+d_.*x_]^p_./(a_+b_.*Sinh[c_.+d_.*x_]),x_Symbol] :=
          Unintegrable[(e+f*x)^m*F[c+d*x]^n*G[c+d*x]^p/(a+b*Sinh[c+d*x]),x] /;
        FreeQ[{a,b,c,d,e,f,m,n,p},x] && HyperbolicQ[F] && HyperbolicQ[G]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern: (e__ + f__ * x_).pow(m_)
            * capital_f_.call(c__ + d__ * x_).pow(n_)
            * capital_g_.call(c__ + d__ * x_).pow(p_)
            / (a__ + b__ * (c__ + d__ * x_).sinh()),
        with: [e__, f__, m_, capital_f_, c__, d__, n_, capital_g_, p_, a__, b__, x_],
        optional: [e__, f__, m_, c__, d__, n_, p_, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_, p_], x_)
                && rubi_hyperbolic_head_q(&capital_f_)
                && rubi_hyperbolic_head_q(&capital_g_)
        },
        rhs: {
            let linear = &e__ + &f__ * x_;
            let angle = &c__ + &d__ * x_;
            let capital_f_ = rubi_function_head_symbol(&capital_f_).unwrap();
            let capital_g_ = rubi_function_head_symbol(&capital_g_).unwrap();
            let integrand = linear.pow(&m_)
                * capital_f_.call(&angle).pow(&n_)
                * capital_g_.call(&angle).pow(&p_)
                / (&a__ + &b__ * angle.sinh());

            rubi_unintegrable(integrand, x_)
        },
    ));
}

fn push_rules_rule_6126(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        a__, b__, c__, d__, e__, f__, capital_f_, capital_g_, m_, n_, p_, x_
    );
    rules.push(rubi_rule!(
        order: 6126,
        source: "Int[(e_.+f_.*x_)^m_.*F_[c_.+d_.*x_]^n_.*G_[c_.+d_.*x_]^p_./(a_+b_.*Cosh[c_.+d_.*x_]),x_Symbol] :=
          Unintegrable[(e+f*x)^m*F[c+d*x]^n*G[c+d*x]^p/(a+b*Cosh[c+d*x]),x] /;
        FreeQ[{a,b,c,d,e,f,m,n,p},x] && HyperbolicQ[F] && HyperbolicQ[G]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern: (e__ + f__ * x_).pow(m_)
            * capital_f_.call(c__ + d__ * x_).pow(n_)
            * capital_g_.call(c__ + d__ * x_).pow(p_)
            / (a__ + b__ * (c__ + d__ * x_).cosh()),
        with: [e__, f__, m_, capital_f_, c__, d__, n_, capital_g_, p_, a__, b__, x_],
        optional: [e__, f__, m_, c__, d__, n_, p_, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_, p_], x_)
                && rubi_hyperbolic_head_q(&capital_f_)
                && rubi_hyperbolic_head_q(&capital_g_)
        },
        rhs: {
            let linear = &e__ + &f__ * x_;
            let angle = &c__ + &d__ * x_;
            let capital_f_ = rubi_function_head_symbol(&capital_f_).unwrap();
            let capital_g_ = rubi_function_head_symbol(&capital_g_).unwrap();
            let integrand = linear.pow(&m_)
                * capital_f_.call(&angle).pow(&n_)
                * capital_g_.call(&angle).pow(&p_)
                / (&a__ + &b__ * angle.cosh());

            rubi_unintegrable(integrand, x_)
        },
    ));
}

fn push_rules_rule_6127(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, capital_f_, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 6127,
        source: "Int[(e_.+f_.*x_)^m_.*F_[c_.+d_.*x_]^n_./(a_+b_.*Sech[c_.+d_.*x_]),x_Symbol] :=
          Int[(e+f*x)^m*Cosh[c+d*x]*F[c+d*x]^n/(b+a*Cosh[c+d*x]),x] /;
        FreeQ[{a,b,c,d,e,f},x] && HyperbolicQ[F] && IntegersQ[m,n]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: (e__ + f__ * x_).pow(m_) * capital_f_.call(c__ + d__ * x_).pow(n_)
            / (a__ + b__ * (c__ + d__ * x_).sech()),
        with: [e__, f__, m_, capital_f_, c__, d__, n_, a__, b__, x_],
        optional: [e__, f__, m_, c__, d__, n_, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && rubi_hyperbolic_head_q(&capital_f_)
                && integersq!([m_, n_])
        },
        rhs: {
            let linear = &e__ + &f__ * x_;
            let angle = &c__ + &d__ * x_;
            let capital_f_ = rubi_function_head_symbol(&capital_f_).unwrap();
            let integrand = linear.pow(&m_) * &angle.cosh() * capital_f_.call(&angle).pow(&n_)
                / (&b__ + &a__ * angle.cosh());

            rubi_rhs_int(&integrand, x_)
        },
    ));
}

fn push_rules_rule_6128(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, capital_f_, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 6128,
        source: "Int[(e_.+f_.*x_)^m_.*F_[c_.+d_.*x_]^n_./(a_+b_.*Csch[c_.+d_.*x_]),x_Symbol] :=
          Int[(e+f*x)^m*Sinh[c+d*x]*F[c+d*x]^n/(b+a*Sinh[c+d*x]),x] /;
        FreeQ[{a,b,c,d,e,f},x] && HyperbolicQ[F] && IntegersQ[m,n]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: (e__ + f__ * x_).pow(m_) * capital_f_.call(c__ + d__ * x_).pow(n_)
            / (a__ + b__ * (c__ + d__ * x_).csch()),
        with: [e__, f__, m_, capital_f_, c__, d__, n_, a__, b__, x_],
        optional: [e__, f__, m_, c__, d__, n_, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && rubi_hyperbolic_head_q(&capital_f_)
                && integersq!([m_, n_])
        },
        rhs: {
            let linear = &e__ + &f__ * x_;
            let angle = &c__ + &d__ * x_;
            let capital_f_ = rubi_function_head_symbol(&capital_f_).unwrap();
            let integrand = linear.pow(&m_) * &angle.sinh() * capital_f_.call(&angle).pow(&n_)
                / (&b__ + &a__ * angle.sinh());

            rubi_rhs_int(&integrand, x_)
        },
    ));
}

fn push_rules_rule_6129(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        a__, b__, c__, d__, e__, f__, capital_f_, capital_g_, m_, n_, p_, x_
    );
    rules.push(rubi_rule!(
        order: 6129,
        source: "Int[(e_.+f_.*x_)^m_.*F_[c_.+d_.*x_]^n_.*G_[c_.+d_.*x_]^p_./(a_+b_.*Sech[c_.+d_.*x_]),x_Symbol] :=
          Int[(e+f*x)^m*Cosh[c+d*x]*F[c+d*x]^n*G[c+d*x]^p/(b+a*Cosh[c+d*x]),x] /;
        FreeQ[{a,b,c,d,e,f},x] && HyperbolicQ[F] && HyperbolicQ[G] && IntegersQ[m,n,p]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: (e__ + f__ * x_).pow(m_)
            * capital_f_.call(c__ + d__ * x_).pow(n_)
            * capital_g_.call(c__ + d__ * x_).pow(p_)
            / (a__ + b__ * (c__ + d__ * x_).sech()),
        with: [e__, f__, m_, capital_f_, c__, d__, n_, capital_g_, p_, a__, b__, x_],
        optional: [e__, f__, m_, c__, d__, n_, p_, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && rubi_hyperbolic_head_q(&capital_f_)
                && rubi_hyperbolic_head_q(&capital_g_)
                && integersq!([m_, n_, p_])
        },
        rhs: {
            let linear = &e__ + &f__ * x_;
            let angle = &c__ + &d__ * x_;
            let capital_f_ = rubi_function_head_symbol(&capital_f_).unwrap();
            let capital_g_ = rubi_function_head_symbol(&capital_g_).unwrap();
            let integrand = linear.pow(&m_)
                * &angle.cosh()
                * capital_f_.call(&angle).pow(&n_)
                * capital_g_.call(&angle).pow(&p_)
                / (&b__ + &a__ * angle.cosh());

            rubi_rhs_int(&integrand, x_)
        },
    ));
}

fn push_rules_rule_6130(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        a__, b__, c__, d__, e__, f__, capital_f_, capital_g_, m_, n_, p_, x_
    );
    rules.push(rubi_rule!(
        order: 6130,
        source: "Int[(e_.+f_.*x_)^m_.*F_[c_.+d_.*x_]^n_.*G_[c_.+d_.*x_]^p_./(a_+b_.*Csch[c_.+d_.*x_]),x_Symbol] :=
          Int[(e+f*x)^m*Sinh[c+d*x]*F[c+d*x]^n*G[c+d*x]^p/(b+a*Sinh[c+d*x]),x] /;
        FreeQ[{a,b,c,d,e,f},x] && HyperbolicQ[F] && HyperbolicQ[G] && IntegersQ[m,n,p]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: (e__ + f__ * x_).pow(m_)
            * capital_f_.call(c__ + d__ * x_).pow(n_)
            * capital_g_.call(c__ + d__ * x_).pow(p_)
            / (a__ + b__ * (c__ + d__ * x_).csch()),
        with: [e__, f__, m_, capital_f_, c__, d__, n_, capital_g_, p_, a__, b__, x_],
        optional: [e__, f__, m_, c__, d__, n_, p_, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && rubi_hyperbolic_head_q(&capital_f_)
                && rubi_hyperbolic_head_q(&capital_g_)
                && integersq!([m_, n_, p_])
        },
        rhs: {
            let linear = &e__ + &f__ * x_;
            let angle = &c__ + &d__ * x_;
            let capital_f_ = rubi_function_head_symbol(&capital_f_).unwrap();
            let capital_g_ = rubi_function_head_symbol(&capital_g_).unwrap();
            let integrand = linear.pow(&m_)
                * &angle.sinh()
                * capital_f_.call(&angle).pow(&n_)
                * capital_g_.call(&angle).pow(&p_)
                / (&b__ + &a__ * angle.sinh());

            rubi_rhs_int(&integrand, x_)
        },
    ));
}

fn push_rules_rule_6131(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 6131,
        source: "Int[Sinh[a_.+b_.*x_]^p_.*Sinh[c_.+d_.*x_]^q_.,x_Symbol] :=
          1/2^(p+q) \\[Star] Int[ExpandIntegrand[(-E^(-c-d*x)+E^(c+d*x))^q,(-E^(-a-b*x)+E^(a+b*x))^p,x],x] /;
        FreeQ[{a,b,c,d,q},x] && IGtQ[p,0] && Not[IntegerQ[q]]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (a__ + b__ * x_).sinh().pow(p_) * (c__ + d__ * x_).sinh().pow(q_),
        with: [a__, b__, p_, c__, d__, q_, x_],
        optional: [a__, b__, p_, c__, d__, q_],
        when: {
            freeq!([a__, b__, c__, d__, q_], x_)
                && igtq!(p_, 0)
                && !integerq!(q_)
        },
        rhs: {
            let first_angle = &a__ + &b__ * x_;
            let second_angle = &c__ + &d__ * x_;
            let first = (-(-&second_angle).exp() + second_angle.exp()).pow(&q_);
            let second = (-(-&first_angle).exp() + first_angle.exp()).pow(&p_);
            let expanded = rubi_expand_integrand(&(first * second), x_);
            let recursive = rubi_rhs_int(&expanded, x_);

            rubi_star(Atom::num(1) / Atom::num(2).pow(&p_ + &q_), recursive)
        },
    ));
}

fn push_rules_rule_6132(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 6132,
        source: "Int[Cosh[a_.+b_.*x_]^p_.*Cosh[c_.+d_.*x_]^q_.,x_Symbol] :=
          1/2^(p+q) \\[Star] Int[ExpandIntegrand[(E^(-c-d*x)+E^(c+d*x))^q,(E^(-a-b*x)+E^(a+b*x))^p,x],x] /;
        FreeQ[{a,b,c,d,q},x] && IGtQ[p,0] && Not[IntegerQ[q]]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (a__ + b__ * x_).cosh().pow(p_) * (c__ + d__ * x_).cosh().pow(q_),
        with: [a__, b__, p_, c__, d__, q_, x_],
        optional: [a__, b__, p_, c__, d__, q_],
        when: {
            freeq!([a__, b__, c__, d__, q_], x_)
                && igtq!(p_, 0)
                && !integerq!(q_)
        },
        rhs: {
            let first_angle = &a__ + &b__ * x_;
            let second_angle = &c__ + &d__ * x_;
            let first = ((-&second_angle).exp() + second_angle.exp()).pow(&q_);
            let second = ((-&first_angle).exp() + first_angle.exp()).pow(&p_);
            let expanded = rubi_expand_integrand(&(first * second), x_);
            let recursive = rubi_rhs_int(&expanded, x_);

            rubi_star(Atom::num(1) / Atom::num(2).pow(&p_ + &q_), recursive)
        },
    ));
}

fn push_rules_rule_6133(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 6133,
        source: "Int[Sinh[a_.+b_.*x_]^p_.*Cosh[c_.+d_.*x_]^q_.,x_Symbol] :=
          1/2^(p+q) \\[Star] Int[ExpandIntegrand[(E^(-c-d*x)+E^(c+d*x))^q,(-E^(-a-b*x)+E^(a+b*x))^p,x],x] /;
        FreeQ[{a,b,c,d,q},x] && IGtQ[p,0] && Not[IntegerQ[q]]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (a__ + b__ * x_).sinh().pow(p_) * (c__ + d__ * x_).cosh().pow(q_),
        with: [a__, b__, p_, c__, d__, q_, x_],
        optional: [a__, b__, p_, c__, d__, q_],
        when: {
            freeq!([a__, b__, c__, d__, q_], x_)
                && igtq!(p_, 0)
                && !integerq!(q_)
        },
        rhs: {
            let first_angle = &a__ + &b__ * x_;
            let second_angle = &c__ + &d__ * x_;
            let first = ((-&second_angle).exp() + second_angle.exp()).pow(&q_);
            let second = (-(-&first_angle).exp() + first_angle.exp()).pow(&p_);
            let expanded = rubi_expand_integrand(&(first * second), x_);
            let recursive = rubi_rhs_int(&expanded, x_);

            rubi_star(Atom::num(1) / Atom::num(2).pow(&p_ + &q_), recursive)
        },
    ));
}

fn push_rules_rule_6134(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 6134,
        source: "Int[Cosh[a_.+b_.*x_]^p_.*Sinh[c_.+d_.*x_]^q_.,x_Symbol] :=
          1/2^(p+q) \\[Star] Int[ExpandIntegrand[(-E^(-c-d*x)+E^(c+d*x))^q,(E^(-a-b*x)+E^(a+b*x))^p,x],x] /;
        FreeQ[{a,b,c,d,q},x] && IGtQ[p,0] && Not[IntegerQ[q]]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (a__ + b__ * x_).cosh().pow(p_) * (c__ + d__ * x_).sinh().pow(q_),
        with: [a__, b__, p_, c__, d__, q_, x_],
        optional: [a__, b__, p_, c__, d__, q_],
        when: {
            freeq!([a__, b__, c__, d__, q_], x_)
                && igtq!(p_, 0)
                && !integerq!(q_)
        },
        rhs: {
            let first_angle = &a__ + &b__ * x_;
            let second_angle = &c__ + &d__ * x_;
            let first = (-(-&second_angle).exp() + second_angle.exp()).pow(&q_);
            let second = ((-&first_angle).exp() + first_angle.exp()).pow(&p_);
            let expanded = rubi_expand_integrand(&(first * second), x_);
            let recursive = rubi_rhs_int(&expanded, x_);

            rubi_star(Atom::num(1) / Atom::num(2).pow(&p_ + &q_), recursive)
        },
    ));
}

fn push_rules_rule_6135(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 6135,
        source: "Int[Sinh[a_.+b_.*x_]*Tanh[c_.+d_.*x_],x_Symbol] :=
          Int[-E^(-(a+b*x))/2 + E^(a+b*x)/2 + E^(-(a+b*x))/(1+E^(2*(c+d*x))) - E^(a+b*x)/(1+E^(2*(c+d*x))),x] /;
        FreeQ[{a,b,c,d},x] && NeQ[b^2-d^2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (a__ + b__ * x_).sinh() * (c__ + d__ * x_).tanh(),
        with: [a__, b__, c__, d__, x_],
        optional: [a__, b__, c__, d__],
        when: { freeq!([a__, b__, c__, d__], x_) && neq!(b__.pow(2) - d__.pow(2), 0) },
        rhs: {
            let first_angle = &a__ + &b__ * x_;
            let second_angle = &c__ + &d__ * x_;
            let integrand = -(-&first_angle).exp() / 2
                + first_angle.exp() / 2
                + (-&first_angle).exp() / (Atom::num(1) + (Atom::num(2) * &second_angle).exp())
                - first_angle.exp() / (Atom::num(1) + (Atom::num(2) * second_angle).exp());

            rubi_rhs_int(&integrand, x_)
        },
    ));
}

fn push_rules_rule_6136(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 6136,
        source: "Int[Cosh[a_.+b_.*x_]*Coth[c_.+d_.*x_],x_Symbol] :=
          Int[E^(-(a+b*x))/2 + E^(a+b*x)/2 - E^(-(a+b*x))/(1-E^(2*(c+d*x))) - E^(a+b*x)/(1-E^(2*(c+d*x))),x] /;
        FreeQ[{a,b,c,d},x] && NeQ[b^2-d^2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (a__ + b__ * x_).cosh() * (c__ + d__ * x_).coth(),
        with: [a__, b__, c__, d__, x_],
        optional: [a__, b__, c__, d__],
        when: { freeq!([a__, b__, c__, d__], x_) && neq!(b__.pow(2) - d__.pow(2), 0) },
        rhs: {
            let first_angle = &a__ + &b__ * x_;
            let second_angle = &c__ + &d__ * x_;
            let integrand = (-&first_angle).exp() / 2
                + first_angle.exp() / 2
                - (-&first_angle).exp() / (Atom::num(1) - (Atom::num(2) * &second_angle).exp())
                - first_angle.exp() / (Atom::num(1) - (Atom::num(2) * second_angle).exp());

            rubi_rhs_int(&integrand, x_)
        },
    ));
}

fn push_rules_rule_6137(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 6137,
        source: "Int[Sinh[a_.+b_.*x_]*Coth[c_.+d_.*x_],x_Symbol] :=
          Int[-E^(-(a+b*x))/2 + E^(a+b*x)/2 + E^(-(a+b*x))/(1-E^(2*(c+d*x))) - E^(a+b*x)/(1-E^(2*(c+d*x))),x] /;
        FreeQ[{a,b,c,d},x] && NeQ[b^2-d^2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (a__ + b__ * x_).sinh() * (c__ + d__ * x_).coth(),
        with: [a__, b__, c__, d__, x_],
        optional: [a__, b__, c__, d__],
        when: { freeq!([a__, b__, c__, d__], x_) && neq!(b__.pow(2) - d__.pow(2), 0) },
        rhs: {
            let first_angle = &a__ + &b__ * x_;
            let second_angle = &c__ + &d__ * x_;
            let integrand = -(-&first_angle).exp() / 2
                + first_angle.exp() / 2
                + (-&first_angle).exp() / (Atom::num(1) - (Atom::num(2) * &second_angle).exp())
                - first_angle.exp() / (Atom::num(1) - (Atom::num(2) * second_angle).exp());

            rubi_rhs_int(&integrand, x_)
        },
    ));
}

fn push_rules_rule_6138(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 6138,
        source: "Int[Cosh[a_.+b_.*x_]*Tanh[c_.+d_.*x_],x_Symbol] :=
          Int[E^(-(a+b*x))/2 + E^(a+b*x)/2 - E^(-(a+b*x))/(1+E^(2*(c+d*x))) - E^(a+b*x)/(1+E^(2*(c+d*x))),x] /;
        FreeQ[{a,b,c,d},x] && NeQ[b^2-d^2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (a__ + b__ * x_).cosh() * (c__ + d__ * x_).tanh(),
        with: [a__, b__, c__, d__, x_],
        optional: [a__, b__, c__, d__],
        when: { freeq!([a__, b__, c__, d__], x_) && neq!(b__.pow(2) - d__.pow(2), 0) },
        rhs: {
            let first_angle = &a__ + &b__ * x_;
            let second_angle = &c__ + &d__ * x_;
            let integrand = (-&first_angle).exp() / 2
                + first_angle.exp() / 2
                - (-&first_angle).exp() / (Atom::num(1) + (Atom::num(2) * &second_angle).exp())
                - first_angle.exp() / (Atom::num(1) + (Atom::num(2) * second_angle).exp());

            rubi_rhs_int(&integrand, x_)
        },
    ));
}

fn push_rules_rule_6139(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, c__, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 6139,
        source: "Int[Sinh[a_./(c_.+d_.*x_)]^n_.,x_Symbol] :=
          -1/d \\[Star] Subst[Int[Sinh[a*x]^n/x^2,x],x,1/(c+d*x)] /;
        FreeQ[{a,c,d},x] && IGtQ[n,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (a__ / (c__ + d__ * x_)).sinh().pow(n_),
        with: [a__, c__, d__, n_, x_],
        optional: [a__, c__, d__, n_],
        when: { freeq!([a__, c__, d__], x_) && igtq!(n_, 0) },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub = Atom::var(substitution_symbol);
            let transformed_integrand = (&a__ * &sub).sinh().pow(&n_) / sub.pow(2);
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);
            let base = Atom::num(1) / (&c__ + &d__ * x_);

            let substituted = rubi_subst(&transformed, substitution_symbol, base);
            rubi_star(-Atom::num(1) / &d__, substituted)
        },
    ));
}

fn push_rules_rule_6140(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, c__, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 6140,
        source: "Int[Cosh[a_./(c_.+d_.*x_)]^n_.,x_Symbol] :=
          -1/d \\[Star] Subst[Int[Cosh[a*x]^n/x^2,x],x,1/(c+d*x)] /;
        FreeQ[{a,c,d},x] && IGtQ[n,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (a__ / (c__ + d__ * x_)).cosh().pow(n_),
        with: [a__, c__, d__, n_, x_],
        optional: [a__, c__, d__, n_],
        when: { freeq!([a__, c__, d__], x_) && igtq!(n_, 0) },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub = Atom::var(substitution_symbol);
            let transformed_integrand = (&a__ * &sub).cosh().pow(&n_) / sub.pow(2);
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);
            let base = Atom::num(1) / (&c__ + &d__ * x_);

            let substituted = rubi_subst(&transformed, substitution_symbol, base);
            rubi_star(-Atom::num(1) / &d__, substituted)
        },
    ));
}

fn push_rules_rule_6141(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 6141,
        source: "Int[Sinh[e_.*(a_.+b_.*x_)/(c_.+d_.*x_)]^n_.,x_Symbol] :=
          -1/d \\[Star] Subst[Int[Sinh[b*e/d-e*(b*c-a*d)*x/d]^n/x^2,x],x,1/(c+d*x)] /;
        FreeQ[{a,b,c,d},x] && IGtQ[n,0] && NeQ[b*c-a*d,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (e__ * (a__ + b__ * x_) / (c__ + d__ * x_)).sinh().pow(n_),
        with: [e__, a__, b__, c__, d__, n_, x_],
        optional: [e__, a__, b__, c__, d__, n_],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && igtq!(n_, 0)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub = Atom::var(substitution_symbol);
            let argument = &b__ * &e__ / &d__ - &e__ * (&b__ * &c__ - &a__ * &d__) * &sub / &d__;
            let transformed_integrand = argument.sinh().pow(&n_) / sub.pow(2);
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);
            let base = Atom::num(1) / (&c__ + &d__ * x_);

            let substituted = rubi_subst(&transformed, substitution_symbol, base);
            rubi_star(-Atom::num(1) / &d__, substituted)
        },
    ));
}

fn push_rules_rule_6142(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 6142,
        source: "Int[Cosh[e_.*(a_.+b_.*x_)/(c_.+d_.*x_)]^n_.,x_Symbol] :=
          -1/d \\[Star] Subst[Int[Cosh[b*e/d-e*(b*c-a*d)*x/d]^n/x^2,x],x,1/(c+d*x)] /;
        FreeQ[{a,b,c,d},x] && IGtQ[n,0] && NeQ[b*c-a*d,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (e__ * (a__ + b__ * x_) / (c__ + d__ * x_)).cosh().pow(n_),
        with: [e__, a__, b__, c__, d__, n_, x_],
        optional: [e__, a__, b__, c__, d__, n_],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && igtq!(n_, 0)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub = Atom::var(substitution_symbol);
            let argument = &b__ * &e__ / &d__ - &e__ * (&b__ * &c__ - &a__ * &d__) * &sub / &d__;
            let transformed_integrand = argument.cosh().pow(&n_) / sub.pow(2);
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);
            let base = Atom::num(1) / (&c__ + &d__ * x_);

            let substituted = rubi_subst(&transformed, substitution_symbol, base);
            rubi_star(-Atom::num(1) / &d__, substituted)
        },
    ));
}

fn push_rules_rule_6143(rules: &mut Vec<RubiRule>) {
    rubi_symb!(n_, u__);
    rules.push(rubi_rule!(
        order: 6143,
        source: "Int[Sinh[u_]^n_.,x_Symbol] :=
          With[{lst=QuotientOfLinearsParts[u,x]},
          Int[Sinh[(lst[[1]]+lst[[2]]*x)/(lst[[3]]+lst[[4]]*x)]^n,x]] /;
        IGtQ[n,0] && QuotientOfLinearsQ[u,x]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: Atom::var(u__).sinh().pow(n_),
        with: [u__, n_, x_],
        optional: [n_],
        when: { igtq!(n_, 0) && rubi_quotient_of_linears_coefficients(&u__, x_).is_some() },
        rhs: {
            let (a, b, c, d) = rubi_quotient_of_linears_coefficients(&u__, x_).rubi_rhs();
            let integrand = ((a + b * x_) / (c + d * x_)).sinh().pow(&n_);

            rubi_rhs_int(&integrand, x_)
        },
    ));
}

fn push_rules_rule_6144(rules: &mut Vec<RubiRule>) {
    rubi_symb!(n_, u__);
    rules.push(rubi_rule!(
        order: 6144,
        source: "Int[Cosh[u_]^n_.,x_Symbol] :=
          With[{lst=QuotientOfLinearsParts[u,x]},
          Int[Cosh[(lst[[1]]+lst[[2]]*x)/(lst[[3]]+lst[[4]]*x)]^n,x]] /;
        IGtQ[n,0] && QuotientOfLinearsQ[u,x]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: Atom::var(u__).cosh().pow(n_),
        with: [u__, n_, x_],
        optional: [n_],
        when: { igtq!(n_, 0) && rubi_quotient_of_linears_coefficients(&u__, x_).is_some() },
        rhs: {
            let (a, b, c, d) = rubi_quotient_of_linears_coefficients(&u__, x_).rubi_rhs();
            let integrand = ((a + b * x_) / (c + d * x_)).cosh().pow(&n_);

            rubi_rhs_int(&integrand, x_)
        },
    ));
}

fn push_rules_rule_6145(rules: &mut Vec<RubiRule>) {
    rubi_symb!(p_, q_, u__, v_, w_);
    rules.push(rubi_rule!(
        order: 6145,
        source: "Int[u_.*Sinh[v_]^p_.*Sinh[w_]^q_.,x_Symbol] :=
          Int[u*Sinh[v]^(p+q),x] /;
        EqQ[w,v]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: u__ * Atom::var(v_).sinh().pow(p_) * Atom::var(w_).sinh().pow(q_),
        with: [u__, v_, p_, w_, q_, x_],
        optional: [u__, p_, q_],
        when: { eqq!(w_, v_) },
        rhs: {
            let integrand = &u__ * v_.sinh().pow(&p_ + &q_);

            rubi_rhs_int(&integrand, x_)
        },
    ));
}

fn push_rules_rule_6146(rules: &mut Vec<RubiRule>) {
    rubi_symb!(p_, q_, u__, v_, w_);
    rules.push(rubi_rule!(
        order: 6146,
        source: "Int[u_.*Cosh[v_]^p_.*Cosh[w_]^q_.,x_Symbol] :=
          Int[u*Cosh[v]^(p+q),x] /;
        EqQ[w,v]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: u__ * Atom::var(v_).cosh().pow(p_) * Atom::var(w_).cosh().pow(q_),
        with: [u__, v_, p_, w_, q_, x_],
        optional: [u__, p_, q_],
        when: { eqq!(w_, v_) },
        rhs: {
            let integrand = &u__ * v_.cosh().pow(&p_ + &q_);

            rubi_rhs_int(&integrand, x_)
        },
    ));
}

fn push_rules_rule_6147(rules: &mut Vec<RubiRule>) {
    rubi_symb!(p_, q_, v_, w_);
    rules.push(rubi_rule!(
        order: 6147,
        source: "Int[Sinh[v_]^p_.*Sinh[w_]^q_.,x_Symbol] :=
          Int[ExpandTrigReduce[Sinh[v]^p*Sinh[w]^q,x],x] /;
        IGtQ[p,0] && IGtQ[q,0] && (PolynomialQ[v,x] && PolynomialQ[w,x] || BinomialQ[{v,w},x] && IndependentQ[Cancel[v/w],x])",
        desc: "Algebraic expansion",
        refs: [],
        pattern: Atom::var(v_).sinh().pow(p_) * Atom::var(w_).sinh().pow(q_),
        with: [v_, p_, w_, q_, x_],
        optional: [p_, q_],
        when: {
            let cancelled = rubi_cancel(&(&v_ / &w_));
            igtq!(p_, 0)
                && igtq!(q_, 0)
                && ((rubi_polynomial_q(&v_, x_) && rubi_polynomial_q(&w_, x_))
                    || (rubi_binomial_q_list(&[&v_, &w_], x_)
                        && rubi_independent_q(&cancelled, x_)))
        },
        rhs: {
            let product = v_.sinh().pow(&p_) * w_.sinh().pow(&q_);
            let expanded = rubi_expand_trig_reduce(&Atom::num(1), &product, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_6148(rules: &mut Vec<RubiRule>) {
    rubi_symb!(p_, q_, v_, w_);
    rules.push(rubi_rule!(
        order: 6148,
        source: "Int[Cosh[v_]^p_.*Cosh[w_]^q_.,x_Symbol] :=
          Int[ExpandTrigReduce[Cosh[v]^p*Cosh[w]^q,x],x] /;
        IGtQ[p,0] && IGtQ[q,0] && (PolynomialQ[v,x] && PolynomialQ[w,x] || BinomialQ[{v,w},x] && IndependentQ[Cancel[v/w],x])",
        desc: "Algebraic expansion",
        refs: [],
        pattern: Atom::var(v_).cosh().pow(p_) * Atom::var(w_).cosh().pow(q_),
        with: [v_, p_, w_, q_, x_],
        optional: [p_, q_],
        when: {
            let cancelled = rubi_cancel(&(&v_ / &w_));
            igtq!(p_, 0)
                && igtq!(q_, 0)
                && ((rubi_polynomial_q(&v_, x_) && rubi_polynomial_q(&w_, x_))
                    || (rubi_binomial_q_list(&[&v_, &w_], x_)
                        && rubi_independent_q(&cancelled, x_)))
        },
        rhs: {
            let product = v_.cosh().pow(&p_) * w_.cosh().pow(&q_);
            let expanded = rubi_expand_trig_reduce(&Atom::num(1), &product, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_6149(rules: &mut Vec<RubiRule>) {
    rubi_symb!(m_, p_, q_, v_, w_, x_);
    rules.push(rubi_rule!(
        order: 6149,
        source: "Int[x_^m_.*Sinh[v_]^p_.*Sinh[w_]^q_.,x_Symbol] :=
          Int[ExpandTrigReduce[x^m,Sinh[v]^p*Sinh[w]^q,x],x] /;
        IGtQ[m,0] && IGtQ[p,0] && IGtQ[q,0] && (PolynomialQ[v,x] && PolynomialQ[w,x] || BinomialQ[{v,w},x] && IndependentQ[Cancel[v/w],x])",
        desc: "Algebraic expansion",
        refs: [],
        pattern: x_.pow(m_) * Atom::var(v_).sinh().pow(p_) * Atom::var(w_).sinh().pow(q_),
        with: [m_, v_, p_, w_, q_, x_],
        optional: [m_, p_, q_],
        when: {
            let cancelled = rubi_cancel(&(&v_ / &w_));
            igtq!(m_, 0)
                && igtq!(p_, 0)
                && igtq!(q_, 0)
                && ((rubi_polynomial_q(&v_, x_) && rubi_polynomial_q(&w_, x_))
                    || (rubi_binomial_q_list(&[&v_, &w_], x_)
                        && rubi_independent_q(&cancelled, x_)))
        },
        rhs: {
            let product = v_.sinh().pow(&p_) * w_.sinh().pow(&q_);
            let expanded = rubi_expand_trig_reduce(x_.pow(&m_), &product, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_6150(rules: &mut Vec<RubiRule>) {
    rubi_symb!(m_, p_, q_, v_, w_, x_);
    rules.push(rubi_rule!(
        order: 6150,
        source: "Int[x_^m_.*Cosh[v_]^p_.*Cosh[w_]^q_.,x_Symbol] :=
          Int[ExpandTrigReduce[x^m,Cosh[v]^p*Cosh[w]^q,x],x] /;
        IGtQ[m,0] && IGtQ[p,0] && IGtQ[q,0] && (PolynomialQ[v,x] && PolynomialQ[w,x] || BinomialQ[{v,w},x] && IndependentQ[Cancel[v/w],x])",
        desc: "Algebraic expansion",
        refs: [],
        pattern: x_.pow(m_) * Atom::var(v_).cosh().pow(p_) * Atom::var(w_).cosh().pow(q_),
        with: [m_, v_, p_, w_, q_, x_],
        optional: [m_, p_, q_],
        when: {
            let cancelled = rubi_cancel(&(&v_ / &w_));
            igtq!(m_, 0)
                && igtq!(p_, 0)
                && igtq!(q_, 0)
                && ((rubi_polynomial_q(&v_, x_) && rubi_polynomial_q(&w_, x_))
                    || (rubi_binomial_q_list(&[&v_, &w_], x_)
                        && rubi_independent_q(&cancelled, x_)))
        },
        rhs: {
            let product = v_.cosh().pow(&p_) * w_.cosh().pow(&q_);
            let expanded = rubi_expand_trig_reduce(x_.pow(&m_), &product, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_6151(rules: &mut Vec<RubiRule>) {
    rubi_symb!(p_, u__, v_, w_);
    rules.push(rubi_rule!(
        order: 6151,
        source: "Int[u_.*Sinh[v_]^p_.*Cosh[w_]^p_.,x_Symbol] :=
          1/2^p \\[Star] Int[u*Sinh[2*v]^p,x] /;
        EqQ[w,v] && IntegerQ[p]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: u__ * Atom::var(v_).sinh().pow(p_) * Atom::var(w_).cosh().pow(p_),
        with: [u__, v_, p_, w_, x_],
        optional: [u__, p_],
        when: { eqq!(w_, v_) && integerq!(p_) },
        rhs: {
            let integrand = &u__ * (Atom::num(2) * &v_).sinh().pow(&p_);
            let recursive = rubi_rhs_int(&integrand, x_);

            rubi_star(Atom::num(1) / Atom::num(2).pow(&p_), recursive)
        },
    ));
}

fn push_rules_rule_6152(rules: &mut Vec<RubiRule>) {
    rubi_symb!(p_, q_, v_, w_);
    rules.push(rubi_rule!(
        order: 6152,
        source: "Int[Sinh[v_]^p_.*Cosh[w_]^q_.,x_Symbol] :=
          Int[ExpandTrigReduce[Sinh[v]^p*Cosh[w]^q,x],x] /;
        IGtQ[p,0] && IGtQ[q,0] && (PolynomialQ[v,x] && PolynomialQ[w,x] || BinomialQ[{v,w},x] && IndependentQ[Cancel[v/w],x])",
        desc: "Algebraic expansion",
        refs: [],
        pattern: Atom::var(v_).sinh().pow(p_) * Atom::var(w_).cosh().pow(q_),
        with: [v_, p_, w_, q_, x_],
        optional: [p_, q_],
        when: {
            let cancelled = rubi_cancel(&(&v_ / &w_));
            igtq!(p_, 0)
                && igtq!(q_, 0)
                && ((rubi_polynomial_q(&v_, x_) && rubi_polynomial_q(&w_, x_))
                    || (rubi_binomial_q_list(&[&v_, &w_], x_)
                        && rubi_independent_q(&cancelled, x_)))
        },
        rhs: {
            let product = v_.sinh().pow(&p_) * w_.cosh().pow(&q_);
            let expanded = rubi_expand_trig_reduce(&Atom::num(1), &product, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_6153(rules: &mut Vec<RubiRule>) {
    rubi_symb!(m_, p_, q_, v_, w_, x_);
    rules.push(rubi_rule!(
        order: 6153,
        source: "Int[x_^m_.*Sinh[v_]^p_.*Cosh[w_]^q_.,x_Symbol] :=
          Int[ExpandTrigReduce[x^m,Sinh[v]^p*Cosh[w]^q,x],x] /;
        IGtQ[m,0] && IGtQ[p,0] && IGtQ[q,0] && (PolynomialQ[v,x] && PolynomialQ[w,x] || BinomialQ[{v,w},x] && IndependentQ[Cancel[v/w],x])",
        desc: "Algebraic expansion",
        refs: [],
        pattern: x_.pow(m_) * Atom::var(v_).sinh().pow(p_) * Atom::var(w_).cosh().pow(q_),
        with: [m_, v_, p_, w_, q_, x_],
        optional: [m_, p_, q_],
        when: {
            let cancelled = rubi_cancel(&(&v_ / &w_));
            igtq!(m_, 0)
                && igtq!(p_, 0)
                && igtq!(q_, 0)
                && ((rubi_polynomial_q(&v_, x_) && rubi_polynomial_q(&w_, x_))
                    || (rubi_binomial_q_list(&[&v_, &w_], x_)
                        && rubi_independent_q(&cancelled, x_)))
        },
        rhs: {
            let product = v_.sinh().pow(&p_) * w_.cosh().pow(&q_);
            let expanded = rubi_expand_trig_reduce(x_.pow(&m_), &product, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_6154(rules: &mut Vec<RubiRule>) {
    rubi_symb!(n_, v_, w_);
    rules.push(rubi_rule!(
        order: 6154,
        source: "Int[Sinh[v_]*Tanh[w_]^n_.,x_Symbol] :=
          Int[Cosh[v]*Tanh[w]^(n-1),x] - Cosh[v-w] \\[Star] Int[Sech[w]*Tanh[w]^(n-1),x] /;
        GtQ[n,0] && NeQ[w,v] && FreeQ[v-w,x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: Atom::var(v_).sinh() * Atom::var(w_).tanh().pow(n_),
        with: [v_, w_, n_, x_],
        optional: [n_],
        when: { gtq!(n_, 0) && neq!(w_, v_) && rubi_evaluated_free_q(&v_ - &w_, x_) },
        rhs: {
            let first = rubi_rhs_int(&(v_.cosh() * w_.tanh().pow(&n_ - 1)), x_);
            let second = rubi_rhs_int(&(w_.sech() * w_.tanh().pow(&n_ - 1)), x_);

            first - rubi_star((&v_ - &w_).cosh(), second)
        },
    ));
}

fn push_rules_rule_6155(rules: &mut Vec<RubiRule>) {
    rubi_symb!(n_, v_, w_);
    rules.push(rubi_rule!(
        order: 6155,
        source: "Int[Cosh[v_]*Coth[w_]^n_.,x_Symbol] :=
          Int[Sinh[v]*Coth[w]^(n-1),x] + Cosh[v-w] \\[Star] Int[Csch[w]*Coth[w]^(n-1),x] /;
        GtQ[n,0] && NeQ[w,v] && FreeQ[v-w,x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: Atom::var(v_).cosh() * Atom::var(w_).coth().pow(n_),
        with: [v_, w_, n_, x_],
        optional: [n_],
        when: { gtq!(n_, 0) && neq!(w_, v_) && rubi_evaluated_free_q(&v_ - &w_, x_) },
        rhs: {
            let first = rubi_rhs_int(&(v_.sinh() * w_.coth().pow(&n_ - 1)), x_);
            let second = rubi_rhs_int(&(w_.csch() * w_.coth().pow(&n_ - 1)), x_);

            first + rubi_star((&v_ - &w_).cosh(), second)
        },
    ));
}

fn push_rules_rule_6156(rules: &mut Vec<RubiRule>) {
    rubi_symb!(n_, v_, w_);
    rules.push(rubi_rule!(
        order: 6156,
        source: "Int[Sinh[v_]*Coth[w_]^n_.,x_Symbol] :=
          Int[Cosh[v]*Coth[w]^(n-1),x] + Sinh[v-w] \\[Star] Int[Csch[w]*Coth[w]^(n-1),x] /;
        GtQ[n,0] && NeQ[w,v] && FreeQ[v-w,x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: Atom::var(v_).sinh() * Atom::var(w_).coth().pow(n_),
        with: [v_, w_, n_, x_],
        optional: [n_],
        when: { gtq!(n_, 0) && neq!(w_, v_) && rubi_evaluated_free_q(&v_ - &w_, x_) },
        rhs: {
            let first = rubi_rhs_int(&(v_.cosh() * w_.coth().pow(&n_ - 1)), x_);
            let second = rubi_rhs_int(&(w_.csch() * w_.coth().pow(&n_ - 1)), x_);

            first + rubi_star((&v_ - &w_).sinh(), second)
        },
    ));
}

fn push_rules_rule_6157(rules: &mut Vec<RubiRule>) {
    rubi_symb!(n_, v_, w_);
    rules.push(rubi_rule!(
        order: 6157,
        source: "Int[Cosh[v_]*Tanh[w_]^n_.,x_Symbol] :=
          Int[Sinh[v]*Tanh[w]^(n-1),x] - Sinh[v-w] \\[Star] Int[Sech[w]*Tanh[w]^(n-1),x] /;
        GtQ[n,0] && NeQ[w,v] && FreeQ[v-w,x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: Atom::var(v_).cosh() * Atom::var(w_).tanh().pow(n_),
        with: [v_, w_, n_, x_],
        optional: [n_],
        when: { gtq!(n_, 0) && neq!(w_, v_) && rubi_evaluated_free_q(&v_ - &w_, x_) },
        rhs: {
            let first = rubi_rhs_int(&(v_.sinh() * w_.tanh().pow(&n_ - 1)), x_);
            let second = rubi_rhs_int(&(w_.sech() * w_.tanh().pow(&n_ - 1)), x_);

            first - rubi_star((&v_ - &w_).sinh(), second)
        },
    ));
}

fn push_rules_rule_6158(rules: &mut Vec<RubiRule>) {
    rubi_symb!(n_, v_, w_);
    rules.push(rubi_rule!(
        order: 6158,
        source: "Int[Sinh[v_]*Sech[w_]^n_.,x_Symbol] :=
          Cosh[v-w] \\[Star] Int[Tanh[w]*Sech[w]^(n-1),x] + Sinh[v-w] \\[Star] Int[Sech[w]^(n-1),x] /;
        GtQ[n,0] && NeQ[w,v] && FreeQ[v-w,x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: Atom::var(v_).sinh() * Atom::var(w_).sech().pow(n_),
        with: [v_, w_, n_, x_],
        optional: [n_],
        when: { gtq!(n_, 0) && neq!(w_, v_) && rubi_evaluated_free_q(&v_ - &w_, x_) },
        rhs: {
            let first = rubi_rhs_int(&(w_.tanh() * w_.sech().pow(&n_ - 1)), x_);
            let second = rubi_rhs_int(&w_.sech().pow(&n_ - 1), x_);

            rubi_star((&v_ - &w_).cosh(), first)
                    + rubi_star((&v_ - &w_).sinh(), second)
        },
    ));
}

fn push_rules_rule_6159(rules: &mut Vec<RubiRule>) {
    rubi_symb!(n_, v_, w_);
    rules.push(rubi_rule!(
        order: 6159,
        source: "Int[Cosh[v_]*Csch[w_]^n_.,x_Symbol] :=
          Cosh[v-w] \\[Star] Int[Coth[w]*Csch[w]^(n-1),x] + Sinh[v-w] \\[Star] Int[Csch[w]^(n-1),x] /;
        GtQ[n,0] && NeQ[w,v] && FreeQ[v-w,x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: Atom::var(v_).cosh() * Atom::var(w_).csch().pow(n_),
        with: [v_, w_, n_, x_],
        optional: [n_],
        when: { gtq!(n_, 0) && neq!(w_, v_) && rubi_evaluated_free_q(&v_ - &w_, x_) },
        rhs: {
            let first = rubi_rhs_int(&(w_.coth() * w_.csch().pow(&n_ - 1)), x_);
            let second = rubi_rhs_int(&w_.csch().pow(&n_ - 1), x_);

            rubi_star((&v_ - &w_).cosh(), first)
                    + rubi_star((&v_ - &w_).sinh(), second)
        },
    ));
}

fn push_rules_rule_6160(rules: &mut Vec<RubiRule>) {
    rubi_symb!(n_, v_, w_);
    rules.push(rubi_rule!(
        order: 6160,
        source: "Int[Sinh[v_]*Csch[w_]^n_.,x_Symbol] :=
          Sinh[v-w] \\[Star] Int[Coth[w]*Csch[w]^(n-1),x] + Cosh[v-w] \\[Star] Int[Csch[w]^(n-1),x] /;
        GtQ[n,0] && NeQ[w,v] && FreeQ[v-w,x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: Atom::var(v_).sinh() * Atom::var(w_).csch().pow(n_),
        with: [v_, w_, n_, x_],
        optional: [n_],
        when: { gtq!(n_, 0) && neq!(w_, v_) && rubi_evaluated_free_q(&v_ - &w_, x_) },
        rhs: {
            let first = rubi_rhs_int(&(w_.coth() * w_.csch().pow(&n_ - 1)), x_);
            let second = rubi_rhs_int(&w_.csch().pow(&n_ - 1), x_);

            rubi_star((&v_ - &w_).sinh(), first)
                    + rubi_star((&v_ - &w_).cosh(), second)
        },
    ));
}

fn push_rules_rule_6161(rules: &mut Vec<RubiRule>) {
    rubi_symb!(n_, v_, w_);
    rules.push(rubi_rule!(
        order: 6161,
        source: "Int[Cosh[v_]*Sech[w_]^n_.,x_Symbol] :=
          Sinh[v-w] \\[Star] Int[Tanh[w]*Sech[w]^(n-1),x] + Cosh[v-w] \\[Star] Int[Sech[w]^(n-1),x] /;
        GtQ[n,0] && NeQ[w,v] && FreeQ[v-w,x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: Atom::var(v_).cosh() * Atom::var(w_).sech().pow(n_),
        with: [v_, w_, n_, x_],
        optional: [n_],
        when: { gtq!(n_, 0) && neq!(w_, v_) && rubi_evaluated_free_q(&v_ - &w_, x_) },
        rhs: {
            let first = rubi_rhs_int(&(w_.tanh() * w_.sech().pow(&n_ - 1)), x_);
            let second = rubi_rhs_int(&w_.sech().pow(&n_ - 1), x_);

            rubi_star((&v_ - &w_).sinh(), first)
                    + rubi_star((&v_ - &w_).cosh(), second)
        },
    ));
}

fn push_rules_rule_6162(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 6162,
        source: "Int[(e_.+f_.*x_)^m_.*(a_+b_.*Sinh[c_.+d_.*x_]*Cosh[c_.+d_.*x_])^n_.,x_Symbol] :=
          Int[(e+f*x)^m*(a+b*Sinh[2*c+2*d*x]/2)^n,x] /;
        FreeQ[{a,b,c,d,e,f,m,n},x]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: (e__ + f__ * x_).pow(m_)
            * (a__ + b__ * (c__ + d__ * x_).sinh() * (c__ + d__ * x_).cosh()).pow(n_),
        with: [e__, f__, m_, a__, b__, c__, d__, n_, x_],
        optional: [e__, f__, m_, b__, c__, d__, n_],
        when: { freeq!([a__, b__, c__, d__, e__, f__, m_, n_], x_) },
        rhs: {
            let double_angle = Atom::num(2) * &c__ + Atom::num(2) * &d__ * x_;
            let integrand = (&e__ + &f__ * x_).pow(&m_) * (&a__ + &b__ * double_angle.sinh() / 2).pow(&n_);

            rubi_rhs_int(&integrand, x_)
        },
    ));
}

fn push_rules_rule_6163(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 6163,
        source: "Int[x_^m_.*(a_+b_.*Sinh[c_.+d_.*x_]^2)^n_,x_Symbol] :=
          1/2^n \\[Star] Int[x^m*(2*a-b+b*Cosh[2*c+2*d*x])^n,x] /;
        FreeQ[{a,b,c,d},x] && NeQ[a-b,0] && IGtQ[m,0] && ILtQ[n,0] && (EqQ[n,-1] || EqQ[m,1] && EqQ[n,-2])",
        desc: "Algebraic simplification",
        refs: [],
        pattern: x_.pow(m_) * (a__ + b__ * (c__ + d__ * x_).sinh().pow(2)).pow(n_),
        with: [m_, a__, b__, c__, d__, n_, x_],
        optional: [m_, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && neq!(&a__ - &b__, 0)
                && igtq!(m_, 0)
                && iltq!(n_, 0)
                && (eqq!(n_, -1) || eqq!(m_, 1) && eqq!(n_, -2))
        },
        rhs: {
            let double_angle = Atom::num(2) * &c__ + Atom::num(2) * &d__ * x_;
            let integrand = x_.pow(&m_) * (Atom::num(2) * &a__ - &b__ + &b__ * double_angle.cosh()).pow(&n_);
            let recursive = rubi_rhs_int(&integrand, x_);

            rubi_star(Atom::num(1) / Atom::num(2).pow(&n_), recursive)
        },
    ));
}

fn push_rules_rule_6164(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 6164,
        source: "Int[x_^m_.*(a_+b_.*Cosh[c_.+d_.*x_]^2)^n_,x_Symbol] :=
          1/2^n \\[Star] Int[x^m*(2*a+b+b*Cosh[2*c+2*d*x])^n,x] /;
        FreeQ[{a,b,c,d},x] && NeQ[a-b,0] && IGtQ[m,0] && ILtQ[n,0] && (EqQ[n,-1] || EqQ[m,1] && EqQ[n,-2])",
        desc: "Algebraic simplification",
        refs: [],
        pattern: x_.pow(m_) * (a__ + b__ * (c__ + d__ * x_).cosh().pow(2)).pow(n_),
        with: [m_, a__, b__, c__, d__, n_, x_],
        optional: [m_, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && neq!(&a__ - &b__, 0)
                && igtq!(m_, 0)
                && iltq!(n_, 0)
                && (eqq!(n_, -1) || eqq!(m_, 1) && eqq!(n_, -2))
        },
        rhs: {
            let double_angle = Atom::num(2) * &c__ + Atom::num(2) * &d__ * x_;
            let integrand = x_.pow(&m_) * (Atom::num(2) * &a__ + &b__ + &b__ * double_angle.cosh()).pow(&n_);
            let recursive = rubi_rhs_int(&integrand, x_);

            rubi_star(Atom::num(1) / Atom::num(2).pow(&n_), recursive)
        },
    ));
}

fn push_rules_rule_6165(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, m_, x_);
    rules.push(rubi_rule!(
        order: 6165,
        source: "Int[(f_.+g_.*x_)^m_./(a_.+b_.*Cosh[d_.+e_.*x_]^2+c_.*Sinh[d_.+e_.*x_]^2),x_Symbol] :=
          2 \\[Star] Int[(f+g*x)^m/(2*a+b-c+(b+c)*Cosh[2*d+2*e*x]),x] /;
        FreeQ[{a,b,c,d,e,f,g},x] && IGtQ[m,0] && NeQ[a+b,0] && NeQ[a+c,0]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: (f__ + g__ * x_).pow(m_)
            / (a__ + b__ * (d__ + e__ * x_).cosh().pow(2) + c__ * (d__ + e__ * x_).sinh().pow(2)),
        with: [f__, g__, m_, a__, b__, d__, e__, c__, x_],
        optional: [f__, g__, m_, a__, b__, d__, e__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__], x_)
                && igtq!(m_, 0)
                && neq!(&a__ + &b__, 0)
                && neq!(&a__ + &c__, 0)
        },
        rhs: {
            let double_angle = Atom::num(2) * &d__ + Atom::num(2) * &e__ * x_;
            let denominator = Atom::num(2) * &a__ + &b__ - &c__ + (&b__ + &c__) * double_angle.cosh();
            let integrand = (&f__ + &g__ * x_).pow(&m_) / denominator;
            let recursive = rubi_rhs_int(&integrand, x_);

            rubi_star(Atom::num(2), recursive)
        },
    ));
}

fn push_rules_rule_6166(rules: &mut Vec<RubiRule>) {
    rubi_symb!(b__, c__, d__, e__, f__, g__, m_, x_);
    rules.push(rubi_rule!(
        order: 6166,
        source: "Int[(f_.+g_.*x_)^m_.*Sech[d_.+e_.*x_]^2/(b_+c_.*Tanh[d_.+e_.*x_]^2),x_Symbol] :=
          2 \\[Star] Int[(f+g*x)^m/(b-c+(b+c)*Cosh[2*d+2*e*x]),x] /;
        FreeQ[{b,c,d,e,f,g},x] && IGtQ[m,0]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: (f__ + g__ * x_).pow(m_) * (d__ + e__ * x_).sech().pow(2)
            / (b__ + c__ * (d__ + e__ * x_).tanh().pow(2)),
        with: [f__, g__, m_, d__, e__, b__, c__, x_],
        optional: [f__, g__, m_, d__, e__, c__],
        when: {
            freeq!([b__, c__, d__, e__, f__, g__], x_) && igtq!(m_, 0)
        },
        rhs: {
            let double_angle = Atom::num(2) * &d__ + Atom::num(2) * &e__ * x_;
            let denominator = &b__ - &c__ + (&b__ + &c__) * double_angle.cosh();
            let integrand = (&f__ + &g__ * x_).pow(&m_) / denominator;
            let recursive = rubi_rhs_int(&integrand, x_);

            rubi_star(Atom::num(2), recursive)
        },
    ));
}

fn push_rules_rule_6167(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, m_, x_);
    rules.push(rubi_rule!(
        order: 6167,
        source: "Int[(f_.+g_.*x_)^m_.*Sech[d_.+e_.*x_]^2/(b_.+a_.*Sech[d_.+e_.*x_]^2+c_.*Tanh[d_.+e_.*x_]^2),x_Symbol] :=
          2 \\[Star] Int[(f+g*x)^m/(2*a+b-c+(b+c)*Cosh[2*d+2*e*x]),x] /;
        FreeQ[{a,b,c,d,e,f,g},x] && IGtQ[m,0] && NeQ[a+b,0] && NeQ[a+c,0]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: (f__ + g__ * x_).pow(m_) * (d__ + e__ * x_).sech().pow(2)
            / (b__ + a__ * (d__ + e__ * x_).sech().pow(2) + c__ * (d__ + e__ * x_).tanh().pow(2)),
        with: [f__, g__, m_, d__, e__, b__, a__, c__, x_],
        optional: [f__, g__, m_, d__, e__, b__, a__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__], x_)
                && igtq!(m_, 0)
                && neq!(&a__ + &b__, 0)
                && neq!(&a__ + &c__, 0)
        },
        rhs: {
            let double_angle = Atom::num(2) * &d__ + Atom::num(2) * &e__ * x_;
            let denominator = Atom::num(2) * &a__ + &b__ - &c__ + (&b__ + &c__) * double_angle.cosh();
            let integrand = (&f__ + &g__ * x_).pow(&m_) / denominator;
            let recursive = rubi_rhs_int(&integrand, x_);

            rubi_star(Atom::num(2), recursive)
        },
    ));
}

fn push_rules_rule_6168(rules: &mut Vec<RubiRule>) {
    rubi_symb!(b__, c__, d__, e__, f__, g__, m_, x_);
    rules.push(rubi_rule!(
        order: 6168,
        source: "Int[(f_.+g_.*x_)^m_.*Csch[d_.+e_.*x_]^2/(c_+b_.*Coth[d_.+e_.*x_]^2),x_Symbol] :=
          2 \\[Star] Int[(f+g*x)^m/(b-c+(b+c)*Cosh[2*d+2*e*x]),x] /;
        FreeQ[{b,c,d,e,f,g},x] && IGtQ[m,0]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: (f__ + g__ * x_).pow(m_) * (d__ + e__ * x_).csch().pow(2)
            / (c__ + b__ * (d__ + e__ * x_).coth().pow(2)),
        with: [f__, g__, m_, d__, e__, c__, b__, x_],
        optional: [f__, g__, m_, d__, e__, b__],
        when: {
            freeq!([b__, c__, d__, e__, f__, g__], x_) && igtq!(m_, 0)
        },
        rhs: {
            let double_angle = Atom::num(2) * &d__ + Atom::num(2) * &e__ * x_;
            let denominator = &b__ - &c__ + (&b__ + &c__) * double_angle.cosh();
            let integrand = (&f__ + &g__ * x_).pow(&m_) / denominator;
            let recursive = rubi_rhs_int(&integrand, x_);

            rubi_star(Atom::num(2), recursive)
        },
    ));
}

fn push_rules_rule_6169(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, m_, x_);
    rules.push(rubi_rule!(
        order: 6169,
        source: "Int[(f_.+g_.*x_)^m_.*Csch[d_.+e_.*x_]^2/(c_.+b_.*Coth[d_.+e_.*x_]^2+a_.*Csch[d_.+e_.*x_]^2),x_Symbol] :=
          2 \\[Star] Int[(f+g*x)^m/(2*a+b-c+(b+c)*Cosh[2*d+2*e*x]),x] /;
        FreeQ[{a,b,c,d,e,f,g},x] && IGtQ[m,0] && NeQ[a+b,0] && NeQ[a+c,0]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: (f__ + g__ * x_).pow(m_) * (d__ + e__ * x_).csch().pow(2)
            / (c__ + b__ * (d__ + e__ * x_).coth().pow(2) + a__ * (d__ + e__ * x_).csch().pow(2)),
        with: [f__, g__, m_, d__, e__, c__, b__, a__, x_],
        optional: [f__, g__, m_, d__, e__, c__, b__, a__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__], x_)
                && igtq!(m_, 0)
                && neq!(&a__ + &b__, 0)
                && neq!(&a__ + &c__, 0)
        },
        rhs: {
            let double_angle = Atom::num(2) * &d__ + Atom::num(2) * &e__ * x_;
            let denominator = Atom::num(2) * &a__ + &b__ - &c__ + (&b__ + &c__) * double_angle.cosh();
            let integrand = (&f__ + &g__ * x_).pow(&m_) / denominator;
            let recursive = rubi_rhs_int(&integrand, x_);

            rubi_star(Atom::num(2), recursive)
        },
    ));
}

fn push_rules_rule_6170(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_a__, capital_b__, a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 6170,
        source: "Int[(e_.+f_.*x_)*(A_+B_.*Sinh[c_.+d_.*x_])/(a_+b_.*Sinh[c_.+d_.*x_])^2,x_Symbol] :=
          B*(e+f*x)*Cosh[c+d*x]/(a*d*(a+b*Sinh[c+d*x])) -
          B*f/(a*d) \\[Star] Int[Cosh[c+d*x]/(a+b*Sinh[c+d*x]),x] /;
        FreeQ[{a,b,c,d,e,f,A,B},x] && EqQ[a*A+b*B,0]",
        desc: "Integration by parts",
        refs: [],
        pattern: (e__ + f__ * x_) * (capital_a__ + capital_b__ * (c__ + d__ * x_).sinh())
            / (a__ + b__ * (c__ + d__ * x_).sinh()).pow(2),
        with: [e__, f__, capital_a__, capital_b__, c__, d__, a__, b__, x_],
        optional: [e__, f__, capital_b__, c__, d__, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, capital_a__, capital_b__], x_)
                && eqq!(&a__ * &capital_a__ + &b__ * &capital_b__, 0)
        },
        rhs: {
            let linear = &e__ + &f__ * x_;
            let angle = &c__ + &d__ * x_;
            let sinh = angle.sinh();
            let cosh = angle.cosh();
            let denominator = &a__ + &b__ * &sinh;
            let recursive_integrand = &cosh / (&a__ + &b__ * sinh);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(&capital_b__ * linear * cosh / (&a__ * &d__ * denominator)), x_)
                    - rubi_star(&capital_b__ * &f__ / (&a__ * &d__), recursive)
        },
    ));
}

fn push_rules_rule_6171(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_a__, capital_b__, a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 6171,
        source: "Int[(e_.+f_.*x_)*(A_+B_.*Cosh[c_.+d_.*x_])/(a_+b_.*Cosh[c_.+d_.*x_])^2,x_Symbol] :=
          B*(e+f*x)*Sinh[c+d*x]/(a*d*(a+b*Cosh[c+d*x])) -
          B*f/(a*d) \\[Star] Int[Sinh[c+d*x]/(a+b*Cosh[c+d*x]),x] /;
        FreeQ[{a,b,c,d,e,f,A,B},x] && EqQ[a*A-b*B,0]",
        desc: "Integration by parts",
        refs: [],
        pattern: (e__ + f__ * x_) * (capital_a__ + capital_b__ * (c__ + d__ * x_).cosh())
            / (a__ + b__ * (c__ + d__ * x_).cosh()).pow(2),
        with: [e__, f__, capital_a__, capital_b__, c__, d__, a__, b__, x_],
        optional: [e__, f__, capital_b__, c__, d__, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, capital_a__, capital_b__], x_)
                && eqq!(&a__ * &capital_a__ - &b__ * &capital_b__, 0)
        },
        rhs: {
            let linear = &e__ + &f__ * x_;
            let angle = &c__ + &d__ * x_;
            let sinh = angle.sinh();
            let cosh = angle.cosh();
            let denominator = &a__ + &b__ * &cosh;
            let recursive_integrand = &sinh / (&a__ + &b__ * cosh);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(&capital_b__ * linear * sinh / (&a__ * &d__ * denominator)), x_)
                    - rubi_star(&capital_b__ * &f__ / (&a__ * &d__), recursive)
        },
    ));
}

fn push_rules_rule_6172(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6172,
        source: "Int[(e_.+f_.*x_)^m_.*Sinh[a_.+b_.*(c_+d_.*x_)^n_]^p_.,x_Symbol] :=
          1/d^(m+1) \\[Star] Subst[Int[(d*e-c*f+f*x)^m*Sinh[a+b*x^n]^p,x],x,c+d*x] /;
        FreeQ[{a,b,c,d,e,f,n},x] && IGtQ[m,0] && RationalQ[p]",
        desc: "Integration by linear substitution",
        refs: [],
        pattern: (e__ + f__ * x_).pow(m_) * (a__ + b__ * (c__ + d__ * x_).pow(n_)).sinh().pow(p_),
        with: [e__, f__, m_, a__, b__, c__, d__, n_, p_, x_],
        optional: [e__, f__, m_, a__, b__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, n_], x_) && igtq!(m_, 0) && rationalq!(p_)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub = Atom::var(substitution_symbol);
            let transformed_integrand =
                (&d__ * &e__ - &c__ * &f__ + &f__ * &sub).pow(&m_) * (&a__ + &b__ * sub.pow(&n_)).sinh().pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);
            let replacement = &c__ + &d__ * x_;

            let substituted = rubi_subst(&transformed, substitution_symbol, replacement);
            rubi_star(Atom::num(1) / d__.pow(&m_ + 1), substituted)
        },
    ));
}

fn push_rules_rule_6173(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6173,
        source: "Int[(e_.+f_.*x_)^m_.*Cosh[a_.+b_.*(c_+d_.*x_)^n_]^p_.,x_Symbol] :=
          1/d^(m+1) \\[Star] Subst[Int[(d*e-c*f+f*x)^m*Cosh[a+b*x^n]^p,x],x,c+d*x] /;
        FreeQ[{a,b,c,d,e,f,n},x] && IGtQ[m,0] && RationalQ[p]",
        desc: "Integration by linear substitution",
        refs: [],
        pattern: (e__ + f__ * x_).pow(m_) * (a__ + b__ * (c__ + d__ * x_).pow(n_)).cosh().pow(p_),
        with: [e__, f__, m_, a__, b__, c__, d__, n_, p_, x_],
        optional: [e__, f__, m_, a__, b__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, n_], x_) && igtq!(m_, 0) && rationalq!(p_)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub = Atom::var(substitution_symbol);
            let transformed_integrand =
                (&d__ * &e__ - &c__ * &f__ + &f__ * &sub).pow(&m_) * (&a__ + &b__ * sub.pow(&n_)).cosh().pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);
            let replacement = &c__ + &d__ * x_;

            let substituted = rubi_subst(&transformed, substitution_symbol, replacement);
            rubi_star(Atom::num(1) / d__.pow(&m_ + 1), substituted)
        },
    ));
}

fn push_rules_rule_6174(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, m_, n_, v_);
    rules.push(rubi_rule!(
        order: 6174,
        source: "Int[Sech[v_]^m_.*(a_+b_.*Tanh[v_])^n_.,x_Symbol] :=
          Int[(a*Cosh[v]+b*Sinh[v])^n,x] /;
        FreeQ[{a,b},x] && IntegerQ[(m-1)/2] && EqQ[m+n,0]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: Atom::var(v_).sech().pow(m_) * (a__ + b__ * Atom::var(v_).tanh()).pow(n_),
        with: [v_, m_, a__, b__, n_, x_],
        optional: [m_, b__, n_],
        when: { freeq!([a__, b__], x_) && integerq!((&m_ - 1) / 2) && eqq!(&m_ + &n_, 0) },
        rhs: {
            let integrand = (&a__ * v_.cosh() + &b__ * v_.sinh()).pow(&n_);

            rubi_rhs_int(&integrand, x_)
        },
    ));
}

fn push_rules_rule_6175(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, m_, n_, v_);
    rules.push(rubi_rule!(
        order: 6175,
        source: "Int[Csch[v_]^m_.*(a_+b_.*Coth[v_])^n_.,x_Symbol] :=
          Int[(b*Cosh[v]+a*Sinh[v])^n,x] /;
        FreeQ[{a,b},x] && IntegerQ[(m-1)/2] && EqQ[m+n,0]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: Atom::var(v_).csch().pow(m_) * (a__ + b__ * Atom::var(v_).coth()).pow(n_),
        with: [v_, m_, a__, b__, n_, x_],
        optional: [m_, b__, n_],
        when: { freeq!([a__, b__], x_) && integerq!((&m_ - 1) / 2) && eqq!(&m_ + &n_, 0) },
        rhs: {
            let integrand = (&b__ * v_.cosh() + &a__ * v_.sinh()).pow(&n_);

            rubi_rhs_int(&integrand, x_)
        },
    ));
}

fn push_rules_rule_6176(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, n_, u__, x_);
    rules.push(rubi_rule!(
        order: 6176,
        source: "Int[u_.*Sinh[a_.+b_.*x_]^m_.*Sinh[c_.+d_.*x_]^n_.,x_Symbol] :=
          Int[ExpandTrigReduce[u,Sinh[a+b*x]^m*Sinh[c+d*x]^n,x],x] /;
        FreeQ[{a,b,c,d},x] && IGtQ[m,0] && IGtQ[n,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: u__ * (a__ + b__ * x_).sinh().pow(m_) * (c__ + d__ * x_).sinh().pow(n_),
        with: [u__, a__, b__, m_, c__, d__, n_, x_],
        optional: [u__, a__, b__, m_, c__, d__, n_],
        when: { freeq!([a__, b__, c__, d__], x_) && igtq!(m_, 0) && igtq!(n_, 0) },
        rhs: {
            let product = (&a__ + &b__ * x_).sinh().pow(&m_) * (&c__ + &d__ * x_).sinh().pow(&n_);
            let expanded = rubi_expand_trig_reduce(&u__, &product, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_6177(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, n_, u__, x_);
    rules.push(rubi_rule!(
        order: 6177,
        source: "Int[u_.*Cosh[a_.+b_.*x_]^m_.*Cosh[c_.+d_.*x_]^n_.,x_Symbol] :=
          Int[ExpandTrigReduce[u,Cosh[a+b*x]^m*Cosh[c+d*x]^n,x],x] /;
        FreeQ[{a,b,c,d},x] && IGtQ[m,0] && IGtQ[n,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: u__ * (a__ + b__ * x_).cosh().pow(m_) * (c__ + d__ * x_).cosh().pow(n_),
        with: [u__, a__, b__, m_, c__, d__, n_, x_],
        optional: [u__, a__, b__, m_, c__, d__, n_],
        when: { freeq!([a__, b__, c__, d__], x_) && igtq!(m_, 0) && igtq!(n_, 0) },
        rhs: {
            let product = (&a__ + &b__ * x_).cosh().pow(&m_) * (&c__ + &d__ * x_).cosh().pow(&n_);
            let expanded = rubi_expand_trig_reduce(&u__, &product, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_6178(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 6178,
        source: "Int[Sech[a_.+b_.*x_]*Sech[c_+d_.*x_],x_Symbol] :=
          -Csch[(b*c-a*d)/d] \\[Star] Int[Tanh[a+b*x],x] + Csch[(b*c-a*d)/b] \\[Star] Int[Tanh[c+d*x],x] /;
        FreeQ[{a,b,c,d},x] && EqQ[b^2-d^2,0] && NeQ[b*c-a*d,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (a__ + b__ * x_).sech() * (c__ + d__ * x_).sech(),
        with: [a__, b__, c__, d__, x_],
        optional: [a__, b__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && eqq!(b__.pow(2) - d__.pow(2), 0)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
        },
        rhs: {
            let determinant = &b__ * &c__ - &a__ * &d__;
            let first = rubi_rhs_int(&(&a__ + &b__ * x_).tanh(), x_);
            let second = rubi_rhs_int(&(&c__ + &d__ * x_).tanh(), x_);

            rubi_star(-(&determinant / &d__).csch(), first)
                    + rubi_star((determinant / &b__).csch(), second)
        },
    ));
}

fn push_rules_rule_6179(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 6179,
        source: "Int[Csch[a_.+b_.*x_]*Csch[c_+d_.*x_],x_Symbol] :=
          Csch[(b*c-a*d)/b] \\[Star] Int[Coth[a+b*x],x] - Csch[(b*c-a*d)/d] \\[Star] Int[Coth[c+d*x],x] /;
        FreeQ[{a,b,c,d},x] && EqQ[b^2-d^2,0] && NeQ[b*c-a*d,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (a__ + b__ * x_).csch() * (c__ + d__ * x_).csch(),
        with: [a__, b__, c__, d__, x_],
        optional: [a__, b__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && eqq!(b__.pow(2) - d__.pow(2), 0)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
        },
        rhs: {
            let determinant = &b__ * &c__ - &a__ * &d__;
            let first = rubi_rhs_int(&(&a__ + &b__ * x_).coth(), x_);
            let second = rubi_rhs_int(&(&c__ + &d__ * x_).coth(), x_);

            rubi_star((&determinant / &b__).csch(), first)
                    - rubi_star((determinant / &d__).csch(), second)
        },
    ));
}

fn push_rules_rule_6180(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 6180,
        source: "Int[Tanh[a_.+b_.*x_]*Tanh[c_+d_.*x_],x_Symbol] :=
          b*x/d - b/d*Cosh[(b*c-a*d)/d] \\[Star] Int[Sech[a+b*x]*Sech[c+d*x],x] /;
        FreeQ[{a,b,c,d},x] && EqQ[b^2-d^2,0] && NeQ[b*c-a*d,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (a__ + b__ * x_).tanh() * (c__ + d__ * x_).tanh(),
        with: [a__, b__, c__, d__, x_],
        optional: [a__, b__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && eqq!(b__.pow(2) - d__.pow(2), 0)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
        },
        rhs: {
            let determinant = &b__ * &c__ - &a__ * &d__;
            let recursive_integrand = (&a__ + &b__ * x_).sech() * (&c__ + &d__ * x_).sech();
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(&b__ * x_ / &d__), x_)
                    - rubi_star(&b__ / &d__ * (determinant / &d__).cosh(), recursive)
        },
    ));
}

fn push_rules_rule_6181(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 6181,
        source: "Int[Coth[a_.+b_.*x_]*Coth[c_+d_.*x_],x_Symbol] :=
          b*x/d + Cosh[(b*c-a*d)/d] \\[Star] Int[Csch[a+b*x]*Csch[c+d*x],x] /;
        FreeQ[{a,b,c,d},x] && EqQ[b^2-d^2,0] && NeQ[b*c-a*d,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (a__ + b__ * x_).coth() * (c__ + d__ * x_).coth(),
        with: [a__, b__, c__, d__, x_],
        optional: [a__, b__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && eqq!(b__.pow(2) - d__.pow(2), 0)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
        },
        rhs: {
            let determinant = &b__ * &c__ - &a__ * &d__;
            let recursive_integrand = (&a__ + &b__ * x_).csch() * (&c__ + &d__ * x_).csch();
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(&b__ * x_ / &d__), x_)
                    + rubi_star((determinant / &d__).cosh(), recursive)
        },
    ));
}

fn push_rules_rule_6182(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, n_, u__, v_);
    rules.push(rubi_rule!(
        order: 6182,
        source: "Int[u_.*(a_.*Cosh[v_]+b_.*Sinh[v_])^n_.,x_Symbol] :=
          Int[u*(a*E^(a/b*v))^n,x] /;
        FreeQ[{a,b,n},x] && EqQ[a^2-b^2,0]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: u__ * (a__ * Atom::var(v_).cosh() + b__ * Atom::var(v_).sinh()).pow(n_),
        with: [u__, a__, v_, b__, n_, x_],
        optional: [u__, a__, b__, n_],
        when: { freeq!([a__, b__, n_], x_) && eqq!(a__.pow(2) - b__.pow(2), 0) },
        rhs: {
            let exponential = ((&a__ / &b__) * &v_).exp();
            let integrand = &u__ * (&a__ * exponential).pow(&n_);

            rubi_rhs_int(&integrand, x_)
        },
    ));
}

fn push_rules_rule_6183(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 6183,
        source: "Int[Sinh[d_.*(a_.+b_.*Log[c_.*x_^n_.])^2],x_Symbol] :=
          -1/2 \\[Star] Int[E^(-d*(a+b*Log[c*x^n])^2),x] + 1/2 \\[Star] Int[E^(d*(a+b*Log[c*x^n])^2),x] /;
        FreeQ[{a,b,c,d,n},x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (d__ * (a__ + b__ * (c__ * x_.pow(n_)).log()).pow(2)).sinh(),
        with: [d__, a__, b__, c__, n_, x_],
        optional: [d__, a__, b__, c__, n_],
        when: { freeq!([a__, b__, c__, d__, n_], x_) },
        rhs: {
            let log_square = (&a__ + &b__ * (&c__ * x_.pow(&n_)).log()).pow(2);
            let negative_exponential = (-&d__ * &log_square).exp();
            let positive_exponential = (&d__ * log_square).exp();
            let first = rubi_rhs_int(&negative_exponential, x_);
            let second = rubi_rhs_int(&positive_exponential, x_);

            rubi_star(-Atom::num(1) / 2, first)
                    + rubi_star(Atom::num(1) / 2, second)
        },
    ));
}

fn push_rules_rule_6184(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 6184,
        source: "Int[Cosh[d_.*(a_.+b_.*Log[c_.*x_^n_.])^2],x_Symbol] :=
          1/2 \\[Star] Int[E^(-d*(a+b*Log[c*x^n])^2),x] + 1/2 \\[Star] Int[E^(d*(a+b*Log[c*x^n])^2),x] /;
        FreeQ[{a,b,c,d,n},x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (d__ * (a__ + b__ * (c__ * x_.pow(n_)).log()).pow(2)).cosh(),
        with: [d__, a__, b__, c__, n_, x_],
        optional: [d__, a__, b__, c__, n_],
        when: { freeq!([a__, b__, c__, d__, n_], x_) },
        rhs: {
            let log_square = (&a__ + &b__ * (&c__ * x_.pow(&n_)).log()).pow(2);
            let negative_exponential = (-&d__ * &log_square).exp();
            let positive_exponential = (&d__ * log_square).exp();
            let first = rubi_rhs_int(&negative_exponential, x_);
            let second = rubi_rhs_int(&positive_exponential, x_);

            rubi_star(Atom::num(1) / 2, first)
                    + rubi_star(Atom::num(1) / 2, second)
        },
    ));
}

fn push_rules_rule_6185(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 6185,
        source: "Int[(e_.*x_)^m_.*Sinh[d_.*(a_.+b_.*Log[c_.*x_^n_.])^2],x_Symbol] :=
          -1/2 \\[Star] Int[(e*x)^m*E^(-d*(a+b*Log[c*x^n])^2),x] + 1/2 \\[Star] Int[(e*x)^m*E^(d*(a+b*Log[c*x^n])^2),x] /;
        FreeQ[{a,b,c,d,e,m,n},x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (e__ * x_).pow(m_) * (d__ * (a__ + b__ * (c__ * x_.pow(n_)).log()).pow(2)).sinh(),
        with: [e__, m_, d__, a__, b__, c__, n_, x_],
        optional: [e__, m_, d__, a__, b__, c__, n_],
        when: { freeq!([a__, b__, c__, d__, e__, m_, n_], x_) },
        rhs: {
            let leading = (&e__ * x_).pow(&m_);
            let log_square = (&a__ + &b__ * (&c__ * x_.pow(&n_)).log()).pow(2);
            let negative_integrand = &leading * (-&d__ * &log_square).exp();
            let positive_integrand = leading * (&d__ * log_square).exp();
            let first = rubi_rhs_int(&negative_integrand, x_);
            let second = rubi_rhs_int(&positive_integrand, x_);

            rubi_star(-Atom::num(1) / 2, first)
                    + rubi_star(Atom::num(1) / 2, second)
        },
    ));
}

fn push_rules_rule_6186(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 6186,
        source: "Int[(e_.*x_)^m_.*Cosh[d_.*(a_.+b_.*Log[c_.*x_^n_.])^2],x_Symbol] :=
          1/2 \\[Star] Int[(e*x)^m*E^(-d*(a+b*Log[c*x^n])^2),x] + 1/2 \\[Star] Int[(e*x)^m*E^(d*(a+b*Log[c*x^n])^2),x] /;
        FreeQ[{a,b,c,d,e,m,n},x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (e__ * x_).pow(m_) * (d__ * (a__ + b__ * (c__ * x_.pow(n_)).log()).pow(2)).cosh(),
        with: [e__, m_, d__, a__, b__, c__, n_, x_],
        optional: [e__, m_, d__, a__, b__, c__, n_],
        when: { freeq!([a__, b__, c__, d__, e__, m_, n_], x_) },
        rhs: {
            let leading = (&e__ * x_).pow(&m_);
            let log_square = (&a__ + &b__ * (&c__ * x_.pow(&n_)).log()).pow(2);
            let negative_integrand = &leading * (-&d__ * &log_square).exp();
            let positive_integrand = leading * (&d__ * log_square).exp();
            let first = rubi_rhs_int(&negative_integrand, x_);
            let second = rubi_rhs_int(&positive_integrand, x_);

            rubi_star(Atom::num(1) / 2, first)
                    + rubi_star(Atom::num(1) / 2, second)
        },
    ));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn downvalues_6091_through_6186_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .filter(|order| (6091..=6186).contains(order))
            .collect::<Vec<_>>();
        assert_eq!(orders, (6091..=6186).collect::<Vec<_>>());
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
    (e__ + f__ * x_).pow(m_) * (c__ + d__ * x_).cosh().pow(n_)
        / (a__ + b__ * (c__ + d__ * x_).sinh())
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
    (e__ + f__ * x_).pow(m_) * (c__ + d__ * x_).cosh() / (a__ + b__ * (c__ + d__ * x_).sinh())
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
    let x_ = symbols.x_;
    (e__ + f__ * x_).pow(m_) * (c__ + d__ * x_).csch().pow(n_)
        / (a__ + b__ * (c__ + d__ * x_).cosh())
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
    (e__ + f__ * x_).pow(m_) * (c__ + d__ * x_).sech().pow(n_)
        / (a__ + b__ * (c__ + d__ * x_).sinh())
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
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    (e__ + f__ * x_).pow(m_) * (c__ + d__ * x_).sinh().pow(n_)
        / (a__ + b__ * (c__ + d__ * x_).cosh())
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
    let x_ = symbols.x_;
    (e__ + f__ * x_).pow(m_) * (c__ + d__ * x_).sinh() / (a__ + b__ * (c__ + d__ * x_).cosh())
}
