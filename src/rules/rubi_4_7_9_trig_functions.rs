use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_5026(rules);
    push_rules_rule_5027(rules);
    push_rules_rule_5028(rules);
    push_rules_rule_5029(rules);
    push_rules_rule_5030(rules);
    push_rules_rule_5031(rules);
    push_rules_rule_5032(rules);
    push_rules_rule_5033(rules);
    push_rules_rule_5034(rules);
    push_rules_rule_5035(rules);
    push_rules_rule_5036(rules);
    push_rules_rule_5037(rules);
    push_rules_rule_5038(rules);
    push_rules_rule_5039(rules);
    push_rules_rule_5040(rules);
    push_rules_rule_5041(rules);
    push_rules_rule_5042(rules);
    push_rules_rule_5043(rules);
    push_rules_rule_5044(rules);
    push_rules_rule_5045(rules);
    push_rules_rule_5046(rules);
    push_rules_rule_5047(rules);
    push_rules_rule_5048(rules);
    push_rules_rule_5049(rules);
    push_rules_rule_5050(rules);
    push_rules_rule_5051(rules);
    push_rules_rule_5052(rules);
    push_rules_rule_5053(rules);
    push_rules_rule_5054(rules);
    push_rules_rule_5055(rules);
    push_rules_rule_5056(rules);
    push_rules_rule_5057(rules);
    push_rules_rule_5058(rules);
    push_rules_rule_5059(rules);
    push_rules_rule_5060(rules);
    push_rules_rule_5061(rules);
    push_rules_rule_5062(rules);
    push_rules_rule_5063(rules);
    push_rules_rule_5064(rules);
    push_rules_rule_5065(rules);
    push_rules_rule_5066(rules);
    push_rules_rule_5067(rules);
    push_rules_rule_5068(rules);
    push_rules_rule_5069(rules);
    push_rules_rule_5070(rules);
    push_rules_rule_5071(rules);
    push_rules_rule_5072(rules);
    push_rules_rule_5073(rules);
    push_rules_rule_5074(rules);
    push_rules_rule_5075(rules);
    push_rules_rule_5076(rules);
    push_rules_rule_5077(rules);
    push_rules_rule_5078(rules);
    push_rules_rule_5079(rules);
    push_rules_rule_5080(rules);
    push_rules_rule_5081(rules);
    push_rules_rule_5082(rules);
    push_rules_rule_5083(rules);
    push_rules_rule_5084(rules);
    push_rules_rule_5085(rules);
    push_rules_rule_5086(rules);
    push_rules_rule_5087(rules);
    push_rules_rule_5088(rules);
    push_rules_rule_5089(rules);
    push_rules_rule_5090(rules);
    push_rules_rule_5091(rules);
    push_rules_rule_5092(rules);
    push_rules_rule_5093(rules);
    push_rules_rule_5094(rules);
    push_rules_rule_5095(rules);
    push_rules_rule_5096(rules);
    push_rules_rule_5097(rules);
    push_rules_rule_5098(rules);
    push_rules_rule_5099(rules);
    push_rules_rule_5100(rules);
    push_rules_rule_5101(rules);
    push_rules_rule_5102(rules);
    push_rules_rule_5103(rules);
    push_rules_rule_5104(rules);
    push_rules_rule_5105(rules);
    push_rules_rule_5106(rules);
    push_rules_rule_5107(rules);
    push_rules_rule_5108(rules);
    push_rules_rule_5109(rules);
    push_rules_rule_5110(rules);
    push_rules_rule_5111(rules);
    push_rules_rule_5112(rules);
    push_rules_rule_5113(rules);
    push_rules_rule_5114(rules);
    push_rules_rule_5115(rules);
    push_rules_rule_5116(rules);
    push_rules_rule_5117(rules);
    push_rules_rule_5118(rules);
    push_rules_rule_5119(rules);
    push_rules_rule_5120(rules);
    push_rules_rule_5121(rules);
    push_rules_rule_5122(rules);
    push_rules_rule_5123(rules);
    push_rules_rule_5124(rules);
    push_rules_rule_5125(rules);
    push_rules_rule_5126(rules);
    push_rules_rule_5127(rules);
    push_rules_rule_5128(rules);
    push_rules_rule_5129(rules);
}

fn push_rules_rule_5026(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5026,
        source: "Int[(e_.+f_.*x_)^m_.*Sin[c_.+d_.*x_]^n_./(a_+b_.*Sin[c_.+d_.*x_]),x_Symbol] :=
          1/b \\[Star] Int[(e+f*x)^m*Sin[c+d*x]^(n-1),x] - a/b \\[Star] Int[(e+f*x)^m*Sin[c+d*x]^(n-1)/(a+b*Sin[c+d*x]),x] /;
        FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && IGtQ[n,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (e__ + f__ * x_).pow(m_) * (c__ + d__ * x_).sin().pow(n_) / (a__ + b__ * (c__ + d__ * x_).sin()),
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
            let first_integrand = linear.pow(&m_) * angle.sin().pow(&n_ - 1);
            let second_integrand = linear.pow(&m_) * angle.sin().pow(&n_ - 1) / (&a__ + &b__ * angle.sin());
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(Atom::num(1) / &b__, first)
                    + rubi_star(-&a__ / &b__, second)
        },
    ));
}

fn push_rules_rule_5027(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5027,
        source: "Int[(e_.+f_.*x_)^m_.*Cos[c_.+d_.*x_]^n_./(a_+b_.*Cos[c_.+d_.*x_]),x_Symbol] :=
          1/b \\[Star] Int[(e+f*x)^m*Cos[c+d*x]^(n-1),x] - a/b \\[Star] Int[(e+f*x)^m*Cos[c+d*x]^(n-1)/(a+b*Cos[c+d*x]),x] /;
        FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && IGtQ[n,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (e__ + f__ * x_).pow(m_) * (c__ + d__ * x_).cos().pow(n_) / (a__ + b__ * (c__ + d__ * x_).cos()),
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
            let first_integrand = linear.pow(&m_) * angle.cos().pow(&n_ - 1);
            let second_integrand = linear.pow(&m_) * angle.cos().pow(&n_ - 1) / (&a__ + &b__ * angle.cos());
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(Atom::num(1) / &b__, first)
                    + rubi_star(-&a__ / &b__, second)
        },
    ));
}

fn push_rules_rule_5028(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, x_);
    rules.push(rubi_rule!(
        order: 5028,
        source: "Int[(e_.+f_.*x_)^m_.*Cos[c_.+d_.*x_]/(a_+b_.*Sin[c_.+d_.*x_]),x_Symbol] :=
          -I*(e+f*x)^(m+1)/(b*f*(m+1)) + 2 \\[Star] Int[(e+f*x)^m*E^(I*(c+d*x))/(a-I*b*E^(I*(c+d*x))),x] /;
        FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && EqQ[a^2-b^2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [e__, f__, m_, c__, d__, a__, b__, x_],
        optional: [e__, f__, m_, c__, d__, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && igtq!(m_, 0)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
        },
        rhs: {
            let i = Atom::i();
            let linear = &e__ + &f__ * x_;
            let angle = &c__ + &d__ * x_;
            let exponential = (&i * angle).exp();
            let recursive_integrand = linear.pow(&m_) * &exponential / (&a__ - &i * &b__ * exponential);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(-&i * linear.pow(&m_ + 1) / (&b__ * &f__ * (&m_ + 1))), x_)
                    + rubi_star(Atom::num(2), recursive)
        },
    ));
}

fn push_rules_rule_5029(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, x_);
    rules.push(rubi_rule!(
        order: 5029,
        source: "Int[(e_.+f_.*x_)^m_.*Sin[c_.+d_.*x_]/(a_+b_.*Cos[c_.+d_.*x_]),x_Symbol] :=
          I*(e+f*x)^(m+1)/(b*f*(m+1)) - 2*I \\[Star] Int[(e+f*x)^m*E^(I*(c+d*x))/(a+b*E^(I*(c+d*x))),x] /;
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
            let i = Atom::i();
            let linear = &e__ + &f__ * x_;
            let angle = &c__ + &d__ * x_;
            let exponential = (&i * angle).exp();
            let recursive_integrand = linear.pow(&m_) * &exponential / (&a__ + &b__ * exponential);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(&i * linear.pow(&m_ + 1) / (&b__ * &f__ * (&m_ + 1))), x_)
                    + rubi_star(-Atom::num(2) * &i, recursive)
        },
    ));
}

fn push_rules_rule_5030(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, x_);
    rules.push(rubi_rule!(
        order: 5030,
        source: "Int[(e_.+f_.*x_)^m_.*Cos[c_.+d_.*x_]/(a_+b_.*Sin[c_.+d_.*x_]),x_Symbol] :=
          -I*(e+f*x)^(m+1)/(b*f*(m+1)) +
          Int[(e+f*x)^m*E^(I*(c+d*x))/(a-Rt[a^2-b^2,2]-I*b*E^(I*(c+d*x))),x] +
          Int[(e+f*x)^m*E^(I*(c+d*x))/(a+Rt[a^2-b^2,2]-I*b*E^(I*(c+d*x))),x] /;
        FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && PosQ[a^2-b^2]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [e__, f__, m_, c__, d__, a__, b__, x_],
        optional: [e__, f__, m_, c__, d__, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && igtq!(m_, 0)
                && posq!(a__.pow(2) - b__.pow(2))
        },
        rhs: {
            let i = Atom::i();
            let linear = &e__ + &f__ * x_;
            let angle = &c__ + &d__ * x_;
            let exponential = (&i * angle).exp();
            let rt = rubi_rt(&(a__.pow(2) - b__.pow(2)), 2);
            let first_integrand = linear.pow(&m_) * &exponential / (&a__ - &rt - &i * &b__ * &exponential);
            let second_integrand = linear.pow(&m_) * &exponential / (&a__ + &rt - &i * &b__ * exponential);
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_simp(&(-&i * linear.pow(&m_ + 1) / (&b__ * &f__ * (&m_ + 1))), x_) + first + second
        },
    ));
}

fn push_rules_rule_5031(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, x_);
    rules.push(rubi_rule!(
        order: 5031,
        source: "Int[(e_.+f_.*x_)^m_.*Sin[c_.+d_.*x_]/(a_+b_.*Cos[c_.+d_.*x_]),x_Symbol] :=
          I*(e+f*x)^(m+1)/(b*f*(m+1)) -
          I \\[Star] Int[(e+f*x)^m*E^(I*(c+d*x))/(a-Rt[a^2-b^2,2]+b*E^(I*(c+d*x))),x] -
          I \\[Star] Int[(e+f*x)^m*E^(I*(c+d*x))/(a+Rt[a^2-b^2,2]+b*E^(I*(c+d*x))),x] /;
        FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && PosQ[a^2-b^2]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [e__, f__, m_, c__, d__, a__, b__, x_],
        optional: [e__, f__, m_, c__, d__, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && igtq!(m_, 0)
                && posq!(a__.pow(2) - b__.pow(2))
        },
        rhs: {
            let i = Atom::i();
            let linear = &e__ + &f__ * x_;
            let angle = &c__ + &d__ * x_;
            let exponential = (&i * angle).exp();
            let rt = rubi_rt(&(a__.pow(2) - b__.pow(2)), 2);
            let first_integrand = linear.pow(&m_) * &exponential / (&a__ - &rt + &b__ * &exponential);
            let second_integrand = linear.pow(&m_) * &exponential / (&a__ + &rt + &b__ * exponential);
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_simp(&(&i * linear.pow(&m_ + 1) / (&b__ * &f__ * (&m_ + 1))), x_)
                    + rubi_star(-&i, first)
                    + rubi_star(-&i, second)
        },
    ));
}

fn push_rules_rule_5032(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, x_);
    rules.push(rubi_rule!(
        order: 5032,
        source: "Int[(e_.+f_.*x_)^m_.*Cos[c_.+d_.*x_]/(a_+b_.*Sin[c_.+d_.*x_]),x_Symbol] :=
          -I*(e+f*x)^(m+1)/(b*f*(m+1)) +
          I \\[Star] Int[(e+f*x)^m*E^(I*(c+d*x))/(I*a-Rt[-a^2+b^2,2]+b*E^(I*(c+d*x))),x] +
          I \\[Star] Int[(e+f*x)^m*E^(I*(c+d*x))/(I*a+Rt[-a^2+b^2,2]+b*E^(I*(c+d*x))),x] /;
        FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && NegQ[a^2-b^2]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [e__, f__, m_, c__, d__, a__, b__, x_],
        optional: [e__, f__, m_, c__, d__, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && igtq!(m_, 0)
                && negq!(a__.pow(2) - b__.pow(2))
        },
        rhs: {
            let i = Atom::i();
            let linear = &e__ + &f__ * x_;
            let angle = &c__ + &d__ * x_;
            let exponential = (&i * angle).exp();
            let rt = rubi_rt(&(-a__.pow(2) + b__.pow(2)), 2);
            let first_integrand = linear.pow(&m_) * &exponential / (&i * &a__ - &rt + &b__ * &exponential);
            let second_integrand = linear.pow(&m_) * &exponential / (&i * &a__ + &rt + &b__ * exponential);
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_simp(&(-&i * linear.pow(&m_ + 1) / (&b__ * &f__ * (&m_ + 1))), x_)
                    + rubi_star(&i, first)
                    + rubi_star(i, second)
        },
    ));
}

fn push_rules_rule_5033(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, x_);
    rules.push(rubi_rule!(
        order: 5033,
        source: "Int[(e_.+f_.*x_)^m_.*Sin[c_.+d_.*x_]/(a_+b_.*Cos[c_.+d_.*x_]),x_Symbol] :=
          I*(e+f*x)^(m+1)/(b*f*(m+1)) +
          Int[(e+f*x)^m*E^(I*(c+d*x))/(I*a-Rt[-a^2+b^2,2]+I*b*E^(I*(c+d*x))),x] +
          Int[(e+f*x)^m*E^(I*(c+d*x))/(I*a+Rt[-a^2+b^2,2]+I*b*E^(I*(c+d*x))),x] /;
        FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && NegQ[a^2-b^2]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [e__, f__, m_, c__, d__, a__, b__, x_],
        optional: [e__, f__, m_, c__, d__, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && igtq!(m_, 0)
                && negq!(a__.pow(2) - b__.pow(2))
        },
        rhs: {
            let i = Atom::i();
            let linear = &e__ + &f__ * x_;
            let angle = &c__ + &d__ * x_;
            let exponential = (&i * angle).exp();
            let rt = rubi_rt(&(-a__.pow(2) + b__.pow(2)), 2);
            let first_integrand = linear.pow(&m_) * &exponential / (&i * &a__ - &rt + &i * &b__ * &exponential);
            let second_integrand = linear.pow(&m_) * &exponential / (&i * &a__ + &rt + &i * &b__ * exponential);
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_simp(&(&i * linear.pow(&m_ + 1) / (&b__ * &f__ * (&m_ + 1))), x_) + first + second
        },
    ));
}

fn push_rules_rule_5034(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5034,
        source: "Int[(e_.+f_.*x_)^m_.*Cos[c_.+d_.*x_]^n_/(a_+b_.*Sin[c_.+d_.*x_]),x_Symbol] :=
          1/a \\[Star] Int[(e+f*x)^m*Cos[c+d*x]^(n-2),x] -
          1/b \\[Star] Int[(e+f*x)^m*Cos[c+d*x]^(n-2)*Sin[c+d*x],x] /;
        FreeQ[{a,b,c,d,e,f,m},x] && IGtQ[n,1] && EqQ[a^2-b^2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
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
            let first_integrand = linear.pow(&m_) * angle.cos().pow(&n_ - 2);
            let second_integrand = linear.pow(&m_) * angle.cos().pow(&n_ - 2) * angle.sin();
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(Atom::num(1) / &a__, first)
                    + rubi_star(-Atom::num(1) / &b__, second)
        },
    ));
}

fn push_rules_rule_5035(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5035,
        source: "Int[(e_.+f_.*x_)^m_.*Sin[c_.+d_.*x_]^n_/(a_+b_.*Cos[c_.+d_.*x_]),x_Symbol] :=
          1/a \\[Star] Int[(e+f*x)^m*Sin[c+d*x]^(n-2),x] -
          1/b \\[Star] Int[(e+f*x)^m*Sin[c+d*x]^(n-2)*Cos[c+d*x],x] /;
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
            let first_integrand = linear.pow(&m_) * angle.sin().pow(&n_ - 2);
            let second_integrand = linear.pow(&m_) * angle.sin().pow(&n_ - 2) * angle.cos();
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(Atom::num(1) / &a__, first)
                    + rubi_star(-Atom::num(1) / &b__, second)
        },
    ));
}

fn push_rules_rule_5036(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5036,
        source: "Int[(e_.+f_.*x_)^m_.*Cos[c_.+d_.*x_]^n_/(a_+b_.*Sin[c_.+d_.*x_]),x_Symbol] :=
          a/b^2 \\[Star] Int[(e+f*x)^m*Cos[c+d*x]^(n-2),x] -
          1/b \\[Star] Int[(e+f*x)^m*Cos[c+d*x]^(n-2)*Sin[c+d*x],x] -
          (a^2-b^2)/b^2 \\[Star] Int[(e+f*x)^m*Cos[c+d*x]^(n-2)/(a+b*Sin[c+d*x]),x] /;
        FreeQ[{a,b,c,d,e,f},x] && IGtQ[n,1] && NeQ[a^2-b^2,0] && IGtQ[m,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
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
            let b2 = b__.pow(2);
            let discriminant = a__.pow(2) - b__.pow(2);
            let first_integrand = linear.pow(&m_) * angle.cos().pow(&n_ - 2);
            let second_integrand = linear.pow(&m_) * angle.cos().pow(&n_ - 2) * angle.sin();
            let third_integrand =
                linear.pow(&m_) * angle.cos().pow(&n_ - 2) / (&a__ + &b__ * angle.sin());
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);
            let third = rubi_rhs_int(&third_integrand, x_);

            rubi_star(&a__ / &b2, first)
                    + rubi_star(-Atom::num(1) / &b__, second)
                    + rubi_star(-discriminant / b2, third)
        },
    ));
}

fn push_rules_rule_5037(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5037,
        source: "Int[(e_.+f_.*x_)^m_.*Sin[c_.+d_.*x_]^n_/(a_+b_.*Cos[c_.+d_.*x_]),x_Symbol] :=
          a/b^2 \\[Star] Int[(e+f*x)^m*Sin[c+d*x]^(n-2),x] -
          1/b \\[Star] Int[(e+f*x)^m*Sin[c+d*x]^(n-2)*Cos[c+d*x],x] -
          (a^2-b^2)/b^2 \\[Star] Int[(e+f*x)^m*Sin[c+d*x]^(n-2)/(a+b*Cos[c+d*x]),x] /;
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
            let b2 = b__.pow(2);
            let discriminant = a__.pow(2) - b__.pow(2);
            let first_integrand = linear.pow(&m_) * angle.sin().pow(&n_ - 2);
            let second_integrand = linear.pow(&m_) * angle.sin().pow(&n_ - 2) * angle.cos();
            let third_integrand =
                linear.pow(&m_) * angle.sin().pow(&n_ - 2) / (&a__ + &b__ * angle.cos());
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);
            let third = rubi_rhs_int(&third_integrand, x_);

            rubi_star(&a__ / &b2, first)
                    + rubi_star(-Atom::num(1) / &b__, second)
                    + rubi_star(-discriminant / b2, third)
        },
    ));
}

fn push_rules_rule_5038(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5038,
        source: "Int[(e_.+f_.*x_)^m_.*Tan[c_.+d_.*x_]^n_./(a_+b_.*Sin[c_.+d_.*x_]),x_Symbol] :=
          1/b \\[Star] Int[(e+f*x)^m*Sec[c+d*x]*Tan[c+d*x]^(n-1),x] - a/b \\[Star] Int[(e+f*x)^m*Sec[c+d*x]*Tan[c+d*x]^(n-1)/(a+b*Sin[c+d*x]),x] /;
        FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && IGtQ[n,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (e__ + f__ * x_).pow(m_) * (c__ + d__ * x_).tan().pow(n_) / (a__ + b__ * (c__ + d__ * x_).sin()),
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
            let first_integrand = linear.pow(&m_) * angle.sec() * angle.tan().pow(&n_ - 1);
            let second_integrand =
                linear.pow(&m_) * angle.sec() * angle.tan().pow(&n_ - 1) / (&a__ + &b__ * angle.sin());
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(Atom::num(1) / &b__, first)
                    + rubi_star(-&a__ / &b__, second)
        },
    ));
}

fn push_rules_rule_5039(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5039,
        source: "Int[(e_.+f_.*x_)^m_.*Cot[c_.+d_.*x_]^n_./(a_+b_.*Cos[c_.+d_.*x_]),x_Symbol] :=
          1/b \\[Star] Int[(e+f*x)^m*Csc[c+d*x]*Cot[c+d*x]^(n-1),x] - a/b \\[Star] Int[(e+f*x)^m*Csc[c+d*x]*Cot[c+d*x]^(n-1)/(a+b*Cos[c+d*x]),x] /;
        FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && IGtQ[n,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (e__ + f__ * x_).pow(m_) * (c__ + d__ * x_).cot().pow(n_) / (a__ + b__ * (c__ + d__ * x_).cos()),
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
            let first_integrand = linear.pow(&m_) * angle.csc() * angle.cot().pow(&n_ - 1);
            let second_integrand =
                linear.pow(&m_) * angle.csc() * angle.cot().pow(&n_ - 1) / (&a__ + &b__ * angle.cos());
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(Atom::num(1) / &b__, first)
                    + rubi_star(-&a__ / &b__, second)
        },
    ));
}

fn push_rules_rule_5040(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5040,
        source: "Int[(e_.+f_.*x_)^m_.*Cot[c_.+d_.*x_]^n_./(a_+b_.*Sin[c_.+d_.*x_]),x_Symbol] :=
          1/a \\[Star] Int[(e+f*x)^m*Cot[c+d*x]^n,x] - b/a \\[Star] Int[(e+f*x)^m*Cos[c+d*x]*Cot[c+d*x]^(n-1)/(a+b*Sin[c+d*x]),x] /;
        FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && IGtQ[n,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (e__ + f__ * x_).pow(m_) * (c__ + d__ * x_).cot().pow(n_) / (a__ + b__ * (c__ + d__ * x_).sin()),
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
            let first_integrand = linear.pow(&m_) * angle.cot().pow(&n_);
            let second_integrand =
                linear.pow(&m_) * angle.cos() * angle.cot().pow(&n_ - 1) / (&a__ + &b__ * angle.sin());
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(Atom::num(1) / &a__, first)
                    + rubi_star(-&b__ / &a__, second)
        },
    ));
}

fn push_rules_rule_5041(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5041,
        source: "Int[(e_.+f_.*x_)^m_.*Tan[c_.+d_.*x_]^n_./(a_+b_.*Cos[c_.+d_.*x_]),x_Symbol] :=
          1/a \\[Star] Int[(e+f*x)^m*Tan[c+d*x]^n,x] - b/a \\[Star] Int[(e+f*x)^m*Sin[c+d*x]*Tan[c+d*x]^(n-1)/(a+b*Cos[c+d*x]),x] /;
        FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && IGtQ[n,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (e__ + f__ * x_).pow(m_) * (c__ + d__ * x_).tan().pow(n_) / (a__ + b__ * (c__ + d__ * x_).cos()),
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
            let first_integrand = linear.pow(&m_) * angle.tan().pow(&n_);
            let second_integrand =
                linear.pow(&m_) * angle.sin() * angle.tan().pow(&n_ - 1) / (&a__ + &b__ * angle.cos());
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(Atom::num(1) / &a__, first)
                    + rubi_star(-&b__ / &a__, second)
        },
    ));
}

fn push_rules_rule_5042(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5042,
        source: "Int[(e_.+f_.*x_)^m_.*Sec[c_.+d_.*x_]^n_./(a_+b_.*Sin[c_.+d_.*x_]),x_Symbol] :=
          1/a \\[Star] Int[(e+f*x)^m*Sec[c+d*x]^(n+2),x] -
          1/b \\[Star] Int[(e+f*x)^m*Sec[c+d*x]^(n+1)*Tan[c+d*x],x] /;
        FreeQ[{a,b,c,d,e,f,n},x] && IGtQ[m,0] && EqQ[a^2-b^2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
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
            let first_integrand = linear.pow(&m_) * angle.sec().pow(&n_ + 2);
            let second_integrand = linear.pow(&m_) * angle.sec().pow(&n_ + 1) * angle.tan();
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(Atom::num(1) / &a__, first)
                    + rubi_star(-Atom::num(1) / &b__, second)
        },
    ));
}

fn push_rules_rule_5043(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5043,
        source: "Int[(e_.+f_.*x_)^m_.*Csc[c_.+d_.*x_]^n_./(a_+b_.*Cos[c_.+d_.*x_]),x_Symbol] :=
          1/a \\[Star] Int[(e+f*x)^m*Csc[c+d*x]^(n+2),x] -
          1/b \\[Star] Int[(e+f*x)^m*Csc[c+d*x]^(n+1)*Cot[c+d*x],x] /;
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
            let first_integrand = linear.pow(&m_) * angle.csc().pow(&n_ + 2);
            let second_integrand = linear.pow(&m_) * angle.csc().pow(&n_ + 1) * angle.cot();
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(Atom::num(1) / &a__, first)
                    + rubi_star(-Atom::num(1) / &b__, second)
        },
    ));
}

fn push_rules_rule_5044(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5044,
        source: "Int[(e_.+f_.*x_)^m_.*Sec[c_.+d_.*x_]^n_./(a_+b_.*Sin[c_.+d_.*x_]),x_Symbol] :=
          -b^2/(a^2-b^2) \\[Star] Int[(e+f*x)^m*Sec[c+d*x]^(n-2)/(a+b*Sin[c+d*x]),x] +
          1/(a^2-b^2) \\[Star] Int[(e+f*x)^m*Sec[c+d*x]^n*(a-b*Sin[c+d*x]),x] /;
        FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && NeQ[a^2-b^2,0] && IGtQ[n,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
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
            let discriminant = a__.pow(2) - b__.pow(2);
            let first_integrand =
                linear.pow(&m_) * angle.sec().pow(&n_ - 2) / (&a__ + &b__ * angle.sin());
            let second_integrand =
                linear.pow(&m_) * angle.sec().pow(&n_) * (&a__ - &b__ * angle.sin());
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(-b__.pow(2) / &discriminant, first)
                    + rubi_star(Atom::num(1) / discriminant, second)
        },
    ));
}

fn push_rules_rule_5045(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5045,
        source: "Int[(e_.+f_.*x_)^m_.*Csc[c_.+d_.*x_]^n_./(a_+b_.*Cos[c_.+d_.*x_]),x_Symbol] :=
          -b^2/(a^2-b^2) \\[Star] Int[(e+f*x)^m*Csc[c+d*x]^(n-2)/(a+b*Cos[c+d*x]),x] +
          1/(a^2-b^2) \\[Star] Int[(e+f*x)^m*Csc[c+d*x]^n*(a-b*Cos[c+d*x]),x] /;
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
            let discriminant = a__.pow(2) - b__.pow(2);
            let first_integrand =
                linear.pow(&m_) * angle.csc().pow(&n_ - 2) / (&a__ + &b__ * angle.cos());
            let second_integrand =
                linear.pow(&m_) * angle.csc().pow(&n_) * (&a__ - &b__ * angle.cos());
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(-b__.pow(2) / &discriminant, first)
                    + rubi_star(Atom::num(1) / discriminant, second)
        },
    ));
}

fn push_rules_rule_5046(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5046,
        source: "Int[(e_.+f_.*x_)^m_.*Csc[c_.+d_.*x_]^n_./(a_+b_.*Sin[c_.+d_.*x_]),x_Symbol] :=
          1/a \\[Star] Int[(e+f*x)^m*Csc[c+d*x]^n,x] - b/a \\[Star] Int[(e+f*x)^m*Csc[c+d*x]^(n-1)/(a+b*Sin[c+d*x]),x] /;
        FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && IGtQ[n,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (e__ + f__ * x_).pow(m_) * (c__ + d__ * x_).csc().pow(n_)
            / (a__ + b__ * (c__ + d__ * x_).sin()),
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
            let first_integrand = linear.pow(&m_) * angle.csc().pow(&n_);
            let second_integrand =
                linear.pow(&m_) * angle.csc().pow(&n_ - 1) / (&a__ + &b__ * angle.sin());
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(Atom::num(1) / &a__, first)
                    + rubi_star(-&b__ / &a__, second)
        },
    ));
}

fn push_rules_rule_5047(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5047,
        source: "Int[(e_.+f_.*x_)^m_.*Sec[c_.+d_.*x_]^n_./(a_+b_.*Cos[c_.+d_.*x_]),x_Symbol] :=
          1/a \\[Star] Int[(e+f*x)^m*Sec[c+d*x]^n,x] - b/a \\[Star] Int[(e+f*x)^m*Sec[c+d*x]^(n-1)/(a+b*Cos[c+d*x]),x] /;
        FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && IGtQ[n,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (e__ + f__ * x_).pow(m_) * (c__ + d__ * x_).sec().pow(n_)
            / (a__ + b__ * (c__ + d__ * x_).cos()),
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
            let first_integrand = linear.pow(&m_) * angle.sec().pow(&n_);
            let second_integrand =
                linear.pow(&m_) * angle.sec().pow(&n_ - 1) / (&a__ + &b__ * angle.cos());
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(Atom::num(1) / &a__, first)
                    + rubi_star(-&b__ / &a__, second)
        },
    ));
}

fn push_rules_rule_5048(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_f_, a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5048,
        source: "Int[(e_.+f_.*x_)^m_.*F_[c_.+d_.*x_]^n_./(a_+b_.*Sin[c_.+d_.*x_]),x_Symbol] :=
          Unintegrable[(e+f*x)^m*F[c+d*x]^n/(a+b*Sin[c+d*x]),x] /;
        FreeQ[{a,b,c,d,e,f,m,n},x] && TrigQ[F]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern: (e__ + f__ * x_).pow(m_) * capital_f_.call( c__ + d__ * x_).pow(n_)
            / (a__ + b__ * (c__ + d__ * x_).sin()),
        with: [e__, f__, m_, capital_f_, c__, d__, n_, a__, b__, x_],
        optional: [e__, f__, m_, c__, d__, n_, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_], x_)
                && rubi_trig_q(&capital_f_)
        },
        rhs: {
            let linear = &e__ + &f__ * x_;
            let angle = &c__ + &d__ * x_;
            let integrand = linear.pow(&m_) * rubi_function_head_symbol(&capital_f_).rubi_rhs().call( &angle).pow(&n_)
                / (&a__ + &b__ * angle.sin());

            rubi_unintegrable(integrand, x_)
        },
    ));
}

fn push_rules_rule_5049(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_f_, a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5049,
        source: "Int[(e_.+f_.*x_)^m_.*F_[c_.+d_.*x_]^n_./(a_+b_.*Cos[c_.+d_.*x_]),x_Symbol] :=
          Unintegrable[(e+f*x)^m*F[c+d*x]^n/(a+b*Cos[c+d*x]),x] /;
        FreeQ[{a,b,c,d,e,f,m,n},x] && TrigQ[F]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern: (e__ + f__ * x_).pow(m_) * capital_f_.call( c__ + d__ * x_).pow(n_)
            / (a__ + b__ * (c__ + d__ * x_).cos()),
        with: [e__, f__, m_, capital_f_, c__, d__, n_, a__, b__, x_],
        optional: [e__, f__, m_, c__, d__, n_, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_], x_)
                && rubi_trig_q(&capital_f_)
        },
        rhs: {
            let linear = &e__ + &f__ * x_;
            let angle = &c__ + &d__ * x_;
            let integrand = linear.pow(&m_) * rubi_function_head_symbol(&capital_f_).rubi_rhs().call( &angle).pow(&n_)
                / (&a__ + &b__ * angle.cos());

            rubi_unintegrable(integrand, x_)
        },
    ));
}

fn push_rules_rule_5050(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5050,
        source: "Int[(e_.+f_.*x_)^m_.*Cos[c_.+d_.*x_]^p_.*Sin[c_.+d_.*x_]^n_./(a_+b_.*Sin[c_.+d_.*x_]),x_Symbol] :=
          1/b \\[Star] Int[(e+f*x)^m*Cos[c+d*x]^p*Sin[c+d*x]^(n-1),x] -
          a/b \\[Star] Int[(e+f*x)^m*Cos[c+d*x]^p*Sin[c+d*x]^(n-1)/(a+b*Sin[c+d*x]),x] /;
        FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && IGtQ[n,0] && IGtQ[p,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (e__ + f__ * x_).pow(m_)
            * (c__ + d__ * x_).cos().pow(p_)
            * (c__ + d__ * x_).sin().pow(n_)
            / (a__ + b__ * (c__ + d__ * x_).sin()),
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
            let first_integrand = linear.pow(&m_) * angle.cos().pow(&p_) * angle.sin().pow(&n_ - 1);
            let second_integrand = linear.pow(&m_) * angle.cos().pow(&p_) * angle.sin().pow(&n_ - 1)
                / (&a__ + &b__ * angle.sin());
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(Atom::num(1) / &b__, first)
                    + rubi_star(-&a__ / &b__, second)
        },
    ));
}

fn push_rules_rule_5051(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5051,
        source: "Int[(e_.+f_.*x_)^m_.*Sin[c_.+d_.*x_]^p_.*Cos[c_.+d_.*x_]^n_./(a_+b_.*Cos[c_.+d_.*x_]),x_Symbol] :=
          1/b \\[Star] Int[(e+f*x)^m*Sin[c+d*x]^p*Cos[c+d*x]^(n-1),x] -
          a/b \\[Star] Int[(e+f*x)^m*Sin[c+d*x]^p*Cos[c+d*x]^(n-1)/(a+b*Cos[c+d*x]),x] /;
        FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && IGtQ[n,0] && IGtQ[p,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (e__ + f__ * x_).pow(m_)
            * (c__ + d__ * x_).sin().pow(p_)
            * (c__ + d__ * x_).cos().pow(n_)
            / (a__ + b__ * (c__ + d__ * x_).cos()),
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
            let first_integrand = linear.pow(&m_) * angle.sin().pow(&p_) * angle.cos().pow(&n_ - 1);
            let second_integrand = linear.pow(&m_) * angle.sin().pow(&p_) * angle.cos().pow(&n_ - 1)
                / (&a__ + &b__ * angle.cos());
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(Atom::num(1) / &b__, first)
                    + rubi_star(-&a__ / &b__, second)
        },
    ));
}

fn push_rules_rule_5052(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5052,
        source: "Int[(e_.+f_.*x_)^m_.*Cos[c_.+d_.*x_]^p_.*Tan[c_.+d_.*x_]^n_./(a_+b_.*Sin[c_.+d_.*x_]),x_Symbol] :=
          1/b \\[Star] Int[(e+f*x)^m*Cos[c+d*x]^(p-1)*Tan[c+d*x]^(n-1),x] -
          a/b \\[Star] Int[(e+f*x)^m*Cos[c+d*x]^(p-1)*Tan[c+d*x]^(n-1)/(a+b*Sin[c+d*x]),x] /;
        FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && IGtQ[n,0] && IGtQ[p,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (e__ + f__ * x_).pow(m_)
            * (c__ + d__ * x_).cos().pow(p_)
            * (c__ + d__ * x_).tan().pow(n_)
            / (a__ + b__ * (c__ + d__ * x_).sin()),
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
            let first_integrand = linear.pow(&m_) * angle.cos().pow(&p_ - 1) * angle.tan().pow(&n_ - 1);
            let second_integrand = linear.pow(&m_)
                * angle.cos().pow(&p_ - 1)
                * angle.tan().pow(&n_ - 1)
                / (&a__ + &b__ * angle.sin());
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(Atom::num(1) / &b__, first)
                    + rubi_star(-&a__ / &b__, second)
        },
    ));
}

fn push_rules_rule_5053(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5053,
        source: "Int[(e_.+f_.*x_)^m_.*Sin[c_.+d_.*x_]^p_.*Cot[c_.+d_.*x_]^n_./(a_+b_.*Cos[c_.+d_.*x_]),x_Symbol] :=
          1/b \\[Star] Int[(e+f*x)^m*Sin[c+d*x]^(p-1)*Cot[c+d*x]^(n-1),x] -
          a/b \\[Star] Int[(e+f*x)^m*Sin[c+d*x]^(p-1)*Cot[c+d*x]^(n-1)/(a+b*Cos[c+d*x]),x] /;
        FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && IGtQ[n,0] && IGtQ[p,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (e__ + f__ * x_).pow(m_)
            * (c__ + d__ * x_).sin().pow(p_)
            * (c__ + d__ * x_).cot().pow(n_)
            / (a__ + b__ * (c__ + d__ * x_).cos()),
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
            let first_integrand = linear.pow(&m_) * angle.sin().pow(&p_ - 1) * angle.cot().pow(&n_ - 1);
            let second_integrand = linear.pow(&m_)
                * angle.sin().pow(&p_ - 1)
                * angle.cot().pow(&n_ - 1)
                / (&a__ + &b__ * angle.cos());
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(Atom::num(1) / &b__, first)
                    + rubi_star(-&a__ / &b__, second)
        },
    ));
}

fn push_rules_rule_5054(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5054,
        source: "Int[(e_.+f_.*x_)^m_.*Cos[c_.+d_.*x_]^p_.*Cot[c_.+d_.*x_]^n_./(a_+b_.*Sin[c_.+d_.*x_]),x_Symbol] :=
          1/a \\[Star] Int[(e+f*x)^m*Cos[c+d*x]^p*Cot[c+d*x]^n,x] -
          b/a \\[Star] Int[(e+f*x)^m*Cos[c+d*x]^(p+1)*Cot[c+d*x]^(n-1)/(a+b*Sin[c+d*x]),x] /;
        FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && IGtQ[n,0] && IGtQ[p,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (e__ + f__ * x_).pow(m_)
            * (c__ + d__ * x_).cos().pow(p_)
            * (c__ + d__ * x_).cot().pow(n_)
            / (a__ + b__ * (c__ + d__ * x_).sin()),
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
            let first_integrand = linear.pow(&m_) * angle.cos().pow(&p_) * angle.cot().pow(&n_);
            let second_integrand = linear.pow(&m_)
                * angle.cos().pow(&p_ + 1)
                * angle.cot().pow(&n_ - 1)
                / (&a__ + &b__ * angle.sin());
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(Atom::num(1) / &a__, first)
                    + rubi_star(-&b__ / &a__, second)
        },
    ));
}

fn push_rules_rule_5055(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5055,
        source: "Int[(e_.+f_.*x_)^m_.*Sin[c_.+d_.*x_]^p_.*Tan[c_.+d_.*x_]^n_./(a_+b_.*Cos[c_.+d_.*x_]),x_Symbol] :=
          1/a \\[Star] Int[(e+f*x)^m*Sin[c+d*x]^p*Tan[c+d*x]^n,x] -
          b/a \\[Star] Int[(e+f*x)^m*Sin[c+d*x]^(p+1)*Tan[c+d*x]^(n-1)/(a+b*Cos[c+d*x]),x] /;
        FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && IGtQ[n,0] && IGtQ[p,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (e__ + f__ * x_).pow(m_)
            * (c__ + d__ * x_).sin().pow(p_)
            * (c__ + d__ * x_).tan().pow(n_)
            / (a__ + b__ * (c__ + d__ * x_).cos()),
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
            let first_integrand = linear.pow(&m_) * angle.sin().pow(&p_) * angle.tan().pow(&n_);
            let second_integrand = linear.pow(&m_)
                * angle.sin().pow(&p_ + 1)
                * angle.tan().pow(&n_ - 1)
                / (&a__ + &b__ * angle.cos());
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(Atom::num(1) / &a__, first)
                    + rubi_star(-&b__ / &a__, second)
        },
    ));
}

fn push_rules_rule_5056(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5056,
        source: "Int[(e_.+f_.*x_)^m_.*Cos[c_.+d_.*x_]^p_.*Csc[c_.+d_.*x_]^n_./(a_+b_.*Sin[c_.+d_.*x_]),x_Symbol] :=
          1/a \\[Star] Int[(e+f*x)^m*Cos[c+d*x]^p*Csc[c+d*x]^n,x] -
          b/a \\[Star] Int[(e+f*x)^m*Cos[c+d*x]^p*Csc[c+d*x]^(n-1)/(a+b*Sin[c+d*x]),x] /;
        FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && IGtQ[n,0] && IGtQ[p,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (e__ + f__ * x_).pow(m_)
            * (c__ + d__ * x_).cos().pow(p_)
            * (c__ + d__ * x_).csc().pow(n_)
            / (a__ + b__ * (c__ + d__ * x_).sin()),
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
            let first_integrand = linear.pow(&m_) * angle.cos().pow(&p_) * angle.csc().pow(&n_);
            let second_integrand = linear.pow(&m_) * angle.cos().pow(&p_) * angle.csc().pow(&n_ - 1)
                / (&a__ + &b__ * angle.sin());
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(Atom::num(1) / &a__, first)
                    + rubi_star(-&b__ / &a__, second)
        },
    ));
}

fn push_rules_rule_5057(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5057,
        source: "Int[(e_.+f_.*x_)^m_.*Sin[c_.+d_.*x_]^p_.*Sec[c_.+d_.*x_]^n_./(a_+b_.*Cos[c_.+d_.*x_]),x_Symbol] :=
          1/a \\[Star] Int[(e+f*x)^m*Sin[c+d*x]^p*Sec[c+d*x]^n,x] -
          b/a \\[Star] Int[(e+f*x)^m*Sin[c+d*x]^p*Sec[c+d*x]^(n-1)/(a+b*Cos[c+d*x]),x] /;
        FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && IGtQ[n,0] && IGtQ[p,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (e__ + f__ * x_).pow(m_)
            * (c__ + d__ * x_).sin().pow(p_)
            * (c__ + d__ * x_).sec().pow(n_)
            / (a__ + b__ * (c__ + d__ * x_).cos()),
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
            let first_integrand = linear.pow(&m_) * angle.sin().pow(&p_) * angle.sec().pow(&n_);
            let second_integrand = linear.pow(&m_) * angle.sin().pow(&p_) * angle.sec().pow(&n_ - 1)
                / (&a__ + &b__ * angle.cos());
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(Atom::num(1) / &a__, first)
                    + rubi_star(-&b__ / &a__, second)
        },
    ));
}

fn push_rules_rule_5058(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_f_, a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5058,
        source: "Int[(e_.+f_.*x_)^m_.*Cos[c_.+d_.*x_]^p_.*F_[c_.+d_.*x_]^n_./(a_+b_.*Sin[c_.+d_.*x_]),x_Symbol] :=
          Unintegrable[(e+f*x)^m*Cos[c+d*x]^p*F[c+d*x]^n/(a+b*Sin[c+d*x]),x] /;
        FreeQ[{a,b,c,d,e,f,m,n,p},x] && TrigQ[F]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern: (e__ + f__ * x_).pow(m_)
            * (c__ + d__ * x_).cos().pow(p_)
            * capital_f_.call( c__ + d__ * x_).pow(n_)
            / (a__ + b__ * (c__ + d__ * x_).sin()),
        with: [e__, f__, m_, c__, d__, p_, capital_f_, n_, a__, b__, x_],
        optional: [e__, f__, m_, c__, d__, p_, n_, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_, p_], x_)
                && rubi_trig_q(&capital_f_)
        },
        rhs: {
            let linear = &e__ + &f__ * x_;
            let angle = &c__ + &d__ * x_;
            let integrand = linear.pow(&m_)
                * angle.cos().pow(&p_)
                * rubi_function_head_symbol(&capital_f_).rubi_rhs().call( &angle).pow(&n_)
                / (&a__ + &b__ * angle.sin());

            rubi_unintegrable(integrand, x_)
        },
    ));
}

fn push_rules_rule_5059(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_f_, a__, b__, c__, d__, e__, f__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5059,
        source: "Int[(e_.+f_.*x_)^m_.*Sin[c_.+d_.*x_]^p_.*F_[c_.+d_.*x_]^n_./(a_+b_.*Cos[c_.+d_.*x_]),x_Symbol] :=
          Unintegrable[(e+f*x)^m*Sin[c+d*x]^p*F[c+d*x]^n/(a+b*Cos[c+d*x]),x] /;
        FreeQ[{a,b,c,d,e,f,m,n},x] && TrigQ[F]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern: (e__ + f__ * x_).pow(m_)
            * (c__ + d__ * x_).sin().pow(p_)
            * capital_f_.call( c__ + d__ * x_).pow(n_)
            / (a__ + b__ * (c__ + d__ * x_).cos()),
        with: [e__, f__, m_, c__, d__, p_, capital_f_, n_, a__, b__, x_],
        optional: [e__, f__, m_, c__, d__, p_, n_, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_], x_)
                && rubi_trig_q(&capital_f_)
        },
        rhs: {
            let linear = &e__ + &f__ * x_;
            let angle = &c__ + &d__ * x_;
            let integrand = linear.pow(&m_)
                * angle.sin().pow(&p_)
                * rubi_function_head_symbol(&capital_f_).rubi_rhs().call( &angle).pow(&n_)
                / (&a__ + &b__ * angle.cos());

            rubi_unintegrable(integrand, x_)
        },
    ));
}

fn push_rules_rule_5060(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_f_, a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5060,
        source: "Int[(e_.+f_.*x_)^m_.*F_[c_.+d_.*x_]^n_./(a_+b_.*Sec[c_.+d_.*x_]),x_Symbol] :=
          Int[(e+f*x)^m*Cos[c+d*x]*F[c+d*x]^n/(b+a*Cos[c+d*x]),x] /;
        FreeQ[{a,b,c,d,e,f},x] && TrigQ[F] && IntegersQ[m,n]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: (e__ + f__ * x_).pow(m_) * capital_f_.call( c__ + d__ * x_).pow(n_)
            / (a__ + b__ * (c__ + d__ * x_).sec()),
        with: [e__, f__, m_, capital_f_, c__, d__, n_, a__, b__, x_],
        optional: [e__, f__, m_, c__, d__, n_, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && rubi_trig_q(&capital_f_)
                && integersq!([m_, n_])
        },
        rhs: {
            let linear = &e__ + &f__ * x_;
            let angle = &c__ + &d__ * x_;
            let integrand = linear.pow(&m_)
                * angle.cos()
                * rubi_function_head_symbol(&capital_f_).rubi_rhs().call( &angle).pow(&n_)
                / (&b__ + &a__ * angle.cos());

            rubi_rhs_int(&integrand, x_)
        },
    ));
}

fn push_rules_rule_5061(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_f_, a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5061,
        source: "Int[(e_.+f_.*x_)^m_.*F_[c_.+d_.*x_]^n_./(a_+b_.*Csc[c_.+d_.*x_]),x_Symbol] :=
          Int[(e+f*x)^m*Sin[c+d*x]*F[c+d*x]^n/(b+a*Sin[c+d*x]),x] /;
        FreeQ[{a,b,c,d,e,f},x] && TrigQ[F] && IntegersQ[m,n]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: (e__ + f__ * x_).pow(m_) * capital_f_.call( c__ + d__ * x_).pow(n_)
            / (a__ + b__ * (c__ + d__ * x_).csc()),
        with: [e__, f__, m_, capital_f_, c__, d__, n_, a__, b__, x_],
        optional: [e__, f__, m_, c__, d__, n_, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && rubi_trig_q(&capital_f_)
                && integersq!([m_, n_])
        },
        rhs: {
            let linear = &e__ + &f__ * x_;
            let angle = &c__ + &d__ * x_;
            let integrand = linear.pow(&m_)
                * angle.sin()
                * rubi_function_head_symbol(&capital_f_).rubi_rhs().call( &angle).pow(&n_)
                / (&b__ + &a__ * angle.sin());

            rubi_rhs_int(&integrand, x_)
        },
    ));
}

fn push_rules_rule_5062(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        capital_f_, capital_g_, a__, b__, c__, d__, e__, f__, m_, n_, p_, x_
    );
    rules.push(rubi_rule!(
        order: 5062,
        source: "Int[(e_.+f_.*x_)^m_.*F_[c_.+d_.*x_]^n_.*G_[c_.+d_.*x_]^p_./(a_+b_.*Sec[c_.+d_.*x_]),x_Symbol] :=
          Int[(e+f*x)^m*Cos[c+d*x]*F[c+d*x]^n*G[c+d*x]^p/(b+a*Cos[c+d*x]),x] /;
        FreeQ[{a,b,c,d,e,f},x] && TrigQ[F] && TrigQ[G] && IntegersQ[m,n,p]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: (e__ + f__ * x_).pow(m_)
            * capital_f_.call( c__ + d__ * x_).pow(n_)
            * capital_g_.call( c__ + d__ * x_).pow(p_)
            / (a__ + b__ * (c__ + d__ * x_).sec()),
        with: [e__, f__, m_, capital_f_, c__, d__, n_, capital_g_, p_, a__, b__, x_],
        optional: [e__, f__, m_, c__, d__, n_, p_, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && rubi_trig_q(&capital_f_)
                && rubi_trig_q(&capital_g_)
                && integersq!([m_, n_, p_])
        },
        rhs: {
            let linear = &e__ + &f__ * x_;
            let angle = &c__ + &d__ * x_;
            let integrand = linear.pow(&m_)
                * angle.cos()
                * rubi_function_head_symbol(&capital_f_).rubi_rhs().call( &angle).pow(&n_)
                * rubi_function_head_symbol(&capital_g_).rubi_rhs().call( &angle).pow(&p_)
                / (&b__ + &a__ * angle.cos());

            rubi_rhs_int(&integrand, x_)
        },
    ));
}

fn push_rules_rule_5063(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        capital_f_, capital_g_, a__, b__, c__, d__, e__, f__, m_, n_, p_, x_
    );
    rules.push(rubi_rule!(
        order: 5063,
        source: "Int[(e_.+f_.*x_)^m_.*F_[c_.+d_.*x_]^n_.*G_[c_.+d_.*x_]^p_./(a_+b_.*Csc[c_.+d_.*x_]),x_Symbol] :=
          Int[(e+f*x)^m*Sin[c+d*x]*F[c+d*x]^n*G[c+d*x]^p/(b+a*Sin[c+d*x]),x] /;
        FreeQ[{a,b,c,d,e,f},x] && TrigQ[F] && TrigQ[G] && IntegersQ[m,n,p]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: (e__ + f__ * x_).pow(m_)
            * capital_f_.call( c__ + d__ * x_).pow(n_)
            * capital_g_.call( c__ + d__ * x_).pow(p_)
            / (a__ + b__ * (c__ + d__ * x_).csc()),
        with: [e__, f__, m_, capital_f_, c__, d__, n_, capital_g_, p_, a__, b__, x_],
        optional: [e__, f__, m_, c__, d__, n_, p_, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && rubi_trig_q(&capital_f_)
                && rubi_trig_q(&capital_g_)
                && integersq!([m_, n_, p_])
        },
        rhs: {
            let linear = &e__ + &f__ * x_;
            let angle = &c__ + &d__ * x_;
            let integrand = linear.pow(&m_)
                * angle.sin()
                * rubi_function_head_symbol(&capital_f_).rubi_rhs().call( &angle).pow(&n_)
                * rubi_function_head_symbol(&capital_g_).rubi_rhs().call( &angle).pow(&p_)
                / (&b__ + &a__ * angle.sin());

            rubi_rhs_int(&integrand, x_)
        },
    ));
}

fn push_rules_rule_5064(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 5064,
        source: "Int[Sin[a_.+b_.*x_]^p_.*Sin[c_.+d_.*x_]^q_.,x_Symbol] :=
          1/2^(p+q) \\[Star] Int[ExpandIntegrand[(I/E^(I*(c+d*x))-I*E^(I*(c+d*x)))^q,(I/E^(I*(a+b*x))-I*E^(I*(a+b*x)))^p,x],x] /;
        FreeQ[{a,b,c,d,q},x] && IGtQ[p,0] && Not[IntegerQ[q]]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (a__ + b__ * x_).sin().pow(p_) * (c__ + d__ * x_).sin().pow(q_),
        with: [a__, b__, p_, c__, d__, q_, x_],
        optional: [a__, b__, p_, c__, d__, q_],
        when: {
            freeq!([a__, b__, c__, d__, q_], x_)
                && igtq!(p_, 0)
                && !integerq!(q_)
        },
        rhs: {
            let i = Atom::i();
            let first_angle = &a__ + &b__ * x_;
            let second_angle = &c__ + &d__ * x_;
            let first_exp = (&i * first_angle).exp();
            let second_exp = (&i * second_angle).exp();
            let first = (&i / &second_exp - &i * second_exp).pow(&q_);
            let second = (&i / &first_exp - &i * first_exp).pow(&p_);
            let expanded = rubi_expand_integrand(&(first * second), x_);
            let recursive = rubi_rhs_int(&expanded, x_);

            rubi_star(Atom::num(1) / Atom::num(2).pow(&p_ + &q_), recursive)
        },
    ));
}

fn push_rules_rule_5065(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 5065,
        source: "Int[Cos[a_.+b_.*x_]^p_.*Cos[c_.+d_.*x_]^q_.,x_Symbol] :=
          1/2^(p+q) \\[Star] Int[ExpandIntegrand[(E^(-I*(c+d*x))+E^(I*(c+d*x)))^q,(E^(-I*(a+b*x))+E^(I*(a+b*x)))^p,x],x] /;
        FreeQ[{a,b,c,d,q},x] && IGtQ[p,0] && Not[IntegerQ[q]]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (a__ + b__ * x_).cos().pow(p_) * (c__ + d__ * x_).cos().pow(q_),
        with: [a__, b__, p_, c__, d__, q_, x_],
        optional: [a__, b__, p_, c__, d__, q_],
        when: {
            freeq!([a__, b__, c__, d__, q_], x_)
                && igtq!(p_, 0)
                && !integerq!(q_)
        },
        rhs: {
            let i = Atom::i();
            let first_angle = &a__ + &b__ * x_;
            let second_angle = &c__ + &d__ * x_;
            let first = ((-&i * &second_angle).exp() + (&i * second_angle).exp()).pow(&q_);
            let second = ((-&i * &first_angle).exp() + (&i * first_angle).exp()).pow(&p_);
            let expanded = rubi_expand_integrand(&(first * second), x_);
            let recursive = rubi_rhs_int(&expanded, x_);

            rubi_star(Atom::num(1) / Atom::num(2).pow(&p_ + &q_), recursive)
        },
    ));
}

fn push_rules_rule_5066(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 5066,
        source: "Int[Sin[a_.+b_.*x_]^p_.*Cos[c_.+d_.*x_]^q_.,x_Symbol] :=
          1/2^(p+q) \\[Star] Int[ExpandIntegrand[(E^(-I*(c+d*x))+E^(I*(c+d*x)))^q,(I/E^(I*(a+b*x))-I*E^(I*(a+b*x)))^p,x],x] /;
        FreeQ[{a,b,c,d,q},x] && IGtQ[p,0] && Not[IntegerQ[q]]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (a__ + b__ * x_).sin().pow(p_) * (c__ + d__ * x_).cos().pow(q_),
        with: [a__, b__, p_, c__, d__, q_, x_],
        optional: [a__, b__, p_, c__, d__, q_],
        when: {
            freeq!([a__, b__, c__, d__, q_], x_)
                && igtq!(p_, 0)
                && !integerq!(q_)
        },
        rhs: {
            let i = Atom::i();
            let first_angle = &a__ + &b__ * x_;
            let second_angle = &c__ + &d__ * x_;
            let first = ((-&i * &second_angle).exp() + (&i * second_angle).exp()).pow(&q_);
            let first_exp = (&i * first_angle).exp();
            let second = (&i / &first_exp - &i * first_exp).pow(&p_);
            let expanded = rubi_expand_integrand(&(first * second), x_);
            let recursive = rubi_rhs_int(&expanded, x_);

            rubi_star(Atom::num(1) / Atom::num(2).pow(&p_ + &q_), recursive)
        },
    ));
}

fn push_rules_rule_5067(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 5067,
        source: "Int[Cos[a_.+b_.*x_]^p_.*Sin[c_.+d_.*x_]^q_.,x_Symbol] :=
          1/2^(p+q) \\[Star] Int[ExpandIntegrand[(I/E^(I*(c+d*x))-I*E^(I*(c+d*x)))^q,(E^(-I*(a+b*x))+E^(I*(a+b*x)))^p,x],x] /;
        FreeQ[{a,b,c,d,q},x] && IGtQ[p,0] && Not[IntegerQ[q]]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (a__ + b__ * x_).cos().pow(p_) * (c__ + d__ * x_).sin().pow(q_),
        with: [a__, b__, p_, c__, d__, q_, x_],
        optional: [a__, b__, p_, c__, d__, q_],
        when: {
            freeq!([a__, b__, c__, d__, q_], x_)
                && igtq!(p_, 0)
                && !integerq!(q_)
        },
        rhs: {
            let i = Atom::i();
            let first_angle = &a__ + &b__ * x_;
            let second_angle = &c__ + &d__ * x_;
            let second_exp = (&i * second_angle).exp();
            let first = (&i / &second_exp - &i * second_exp).pow(&q_);
            let second = ((-&i * &first_angle).exp() + (&i * first_angle).exp()).pow(&p_);
            let expanded = rubi_expand_integrand(&(first * second), x_);
            let recursive = rubi_rhs_int(&expanded, x_);

            rubi_star(Atom::num(1) / Atom::num(2).pow(&p_ + &q_), recursive)
        },
    ));
}

fn push_rules_rule_5068(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 5068,
        source: "Int[Sin[a_.+b_.*x_]*Tan[c_.+d_.*x_],x_Symbol] :=
          Int[E^(-I*(a+b*x))/2 - E^(I*(a+b*x))/2 - E^(-I*(a+b*x))/(1+E^(2*I*(c+d*x))) + E^(I*(a+b*x))/(1+E^(2*I*(c+d*x))),x] /;
        FreeQ[{a,b,c,d},x] && NeQ[b^2-d^2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (a__ + b__ * x_).sin() * (c__ + d__ * x_).tan(),
        with: [a__, b__, c__, d__, x_],
        optional: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_) && neq!(b__.pow(2) - d__.pow(2), 0)
        },
        rhs: {
            let i = Atom::i();
            let two = Atom::num(2);
            let first_angle = &a__ + &b__ * x_;
            let second_angle = &c__ + &d__ * x_;
            let first_exp_neg = (-&i * &first_angle).exp();
            let first_exp_pos = (&i * first_angle).exp();
            let denominator = Atom::num(1) + (Atom::num(2) * &i * second_angle).exp();
            let integrand = &first_exp_neg / &two - &first_exp_pos / &two - &first_exp_neg / &denominator
                + &first_exp_pos / denominator;

            rubi_rhs_int(&integrand, x_)
        },
    ));
}

fn push_rules_rule_5069(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 5069,
        source: "Int[Cos[a_.+b_.*x_]*Cot[c_.+d_.*x_],x_Symbol] :=
          Int[I*E^(-I*(a+b*x))/2 + I*E^(I*(a+b*x))/2 - I*E^(-I*(a+b*x))/(1-E^(2*I*(c+d*x))) - I*E^(I*(a+b*x))/(1-E^(2*I*(c+d*x))),x] /;
        FreeQ[{a,b,c,d},x] && NeQ[b^2-d^2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (a__ + b__ * x_).cos() * (c__ + d__ * x_).cot(),
        with: [a__, b__, c__, d__, x_],
        optional: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_) && neq!(b__.pow(2) - d__.pow(2), 0)
        },
        rhs: {
            let i = Atom::i();
            let two = Atom::num(2);
            let first_angle = &a__ + &b__ * x_;
            let second_angle = &c__ + &d__ * x_;
            let first_exp_neg = (-&i * &first_angle).exp();
            let first_exp_pos = (&i * first_angle).exp();
            let denominator = Atom::num(1) - (Atom::num(2) * &i * second_angle).exp();
            let integrand = &i * &first_exp_neg / &two + &i * &first_exp_pos / &two
                - &i * &first_exp_neg / &denominator
                - &i * &first_exp_pos / denominator;

            rubi_rhs_int(&integrand, x_)
        },
    ));
}

fn push_rules_rule_5070(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 5070,
        source: "Int[Sin[a_.+b_.*x_]*Cot[c_.+d_.*x_],x_Symbol] :=
          Int[-E^(-I*(a+b*x))/2 + E^(I*(a+b*x))/2 + E^(-I*(a+b*x))/(1-E^(2*I*(c+d*x))) - E^(I*(a+b*x))/(1-E^(2*I*(c+d*x))),x] /;
        FreeQ[{a,b,c,d},x] && NeQ[b^2-d^2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (a__ + b__ * x_).sin() * (c__ + d__ * x_).cot(),
        with: [a__, b__, c__, d__, x_],
        optional: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_) && neq!(b__.pow(2) - d__.pow(2), 0)
        },
        rhs: {
            let i = Atom::i();
            let two = Atom::num(2);
            let first_angle = &a__ + &b__ * x_;
            let second_angle = &c__ + &d__ * x_;
            let first_exp_neg = (-&i * &first_angle).exp();
            let first_exp_pos = (&i * first_angle).exp();
            let denominator = Atom::num(1) - (Atom::num(2) * &i * second_angle).exp();
            let integrand = -&first_exp_neg / &two + &first_exp_pos / &two
                + &first_exp_neg / &denominator
                - &first_exp_pos / denominator;

            rubi_rhs_int(&integrand, x_)
        },
    ));
}

fn push_rules_rule_5071(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 5071,
        source: "Int[Cos[a_.+b_.*x_]*Tan[c_.+d_.*x_],x_Symbol] :=
          Int[-I*E^(-I*(a+b*x))/2 - I*E^(I*(a+b*x))/2 + I*E^(-I*(a+b*x))/(1+E^(2*I*(c+d*x))) + I*E^(I*(a+b*x))/(1+E^(2*I*(c+d*x))),x] /;
        FreeQ[{a,b,c,d},x] && NeQ[b^2-d^2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (a__ + b__ * x_).cos() * (c__ + d__ * x_).tan(),
        with: [a__, b__, c__, d__, x_],
        optional: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_) && neq!(b__.pow(2) - d__.pow(2), 0)
        },
        rhs: {
            let i = Atom::i();
            let two = Atom::num(2);
            let first_angle = &a__ + &b__ * x_;
            let second_angle = &c__ + &d__ * x_;
            let first_exp_neg = (-&i * &first_angle).exp();
            let first_exp_pos = (&i * first_angle).exp();
            let denominator = Atom::num(1) + (Atom::num(2) * &i * second_angle).exp();
            let integrand = -&i * &first_exp_neg / &two - &i * &first_exp_pos / &two
                + &i * &first_exp_neg / &denominator
                + &i * &first_exp_pos / denominator;

            rubi_rhs_int(&integrand, x_)
        },
    ));
}

fn push_rules_rule_5072(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, c__, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 5072,
        source: "Int[Sin[a_./(c_.+d_.*x_)]^n_.,x_Symbol] :=
          -1/d \\[Star] Subst[Int[Sin[a*x]^n/x^2,x],x,1/(c+d*x)] /;
        FreeQ[{a,c,d},x] && IGtQ[n,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (a__ / (c__ + d__ * x_)).sin().pow(n_),
        with: [a__, c__, d__, n_, x_],
        optional: [a__, c__, d__, n_],
        when: { freeq!([a__, c__, d__], x_) && igtq!(n_, 0) },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub = Atom::var(substitution_symbol);
            let transformed_integrand = (&a__ * &sub).sin().pow(&n_) / sub.pow(2);
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);
            let base = Atom::num(1) / (&c__ + &d__ * x_);

            let substituted = rubi_subst(&transformed, substitution_symbol, base);

            rubi_star(-Atom::num(1) / &d__, substituted)
        },
    ));
}

fn push_rules_rule_5073(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, c__, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 5073,
        source: "Int[Cos[a_./(c_.+d_.*x_)]^n_.,x_Symbol] :=
          -1/d \\[Star] Subst[Int[Cos[a*x]^n/x^2,x],x,1/(c+d*x)] /;
        FreeQ[{a,c,d},x] && IGtQ[n,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (a__ / (c__ + d__ * x_)).cos().pow(n_),
        with: [a__, c__, d__, n_, x_],
        optional: [a__, c__, d__, n_],
        when: { freeq!([a__, c__, d__], x_) && igtq!(n_, 0) },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub = Atom::var(substitution_symbol);
            let transformed_integrand = (&a__ * &sub).cos().pow(&n_) / sub.pow(2);
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);
            let base = Atom::num(1) / (&c__ + &d__ * x_);

            let substituted = rubi_subst(&transformed, substitution_symbol, base);

            rubi_star(-Atom::num(1) / &d__, substituted)
        },
    ));
}

fn push_rules_rule_5074(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 5074,
        source: "Int[Sin[e_.*(a_.+b_.*x_)/(c_.+d_.*x_)]^n_.,x_Symbol] :=
          -1/d \\[Star] Subst[Int[Sin[b*e/d-e*(b*c-a*d)*x/d]^n/x^2,x],x,1/(c+d*x)] /;
        FreeQ[{a,b,c,d},x] && IGtQ[n,0] && NeQ[b*c-a*d,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (e__ * (a__ + b__ * x_) / (c__ + d__ * x_)).sin().pow(n_),
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
            let transformed_integrand = argument.sin().pow(&n_) / sub.pow(2);
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);
            let base = Atom::num(1) / (&c__ + &d__ * x_);

            let substituted = rubi_subst(&transformed, substitution_symbol, base);

            rubi_star(-Atom::num(1) / &d__, substituted)
        },
    ));
}

fn push_rules_rule_5075(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, n_, x_);
    rules.push(rubi_rule!(
        order: 5075,
        source: "Int[Cos[e_.*(a_.+b_.*x_)/(c_.+d_.*x_)]^n_.,x_Symbol] :=
          -1/d \\[Star] Subst[Int[Cos[b*e/d-e*(b*c-a*d)*x/d]^n/x^2,x],x,1/(c+d*x)] /;
        FreeQ[{a,b,c,d},x] && IGtQ[n,0] && NeQ[b*c-a*d,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (e__ * (a__ + b__ * x_) / (c__ + d__ * x_)).cos().pow(n_),
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
            let transformed_integrand = argument.cos().pow(&n_) / sub.pow(2);
            let transformed = rubi_rhs_int(&transformed_integrand, substitution_symbol);
            let base = Atom::num(1) / (&c__ + &d__ * x_);

            let substituted = rubi_subst(&transformed, substitution_symbol, base);

            rubi_star(-Atom::num(1) / &d__, substituted)
        },
    ));
}

fn push_rules_rule_5076(rules: &mut Vec<RubiRule>) {
    rubi_symb!(n_, u__);
    rules.push(rubi_rule!(
        order: 5076,
        source: "Int[Sin[u_]^n_.,x_Symbol] :=
          Module[{lst=QuotientOfLinearsParts[u,x]},
          Int[Sin[(lst[[1]]+lst[[2]]*x)/(lst[[3]]+lst[[4]]*x)]^n,x]] /;
        IGtQ[n,0] && QuotientOfLinearsQ[u,x]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: (Atom::var(u__)).sin().pow(n_),
        with: [u__, n_, x_],
        optional: [n_],
        when: { igtq!(n_, 0) && rubi_quotient_of_linears_coefficients(&u__, x_).is_some() },
        rhs: {
            let (a, b, c, d) = rubi_quotient_of_linears_coefficients(&u__, x_).rubi_rhs();
            let integrand = ((a + b * x_) / (c + d * x_)).sin().pow(&n_);

            rubi_rhs_int(&integrand, x_)
        },
    ));
}

fn push_rules_rule_5077(rules: &mut Vec<RubiRule>) {
    rubi_symb!(n_, u__);
    rules.push(rubi_rule!(
        order: 5077,
        source: "Int[Cos[u_]^n_.,x_Symbol] :=
          Module[{lst=QuotientOfLinearsParts[u,x]},
          Int[Cos[(lst[[1]]+lst[[2]]*x)/(lst[[3]]+lst[[4]]*x)]^n,x]] /;
        IGtQ[n,0] && QuotientOfLinearsQ[u,x]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: (Atom::var(u__)).cos().pow(n_),
        with: [u__, n_, x_],
        optional: [n_],
        when: { igtq!(n_, 0) && rubi_quotient_of_linears_coefficients(&u__, x_).is_some() },
        rhs: {
            let (a, b, c, d) = rubi_quotient_of_linears_coefficients(&u__, x_).rubi_rhs();
            let integrand = ((a + b * x_) / (c + d * x_)).cos().pow(&n_);

            rubi_rhs_int(&integrand, x_)
        },
    ));
}

fn push_rules_rule_5078(rules: &mut Vec<RubiRule>) {
    rubi_symb!(p_, q_, u__, v_, w_);
    rules.push(rubi_rule!(
        order: 5078,
        source: "Int[u_.*Sin[v_]^p_.*Sin[w_]^q_.,x_Symbol] :=
          Int[u*Sin[v]^(p+q),x] /;
        EqQ[w,v]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: u__ * (Atom::var(v_)).sin().pow(p_) * (Atom::var(w_)).sin().pow(q_),
        with: [u__, v_, p_, w_, q_, x_],
        optional: [u__, p_, q_],
        when: { eqq!(w_, v_) },
        rhs: {
            let integrand = &u__ * v_.sin().pow(&p_ + &q_);

            rubi_rhs_int(&integrand, x_)
        },
    ));
}

fn push_rules_rule_5079(rules: &mut Vec<RubiRule>) {
    rubi_symb!(p_, q_, u__, v_, w_);
    rules.push(rubi_rule!(
        order: 5079,
        source: "Int[u_.*Cos[v_]^p_.*Cos[w_]^q_.,x_Symbol] :=
          Int[u*Cos[v]^(p+q),x] /;
        EqQ[w,v]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: u__ * (Atom::var(v_)).cos().pow(p_) * (Atom::var(w_)).cos().pow(q_),
        with: [u__, v_, p_, w_, q_, x_],
        optional: [u__, p_, q_],
        when: { eqq!(w_, v_) },
        rhs: {
            let integrand = &u__ * v_.cos().pow(&p_ + &q_);

            rubi_rhs_int(&integrand, x_)
        },
    ));
}

fn push_rules_rule_5080(rules: &mut Vec<RubiRule>) {
    rubi_symb!(p_, q_, v_, w_);
    rules.push(rubi_rule!(
        order: 5080,
        source: "Int[Sin[v_]^p_.*Sin[w_]^q_.,x_Symbol] :=
          Int[ExpandTrigReduce[Sin[v]^p*Sin[w]^q,x],x] /;
        (PolynomialQ[v,x] && PolynomialQ[w,x] || BinomialQ[{v,w},x] && IndependentQ[Cancel[v/w],x]) && IGtQ[p,0] && IGtQ[q,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (Atom::var(v_)).sin().pow(p_) * (Atom::var(w_)).sin().pow(q_),
        with: [v_, p_, w_, q_, x_],
        optional: [p_, q_],
        when: {
            rubi_expand_trig_reduce_angles_q(&v_, &w_, x_) && igtq!(p_, 0) && igtq!(q_, 0)
        },
        rhs: {
            let product = v_.sin().pow(&p_) * w_.sin().pow(&q_);
            let expanded = rubi_expand_trig_reduce(&Atom::num(1), &product, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_5081(rules: &mut Vec<RubiRule>) {
    rubi_symb!(p_, q_, v_, w_);
    rules.push(rubi_rule!(
        order: 5081,
        source: "Int[Cos[v_]^p_.*Cos[w_]^q_.,x_Symbol] :=
          Int[ExpandTrigReduce[Cos[v]^p*Cos[w]^q,x],x] /;
        (PolynomialQ[v,x] && PolynomialQ[w,x] || BinomialQ[{v,w},x] && IndependentQ[Cancel[v/w],x]) && IGtQ[p,0] && IGtQ[q,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (Atom::var(v_)).cos().pow(p_) * (Atom::var(w_)).cos().pow(q_),
        with: [v_, p_, w_, q_, x_],
        optional: [p_, q_],
        when: {
            rubi_expand_trig_reduce_angles_q(&v_, &w_, x_) && igtq!(p_, 0) && igtq!(q_, 0)
        },
        rhs: {
            let product = v_.cos().pow(&p_) * w_.cos().pow(&q_);
            let expanded = rubi_expand_trig_reduce(&Atom::num(1), &product, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_5082(rules: &mut Vec<RubiRule>) {
    rubi_symb!(m_, p_, q_, v_, w_, x_);
    rules.push(rubi_rule!(
        order: 5082,
        source: "Int[x_^m_.*Sin[v_]^p_.*Sin[w_]^q_.,x_Symbol] :=
          Int[ExpandTrigReduce[x^m,Sin[v]^p*Sin[w]^q,x],x] /;
        IGtQ[m,0] && IGtQ[p,0] && IGtQ[q,0] && (PolynomialQ[v,x] && PolynomialQ[w,x] || BinomialQ[{v,w},x] && IndependentQ[Cancel[v/w],x])",
        desc: "Algebraic expansion",
        refs: [],
        pattern: x_.pow(m_) * (Atom::var(v_)).sin().pow(p_) * (Atom::var(w_)).sin().pow(q_),
        with: [m_, v_, p_, w_, q_, x_],
        optional: [m_, p_, q_],
        when: {
            igtq!(m_, 0)
                && igtq!(p_, 0)
                && igtq!(q_, 0)
                && rubi_expand_trig_reduce_angles_q(&v_, &w_, x_)
        },
        rhs: {
            let product = v_.sin().pow(&p_) * w_.sin().pow(&q_);
            let expanded = rubi_expand_trig_reduce(x_.pow(&m_), &product, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_5083(rules: &mut Vec<RubiRule>) {
    rubi_symb!(m_, p_, q_, v_, w_, x_);
    rules.push(rubi_rule!(
        order: 5083,
        source: "Int[x_^m_.*Cos[v_]^p_.*Cos[w_]^q_.,x_Symbol] :=
          Int[ExpandTrigReduce[x^m,Cos[v]^p*Cos[w]^q,x],x] /;
        IGtQ[m,0] && IGtQ[p,0] && IGtQ[q,0] && (PolynomialQ[v,x] && PolynomialQ[w,x] || BinomialQ[{v,w},x] && IndependentQ[Cancel[v/w],x])",
        desc: "Algebraic expansion",
        refs: [],
        pattern: x_.pow(m_) * (Atom::var(v_)).cos().pow(p_) * (Atom::var(w_)).cos().pow(q_),
        with: [m_, v_, p_, w_, q_, x_],
        optional: [m_, p_, q_],
        when: {
            igtq!(m_, 0)
                && igtq!(p_, 0)
                && igtq!(q_, 0)
                && rubi_expand_trig_reduce_angles_q(&v_, &w_, x_)
        },
        rhs: {
            let product = v_.cos().pow(&p_) * w_.cos().pow(&q_);
            let expanded = rubi_expand_trig_reduce(x_.pow(&m_), &product, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_5084(rules: &mut Vec<RubiRule>) {
    rubi_symb!(p_, u__, v_, w_);
    rules.push(rubi_rule!(
        order: 5084,
        source: "Int[u_.*Sin[v_]^p_.*Cos[w_]^p_.,x_Symbol] :=
          1/2^p \\[Star] Int[u*Sin[2*v]^p,x] /;
        EqQ[w,v] && IntegerQ[p]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: u__ * (Atom::var(v_)).sin().pow(p_) * (Atom::var(w_)).cos().pow(p_),
        with: [u__, v_, p_, w_, x_],
        optional: [u__, p_],
        when: { eqq!(w_, v_) && integerq!(p_) },
        rhs: {
            let integrand = &u__ * (Atom::num(2) * &v_).sin().pow(&p_);
            let recursive = rubi_rhs_int(&integrand, x_);

            rubi_star(Atom::num(1) / Atom::num(2).pow(&p_), recursive)
        },
    ));
}

fn push_rules_rule_5085(rules: &mut Vec<RubiRule>) {
    rubi_symb!(p_, q_, v_, w_);
    rules.push(rubi_rule!(
        order: 5085,
        source: "Int[Sin[v_]^p_.*Cos[w_]^q_.,x_Symbol] :=
          Int[ExpandTrigReduce[Sin[v]^p*Cos[w]^q,x],x] /;
        IGtQ[p,0] && IGtQ[q,0] && (PolynomialQ[v,x] && PolynomialQ[w,x] || BinomialQ[{v,w},x] && IndependentQ[Cancel[v/w],x])",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (Atom::var(v_)).sin().pow(p_) * (Atom::var(w_)).cos().pow(q_),
        with: [v_, p_, w_, q_, x_],
        optional: [p_, q_],
        when: {
            igtq!(p_, 0) && igtq!(q_, 0) && rubi_expand_trig_reduce_angles_q(&v_, &w_, x_)
        },
        rhs: {
            let product = v_.sin().pow(&p_) * w_.cos().pow(&q_);
            let expanded = rubi_expand_trig_reduce(&Atom::num(1), &product, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_5086(rules: &mut Vec<RubiRule>) {
    rubi_symb!(m_, p_, q_, v_, w_, x_);
    rules.push(rubi_rule!(
        order: 5086,
        source: "Int[x_^m_.*Sin[v_]^p_.*Cos[w_]^q_.,x_Symbol] :=
          Int[ExpandTrigReduce[x^m,Sin[v]^p*Cos[w]^q,x],x] /;
        IGtQ[m,0] && IGtQ[p,0] && IGtQ[q,0] && (PolynomialQ[v,x] && PolynomialQ[w,x] || BinomialQ[{v,w},x] && IndependentQ[Cancel[v/w],x])",
        desc: "Algebraic expansion",
        refs: [],
        pattern: x_.pow(m_) * (Atom::var(v_)).sin().pow(p_) * (Atom::var(w_)).cos().pow(q_),
        with: [m_, v_, p_, w_, q_, x_],
        optional: [m_, p_, q_],
        when: {
            igtq!(m_, 0)
                && igtq!(p_, 0)
                && igtq!(q_, 0)
                && rubi_expand_trig_reduce_angles_q(&v_, &w_, x_)
        },
        rhs: {
            let product = v_.sin().pow(&p_) * w_.cos().pow(&q_);
            let expanded = rubi_expand_trig_reduce(x_.pow(&m_), &product, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_5087(rules: &mut Vec<RubiRule>) {
    rubi_symb!(n_, v_, w_);
    rules.push(rubi_rule!(
        order: 5087,
        source: "Int[Sin[v_]*Tan[w_]^n_.,x_Symbol] :=
          -Int[Cos[v]*Tan[w]^(n-1),x] + Cos[v-w] \\[Star] Int[Sec[w]*Tan[w]^(n-1),x] /;
        GtQ[n,0] && FreeQ[v-w,x] && NeQ[w,v]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (Atom::var(v_)).sin() * (Atom::var(w_)).tan().pow(n_),
        with: [v_, w_, n_, x_],
        optional: [n_],
        when: { gtq!(n_, 0) && rubi_evaluated_free_q(&v_ - &w_, x_) && neq!(w_, v_) },
        rhs: {
            let first = rubi_rhs_int(&(v_.cos() * w_.tan().pow(&n_ - 1)), x_);
            let second = rubi_rhs_int(&(w_.sec() * w_.tan().pow(&n_ - 1)), x_);

            -first + rubi_star((&v_ - &w_).cos(), second)
        },
    ));
}

fn push_rules_rule_5088(rules: &mut Vec<RubiRule>) {
    rubi_symb!(n_, v_, w_);
    rules.push(rubi_rule!(
        order: 5088,
        source: "Int[Cos[v_]*Cot[w_]^n_.,x_Symbol] :=
          -Int[Sin[v]*Cot[w]^(n-1),x] + Cos[v-w] \\[Star] Int[Csc[w]*Cot[w]^(n-1),x] /;
        GtQ[n,0] && FreeQ[v-w,x] && NeQ[w,v]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (Atom::var(v_)).cos() * (Atom::var(w_)).cot().pow(n_),
        with: [v_, w_, n_, x_],
        optional: [n_],
        when: { gtq!(n_, 0) && rubi_evaluated_free_q(&v_ - &w_, x_) && neq!(w_, v_) },
        rhs: {
            let first = rubi_rhs_int(&(v_.sin() * w_.cot().pow(&n_ - 1)), x_);
            let second = rubi_rhs_int(&(w_.csc() * w_.cot().pow(&n_ - 1)), x_);

            -first + rubi_star((&v_ - &w_).cos(), second)
        },
    ));
}

fn push_rules_rule_5089(rules: &mut Vec<RubiRule>) {
    rubi_symb!(n_, v_, w_);
    rules.push(rubi_rule!(
        order: 5089,
        source: "Int[Sin[v_]*Cot[w_]^n_.,x_Symbol] :=
          Int[Cos[v]*Cot[w]^(n-1),x] + Sin[v-w] \\[Star] Int[Csc[w]*Cot[w]^(n-1),x] /;
        GtQ[n,0] && FreeQ[v-w,x] && NeQ[w,v]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (Atom::var(v_)).sin() * (Atom::var(w_)).cot().pow(n_),
        with: [v_, w_, n_, x_],
        optional: [n_],
        when: { gtq!(n_, 0) && rubi_evaluated_free_q(&v_ - &w_, x_) && neq!(w_, v_) },
        rhs: {
            let first = rubi_rhs_int(&(v_.cos() * w_.cot().pow(&n_ - 1)), x_);
            let second = rubi_rhs_int(&(w_.csc() * w_.cot().pow(&n_ - 1)), x_);

            first + rubi_star((&v_ - &w_).sin(), second)
        },
    ));
}

fn push_rules_rule_5090(rules: &mut Vec<RubiRule>) {
    rubi_symb!(n_, v_, w_);
    rules.push(rubi_rule!(
        order: 5090,
        source: "Int[Cos[v_]*Tan[w_]^n_.,x_Symbol] :=
          Int[Sin[v]*Tan[w]^(n-1),x] - Sin[v-w] \\[Star] Int[Sec[w]*Tan[w]^(n-1),x] /;
        GtQ[n,0] && FreeQ[v-w,x] && NeQ[w,v]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (Atom::var(v_)).cos() * (Atom::var(w_)).tan().pow(n_),
        with: [v_, w_, n_, x_],
        optional: [n_],
        when: { gtq!(n_, 0) && rubi_evaluated_free_q(&v_ - &w_, x_) && neq!(w_, v_) },
        rhs: {
            let first = rubi_rhs_int(&(v_.sin() * w_.tan().pow(&n_ - 1)), x_);
            let second = rubi_rhs_int(&(w_.sec() * w_.tan().pow(&n_ - 1)), x_);

            first + rubi_star(-(&v_ - &w_).sin(), second)
        },
    ));
}

fn push_rules_rule_5091(rules: &mut Vec<RubiRule>) {
    rubi_symb!(n_, v_, w_);
    rules.push(rubi_rule!(
        order: 5091,
        source: "Int[Sin[v_]*Sec[w_]^n_.,x_Symbol] :=
          Cos[v-w] \\[Star] Int[Tan[w]*Sec[w]^(n-1),x] + Sin[v-w] \\[Star] Int[Sec[w]^(n-1),x] /;
        GtQ[n,0] && FreeQ[v-w,x] && NeQ[w,v]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (Atom::var(v_)).sin() * (Atom::var(w_)).sec().pow(n_),
        with: [v_, w_, n_, x_],
        optional: [n_],
        when: { gtq!(n_, 0) && rubi_evaluated_free_q(&v_ - &w_, x_) && neq!(w_, v_) },
        rhs: {
            let first = rubi_rhs_int(&(w_.tan() * w_.sec().pow(&n_ - 1)), x_);
            let second = rubi_rhs_int(&w_.sec().pow(&n_ - 1), x_);

            rubi_star((&v_ - &w_).cos(), first)
                    + rubi_star((&v_ - &w_).sin(), second)
        },
    ));
}

fn push_rules_rule_5092(rules: &mut Vec<RubiRule>) {
    rubi_symb!(n_, v_, w_);
    rules.push(rubi_rule!(
        order: 5092,
        source: "Int[Cos[v_]*Csc[w_]^n_.,x_Symbol] :=
          Cos[v-w] \\[Star] Int[Cot[w]*Csc[w]^(n-1),x] - Sin[v-w] \\[Star] Int[Csc[w]^(n-1),x] /;
        GtQ[n,0] && FreeQ[v-w,x] && NeQ[w,v]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (Atom::var(v_)).cos() * (Atom::var(w_)).csc().pow(n_),
        with: [v_, w_, n_, x_],
        optional: [n_],
        when: { gtq!(n_, 0) && rubi_evaluated_free_q(&v_ - &w_, x_) && neq!(w_, v_) },
        rhs: {
            let first = rubi_rhs_int(&(w_.cot() * w_.csc().pow(&n_ - 1)), x_);
            let second = rubi_rhs_int(&w_.csc().pow(&n_ - 1), x_);

            rubi_star((&v_ - &w_).cos(), first)
                    + rubi_star(-(&v_ - &w_).sin(), second)
        },
    ));
}

fn push_rules_rule_5093(rules: &mut Vec<RubiRule>) {
    rubi_symb!(n_, v_, w_);
    rules.push(rubi_rule!(
        order: 5093,
        source: "Int[Sin[v_]*Csc[w_]^n_.,x_Symbol] :=
          Sin[v-w] \\[Star] Int[Cot[w]*Csc[w]^(n-1),x] + Cos[v-w] \\[Star] Int[Csc[w]^(n-1),x] /;
        GtQ[n,0] && FreeQ[v-w,x] && NeQ[w,v]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (Atom::var(v_)).sin() * (Atom::var(w_)).csc().pow(n_),
        with: [v_, w_, n_, x_],
        optional: [n_],
        when: { gtq!(n_, 0) && rubi_evaluated_free_q(&v_ - &w_, x_) && neq!(w_, v_) },
        rhs: {
            let first = rubi_rhs_int(&(w_.cot() * w_.csc().pow(&n_ - 1)), x_);
            let second = rubi_rhs_int(&w_.csc().pow(&n_ - 1), x_);

            rubi_star((&v_ - &w_).sin(), first)
                    + rubi_star((&v_ - &w_).cos(), second)
        },
    ));
}

fn push_rules_rule_5094(rules: &mut Vec<RubiRule>) {
    rubi_symb!(n_, v_, w_);
    rules.push(rubi_rule!(
        order: 5094,
        source: "Int[Cos[v_]*Sec[w_]^n_.,x_Symbol] :=
          -Sin[v-w] \\[Star] Int[Tan[w]*Sec[w]^(n-1),x] + Cos[v-w] \\[Star] Int[Sec[w]^(n-1),x] /;
        GtQ[n,0] && FreeQ[v-w,x] && NeQ[w,v]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (Atom::var(v_)).cos() * (Atom::var(w_)).sec().pow(n_),
        with: [v_, w_, n_, x_],
        optional: [n_],
        when: { gtq!(n_, 0) && rubi_evaluated_free_q(&v_ - &w_, x_) && neq!(w_, v_) },
        rhs: {
            let first = rubi_rhs_int(&(w_.tan() * w_.sec().pow(&n_ - 1)), x_);
            let second = rubi_rhs_int(&w_.sec().pow(&n_ - 1), x_);

            rubi_star(-(&v_ - &w_).sin(), first)
                    + rubi_star((&v_ - &w_).cos(), second)
        },
    ));
}

fn push_rules_rule_5095(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5095,
        source: "Int[(e_.+f_.*x_)^m_.*(a_+b_.*Sin[c_.+d_.*x_]*Cos[c_.+d_.*x_])^n_.,x_Symbol] :=
          Int[(e+f*x)^m*(a+b*Sin[2*c+2*d*x]/2)^n,x] /;
        FreeQ[{a,b,c,d,e,f,m,n},x]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: (e__ + f__ * x_).pow(m_)
            * (a__ + b__ * (c__ + d__ * x_).sin() * (c__ + d__ * x_).cos()).pow(n_),
        with: [e__, f__, m_, a__, b__, c__, d__, n_, x_],
        optional: [e__, f__, m_, b__, c__, d__, n_],
        when: { freeq!([a__, b__, c__, d__, e__, f__, m_, n_], x_) },
        rhs: {
            let integrand = (&e__ + &f__ * x_).pow(&m_)
                * (&a__ + &b__ * (Atom::num(2) * &c__ + Atom::num(2) * &d__ * x_).sin() / 2).pow(&n_);

            rubi_rhs_int(&integrand, x_)
        },
    ));
}

fn push_rules_rule_5096(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5096,
        source: "Int[x_^m_.*(a_+b_.*Sin[c_.+d_.*x_]^2)^n_,x_Symbol] :=
          1/2^n \\[Star] Int[x^m*(2*a+b-b*Cos[2*c+2*d*x])^n,x] /;
        FreeQ[{a,b,c,d},x] && NeQ[a+b,0] && IGtQ[m,0] && ILtQ[n,0] && (EqQ[n,-1] || EqQ[m,1] && EqQ[n,-2])",
        desc: "Algebraic simplification",
        refs: [],
        pattern: x_.pow(m_) * (a__ + b__ * (c__ + d__ * x_).sin().pow(2)).pow(n_),
        with: [m_, a__, b__, c__, d__, n_, x_],
        optional: [m_, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && neq!(&a__ + &b__, 0)
                && igtq!(m_, 0)
                && iltq!(n_, 0)
                && (eqq!(n_, -1) || eqq!(m_, 1) && eqq!(n_, -2))
        },
        rhs: {
            let integrand =
                x_.pow(&m_) * (Atom::num(2) * &a__ + &b__ - &b__ * (Atom::num(2) * &c__ + Atom::num(2) * &d__ * x_).cos()).pow(&n_);
            let recursive = rubi_rhs_int(&integrand, x_);

            rubi_star(Atom::num(1) / Atom::num(2).pow(&n_), recursive)
        },
    ));
}

fn push_rules_rule_5097(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5097,
        source: "Int[x_^m_.*(a_+b_.*Cos[c_.+d_.*x_]^2)^n_,x_Symbol] :=
          1/2^n \\[Star] Int[x^m*(2*a+b+b*Cos[2*c+2*d*x])^n,x] /;
        FreeQ[{a,b,c,d},x] && NeQ[a+b,0] && IGtQ[m,0] && ILtQ[n,0] && (EqQ[n,-1] || EqQ[m,1] && EqQ[n,-2])",
        desc: "Algebraic simplification",
        refs: [],
        pattern: x_.pow(m_) * (a__ + b__ * (c__ + d__ * x_).cos().pow(2)).pow(n_),
        with: [m_, a__, b__, c__, d__, n_, x_],
        optional: [m_, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && neq!(&a__ + &b__, 0)
                && igtq!(m_, 0)
                && iltq!(n_, 0)
                && (eqq!(n_, -1) || eqq!(m_, 1) && eqq!(n_, -2))
        },
        rhs: {
            let integrand =
                x_.pow(&m_) * (Atom::num(2) * &a__ + &b__ + &b__ * (Atom::num(2) * &c__ + Atom::num(2) * &d__ * x_).cos()).pow(&n_);
            let recursive = rubi_rhs_int(&integrand, x_);

            rubi_star(Atom::num(1) / Atom::num(2).pow(&n_), recursive)
        },
    ));
}

fn push_rules_rule_5098(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, m_, x_);
    rules.push(rubi_rule!(
        order: 5098,
        source: "Int[(f_.+g_.*x_)^m_./(a_.+b_.*Cos[d_.+e_.*x_]^2+c_.*Sin[d_.+e_.*x_]^2),x_Symbol] :=
          2 \\[Star] Int[(f+g*x)^m/(2*a+b+c+(b-c)*Cos[2*d+2*e*x]),x] /;
        FreeQ[{a,b,c,d,e,f,g},x] && IGtQ[m,0] && NeQ[a+b,0] && NeQ[a+c,0]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: (f__ + g__ * x_).pow(m_)
            / (a__ + b__ * (d__ + e__ * x_).cos().pow(2) + c__ * (d__ + e__ * x_).sin().pow(2)),
        with: [f__, g__, m_, a__, b__, d__, e__, c__, x_],
        optional: [f__, g__, m_, a__, b__, d__, e__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__], x_)
                && igtq!(m_, 0)
                && neq!(&a__ + &b__, 0)
                && neq!(&a__ + &c__, 0)
        },
        rhs: {
            let denominator = Atom::num(2) * &a__
                + &b__
                + &c__
                + (&b__ - &c__) * (Atom::num(2) * &d__ + Atom::num(2) * &e__ * x_).cos();
            let recursive = rubi_rhs_int(&((&f__ + &g__ * x_).pow(&m_) / denominator), x_);

            rubi_star(Atom::num(2), recursive)
        },
    ));
}

fn push_rules_rule_5099(rules: &mut Vec<RubiRule>) {
    rubi_symb!(b__, c__, d__, e__, f__, g__, m_, x_);
    rules.push(rubi_rule!(
        order: 5099,
        source: "Int[(f_.+g_.*x_)^m_.*Sec[d_.+e_.*x_]^2/(b_+c_.*Tan[d_.+e_.*x_]^2),x_Symbol] :=
          2 \\[Star] Int[(f+g*x)^m/(b+c+(b-c)*Cos[2*d+2*e*x]),x] /;
        FreeQ[{b,c,d,e,f,g},x] && IGtQ[m,0]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: (f__ + g__ * x_).pow(m_) * (d__ + e__ * x_).sec().pow(2)
            / (b__ + c__ * (d__ + e__ * x_).tan().pow(2)),
        with: [f__, g__, m_, d__, e__, b__, c__, x_],
        optional: [f__, g__, m_, d__, e__, c__],
        when: { freeq!([b__, c__, d__, e__, f__, g__], x_) && igtq!(m_, 0) },
        rhs: {
            let denominator = &b__ + &c__ + (&b__ - &c__) * (Atom::num(2) * &d__ + Atom::num(2) * &e__ * x_).cos();
            let recursive = rubi_rhs_int(&((&f__ + &g__ * x_).pow(&m_) / denominator), x_);

            rubi_star(Atom::num(2), recursive)
        },
    ));
}

fn push_rules_rule_5100(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, m_, x_);
    rules.push(rubi_rule!(
        order: 5100,
        source: "Int[(f_.+g_.*x_)^m_.*Sec[d_.+e_.*x_]^2/(b_.+a_.*Sec[d_.+e_.*x_]^2+c_.*Tan[d_.+e_.*x_]^2),x_Symbol] :=
          2 \\[Star] Int[(f+g*x)^m/(2*a+b+c+(b-c)*Cos[2*d+2*e*x]),x] /;
        FreeQ[{a,b,c,d,e,f,g},x] && IGtQ[m,0] && NeQ[a+b,0] && NeQ[a+c,0]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: (f__ + g__ * x_).pow(m_) * (d__ + e__ * x_).sec().pow(2)
            / (b__ + a__ * (d__ + e__ * x_).sec().pow(2) + c__ * (d__ + e__ * x_).tan().pow(2)),
        with: [f__, g__, m_, d__, e__, b__, a__, c__, x_],
        optional: [f__, g__, m_, d__, e__, b__, a__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__], x_)
                && igtq!(m_, 0)
                && neq!(&a__ + &b__, 0)
                && neq!(&a__ + &c__, 0)
        },
        rhs: {
            let denominator = Atom::num(2) * &a__
                + &b__
                + &c__
                + (&b__ - &c__) * (Atom::num(2) * &d__ + Atom::num(2) * &e__ * x_).cos();
            let recursive = rubi_rhs_int(&((&f__ + &g__ * x_).pow(&m_) / denominator), x_);

            rubi_star(Atom::num(2), recursive)
        },
    ));
}

fn push_rules_rule_5101(rules: &mut Vec<RubiRule>) {
    rubi_symb!(b__, c__, d__, e__, f__, g__, m_, x_);
    rules.push(rubi_rule!(
        order: 5101,
        source: "Int[(f_.+g_.*x_)^m_.*Csc[d_.+e_.*x_]^2/(c_+b_.*Cot[d_.+e_.*x_]^2),x_Symbol] :=
          2 \\[Star] Int[(f+g*x)^m/(b+c+(b-c)*Cos[2*d+2*e*x]),x] /;
        FreeQ[{b,c,d,e,f,g},x] && IGtQ[m,0]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: (f__ + g__ * x_).pow(m_) * (d__ + e__ * x_).csc().pow(2)
            / (c__ + b__ * (d__ + e__ * x_).cot().pow(2)),
        with: [f__, g__, m_, d__, e__, c__, b__, x_],
        optional: [f__, g__, m_, d__, e__, b__],
        when: { freeq!([b__, c__, d__, e__, f__, g__], x_) && igtq!(m_, 0) },
        rhs: {
            let denominator = &b__ + &c__ + (&b__ - &c__) * (Atom::num(2) * &d__ + Atom::num(2) * &e__ * x_).cos();
            let recursive = rubi_rhs_int(&((&f__ + &g__ * x_).pow(&m_) / denominator), x_);

            rubi_star(Atom::num(2), recursive)
        },
    ));
}

fn push_rules_rule_5102(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, m_, x_);
    rules.push(rubi_rule!(
        order: 5102,
        source: "Int[(f_.+g_.*x_)^m_.*Csc[d_.+e_.*x_]^2/(c_.+b_.*Cot[d_.+e_.*x_]^2+a_.*Csc[d_.+e_.*x_]^2),x_Symbol] :=
          2 \\[Star] Int[(f+g*x)^m/(2*a+b+c+(b-c)*Cos[2*d+2*e*x]),x] /;
        FreeQ[{a,b,c,d,e,f,g},x] && IGtQ[m,0] && NeQ[a+b,0] && NeQ[a+c,0]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: (f__ + g__ * x_).pow(m_) * (d__ + e__ * x_).csc().pow(2)
            / (c__ + b__ * (d__ + e__ * x_).cot().pow(2) + a__ * (d__ + e__ * x_).csc().pow(2)),
        with: [f__, g__, m_, d__, e__, c__, b__, a__, x_],
        optional: [f__, g__, m_, d__, e__, c__, b__, a__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__], x_)
                && igtq!(m_, 0)
                && neq!(&a__ + &b__, 0)
                && neq!(&a__ + &c__, 0)
        },
        rhs: {
            let denominator = Atom::num(2) * &a__
                + &b__
                + &c__
                + (&b__ - &c__) * (Atom::num(2) * &d__ + Atom::num(2) * &e__ * x_).cos();
            let recursive = rubi_rhs_int(&((&f__ + &g__ * x_).pow(&m_) / denominator), x_);

            rubi_star(Atom::num(2), recursive)
        },
    ));
}

fn push_rules_rule_5103(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_a__, capital_b__, a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 5103,
        source: "Int[(e_.+f_.*x_)*(A_+B_.*Sin[c_.+d_.*x_])/(a_+b_.*Sin[c_.+d_.*x_])^2,x_Symbol] :=
          -B*(e+f*x)*Cos[c+d*x]/(a*d*(a+b*Sin[c+d*x])) +
          B*f/(a*d) \\[Star] Int[Cos[c+d*x]/(a+b*Sin[c+d*x]),x] /;
        FreeQ[{a,b,c,d,e,f,A,B},x] && EqQ[a*A-b*B,0]",
        desc: "Integration by parts",
        refs: [],
        pattern: (e__ + f__ * x_) * (capital_a__ + capital_b__ * (c__ + d__ * x_).sin())
            / (a__ + b__ * (c__ + d__ * x_).sin()).pow(2),
        with: [e__, f__, capital_a__, capital_b__, c__, d__, a__, b__, x_],
        optional: [e__, f__, capital_b__, c__, d__, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, capital_a__, capital_b__], x_)
                && eqq!(&a__ * &capital_a__ - &b__ * &capital_b__, 0)
        },
        rhs: {
            let linear = &e__ + &f__ * x_;
            let angle = &c__ + &d__ * x_;
            let sin = angle.sin();
            let cos = angle.cos();
            let denominator = &a__ + &b__ * &sin;
            let recursive_integrand = &cos / (&a__ + &b__ * sin);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(-&capital_b__ * linear * cos / (&a__ * &d__ * denominator)), x_)
                    + rubi_star(&capital_b__ * &f__ / (&a__ * &d__), recursive)
        },
    ));
}

fn push_rules_rule_5104(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_a__, capital_b__, a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 5104,
        source: "Int[(e_.+f_.*x_)*(A_+B_.*Cos[c_.+d_.*x_])/(a_+b_.*Cos[c_.+d_.*x_])^2,x_Symbol] :=
          B*(e+f*x)*Sin[c+d*x]/(a*d*(a+b*Cos[c+d*x])) -
          B*f/(a*d) \\[Star] Int[Sin[c+d*x]/(a+b*Cos[c+d*x]),x] /;
        FreeQ[{a,b,c,d,e,f,A,B},x] && EqQ[a*A-b*B,0]",
        desc: "Integration by parts",
        refs: [],
        pattern: (e__ + f__ * x_) * (capital_a__ + capital_b__ * (c__ + d__ * x_).cos())
            / (a__ + b__ * (c__ + d__ * x_).cos()).pow(2),
        with: [e__, f__, capital_a__, capital_b__, c__, d__, a__, b__, x_],
        optional: [e__, f__, capital_b__, c__, d__, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, capital_a__, capital_b__], x_)
                && eqq!(&a__ * &capital_a__ - &b__ * &capital_b__, 0)
        },
        rhs: {
            let linear = &e__ + &f__ * x_;
            let angle = &c__ + &d__ * x_;
            let sin = angle.sin();
            let cos = angle.cos();
            let denominator = &a__ + &b__ * &cos;
            let recursive_integrand = &sin / (&a__ + &b__ * cos);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(&capital_b__ * linear * sin / (&a__ * &d__ * denominator)), x_)
                    + rubi_star(-&capital_b__ * &f__ / (&a__ * &d__), recursive)
        },
    ));
}

fn push_rules_rule_5105(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 5105,
        source: "Int[x_^2/(c_.*Sin[a_.*x_]+d_.*x_*Cos[a_.*x_])^2,x_Symbol] :=
          x/(a*d*Sin[a*x]*(c*Sin[a*x]+d*x*Cos[a*x])) + 1/d^2 \\[Star] Int[1/Sin[a*x]^2,x] /;
        FreeQ[{a,c,d},x] && EqQ[a*c+d,0]",
        desc: "Integration by parts",
        refs: [],
        pattern: x_.pow(2) / (c__ * (a__ * x_).sin() + d__ * x_ * (a__ * x_).cos()).pow(2),
        with: [c__, a__, d__, x_],
        optional: [c__, a__, d__],
        when: { freeq!([a__, c__, d__], x_) && eqq!(&a__ * &c__ + &d__, 0) },
        rhs: {
            let angle = &a__ * x_;
            let sin = angle.sin();
            let cos = angle.cos();
            let denominator = &c__ * &sin + &d__ * x_ * cos;
            let recursive_integrand = Atom::num(1) / sin.pow(2);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(x_ / (&a__ * &d__ * sin * denominator)), x_)
                    + rubi_star(Atom::num(1) / d__.pow(2), recursive)
        },
    ));
}

fn push_rules_rule_5106(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 5106,
        source: "Int[x_^2/(c_.*Cos[a_.*x_]+d_.*x_*Sin[a_.*x_])^2,x_Symbol] :=
          -x/(a*d*Cos[a*x]*(c*Cos[a*x]+d*x*Sin[a*x])) + 1/d^2 \\[Star] Int[1/Cos[a*x]^2,x] /;
        FreeQ[{a,c,d},x] && EqQ[a*c-d,0]",
        desc: "Integration by parts",
        refs: [],
        pattern: x_.pow(2) / (c__ * (a__ * x_).cos() + d__ * x_ * (a__ * x_).sin()).pow(2),
        with: [c__, a__, d__, x_],
        optional: [c__, a__, d__],
        when: { freeq!([a__, c__, d__], x_) && eqq!(&a__ * &c__ - &d__, 0) },
        rhs: {
            let angle = &a__ * x_;
            let sin = angle.sin();
            let cos = angle.cos();
            let denominator = &c__ * &cos + &d__ * x_ * sin;
            let recursive_integrand = Atom::num(1) / cos.pow(2);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(Atom::num(-1) * x_ / (&a__ * &d__ * cos * denominator)), x_)
                    + rubi_star(Atom::num(1) / d__.pow(2), recursive)
        },
    ));
}

fn push_rules_rule_5107(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 5107,
        source: "Int[Sin[a_.*x_]^2/(c_.*Sin[a_.*x_]+d_.*x_*Cos[a_.*x_])^2,x_Symbol] :=
          1/(d^2*x) + Sin[a*x]/(a*d*x*(d*x*Cos[a*x]+c*Sin[a*x])) /;
        FreeQ[{a,c,d},x] && EqQ[a*c+d,0]",
        desc: "Integration by parts",
        refs: [],
        pattern: (a__ * x_).sin().pow(2) / (c__ * (a__ * x_).sin() + d__ * x_ * (a__ * x_).cos()).pow(2),
        with: [a__, c__, d__, x_],
        optional: [a__, c__, d__],
        when: { freeq!([a__, c__, d__], x_) && eqq!(&a__ * &c__ + &d__, 0) },
        rhs: {
            let angle = &a__ * x_;
            let sin = angle.sin();
            let cos = angle.cos();
            let denominator = &d__ * x_ * cos + &c__ * &sin;

            rubi_simp(&(Atom::num(1) / (d__.pow(2) * x_)), x_) + rubi_simp(&(sin / (&a__ * &d__ * x_ * denominator)), x_)
        },
    ));
}

fn push_rules_rule_5108(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 5108,
        source: "Int[Cos[a_.*x_]^2/(c_.*Cos[a_.*x_]+d_.*x_*Sin[a_.*x_])^2,x_Symbol] :=
          1/(d^2*x) - Cos[a*x]/(a*d*x*(d*x*Sin[a*x]+c*Cos[a*x])) /;
        FreeQ[{a,c,d},x] && EqQ[a*c-d,0]",
        desc: "Integration by parts",
        refs: [],
        pattern: (a__ * x_).cos().pow(2) / (c__ * (a__ * x_).cos() + d__ * x_ * (a__ * x_).sin()).pow(2),
        with: [a__, c__, d__, x_],
        optional: [a__, c__, d__],
        when: { freeq!([a__, c__, d__], x_) && eqq!(&a__ * &c__ - &d__, 0) },
        rhs: {
            let angle = &a__ * x_;
            let sin = angle.sin();
            let cos = angle.cos();
            let denominator = &d__ * x_ * sin + &c__ * &cos;

            rubi_simp(&(Atom::num(1) / (d__.pow(2) * x_)), x_) - rubi_simp(&(cos / (&a__ * &d__ * x_ * denominator)), x_)
        },
    ));
}

fn push_rules_rule_5109(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5109,
        source: "Int[(b_.*x_)^m_*Sin[a_.*x_]^n_/(c_.*Sin[a_.*x_]+d_.*x_*Cos[a_.*x_])^2,x_Symbol] :=
          b*(b*x)^(m-1)*Sin[a*x]^(n-1)/(a*d*(c*Sin[a*x]+d*x*Cos[a*x])) -
          b^2*(n-1)/d^2 \\[Star] Int[(b*x)^(m-2)*Sin[a*x]^(n-2),x] /;
        FreeQ[{a,b,c,d,m,n},x] && EqQ[a*c+d,0] && EqQ[m,2-n]",
        desc: "Integration by parts",
        refs: [],
        pattern: (b__ * x_).pow(m_) * (a__ * x_).sin().pow(n_)
            / (c__ * (a__ * x_).sin() + d__ * x_ * (a__ * x_).cos()).pow(2),
        with: [b__, m_, a__, n_, c__, d__, x_],
        optional: [b__, a__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, m_, n_], x_)
                && eqq!(&a__ * &c__ + &d__, 0)
                && eqq!(m_, Atom::num(2) - &n_)
        },
        rhs: {
            let angle = &a__ * x_;
            let sin = angle.sin();
            let cos = angle.cos();
            let scaled = &b__ * x_;
            let denominator = &c__ * &sin + &d__ * x_ * cos;
            let recursive_integrand = scaled.pow(&m_ - 2) * sin.pow(&n_ - 2);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(&b__ * scaled.pow(&m_ - 1) * sin.pow(&n_ - 1) / (&a__ * &d__ * denominator)), x_)
                    + rubi_star(-b__.pow(2) * (&n_ - 1) / d__.pow(2), recursive)
        },
    ));
}

fn push_rules_rule_5110(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5110,
        source: "Int[(b_.*x_)^m_*Cos[a_.*x_]^n_/(c_.*Cos[a_.*x_]+d_.*x_*Sin[a_.*x_])^2,x_Symbol] :=
          -b*(b*x)^(m-1)*Cos[a*x]^(n-1)/(a*d*(c*Cos[a*x]+d*x*Sin[a*x])) -
          b^2*(n-1)/d^2 \\[Star] Int[(b*x)^(m-2)*Cos[a*x]^(n-2),x] /;
        FreeQ[{a,b,c,d,m,n},x] && EqQ[a*c-d,0] && EqQ[m,2-n]",
        desc: "Integration by parts",
        refs: [],
        pattern: (b__ * x_).pow(m_) * (a__ * x_).cos().pow(n_)
            / (c__ * (a__ * x_).cos() + d__ * x_ * (a__ * x_).sin()).pow(2),
        with: [b__, m_, a__, n_, c__, d__, x_],
        optional: [b__, a__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, m_, n_], x_)
                && eqq!(&a__ * &c__ - &d__, 0)
                && eqq!(m_, Atom::num(2) - &n_)
        },
        rhs: {
            let angle = &a__ * x_;
            let sin = angle.sin();
            let cos = angle.cos();
            let scaled = &b__ * x_;
            let denominator = &c__ * &cos + &d__ * x_ * sin;
            let recursive_integrand = scaled.pow(&m_ - 2) * cos.pow(&n_ - 2);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(-&b__ * scaled.pow(&m_ - 1) * cos.pow(&n_ - 1) / (&a__ * &d__ * denominator)), x_)
                    + rubi_star(-b__.pow(2) * (&n_ - 1) / d__.pow(2), recursive)
        },
    ));
}

fn push_rules_rule_5111(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5111,
        source: "Int[(b_.*x_)^m_.*Csc[a_.*x_]^n_./(c_.*Sin[a_.*x_]+d_.*x_*Cos[a_.*x_])^2,x_Symbol] :=
          b*(b*x)^(m-1)*Csc[a*x]^(n+1)/(a*d*(c*Sin[a*x]+d*x*Cos[a*x])) +
          b^2*(n+1)/d^2 \\[Star] Int[(b*x)^(m-2)*Csc[a*x]^(n+2),x] /;
        FreeQ[{a,b,c,d,m,n},x] && EqQ[a*c+d,0] && EqQ[m,n+2]",
        desc: "Integration by parts",
        refs: [],
        pattern: (b__ * x_).pow(m_) * (a__ * x_).csc().pow(n_)
            / (c__ * (a__ * x_).sin() + d__ * x_ * (a__ * x_).cos()).pow(2),
        with: [b__, m_, a__, n_, c__, d__, x_],
        optional: [b__, m_, a__, n_, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, m_, n_], x_)
                && eqq!(&a__ * &c__ + &d__, 0)
                && eqq!(m_, &n_ + 2)
        },
        rhs: {
            let scaled_x = &b__ * x_;
            let angle = &a__ * x_;
            let denominator = &c__ * angle.sin() + &d__ * x_ * angle.cos();
            let direct = &b__ * scaled_x.pow(&m_ - 1) * angle.csc().pow(&n_ + 1)
                / (&a__ * &d__ * denominator);
            let recursive_integrand = scaled_x.pow(&m_ - 2) * angle.csc().pow(&n_ + 2);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let coefficient = b__.pow(2) * (&n_ + 1) / d__.pow(2);

            rubi_simp(&(direct), x_) + rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_5112(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5112,
        source: "Int[(b_.*x_)^m_.*Sec[a_.*x_]^n_./(c_.*Cos[a_.*x_]+d_.*x_*Sin[a_.*x_])^2,x_Symbol] :=
          -b*(b*x)^(m-1)*Sec[a*x]^(n+1)/(a*d*(c*Cos[a*x]+d*x*Sin[a*x])) +
          b^2*(n+1)/d^2 \\[Star] Int[(b*x)^(m-2)*Sec[a*x]^(n+2),x] /;
        FreeQ[{a,b,c,d,m,n},x] && EqQ[a*c-d,0] && EqQ[m,n+2]",
        desc: "Integration by parts",
        refs: [],
        pattern: (b__ * x_).pow(m_) * (a__ * x_).sec().pow(n_)
            / (c__ * (a__ * x_).cos() + d__ * x_ * (a__ * x_).sin()).pow(2),
        with: [b__, m_, a__, n_, c__, d__, x_],
        optional: [b__, m_, a__, n_, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, m_, n_], x_)
                && eqq!(&a__ * &c__ - &d__, 0)
                && eqq!(m_, &n_ + 2)
        },
        rhs: {
            let scaled_x = &b__ * x_;
            let angle = &a__ * x_;
            let denominator = &c__ * angle.cos() + &d__ * x_ * angle.sin();
            let direct = -&b__ * scaled_x.pow(&m_ - 1) * angle.sec().pow(&n_ + 1)
                / (&a__ * &d__ * denominator);
            let recursive_integrand = scaled_x.pow(&m_ - 2) * angle.sec().pow(&n_ + 2);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let coefficient = b__.pow(2) * (&n_ + 1) / d__.pow(2);

            rubi_simp(&(direct), x_) + rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_5113(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, h__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5113,
        source: "Int[(g_.+h_.*x_)^p_.*(a_+b_.*Sin[e_.+f_.*x_])^m_.*(c_+d_.*Sin[e_.+f_.*x_])^n_.,x_Symbol] :=
          a^m*c^m \\[Star] Int[(g+h*x)^p*Cos[e+f*x]^(2*m)*(c+d*Sin[e+f*x])^(n-m),x] /;
        FreeQ[{a,b,c,d,e,f,g,h},x] && EqQ[b*c+a*d,0] && EqQ[a^2-b^2,0] && IntegerQ[m] && IGtQ[n-m,0]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [g__, h__, p_, a__, b__, e__, f__, m_, c__, d__, n_, x_],
        optional: [g__, h__, p_, b__, e__, f__, m_, d__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__], x_)
                && eqq!(&b__ * &c__ + &a__ * &d__, 0)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && integerq!(m_)
                && igtq!(&n_ - &m_, 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let cos = angle.cos();
            let recursive_integrand =
                (&g__ + &h__ * x_).pow(&p_) * cos.pow(Atom::num(2) * &m_) * (&c__ + &d__ * sin).pow(&n_ - &m_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(a__.pow(&m_) * c__.pow(&m_), recursive)
        },
    ));
}

fn push_rules_rule_5114(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, h__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5114,
        source: "Int[(g_.+h_.*x_)^p_.*(a_+b_.*Cos[e_.+f_.*x_])^m_.*(c_+d_.*Cos[e_.+f_.*x_])^n_.,x_Symbol] :=
          a^m*c^m \\[Star] Int[(g+h*x)^p*Sin[e+f*x]^(2*m)*(c+d*Cos[e+f*x])^(n-m),x] /;
        FreeQ[{a,b,c,d,e,f,g,h},x] && EqQ[b*c+a*d,0] && EqQ[a^2-b^2,0] && IntegerQ[m] && IGtQ[n-m,0]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [g__, h__, p_, a__, b__, e__, f__, m_, c__, d__, n_, x_],
        optional: [g__, h__, p_, b__, e__, f__, m_, d__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__], x_)
                && eqq!(&b__ * &c__ + &a__ * &d__, 0)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && integerq!(m_)
                && igtq!(&n_ - &m_, 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let cos = angle.cos();
            let recursive_integrand =
                (&g__ + &h__ * x_).pow(&p_) * sin.pow(Atom::num(2) * &m_) * (&c__ + &d__ * cos).pow(&n_ - &m_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(a__.pow(&m_) * c__.pow(&m_), recursive)
        },
    ));
}

fn push_rules_rule_5115(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, h__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5115,
        source: "Int[(g_.+h_.*x_)^p_.*(a_+b_.*Sin[e_.+f_.*x_])^m_*(c_+d_.*Sin[e_.+f_.*x_])^n_,x_Symbol] :=
          a^IntPart[m]*c^IntPart[m]*(a+b*Sin[e+f*x])^FracPart[m]*(c+d*Sin[e+f*x])^FracPart[m]/Cos[e+f*x]^(2*FracPart[m]) \\[Star]
            Int[(g+h*x)^p*Cos[e+f*x]^(2*m)*(c+d*Sin[e+f*x])^(n-m),x] /;
        FreeQ[{a,b,c,d,e,f,g,h},x] && EqQ[b*c+a*d,0] && EqQ[a^2-b^2,0] && IntegerQ[p] && IntegerQ[2*m] && IGeQ[n-m,0]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [g__, h__, p_, a__, b__, e__, f__, m_, c__, d__, n_, x_],
        optional: [g__, h__, p_, b__, e__, f__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__], x_)
                && eqq!(&b__ * &c__ + &a__ * &d__, 0)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && integerq!(p_)
                && integerq!(Atom::num(2) * &m_)
                && igeq!(&n_ - &m_, 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let cos = angle.cos();
            let frac_m = rubi_frac_part(&m_);
            let int_m = rubi_int_part(&m_);
            let first = &a__ + &b__ * &sin;
            let second = &c__ + &d__ * &sin;
            let recursive_integrand =
                (&g__ + &h__ * x_).pow(&p_) * cos.pow(Atom::num(2) * &m_) * second.pow(&n_ - &m_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            let coefficient = a__.pow(&int_m)
                * c__.pow(&int_m)
                * first.pow(&frac_m)
                * second.pow(&frac_m)
                / cos.pow(Atom::num(2) * frac_m);
            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_5116(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, h__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5116,
        source: "Int[(g_.+h_.*x_)^p_.*(a_+b_.*Cos[e_.+f_.*x_])^m_*(c_+d_.*Cos[e_.+f_.*x_])^n_,x_Symbol] :=
          a^IntPart[m]*c^IntPart[m]*(a+b*Cos[e+f*x])^FracPart[m]*(c+d*Cos[e+f*x])^FracPart[m]/Sin[e+f*x]^(2*FracPart[m]) \\[Star]
            Int[(g+h*x)^p*Sin[e+f*x]^(2*m)*(c+d*Cos[e+f*x])^(n-m),x] /;
        FreeQ[{a,b,c,d,e,f,g,h},x] && EqQ[b*c+a*d,0] && EqQ[a^2-b^2,0] && IntegerQ[p] && IntegerQ[2*m] && IGeQ[n-m,0]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [g__, h__, p_, a__, b__, e__, f__, m_, c__, d__, n_, x_],
        optional: [g__, h__, p_, b__, e__, f__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__], x_)
                && eqq!(&b__ * &c__ + &a__ * &d__, 0)
                && eqq!(a__.pow(2) - b__.pow(2), 0)
                && integerq!(p_)
                && integerq!(Atom::num(2) * &m_)
                && igeq!(&n_ - &m_, 0)
        },
        rhs: {
            let angle = &e__ + &f__ * x_;
            let sin = angle.sin();
            let cos = angle.cos();
            let frac_m = rubi_frac_part(&m_);
            let int_m = rubi_int_part(&m_);
            let first = &a__ + &b__ * &cos;
            let second = &c__ + &d__ * &cos;
            let recursive_integrand =
                (&g__ + &h__ * x_).pow(&p_) * sin.pow(Atom::num(2) * &m_) * second.pow(&n_ - &m_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            let coefficient = a__.pow(&int_m)
                * c__.pow(&int_m)
                * first.pow(&frac_m)
                * second.pow(&frac_m)
                / sin.pow(Atom::num(2) * frac_m);
            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_5117(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, m_, n_, v_);
    rules.push(rubi_rule!(
        order: 5117,
        source: "Int[Sec[v_]^m_.*(a_+b_.*Tan[v_])^n_., x_Symbol] :=
          Int[(a*Cos[v]+b*Sin[v])^n,x] /;
        FreeQ[{a,b},x] && IntegerQ[(m-1)/2] && EqQ[m+n,0]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: (Atom::var(v_)).sec().pow(m_) * (a__ + b__ * (Atom::var(v_)).tan()).pow(n_),
        with: [v_, m_, a__, b__, n_, x_],
        optional: [m_, b__, n_],
        when: {
            freeq!([a__, b__], x_) && integerq!((&m_ - 1) / Atom::num(2)) && eqq!(&m_ + &n_, 0)
        },
        rhs: {
            let recursive_integrand = (&a__ * v_.cos() + &b__ * v_.sin()).pow(&n_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            recursive
        },
    ));
}

fn push_rules_rule_5118(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, m_, n_, v_);
    rules.push(rubi_rule!(
        order: 5118,
        source: "Int[Csc[v_]^m_.*(a_+b_.*Cot[v_])^n_., x_Symbol] :=
          Int[(b*Cos[v]+a*Sin[v])^n,x] /;
        FreeQ[{a,b},x] && IntegerQ[(m-1)/2] && EqQ[m+n,0]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: (Atom::var(v_)).csc().pow(m_) * (a__ + b__ * (Atom::var(v_)).cot()).pow(n_),
        with: [v_, m_, a__, b__, n_, x_],
        optional: [m_, b__, n_],
        when: {
            freeq!([a__, b__], x_) && integerq!((&m_ - 1) / Atom::num(2)) && eqq!(&m_ + &n_, 0)
        },
        rhs: {
            let recursive_integrand = (&b__ * v_.cos() + &a__ * v_.sin()).pow(&n_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            recursive
        },
    ));
}

fn push_rules_rule_5119(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, n_, u__, x_);
    rules.push(rubi_rule!(
        order: 5119,
        source: "Int[u_.*Sin[a_.+b_.*x_]^m_.*Sin[c_.+d_.*x_]^n_.,x_Symbol] :=
          Int[ExpandTrigReduce[u,Sin[a+b*x]^m*Sin[c+d*x]^n,x],x] /;
        FreeQ[{a,b,c,d},x] && IGtQ[m,0] && IGtQ[n,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: u__ * (a__ + b__ * x_).sin().pow(m_) * (c__ + d__ * x_).sin().pow(n_),
        with: [u__, a__, b__, m_, c__, d__, n_, x_],
        optional: [u__, a__, b__, m_, c__, d__, n_],
        when: { freeq!([a__, b__, c__, d__], x_) && igtq!(m_, 0) && igtq!(n_, 0) },
        rhs: {
            let product = (&a__ + &b__ * x_).sin().pow(&m_) * (&c__ + &d__ * x_).sin().pow(&n_);
            let expanded = rubi_expand_trig_reduce(&u__, &product, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_5120(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, n_, u__, x_);
    rules.push(rubi_rule!(
        order: 5120,
        source: "Int[u_.*Cos[a_.+b_.*x_]^m_.*Cos[c_.+d_.*x_]^n_.,x_Symbol] :=
          Int[ExpandTrigReduce[u,Cos[a+b*x]^m*Cos[c+d*x]^n,x],x] /;
        FreeQ[{a,b,c,d},x] && IGtQ[m,0] && IGtQ[n,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: u__ * (a__ + b__ * x_).cos().pow(m_) * (c__ + d__ * x_).cos().pow(n_),
        with: [u__, a__, b__, m_, c__, d__, n_, x_],
        optional: [u__, a__, b__, m_, c__, d__, n_],
        when: { freeq!([a__, b__, c__, d__], x_) && igtq!(m_, 0) && igtq!(n_, 0) },
        rhs: {
            let product = (&a__ + &b__ * x_).cos().pow(&m_) * (&c__ + &d__ * x_).cos().pow(&n_);
            let expanded = rubi_expand_trig_reduce(&u__, &product, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_5121(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 5121,
        source: "Int[Sec[a_.+b_.*x_]*Sec[c_+d_.*x_],x_Symbol] :=
          -Csc[(b*c-a*d)/d] \\[Star] Int[Tan[a+b*x],x] + Csc[(b*c-a*d)/b] \\[Star] Int[Tan[c+d*x],x] /;
        FreeQ[{a,b,c,d},x] && EqQ[b^2-d^2,0] && NeQ[b*c-a*d,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (a__ + b__ * x_).sec() * (c__ + d__ * x_).sec(),
        with: [a__, b__, c__, d__, x_],
        optional: [a__, b__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && eqq!(b__.pow(2) - d__.pow(2), 0)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
        },
        rhs: {
            let phase = &b__ * &c__ - &a__ * &d__;
            let first = rubi_rhs_int(&(&a__ + &b__ * x_).tan(), x_);
            let second = rubi_rhs_int(&(&c__ + &d__ * x_).tan(), x_);

            rubi_star(-(&phase / &d__).csc(), first)
                    + rubi_star((&phase / &b__).csc(), second)
        },
    ));
}

fn push_rules_rule_5122(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 5122,
        source: "Int[Csc[a_.+b_.*x_]*Csc[c_+d_.*x_],x_Symbol] :=
          Csc[(b*c-a*d)/b] \\[Star] Int[Cot[a+b*x],x] - Csc[(b*c-a*d)/d] \\[Star] Int[Cot[c+d*x],x] /;
        FreeQ[{a,b,c,d},x] && EqQ[b^2-d^2,0] && NeQ[b*c-a*d,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (a__ + b__ * x_).csc() * (c__ + d__ * x_).csc(),
        with: [a__, b__, c__, d__, x_],
        optional: [a__, b__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && eqq!(b__.pow(2) - d__.pow(2), 0)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
        },
        rhs: {
            let phase = &b__ * &c__ - &a__ * &d__;
            let first = rubi_rhs_int(&(&a__ + &b__ * x_).cot(), x_);
            let second = rubi_rhs_int(&(&c__ + &d__ * x_).cot(), x_);

            rubi_star((&phase / &b__).csc(), first)
                    + rubi_star(-(&phase / &d__).csc(), second)
        },
    ));
}

fn push_rules_rule_5123(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 5123,
        source: "Int[Tan[a_.+b_.*x_]*Tan[c_+d_.*x_],x_Symbol] :=
          -b*x/d + b/d*Cos[(b*c-a*d)/d] \\[Star] Int[Sec[a+b*x]*Sec[c+d*x],x] /;
        FreeQ[{a,b,c,d},x] && EqQ[b^2-d^2,0] && NeQ[b*c-a*d,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (a__ + b__ * x_).tan() * (c__ + d__ * x_).tan(),
        with: [a__, b__, c__, d__, x_],
        optional: [a__, b__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && eqq!(b__.pow(2) - d__.pow(2), 0)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
        },
        rhs: {
            let phase = &b__ * &c__ - &a__ * &d__;
            let recursive_integrand = (&a__ + &b__ * x_).sec() * (&c__ + &d__ * x_).sec();
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(-&b__ * x_ / &d__), x_)
                    + rubi_star(&b__ * (&phase / &d__).cos() / &d__, recursive)
        },
    ));
}

fn push_rules_rule_5124(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 5124,
        source: "Int[Cot[a_.+b_.*x_]*Cot[c_+d_.*x_],x_Symbol] :=
          -b*x/d + Cos[(b*c-a*d)/d] \\[Star] Int[Csc[a+b*x]*Csc[c+d*x],x] /;
        FreeQ[{a,b,c,d},x] && EqQ[b^2-d^2,0] && NeQ[b*c-a*d,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (a__ + b__ * x_).cot() * (c__ + d__ * x_).cot(),
        with: [a__, b__, c__, d__, x_],
        optional: [a__, b__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && eqq!(b__.pow(2) - d__.pow(2), 0)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
        },
        rhs: {
            let phase = &b__ * &c__ - &a__ * &d__;
            let recursive_integrand = (&a__ + &b__ * x_).csc() * (&c__ + &d__ * x_).csc();
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(-&b__ * x_ / &d__), x_)
                    + rubi_star((&phase / &d__).cos(), recursive)
        },
    ));
}

fn push_rules_rule_5125(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, n_, u__, v_);
    rules.push(rubi_rule!(
        order: 5125,
        source: "Int[u_.*(a_.*Cos[v_]+b_.*Sin[v_])^n_.,x_Symbol] :=
          Int[u*(a*E^(-a/b*v))^n,x] /;
        FreeQ[{a,b,n},x] && EqQ[a^2+b^2,0]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: u__ * (a__ * (Atom::var(v_)).cos() + b__ * (Atom::var(v_)).sin()).pow(n_),
        with: [u__, a__, v_, b__, n_, x_],
        optional: [u__, a__, b__, n_],
        when: { freeq!([a__, b__, n_], x_) && eqq!(a__.pow(2) + b__.pow(2), 0) },
        rhs: {
            let recursive_integrand = &u__ * (&a__ * ((-&a__ / &b__) * &v_).exp()).pow(&n_);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_5126(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 5126,
        source: "Int[Sin[d_.*(a_.+b_.*Log[c_.*x_^n_.])^2],x_Symbol] :=
          I/2 \\[Star] Int[E^(-I*d*(a+b*Log[c*x^n])^2),x] - I/2 \\[Star] Int[E^(I*d*(a+b*Log[c*x^n])^2),x] /;
        FreeQ[{a,b,c,d,n},x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (d__ * (a__ + b__ * (c__ * x_.pow(n_)).log()).pow(2)).sin(),
        with: [d__, a__, b__, c__, n_, x_],
        optional: [d__, a__, b__, c__, n_],
        when: { freeq!([a__, b__, c__, d__, n_], x_) },
        rhs: {
            let i = Atom::i();
            let log_argument = &a__ + &b__ * (&c__ * x_.pow(&n_)).log();
            let exponent = &d__ * log_argument.pow(2);
            let first_integrand = (-&i * &exponent).exp();
            let second_integrand = (&i * exponent).exp();
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(&i / 2, first)
                    + rubi_star(-&i / 2, second)
        },
    ));
}

fn push_rules_rule_5127(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 5127,
        source: "Int[Cos[d_.*(a_.+b_.*Log[c_.*x_^n_.])^2],x_Symbol] :=
          1/2 \\[Star] Int[E^(-I*d*(a+b*Log[c*x^n])^2),x] + 1/2 \\[Star] Int[E^(I*d*(a+b*Log[c*x^n])^2),x] /;
        FreeQ[{a,b,c,d,n},x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (d__ * (a__ + b__ * (c__ * x_.pow(n_)).log()).pow(2)).cos(),
        with: [d__, a__, b__, c__, n_, x_],
        optional: [d__, a__, b__, c__, n_],
        when: { freeq!([a__, b__, c__, d__, n_], x_) },
        rhs: {
            let i = Atom::i();
            let log_argument = &a__ + &b__ * (&c__ * x_.pow(&n_)).log();
            let exponent = &d__ * log_argument.pow(2);
            let first_integrand = (-&i * &exponent).exp();
            let second_integrand = (&i * exponent).exp();
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(Atom::num(1) / 2, first)
                    + rubi_star(Atom::num(1) / 2, second)
        },
    ));
}

fn push_rules_rule_5128(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5128,
        source: "Int[(e_.*x_)^m_.*Sin[d_.*(a_.+b_.*Log[c_.*x_^n_.])^2],x_Symbol] :=
          I/2 \\[Star] Int[(e*x)^m*E^(-I*d*(a+b*Log[c*x^n])^2),x] - I/2 \\[Star] Int[(e*x)^m*E^(I*d*(a+b*Log[c*x^n])^2),x] /;
        FreeQ[{a,b,c,d,e,m,n},x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (e__ * x_).pow(m_) * (d__ * (a__ + b__ * (c__ * x_.pow(n_)).log()).pow(2)).sin(),
        with: [e__, m_, d__, a__, b__, c__, n_, x_],
        optional: [e__, m_, d__, a__, b__, c__, n_],
        when: { freeq!([a__, b__, c__, d__, e__, m_, n_], x_) },
        rhs: {
            let i = Atom::i();
            let scaled = (&e__ * x_).pow(&m_);
            let log_argument = &a__ + &b__ * (&c__ * x_.pow(&n_)).log();
            let exponent = &d__ * log_argument.pow(2);
            let first_integrand = &scaled * (-&i * &exponent).exp();
            let second_integrand = scaled * (&i * exponent).exp();
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(&i / 2, first)
                    + rubi_star(-&i / 2, second)
        },
    ));
}

fn push_rules_rule_5129(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5129,
        source: "Int[(e_.*x_)^m_.*Cos[d_.*(a_.+b_.*Log[c_.*x_^n_.])^2],x_Symbol] :=
          1/2 \\[Star] Int[(e*x)^m*E^(-I*d*(a+b*Log[c*x^n])^2),x] + 1/2 \\[Star] Int[(e*x)^m*E^(I*d*(a+b*Log[c*x^n])^2),x] /;
        FreeQ[{a,b,c,d,e,m,n},x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (e__ * x_).pow(m_) * (d__ * (a__ + b__ * (c__ * x_.pow(n_)).log()).pow(2)).cos(),
        with: [e__, m_, d__, a__, b__, c__, n_, x_],
        optional: [e__, m_, d__, a__, b__, c__, n_],
        when: { freeq!([a__, b__, c__, d__, e__, m_, n_], x_) },
        rhs: {
            let i = Atom::i();
            let scaled = (&e__ * x_).pow(&m_);
            let log_argument = &a__ + &b__ * (&c__ * x_.pow(&n_)).log();
            let exponent = &d__ * log_argument.pow(2);
            let first_integrand = &scaled * (-&i * &exponent).exp();
            let second_integrand = scaled * (&i * exponent).exp();
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(Atom::num(1) / 2, first)
                    + rubi_star(Atom::num(1) / 2, second)
        },
    ));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn downvalues_5026_through_5042_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .filter(|order| (5026..=5042).contains(order))
            .collect::<Vec<_>>();
        assert_eq!(orders, (5026..=5042).collect::<Vec<_>>());
    }

    #[test]
    fn downvalues_5043_through_5092_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .filter(|order| (5043..=5092).contains(order))
            .collect::<Vec<_>>();
        assert_eq!(orders, (5043..=5092).collect::<Vec<_>>());
    }

    #[test]
    fn downvalues_5093_through_5129_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .filter(|order| (5093..=5129).contains(order))
            .collect::<Vec<_>>();
        assert_eq!(orders, (5093..=5129).collect::<Vec<_>>());
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
    (e__ + f__ * x_).pow(m_) * (c__ + d__ * x_).cos().pow(n_) / (a__ + b__ * (c__ + d__ * x_).sin())
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
    (e__ + f__ * x_).pow(m_) * (c__ + d__ * x_).cos() / (a__ + b__ * (c__ + d__ * x_).sin())
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
    (e__ + f__ * x_).pow(m_) * (c__ + d__ * x_).csc().pow(n_) / (a__ + b__ * (c__ + d__ * x_).cos())
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
    (e__ + f__ * x_).pow(m_) * (c__ + d__ * x_).sec().pow(n_) / (a__ + b__ * (c__ + d__ * x_).sin())
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
    (e__ + f__ * x_).pow(m_) * (c__ + d__ * x_).sin().pow(n_) / (a__ + b__ * (c__ + d__ * x_).cos())
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
    (e__ + f__ * x_).pow(m_) * (c__ + d__ * x_).sin() / (a__ + b__ * (c__ + d__ * x_).cos())
}

#[inline(never)]
fn rubi_shared_pattern_6(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let g__ = symbols.g__;
    let h__ = symbols.h__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (g__ + h__ * x_).pow(p_)
        * (a__ + b__ * (e__ + f__ * x_).cos()).pow(m_)
        * (c__ + d__ * (e__ + f__ * x_).cos()).pow(n_)
}

#[inline(never)]
fn rubi_shared_pattern_7(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let g__ = symbols.g__;
    let h__ = symbols.h__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (g__ + h__ * x_).pow(p_)
        * (a__ + b__ * (e__ + f__ * x_).sin()).pow(m_)
        * (c__ + d__ * (e__ + f__ * x_).sin()).pow(n_)
}
