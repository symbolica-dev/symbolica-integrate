use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_5658(rules);
    push_rules_rule_5659(rules);
    push_rules_rule_5660(rules);
    push_rules_rule_5661(rules);
    push_rules_rule_5662(rules);
    push_rules_rule_5663(rules);
    push_rules_rule_5664(rules);
    push_rules_rule_5665(rules);
    push_rules_rule_5666(rules);
    push_rules_rule_5667(rules);
    push_rules_rule_5668(rules);
    push_rules_rule_5669(rules);
    push_rules_rule_5670(rules);
    push_rules_rule_5671(rules);
    push_rules_rule_5672(rules);
    push_rules_rule_5673(rules);
    push_rules_rule_5674(rules);
    push_rules_rule_5675(rules);
    push_rules_rule_5676(rules);
    push_rules_rule_5677(rules);
    push_rules_rule_5678(rules);
    push_rules_rule_5679(rules);
    push_rules_rule_5680(rules);
    push_rules_rule_5681(rules);
    push_rules_rule_5682(rules);
    push_rules_rule_5683(rules);
    push_rules_rule_5684(rules);
    push_rules_rule_5685(rules);
    push_rules_rule_5686(rules);
    push_rules_rule_5687(rules);
    push_rules_rule_5688(rules);
    push_rules_rule_5689(rules);
    push_rules_rule_5690(rules);
    push_rules_rule_5691(rules);
    push_rules_rule_5692(rules);
    push_rules_rule_5693(rules);
    push_rules_rule_5694(rules);
    push_rules_rule_5695(rules);
    push_rules_rule_5696(rules);
    push_rules_rule_5697(rules);
    push_rules_rule_5698(rules);
    push_rules_rule_5699(rules);
    push_rules_rule_5700(rules);
    push_rules_rule_5701(rules);
    push_rules_rule_5702(rules);
    push_rules_rule_5703(rules);
    push_rules_rule_5704(rules);
    push_rules_rule_5705(rules);
    push_rules_rule_5706(rules);
    push_rules_rule_5707(rules);
    push_rules_rule_5708(rules);
    push_rules_rule_5709(rules);
    push_rules_rule_5710(rules);
    push_rules_rule_5711(rules);
    push_rules_rule_5712(rules);
    push_rules_rule_5713(rules);
    push_rules_rule_5714(rules);
    push_rules_rule_5715(rules);
    push_rules_rule_5716(rules);
    push_rules_rule_5717(rules);
    push_rules_rule_5718(rules);
    push_rules_rule_5719(rules);
    push_rules_rule_5720(rules);
    push_rules_rule_5721(rules);
    push_rules_rule_5722(rules);
    push_rules_rule_5723(rules);
    push_rules_rule_5724(rules);
    push_rules_rule_5725(rules);
    push_rules_rule_5726(rules);
    push_rules_rule_5727(rules);
    push_rules_rule_5728(rules);
    push_rules_rule_5729(rules);
    push_rules_rule_5730(rules);
    push_rules_rule_5731(rules);
    push_rules_rule_5732(rules);
    push_rules_rule_5733(rules);
    push_rules_rule_5734(rules);
    push_rules_rule_5735(rules);
    push_rules_rule_5736(rules);
}

fn push_rules_rule_5658(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a_, b__, n_, x_);
    rules.push(rubi_rule!(
        order: 5658,
        source: "Int[ArcTan[a_+b_.*x_^n_],x_Symbol] :=
          x*ArcTan[a+b*x^n] -
          b*n \\[Star] Int[x^n/(1+a^2+2*a*b*x^n+b^2*x^(2*n)),x] /;
        FreeQ[{a,b,n},x]",
        desc: "Integration by parts",
        refs: [],
        pattern: (a_ + b__ * x_.pow(n_)).atan(),
        with: [a_, b__, n_, x_],
        optional: [b__],
        when: { freeq!([a_, b__, n_], x_) },
        rhs: {
            let power = x_.pow(&n_);
            let denominator = Atom::num(1) + a_.pow(2) + Atom::num(2) * &a_ * &b__ * &power + b__.pow(2) * x_.pow(Atom::num(2) * &n_);
            rubi_simp(&(x_ * (&a_ + &b__ * power).atan()), x_)
                    + rubi_star(-(&b__ * &n_), rubi_rhs_int(&(x_.pow(&n_) / denominator), x_))
        },
    ));
}

fn push_rules_rule_5659(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a_, b__, n_, x_);
    rules.push(rubi_rule!(
        order: 5659,
        source: "Int[ArcCot[a_+b_.*x_^n_],x_Symbol] :=
          x*ArcCot[a+b*x^n] +
          b*n \\[Star] Int[x^n/(1+a^2+2*a*b*x^n+b^2*x^(2*n)),x] /;
        FreeQ[{a,b,n},x]",
        desc: "Integration by parts",
        refs: [],
        pattern: (a_ + b__ * x_.pow(n_)).acot(),
        with: [a_, b__, n_, x_],
        optional: [b__],
        when: { freeq!([a_, b__, n_], x_) },
        rhs: {
            let power = x_.pow(&n_);
            let denominator = Atom::num(1) + a_.pow(2) + Atom::num(2) * &a_ * &b__ * &power + b__.pow(2) * x_.pow(Atom::num(2) * &n_);
            rubi_simp(&(x_ * (&a_ + &b__ * power).acot()), x_)
                    + rubi_star(&b__ * &n_, rubi_rhs_int(&(x_.pow(&n_) / denominator), x_))
        },
    ));
}

fn push_rules_rule_5660(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, n_, x_);
    rules.push(rubi_rule!(
        order: 5660,
        source: "Int[ArcTan[a_.+b_.*x_^n_]/x_,x_Symbol] :=
          I/2 \\[Star] Int[Log[1-I*a-I*b*x^n]/x,x] -
          I/2 \\[Star] Int[Log[1+I*a+I*b*x^n]/x,x] /;
        FreeQ[{a,b,n},x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (a__ + b__ * x_.pow(n_)).atan() / x_,
        with: [a__, b__, n_, x_],
        optional: [a__, b__],
        when: { freeq!([a__, b__, n_], x_) },
        rhs: {
            let i = Atom::i();
            let power = x_.pow(&n_);
            let first = (Atom::num(1) - &i * &a__ - &i * &b__ * &power).log() / x_;
            let second = (Atom::num(1) + &i * &a__ + &i * &b__ * power).log() / x_;
            rubi_star(&i / 2, rubi_rhs_int(&first, x_))
                    + rubi_star(-i / 2, rubi_rhs_int(&second, x_))
        },
    ));
}

fn push_rules_rule_5661(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, n_, x_);
    rules.push(rubi_rule!(
        order: 5661,
        source: "Int[ArcCot[a_.+b_.*x_^n_]/x_,x_Symbol] :=
          I/2 \\[Star] Int[Log[1-I/(a+b*x^n)]/x,x] -
          I/2 \\[Star] Int[Log[1+I/(a+b*x^n)]/x,x] /;
        FreeQ[{a,b,n},x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (a__ + b__ * x_.pow(n_)).acot() / x_,
        with: [a__, b__, n_, x_],
        optional: [a__, b__],
        when: { freeq!([a__, b__, n_], x_) },
        rhs: {
            let i = Atom::i();
            let argument = &a__ + &b__ * x_.pow(&n_);
            let first = (Atom::num(1) - &i / &argument).log() / x_;
            let second = (Atom::num(1) + &i / argument).log() / x_;
            rubi_star(&i / 2, rubi_rhs_int(&first, x_))
                    + rubi_star(-i / 2, rubi_rhs_int(&second, x_))
        },
    ));
}

fn push_rules_rule_5662(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a_, b__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5662,
        source: "Int[x_^m_.*ArcTan[a_+b_.*x_^n_],x_Symbol] :=
          x^(m+1)*ArcTan[a+b*x^n]/(m+1) -
          b*n/(m+1) \\[Star] Int[x^(m+n)/(1+a^2+2*a*b*x^n+b^2*x^(2*n)),x] /;
        FreeQ[{a,b},x] && RationalQ[m,n] && m+1!=0 && m+1!=n",
        desc: "Integration by parts",
        refs: ["G&R 2.851, CRC 456, A&S 4.4.69", "G&R 2.852, CRC 458, A&S 4.4.71"],
        pattern: x_.pow(m_) * (a_ + b__ * x_.pow(n_)).atan(),
        with: [m_, a_, b__, n_, x_],
        optional: [m_, b__],
        when: {
            freeq!([a_, b__], x_)
                && rationalq!([m_, n_])
                && neq!(&m_ + 1, 0)
                && neq!(&m_ + 1, n_)
        },
        rhs: {
            let power = x_.pow(&n_);
            let denominator = Atom::num(1) + a_.pow(2) + Atom::num(2) * &a_ * &b__ * &power + b__.pow(2) * x_.pow(Atom::num(2) * &n_);
            rubi_simp(&(x_.pow(&m_ + 1) * (&a_ + &b__ * power).atan() / (&m_ + 1)), x_)
                    + rubi_star(-(&b__ * &n_) / (&m_ + 1), rubi_rhs_int(&(x_.pow(&m_ + &n_) / denominator), x_))
        },
    ));
}

fn push_rules_rule_5663(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a_, b__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5663,
        source: "Int[x_^m_.*ArcCot[a_+b_.*x_^n_],x_Symbol] :=
          x^(m+1)*ArcCot[a+b*x^n]/(m+1) +
          b*n/(m+1) \\[Star] Int[x^(m+n)/(1+a^2+2*a*b*x^n+b^2*x^(2*n)),x] /;
        FreeQ[{a,b},x] && RationalQ[m,n] && m+1!=0 && m+1!=n",
        desc: "Integration by parts",
        refs: ["G&R 2.851, CRC 456, A&S 4.4.69", "G&R 2.852, CRC 458, A&S 4.4.71"],
        pattern: x_.pow(m_) * (a_ + b__ * x_.pow(n_)).acot(),
        with: [m_, a_, b__, n_, x_],
        optional: [m_, b__],
        when: {
            freeq!([a_, b__], x_)
                && rationalq!([m_, n_])
                && neq!(&m_ + 1, 0)
                && neq!(&m_ + 1, n_)
        },
        rhs: {
            let power = x_.pow(&n_);
            let denominator = Atom::num(1) + a_.pow(2) + Atom::num(2) * &a_ * &b__ * &power + b__.pow(2) * x_.pow(Atom::num(2) * &n_);
            rubi_simp(&(x_.pow(&m_ + 1) * (&a_ + &b__ * power).acot() / (&m_ + 1)), x_)
                    + rubi_star(&b__ * &n_ / (&m_ + 1), rubi_rhs_int(&(x_.pow(&m_ + &n_) / denominator), x_))
        },
    ));
}

fn push_rules_rule_5664(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, f_, x_);
    rules.push(rubi_rule!(
        order: 5664,
        source: "Int[ArcTan[a_.+b_.*f_^(c_.+d_.*x_)],x_Symbol] :=
          I/2 \\[Star] Int[Log[1-I*a-I*b*f^(c+d*x)],x] -
          I/2 \\[Star] Int[Log[1+I*a+I*b*f^(c+d*x)],x] /;
        FreeQ[{a,b,c,d,f},x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (a__ + b__ * f_.pow(c__ + d__ * x_)).atan(),
        with: [a__, b__, f_, c__, d__, x_],
        optional: [a__, b__, c__, d__],
        when: { freeq!([a__, b__, c__, d__, f_], x_) },
        rhs: {
            let i = Atom::i();
            let exponential = f_.pow(&c__ + &d__ * x_);
            let first = (Atom::num(1) - &i * &a__ - &i * &b__ * &exponential).log();
            let second = (Atom::num(1) + &i * &a__ + &i * &b__ * exponential).log();
            rubi_star(&i / 2, rubi_rhs_int(&first, x_))
                    + rubi_star(-i / 2, rubi_rhs_int(&second, x_))
        },
    ));
}

fn push_rules_rule_5665(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, f_, x_);
    rules.push(rubi_rule!(
        order: 5665,
        source: "Int[ArcCot[a_.+b_.*f_^(c_.+d_.*x_)],x_Symbol] :=
          I/2 \\[Star] Int[Log[1-I/(a+b*f^(c+d*x))],x] -
          I/2 \\[Star] Int[Log[1+I/(a+b*f^(c+d*x))],x] /;
        FreeQ[{a,b,c,d,f},x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (a__ + b__ * f_.pow(c__ + d__ * x_)).acot(),
        with: [a__, b__, f_, c__, d__, x_],
        optional: [a__, b__, c__, d__],
        when: { freeq!([a__, b__, c__, d__, f_], x_) },
        rhs: {
            let i = Atom::i();
            let argument = &a__ + &b__ * f_.pow(&c__ + &d__ * x_);
            let first = (Atom::num(1) - &i / &argument).log();
            let second = (Atom::num(1) + &i / argument).log();
            rubi_star(&i / 2, rubi_rhs_int(&first, x_))
                    + rubi_star(-i / 2, rubi_rhs_int(&second, x_))
        },
    ));
}

fn push_rules_rule_5666(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, f_, m_, x_);
    rules.push(rubi_rule!(
        order: 5666,
        source: "Int[x_^m_.*ArcTan[a_.+b_.*f_^(c_.+d_.*x_)],x_Symbol] :=
          I/2 \\[Star] Int[x^m*Log[1-I*a-I*b*f^(c+d*x)],x] -
          I/2 \\[Star] Int[x^m*Log[1+I*a+I*b*f^(c+d*x)],x] /;
        FreeQ[{a,b,c,d,f},x] && IntegerQ[m] && m>0",
        desc: "Algebraic expansion",
        refs: [],
        pattern: x_.pow(m_) * (a__ + b__ * f_.pow(c__ + d__ * x_)).atan(),
        with: [m_, a__, b__, f_, c__, d__, x_],
        optional: [m_, a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, f_], x_)
                && integerq!(m_)
        },
        rhs: {
            let i = Atom::i();
            let exponential = f_.pow(&c__ + &d__ * x_);
            let first =
                x_.pow(&m_) * (Atom::num(1) - &i * &a__ - &i * &b__ * &exponential).log();
            let second =
                x_.pow(&m_) * (Atom::num(1) + &i * &a__ + &i * &b__ * exponential).log();
            rubi_star(&i / 2, rubi_rhs_int(&first, x_))
                    + rubi_star(-i / 2, rubi_rhs_int(&second, x_))
        },
    ));
}

fn push_rules_rule_5667(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, f_, m_, x_);
    rules.push(rubi_rule!(
        order: 5667,
        source: "Int[x_^m_.*ArcCot[a_.+b_.*f_^(c_.+d_.*x_)],x_Symbol] :=
          I/2 \\[Star] Int[x^m*Log[1-I/(a+b*f^(c+d*x))],x] -
          I/2 \\[Star] Int[x^m*Log[1+I/(a+b*f^(c+d*x))],x] /;
        FreeQ[{a,b,c,d,f},x] && IntegerQ[m] && m>0",
        desc: "Algebraic expansion",
        refs: [],
        pattern: x_.pow(m_) * (a__ + b__ * f_.pow(c__ + d__ * x_)).acot(),
        with: [m_, a__, b__, f_, c__, d__, x_],
        optional: [m_, a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, f_], x_)
                && integerq!(m_)
        },
        rhs: {
            let i = Atom::i();
            let argument = &a__ + &b__ * f_.pow(&c__ + &d__ * x_);
            let first = x_.pow(&m_) * (Atom::num(1) - &i / &argument).log();
            let second = x_.pow(&m_) * (Atom::num(1) + &i / argument).log();
            rubi_star(&i / 2, rubi_rhs_int(&first, x_))
                    + rubi_star(-i / 2, rubi_rhs_int(&second, x_))
        },
    ));
}

fn push_rules_rule_5668(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, m_, n_, u__, x_);
    rules.push(rubi_rule!(
        order: 5668,
        source: "Int[u_.*ArcTan[c_./(a_.+b_.*x_^n_.)]^m_.,x_Symbol] :=
          Int[u*ArcCot[a/c+b*x^n/c]^m,x] /;
        FreeQ[{a,b,c,n,m},x]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: u__ * (c__ / (a__ + b__ * x_.pow(n_))).atan().pow(m_),
        with: [u__, c__, a__, b__, n_, m_, x_],
        optional: [u__, c__, a__, b__, n_, m_],
        when: { freeq!([a__, b__, c__, n_, m_], x_) },
        rhs: {
            let transformed = &u__ * (&a__ / &c__ + &b__ * x_.pow(&n_) / &c__).acot().pow(&m_);
            rubi_rhs_int(&transformed, x_)
        },
    ));
}

fn push_rules_rule_5669(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, m_, n_, u__, x_);
    rules.push(rubi_rule!(
        order: 5669,
        source: "Int[u_.*ArcCot[c_./(a_.+b_.*x_^n_.)]^m_.,x_Symbol] :=
          Int[u*ArcTan[a/c+b*x^n/c]^m,x] /;
        FreeQ[{a,b,c,n,m},x]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: u__ * (c__ / (a__ + b__ * x_.pow(n_))).acot().pow(m_),
        with: [u__, c__, a__, b__, n_, m_, x_],
        optional: [u__, c__, a__, b__, n_, m_],
        when: { freeq!([a__, b__, c__, n_, m_], x_) },
        rhs: {
            let transformed = &u__ * (&a__ / &c__ + &b__ * x_.pow(&n_) / &c__).atan().pow(&m_);
            rubi_rhs_int(&transformed, x_)
        },
    ));
}

fn push_rules_rule_5670(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, x_);
    rules.push(rubi_rule!(
        order: 5670,
        source: "Int[ArcTan[c_.*x_/Sqrt[a_.+b_.*x_^2]],x_Symbol] :=
          x*ArcTan[(c*x)/Sqrt[a+b*x^2]] - c \\[Star] Int[x/Sqrt[a+b*x^2],x] /;
        FreeQ[{a,b,c},x] && EqQ[b+c^2,0]",
        desc: "Integration by parts",
        refs: [],
        pattern: (c__ * x_ / (a__ + b__ * x_.pow(2)).sqrt()).atan(),
        with: [c__, a__, b__, x_],
        optional: [c__, a__, b__],
        when: { freeq!([a__, b__, c__], x_) && eqq!(&b__ + c__.pow(2), 0) },
        rhs: {
            let quadratic = &a__ + &b__ * x_.pow(2);
            rubi_simp(&(x_ * (&c__ * x_ / &quadratic.sqrt()).atan()), x_)
                    + rubi_star(-&c__, rubi_rhs_int(&(x_ / quadratic.sqrt()), x_))
        },
    ));
}

fn push_rules_rule_5671(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, x_);
    rules.push(rubi_rule!(
        order: 5671,
        source: "Int[ArcCot[c_.*x_/Sqrt[a_.+b_.*x_^2]],x_Symbol] :=
          x*ArcCot[(c*x)/Sqrt[a+b*x^2]] + c \\[Star] Int[x/Sqrt[a+b*x^2],x] /;
        FreeQ[{a,b,c},x] && EqQ[b+c^2,0]",
        desc: "Integration by parts",
        refs: [],
        pattern: (c__ * x_ / (a__ + b__ * x_.pow(2)).sqrt()).acot(),
        with: [c__, a__, b__, x_],
        optional: [c__, a__, b__],
        when: { freeq!([a__, b__, c__], x_) && eqq!(&b__ + c__.pow(2), 0) },
        rhs: {
            let quadratic = &a__ + &b__ * x_.pow(2);
            rubi_simp(&(x_ * (&c__ * x_ / &quadratic.sqrt()).acot()), x_)
                    + rubi_star(c__, rubi_rhs_int(&(x_ / quadratic.sqrt()), x_))
        },
    ));
}

fn push_rules_rule_5672(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, x_);
    rules.push(rubi_rule!(
        order: 5672,
        source: "Int[ArcTan[c_.*x_/Sqrt[a_.+b_.*x_^2]]/x_,x_Symbol] :=
          ArcTan[c*x/Sqrt[a+b*x^2]]*Log[x] - c \\[Star] Int[Log[x]/Sqrt[a+b*x^2],x] /;
        FreeQ[{a,b,c},x] && EqQ[b+c^2,0]",
        desc: "Integration by parts",
        refs: [],
        pattern: (c__ * x_ / (a__ + b__ * x_.pow(2)).sqrt()).atan() / x_,
        with: [c__, a__, b__, x_],
        optional: [c__, a__, b__],
        when: { freeq!([a__, b__, c__], x_) && eqq!(&b__ + c__.pow(2), 0) },
        rhs: {
            let quadratic = &a__ + &b__ * x_.pow(2);
            rubi_simp(&((&c__ * x_ / &quadratic.sqrt()).atan() * x_.log()), x_)
                    + rubi_star(-&c__, rubi_rhs_int(&(x_.log() / quadratic.sqrt()), x_))
        },
    ));
}

fn push_rules_rule_5673(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, x_);
    rules.push(rubi_rule!(
        order: 5673,
        source: "Int[ArcCot[c_.*x_/Sqrt[a_.+b_.*x_^2]]/x_,x_Symbol] :=
          ArcCot[c*x/Sqrt[a+b*x^2]]*Log[x] + c \\[Star] Int[Log[x]/Sqrt[a+b*x^2],x] /;
        FreeQ[{a,b,c},x] && EqQ[b+c^2,0]",
        desc: "Integration by parts",
        refs: [],
        pattern: (c__ * x_ / (a__ + b__ * x_.pow(2)).sqrt()).acot() / x_,
        with: [c__, a__, b__, x_],
        optional: [c__, a__, b__],
        when: { freeq!([a__, b__, c__], x_) && eqq!(&b__ + c__.pow(2), 0) },
        rhs: {
            let quadratic = &a__ + &b__ * x_.pow(2);
            rubi_simp(&((&c__ * x_ / &quadratic.sqrt()).acot() * x_.log()), x_)
                    + rubi_star(c__, rubi_rhs_int(&(x_.log() / quadratic.sqrt()), x_))
        },
    ));
}

fn push_rules_rule_5674(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, x_);
    rules.push(rubi_rule!(
        order: 5674,
        source: "Int[(d_.*x_)^m_.*ArcTan[c_.*x_/Sqrt[a_.+b_.*x_^2]],x_Symbol] :=
          (d*x)^(m+1)*ArcTan[(c*x)/Sqrt[a+b*x^2]]/(d*(m+1)) - c/(d*(m+1)) \\[Star] Int[(d*x)^(m+1)/Sqrt[a+b*x^2],x] /;
        FreeQ[{a,b,c,d,m},x] && EqQ[b+c^2,0] && NeQ[m,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern: (d__ * x_).pow(m_) * (c__ * x_ / (a__ + b__ * x_.pow(2)).sqrt()).atan(),
        with: [d__, m_, c__, a__, b__, x_],
        optional: [d__, m_, c__, a__, b__],
        when: {
            freeq!([a__, b__, c__, d__, m_], x_)
                && eqq!(&b__ + c__.pow(2), 0)
                && neq!(m_, -1)
        },
        rhs: {
            let quadratic = &a__ + &b__ * x_.pow(2);
            let scaled = &d__ * x_;
            rubi_simp(&(scaled.pow(&m_ + 1) * (&c__ * x_ / &quadratic.sqrt()).atan()
                    / (&d__ * (&m_ + 1))), x_)
                    + rubi_star(-&c__ / (&d__ * (&m_ + 1)), rubi_rhs_int(&(scaled.pow(&m_ + 1) / quadratic.sqrt()), x_))
        },
    ));
}

fn push_rules_rule_5675(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, x_);
    rules.push(rubi_rule!(
        order: 5675,
        source: "Int[(d_.*x_)^m_.*ArcCot[c_.*x_/Sqrt[a_.+b_.*x_^2]],x_Symbol] :=
          (d*x)^(m+1)*ArcCot[(c*x)/Sqrt[a+b*x^2]]/(d*(m+1)) + c/(d*(m+1)) \\[Star] Int[(d*x)^(m+1)/Sqrt[a+b*x^2],x] /;
        FreeQ[{a,b,c,d,m},x] && EqQ[b+c^2,0] && NeQ[m,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern: (d__ * x_).pow(m_) * (c__ * x_ / (a__ + b__ * x_.pow(2)).sqrt()).acot(),
        with: [d__, m_, c__, a__, b__, x_],
        optional: [d__, m_, c__, a__, b__],
        when: {
            freeq!([a__, b__, c__, d__, m_], x_)
                && eqq!(&b__ + c__.pow(2), 0)
                && neq!(m_, -1)
        },
        rhs: {
            let quadratic = &a__ + &b__ * x_.pow(2);
            let scaled = &d__ * x_;
            rubi_simp(&(scaled.pow(&m_ + 1) * (&c__ * x_ / &quadratic.sqrt()).acot()
                    / (&d__ * (&m_ + 1))), x_)
                    + rubi_star(&c__ / (&d__ * (&m_ + 1)), rubi_rhs_int(&(scaled.pow(&m_ + 1) / quadratic.sqrt()), x_))
        },
    ));
}

fn push_rules_rule_5676(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, x_);
    rules.push(rubi_rule!(
        order: 5676,
        source: "Int[1/(Sqrt[a_.+b_.*x_^2]*ArcTan[c_.*x_/Sqrt[a_.+b_.*x_^2]]),x_Symbol] :=
          1/c*Log[ArcTan[c*x/Sqrt[a+b*x^2]]] /;
        FreeQ[{a,b,c},x] && EqQ[b+c^2,0]",
        desc: "Reciprocal rule for integration",
        refs: [],
        pattern: Atom::num(1) / ((a__ + b__ * x_.pow(2)).sqrt() * (c__ * x_ / (a__ + b__ * x_.pow(2)).sqrt()).atan()),
        with: [a__, b__, c__, x_],
        optional: [a__, b__, c__],
        when: { freeq!([a__, b__, c__], x_) && eqq!(&b__ + c__.pow(2), 0) },
        rhs: {
            rubi_simp(&((&c__ * x_ / (&a__ + &b__ * x_.pow(2)).sqrt()).atan().log() / &c__), x_)
        },
    ));
}

fn push_rules_rule_5677(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, x_);
    rules.push(rubi_rule!(
        order: 5677,
        source: "Int[1/(Sqrt[a_.+b_.*x_^2]*ArcCot[c_.*x_/Sqrt[a_.+b_.*x_^2]]),x_Symbol] :=
          -1/c*Log[ArcCot[c*x/Sqrt[a+b*x^2]]] /;
        FreeQ[{a,b,c},x] && EqQ[b+c^2,0]",
        desc: "Reciprocal rule for integration",
        refs: [],
        pattern: Atom::num(1) / ((a__ + b__ * x_.pow(2)).sqrt() * (c__ * x_ / (a__ + b__ * x_.pow(2)).sqrt()).acot()),
        with: [a__, b__, c__, x_],
        optional: [a__, b__, c__],
        when: { freeq!([a__, b__, c__], x_) && eqq!(&b__ + c__.pow(2), 0) },
        rhs: {
            rubi_simp(&(-(&c__ * x_ / (&a__ + &b__ * x_.pow(2)).sqrt()).acot().log() / &c__), x_)
        },
    ));
}

fn push_rules_rule_5678(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, m_, x_);
    rules.push(rubi_rule!(
        order: 5678,
        source: "Int[ArcTan[c_.*x_/Sqrt[a_.+b_.*x_^2]]^m_./Sqrt[a_.+b_.*x_^2],x_Symbol] :=
          ArcTan[c*x/Sqrt[a+b*x^2]]^(m+1)/(c*(m+1)) /;
        FreeQ[{a,b,c,m},x] && EqQ[b+c^2,0] && NeQ[m,-1]",
        desc: "Power rule for integration",
        refs: [],
        pattern: (c__ * x_ / (a__ + b__ * x_.pow(2)).sqrt()).atan().pow(m_) / (a__ + b__ * x_.pow(2)).sqrt(),
        with: [c__, a__, b__, m_, x_],
        optional: [c__, a__, b__, m_],
        when: {
            freeq!([a__, b__, c__, m_], x_)
                && eqq!(&b__ + c__.pow(2), 0)
                && neq!(m_, -1)
        },
        rhs: {
            rubi_simp(&((&c__ * x_ / (&a__ + &b__ * x_.pow(2)).sqrt())
                    .atan()
                    .pow(&m_ + 1)
                    / (&c__ * (&m_ + 1))), x_)
        },
    ));
}

fn push_rules_rule_5679(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, m_, x_);
    rules.push(rubi_rule!(
        order: 5679,
        source: "Int[ArcCot[c_.*x_/Sqrt[a_.+b_.*x_^2]]^m_./Sqrt[a_.+b_.*x_^2],x_Symbol] :=
          -ArcCot[c*x/Sqrt[a+b*x^2]]^(m+1)/(c*(m+1)) /;
        FreeQ[{a,b,c,m},x] && EqQ[b+c^2,0] && NeQ[m,-1]",
        desc: "Power rule for integration",
        refs: [],
        pattern: (c__ * x_ / (a__ + b__ * x_.pow(2)).sqrt()).acot().pow(m_) / (a__ + b__ * x_.pow(2)).sqrt(),
        with: [c__, a__, b__, m_, x_],
        optional: [c__, a__, b__, m_],
        when: {
            freeq!([a__, b__, c__, m_], x_)
                && eqq!(&b__ + c__.pow(2), 0)
                && neq!(m_, -1)
        },
        rhs: {
            rubi_simp(&(-(&c__ * x_ / (&a__ + &b__ * x_.pow(2)).sqrt())
                    .acot()
                    .pow(&m_ + 1)
                    / (&c__ * (&m_ + 1))), x_)
        },
    ));
}

fn push_rules_rule_5680(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, x_);
    rules.push(rubi_rule!(
        order: 5680,
        source: "Int[ArcTan[c_.*x_/Sqrt[a_.+b_.*x_^2]]^m_./Sqrt[d_.+e_.*x_^2],x_Symbol] :=
          Sqrt[a+b*x^2]/Sqrt[d+e*x^2] \\[Star] Int[ArcTan[c*x/Sqrt[a+b*x^2]]^m/Sqrt[a+b*x^2],x] /;
        FreeQ[{a,b,c,d,e,m},x] && EqQ[b+c^2,0] && EqQ[b*d-a*e,0]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: (c__ * x_ / (a__ + b__ * x_.pow(2)).sqrt()).atan().pow(m_) / (d__ + e__ * x_.pow(2)).sqrt(),
        with: [c__, a__, b__, m_, d__, e__, x_],
        optional: [c__, a__, b__, m_, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_], x_)
                && eqq!(&b__ + c__.pow(2), 0)
                && eqq!(&b__ * &d__ - &a__ * &e__, 0)
        },
        rhs: {
            let first_quadratic = &a__ + &b__ * x_.pow(2);
            let angle = (&c__ * x_ / &first_quadratic.sqrt()).atan();
            let transformed = angle.pow(&m_) / &first_quadratic.sqrt();
            rubi_star(first_quadratic.sqrt() / (&d__ + &e__ * x_.pow(2)).sqrt(), rubi_rhs_int(&transformed, x_))
        },
    ));
}

fn push_rules_rule_5681(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, x_);
    rules.push(rubi_rule!(
        order: 5681,
        source: "Int[ArcCot[c_.*x_/Sqrt[a_.+b_.*x_^2]]^m_./Sqrt[d_.+e_.*x_^2],x_Symbol] :=
          Sqrt[a+b*x^2]/Sqrt[d+e*x^2] \\[Star] Int[ArcCot[c*x/Sqrt[a+b*x^2]]^m/Sqrt[a+b*x^2],x] /;
        FreeQ[{a,b,c,d,e,m},x] && EqQ[b+c^2,0] && EqQ[b*d-a*e,0]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: (c__ * x_ / (a__ + b__ * x_.pow(2)).sqrt()).acot().pow(m_) / (d__ + e__ * x_.pow(2)).sqrt(),
        with: [c__, a__, b__, m_, d__, e__, x_],
        optional: [c__, a__, b__, m_, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_], x_)
                && eqq!(&b__ + c__.pow(2), 0)
                && eqq!(&b__ * &d__ - &a__ * &e__, 0)
        },
        rhs: {
            let first_quadratic = &a__ + &b__ * x_.pow(2);
            let angle = (&c__ * x_ / &first_quadratic.sqrt()).acot();
            let transformed = angle.pow(&m_) / &first_quadratic.sqrt();
            rubi_star(first_quadratic.sqrt() / (&d__ + &e__ * x_.pow(2)).sqrt(), rubi_rhs_int(&transformed, x_))
        },
    ));
}

fn push_rules_rule_5682(rules: &mut Vec<RubiRule>) {
    rubi_symb!(s__, u__, v_, w_);
    rules.push(rubi_rule!(
        order: 5682,
        source: "Int[u_.*ArcTan[v_+s_.*Sqrt[w_]],x_Symbol] :=
          Pi*s/4 \\[Star] Int[u,x] + 1/2 \\[Star] Int[u*ArcTan[v],x] /;
        EqQ[s^2,1] && EqQ[w,v^2+1]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: u__ * (v_ + s__ * w_.pow(Atom::num(1) / Atom::num(2))).atan(),
        with: [u__, v_, s__, w_, x_],
        optional: [u__, s__],
        when: { eqq!(s__.pow(2), 1) && eqq!(w_, v_.pow(2) + 1) },
        rhs: {
            rubi_star(Atom::var(Symbol::PI) * &s__ / 4, rubi_rhs_int(&u__, x_)) + rubi_star(Atom::num(1) / 2, rubi_rhs_int(&(&u__ * v_.atan()), x_))
        },
    ));
}

fn push_rules_rule_5683(rules: &mut Vec<RubiRule>) {
    rubi_symb!(s__, u__, v_, w_);
    rules.push(rubi_rule!(
        order: 5683,
        source: "Int[u_.*ArcCot[v_+s_.*Sqrt[w_]],x_Symbol] :=
          Pi*s/4 \\[Star] Int[u,x] - 1/2 \\[Star] Int[u*ArcTan[v],x] /;
        EqQ[s^2,1] && EqQ[w,v^2+1]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: u__ * (v_ + s__ * w_.pow(Atom::num(1) / Atom::num(2))).acot(),
        with: [u__, v_, s__, w_, x_],
        optional: [u__, s__],
        when: { eqq!(s__.pow(2), 1) && eqq!(w_, v_.pow(2) + 1) },
        rhs: {
            rubi_star(Atom::var(Symbol::PI) * &s__ / 4, rubi_rhs_int(&u__, x_)) + rubi_star(-Atom::num(1) / 2, rubi_rhs_int(&(&u__ * v_.atan()), x_))
        },
    ));
}

fn push_rules_rule_5684(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; n_, u__, v_);
    rules.push(rubi_rule!(
        order: 5684,
        source: "Int[u_*v_^n_.,x_Symbol] :=
          With[{tmp=InverseFunctionOfLinear[u,x]},
          (-Discriminant[v,x]/(4*Coefficient[v,x,2]))^n/Coefficient[tmp[[1]],x,1]*
        \tSubst[Int[SimplifyIntegrand[SubstForInverseFunction[u,tmp,x]*Sec[x]^(2*(n+1)),x],x], x, tmp] /;
         Not[FalseQ[tmp]] && EqQ[Head[tmp],ArcTan] && EqQ[Discriminant[v,x]*tmp[[1]]^2+D[v,x]^2,0]] /;
        QuadraticQ[v,x] && ILtQ[n,0] && NegQ[Discriminant[v,x]] && MatchQ[u,r_.*f_^w_ /; FreeQ[f,x]]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_16(symbols),
        with: [u__, v_, n_, x_],
        optional: [n_],
        when: {
            iltq!(n_, 0)
                && rubi_inverse_linear_quadratic_match(&u__, &v_, x_, RubiInverseKind::ArcTan)
                    .is_some()
        },
        rhs: {
            let matched =
                rubi_inverse_linear_quadratic_match(&u__, &v_, x_, RubiInverseKind::ArcTan).rubi_rhs();
            let inverse = rubi_inverse_function_of_linear(&u__, x_, RubiInverseKind::ArcTan).rubi_rhs();
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let exponent = Atom::num(2) * (&n_ + 1);
            let transformed_u = rubi_subst_for_inverse_function(
                &u__,
                x_,
                substitution_symbol,
                &inverse,
                RubiInverseKind::ArcTan,
            );
            let payload = rubi_simplify_integrand(
                &(transformed_u * sub_atom.sec().pow(exponent)),
                substitution_symbol,
            );
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            let prefactor = (-matched.discriminant / (Atom::num(4) * matched.quadratic_coeff)).pow(&n_)
                / matched.linear_slope;
            let result = prefactor * rubi_subst(&primitive, substitution_symbol, inverse.tmp);
            rubi_simp(&result, x_)
        },
    ));
}

fn push_rules_rule_5685(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; n_, u__, v_);
    rules.push(rubi_rule!(
        order: 5685,
        source: "Int[u_*v_^n_.,x_Symbol] :=
          With[{tmp=InverseFunctionOfLinear[u,x]},
          -(-Discriminant[v,x]/(4*Coefficient[v,x,2]))^n/Coefficient[tmp[[1]],x,1]*
        \tSubst[Int[SimplifyIntegrand[SubstForInverseFunction[u,tmp,x]*Csc[x]^(2*(n+1)),x],x], x, tmp] /;
         Not[FalseQ[tmp]] && EqQ[Head[tmp],ArcCot] && EqQ[Discriminant[v,x]*tmp[[1]]^2+D[v,x]^2,0]] /;
        QuadraticQ[v,x] && ILtQ[n,0] && NegQ[Discriminant[v,x]] && MatchQ[u,r_.*f_^w_ /; FreeQ[f,x]]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_16(symbols),
        with: [u__, v_, n_, x_],
        optional: [n_],
        when: {
            iltq!(n_, 0)
                && rubi_inverse_linear_quadratic_match(&u__, &v_, x_, RubiInverseKind::ArcCot)
                    .is_some()
        },
        rhs: {
            let matched =
                rubi_inverse_linear_quadratic_match(&u__, &v_, x_, RubiInverseKind::ArcCot).rubi_rhs();
            let inverse = rubi_inverse_function_of_linear(&u__, x_, RubiInverseKind::ArcCot).rubi_rhs();
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let exponent = Atom::num(2) * (&n_ + 1);
            let transformed_u = rubi_subst_for_inverse_function(
                &u__,
                x_,
                substitution_symbol,
                &inverse,
                RubiInverseKind::ArcCot,
            );
            let payload = rubi_simplify_integrand(
                &(transformed_u * sub_atom.csc().pow(exponent)),
                substitution_symbol,
            );
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            let prefactor = (-matched.discriminant / (Atom::num(4) * matched.quadratic_coeff)).pow(&n_)
                / matched.linear_slope;
            let result = -prefactor * rubi_subst(&primitive, substitution_symbol, inverse.tmp);
            rubi_simp(&result, x_)
        },
    ));
}

fn push_rules_rule_5686(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 5686,
        source: "Int[ArcTan[c_.+d_.*Tan[a_.+b_.*x_]],x_Symbol] :=
          x*ArcTan[c+d*Tan[a+b*x]] -
          I*b \\[Star] Int[x/(c+I*d+c*E^(2*I*a+2*I*b*x)),x] /;
        FreeQ[{a,b,c,d},x] && EqQ[(c+I*d)^2,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [c__, d__, a__, b__, x_],
        optional: [c__, d__, a__, b__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && eqq!((&c__ + Atom::i() * &d__).pow(2), -1)
        },
        rhs: {
            let i = Atom::i();
            let angle = &a__ + &b__ * x_;
            let exponential = (Atom::num(2) * &i * &a__ + Atom::num(2) * &i * &b__ * x_).exp();
            let denominator = &c__ + &i * &d__ + &c__ * exponential;
            rubi_simp(&(x_ * (&c__ + &d__ * angle.tan()).atan()), x_)
                    + rubi_star(-(&i * &b__), rubi_rhs_int(&(x_ / denominator), x_))
        },
    ));
}

fn push_rules_rule_5687(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 5687,
        source: "Int[ArcCot[c_.+d_.*Tan[a_.+b_.*x_]],x_Symbol] :=
          x*ArcCot[c+d*Tan[a+b*x]] +
          I*b \\[Star] Int[x/(c+I*d+c*E^(2*I*a+2*I*b*x)),x] /;
        FreeQ[{a,b,c,d},x] && EqQ[(c+I*d)^2,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [c__, d__, a__, b__, x_],
        optional: [c__, d__, a__, b__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && eqq!((&c__ + Atom::i() * &d__).pow(2), -1)
        },
        rhs: {
            let i = Atom::i();
            let angle = &a__ + &b__ * x_;
            let exponential = (Atom::num(2) * &i * &a__ + Atom::num(2) * &i * &b__ * x_).exp();
            let denominator = &c__ + &i * &d__ + &c__ * exponential;
            rubi_simp(&(x_ * (&c__ + &d__ * angle.tan()).acot()), x_)
                    + rubi_star(&i * &b__, rubi_rhs_int(&(x_ / denominator), x_))
        },
    ));
}

fn push_rules_rule_5688(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 5688,
        source: "Int[ArcTan[c_.+d_.*Cot[a_.+b_.*x_]],x_Symbol] :=
          x*ArcTan[c+d*Cot[a+b*x]] -
          I*b \\[Star] Int[x/(c-I*d-c*E^(2*I*a+2*I*b*x)),x] /;
        FreeQ[{a,b,c,d},x] && EqQ[(c-I*d)^2,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [c__, d__, a__, b__, x_],
        optional: [c__, d__, a__, b__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && eqq!((&c__ - Atom::i() * &d__).pow(2), -1)
        },
        rhs: {
            let i = Atom::i();
            let angle = &a__ + &b__ * x_;
            let exponential = (Atom::num(2) * &i * &a__ + Atom::num(2) * &i * &b__ * x_).exp();
            let denominator = &c__ - &i * &d__ - &c__ * exponential;
            rubi_simp(&(x_ * (&c__ + &d__ * angle.cot()).atan()), x_)
                    + rubi_star(-(&i * &b__), rubi_rhs_int(&(x_ / denominator), x_))
        },
    ));
}

fn push_rules_rule_5689(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 5689,
        source: "Int[ArcCot[c_.+d_.*Cot[a_.+b_.*x_]],x_Symbol] :=
          x*ArcCot[c+d*Cot[a+b*x]] +
          I*b \\[Star] Int[x/(c-I*d-c*E^(2*I*a+2*I*b*x)),x] /;
        FreeQ[{a,b,c,d},x] && EqQ[(c-I*d)^2,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [c__, d__, a__, b__, x_],
        optional: [c__, d__, a__, b__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && eqq!((&c__ - Atom::i() * &d__).pow(2), -1)
        },
        rhs: {
            let i = Atom::i();
            let angle = &a__ + &b__ * x_;
            let exponential = (Atom::num(2) * &i * &a__ + Atom::num(2) * &i * &b__ * x_).exp();
            let denominator = &c__ - &i * &d__ - &c__ * exponential;
            rubi_simp(&(x_ * (&c__ + &d__ * angle.cot()).acot()), x_)
                    + rubi_star(&i * &b__, rubi_rhs_int(&(x_ / denominator), x_))
        },
    ));
}

fn push_rules_rule_5690(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 5690,
        source: "Int[ArcTan[c_.+d_.*Tan[a_.+b_.*x_]],x_Symbol] :=
          x*ArcTan[c+d*Tan[a+b*x]] -
          b*(1+I*c+d) \\[Star] Int[x*E^(2*I*a+2*I*b*x)/(1+I*c-d+(1+I*c+d)*E^(2*I*a+2*I*b*x)),x] +
          b*(1-I*c-d) \\[Star] Int[x*E^(2*I*a+2*I*b*x)/(1-I*c+d+(1-I*c-d)*E^(2*I*a+2*I*b*x)),x] /;
        FreeQ[{a,b,c,d},x] && NeQ[(c+I*d)^2,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [c__, d__, a__, b__, x_],
        optional: [c__, d__, a__, b__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && neq!((&c__ + Atom::i() * &d__).pow(2), -1)
        },
        rhs: {
            let i = Atom::i();
            let angle = &a__ + &b__ * x_;
            let exponential = (Atom::num(2) * &i * &a__ + Atom::num(2) * &i * &b__ * x_).exp();
            let factor1 = Atom::num(1) + &i * &c__ + &d__;
            let factor2 = Atom::num(1) - &i * &c__ - &d__;
            let denominator1 = Atom::num(1) + &i * &c__ - &d__ + &factor1 * &exponential;
            let denominator2 = Atom::num(1) - &i * &c__ + &d__ + &factor2 * &exponential;
            rubi_simp(&(x_ * (&c__ + &d__ * angle.tan()).atan()), x_)
                    + rubi_star(-(&b__ * &factor1), rubi_rhs_int(&(x_ * &exponential / denominator1), x_))
                    + rubi_star(&b__ * &factor2, rubi_rhs_int(&(x_ * exponential / denominator2), x_))
        },
    ));
}

fn push_rules_rule_5691(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 5691,
        source: "Int[ArcCot[c_.+d_.*Tan[a_.+b_.*x_]],x_Symbol] :=
          x*ArcCot[c+d*Tan[a+b*x]] +
          b*(1+I*c+d) \\[Star] Int[x*E^(2*I*a+2*I*b*x)/(1+I*c-d+(1+I*c+d)*E^(2*I*a+2*I*b*x)),x] -
          b*(1-I*c-d) \\[Star] Int[x*E^(2*I*a+2*I*b*x)/(1-I*c+d+(1-I*c-d)*E^(2*I*a+2*I*b*x)),x] /;
        FreeQ[{a,b,c,d},x] && NeQ[(c+I*d)^2,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [c__, d__, a__, b__, x_],
        optional: [c__, d__, a__, b__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && neq!((&c__ + Atom::i() * &d__).pow(2), -1)
        },
        rhs: {
            let i = Atom::i();
            let angle = &a__ + &b__ * x_;
            let exponential = (Atom::num(2) * &i * &a__ + Atom::num(2) * &i * &b__ * x_).exp();
            let factor1 = Atom::num(1) + &i * &c__ + &d__;
            let factor2 = Atom::num(1) - &i * &c__ - &d__;
            let denominator1 = Atom::num(1) + &i * &c__ - &d__ + &factor1 * &exponential;
            let denominator2 = Atom::num(1) - &i * &c__ + &d__ + &factor2 * &exponential;
            rubi_simp(&(x_ * (&c__ + &d__ * angle.tan()).acot()), x_)
                    + rubi_star(&b__ * &factor1, rubi_rhs_int(&(x_ * &exponential / denominator1), x_))
                    + rubi_star(-(&b__ * &factor2), rubi_rhs_int(&(x_ * exponential / denominator2), x_))
        },
    ));
}

fn push_rules_rule_5692(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 5692,
        source: "Int[ArcTan[c_.+d_.*Cot[a_.+b_.*x_]],x_Symbol] :=
          x*ArcTan[c+d*Cot[a+b*x]] +
          b*(1+I*c-d) \\[Star] Int[x*E^(2*I*a+2*I*b*x)/(1+I*c+d-(1+I*c-d)*E^(2*I*a+2*I*b*x)),x] -
          b*(1-I*c+d) \\[Star] Int[x*E^(2*I*a+2*I*b*x)/(1-I*c-d-(1-I*c+d)*E^(2*I*a+2*I*b*x)),x] /;
        FreeQ[{a,b,c,d},x] && NeQ[(c+I*d)^2,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [c__, d__, a__, b__, x_],
        optional: [c__, d__, a__, b__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && neq!((&c__ + Atom::i() * &d__).pow(2), -1)
        },
        rhs: {
            let i = Atom::i();
            let angle = &a__ + &b__ * x_;
            let exponential = (Atom::num(2) * &i * &a__ + Atom::num(2) * &i * &b__ * x_).exp();
            let factor1 = Atom::num(1) + &i * &c__ - &d__;
            let factor2 = Atom::num(1) - &i * &c__ + &d__;
            let denominator1 = Atom::num(1) + &i * &c__ + &d__ - &factor1 * &exponential;
            let denominator2 = Atom::num(1) - &i * &c__ - &d__ - &factor2 * &exponential;
            rubi_simp(&(x_ * (&c__ + &d__ * angle.cot()).atan()), x_)
                    + rubi_star(&b__ * &factor1, rubi_rhs_int(&(x_ * &exponential / denominator1), x_))
                    + rubi_star(-(&b__ * &factor2), rubi_rhs_int(&(x_ * exponential / denominator2), x_))
        },
    ));
}

fn push_rules_rule_5693(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 5693,
        source: "Int[ArcCot[c_.+d_.*Cot[a_.+b_.*x_]],x_Symbol] :=
          x*ArcCot[c+d*Cot[a+b*x]] -
          b*(1+I*c-d) \\[Star] Int[x*E^(2*I*a+2*I*b*x)/(1+I*c+d-(1+I*c-d)*E^(2*I*a+2*I*b*x)),x] +
          b*(1-I*c+d) \\[Star] Int[x*E^(2*I*a+2*I*b*x)/(1-I*c-d-(1-I*c+d)*E^(2*I*a+2*I*b*x)),x] /;
        FreeQ[{a,b,c,d},x] && NeQ[(c-I*d)^2,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [c__, d__, a__, b__, x_],
        optional: [c__, d__, a__, b__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && neq!((&c__ - Atom::i() * &d__).pow(2), -1)
        },
        rhs: {
            let i = Atom::i();
            let angle = &a__ + &b__ * x_;
            let exponential = (Atom::num(2) * &i * &a__ + Atom::num(2) * &i * &b__ * x_).exp();
            let factor1 = Atom::num(1) + &i * &c__ - &d__;
            let factor2 = Atom::num(1) - &i * &c__ + &d__;
            let denominator1 = Atom::num(1) + &i * &c__ + &d__ - &factor1 * &exponential;
            let denominator2 = Atom::num(1) - &i * &c__ - &d__ - &factor2 * &exponential;
            rubi_simp(&(x_ * (&c__ + &d__ * angle.cot()).acot()), x_)
                    - rubi_star(&b__ * &factor1, rubi_rhs_int(&(x_ * &exponential / denominator1), x_))
                    + rubi_star(&b__ * &factor2, rubi_rhs_int(&(x_ * exponential / denominator2), x_))
        },
    ));
}

fn push_rules_rule_5694(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, x_);
    rules.push(rubi_rule!(
        order: 5694,
        source: "Int[(e_.+f_.*x_)^m_.*ArcTan[c_.+d_.*Tan[a_.+b_.*x_]],x_Symbol] :=
          (e+f*x)^(m+1)*ArcTan[c+d*Tan[a+b*x]]/(f*(m+1)) -
          I*b/(f*(m+1)) \\[Star] Int[(e+f*x)^(m+1)/(c+I*d+c*E^(2*I*a+2*I*b*x)),x] /;
        FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && EqQ[(c+I*d)^2,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_13(symbols),
        with: [e__, f__, m_, c__, d__, a__, b__, x_],
        optional: [e__, f__, m_, c__, d__, a__, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && igtq!(m_, 0)
                && eqq!((&c__ + Atom::i() * &d__).pow(2), -1)
        },
        rhs: {
            let i = Atom::i();
            let angle = &a__ + &b__ * x_;
            let base = &e__ + &f__ * x_;
            let m_plus_one = &m_ + 1;
            let powered_base = base.pow(&m_plus_one);
            let denominator_scale = &f__ * &m_plus_one;
            let exponential = (Atom::num(2) * &i * &a__ + Atom::num(2) * &i * &b__ * x_).exp();
            let denominator = &c__ + &i * &d__ + &c__ * exponential;
            rubi_simp(&(&powered_base * (&c__ + &d__ * angle.tan()).atan() / &denominator_scale), x_)
                    - rubi_star(&i * &b__ / &denominator_scale, rubi_rhs_int(&(&powered_base / denominator), x_))
        },
    ));
}

fn push_rules_rule_5695(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, x_);
    rules.push(rubi_rule!(
        order: 5695,
        source: "Int[(e_.+f_.*x_)^m_.*ArcCot[c_.+d_.*Tan[a_.+b_.*x_]],x_Symbol] :=
          (e+f*x)^(m+1)*ArcCot[c+d*Tan[a+b*x]]/(f*(m+1)) +
          I*b/(f*(m+1)) \\[Star] Int[(e+f*x)^(m+1)/(c+I*d+c*E^(2*I*a+2*I*b*x)),x] /;
        FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && EqQ[(c+I*d)^2,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_12(symbols),
        with: [e__, f__, m_, c__, d__, a__, b__, x_],
        optional: [e__, f__, m_, c__, d__, a__, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && igtq!(m_, 0)
                && eqq!((&c__ + Atom::i() * &d__).pow(2), -1)
        },
        rhs: {
            let i = Atom::i();
            let angle = &a__ + &b__ * x_;
            let base = &e__ + &f__ * x_;
            let m_plus_one = &m_ + 1;
            let powered_base = base.pow(&m_plus_one);
            let denominator_scale = &f__ * &m_plus_one;
            let exponential = (Atom::num(2) * &i * &a__ + Atom::num(2) * &i * &b__ * x_).exp();
            let denominator = &c__ + &i * &d__ + &c__ * exponential;
            rubi_simp(&(&powered_base * (&c__ + &d__ * angle.tan()).acot() / &denominator_scale), x_)
                    + rubi_star(&i * &b__ / &denominator_scale, rubi_rhs_int(&(&powered_base / denominator), x_))
        },
    ));
}

fn push_rules_rule_5696(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, x_);
    rules.push(rubi_rule!(
        order: 5696,
        source: "Int[(e_.+f_.*x_)^m_.*ArcTan[c_.+d_.*Cot[a_.+b_.*x_]],x_Symbol] :=
          (e+f*x)^(m+1)*ArcTan[c+d*Cot[a+b*x]]/(f*(m+1)) -
          I*b/(f*(m+1)) \\[Star] Int[(e+f*x)^(m+1)/(c-I*d-c*E^(2*I*a+2*I*b*x)),x] /;
        FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && EqQ[(c-I*d)^2,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [e__, f__, m_, c__, d__, a__, b__, x_],
        optional: [e__, f__, m_, c__, d__, a__, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && igtq!(m_, 0)
                && eqq!((&c__ - Atom::i() * &d__).pow(2), -1)
        },
        rhs: {
            let i = Atom::i();
            let angle = &a__ + &b__ * x_;
            let base = &e__ + &f__ * x_;
            let m_plus_one = &m_ + 1;
            let powered_base = base.pow(&m_plus_one);
            let denominator_scale = &f__ * &m_plus_one;
            let exponential = (Atom::num(2) * &i * &a__ + Atom::num(2) * &i * &b__ * x_).exp();
            let denominator = &c__ - &i * &d__ - &c__ * exponential;
            rubi_simp(&(&powered_base * (&c__ + &d__ * angle.cot()).atan() / &denominator_scale), x_)
                    - rubi_star(&i * &b__ / &denominator_scale, rubi_rhs_int(&(&powered_base / denominator), x_))
        },
    ));
}

fn push_rules_rule_5697(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, x_);
    rules.push(rubi_rule!(
        order: 5697,
        source: "Int[(e_.+f_.*x_)^m_.*ArcCot[c_.+d_.*Cot[a_.+b_.*x_]],x_Symbol] :=
          (e+f*x)^(m+1)*ArcCot[c+d*Cot[a+b*x]]/(f*(m+1)) +
          I*b/(f*(m+1)) \\[Star] Int[(e+f*x)^(m+1)/(c-I*d-c*E^(2*I*a+2*I*b*x)),x] /;
        FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && EqQ[(c-I*d)^2,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [e__, f__, m_, c__, d__, a__, b__, x_],
        optional: [e__, f__, m_, c__, d__, a__, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && igtq!(m_, 0)
                && eqq!((&c__ - Atom::i() * &d__).pow(2), -1)
        },
        rhs: {
            let i = Atom::i();
            let angle = &a__ + &b__ * x_;
            let base = &e__ + &f__ * x_;
            let m_plus_one = &m_ + 1;
            let powered_base = base.pow(&m_plus_one);
            let denominator_scale = &f__ * &m_plus_one;
            let exponential = (Atom::num(2) * &i * &a__ + Atom::num(2) * &i * &b__ * x_).exp();
            let denominator = &c__ - &i * &d__ - &c__ * exponential;
            rubi_simp(&(&powered_base * (&c__ + &d__ * angle.cot()).acot() / &denominator_scale), x_)
                    + rubi_star(&i * &b__ / &denominator_scale, rubi_rhs_int(&(&powered_base / denominator), x_))
        },
    ));
}

fn push_rules_rule_5698(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, x_);
    rules.push(rubi_rule!(
        order: 5698,
        source: "Int[(e_.+f_.*x_)^m_.*ArcTan[c_.+d_.*Tan[a_.+b_.*x_]],x_Symbol] :=
          (e+f*x)^(m+1)*ArcTan[c+d*Tan[a+b*x]]/(f*(m+1)) -
          b*(1+I*c+d)/(f*(m+1)) \\[Star] Int[(e+f*x)^(m+1)*E^(2*I*a+2*I*b*x)/(1+I*c-d+(1+I*c+d)*E^(2*I*a+2*I*b*x)),x] +
          b*(1-I*c-d)/(f*(m+1)) \\[Star] Int[(e+f*x)^(m+1)*E^(2*I*a+2*I*b*x)/(1-I*c+d+(1-I*c-d)*E^(2*I*a+2*I*b*x)),x] /;
        FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && NeQ[(c+I*d)^2,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_13(symbols),
        with: [e__, f__, m_, c__, d__, a__, b__, x_],
        optional: [e__, f__, m_, c__, d__, a__, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && igtq!(m_, 0)
                && neq!((&c__ + Atom::i() * &d__).pow(2), -1)
        },
        rhs: {
            let i = Atom::i();
            let angle = &a__ + &b__ * x_;
            let base = &e__ + &f__ * x_;
            let m_plus_one = &m_ + 1;
            let powered_base = base.pow(&m_plus_one);
            let denominator_scale = &f__ * &m_plus_one;
            let exponential = (Atom::num(2) * &i * &a__ + Atom::num(2) * &i * &b__ * x_).exp();
            let factor1 = Atom::num(1) + &i * &c__ + &d__;
            let factor2 = Atom::num(1) - &i * &c__ - &d__;
            let denominator1 = Atom::num(1) + &i * &c__ - &d__ + &factor1 * &exponential;
            let denominator2 = Atom::num(1) - &i * &c__ + &d__ + &factor2 * &exponential;
            rubi_simp(&(&powered_base * (&c__ + &d__ * angle.tan()).atan() / &denominator_scale), x_)
                    - rubi_star(&b__ * &factor1 / &denominator_scale, rubi_rhs_int(&(&powered_base * &exponential / denominator1), x_))
                    + rubi_star(&b__ * &factor2 / &denominator_scale, rubi_rhs_int(&(&powered_base * exponential / denominator2), x_))
        },
    ));
}

fn push_rules_rule_5699(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, x_);
    rules.push(rubi_rule!(
        order: 5699,
        source: "Int[(e_.+f_.*x_)^m_.*ArcCot[c_.+d_.*Tan[a_.+b_.*x_]],x_Symbol] :=
          (e+f*x)^(m+1)*ArcCot[c+d*Tan[a+b*x]]/(f*(m+1)) +
          b*(1+I*c+d)/(f*(m+1)) \\[Star] Int[(e+f*x)^(m+1)*E^(2*I*a+2*I*b*x)/(1+I*c-d+(1+I*c+d)*E^(2*I*a+2*I*b*x)),x] -
          b*(1-I*c-d)/(f*(m+1)) \\[Star] Int[(e+f*x)^(m+1)*E^(2*I*a+2*I*b*x)/(1-I*c+d+(1-I*c-d)*E^(2*I*a+2*I*b*x)),x] /;
        FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && NeQ[(c+I*d)^2,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_12(symbols),
        with: [e__, f__, m_, c__, d__, a__, b__, x_],
        optional: [e__, f__, m_, c__, d__, a__, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && igtq!(m_, 0)
                && neq!((&c__ + Atom::i() * &d__).pow(2), -1)
        },
        rhs: {
            let i = Atom::i();
            let angle = &a__ + &b__ * x_;
            let base = &e__ + &f__ * x_;
            let m_plus_one = &m_ + 1;
            let powered_base = base.pow(&m_plus_one);
            let denominator_scale = &f__ * &m_plus_one;
            let exponential = (Atom::num(2) * &i * &a__ + Atom::num(2) * &i * &b__ * x_).exp();
            let factor1 = Atom::num(1) + &i * &c__ + &d__;
            let factor2 = Atom::num(1) - &i * &c__ - &d__;
            let denominator1 = Atom::num(1) + &i * &c__ - &d__ + &factor1 * &exponential;
            let denominator2 = Atom::num(1) - &i * &c__ + &d__ + &factor2 * &exponential;
            rubi_simp(&(&powered_base * (&c__ + &d__ * angle.tan()).acot() / &denominator_scale), x_)
                    + rubi_star(&b__ * &factor1 / &denominator_scale, rubi_rhs_int(&(&powered_base * &exponential / denominator1), x_))
                    - rubi_star(&b__ * &factor2 / &denominator_scale, rubi_rhs_int(&(&powered_base * exponential / denominator2), x_))
        },
    ));
}

fn push_rules_rule_5700(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, x_);
    rules.push(rubi_rule!(
        order: 5700,
        source: "Int[(e_.+f_.*x_)^m_.*ArcTan[c_.+d_.*Cot[a_.+b_.*x_]],x_Symbol] :=
          (e+f*x)^(m+1)*ArcTan[c+d*Cot[a+b*x]]/(f*(m+1)) +
          b*(1+I*c-d)/(f*(m+1)) \\[Star] Int[(e+f*x)^(m+1)*E^(2*I*a+2*I*b*x)/(1+I*c+d-(1+I*c-d)*E^(2*I*a+2*I*b*x)),x] -
          b*(1-I*c+d)/(f*(m+1)) \\[Star] Int[(e+f*x)^(m+1)*E^(2*I*a+2*I*b*x)/(1-I*c-d-(1-I*c+d)*E^(2*I*a+2*I*b*x)),x] /;
        FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && NeQ[(c-I*d)^2,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [e__, f__, m_, c__, d__, a__, b__, x_],
        optional: [e__, f__, m_, c__, d__, a__, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && igtq!(m_, 0)
                && neq!((&c__ - Atom::i() * &d__).pow(2), -1)
        },
        rhs: {
            let i = Atom::i();
            let angle = &a__ + &b__ * x_;
            let base = &e__ + &f__ * x_;
            let m_plus_one = &m_ + 1;
            let powered_base = base.pow(&m_plus_one);
            let denominator_scale = &f__ * &m_plus_one;
            let exponential = (Atom::num(2) * &i * &a__ + Atom::num(2) * &i * &b__ * x_).exp();
            let factor1 = Atom::num(1) + &i * &c__ - &d__;
            let factor2 = Atom::num(1) - &i * &c__ + &d__;
            let denominator1 = Atom::num(1) + &i * &c__ + &d__ - &factor1 * &exponential;
            let denominator2 = Atom::num(1) - &i * &c__ - &d__ - &factor2 * &exponential;
            rubi_simp(&(&powered_base * (&c__ + &d__ * angle.cot()).atan() / &denominator_scale), x_)
                    + rubi_star(&b__ * &factor1 / &denominator_scale, rubi_rhs_int(&(&powered_base * &exponential / denominator1), x_))
                    - rubi_star(&b__ * &factor2 / &denominator_scale, rubi_rhs_int(&(&powered_base * exponential / denominator2), x_))
        },
    ));
}

fn push_rules_rule_5701(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, x_);
    rules.push(rubi_rule!(
        order: 5701,
        source: "Int[(e_.+f_.*x_)^m_.*ArcCot[c_.+d_.*Cot[a_.+b_.*x_]],x_Symbol] :=
          (e+f*x)^(m+1)*ArcCot[c+d*Cot[a+b*x]]/(f*(m+1)) -
          b*(1+I*c-d)/(f*(m+1)) \\[Star] Int[(e+f*x)^(m+1)*E^(2*I*a+2*I*b*x)/(1+I*c+d-(1+I*c-d)*E^(2*I*a+2*I*b*x)),x] +
          b*(1-I*c+d)/(f*(m+1)) \\[Star] Int[(e+f*x)^(m+1)*E^(2*I*a+2*I*b*x)/(1-I*c-d-(1-I*c+d)*E^(2*I*a+2*I*b*x)),x] /;
        FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && NeQ[(c-I*d)^2,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [e__, f__, m_, c__, d__, a__, b__, x_],
        optional: [e__, f__, m_, c__, d__, a__, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && igtq!(m_, 0)
                && neq!((&c__ - Atom::i() * &d__).pow(2), -1)
        },
        rhs: {
            let i = Atom::i();
            let angle = &a__ + &b__ * x_;
            let base = &e__ + &f__ * x_;
            let m_plus_one = &m_ + 1;
            let powered_base = base.pow(&m_plus_one);
            let denominator_scale = &f__ * &m_plus_one;
            let exponential = (Atom::num(2) * &i * &a__ + Atom::num(2) * &i * &b__ * x_).exp();
            let factor1 = Atom::num(1) + &i * &c__ - &d__;
            let factor2 = Atom::num(1) - &i * &c__ + &d__;
            let denominator1 = Atom::num(1) + &i * &c__ + &d__ - &factor1 * &exponential;
            let denominator2 = Atom::num(1) - &i * &c__ - &d__ - &factor2 * &exponential;
            rubi_simp(&(&powered_base * (&c__ + &d__ * angle.cot()).acot() / &denominator_scale), x_)
                    - rubi_star(&b__ * &factor1 / &denominator_scale, rubi_rhs_int(&(&powered_base * &exponential / denominator1), x_))
                    + rubi_star(&b__ * &factor2 / &denominator_scale, rubi_rhs_int(&(&powered_base * exponential / denominator2), x_))
        },
    ));
}

fn push_rules_rule_5702(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, x_);
    rules.push(rubi_rule!(
        order: 5702,
        source: "Int[ArcTan[Tanh[a_.+b_.*x_]],x_Symbol] :=
          x*ArcTan[Tanh[a+b*x]] - b \\[Star] Int[x*Sech[2*a+2*b*x],x] /;
        FreeQ[{a,b},x]",
        desc: "Integration by parts",
        refs: [],
        pattern: (a__ + b__ * x_).tanh().atan(),
        with: [a__, b__, x_],
        optional: [a__, b__],
        when: { freeq!([a__, b__], x_) },
        rhs: {
            let angle = &a__ + &b__ * x_;
            let sech_argument = Atom::num(2) * &a__ + Atom::num(2) * &b__ * x_;
            rubi_simp(&(x_ * angle.tanh().atan()), x_)
                    - rubi_star(b__, rubi_rhs_int(&(x_ * sech_argument.sech()), x_))
        },
    ));
}

fn push_rules_rule_5703(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, x_);
    rules.push(rubi_rule!(
        order: 5703,
        source: "Int[ArcCot[Tanh[a_.+b_.*x_]],x_Symbol] :=
          x*ArcCot[Tanh[a+b*x]] + b \\[Star] Int[x*Sech[2*a+2*b*x],x] /;
        FreeQ[{a,b},x]",
        desc: "Integration by parts",
        refs: [],
        pattern: (a__ + b__ * x_).tanh().acot(),
        with: [a__, b__, x_],
        optional: [a__, b__],
        when: { freeq!([a__, b__], x_) },
        rhs: {
            let angle = &a__ + &b__ * x_;
            let sech_argument = Atom::num(2) * &a__ + Atom::num(2) * &b__ * x_;
            rubi_simp(&(x_ * angle.tanh().acot()), x_)
                    + rubi_star(b__, rubi_rhs_int(&(x_ * sech_argument.sech()), x_))
        },
    ));
}

fn push_rules_rule_5704(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, x_);
    rules.push(rubi_rule!(
        order: 5704,
        source: "Int[ArcTan[Coth[a_.+b_.*x_]],x_Symbol] :=
          x*ArcTan[Coth[a+b*x]] + b \\[Star] Int[x*Sech[2*a+2*b*x],x] /;
        FreeQ[{a,b},x]",
        desc: "Integration by parts",
        refs: [],
        pattern: (a__ + b__ * x_).coth().atan(),
        with: [a__, b__, x_],
        optional: [a__, b__],
        when: { freeq!([a__, b__], x_) },
        rhs: {
            let angle = &a__ + &b__ * x_;
            let sech_argument = Atom::num(2) * &a__ + Atom::num(2) * &b__ * x_;
            rubi_simp(&(x_ * angle.coth().atan()), x_)
                    + rubi_star(b__, rubi_rhs_int(&(x_ * sech_argument.sech()), x_))
        },
    ));
}

fn push_rules_rule_5705(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, x_);
    rules.push(rubi_rule!(
        order: 5705,
        source: "Int[ArcCot[Coth[a_.+b_.*x_]],x_Symbol] :=
          x*ArcCot[Coth[a+b*x]] - b \\[Star] Int[x*Sech[2*a+2*b*x],x] /;
        FreeQ[{a,b},x]",
        desc: "Integration by parts",
        refs: [],
        pattern: (a__ + b__ * x_).coth().acot(),
        with: [a__, b__, x_],
        optional: [a__, b__],
        when: { freeq!([a__, b__], x_) },
        rhs: {
            let angle = &a__ + &b__ * x_;
            let sech_argument = Atom::num(2) * &a__ + Atom::num(2) * &b__ * x_;
            rubi_simp(&(x_ * angle.coth().acot()), x_)
                    - rubi_star(b__, rubi_rhs_int(&(x_ * sech_argument.sech()), x_))
        },
    ));
}

fn push_rules_rule_5706(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, e__, f__, m_, x_);
    rules.push(rubi_rule!(
        order: 5706,
        source: "Int[(e_.+f_.*x_)^m_.*ArcTan[Tanh[a_.+b_.*x_]],x_Symbol] :=
          (e+f*x)^(m+1)*ArcTan[Tanh[a+b*x]]/(f*(m+1)) - b/(f*(m+1)) \\[Star] Int[(e+f*x)^(m+1)*Sech[2*a+2*b*x],x] /;
        FreeQ[{a,b,e,f},x] && IGtQ[m,0]",
        desc: "Integration by parts",
        refs: [],
        pattern: (e__ + f__ * x_).pow(m_) * (a__ + b__ * x_).tanh().atan(),
        with: [e__, f__, m_, a__, b__, x_],
        optional: [e__, f__, m_, a__, b__],
        when: {
            freeq!([a__, b__, e__, f__], x_) && igtq!(m_, 0)
        },
        rhs: {
            let angle = &a__ + &b__ * x_;
            let base = &e__ + &f__ * x_;
            let m_plus_one = &m_ + 1;
            let powered_base = base.pow(&m_plus_one);
            let denominator_scale = &f__ * &m_plus_one;
            let sech_argument = Atom::num(2) * &a__ + Atom::num(2) * &b__ * x_;
            rubi_simp(&(&powered_base * angle.tanh().atan() / &denominator_scale), x_)
                    - rubi_star(&b__ / &denominator_scale, rubi_rhs_int(&(&powered_base * sech_argument.sech()), x_))
        },
    ));
}

fn push_rules_rule_5707(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, e__, f__, m_, x_);
    rules.push(rubi_rule!(
        order: 5707,
        source: "Int[(e_.+f_.*x_)^m_.*ArcCot[Tanh[a_.+b_.*x_]],x_Symbol] :=
          (e+f*x)^(m+1)*ArcCot[Tanh[a+b*x]]/(f*(m+1)) + b/(f*(m+1)) \\[Star] Int[(e+f*x)^(m+1)*Sech[2*a+2*b*x],x] /;
        FreeQ[{a,b,e,f},x] && IGtQ[m,0]",
        desc: "Integration by parts",
        refs: [],
        pattern: (e__ + f__ * x_).pow(m_) * (a__ + b__ * x_).tanh().acot(),
        with: [e__, f__, m_, a__, b__, x_],
        optional: [e__, f__, m_, a__, b__],
        when: {
            freeq!([a__, b__, e__, f__], x_) && igtq!(m_, 0)
        },
        rhs: {
            let angle = &a__ + &b__ * x_;
            let base = &e__ + &f__ * x_;
            let m_plus_one = &m_ + 1;
            let powered_base = base.pow(&m_plus_one);
            let denominator_scale = &f__ * &m_plus_one;
            let sech_argument = Atom::num(2) * &a__ + Atom::num(2) * &b__ * x_;
            rubi_simp(&(&powered_base * angle.tanh().acot() / &denominator_scale), x_)
                    + rubi_star(&b__ / &denominator_scale, rubi_rhs_int(&(&powered_base * sech_argument.sech()), x_))
        },
    ));
}

fn push_rules_rule_5708(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, e__, f__, m_, x_);
    rules.push(rubi_rule!(
        order: 5708,
        source: "Int[(e_.+f_.*x_)^m_.*ArcTan[Coth[a_.+b_.*x_]],x_Symbol] :=
          (e+f*x)^(m+1)*ArcTan[Coth[a+b*x]]/(f*(m+1)) + b/(f*(m+1)) \\[Star] Int[(e+f*x)^(m+1)*Sech[2*a+2*b*x],x] /;
        FreeQ[{a,b,e,f},x] && IGtQ[m,0]",
        desc: "Integration by parts",
        refs: [],
        pattern: (e__ + f__ * x_).pow(m_) * (a__ + b__ * x_).coth().atan(),
        with: [e__, f__, m_, a__, b__, x_],
        optional: [e__, f__, m_, a__, b__],
        when: {
            freeq!([a__, b__, e__, f__], x_) && igtq!(m_, 0)
        },
        rhs: {
            let angle = &a__ + &b__ * x_;
            let base = &e__ + &f__ * x_;
            let m_plus_one = &m_ + 1;
            let powered_base = base.pow(&m_plus_one);
            let denominator_scale = &f__ * &m_plus_one;
            let sech_argument = Atom::num(2) * &a__ + Atom::num(2) * &b__ * x_;
            rubi_simp(&(&powered_base * angle.coth().atan() / &denominator_scale), x_)
                    + rubi_star(&b__ / &denominator_scale, rubi_rhs_int(&(&powered_base * sech_argument.sech()), x_))
        },
    ));
}

fn push_rules_rule_5709(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, e__, f__, m_, x_);
    rules.push(rubi_rule!(
        order: 5709,
        source: "Int[(e_.+f_.*x_)^m_.*ArcCot[Coth[a_.+b_.*x_]],x_Symbol] :=
          (e+f*x)^(m+1)*ArcCot[Coth[a+b*x]]/(f*(m+1)) - b/(f*(m+1)) \\[Star] Int[(e+f*x)^(m+1)*Sech[2*a+2*b*x],x] /;
        FreeQ[{a,b,e,f},x] && IGtQ[m,0]",
        desc: "Integration by parts",
        refs: [],
        pattern: (e__ + f__ * x_).pow(m_) * (a__ + b__ * x_).coth().acot(),
        with: [e__, f__, m_, a__, b__, x_],
        optional: [e__, f__, m_, a__, b__],
        when: {
            freeq!([a__, b__, e__, f__], x_) && igtq!(m_, 0)
        },
        rhs: {
            let angle = &a__ + &b__ * x_;
            let base = &e__ + &f__ * x_;
            let m_plus_one = &m_ + 1;
            let powered_base = base.pow(&m_plus_one);
            let denominator_scale = &f__ * &m_plus_one;
            let sech_argument = Atom::num(2) * &a__ + Atom::num(2) * &b__ * x_;
            rubi_simp(&(&powered_base * angle.coth().acot() / &denominator_scale), x_)
                    - rubi_star(&b__ / &denominator_scale, rubi_rhs_int(&(&powered_base * sech_argument.sech()), x_))
        },
    ));
}

fn push_rules_rule_5710(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 5710,
        source: "Int[ArcTan[c_.+d_.*Tanh[a_.+b_.*x_]],x_Symbol] :=
          x*ArcTan[c+d*Tanh[a+b*x]] -
          b \\[Star] Int[x/(c-d+c*E^(2*a+2*b*x)),x] /;
        FreeQ[{a,b,c,d},x] && EqQ[(c-d)^2,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [c__, d__, a__, b__, x_],
        optional: [c__, d__, a__, b__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && eqq!((&c__ - &d__).pow(2), -1)
        },
        rhs: {
            let angle = &a__ + &b__ * x_;
            let exponential = (Atom::num(2) * &a__ + Atom::num(2) * &b__ * x_).exp();
            let denominator = &c__ - &d__ + &c__ * exponential;
            rubi_simp(&(x_ * (&c__ + &d__ * angle.tanh()).atan()), x_)
                    - rubi_star(b__, rubi_rhs_int(&(x_ / denominator), x_))
        },
    ));
}

fn push_rules_rule_5711(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 5711,
        source: "Int[ArcCot[c_.+d_.*Tanh[a_.+b_.*x_]],x_Symbol] :=
          x*ArcCot[c+d*Tanh[a+b*x]] +
          b \\[Star] Int[x/(c-d+c*E^(2*a+2*b*x)),x] /;
        FreeQ[{a,b,c,d},x] && EqQ[(c-d)^2,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [c__, d__, a__, b__, x_],
        optional: [c__, d__, a__, b__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && eqq!((&c__ - &d__).pow(2), -1)
        },
        rhs: {
            let angle = &a__ + &b__ * x_;
            let exponential = (Atom::num(2) * &a__ + Atom::num(2) * &b__ * x_).exp();
            let denominator = &c__ - &d__ + &c__ * exponential;
            rubi_simp(&(x_ * (&c__ + &d__ * angle.tanh()).acot()), x_)
                    + rubi_star(b__, rubi_rhs_int(&(x_ / denominator), x_))
        },
    ));
}

fn push_rules_rule_5712(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 5712,
        source: "Int[ArcTan[c_.+d_.*Coth[a_.+b_.*x_]],x_Symbol] :=
          x*ArcTan[c+d*Coth[a+b*x]] -
          b \\[Star] Int[x/(c-d-c*E^(2*a+2*b*x)),x] /;
        FreeQ[{a,b,c,d},x] && EqQ[(c-d)^2,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [c__, d__, a__, b__, x_],
        optional: [c__, d__, a__, b__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && eqq!((&c__ - &d__).pow(2), -1)
        },
        rhs: {
            let angle = &a__ + &b__ * x_;
            let exponential = (Atom::num(2) * &a__ + Atom::num(2) * &b__ * x_).exp();
            let denominator = &c__ - &d__ - &c__ * exponential;
            rubi_simp(&(x_ * (&c__ + &d__ * angle.coth()).atan()), x_)
                    - rubi_star(b__, rubi_rhs_int(&(x_ / denominator), x_))
        },
    ));
}

fn push_rules_rule_5713(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 5713,
        source: "Int[ArcCot[c_.+d_.*Coth[a_.+b_.*x_]],x_Symbol] :=
          x*ArcCot[c+d*Coth[a+b*x]] +
          b \\[Star] Int[x/(c-d-c*E^(2*a+2*b*x)),x] /;
        FreeQ[{a,b,c,d},x] && EqQ[(c-d)^2,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [c__, d__, a__, b__, x_],
        optional: [c__, d__, a__, b__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && eqq!((&c__ - &d__).pow(2), -1)
        },
        rhs: {
            let angle = &a__ + &b__ * x_;
            let exponential = (Atom::num(2) * &a__ + Atom::num(2) * &b__ * x_).exp();
            let denominator = &c__ - &d__ - &c__ * exponential;
            rubi_simp(&(x_ * (&c__ + &d__ * angle.coth()).acot()), x_)
                    + rubi_star(b__, rubi_rhs_int(&(x_ / denominator), x_))
        },
    ));
}

fn push_rules_rule_5714(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 5714,
        source: "Int[ArcTan[c_.+d_.*Tanh[a_.+b_.*x_]],x_Symbol] :=
          x*ArcTan[c+d*Tanh[a+b*x]] +
          I*b*(I-c-d) \\[Star] Int[x*E^(2*a+2*b*x)/(I-c+d+(I-c-d)*E^(2*a+2*b*x)),x] -
          I*b*(I+c+d) \\[Star] Int[x*E^(2*a+2*b*x)/(I+c-d+(I+c+d)*E^(2*a+2*b*x)),x] /;
        FreeQ[{a,b,c,d},x] && NeQ[(c-d)^2,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [c__, d__, a__, b__, x_],
        optional: [c__, d__, a__, b__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && neq!((&c__ - &d__).pow(2), -1)
        },
        rhs: {
            let i = Atom::i();
            let angle = &a__ + &b__ * x_;
            let exponential = (Atom::num(2) * &a__ + Atom::num(2) * &b__ * x_).exp();
            let factor1 = &i - &c__ - &d__;
            let factor2 = &i + &c__ + &d__;
            let denominator1 = &i - &c__ + &d__ + &factor1 * &exponential;
            let denominator2 = &i + &c__ - &d__ + &factor2 * &exponential;
            rubi_simp(&(x_ * (&c__ + &d__ * angle.tanh()).atan()), x_)
                    + rubi_star(&i * &b__ * &factor1, rubi_rhs_int(&(x_ * &exponential / denominator1), x_))
                    - rubi_star(&i * &b__ * &factor2, rubi_rhs_int(&(x_ * exponential / denominator2), x_))
        },
    ));
}

fn push_rules_rule_5715(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 5715,
        source: "Int[ArcCot[c_.+d_.*Tanh[a_.+b_.*x_]],x_Symbol] :=
          x*ArcCot[c+d*Tanh[a+b*x]] -
          I*b*(I-c-d) \\[Star] Int[x*E^(2*a+2*b*x)/(I-c+d+(I-c-d)*E^(2*a+2*b*x)),x] +
          I*b*(I+c+d) \\[Star] Int[x*E^(2*a+2*b*x)/(I+c-d+(I+c+d)*E^(2*a+2*b*x)),x] /;
        FreeQ[{a,b,c,d},x] && NeQ[(c-d)^2,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [c__, d__, a__, b__, x_],
        optional: [c__, d__, a__, b__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && neq!((&c__ - &d__).pow(2), -1)
        },
        rhs: {
            let i = Atom::i();
            let angle = &a__ + &b__ * x_;
            let exponential = (Atom::num(2) * &a__ + Atom::num(2) * &b__ * x_).exp();
            let factor1 = &i - &c__ - &d__;
            let factor2 = &i + &c__ + &d__;
            let denominator1 = &i - &c__ + &d__ + &factor1 * &exponential;
            let denominator2 = &i + &c__ - &d__ + &factor2 * &exponential;
            rubi_simp(&(x_ * (&c__ + &d__ * angle.tanh()).acot()), x_)
                    - rubi_star(&i * &b__ * &factor1, rubi_rhs_int(&(x_ * &exponential / denominator1), x_))
                    + rubi_star(&i * &b__ * &factor2, rubi_rhs_int(&(x_ * exponential / denominator2), x_))
        },
    ));
}

fn push_rules_rule_5716(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 5716,
        source: "Int[ArcTan[c_.+d_.*Coth[a_.+b_.*x_]],x_Symbol] :=
          x*ArcTan[c+d*Coth[a+b*x]] -
          I*b*(I-c-d) \\[Star] Int[x*E^(2*a+2*b*x)/(I-c+d-(I-c-d)*E^(2*a+2*b*x)),x] +
          I*b*(I+c+d) \\[Star] Int[x*E^(2*a+2*b*x)/(I+c-d-(I+c+d)*E^(2*a+2*b*x)),x] /;
        FreeQ[{a,b,c,d},x] && NeQ[(c-d)^2,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [c__, d__, a__, b__, x_],
        optional: [c__, d__, a__, b__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && neq!((&c__ - &d__).pow(2), -1)
        },
        rhs: {
            let i = Atom::i();
            let angle = &a__ + &b__ * x_;
            let exponential = (Atom::num(2) * &a__ + Atom::num(2) * &b__ * x_).exp();
            let factor1 = &i - &c__ - &d__;
            let factor2 = &i + &c__ + &d__;
            let denominator1 = &i - &c__ + &d__ - &factor1 * &exponential;
            let denominator2 = &i + &c__ - &d__ - &factor2 * &exponential;
            rubi_simp(&(x_ * (&c__ + &d__ * angle.coth()).atan()), x_)
                    - rubi_star(&i * &b__ * &factor1, rubi_rhs_int(&(x_ * &exponential / denominator1), x_))
                    + rubi_star(&i * &b__ * &factor2, rubi_rhs_int(&(x_ * exponential / denominator2), x_))
        },
    ));
}

fn push_rules_rule_5717(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 5717,
        source: "Int[ArcCot[c_.+d_.*Coth[a_.+b_.*x_]],x_Symbol] :=
          x*ArcCot[c+d*Coth[a+b*x]] +
          I*b*(I-c-d) \\[Star] Int[x*E^(2*a+2*b*x)/(I-c+d-(I-c-d)*E^(2*a+2*b*x)),x] -
          I*b*(I+c+d) \\[Star] Int[x*E^(2*a+2*b*x)/(I+c-d-(I+c+d)*E^(2*a+2*b*x)),x] /;
        FreeQ[{a,b,c,d},x] && NeQ[(c-d)^2,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [c__, d__, a__, b__, x_],
        optional: [c__, d__, a__, b__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && neq!((&c__ - &d__).pow(2), -1)
        },
        rhs: {
            let i = Atom::i();
            let angle = &a__ + &b__ * x_;
            let exponential = (Atom::num(2) * &a__ + Atom::num(2) * &b__ * x_).exp();
            let factor1 = &i - &c__ - &d__;
            let factor2 = &i + &c__ + &d__;
            let denominator1 = &i - &c__ + &d__ - &factor1 * &exponential;
            let denominator2 = &i + &c__ - &d__ - &factor2 * &exponential;
            rubi_simp(&(x_ * (&c__ + &d__ * angle.coth()).acot()), x_)
                    + rubi_star(&i * &b__ * &factor1, rubi_rhs_int(&(x_ * &exponential / denominator1), x_))
                    - rubi_star(&i * &b__ * &factor2, rubi_rhs_int(&(x_ * exponential / denominator2), x_))
        },
    ));
}

fn push_rules_rule_5718(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, x_);
    rules.push(rubi_rule!(
        order: 5718,
        source: "Int[(e_.+f_.*x_)^m_.*ArcTan[c_.+d_.*Tanh[a_.+b_.*x_]],x_Symbol] :=
          (e+f*x)^(m+1)*ArcTan[c+d*Tanh[a+b*x]]/(f*(m+1)) -
          b/(f*(m+1)) \\[Star] Int[(e+f*x)^(m+1)/(c-d+c*E^(2*a+2*b*x)),x] /;
        FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && EqQ[(c-d)^2,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_15(symbols),
        with: [e__, f__, m_, c__, d__, a__, b__, x_],
        optional: [e__, f__, m_, c__, d__, a__, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && igtq!(m_, 0)
                && eqq!((&c__ - &d__).pow(2), -1)
        },
        rhs: {
            let angle = &a__ + &b__ * x_;
            let base = &e__ + &f__ * x_;
            let m_plus_one = &m_ + 1;
            let powered_base = base.pow(&m_plus_one);
            let denominator_scale = &f__ * &m_plus_one;
            let exponential = (Atom::num(2) * &a__ + Atom::num(2) * &b__ * x_).exp();
            let denominator = &c__ - &d__ + &c__ * exponential;
            rubi_simp(&(&powered_base * (&c__ + &d__ * angle.tanh()).atan() / &denominator_scale), x_)
                    - rubi_star(&b__ / &denominator_scale, rubi_rhs_int(&(&powered_base / denominator), x_))
        },
    ));
}

fn push_rules_rule_5719(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, x_);
    rules.push(rubi_rule!(
        order: 5719,
        source: "Int[(e_.+f_.*x_)^m_.*ArcCot[c_.+d_.*Tanh[a_.+b_.*x_]],x_Symbol] :=
          (e+f*x)^(m+1)*ArcCot[c+d*Tanh[a+b*x]]/(f*(m+1)) +
          b/(f*(m+1)) \\[Star] Int[(e+f*x)^(m+1)/(c-d+c*E^(2*a+2*b*x)),x] /;
        FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && EqQ[(c-d)^2,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_14(symbols),
        with: [e__, f__, m_, c__, d__, a__, b__, x_],
        optional: [e__, f__, m_, c__, d__, a__, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && igtq!(m_, 0)
                && eqq!((&c__ - &d__).pow(2), -1)
        },
        rhs: {
            let angle = &a__ + &b__ * x_;
            let base = &e__ + &f__ * x_;
            let m_plus_one = &m_ + 1;
            let powered_base = base.pow(&m_plus_one);
            let denominator_scale = &f__ * &m_plus_one;
            let exponential = (Atom::num(2) * &a__ + Atom::num(2) * &b__ * x_).exp();
            let denominator = &c__ - &d__ + &c__ * exponential;
            rubi_simp(&(&powered_base * (&c__ + &d__ * angle.tanh()).acot() / &denominator_scale), x_)
                    + rubi_star(&b__ / &denominator_scale, rubi_rhs_int(&(&powered_base / denominator), x_))
        },
    ));
}

fn push_rules_rule_5720(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, x_);
    rules.push(rubi_rule!(
        order: 5720,
        source: "Int[(e_.+f_.*x_)^m_.*ArcTan[c_.+d_.*Coth[a_.+b_.*x_]],x_Symbol] :=
          (e+f*x)^(m+1)*ArcTan[c+d*Coth[a+b*x]]/(f*(m+1)) -
          b/(f*(m+1)) \\[Star] Int[(e+f*x)^(m+1)/(c-d-c*E^(2*a+2*b*x)),x] /;
        FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && EqQ[(c-d)^2,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_11(symbols),
        with: [e__, f__, m_, c__, d__, a__, b__, x_],
        optional: [e__, f__, m_, c__, d__, a__, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && igtq!(m_, 0)
                && eqq!((&c__ - &d__).pow(2), -1)
        },
        rhs: {
            let angle = &a__ + &b__ * x_;
            let base = &e__ + &f__ * x_;
            let m_plus_one = &m_ + 1;
            let powered_base = base.pow(&m_plus_one);
            let denominator_scale = &f__ * &m_plus_one;
            let exponential = (Atom::num(2) * &a__ + Atom::num(2) * &b__ * x_).exp();
            let denominator = &c__ - &d__ - &c__ * exponential;
            rubi_simp(&(&powered_base * (&c__ + &d__ * angle.coth()).atan() / &denominator_scale), x_)
                    - rubi_star(&b__ / &denominator_scale, rubi_rhs_int(&(&powered_base / denominator), x_))
        },
    ));
}

fn push_rules_rule_5721(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, x_);
    rules.push(rubi_rule!(
        order: 5721,
        source: "Int[(e_.+f_.*x_)^m_.*ArcCot[c_.+d_.*Coth[a_.+b_.*x_]],x_Symbol] :=
          (e+f*x)^(m+1)*ArcCot[c+d*Coth[a+b*x]]/(f*(m+1)) +
          b/(f*(m+1)) \\[Star] Int[(e+f*x)^(m+1)/(c-d-c*E^(2*a+2*b*x)),x] /;
        FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && EqQ[(c-d)^2,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_10(symbols),
        with: [e__, f__, m_, c__, d__, a__, b__, x_],
        optional: [e__, f__, m_, c__, d__, a__, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && igtq!(m_, 0)
                && eqq!((&c__ - &d__).pow(2), -1)
        },
        rhs: {
            let angle = &a__ + &b__ * x_;
            let base = &e__ + &f__ * x_;
            let m_plus_one = &m_ + 1;
            let powered_base = base.pow(&m_plus_one);
            let denominator_scale = &f__ * &m_plus_one;
            let exponential = (Atom::num(2) * &a__ + Atom::num(2) * &b__ * x_).exp();
            let denominator = &c__ - &d__ - &c__ * exponential;
            rubi_simp(&(&powered_base * (&c__ + &d__ * angle.coth()).acot() / &denominator_scale), x_)
                    + rubi_star(&b__ / &denominator_scale, rubi_rhs_int(&(&powered_base / denominator), x_))
        },
    ));
}

fn push_rules_rule_5722(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, x_);
    rules.push(rubi_rule!(
        order: 5722,
        source: "Int[(e_.+f_.*x_)^m_.*ArcTan[c_.+d_.*Tanh[a_.+b_.*x_]],x_Symbol] :=
          (e+f*x)^(m+1)*ArcTan[c+d*Tanh[a+b*x]]/(f*(m+1)) +
          I*b*(I-c-d)/(f*(m+1)) \\[Star] Int[(e+f*x)^(m+1)*E^(2*a+2*b*x)/(I-c+d+(I-c-d)*E^(2*a+2*b*x)),x] -
          I*b*(I+c+d)/(f*(m+1)) \\[Star] Int[(e+f*x)^(m+1)*E^(2*a+2*b*x)/(I+c-d+(I+c+d)*E^(2*a+2*b*x)),x] /;
        FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && NeQ[(c-d)^2,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_15(symbols),
        with: [e__, f__, m_, c__, d__, a__, b__, x_],
        optional: [e__, f__, m_, c__, d__, a__, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && igtq!(m_, 0)
                && neq!((&c__ - &d__).pow(2), -1)
        },
        rhs: {
            let i = Atom::i();
            let angle = &a__ + &b__ * x_;
            let base = &e__ + &f__ * x_;
            let m_plus_one = &m_ + 1;
            let powered_base = base.pow(&m_plus_one);
            let denominator_scale = &f__ * &m_plus_one;
            let exponential = (Atom::num(2) * &a__ + Atom::num(2) * &b__ * x_).exp();
            let factor1 = &i - &c__ - &d__;
            let factor2 = &i + &c__ + &d__;
            let denominator1 = &i - &c__ + &d__ + &factor1 * &exponential;
            let denominator2 = &i + &c__ - &d__ + &factor2 * &exponential;
            rubi_simp(&(&powered_base * (&c__ + &d__ * angle.tanh()).atan() / &denominator_scale), x_)
                    + rubi_star(&i * &b__ * &factor1 / &denominator_scale, rubi_rhs_int(&(&powered_base * &exponential / denominator1), x_))
                    - rubi_star(&i * &b__ * &factor2 / &denominator_scale, rubi_rhs_int(&(&powered_base * exponential / denominator2), x_))
        },
    ));
}

fn push_rules_rule_5723(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, x_);
    rules.push(rubi_rule!(
        order: 5723,
        source: "Int[(e_.+f_.*x_)^m_.*ArcCot[c_.+d_.*Tanh[a_.+b_.*x_]],x_Symbol] :=
          (e+f*x)^(m+1)*ArcCot[c+d*Tanh[a+b*x]]/(f*(m+1)) -
          I*b*(I-c-d)/(f*(m+1)) \\[Star] Int[(e+f*x)^(m+1)*E^(2*a+2*b*x)/(I-c+d+(I-c-d)*E^(2*a+2*b*x)),x] +
          I*b*(I+c+d)/(f*(m+1)) \\[Star] Int[(e+f*x)^(m+1)*E^(2*a+2*b*x)/(I+c-d+(I+c+d)*E^(2*a+2*b*x)),x] /;
        FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && NeQ[(c-d)^2,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_14(symbols),
        with: [e__, f__, m_, c__, d__, a__, b__, x_],
        optional: [e__, f__, m_, c__, d__, a__, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && igtq!(m_, 0)
                && neq!((&c__ - &d__).pow(2), -1)
        },
        rhs: {
            let i = Atom::i();
            let angle = &a__ + &b__ * x_;
            let base = &e__ + &f__ * x_;
            let m_plus_one = &m_ + 1;
            let powered_base = base.pow(&m_plus_one);
            let denominator_scale = &f__ * &m_plus_one;
            let exponential = (Atom::num(2) * &a__ + Atom::num(2) * &b__ * x_).exp();
            let factor1 = &i - &c__ - &d__;
            let factor2 = &i + &c__ + &d__;
            let denominator1 = &i - &c__ + &d__ + &factor1 * &exponential;
            let denominator2 = &i + &c__ - &d__ + &factor2 * &exponential;
            rubi_simp(&(&powered_base * (&c__ + &d__ * angle.tanh()).acot() / &denominator_scale), x_)
                    - rubi_star(&i * &b__ * &factor1 / &denominator_scale, rubi_rhs_int(&(&powered_base * &exponential / denominator1), x_))
                    + rubi_star(&i * &b__ * &factor2 / &denominator_scale, rubi_rhs_int(&(&powered_base * exponential / denominator2), x_))
        },
    ));
}

fn push_rules_rule_5724(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, x_);
    rules.push(rubi_rule!(
        order: 5724,
        source: "Int[(e_.+f_.*x_)^m_.*ArcTan[c_.+d_.*Coth[a_.+b_.*x_]],x_Symbol] :=
          (e+f*x)^(m+1)*ArcTan[c+d*Coth[a+b*x]]/(f*(m+1)) -
          I*b*(I-c-d)/(f*(m+1)) \\[Star] Int[(e+f*x)^(m+1)*E^(2*a+2*b*x)/(I-c+d-(I-c-d)*E^(2*a+2*b*x)),x] +
          I*b*(I+c+d)/(f*(m+1)) \\[Star] Int[(e+f*x)^(m+1)*E^(2*a+2*b*x)/(I+c-d-(I+c+d)*E^(2*a+2*b*x)),x] /;
        FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && NeQ[(c-d)^2,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_11(symbols),
        with: [e__, f__, m_, c__, d__, a__, b__, x_],
        optional: [e__, f__, m_, c__, d__, a__, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && igtq!(m_, 0)
                && neq!((&c__ - &d__).pow(2), -1)
        },
        rhs: {
            let i = Atom::i();
            let angle = &a__ + &b__ * x_;
            let base = &e__ + &f__ * x_;
            let m_plus_one = &m_ + 1;
            let powered_base = base.pow(&m_plus_one);
            let denominator_scale = &f__ * &m_plus_one;
            let exponential = (Atom::num(2) * &a__ + Atom::num(2) * &b__ * x_).exp();
            let factor1 = &i - &c__ - &d__;
            let factor2 = &i + &c__ + &d__;
            let denominator1 = &i - &c__ + &d__ - &factor1 * &exponential;
            let denominator2 = &i + &c__ - &d__ - &factor2 * &exponential;
            rubi_simp(&(&powered_base * (&c__ + &d__ * angle.coth()).atan() / &denominator_scale), x_)
                    - rubi_star(&i * &b__ * &factor1 / &denominator_scale, rubi_rhs_int(&(&powered_base * &exponential / denominator1), x_))
                    + rubi_star(&i * &b__ * &factor2 / &denominator_scale, rubi_rhs_int(&(&powered_base * exponential / denominator2), x_))
        },
    ));
}

fn push_rules_rule_5725(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, x_);
    rules.push(rubi_rule!(
        order: 5725,
        source: "Int[(e_.+f_.*x_)^m_.*ArcCot[c_.+d_.*Coth[a_.+b_.*x_]],x_Symbol] :=
          (e+f*x)^(m+1)*ArcCot[c+d*Coth[a+b*x]]/(f*(m+1)) +
          I*b*(I-c-d)/(f*(m+1)) \\[Star] Int[(e+f*x)^(m+1)*E^(2*a+2*b*x)/(I-c+d-(I-c-d)*E^(2*a+2*b*x)),x] -
          I*b*(I+c+d)/(f*(m+1)) \\[Star] Int[(e+f*x)^(m+1)*E^(2*a+2*b*x)/(I+c-d-(I+c+d)*E^(2*a+2*b*x)),x] /;
        FreeQ[{a,b,c,d,e,f},x] && IGtQ[m,0] && NeQ[(c-d)^2,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_10(symbols),
        with: [e__, f__, m_, c__, d__, a__, b__, x_],
        optional: [e__, f__, m_, c__, d__, a__, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && igtq!(m_, 0)
                && neq!((&c__ - &d__).pow(2), -1)
        },
        rhs: {
            let i = Atom::i();
            let angle = &a__ + &b__ * x_;
            let base = &e__ + &f__ * x_;
            let m_plus_one = &m_ + 1;
            let powered_base = base.pow(&m_plus_one);
            let denominator_scale = &f__ * &m_plus_one;
            let exponential = (Atom::num(2) * &a__ + Atom::num(2) * &b__ * x_).exp();
            let factor1 = &i - &c__ - &d__;
            let factor2 = &i + &c__ + &d__;
            let denominator1 = &i - &c__ + &d__ - &factor1 * &exponential;
            let denominator2 = &i + &c__ - &d__ - &factor2 * &exponential;
            rubi_simp(&(&powered_base * (&c__ + &d__ * angle.coth()).acot() / &denominator_scale), x_)
                    + rubi_star(&i * &b__ * &factor1 / &denominator_scale, rubi_rhs_int(&(&powered_base * &exponential / denominator1), x_))
                    - rubi_star(&i * &b__ * &factor2 / &denominator_scale, rubi_rhs_int(&(&powered_base * exponential / denominator2), x_))
        },
    ));
}

fn push_rules_rule_5726(rules: &mut Vec<RubiRule>) {
    rubi_symb!(u_);
    rules.push(rubi_rule!(
        order: 5726,
        source: "Int[ArcTan[u_],x_Symbol] :=
          x*ArcTan[u] -
          Int[SimplifyIntegrand[x*D[u,x]/(1+u^2),x],x] /;
        InverseFunctionFreeQ[u,x]",
        desc: "Integration by parts",
        refs: [],
        pattern: Atom::var(u_).atan(),
        with: [u_, x_],
        when: { rubi_inverse_function_free_q(&u_, x_) },
        rhs: {
            let recursive = rubi_simplify_integrand(
                &(x_ * u_.derivative(x_) / (Atom::num(1) + u_.pow(2))),
                x_,
            );
            rubi_simp(&(x_ * u_.atan()), x_) - rubi_rhs_int(&recursive, x_)
        },
    ));
}

fn push_rules_rule_5727(rules: &mut Vec<RubiRule>) {
    rubi_symb!(u_);
    rules.push(rubi_rule!(
        order: 5727,
        source: "Int[ArcCot[u_],x_Symbol] :=
          x*ArcCot[u] +
          Int[SimplifyIntegrand[x*D[u,x]/(1+u^2),x],x] /;
        InverseFunctionFreeQ[u,x]",
        desc: "Integration by parts",
        refs: [],
        pattern: Atom::var(u_).acot(),
        with: [u_, x_],
        when: { rubi_inverse_function_free_q(&u_, x_) },
        rhs: {
            let recursive = rubi_simplify_integrand(
                &(x_ * u_.derivative(x_) / (Atom::num(1) + u_.pow(2))),
                x_,
            );
            rubi_simp(&(x_ * u_.acot()), x_) + rubi_rhs_int(&recursive, x_)
        },
    ));
}

fn push_rules_rule_5728(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, u_, x_);
    rules.push(rubi_rule!(
        order: 5728,
        source: "Int[(c_.+d_.*x_)^m_.*(a_.+b_.*ArcTan[u_]),x_Symbol] :=
          (c+d*x)^(m+1)*(a+b*ArcTan[u])/(d*(m+1)) -
          b/(d*(m+1)) \\[Star] Int[SimplifyIntegrand[(c+d*x)^(m+1)*D[u,x]/(1+u^2),x],x] /;
        FreeQ[{a,b,c,d,m},x] && NeQ[m,-1] && InverseFunctionFreeQ[u,x] && Not[FunctionOfQ[(c+d*x)^(m+1),u,x]] && FalseQ[PowerVariableExpn[u,m+1,x]]",
        desc: "Integration by parts",
        refs: [],
        pattern: (c__ + d__ * x_).pow(m_) * (a__ + b__ * Atom::var(u_).atan()),
        with: [c__, d__, m_, a__, b__, u_, x_],
        optional: [c__, d__, m_, a__, b__],
        when: {
            freeq!([a__, b__, c__, d__, m_], x_)
                && neq!(m_, -1)
                && rubi_inverse_function_free_q(&u_, x_)
                && !rubi_function_of_q(&(&c__ + &d__ * x_).pow(&m_ + 1), &u_, x_)
                && !rubi_power_variable_expn_q(&u_, &(&m_ + 1), x_)
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let denominator_scale = &d__ * (&m_ + 1);
            let argument = &a__ + &b__ * u_.atan();
            let recursive = rubi_simplify_integrand(
                &(linear.pow(&m_ + 1) * u_.derivative(x_) / (Atom::num(1) + u_.pow(2))),
                x_,
            );
            rubi_simp(&(linear.pow(&m_ + 1) * argument / &denominator_scale), x_)
                    - rubi_star(&b__ / &denominator_scale, rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_5729(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, u_, x_);
    rules.push(rubi_rule!(
        order: 5729,
        source: "Int[(c_.+d_.*x_)^m_.*(a_.+b_.*ArcCot[u_]),x_Symbol] :=
          (c+d*x)^(m+1)*(a+b*ArcCot[u])/(d*(m+1)) +
          b/(d*(m+1)) \\[Star] Int[SimplifyIntegrand[(c+d*x)^(m+1)*D[u,x]/(1+u^2),x],x] /;
        FreeQ[{a,b,c,d,m},x] && NeQ[m,-1] && InverseFunctionFreeQ[u,x] && Not[FunctionOfQ[(c+d*x)^(m+1),u,x]] && FalseQ[PowerVariableExpn[u,m+1,x]]",
        desc: "Integration by parts",
        refs: [],
        pattern: (c__ + d__ * x_).pow(m_) * (a__ + b__ * Atom::var(u_).acot()),
        with: [c__, d__, m_, a__, b__, u_, x_],
        optional: [c__, d__, m_, a__, b__],
        when: {
            freeq!([a__, b__, c__, d__, m_], x_)
                && neq!(m_, -1)
                && rubi_inverse_function_free_q(&u_, x_)
                && !rubi_function_of_q(&(&c__ + &d__ * x_).pow(&m_ + 1), &u_, x_)
                && !rubi_power_variable_expn_q(&u_, &(&m_ + 1), x_)
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let denominator_scale = &d__ * (&m_ + 1);
            let argument = &a__ + &b__ * u_.acot();
            let recursive = rubi_simplify_integrand(
                &(linear.pow(&m_ + 1) * u_.derivative(x_) / (Atom::num(1) + u_.pow(2))),
                x_,
            );
            rubi_simp(&(linear.pow(&m_ + 1) * argument / &denominator_scale), x_)
                    + rubi_star(&b__ / &denominator_scale, rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_5730(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, u_, v__);
    rules.push(rubi_rule!(
        order: 5730,
        source: "Int[v_*(a_.+b_.*ArcTan[u_]),x_Symbol] :=
          With[{w=IntHide[v,x]},
          (a+b*ArcTan[u]) \\[Star] w - b \\[Star] Int[SimplifyIntegrand[w*D[u,x]/(1+u^2),x],x] /;
         InverseFunctionFreeQ[w,x]] /;
        FreeQ[{a,b},x] && InverseFunctionFreeQ[u,x] && Not[MatchQ[v, (c_.+d_.*x)^m_. /; FreeQ[{c,d,m},x]]] && FalseQ[FunctionOfLinear[v*(a+b*ArcTan[u]),x]]",
        desc: "Integration by parts",
        refs: [],
        pattern: v__ * (a__ + b__ * Atom::var(u_).atan()),
        with: [v__, a__, b__, u_, x_],
        optional: [a__, b__],
        when: {
            freeq!([a__, b__], x_)
                && rubi_inverse_function_free_q(&u_, x_)
                && !rubi_linear_power_q(&v__, x_)
                && !rubi_function_of_linear_q(&(&v__ * (&a__ + &b__ * u_.atan())), x_)
                && rubi_int_hide_inverse_function_free_q(&v__, x_)
        },
        rhs: {
            let hidden = rubi_int_hide(&v__, x_).rubi_rhs();
            let argument = &a__ + &b__ * u_.atan();
            let recursive = rubi_simplify_integrand(
                &(&hidden * u_.derivative(x_) / (Atom::num(1) + u_.pow(2))),
                x_,
            );
            rubi_star(argument, hidden)
                    - rubi_star(b__, rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_5731(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, u_, v__);
    rules.push(rubi_rule!(
        order: 5731,
        source: "Int[v_*(a_.+b_.*ArcCot[u_]),x_Symbol] :=
          With[{w=IntHide[v,x]},
          (a+b*ArcCot[u])w + b \\[Star] Int[SimplifyIntegrand[w*D[u,x]/(1+u^2),x],x] /;
         InverseFunctionFreeQ[w,x]] /;
        FreeQ[{a,b},x] && InverseFunctionFreeQ[u,x] && Not[MatchQ[v, (c_.+d_.*x)^m_. /; FreeQ[{c,d,m},x]]] && FalseQ[FunctionOfLinear[v*(a+b*ArcCot[u]),x]]",
        desc: "Integration by parts",
        refs: [],
        pattern: v__ * (a__ + b__ * Atom::var(u_).acot()),
        with: [v__, a__, b__, u_, x_],
        optional: [a__, b__],
        when: {
            freeq!([a__, b__], x_)
                && rubi_inverse_function_free_q(&u_, x_)
                && !rubi_linear_power_q(&v__, x_)
                && !rubi_function_of_linear_q(&(&v__ * (&a__ + &b__ * u_.acot())), x_)
                && rubi_int_hide_inverse_function_free_q(&v__, x_)
        },
        rhs: {
            let hidden = rubi_int_hide(&v__, x_).rubi_rhs();
            let argument = &a__ + &b__ * u_.acot();
            let recursive = rubi_simplify_integrand(
                &(&hidden * u_.derivative(x_) / (Atom::num(1) + u_.pow(2))),
                x_,
            );
            rubi_simp(&(argument * hidden), x_) + rubi_star(b__, rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_5732(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, v_, w_, z_);
    rules.push(rubi_rule!(
        order: 5732,
        source: "Int[ArcTan[v_]*Log[w_]/(a_.+b_.*x_),x_Symbol] :=
          I/2 \\[Star] Int[Log[1-I*v]*Log[w]/(a+b*x),x] - I/2 \\[Star] Int[Log[1+I*v]*Log[w]/(a+b*x),x] /;
        FreeQ[{a,b},x] && LinearQ[v,x] && LinearQ[w,x] && EqQ[Simplify[D[v/(a+b*x),x]],0] && EqQ[Simplify[D[w/(a+b*x),x]],0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: Atom::var(v_).atan() * Atom::var(w_).log() / (a__ + b__ * z_),
        with: [v_, w_, a__, b__, z_, x_],
        optional: [a__, b__],
        x_dep: [v_, w_],
        x_free: [a__, b__],
        when: {
            let linear = &a__ + &b__ * x_;
            z_ == x_
                && freeq!([a__, b__], x_)
                && rubi_linear_q(&v_, x_)
                && rubi_linear_q(&w_, x_)
                && eqq!(rubi_simplify(&((&v_ / &linear).derivative(x_))), 0)
                && eqq!(rubi_simplify(&((&w_ / linear).derivative(x_))), 0)
        },
        rhs: {
            let i = Atom::i();
            let linear = &a__ + &b__ * x_;
            let log_w = w_.log();
            let first = (Atom::num(1) - &i * &v_).log() * &log_w / &linear;
            let second = (Atom::num(1) + &i * &v_).log() * log_w / linear;
            rubi_star(&i / 2, rubi_rhs_int(&first, x_))
                    - rubi_star(&i / 2, rubi_rhs_int(&second, x_))
        },
    ));
}

fn push_rules_rule_5733(rules: &mut Vec<RubiRule>) {
    rubi_symb!(v_, w_);
    rules.push(rubi_rule!(
        order: 5733,
        source: "Int[ArcTan[v_]*Log[w_],x_Symbol] :=
          x*ArcTan[v]*Log[w] -
          Int[SimplifyIntegrand[x*Log[w]*D[v,x]/(1+v^2),x],x] -
          Int[SimplifyIntegrand[x*ArcTan[v]*D[w,x]/w,x],x] /;
        InverseFunctionFreeQ[v,x] && InverseFunctionFreeQ[w,x]",
        desc: "Integration by parts",
        refs: [],
        pattern: Atom::var(v_).atan() * Atom::var(w_).log(),
        with: [v_, w_, x_],
        when: { rubi_inverse_function_free_q(&v_, x_) && rubi_inverse_function_free_q(&w_, x_) },
        rhs: {
            let log_w = w_.log();
            let recursive_v = rubi_simplify_integrand(
                &(x_ * &log_w * v_.derivative(x_) / (Atom::num(1) + v_.pow(2))),
                x_,
            );
            let recursive_w = rubi_simplify_integrand(
                &(x_ * v_.atan() * w_.derivative(x_) / &w_),
                x_,
            );
            rubi_simp(&(x_ * v_.atan() * log_w), x_)
                    - rubi_rhs_int(&recursive_v, x_)
                    - rubi_rhs_int(&recursive_w, x_)
        },
    ));
}

fn push_rules_rule_5734(rules: &mut Vec<RubiRule>) {
    rubi_symb!(v_, w_);
    rules.push(rubi_rule!(
        order: 5734,
        source: "Int[ArcCot[v_]*Log[w_],x_Symbol] :=
          x*ArcCot[v]*Log[w] +
          Int[SimplifyIntegrand[x*Log[w]*D[v,x]/(1+v^2),x],x] -
          Int[SimplifyIntegrand[x*ArcCot[v]*D[w,x]/w,x],x] /;
        InverseFunctionFreeQ[v,x] && InverseFunctionFreeQ[w,x]",
        desc: "Integration by parts",
        refs: [],
        pattern: Atom::var(v_).acot() * Atom::var(w_).log(),
        with: [v_, w_, x_],
        when: { rubi_inverse_function_free_q(&v_, x_) && rubi_inverse_function_free_q(&w_, x_) },
        rhs: {
            let log_w = w_.log();
            let recursive_v = rubi_simplify_integrand(
                &(x_ * &log_w * v_.derivative(x_) / (Atom::num(1) + v_.pow(2))),
                x_,
            );
            let recursive_w = rubi_simplify_integrand(
                &(x_ * v_.acot() * w_.derivative(x_) / &w_),
                x_,
            );
            rubi_simp(&(x_ * v_.acot() * log_w), x_)
                    + rubi_rhs_int(&recursive_v, x_)
                    - rubi_rhs_int(&recursive_w, x_)
        },
    ));
}

fn push_rules_rule_5735(rules: &mut Vec<RubiRule>) {
    rubi_symb!(u__, v_, w_);
    rules.push(rubi_rule!(
        order: 5735,
        source: "Int[u_*ArcTan[v_]*Log[w_],x_Symbol] :=
          With[{z=IntHide[u,x]},
          ArcTan[v]*Log[w] \\[Star] z -
          Int[SimplifyIntegrand[z*Log[w]*D[v,x]/(1+v^2),x],x] -
          Int[SimplifyIntegrand[z*ArcTan[v]*D[w,x]/w,x],x] /;
         InverseFunctionFreeQ[z,x]] /;
        InverseFunctionFreeQ[v,x] && InverseFunctionFreeQ[w,x]",
        desc: "Integration by parts",
        refs: [],
        pattern: Atom::var(u__) * Atom::var(v_).atan() * Atom::var(w_).log(),
        with: [u__, v_, w_, x_],
        when: {
            rubi_inverse_function_free_q(&v_, x_)
                && rubi_inverse_function_free_q(&w_, x_)
                && rubi_int_hide_inverse_function_free_q(&u__, x_)
        },
        rhs: {
            let hidden = rubi_int_hide(&u__, x_).rubi_rhs();
            let log_w = w_.log();
            let argument = v_.atan() * &log_w;
            let recursive_v = rubi_simplify_integrand(
                &(&hidden * &log_w * v_.derivative(x_) / (Atom::num(1) + v_.pow(2))),
                x_,
            );
            let recursive_w = rubi_simplify_integrand(
                &(&hidden * v_.atan() * w_.derivative(x_) / &w_),
                x_,
            );
            rubi_star(argument, hidden)
                    - rubi_rhs_int(&recursive_v, x_)
                    - rubi_rhs_int(&recursive_w, x_)
        },
    ));
}

fn push_rules_rule_5736(rules: &mut Vec<RubiRule>) {
    rubi_symb!(u__, v_, w_);
    rules.push(rubi_rule!(
        order: 5736,
        source: "Int[u_*ArcCot[v_]*Log[w_],x_Symbol] :=
          With[{z=IntHide[u,x]},
          ArcCot[v]*Log[w] \\[Star] z +
          Int[SimplifyIntegrand[z*Log[w]*D[v,x]/(1+v^2),x],x] -
          Int[SimplifyIntegrand[z*ArcCot[v]*D[w,x]/w,x],x] /;
         InverseFunctionFreeQ[z,x]] /;
        InverseFunctionFreeQ[v,x] && InverseFunctionFreeQ[w,x]",
        desc: "Integration by parts",
        refs: [],
        pattern: Atom::var(u__) * Atom::var(v_).acot() * Atom::var(w_).log(),
        with: [u__, v_, w_, x_],
        when: {
            rubi_inverse_function_free_q(&v_, x_)
                && rubi_inverse_function_free_q(&w_, x_)
                && rubi_int_hide_inverse_function_free_q(&u__, x_)
        },
        rhs: {
            let hidden = rubi_int_hide(&u__, x_).rubi_rhs();
            let log_w = w_.log();
            let argument = v_.acot() * &log_w;
            let recursive_v = rubi_simplify_integrand(
                &(&hidden * &log_w * v_.derivative(x_) / (Atom::num(1) + v_.pow(2))),
                x_,
            );
            let recursive_w = rubi_simplify_integrand(
                &(&hidden * v_.acot() * w_.derivative(x_) / &w_),
                x_,
            );
            rubi_star(argument, hidden)
                    + rubi_rhs_int(&recursive_v, x_)
                    - rubi_rhs_int(&recursive_w, x_)
        },
    ));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn downvalues_5658_through_5692_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .filter(|order| (5658..=5692).contains(order))
            .collect::<Vec<_>>();
        assert_eq!(orders, (5658..=5692).collect::<Vec<_>>());
    }

    #[test]
    fn downvalues_5693_through_5736_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .filter(|order| (5693..=5736).contains(order))
            .collect::<Vec<_>>();
        assert_eq!(orders, (5693..=5736).collect::<Vec<_>>());
    }
}

// Generated shared pattern builders.

#[inline(never)]
fn rubi_shared_pattern_0(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let x_ = symbols.x_;
    (c__ + d__ * (a__ + b__ * x_).cot()).acot()
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let x_ = symbols.x_;
    (c__ + d__ * (a__ + b__ * x_).cot()).atan()
}

#[inline(never)]
fn rubi_shared_pattern_2(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let x_ = symbols.x_;
    (c__ + d__ * (a__ + b__ * x_).coth()).acot()
}

#[inline(never)]
fn rubi_shared_pattern_3(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let x_ = symbols.x_;
    (c__ + d__ * (a__ + b__ * x_).coth()).atan()
}

#[inline(never)]
fn rubi_shared_pattern_4(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let x_ = symbols.x_;
    (c__ + d__ * (a__ + b__ * x_).tan()).acot()
}

#[inline(never)]
fn rubi_shared_pattern_5(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let x_ = symbols.x_;
    (c__ + d__ * (a__ + b__ * x_).tan()).atan()
}

#[inline(never)]
fn rubi_shared_pattern_6(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let x_ = symbols.x_;
    (c__ + d__ * (a__ + b__ * x_).tanh()).acot()
}

#[inline(never)]
fn rubi_shared_pattern_7(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let x_ = symbols.x_;
    (c__ + d__ * (a__ + b__ * x_).tanh()).atan()
}

#[inline(never)]
fn rubi_shared_pattern_8(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let x_ = symbols.x_;
    (e__ + f__ * x_).pow(m_) * (c__ + d__ * (a__ + b__ * x_).cot()).acot()
}

#[inline(never)]
fn rubi_shared_pattern_9(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let x_ = symbols.x_;
    (e__ + f__ * x_).pow(m_) * (c__ + d__ * (a__ + b__ * x_).cot()).atan()
}

#[inline(never)]
fn rubi_shared_pattern_10(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let x_ = symbols.x_;
    (e__ + f__ * x_).pow(m_) * (c__ + d__ * (a__ + b__ * x_).coth()).acot()
}

#[inline(never)]
fn rubi_shared_pattern_11(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let x_ = symbols.x_;
    (e__ + f__ * x_).pow(m_) * (c__ + d__ * (a__ + b__ * x_).coth()).atan()
}

#[inline(never)]
fn rubi_shared_pattern_12(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let x_ = symbols.x_;
    (e__ + f__ * x_).pow(m_) * (c__ + d__ * (a__ + b__ * x_).tan()).acot()
}

#[inline(never)]
fn rubi_shared_pattern_13(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let x_ = symbols.x_;
    (e__ + f__ * x_).pow(m_) * (c__ + d__ * (a__ + b__ * x_).tan()).atan()
}

#[inline(never)]
fn rubi_shared_pattern_14(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let x_ = symbols.x_;
    (e__ + f__ * x_).pow(m_) * (c__ + d__ * (a__ + b__ * x_).tanh()).acot()
}

#[inline(never)]
fn rubi_shared_pattern_15(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let x_ = symbols.x_;
    (e__ + f__ * x_).pow(m_) * (c__ + d__ * (a__ + b__ * x_).tanh()).atan()
}

#[inline(never)]
fn rubi_shared_pattern_16(symbols: &RubiSymbols) -> Atom {
    let n_ = symbols.n_;
    let u__ = symbols.u__;
    let v_ = symbols.v_;
    u__ * v_.pow(n_)
}
