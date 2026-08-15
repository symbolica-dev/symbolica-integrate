use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_6410(rules);
    push_rules_rule_6411(rules);
    push_rules_rule_6412(rules);
    push_rules_rule_6413(rules);
    push_rules_rule_6414(rules);
    push_rules_rule_6415(rules);
    push_rules_rule_6416(rules);
    push_rules_rule_6417(rules);
    push_rules_rule_6418(rules);
    push_rules_rule_6419(rules);
    push_rules_rule_6420(rules);
    push_rules_rule_6421(rules);
    push_rules_rule_6422(rules);
    push_rules_rule_6423(rules);
    push_rules_rule_6424(rules);
    push_rules_rule_6425(rules);
    push_rules_rule_6426(rules);
    push_rules_rule_6427(rules);
    push_rules_rule_6428(rules);
    push_rules_rule_6429(rules);
    push_rules_rule_6430(rules);
    push_rules_rule_6431(rules);
    push_rules_rule_6432(rules);
    push_rules_rule_6433(rules);
    push_rules_rule_6434(rules);
    push_rules_rule_6435(rules);
}

fn push_rules_rule_6410(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 6410,
        source: "Int[(a_.+b_.*ArcCosh[c_+d_.*x_])^n_.,x_Symbol] :=
          1/d \\[Star] Subst[Int[(a+b*ArcCosh[x])^n,x],x,c+d*x] /;
        FreeQ[{a,b,c,d,n},x]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (a__ + b__ * (c__ + d__ * x_).acosh()).pow(n_),
        with: [a__, b__, c__, d__, n_, x_],
        optional: [a__, b__, d__, n_],
        when: { freeq!([a__, b__, c__, d__, n_], x_) },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().rubi_rhs();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let payload = (&a__ + &b__ * sub_atom.acosh()).pow(&n_);
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            let substituted = rubi_subst(&primitive, substitution_symbol, &c__ + &d__ * x_);
            rubi_star(Atom::num(1) / &d__, substituted)
        },
    ));
}

fn push_rules_rule_6411(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 6411,
        source: "Int[(e_.+f_.*x_)^m_.*(a_.+b_.*ArcCosh[c_+d_.*x_])^n_.,x_Symbol] :=
          1/d \\[Star] Subst[Int[((d*e-c*f)/d+f*x/d)^m*(a+b*ArcCosh[x])^n,x],x,c+d*x] /;
        FreeQ[{a,b,c,d,e,f,m,n},x]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (e__ + f__ * x_).pow(m_) * (a__ + b__ * (c__ + d__ * x_).acosh()).pow(n_),
        with: [e__, f__, m_, a__, b__, c__, d__, n_, x_],
        optional: [e__, f__, m_, a__, b__, d__, n_],
        when: { freeq!([a__, b__, c__, d__, e__, f__, m_, n_], x_) },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().rubi_rhs();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let transformed_linear = (&d__ * &e__ - &c__ * &f__) / &d__ + &f__ * &sub_atom / &d__;
            let payload = transformed_linear.pow(&m_) * (&a__ + &b__ * sub_atom.acosh()).pow(&n_);
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            let substituted = rubi_subst(&primitive, substitution_symbol, &c__ + &d__ * x_);
            rubi_star(Atom::num(1) / &d__, substituted)
        },
    ));
}

fn push_rules_rule_6412(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        capital_a__,
        capital_b__,
        capital_c__,
        a__,
        b__,
        c__,
        d__,
        n_,
        p_,
        x_
    );
    rules.push(rubi_rule!(
        order: 6412,
        source: "Int[(A_.+B_.*x_+C_.*x_^2)^p_.*(a_.+b_.*ArcCosh[c_+d_.*x_])^n_.,x_Symbol] :=
          1/d \\[Star] Subst[Int[(-C/d^2+C/d^2*x^2)^p*(a+b*ArcCosh[x])^n,x],x,c+d*x] /;
        FreeQ[{a,b,c,d,A,B,C,n,p},x] && EqQ[B*(1-c^2)+2*A*c*d,0] && EqQ[2*c*C-B*d,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (capital_a__ + capital_b__ * x_ + capital_c__ * x_.pow(2)).pow(p_)
            * (a__ + b__ * (c__ + d__ * x_).acosh()).pow(n_),
        with: [capital_a__, capital_b__, capital_c__, p_, a__, b__, c__, d__, n_, x_],
        optional: [capital_a__, capital_b__, capital_c__, a__, b__, d__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, capital_a__, capital_b__, capital_c__, n_, p_], x_)
                && eqq!(&capital_b__ * (Atom::num(1) - c__.pow(2)) + Atom::num(2) * &capital_a__ * &c__ * &d__, 0)
                && eqq!(Atom::num(2) * &c__ * &capital_c__ - &capital_b__ * &d__, 0)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().rubi_rhs();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let transformed_quadratic = -&capital_c__ / d__.pow(2) + &capital_c__ * sub_atom.pow(2) / d__.pow(2);
            let payload = transformed_quadratic.pow(&p_) * (&a__ + &b__ * sub_atom.acosh()).pow(&n_);
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            let substituted = rubi_subst(
                &primitive,
                substitution_symbol,
                &c__ + &d__ * x_,
            );
            rubi_star(Atom::num(1) / &d__, substituted)
        },
    ));
}

fn push_rules_rule_6413(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        capital_a__,
        capital_b__,
        capital_c__,
        a__,
        b__,
        c__,
        d__,
        e__,
        f__,
        m_,
        n_,
        p_,
        x_
    );
    rules.push(rubi_rule!(
        order: 6413,
        source: "Int[(e_.+f_.*x_)^m_.*(A_.+B_.*x_+C_.*x_^2)^p_.*(a_.+b_.*ArcCosh[c_+d_.*x_])^n_.,x_Symbol] :=
          1/d \\[Star] Subst[Int[((d*e-c*f)/d+f*x/d)^m*(-C/d^2+C/d^2*x^2)^p*(a+b*ArcCosh[x])^n,x],x,c+d*x] /;
        FreeQ[{a,b,c,d,e,f,A,B,C,m,n,p},x] && EqQ[B*(1-c^2)+2*A*c*d,0] && EqQ[2*c*C-B*d,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (e__ + f__ * x_).pow(m_)
            * (capital_a__ + capital_b__ * x_ + capital_c__ * x_.pow(2)).pow(p_)
            * (a__ + b__ * (c__ + d__ * x_).acosh()).pow(n_),
        with: [e__, f__, m_, capital_a__, capital_b__, capital_c__, p_, a__, b__, c__, d__, n_, x_],
        optional: [e__, f__, m_, capital_a__, capital_b__, capital_c__, a__, b__, d__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, capital_a__, capital_b__, capital_c__, m_, n_, p_], x_)
                && eqq!(&capital_b__ * (Atom::num(1) - c__.pow(2)) + Atom::num(2) * &capital_a__ * &c__ * &d__, 0)
                && eqq!(Atom::num(2) * &c__ * &capital_c__ - &capital_b__ * &d__, 0)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().rubi_rhs();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let transformed_linear = (&d__ * &e__ - &c__ * &f__) / &d__ + &f__ * &sub_atom / &d__;
            let transformed_quadratic = -&capital_c__ / d__.pow(2) + &capital_c__ * sub_atom.pow(2) / d__.pow(2);
            let payload = transformed_linear.pow(&m_)
                * transformed_quadratic.pow(&p_)
                * (&a__ + &b__ * sub_atom.acosh()).pow(&n_);
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            let substituted = rubi_subst(&primitive, substitution_symbol, &c__ + &d__ * x_);
            rubi_star(Atom::num(1) / &d__, substituted)
        },
    ));
}

fn push_rules_rule_6414(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, d__, x_);
    rules.push(rubi_rule!(
        order: 6414,
        source: "Int[Sqrt[a_.+b_.*ArcCosh[1+d_.*x_^2]],x_Symbol] :=
          2*Sqrt[a+b*ArcCosh[1+d*x^2]]*Sinh[(1/2)*ArcCosh[1+d*x^2]]^2/(d*x) -
          Sqrt[b]*Sqrt[Pi/2]*(Cosh[a/(2*b)]-Sinh[a/(2*b)])*Sinh[(1/2)*ArcCosh[1+d*x^2]]*
            Erfi[(1/Sqrt[2*b])*Sqrt[a+b*ArcCosh[1+d*x^2]]]/(d*x) +
          Sqrt[b]*Sqrt[Pi/2]*(Cosh[a/(2*b)]+Sinh[a/(2*b)])*Sinh[(1/2)*ArcCosh[1+d*x^2]]*
            Erf[(1/Sqrt[2*b])*Sqrt[a+b*ArcCosh[1+d*x^2]]]/(d*x) /;
        FreeQ[{a,b,d},x]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: (a__ + b__ * (Atom::num(1) + d__ * x_.pow(2)).acosh()).sqrt(),
        with: [a__, b__, d__, x_],
        optional: [a__, b__, d__],
        when: { freeq!([a__, b__, d__], x_) },
        rhs: {
            let acosh = (Atom::num(1) + &d__ * x_.pow(2)).acosh();
            let half = &acosh / Atom::num(2);
            let argument = &a__ + &b__ * acosh;
            let scaled_sqrt = &argument.sqrt() / (Atom::num(2) * &b__).sqrt();
            let ab_half = &a__ / (Atom::num(2) * &b__);
            let denom = &d__ * x_;
            rubi_simp(&(Atom::num(2) * &argument.sqrt() * &half.sinh().pow(2) / &denom), x_)
                    - rubi_simp(&(b__.sqrt()
                        * (Atom::var(Symbol::PI) / Atom::num(2)).sqrt()
                        * (&ab_half.cosh() - &ab_half.sinh())
                        * &half.sinh()
                        * rubi_erfi(&scaled_sqrt)
                        / &denom), x_)
                    + rubi_simp(&(b__.sqrt()
                        * (Atom::var(Symbol::PI) / Atom::num(2)).sqrt()
                        * (&ab_half.cosh() + ab_half.sinh())
                        * half.sinh()
                        * rubi_erf(scaled_sqrt)
                        / denom), x_)
        },
    ));
}

fn push_rules_rule_6415(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, d__, x_);
    rules.push(rubi_rule!(
        order: 6415,
        source: "Int[Sqrt[a_.+b_.*ArcCosh[-1+d_.*x_^2]],x_Symbol] :=
          2*Sqrt[a+b*ArcCosh[-1+d*x^2]]*Cosh[(1/2)*ArcCosh[-1+d*x^2]]^2/(d*x) -
          Sqrt[b]*Sqrt[Pi/2]*(Cosh[a/(2*b)]-Sinh[a/(2*b)])*Cosh[(1/2)*ArcCosh[-1+d*x^2]]*
            Erfi[(1/Sqrt[2*b])*Sqrt[a+b*ArcCosh[-1+d*x^2]]]/(d*x) -
          Sqrt[b]*Sqrt[Pi/2]*(Cosh[a/(2*b)]+Sinh[a/(2*b)])*Cosh[(1/2)*ArcCosh[-1+d*x^2]]*
            Erf[(1/Sqrt[2*b])*Sqrt[a+b*ArcCosh[-1+d*x^2]]]/(d*x) /;
        FreeQ[{a,b,d},x]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: (a__ + b__ * (Atom::num(-1) + d__ * x_.pow(2)).acosh()).sqrt(),
        with: [a__, b__, d__, x_],
        optional: [a__, b__, d__],
        when: { freeq!([a__, b__, d__], x_) },
        rhs: {
            let acosh = (Atom::num(-1) + &d__ * x_.pow(2)).acosh();
            let half = &acosh / Atom::num(2);
            let argument = &a__ + &b__ * acosh;
            let scaled_sqrt = &argument.sqrt() / (Atom::num(2) * &b__).sqrt();
            let ab_half = &a__ / (Atom::num(2) * &b__);
            let denom = &d__ * x_;
            rubi_simp(&(Atom::num(2) * &argument.sqrt() * &half.cosh().pow(2) / &denom), x_)
                    - rubi_simp(&(b__.sqrt()
                        * (Atom::var(Symbol::PI) / Atom::num(2)).sqrt()
                        * (&ab_half.cosh() - &ab_half.sinh())
                        * &half.cosh()
                        * rubi_erfi(&scaled_sqrt)
                        / &denom), x_)
                    - rubi_simp(&(b__.sqrt()
                        * (Atom::var(Symbol::PI) / Atom::num(2)).sqrt()
                        * (&ab_half.cosh() + ab_half.sinh())
                        * half.cosh()
                        * rubi_erf(scaled_sqrt)
                        / denom), x_)
        },
    ));
}

fn push_rules_rule_6416(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 6416,
        source: "Int[(a_.+b_.*ArcCosh[c_+d_.*x_^2])^n_,x_Symbol] :=
          x*(a+b*ArcCosh[c+d*x^2])^n -
          2*b*n*(2*c*d*x^2+d^2*x^4)*(a+b*ArcCosh[c+d*x^2])^(n-1)/(d*x*Sqrt[-1+c+d*x^2]*Sqrt[1+c+d*x^2]) +
          4*b^2*n*(n-1) \\[Star] Int[(a+b*ArcCosh[c+d*x^2])^(n-2),x] /;
        FreeQ[{a,b,c,d},x] && EqQ[c^2,1] && GtQ[n,1]",
        desc: "Integration by parts and piecewise constant extraction both twice!",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, n_, x_],
        optional: [a__, b__, d__],
        when: { freeq!([a__, b__, c__, d__], x_) && eqq!(c__.pow(2), 1) && gtq!(n_, 1) },
        rhs: {
            let argument = &a__ + &b__ * (&c__ + &d__ * x_.pow(2)).acosh();
            let denominator = &d__
                * x_
                * (Atom::num(-1) + &c__ + &d__ * x_.pow(2)).sqrt()
                * (Atom::num(1) + &c__ + &d__ * x_.pow(2)).sqrt();
            let numerator = Atom::num(2) * &c__ * &d__ * x_.pow(2) + d__.pow(2) * x_.pow(4);
            let coefficient = Atom::num(4) * b__.pow(2) * &n_ * (&n_ - Atom::num(1));
            rubi_simp(&(x_ * argument.pow(&n_)), x_)
                    - rubi_simp(&(Atom::num(2) * &b__ * &n_ * numerator * argument.pow(&n_ - Atom::num(1)) / denominator), x_)
                    + rubi_star(coefficient, rubi_rhs_int(&argument.pow(&n_ - Atom::num(2)), x_))
        },
    ));
}

fn push_rules_rule_6417(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, d__, x_);
    rules.push(rubi_rule!(
        order: 6417,
        source: "Int[1/(a_.+b_.*ArcCosh[1+d_.*x_^2]),x_Symbol] :=
          x*Cosh[a/(2*b)]*CoshIntegral[(a+b*ArcCosh[1+d*x^2])/(2*b)]/(Sqrt[2]*b*Sqrt[d*x^2]) -
          x*Sinh[a/(2*b)]*SinhIntegral[(a+b*ArcCosh[1+d*x^2])/(2*b)]/(Sqrt[2]*b*Sqrt[d*x^2]) /;
        FreeQ[{a,b,d},x]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: Atom::num(1) / (a__ + b__ * (Atom::num(1) + d__ * x_.pow(2)).acosh()),
        with: [a__, b__, d__, x_],
        optional: [a__, b__, d__],
        when: { freeq!([a__, b__, d__], x_) },
        rhs: {
            let argument = &a__ + &b__ * (Atom::num(1) + &d__ * x_.pow(2)).acosh();
            let denom = Atom::num(2).sqrt() * &b__ * (&d__ * x_.pow(2)).sqrt();
            let ab_half = &a__ / (Atom::num(2) * &b__);
            rubi_simp(&(x_ * &ab_half.cosh() * rubi_cosh_integral(&argument / (Atom::num(2) * &b__)) / &denom), x_)
                    - rubi_simp(&(x_ * ab_half.sinh() * rubi_sinh_integral(argument / (Atom::num(2) * &b__)) / denom), x_)
        },
    ));
}

fn push_rules_rule_6418(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, d__, x_);
    rules.push(rubi_rule!(
        order: 6418,
        source: "Int[1/(a_.+b_.*ArcCosh[-1+d_.*x_^2]),x_Symbol] :=
          -x*Sinh[a/(2*b)]*CoshIntegral[(a+b*ArcCosh[-1+d*x^2])/(2*b)]/(Sqrt[2]*b*Sqrt[d*x^2]) +
          x*Cosh[a/(2*b)]*SinhIntegral[(a+b*ArcCosh[-1+d*x^2])/(2*b)]/(Sqrt[2]*b*Sqrt[d*x^2]) /;
        FreeQ[{a,b,d},x]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: Atom::num(1) / (a__ + b__ * (Atom::num(-1) + d__ * x_.pow(2)).acosh()),
        with: [a__, b__, d__, x_],
        optional: [a__, b__, d__],
        when: { freeq!([a__, b__, d__], x_) },
        rhs: {
            let argument = &a__ + &b__ * (Atom::num(-1) + &d__ * x_.pow(2)).acosh();
            let denom = Atom::num(2).sqrt() * &b__ * (&d__ * x_.pow(2)).sqrt();
            let ab_half = &a__ / (Atom::num(2) * &b__);
            rubi_simp(&(Atom::num(-1) * x_ * &ab_half.sinh() * rubi_cosh_integral(&argument / (Atom::num(2) * &b__)) / &denom), x_)
                    + rubi_simp(&(x_ * ab_half.cosh() * rubi_sinh_integral(argument / (Atom::num(2) * &b__)) / denom), x_)
        },
    ));
}

fn push_rules_rule_6419(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, d__, x_);
    rules.push(rubi_rule!(
        order: 6419,
        source: "Int[1/Sqrt[a_.+b_.*ArcCosh[1+d_.*x_^2]],x_Symbol] :=
          Sqrt[Pi/2]*(Cosh[a/(2*b)]-Sinh[a/(2*b)])*Sinh[ArcCosh[1+d*x^2]/2]*Erfi[Sqrt[a+b*ArcCosh[1+d*x^2]]/Sqrt[2*b]]/(Sqrt[b]*d*x) +
          Sqrt[Pi/2]*(Cosh[a/(2*b)]+Sinh[a/(2*b)])*Sinh[ArcCosh[1+d*x^2]/2]*Erf[Sqrt[a+b*ArcCosh[1+d*x^2]]/Sqrt[2*b]]/(Sqrt[b]*d*x) /;
        FreeQ[{a,b,d},x]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: Atom::num(1) / (a__ + b__ * (Atom::num(1) + d__ * x_.pow(2)).acosh()).sqrt(),
        with: [a__, b__, d__, x_],
        optional: [a__, b__, d__],
        when: { freeq!([a__, b__, d__], x_) },
        rhs: {
            let acosh = (Atom::num(1) + &d__ * x_.pow(2)).acosh();
            let argument = &a__ + &b__ * &acosh;
            let half = acosh / Atom::num(2);
            let scaled_sqrt = argument.sqrt() / (Atom::num(2) * &b__).sqrt();
            let ab_half = &a__ / (Atom::num(2) * &b__);
            let denom = b__.sqrt() * &d__ * x_;
            rubi_simp(&((Atom::var(Symbol::PI) / Atom::num(2)).sqrt()
                    * (&ab_half.cosh() - &ab_half.sinh())
                    * &half.sinh()
                    * rubi_erfi(&scaled_sqrt)
                    / &denom), x_)
                    + rubi_simp(&((Atom::var(Symbol::PI) / Atom::num(2)).sqrt()
                        * (&ab_half.cosh() + ab_half.sinh())
                        * half.sinh()
                        * rubi_erf(scaled_sqrt)
                        / denom), x_)
        },
    ));
}

fn push_rules_rule_6420(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, d__, x_);
    rules.push(rubi_rule!(
        order: 6420,
        source: "Int[1/Sqrt[a_.+b_.*ArcCosh[-1+d_.*x_^2]],x_Symbol] :=
          Sqrt[Pi/2]*(Cosh[a/(2*b)]-Sinh[a/(2*b)])*Cosh[ArcCosh[-1+d*x^2]/2]*Erfi[Sqrt[a+b*ArcCosh[-1+d*x^2]]/Sqrt[2*b]]/(Sqrt[b]*d*x) -
          Sqrt[Pi/2]*(Cosh[a/(2*b)]+Sinh[a/(2*b)])*Cosh[ArcCosh[-1+d*x^2]/2]*Erf[Sqrt[a+b*ArcCosh[-1+d*x^2]]/Sqrt[2*b]]/(Sqrt[b]*d*x) /;
        FreeQ[{a,b,d},x]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: Atom::num(1) / (a__ + b__ * (Atom::num(-1) + d__ * x_.pow(2)).acosh()).sqrt(),
        with: [a__, b__, d__, x_],
        optional: [a__, b__, d__],
        when: { freeq!([a__, b__, d__], x_) },
        rhs: {
            let acosh = (Atom::num(-1) + &d__ * x_.pow(2)).acosh();
            let argument = &a__ + &b__ * &acosh;
            let half = acosh / Atom::num(2);
            let scaled_sqrt = argument.sqrt() / (Atom::num(2) * &b__).sqrt();
            let ab_half = &a__ / (Atom::num(2) * &b__);
            let denom = b__.sqrt() * &d__ * x_;
            rubi_simp(&((Atom::var(Symbol::PI) / Atom::num(2)).sqrt()
                    * (&ab_half.cosh() - &ab_half.sinh())
                    * &half.cosh()
                    * rubi_erfi(&scaled_sqrt)
                    / &denom), x_)
                    - rubi_simp(&((Atom::var(Symbol::PI) / Atom::num(2)).sqrt()
                        * (&ab_half.cosh() + ab_half.sinh())
                        * half.cosh()
                        * rubi_erf(scaled_sqrt)
                        / denom), x_)
        },
    ));
}

fn push_rules_rule_6421(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, d__, x_);
    rules.push(rubi_rule!(
        order: 6421,
        source: "Int[1/(a_.+b_.*ArcCosh[1+d_.*x_^2])^(3/2),x_Symbol] :=
          -Sqrt[d*x^2]*Sqrt[2+d*x^2]/(b*d*x*Sqrt[a+b*ArcCosh[1+d*x^2]]) +
          Sqrt[Pi/2]*(Cosh[a/(2*b)]-Sinh[a/(2*b)])*Sinh[ArcCosh[1+d*x^2]/2]*Erfi[Sqrt[a+b*ArcCosh[1+d*x^2]]/Sqrt[2*b]]/(b^(3/2)*d*x)-
          Sqrt[Pi/2]*(Cosh[a/(2*b)]+Sinh[a/(2*b)])*Sinh[ArcCosh[1+d*x^2]/2]*Erf[Sqrt[a+b*ArcCosh[1+d*x^2]]/Sqrt[2*b]]/(b^(3/2)*d*x) /;
        FreeQ[{a,b,d},x]",
        desc: "Integration by parts",
        refs: [],
        pattern: Atom::num(1) / (a__ + b__ * (Atom::num(1) + d__ * x_.pow(2)).acosh()).pow(Atom::num(3) / Atom::num(2)),
        with: [a__, b__, d__, x_],
        optional: [a__, b__, d__],
        when: { freeq!([a__, b__, d__], x_) },
        rhs: {
            let acosh = (Atom::num(1) + &d__ * x_.pow(2)).acosh();
            let argument = &a__ + &b__ * &acosh;
            let half = acosh / Atom::num(2);
            let scaled_sqrt = &argument.sqrt() / (Atom::num(2) * &b__).sqrt();
            let ab_half = &a__ / (Atom::num(2) * &b__);
            let denom = b__.pow(Atom::num(3) / Atom::num(2)) * &d__ * x_;
            rubi_simp(&(-(&d__ * x_.pow(2)).sqrt()
                    * (Atom::num(2) + &d__ * x_.pow(2)).sqrt()
                    / (&b__ * &d__ * x_ * &argument.sqrt())), x_)
                    + rubi_simp(&((Atom::var(Symbol::PI) / Atom::num(2)).sqrt()
                        * (&ab_half.cosh() - &ab_half.sinh())
                        * &half.sinh()
                        * rubi_erfi(&scaled_sqrt)
                        / &denom), x_)
                    - rubi_simp(&((Atom::var(Symbol::PI) / Atom::num(2)).sqrt()
                        * (&ab_half.cosh() + ab_half.sinh())
                        * half.sinh()
                        * rubi_erf(scaled_sqrt)
                        / denom), x_)
        },
    ));
}

fn push_rules_rule_6422(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, d__, x_);
    rules.push(rubi_rule!(
        order: 6422,
        source: "Int[1/(a_.+b_.*ArcCosh[-1+d_.*x_^2])^(3/2),x_Symbol] :=
          -Sqrt[d*x^2]*Sqrt[-2+d*x^2]/(b*d*x*Sqrt[a+b*ArcCosh[-1+d*x^2]]) +
          Sqrt[Pi/2]*(Cosh[a/(2*b)]-Sinh[a/(2*b)])*Cosh[ArcCosh[-1+d*x^2]/2]*Erfi[Sqrt[a+b*ArcCosh[-1+d*x^2]]/Sqrt[2*b]]/(b^(3/2)*d*x) +
          Sqrt[Pi/2]*(Cosh[a/(2*b)]+Sinh[a/(2*b)])*Cosh[ArcCosh[-1+d*x^2]/2]*Erf[Sqrt[a+b*ArcCosh[-1+d*x^2]]/Sqrt[2*b]]/(b^(3/2)*d*x) /;
        FreeQ[{a,b,d},x]",
        desc: "Integration by parts",
        refs: [],
        pattern: Atom::num(1) / (a__ + b__ * (Atom::num(-1) + d__ * x_.pow(2)).acosh()).pow(Atom::num(3) / Atom::num(2)),
        with: [a__, b__, d__, x_],
        optional: [a__, b__, d__],
        when: { freeq!([a__, b__, d__], x_) },
        rhs: {
            let acosh = (Atom::num(-1) + &d__ * x_.pow(2)).acosh();
            let argument = &a__ + &b__ * &acosh;
            let half = acosh / Atom::num(2);
            let scaled_sqrt = &argument.sqrt() / (Atom::num(2) * &b__).sqrt();
            let ab_half = &a__ / (Atom::num(2) * &b__);
            let denom = b__.pow(Atom::num(3) / Atom::num(2)) * &d__ * x_;
            rubi_simp(&(-(&d__ * x_.pow(2)).sqrt()
                    * (Atom::num(-2) + &d__ * x_.pow(2)).sqrt()
                    / (&b__ * &d__ * x_ * &argument.sqrt())), x_)
                    + rubi_simp(&((Atom::var(Symbol::PI) / Atom::num(2)).sqrt()
                        * (&ab_half.cosh() - &ab_half.sinh())
                        * &half.cosh()
                        * rubi_erfi(&scaled_sqrt)
                        / &denom), x_)
                    + rubi_simp(&((Atom::var(Symbol::PI) / Atom::num(2)).sqrt()
                        * (&ab_half.cosh() + ab_half.sinh())
                        * half.cosh()
                        * rubi_erf(scaled_sqrt)
                        / denom), x_)
        },
    ));
}

fn push_rules_rule_6423(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, d__, x_);
    rules.push(rubi_rule!(
        order: 6423,
        source: "Int[1/(a_.+b_.*ArcCosh[1+d_.*x_^2])^2,x_Symbol] :=
          -Sqrt[d*x^2]*Sqrt[2+d*x^2]/(2*b*d*x*(a+b*ArcCosh[1+d*x^2])) -
          x*Sinh[a/(2*b)]*CoshIntegral[(a+b*ArcCosh[1+d*x^2])/(2*b)]/(2*Sqrt[2]*b^2*Sqrt[d*x^2]) +
          x*Cosh[a/(2*b)]*SinhIntegral[(a+b*ArcCosh[1+d*x^2])/(2*b)]/(2*Sqrt[2]*b^2*Sqrt[d*x^2]) /;
        FreeQ[{a,b,d},x]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: Atom::num(1) / (a__ + b__ * (Atom::num(1) + d__ * x_.pow(2)).acosh()).pow(2),
        with: [a__, b__, d__, x_],
        optional: [a__, b__, d__],
        when: { freeq!([a__, b__, d__], x_) },
        rhs: {
            let argument = &a__ + &b__ * (Atom::num(1) + &d__ * x_.pow(2)).acosh();
            let ab_half = &a__ / (Atom::num(2) * &b__);
            let denom = Atom::num(2).sqrt() * b__.pow(2) * (&d__ * x_.pow(2)).sqrt();
            rubi_simp(&(-(&d__ * x_.pow(2)).sqrt()
                    * (Atom::num(2) + &d__ * x_.pow(2)).sqrt()
                    / (Atom::num(2) * &b__ * &d__ * x_ * &argument)), x_)
                    - rubi_simp(&(x_ * &ab_half.sinh() * rubi_cosh_integral(&argument / (Atom::num(2) * &b__)) / (Atom::num(2) * &denom)), x_)
                    + rubi_simp(&(x_ * ab_half.cosh() * rubi_sinh_integral(argument / (Atom::num(2) * &b__)) / (Atom::num(2) * denom)), x_)
        },
    ));
}

fn push_rules_rule_6424(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, d__, x_);
    rules.push(rubi_rule!(
        order: 6424,
        source: "Int[1/(a_.+b_.*ArcCosh[-1+d_.*x_^2])^2,x_Symbol] :=
          -Sqrt[d*x^2]*Sqrt[-2+d*x^2]/(2*b*d*x*(a+b*ArcCosh[-1+d*x^2])) +
          x*Cosh[a/(2*b)]*CoshIntegral[(a+b*ArcCosh[-1+d*x^2])/(2*b)]/(2*Sqrt[2]*b^2*Sqrt[d*x^2]) -
          x*Sinh[a/(2*b)]*SinhIntegral[(a+b*ArcCosh[-1+d*x^2])/(2*b)]/(2*Sqrt[2]*b^2*Sqrt[d*x^2]) /;
        FreeQ[{a,b,d},x]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: Atom::num(1) / (a__ + b__ * (Atom::num(-1) + d__ * x_.pow(2)).acosh()).pow(2),
        with: [a__, b__, d__, x_],
        optional: [a__, b__, d__],
        when: { freeq!([a__, b__, d__], x_) },
        rhs: {
            let argument = &a__ + &b__ * (Atom::num(-1) + &d__ * x_.pow(2)).acosh();
            let ab_half = &a__ / (Atom::num(2) * &b__);
            let denom = Atom::num(2).sqrt() * b__.pow(2) * (&d__ * x_.pow(2)).sqrt();
            rubi_simp(&(-(&d__ * x_.pow(2)).sqrt()
                    * (Atom::num(-2) + &d__ * x_.pow(2)).sqrt()
                    / (Atom::num(2) * &b__ * &d__ * x_ * &argument)), x_)
                    + rubi_simp(&(x_ * &ab_half.cosh() * rubi_cosh_integral(&argument / (Atom::num(2) * &b__)) / (Atom::num(2) * &denom)), x_)
                    - rubi_simp(&(x_ * ab_half.sinh() * rubi_sinh_integral(argument / (Atom::num(2) * &b__)) / (Atom::num(2) * denom)), x_)
        },
    ));
}

fn push_rules_rule_6425(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 6425,
        source: "Int[(a_.+b_.*ArcCosh[c_+d_.*x_^2])^n_,x_Symbol] :=
          -x*(a+b*ArcCosh[c+d*x^2])^(n+2)/(4*b^2*(n+1)*(n+2)) +
          (2*c*x^2 +d*x^4)*(a+b*ArcCosh[c+d*x^2])^(n+1)/(2*b*(n+1)*x*Sqrt[-1+c+d*x^2]*Sqrt[1+c+d*x^2]) +
          1/(4*b^2*(n+1)*(n+2)) \\[Star] Int[(a+b*ArcCosh[c+d*x^2])^(n+2),x] /;
        FreeQ[{a,b,c,d},x] && EqQ[c^2,1] && LtQ[n,-1] && NeQ[n,-2]",
        desc: "Inverted integration by parts and piecewise constant extraction both twice!",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, n_, x_],
        optional: [a__, b__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && eqq!(c__.pow(2), 1)
                && ltq!(n_, -1)
                && neq!(n_, -2)
        },
        rhs: {
            let argument = &a__ + &b__ * (&c__ + &d__ * x_.pow(2)).acosh();
            let denominator = Atom::num(2)
                * &b__
                * (&n_ + Atom::num(1))
                * x_
                * (Atom::num(-1) + &c__ + &d__ * x_.pow(2)).sqrt()
                * (Atom::num(1) + &c__ + &d__ * x_.pow(2)).sqrt();
            let numerator = Atom::num(2) * &c__ * x_.pow(2) + &d__ * x_.pow(4);
            let coefficient = Atom::num(1)
                / (Atom::num(4)
                    * b__.pow(2)
                    * (&n_ + Atom::num(1))
                    * (&n_ + Atom::num(2)));
            rubi_simp(&(Atom::num(-1) * x_ * argument.pow(&n_ + Atom::num(2))
                    / (Atom::num(4) * b__.pow(2) * (&n_ + Atom::num(1)) * (&n_ + Atom::num(2)))), x_)
                    + rubi_simp(&(numerator * argument.pow(&n_ + Atom::num(1)) / denominator), x_)
                    + rubi_star(coefficient, rubi_rhs_int(&argument.pow(&n_ + Atom::num(2)), x_))
        },
    ));
}

fn push_rules_rule_6426(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6426,
        source: "Int[ArcCosh[a_.*x_^p_]^n_./x_,x_Symbol] :=
          1/p \\[Star] Subst[Int[x^n*Tanh[x],x],x,ArcCosh[a*x^p]] /;
        FreeQ[{a,p},x] && IGtQ[n,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (a__ * x_.pow(p_)).acosh().pow(n_) / x_,
        with: [a__, p_, n_, x_],
        optional: [a__, n_],
        when: { freeq!([a__, p_], x_) && igtq!(n_, 0) },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().rubi_rhs();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let payload = sub_atom.pow(&n_) * sub_atom.tanh();
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            let substituted = rubi_subst(
                &primitive,
                substitution_symbol,
                (&a__ * x_.pow(&p_)).acosh(),
            );
            rubi_star(Atom::num(1) / &p_, substituted)
        },
    ));
}

fn push_rules_rule_6427(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, m_, n_, u__, x_);
    rules.push(rubi_rule!(
        order: 6427,
        source: "Int[u_.*ArcCosh[c_./(a_.+b_.*x_^n_.)]^m_.,x_Symbol] :=
          Int[u*ArcSech[a/c+b*x^n/c]^m,x] /;
        FreeQ[{a,b,c,n,m},x]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: u__ * (c__ / (a__ + b__ * x_.pow(n_))).acosh().pow(m_),
        with: [u__, c__, a__, b__, n_, m_, x_],
        optional: [u__, a__, b__, n_, m_, c__],
        when: { freeq!([a__, b__, c__, n_, m_], x_) },
        rhs: {
            let transformed = u__ * (&a__ / &c__ + &b__ * x_.pow(&n_) / &c__).asech().pow(&m_);
            rubi_rhs_int(&transformed, x_)
        },
    ));
}

fn push_rules_rule_6428(rules: &mut Vec<RubiRule>) {
    rubi_symb!(b__, n_, x_);
    rules.push(rubi_rule!(
        order: 6428,
        source: "Int[ArcCosh[Sqrt[1+b_.*x_^2]]^n_./Sqrt[1+b_.*x_^2],x_Symbol] :=
          Sqrt[-1+Sqrt[1+b*x^2]]*Sqrt[1+Sqrt[1+b*x^2]]/(b*x) \\[Star] Subst[Int[ArcCosh[x]^n/(Sqrt[-1+x]*Sqrt[1+x]),x],x,Sqrt[1+b*x^2]] /;
        FreeQ[{b,n},x]",
        desc: "Piecewise constant extraction and integration by substitution",
        refs: [],
        pattern: (Atom::num(1) + b__ * x_.pow(2)).sqrt().acosh().pow(n_)
            / (Atom::num(1) + b__ * x_.pow(2)).sqrt(),
        with: [b__, n_, x_],
        optional: [b__, n_],
        when: { freeq!([b__, n_], x_) },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().rubi_rhs();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let payload = sub_atom.acosh().pow(&n_) / ((Atom::num(-1) + &sub_atom).sqrt() * (Atom::num(1) + &sub_atom).sqrt());
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            let replacement = (Atom::num(1) + &b__ * x_.pow(2)).sqrt();
            let coefficient = (Atom::num(-1) + &replacement).sqrt()
                * (Atom::num(1) + &replacement).sqrt()
                / (&b__ * x_);
            let substituted = rubi_subst(&primitive, substitution_symbol, replacement);
            rubi_star(coefficient, substituted)
        },
    ));
}

fn push_rules_rule_6429(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, f__, n_, x_);
    rules.push(rubi_rule!(
        order: 6429,
        source: "Int[f_^(c_.*ArcCosh[a_.+b_.*x_]^n_.),x_Symbol] :=
          1/b \\[Star] Subst[Int[f^(c*x^n)*Sinh[x],x],x,ArcCosh[a+b*x]] /;
        FreeQ[{a,b,c,f},x] && IGtQ[n,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: f__.pow(c__ * (a__ + b__ * x_).acosh().pow(n_)),
        with: [f__, c__, a__, b__, n_, x_],
        optional: [c__, a__, b__, n_],
        when: { freeq!([a__, b__, c__, f__], x_) && igtq!(n_, 0) },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().rubi_rhs();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let payload = f__.pow(&c__ * sub_atom.pow(&n_)) * sub_atom.sinh();
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            let substituted = rubi_subst(
                &primitive,
                substitution_symbol,
                (&a__ + &b__ * x_).acosh(),
            );
            rubi_star(Atom::num(1) / &b__, substituted)
        },
    ));
}

fn push_rules_rule_6430(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 6430,
        source: "Int[x_^m_.*f_^(c_.*ArcCosh[a_.+b_.*x_]^n_.),x_Symbol] :=
          1/b \\[Star] Subst[Int[(-a/b+Cosh[x]/b)^m*f^(c*x^n)*Sinh[x],x],x,ArcCosh[a+b*x]] /;
        FreeQ[{a,b,c,f},x] && IGtQ[m,0] && IGtQ[n,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: x_.pow(m_) * f__.pow(c__ * (a__ + b__ * x_).acosh().pow(n_)),
        with: [m_, f__, c__, a__, b__, n_, x_],
        optional: [c__, a__, b__, n_, m_],
        when: { freeq!([a__, b__, c__, f__], x_) && igtq!(m_, 0) && igtq!(n_, 0) },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().rubi_rhs();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let payload = (-&a__ / &b__ + sub_atom.cosh() / &b__).pow(&m_)
                * f__.pow(&c__ * sub_atom.pow(&n_))
                * sub_atom.sinh();
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            let substituted = rubi_subst(
                &primitive,
                substitution_symbol,
                (&a__ + &b__ * x_).acosh(),
            );
            rubi_star(Atom::num(1) / &b__, substituted)
        },
    ));
}

fn push_rules_rule_6431(rules: &mut Vec<RubiRule>) {
    rubi_symb!(u_);
    rules.push(rubi_rule!(
        order: 6431,
        source: "Int[ArcCosh[u_],x_Symbol] :=
          x*ArcCosh[u] -
          Int[SimplifyIntegrand[x*D[u,x]/(Sqrt[-1+u]*Sqrt[1+u]),x],x] /;
        InverseFunctionFreeQ[u,x] && Not[FunctionOfExponentialQ[u,x]]",
        desc: "Integration by parts",
        refs: [],
        pattern: Atom::var(u_).acosh(),
        with: [u_, x_],
        when: { rubi_inverse_function_free_q(&u_, x_) && !rubi_function_of_exponential_q(u_.as_view(), x_) },
        rhs: {
            let recursive = rubi_simplify_integrand(
                &(x_ * u_.derivative(x_) / ((Atom::num(-1) + &u_).sqrt() * (Atom::num(1) + &u_).sqrt())),
                x_,
            );
            rubi_simp(&(x_ * u_.acosh()), x_) - rubi_rhs_int(&recursive, x_)
        },
    ));
}

fn push_rules_rule_6432(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, u_, x_);
    rules.push(rubi_rule!(
        order: 6432,
        source: "Int[(c_.+d_.*x_)^m_.*(a_.+b_.*ArcCosh[u_]),x_Symbol] :=
          (c+d*x)^(m+1)*(a+b*ArcCosh[u])/(d*(m+1)) -
          b/(d*(m+1)) \\[Star] Int[SimplifyIntegrand[(c+d*x)^(m+1)*D[u,x]/(Sqrt[-1+u]*Sqrt[1+u]),x],x] /;
        FreeQ[{a,b,c,d,m},x] && NeQ[m,-1] && InverseFunctionFreeQ[u,x] && Not[FunctionOfQ[(c+d*x)^(m+1),u,x]] && Not[FunctionOfExponentialQ[u,x]]",
        desc: "Integration by parts and piecewise constant extraction",
        refs: [],
        pattern: (c__ + d__ * x_).pow(m_) * (a__ + b__ * Atom::var(u_).acosh()),
        with: [c__, d__, m_, a__, b__, u_, x_],
        optional: [c__, d__, m_, a__, b__],
        when: {
            freeq!([a__, b__, c__, d__, m_], x_)
                && neq!(m_, -1)
                && rubi_inverse_function_free_q(&u_, x_)
                && !rubi_function_of_q(&(&c__ + &d__ * x_).pow(&m_ + Atom::num(1)), &u_, x_)
                && !rubi_function_of_exponential_q(u_.as_view(), x_)
        },
        rhs: {
            let linear = &c__ + &d__ * x_;
            let argument = &a__ + &b__ * u_.acosh();
            let recursive = rubi_simplify_integrand(
                &(linear.pow(&m_ + Atom::num(1))
                    * u_.derivative(x_)
                    / ((Atom::num(-1) + &u_).sqrt() * (Atom::num(1) + &u_).sqrt())),
                x_,
            );
            let coefficient = &b__ / (&d__ * (&m_ + Atom::num(1)));
            rubi_simp(&(linear.pow(&m_ + Atom::num(1)) * argument / (&d__ * (&m_ + Atom::num(1)))), x_)
                    - rubi_star(coefficient, rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_6433(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, u_, v__);
    rules.push(rubi_rule!(
        order: 6433,
        source: "Int[v_*(a_.+b_.*ArcCosh[u_]),x_Symbol] :=
          With[{w=IntHide[v,x]},
          (a+b*ArcCosh[u]) \\[Star] w - b \\[Star] Int[SimplifyIntegrand[w*D[u,x]/(Sqrt[-1+u]*Sqrt[1+u]),x],x] /;
         InverseFunctionFreeQ[w,x]] /;
        FreeQ[{a,b},x] && InverseFunctionFreeQ[u,x] && Not[MatchQ[v, (c_.+d_.*x)^m_. /; FreeQ[{c,d,m},x]]]",
        desc: "Integration by parts and piecewise constant extraction",
        refs: [],
        pattern: v__ * (a__ + b__ * Atom::var(u_).acosh()),
        with: [v__, a__, b__, u_, x_],
        optional: [a__, b__],
        when: {
            freeq!([a__, b__], x_)
                && rubi_inverse_function_free_q(&u_, x_)
                && !rubi_match_optional_multiplier_linear_power_q(&v__, x_)
                && rubi_int_hide_inverse_function_free_q(&v__, x_)
        },
        rhs: {
            let v_int = rubi_int_hide(&v__, x_).rubi_rhs();
            let argument = &a__ + &b__ * u_.acosh();
            let recursive = rubi_simplify_integrand(
                &(&v_int * u_.derivative(x_) / ((Atom::num(-1) + &u_).sqrt() * (Atom::num(1) + &u_).sqrt())),
                x_,
            );
            rubi_star(argument, v_int)
                    - rubi_star(b__, rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_6434(rules: &mut Vec<RubiRule>) {
    rubi_symb!(n_, u_);
    rules.push(rubi_rule!(
        order: 6434,
        source: "Int[E^(n_.*ArcCosh[u_]), x_Symbol] :=
          Int[(u+Sqrt[-1+u]*Sqrt[1+u])^n,x] /;
        IntegerQ[n] && PolyQ[u,x]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: (n_ * Atom::var(u_).acosh()).exp(),
        with: [n_, u_, x_],
        optional: [n_],
        when: { integerq!(n_) && rubi_poly_q(&u_, x_) },
        rhs: {
            let transformed = (&u_ + (Atom::num(-1) + &u_).sqrt() * (Atom::num(1) + &u_).sqrt()).pow(&n_);
            rubi_rhs_int(&transformed, x_)
        },
    ));
}

fn push_rules_rule_6435(rules: &mut Vec<RubiRule>) {
    rubi_symb!(m_, n_, u_, x_);
    rules.push(rubi_rule!(
        order: 6435,
        source: "Int[x_^m_.*E^(n_.*ArcCosh[u_]), x_Symbol] :=
          Int[x^m*(u+Sqrt[-1+u]*Sqrt[1+u])^n,x] /;
        RationalQ[m] && IntegerQ[n] && PolyQ[u,x]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: x_.pow(m_) * (n_ * Atom::var(u_).acosh()).exp(),
        with: [m_, n_, u_, x_],
        optional: [n_, m_],
        when: { rationalq!(m_) && integerq!(n_) && rubi_poly_q(&u_, x_) },
        rhs: {
            let transformed =
                x_.pow(&m_) * (&u_ + (Atom::num(-1) + &u_).sqrt() * (Atom::num(1) + &u_).sqrt()).pow(&n_);
            rubi_rhs_int(&transformed, x_)
        },
    ));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn downvalues_6410_through_6435_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .filter(|order| (6410..=6435).contains(order))
            .collect::<Vec<_>>();
        assert_eq!(orders, (6410..=6435).collect::<Vec<_>>());
    }
}

// Generated shared pattern builders.

#[inline(never)]
fn rubi_shared_pattern_0(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    (a__ + b__ * (c__ + d__ * x_.pow(2)).acosh()).pow(n_)
}
