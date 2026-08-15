use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_5302(rules);
    push_rules_rule_5303(rules);
    push_rules_rule_5304(rules);
    push_rules_rule_5305(rules);
    push_rules_rule_5306(rules);
    push_rules_rule_5307(rules);
    push_rules_rule_5308(rules);
    push_rules_rule_5309(rules);
    push_rules_rule_5310(rules);
    push_rules_rule_5311(rules);
    push_rules_rule_5312(rules);
    push_rules_rule_5313(rules);
    push_rules_rule_5314(rules);
    push_rules_rule_5315(rules);
    push_rules_rule_5316(rules);
    push_rules_rule_5317(rules);
    push_rules_rule_5318(rules);
    push_rules_rule_5319(rules);
    push_rules_rule_5320(rules);
    push_rules_rule_5321(rules);
    push_rules_rule_5322(rules);
    push_rules_rule_5323(rules);
    push_rules_rule_5324(rules);
    push_rules_rule_5325(rules);
    push_rules_rule_5326(rules);
    push_rules_rule_5327(rules);
    push_rules_rule_5328(rules);
    push_rules_rule_5329(rules);
    push_rules_rule_5330(rules);
    push_rules_rule_5331(rules);
    push_rules_rule_5332(rules);
    push_rules_rule_5333(rules);
    push_rules_rule_5334(rules);
    push_rules_rule_5335(rules);
    push_rules_rule_5336(rules);
    push_rules_rule_5337(rules);
    push_rules_rule_5338(rules);
    push_rules_rule_5339(rules);
    push_rules_rule_5340(rules);
    push_rules_rule_5341(rules);
    push_rules_rule_5342(rules);
    push_rules_rule_5343(rules);
    push_rules_rule_5344(rules);
}

fn push_rules_rule_5302(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 5302,
        source: "Int[(a_.+b_.*ArcSin[c_+d_.*x_])^n_.,x_Symbol] :=
          1/d \\[Star] Subst[Int[(a+b*ArcSin[x])^n,x],x,c+d*x] /;
        FreeQ[{a,b,c,d,n},x]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (a__ + b__ * (c__ + d__ * x_).asin()).pow(n_),
        with: [a__, b__, c__, d__, n_, x_],
        optional: [a__, b__, d__, n_],
        when: { freeq!([a__, b__, c__, d__, n_], x_) },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let payload = (&a__ + &b__ * sub_atom.asin()).pow(&n_);
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            rubi_star(Atom::num(1) / &d__, rubi_subst(&primitive, substitution_symbol, &c__ + &d__ * x_))
        },
    ));
}

fn push_rules_rule_5303(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 5303,
        source: "Int[(a_.+b_.*ArcCos[c_+d_.*x_])^n_.,x_Symbol] :=
          1/d \\[Star] Subst[Int[(a+b*ArcCos[x])^n,x],x,c+d*x] /;
        FreeQ[{a,b,c,d,n},x]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (a__ + b__ * (c__ + d__ * x_).acos()).pow(n_),
        with: [a__, b__, c__, d__, n_, x_],
        optional: [a__, b__, d__, n_],
        when: { freeq!([a__, b__, c__, d__, n_], x_) },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let payload = (&a__ + &b__ * sub_atom.acos()).pow(&n_);
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            rubi_star(Atom::num(1) / &d__, rubi_subst(&primitive, substitution_symbol, &c__ + &d__ * x_))
        },
    ));
}

fn push_rules_rule_5304(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5304,
        source: "Int[(e_.+f_.*x_)^m_.*(a_.+b_.*ArcSin[c_+d_.*x_])^n_.,x_Symbol] :=
          1/d \\[Star] Subst[Int[((d*e-c*f)/d+f*x/d)^m*(a+b*ArcSin[x])^n,x],x,c+d*x] /;
        FreeQ[{a,b,c,d,e,f,m,n},x]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (e__ + f__ * x_).pow(m_) * (a__ + b__ * (c__ + d__ * x_).asin()).pow(n_),
        with: [e__, f__, m_, a__, b__, c__, d__, n_, x_],
        optional: [e__, f__, m_, a__, b__, d__, n_],
        when: { freeq!([a__, b__, c__, d__, e__, f__, m_, n_], x_) },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let transformed_linear = (&d__ * &e__ - &c__ * &f__) / &d__ + &f__ * &sub_atom / &d__;
            let payload = transformed_linear.pow(&m_) * (&a__ + &b__ * sub_atom.asin()).pow(&n_);
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            rubi_star(Atom::num(1) / &d__, rubi_subst(&primitive, substitution_symbol, &c__ + &d__ * x_))
        },
    ));
}

fn push_rules_rule_5305(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5305,
        source: "Int[(e_.+f_.*x_)^m_.*(a_.+b_.*ArcCos[c_+d_.*x_])^n_.,x_Symbol] :=
          1/d \\[Star] Subst[Int[((d*e-c*f)/d+f*x/d)^m*(a+b*ArcCos[x])^n,x],x,c+d*x] /;
        FreeQ[{a,b,c,d,e,f,m,n},x]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (e__ + f__ * x_).pow(m_) * (a__ + b__ * (c__ + d__ * x_).acos()).pow(n_),
        with: [e__, f__, m_, a__, b__, c__, d__, n_, x_],
        optional: [e__, f__, m_, a__, b__, d__, n_],
        when: { freeq!([a__, b__, c__, d__, e__, f__, m_, n_], x_) },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let transformed_linear = (&d__ * &e__ - &c__ * &f__) / &d__ + &f__ * &sub_atom / &d__;
            let payload = transformed_linear.pow(&m_) * (&a__ + &b__ * sub_atom.acos()).pow(&n_);
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            rubi_star(Atom::num(1) / &d__, rubi_subst(&primitive, substitution_symbol, &c__ + &d__ * x_))
        },
    ));
}

fn push_rules_rule_5306(rules: &mut Vec<RubiRule>) {
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
        order: 5306,
        source: "Int[(A_.+B_.*x_+C_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_+d_.*x_])^n_.,x_Symbol] :=
          1/d \\[Star] Subst[Int[(-C/d^2+C/d^2*x^2)^p*(a+b*ArcSin[x])^n,x],x,c+d*x] /;
        FreeQ[{a,b,c,d,A,B,C,n,p},x] && EqQ[B*(1-c^2)+2*A*c*d,0] && EqQ[2*c*C-B*d,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (capital_a__ + capital_b__ * x_ + capital_c__ * x_.pow(2)).pow(p_) * (a__ + b__ * (c__ + d__ * x_).asin()).pow(n_),
        with: [capital_a__, capital_b__, capital_c__, p_, a__, b__, c__, d__, n_, x_],
        optional: [capital_a__, capital_b__, capital_c__, p_, a__, b__, d__, n_],
        when: {
            freeq!([a__, b__, c__, d__, capital_a__, capital_b__, capital_c__, n_, p_], x_)
                && eqq!(&capital_b__ * (Atom::num(1) - c__.pow(2)) + Atom::num(2) * &capital_a__ * &c__ * &d__, 0)
                && eqq!(Atom::num(2) * &c__ * &capital_c__ - &capital_b__ * &d__, 0)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let transformed_quadratic = -&capital_c__ / d__.pow(2) + &capital_c__ * sub_atom.pow(2) / d__.pow(2);
            let payload = transformed_quadratic.pow(&p_) * (&a__ + &b__ * sub_atom.asin()).pow(&n_);
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            rubi_star(Atom::num(1) / &d__, rubi_subst(&primitive, substitution_symbol, &c__ + &d__ * x_))
        },
    ));
}

fn push_rules_rule_5307(rules: &mut Vec<RubiRule>) {
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
        order: 5307,
        source: "Int[(A_.+B_.*x_+C_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_+d_.*x_])^n_.,x_Symbol] :=
          1/d \\[Star] Subst[Int[(-C/d^2+C/d^2*x^2)^p*(a+b*ArcCos[x])^n,x],x,c+d*x] /;
        FreeQ[{a,b,c,d,A,B,C,n,p},x] && EqQ[B*(1-c^2)+2*A*c*d,0] && EqQ[2*c*C-B*d,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (capital_a__ + capital_b__ * x_ + capital_c__ * x_.pow(2)).pow(p_) * (a__ + b__ * (c__ + d__ * x_).acos()).pow(n_),
        with: [capital_a__, capital_b__, capital_c__, p_, a__, b__, c__, d__, n_, x_],
        optional: [capital_a__, capital_b__, capital_c__, p_, a__, b__, d__, n_],
        when: {
            freeq!([a__, b__, c__, d__, capital_a__, capital_b__, capital_c__, n_, p_], x_)
                && eqq!(&capital_b__ * (Atom::num(1) - c__.pow(2)) + Atom::num(2) * &capital_a__ * &c__ * &d__, 0)
                && eqq!(Atom::num(2) * &c__ * &capital_c__ - &capital_b__ * &d__, 0)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let transformed_quadratic = -&capital_c__ / d__.pow(2) + &capital_c__ * sub_atom.pow(2) / d__.pow(2);
            let payload = transformed_quadratic.pow(&p_) * (&a__ + &b__ * sub_atom.acos()).pow(&n_);
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            rubi_star(Atom::num(1) / &d__, rubi_subst(&primitive, substitution_symbol, &c__ + &d__ * x_))
        },
    ));
}

fn push_rules_rule_5308(rules: &mut Vec<RubiRule>) {
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
        order: 5308,
        source: "Int[(e_.+f_.*x_)^m_.*(A_.+B_.*x_+C_.*x_^2)^p_.*(a_.+b_.*ArcSin[c_+d_.*x_])^n_.,x_Symbol] :=
          1/d \\[Star] Subst[Int[((d*e-c*f)/d+f*x/d)^m*(-C/d^2+C/d^2*x^2)^p*(a+b*ArcSin[x])^n,x],x,c+d*x] /;
        FreeQ[{a,b,c,d,e,f,A,B,C,m,n,p},x] && EqQ[B*(1-c^2)+2*A*c*d,0] && EqQ[2*c*C-B*d,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (e__ + f__ * x_).pow(m_)
            * (capital_a__ + capital_b__ * x_ + capital_c__ * x_.pow(2)).pow(p_)
            * (a__ + b__ * (c__ + d__ * x_).asin()).pow(n_),
        with: [e__, f__, m_, capital_a__, capital_b__, capital_c__, p_, a__, b__, c__, d__, n_, x_],
        optional: [e__, f__, m_, capital_a__, capital_b__, capital_c__, p_, a__, b__, d__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, capital_a__, capital_b__, capital_c__, m_, n_, p_], x_)
                && eqq!(&capital_b__ * (Atom::num(1) - c__.pow(2)) + Atom::num(2) * &capital_a__ * &c__ * &d__, 0)
                && eqq!(Atom::num(2) * &c__ * &capital_c__ - &capital_b__ * &d__, 0)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let transformed_linear = (&d__ * &e__ - &c__ * &f__) / &d__ + &f__ * &sub_atom / &d__;
            let transformed_quadratic = -&capital_c__ / d__.pow(2) + &capital_c__ * sub_atom.pow(2) / d__.pow(2);
            let payload = transformed_linear.pow(&m_)
                * transformed_quadratic.pow(&p_)
                * (&a__ + &b__ * sub_atom.asin()).pow(&n_);
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            rubi_star(Atom::num(1) / &d__, rubi_subst(&primitive, substitution_symbol, &c__ + &d__ * x_))
        },
    ));
}

fn push_rules_rule_5309(rules: &mut Vec<RubiRule>) {
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
        order: 5309,
        source: "Int[(e_.+f_.*x_)^m_.*(A_.+B_.*x_+C_.*x_^2)^p_.*(a_.+b_.*ArcCos[c_+d_.*x_])^n_.,x_Symbol] :=
          1/d \\[Star] Subst[Int[((d*e-c*f)/d+f*x/d)^m*(-C/d^2+C/d^2*x^2)^p*(a+b*ArcCos[x])^n,x],x,c+d*x] /;
        FreeQ[{a,b,c,d,e,f,A,B,C,m,n,p},x] && EqQ[B*(1-c^2)+2*A*c*d,0] && EqQ[2*c*C-B*d,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (e__ + f__ * x_).pow(m_)
            * (capital_a__ + capital_b__ * x_ + capital_c__ * x_.pow(2)).pow(p_)
            * (a__ + b__ * (c__ + d__ * x_).acos()).pow(n_),
        with: [e__, f__, m_, capital_a__, capital_b__, capital_c__, p_, a__, b__, c__, d__, n_, x_],
        optional: [e__, f__, m_, capital_a__, capital_b__, capital_c__, p_, a__, b__, d__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, capital_a__, capital_b__, capital_c__, m_, n_, p_], x_)
                && eqq!(&capital_b__ * (Atom::num(1) - c__.pow(2)) + Atom::num(2) * &capital_a__ * &c__ * &d__, 0)
                && eqq!(Atom::num(2) * &c__ * &capital_c__ - &capital_b__ * &d__, 0)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let transformed_linear = (&d__ * &e__ - &c__ * &f__) / &d__ + &f__ * &sub_atom / &d__;
            let transformed_quadratic = -&capital_c__ / d__.pow(2) + &capital_c__ * sub_atom.pow(2) / d__.pow(2);
            let payload = transformed_linear.pow(&m_)
                * transformed_quadratic.pow(&p_)
                * (&a__ + &b__ * sub_atom.acos()).pow(&n_);
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            rubi_star(Atom::num(1) / &d__, rubi_subst(&primitive, substitution_symbol, &c__ + &d__ * x_))
        },
    ));
}

fn push_rules_rule_5310(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 5310,
        source: "Int[Sqrt[a_.+b_.*ArcSin[c_+d_.*x_^2]],x_Symbol] :=
          x*Sqrt[a+b*ArcSin[c+d*x^2]] -
          Sqrt[Pi]*x*(Cos[a/(2*b)]+c*Sin[a/(2*b)])*FresnelC[Sqrt[c/(Pi*b)]*Sqrt[a+b*ArcSin[c+d*x^2]]]/
            (Sqrt[c/b]*(Cos[ArcSin[c+d*x^2]/2]-c*Sin[ArcSin[c+d*x^2]/2])) +
          Sqrt[Pi]*x*(Cos[a/(2*b)]-c*Sin[a/(2*b)])*FresnelS[Sqrt[c/(Pi*b)]*Sqrt[a+b*ArcSin[c+d*x^2]]]/
            (Sqrt[c/b]*(Cos[ArcSin[c+d*x^2]/2]-c*Sin[ArcSin[c+d*x^2]/2])) /;
        FreeQ[{a,b,c,d},x] && EqQ[c^2,1]",
        desc: "Integration by parts",
        refs: [],
        pattern: (a__ + b__ * (c__ + d__ * x_.pow(2)).asin()).sqrt(),
        with: [a__, b__, c__, d__, x_],
        optional: [a__, b__, d__],
        when: { freeq!([a__, b__, c__, d__], x_) && eqq!(c__.pow(2), 1) },
        rhs: {
            let asin = (&c__ + &d__ * x_.pow(2)).asin();
            let argument = &a__ + &b__ * &asin;
            let half_asin = asin / Atom::num(2);
            let denom = (&c__ / &b__).sqrt() * (&half_asin.cos() - &c__ * half_asin.sin());
            rubi_simp(&(x_ * &argument.sqrt()), x_)
                    - rubi_simp(&(Atom::var(Symbol::PI).sqrt()
                        * x_
                        * ((&a__ / (Atom::num(2) * &b__)).cos() + &c__ * (&a__ / (Atom::num(2) * &b__)).sin())
                        * rubi_fresnel_c((&c__ / (Atom::var(Symbol::PI) * &b__)).sqrt() * &argument.sqrt())
                        / &denom), x_)
                    + rubi_simp(&(Atom::var(Symbol::PI).sqrt()
                        * x_
                        * ((&a__ / (Atom::num(2) * &b__)).cos() - &c__ * (&a__ / (Atom::num(2) * &b__)).sin())
                        * rubi_fresnel_s((&c__ / (Atom::var(Symbol::PI) * &b__)).sqrt() * argument.sqrt())
                        / denom), x_)
        },
    ));
}

fn push_rules_rule_5311(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, d__, x_);
    rules.push(rubi_rule!(
        order: 5311,
        source: "Int[Sqrt[a_.+b_.*ArcCos[1+d_.*x_^2]],x_Symbol] :=
          -2*Sqrt[a+b*ArcCos[1+d*x^2]]*Sin[ArcCos[1+d*x^2]/2]^2/(d*x) -
          2*Sqrt[Pi]*Sin[a/(2*b)]*Sin[ArcCos[1+d*x^2]/2]*FresnelC[Sqrt[1/(Pi*b)]*Sqrt[a+b*ArcCos[1+d*x^2]]]/(Sqrt[1/b]*d*x) +
          2*Sqrt[Pi]*Cos[a/(2*b)]*Sin[ArcCos[1+d*x^2]/2]*FresnelS[Sqrt[1/(Pi*b)]*Sqrt[a+b*ArcCos[1+d*x^2]]]/(Sqrt[1/b]*d*x) /;
        FreeQ[{a,b,d},x]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: (a__ + b__ * (Atom::num(1) + d__ * x_.pow(2)).acos()).sqrt(),
        with: [a__, b__, d__, x_],
        optional: [a__, b__, d__],
        when: { freeq!([a__, b__, d__], x_) },
        rhs: {
            let acos = (Atom::num(1) + &d__ * x_.pow(2)).acos();
            let argument = &a__ + &b__ * &acos;
            let half_acos = acos / Atom::num(2);
            let denom = (Atom::num(1) / &b__).sqrt() * &d__ * x_;
            rubi_simp(&(-Atom::num(2) * &argument.sqrt() * &half_acos.sin().pow(2) / (&d__ * x_)), x_)
                    - rubi_simp(&(Atom::num(2)
                        * Atom::var(Symbol::PI).sqrt()
                        * (&a__ / (Atom::num(2) * &b__)).sin()
                        * &half_acos.sin()
                        * rubi_fresnel_c((Atom::num(1) / (Atom::var(Symbol::PI) * &b__)).sqrt() * &argument.sqrt())
                        / &denom), x_)
                    + rubi_simp(&(Atom::num(2)
                        * Atom::var(Symbol::PI).sqrt()
                        * (&a__ / (Atom::num(2) * &b__)).cos()
                        * half_acos.sin()
                        * rubi_fresnel_s((Atom::num(1) / (Atom::var(Symbol::PI) * &b__)).sqrt() * argument.sqrt())
                        / denom), x_)
        },
    ));
}

fn push_rules_rule_5312(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, d__, x_);
    rules.push(rubi_rule!(
        order: 5312,
        source: "Int[Sqrt[a_.+b_.*ArcCos[-1+d_.*x_^2]],x_Symbol] :=
          2*Sqrt[a+b*ArcCos[-1+d*x^2]]*Cos[(1/2)*ArcCos[-1+d*x^2]]^2/(d*x) -
          2*Sqrt[Pi]*Cos[a/(2*b)]*Cos[ArcCos[-1+d*x^2]/2]*FresnelC[Sqrt[1/(Pi*b)]*Sqrt[a+b*ArcCos[-1+d*x^2]]]/(Sqrt[1/b]*d*x) -
          2*Sqrt[Pi]*Sin[a/(2*b)]*Cos[ArcCos[-1+d*x^2]/2]*FresnelS[Sqrt[1/(Pi*b)]*Sqrt[a+b*ArcCos[-1+d*x^2]]]/(Sqrt[1/b]*d*x) /;
        FreeQ[{a,b,d},x]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: (a__ + b__ * (-Atom::num(1) + d__ * x_.pow(2)).acos()).sqrt(),
        with: [a__, b__, d__, x_],
        optional: [a__, b__, d__],
        when: { freeq!([a__, b__, d__], x_) },
        rhs: {
            let acos = (-Atom::num(1) + &d__ * x_.pow(2)).acos();
            let argument = &a__ + &b__ * &acos;
            let half_acos = acos / Atom::num(2);
            let denom = (Atom::num(1) / &b__).sqrt() * &d__ * x_;
            rubi_simp(&(Atom::num(2) * &argument.sqrt() * &half_acos.cos().pow(2) / (&d__ * x_)), x_)
                    - rubi_simp(&(Atom::num(2)
                        * Atom::var(Symbol::PI).sqrt()
                        * (&a__ / (Atom::num(2) * &b__)).cos()
                        * &half_acos.cos()
                        * rubi_fresnel_c((Atom::num(1) / (Atom::var(Symbol::PI) * &b__)).sqrt() * &argument.sqrt())
                        / &denom), x_)
                    - rubi_simp(&(Atom::num(2)
                        * Atom::var(Symbol::PI).sqrt()
                        * (&a__ / (Atom::num(2) * &b__)).sin()
                        * half_acos.cos()
                        * rubi_fresnel_s((Atom::num(1) / (Atom::var(Symbol::PI) * &b__)).sqrt() * argument.sqrt())
                        / denom), x_)
        },
    ));
}

fn push_rules_rule_5313(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 5313,
        source: "Int[(a_.+b_.*ArcSin[c_+d_.*x_^2])^n_,x_Symbol] :=
          x*(a+b*ArcSin[c+d*x^2])^n +
          2*b*n*Sqrt[-2*c*d*x^2-d^2*x^4]*(a+b*ArcSin[c+d*x^2])^(n-1)/(d*x) -
          4*b^2*n*(n-1) \\[Star] Int[(a+b*ArcSin[c+d*x^2])^(n-2),x] /;
        FreeQ[{a,b,c,d},x] && EqQ[c^2,1] && GtQ[n,1]",
        desc: "Integration by parts twice",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, n_, x_],
        optional: [a__, b__, d__],
        when: { freeq!([a__, b__, c__, d__], x_) && eqq!(c__.pow(2), 1) && gtq!(n_, 1) },
        rhs: {
            let argument = &a__ + &b__ * (&c__ + &d__ * x_.pow(2)).asin();
            let radical = (-Atom::num(2) * &c__ * &d__ * x_.pow(2) - d__.pow(2) * x_.pow(4)).sqrt();
            let recursive = argument.pow(&n_ - Atom::num(2));
            rubi_simp(&(x_ * argument.pow(&n_)), x_)
                    + rubi_simp(&(Atom::num(2) * &b__ * &n_ * radical * argument.pow(&n_ - Atom::num(1)) / (&d__ * x_)), x_)
                    - rubi_star(Atom::num(4) * b__.pow(2) * &n_ * (&n_ - Atom::num(1)), rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_5314(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 5314,
        source: "Int[(a_.+b_.*ArcCos[c_+d_.*x_^2])^n_,x_Symbol] :=
          x*(a+b*ArcCos[c+d*x^2])^n -
          2*b*n*Sqrt[-2*c*d*x^2-d^2*x^4]*(a+b*ArcCos[c+d*x^2])^(n-1)/(d*x) -
          4*b^2*n*(n-1) \\[Star] Int[(a+b*ArcCos[c+d*x^2])^(n-2),x] /;
        FreeQ[{a,b,c,d},x] && EqQ[c^2,1] && GtQ[n,1]",
        desc: "Integration by parts twice",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, n_, x_],
        optional: [a__, b__, d__],
        when: { freeq!([a__, b__, c__, d__], x_) && eqq!(c__.pow(2), 1) && gtq!(n_, 1) },
        rhs: {
            let argument = &a__ + &b__ * (&c__ + &d__ * x_.pow(2)).acos();
            let radical = (-Atom::num(2) * &c__ * &d__ * x_.pow(2) - d__.pow(2) * x_.pow(4)).sqrt();
            let recursive = argument.pow(&n_ - Atom::num(2));
            rubi_simp(&(x_ * argument.pow(&n_)), x_)
                    - rubi_simp(&(Atom::num(2) * &b__ * &n_ * radical * argument.pow(&n_ - Atom::num(1)) / (&d__ * x_)), x_)
                    - rubi_star(Atom::num(4) * b__.pow(2) * &n_ * (&n_ - Atom::num(1)), rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_5315(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 5315,
        source: "Int[1/(a_.+b_.*ArcSin[c_+d_.*x_^2]),x_Symbol] :=
          -x*(c*Cos[a/(2*b)]-Sin[a/(2*b)])*CosIntegral[(c/(2*b))*(a+b*ArcSin[c+d*x^2])]/
            (2*b*(Cos[ArcSin[c+d*x^2]/2]-c*Sin[ArcSin[c+d*x^2]/2])) -
          x*(c*Cos[a/(2*b)]+Sin[a/(2*b)])*SinIntegral[(c/(2*b))*(a+b*ArcSin[c+d*x^2])]/
            (2*b*(Cos[ArcSin[c+d*x^2]/2]-c*Sin[ArcSin[c+d*x^2]/2])) /;
        FreeQ[{a,b,c,d},x] && EqQ[c^2,1]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: Atom::num(1) / (a__ + b__ * (c__ + d__ * x_.pow(2)).asin()),
        with: [a__, b__, c__, d__, x_],
        optional: [a__, b__, d__],
        when: { freeq!([a__, b__, c__, d__], x_) && eqq!(c__.pow(2), 1) },
        rhs: {
            let asin = (&c__ + &d__ * x_.pow(2)).asin();
            let argument = &a__ + &b__ * &asin;
            let ab_half = &a__ / (Atom::num(2) * &b__);
            let half_asin = asin / Atom::num(2);
            let denom = Atom::num(2) * &b__ * (&half_asin.cos() - &c__ * half_asin.sin());
            rubi_simp(&(Atom::num(-1) * x_
                    * (&c__ * &ab_half.cos() - &ab_half.sin())
                    * rubi_cos_integral(&c__ * &argument / (Atom::num(2) * &b__))
                    / &denom), x_)
                    - rubi_simp(&(x_
                        * (&c__ * &ab_half.cos() + ab_half.sin())
                        * rubi_sin_integral(&c__ * argument / (Atom::num(2) * &b__))
                        / denom), x_)
        },
    ));
}

fn push_rules_rule_5316(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, d__, x_);
    rules.push(rubi_rule!(
        order: 5316,
        source: "Int[1/(a_.+b_.*ArcCos[1+d_.*x_^2]),x_Symbol] :=
          x*Cos[a/(2*b)]*CosIntegral[(a+b*ArcCos[1+d*x^2])/(2*b)]/(Sqrt[2]*b*Sqrt[-d*x^2]) +
          x*Sin[a/(2*b)]*SinIntegral[(a+b*ArcCos[1+d*x^2])/(2*b)]/(Sqrt[2]*b*Sqrt[-d*x^2]) /;
        FreeQ[{a,b,d},x]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: Atom::num(1) / (a__ + b__ * (Atom::num(1) + d__ * x_.pow(2)).acos()),
        with: [a__, b__, d__, x_],
        optional: [a__, b__, d__],
        when: { freeq!([a__, b__, d__], x_) },
        rhs: {
            let argument = &a__ + &b__ * (Atom::num(1) + &d__ * x_.pow(2)).acos();
            let ab_half = &a__ / (Atom::num(2) * &b__);
            let denom = Atom::num(2).sqrt() * &b__ * (-&d__ * x_.pow(2)).sqrt();
            rubi_simp(&(x_ * &ab_half.cos() * rubi_cos_integral(&argument / (Atom::num(2) * &b__)) / &denom), x_)
                    + rubi_simp(&(x_ * ab_half.sin() * rubi_sin_integral(argument / (Atom::num(2) * &b__)) / denom), x_)
        },
    ));
}

fn push_rules_rule_5317(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, d__, x_);
    rules.push(rubi_rule!(
        order: 5317,
        source: "Int[1/(a_.+b_.*ArcCos[-1+d_.*x_^2]),x_Symbol] :=
          x*Sin[a/(2*b)]*CosIntegral[(a+b*ArcCos[-1+d*x^2])/(2*b)]/(Sqrt[2]*b*Sqrt[d*x^2]) -
          x*Cos[a/(2*b)]*SinIntegral[(a+b*ArcCos[-1+d*x^2])/(2*b)]/(Sqrt[2]*b*Sqrt[d*x^2]) /;
        FreeQ[{a,b,d},x]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: Atom::num(1) / (a__ + b__ * (-Atom::num(1) + d__ * x_.pow(2)).acos()),
        with: [a__, b__, d__, x_],
        optional: [a__, b__, d__],
        when: { freeq!([a__, b__, d__], x_) },
        rhs: {
            let argument = &a__ + &b__ * (-Atom::num(1) + &d__ * x_.pow(2)).acos();
            let ab_half = &a__ / (Atom::num(2) * &b__);
            let denom = Atom::num(2).sqrt() * &b__ * (&d__ * x_.pow(2)).sqrt();
            rubi_simp(&(x_ * &ab_half.sin() * rubi_cos_integral(&argument / (Atom::num(2) * &b__)) / &denom), x_)
                    - rubi_simp(&(x_ * ab_half.cos() * rubi_sin_integral(argument / (Atom::num(2) * &b__)) / denom), x_)
        },
    ));
}

fn push_rules_rule_5318(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 5318,
        source: "Int[1/Sqrt[a_.+b_.*ArcSin[c_+d_.*x_^2]],x_Symbol] :=
          -Sqrt[Pi]*x*(Cos[a/(2*b)]-c*Sin[a/(2*b)])*FresnelC[1/(Sqrt[b*c]*Sqrt[Pi])*Sqrt[a+b*ArcSin[c+d*x^2]]]/
            (Sqrt[b*c]*(Cos[ArcSin[c+d*x^2]/2]-c*Sin[ArcSin[c+d*x^2]/2])) -
          Sqrt[Pi]*x*(Cos[a/(2*b)]+c*Sin[a/(2*b)])*FresnelS[(1/(Sqrt[b*c]*Sqrt[Pi]))*Sqrt[a+b*ArcSin[c+d*x^2]]]/
            (Sqrt[b*c]*(Cos[ArcSin[c+d*x^2]/2]-c*Sin[ArcSin[c+d*x^2]/2])) /;
        FreeQ[{a,b,c,d},x] && EqQ[c^2,1]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: Atom::num(1) / (a__ + b__ * (c__ + d__ * x_.pow(2)).asin()).sqrt(),
        with: [a__, b__, c__, d__, x_],
        optional: [a__, b__, d__],
        when: { freeq!([a__, b__, c__, d__], x_) && eqq!(c__.pow(2), 1) },
        rhs: {
            let asin = (&c__ + &d__ * x_.pow(2)).asin();
            let argument = &a__ + &b__ * &asin;
            let ab_half = &a__ / (Atom::num(2) * &b__);
            let half_asin = asin / Atom::num(2);
            let bc_sqrt = (&b__ * &c__).sqrt();
            let fresnel_arg = &argument.sqrt() / (&bc_sqrt * Atom::var(Symbol::PI).sqrt());
            let denom = &bc_sqrt * (&half_asin.cos() - &c__ * half_asin.sin());
            rubi_simp(&(-Atom::var(Symbol::PI).sqrt()
                    * x_
                    * (&ab_half.cos() - &c__ * &ab_half.sin())
                    * rubi_fresnel_c(&fresnel_arg)
                    / &denom), x_)
                    - rubi_simp(&(Atom::var(Symbol::PI).sqrt()
                        * x_
                        * (&ab_half.cos() + &c__ * ab_half.sin())
                        * rubi_fresnel_s(fresnel_arg)
                        / denom), x_)
        },
    ));
}

fn push_rules_rule_5319(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, d__, x_);
    rules.push(rubi_rule!(
        order: 5319,
        source: "Int[1/Sqrt[a_.+b_.*ArcCos[1+d_.*x_^2]],x_Symbol] :=
          -2*Sqrt[Pi/b]*Cos[a/(2*b)]*Sin[ArcCos[1+d*x^2]/2]*FresnelC[Sqrt[1/(Pi*b)]*Sqrt[a+b*ArcCos[1+d*x^2]]]/(d*x) -
           2*Sqrt[Pi/b]*Sin[a/(2*b)]*Sin[ArcCos[1+d*x^2]/2]*FresnelS[Sqrt[1/(Pi*b)]*Sqrt[a+b*ArcCos[1+d*x^2]]]/(d*x) /;
        FreeQ[{a,b,d},x]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: Atom::num(1) / (a__ + b__ * (Atom::num(1) + d__ * x_.pow(2)).acos()).sqrt(),
        with: [a__, b__, d__, x_],
        optional: [a__, b__, d__],
        when: { freeq!([a__, b__, d__], x_) },
        rhs: {
            let acos = (Atom::num(1) + &d__ * x_.pow(2)).acos();
            let argument = &a__ + &b__ * &acos;
            let ab_half = &a__ / (Atom::num(2) * &b__);
            let half_acos = acos / Atom::num(2);
            let scale = (Atom::var(Symbol::PI) / &b__).sqrt();
            let fresnel_arg = (Atom::num(1) / (Atom::var(Symbol::PI) * &b__)).sqrt() * argument.sqrt();
            rubi_simp(&(-Atom::num(2)
                    * &scale
                    * &ab_half.cos()
                    * &half_acos.sin()
                    * rubi_fresnel_c(&fresnel_arg)
                    / (&d__ * x_)), x_)
                    - rubi_simp(&(Atom::num(2)
                        * scale
                        * ab_half.sin()
                        * half_acos.sin()
                        * rubi_fresnel_s(fresnel_arg)
                        / (&d__ * x_)), x_)
        },
    ));
}

fn push_rules_rule_5320(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, d__, x_);
    rules.push(rubi_rule!(
        order: 5320,
        source: "Int[1/Sqrt[a_.+b_.*ArcCos[-1+d_.*x_^2]],x_Symbol] :=
          2*Sqrt[Pi/b]*Sin[a/(2*b)]*Cos[ArcCos[-1+d*x^2]/2]*FresnelC[Sqrt[1/(Pi*b)]*Sqrt[a+b*ArcCos[-1+d*x^2]]]/(d*x) -
          2*Sqrt[Pi/b]*Cos[a/(2*b)]*Cos[ArcCos[-1+d*x^2]/2]*FresnelS[Sqrt[1/(Pi*b)]*Sqrt[a+b*ArcCos[-1+d*x^2]]]/(d*x) /;
        FreeQ[{a,b,d},x]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: Atom::num(1) / (a__ + b__ * (-Atom::num(1) + d__ * x_.pow(2)).acos()).sqrt(),
        with: [a__, b__, d__, x_],
        optional: [a__, b__, d__],
        when: { freeq!([a__, b__, d__], x_) },
        rhs: {
            let acos = (-Atom::num(1) + &d__ * x_.pow(2)).acos();
            let argument = &a__ + &b__ * &acos;
            let ab_half = &a__ / (Atom::num(2) * &b__);
            let half_acos = acos / Atom::num(2);
            let scale = (Atom::var(Symbol::PI) / &b__).sqrt();
            let fresnel_arg = (Atom::num(1) / (Atom::var(Symbol::PI) * &b__)).sqrt() * argument.sqrt();
            rubi_simp(&(Atom::num(2)
                    * &scale
                    * &ab_half.sin()
                    * &half_acos.cos()
                    * rubi_fresnel_c(&fresnel_arg)
                    / (&d__ * x_)), x_)
                    - rubi_simp(&(Atom::num(2)
                        * scale
                        * ab_half.cos()
                        * half_acos.cos()
                        * rubi_fresnel_s(fresnel_arg)
                        / (&d__ * x_)), x_)
        },
    ));
}

fn push_rules_rule_5321(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 5321,
        source: "Int[1/(a_.+b_.*ArcSin[c_+d_.*x_^2])^(3/2),x_Symbol] :=
          -Sqrt[-2*c*d*x^2-d^2*x^4]/(b*d*x*Sqrt[a+b*ArcSin[c+d*x^2]]) -
          (c/b)^(3/2)*Sqrt[Pi]*x*(Cos[a/(2*b)]+c*Sin[a/(2*b)])*FresnelC[Sqrt[c/(Pi*b)]*Sqrt[a+b*ArcSin[c+d*x^2]]]/
            (Cos[(1/2)*ArcSin[c+d*x^2]]-c*Sin[ArcSin[c+d*x^2]/2]) +
          (c/b)^(3/2)*Sqrt[Pi]*x*(Cos[a/(2*b)]-c*Sin[a/(2*b)])*FresnelS[Sqrt[c/(Pi*b)]*Sqrt[a+b*ArcSin[c+d*x^2]]]/
            (Cos[(1/2)*ArcSin[c+d*x^2]]-c*Sin[ArcSin[c+d*x^2]/2]) /;
        FreeQ[{a,b,c,d},x] && EqQ[c^2,1]",
        desc: "Integration by parts",
        refs: [],
        pattern: Atom::num(1) / (a__ + b__ * (c__ + d__ * x_.pow(2)).asin()).pow(Atom::num(3) / Atom::num(2)),
        with: [a__, b__, c__, d__, x_],
        optional: [a__, b__, d__],
        when: { freeq!([a__, b__, c__, d__], x_) && eqq!(c__.pow(2), 1) },
        rhs: {
            let asin = (&c__ + &d__ * x_.pow(2)).asin();
            let argument = &a__ + &b__ * &asin;
            let ab_half = &a__ / (Atom::num(2) * &b__);
            let half_asin = asin / Atom::num(2);
            let radical = (-Atom::num(2) * &c__ * &d__ * x_.pow(2) - d__.pow(2) * x_.pow(4)).sqrt();
            let denom = &half_asin.cos() - &c__ * half_asin.sin();
            let fresnel_arg = (&c__ / (Atom::var(Symbol::PI) * &b__)).sqrt() * &argument.sqrt();
            let scale = (&c__ / &b__).pow(Atom::num(3) / Atom::num(2)) * Atom::var(Symbol::PI).sqrt() * x_;
            rubi_simp(&(-radical / (&b__ * &d__ * x_ * &argument.sqrt())), x_)
                    - rubi_simp(&(&scale
                        * (&ab_half.cos() + &c__ * &ab_half.sin())
                        * rubi_fresnel_c(&fresnel_arg)
                        / &denom), x_)
                    + rubi_simp(&(scale
                        * (&ab_half.cos() - &c__ * ab_half.sin())
                        * rubi_fresnel_s(fresnel_arg)
                        / denom), x_)
        },
    ));
}

fn push_rules_rule_5322(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, d__, x_);
    rules.push(rubi_rule!(
        order: 5322,
        source: "Int[1/(a_.+b_.*ArcCos[1+d_.*x_^2])^(3/2),x_Symbol] :=
          Sqrt[-2*d*x^2-d^2*x^4]/(b*d*x*Sqrt[a+b*ArcCos[1+d*x^2]]) -
          2*(1/b)^(3/2)*Sqrt[Pi]*Sin[a/(2*b)]*Sin[ArcCos[1+d*x^2]/2]*FresnelC[Sqrt[1/(Pi*b)]*Sqrt[a+b*ArcCos[1+d*x^2]]]/(d*x) +
          2*(1/b)^(3/2)*Sqrt[Pi]*Cos[a/(2*b)]*Sin[ArcCos[1+d*x^2]/2]*FresnelS[Sqrt[1/(Pi*b)]*Sqrt[a+b*ArcCos[1+d*x^2]]]/(d*x) /;
        FreeQ[{a,b,d},x]",
        desc: "Integration by parts",
        refs: [],
        pattern: Atom::num(1) / (a__ + b__ * (Atom::num(1) + d__ * x_.pow(2)).acos()).pow(Atom::num(3) / Atom::num(2)),
        with: [a__, b__, d__, x_],
        optional: [a__, b__, d__],
        when: { freeq!([a__, b__, d__], x_) },
        rhs: {
            let acos = (Atom::num(1) + &d__ * x_.pow(2)).acos();
            let argument = &a__ + &b__ * &acos;
            let ab_half = &a__ / (Atom::num(2) * &b__);
            let half_acos = acos / Atom::num(2);
            let radical = (-Atom::num(2) * &d__ * x_.pow(2) - d__.pow(2) * x_.pow(4)).sqrt();
            let scale = (Atom::num(1) / &b__).pow(Atom::num(3) / Atom::num(2)) * Atom::var(Symbol::PI).sqrt();
            let fresnel_arg = (Atom::num(1) / (Atom::var(Symbol::PI) * &b__)).sqrt() * &argument.sqrt();
            rubi_simp(&(radical / (&b__ * &d__ * x_ * argument.sqrt())), x_)
                    - rubi_simp(&(Atom::num(2)
                        * &scale
                        * &ab_half.sin()
                        * &half_acos.sin()
                        * rubi_fresnel_c(&fresnel_arg)
                        / (&d__ * x_)), x_)
                    + rubi_simp(&(Atom::num(2)
                        * scale
                        * ab_half.cos()
                        * half_acos.sin()
                        * rubi_fresnel_s(fresnel_arg)
                        / (&d__ * x_)), x_)
        },
    ));
}

fn push_rules_rule_5323(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, d__, x_);
    rules.push(rubi_rule!(
        order: 5323,
        source: "Int[1/(a_.+b_.*ArcCos[-1+d_.*x_^2])^(3/2),x_Symbol] :=
          Sqrt[2*d*x^2-d^2*x^4]/(b*d*x*Sqrt[a+b*ArcCos[-1+d*x^2]]) -
          2*(1/b)^(3/2)*Sqrt[Pi]*Cos[a/(2*b)]*Cos[ArcCos[-1+d*x^2]/2]*FresnelC[Sqrt[1/(Pi*b)]*Sqrt[a+b*ArcCos[-1+d*x^2]]]/(d*x) -
          2*(1/b)^(3/2)*Sqrt[Pi]*Sin[a/(2*b)]*Cos[ArcCos[-1+d*x^2]/2]*FresnelS[Sqrt[1/(Pi*b)]*Sqrt[a+b*ArcCos[-1+d*x^2]]]/(d*x) /;
        FreeQ[{a,b,d},x]",
        desc: "Integration by parts",
        refs: [],
        pattern: Atom::num(1) / (a__ + b__ * (-Atom::num(1) + d__ * x_.pow(2)).acos()).pow(Atom::num(3) / Atom::num(2)),
        with: [a__, b__, d__, x_],
        optional: [a__, b__, d__],
        when: { freeq!([a__, b__, d__], x_) },
        rhs: {
            let acos = (-Atom::num(1) + &d__ * x_.pow(2)).acos();
            let argument = &a__ + &b__ * &acos;
            let ab_half = &a__ / (Atom::num(2) * &b__);
            let half_acos = acos / Atom::num(2);
            let radical = (Atom::num(2) * &d__ * x_.pow(2) - d__.pow(2) * x_.pow(4)).sqrt();
            let scale = (Atom::num(1) / &b__).pow(Atom::num(3) / Atom::num(2)) * Atom::var(Symbol::PI).sqrt();
            let fresnel_arg = (Atom::num(1) / (Atom::var(Symbol::PI) * &b__)).sqrt() * &argument.sqrt();
            rubi_simp(&(radical / (&b__ * &d__ * x_ * argument.sqrt())), x_)
                    - rubi_simp(&(Atom::num(2)
                        * &scale
                        * &ab_half.cos()
                        * &half_acos.cos()
                        * rubi_fresnel_c(&fresnel_arg)
                        / (&d__ * x_)), x_)
                    - rubi_simp(&(Atom::num(2)
                        * scale
                        * ab_half.sin()
                        * half_acos.cos()
                        * rubi_fresnel_s(fresnel_arg)
                        / (&d__ * x_)), x_)
        },
    ));
}

fn push_rules_rule_5324(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 5324,
        source: "Int[1/(a_.+b_.*ArcSin[c_+d_.*x_^2])^2,x_Symbol] :=
          -Sqrt[-2*c*d*x^2-d^2*x^4]/(2*b*d*x*(a+b*ArcSin[c+d*x^2])) -
          x*(Cos[a/(2*b)]+c*Sin[a/(2*b)])*CosIntegral[(c/(2*b))*(a+b*ArcSin[c+d*x^2])]/
            (4*b^2*(Cos[ArcSin[c+d*x^2]/2]-c*Sin[ArcSin[c+d*x^2]/2])) +
          x*(Cos[a/(2*b)]-c*Sin[a/(2*b)])*SinIntegral[(c/(2*b))*(a+b*ArcSin[c+d*x^2])]/
            (4*b^2*(Cos[ArcSin[c+d*x^2]/2]-c*Sin[ArcSin[c+d*x^2]/2])) /;
        FreeQ[{a,b,c,d},x] && EqQ[c^2,1]",
        desc: "Integration by parts",
        refs: [],
        pattern: Atom::num(1) / (a__ + b__ * (c__ + d__ * x_.pow(2)).asin()).pow(2),
        with: [a__, b__, c__, d__, x_],
        optional: [a__, b__, d__],
        when: { freeq!([a__, b__, c__, d__], x_) && eqq!(c__.pow(2), 1) },
        rhs: {
            let asin = (&c__ + &d__ * x_.pow(2)).asin();
            let argument = &a__ + &b__ * &asin;
            let ab_half = &a__ / (Atom::num(2) * &b__);
            let half_asin = asin / Atom::num(2);
            let radical = (-Atom::num(2) * &c__ * &d__ * x_.pow(2) - d__.pow(2) * x_.pow(4)).sqrt();
            let denom = Atom::num(4) * b__.pow(2) * (&half_asin.cos() - &c__ * half_asin.sin());
            rubi_simp(&(-radical / (Atom::num(2) * &b__ * &d__ * x_ * &argument)), x_)
                    - rubi_simp(&(x_
                        * (&ab_half.cos() + &c__ * &ab_half.sin())
                        * rubi_cos_integral(&c__ * &argument / (Atom::num(2) * &b__))
                        / &denom), x_)
                    + rubi_simp(&(x_
                        * (&ab_half.cos() - &c__ * ab_half.sin())
                        * rubi_sin_integral(&c__ * argument / (Atom::num(2) * &b__))
                        / denom), x_)
        },
    ));
}

fn push_rules_rule_5325(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, d__, x_);
    rules.push(rubi_rule!(
        order: 5325,
        source: "Int[1/(a_.+b_.*ArcCos[1+d_.*x_^2])^2,x_Symbol] :=
          Sqrt[-2*d*x^2-d^2*x^4]/(2*b*d*x*(a+b*ArcCos[1+d*x^2])) +
          x*Sin[a/(2*b)]*CosIntegral[(a+b*ArcCos[1+d*x^2])/(2*b)]/(2*Sqrt[2]*b^2*Sqrt[(-d)*x^2]) -
          x*Cos[a/(2*b)]*SinIntegral[(a+b*ArcCos[1+d*x^2])/(2*b)]/(2*Sqrt[2]*b^2*Sqrt[(-d)*x^2]) /;
        FreeQ[{a,b,d},x]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: Atom::num(1) / (a__ + b__ * (Atom::num(1) + d__ * x_.pow(2)).acos()).pow(2),
        with: [a__, b__, d__, x_],
        optional: [a__, b__, d__],
        when: { freeq!([a__, b__, d__], x_) },
        rhs: {
            let argument = &a__ + &b__ * (Atom::num(1) + &d__ * x_.pow(2)).acos();
            let ab_half = &a__ / (Atom::num(2) * &b__);
            let radical = (-Atom::num(2) * &d__ * x_.pow(2) - d__.pow(2) * x_.pow(4)).sqrt();
            let denom = Atom::num(2) * Atom::num(2).sqrt() * b__.pow(2) * (-&d__ * x_.pow(2)).sqrt();
            rubi_simp(&(radical / (Atom::num(2) * &b__ * &d__ * x_ * &argument)), x_)
                    + rubi_simp(&(x_ * &ab_half.sin() * rubi_cos_integral(&argument / (Atom::num(2) * &b__)) / &denom), x_)
                    - rubi_simp(&(x_ * ab_half.cos() * rubi_sin_integral(argument / (Atom::num(2) * &b__)) / denom), x_)
        },
    ));
}

fn push_rules_rule_5326(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, d__, x_);
    rules.push(rubi_rule!(
        order: 5326,
        source: "Int[1/(a_.+b_.*ArcCos[-1+d_.*x_^2])^2,x_Symbol] :=
          Sqrt[2*d*x^2-d^2*x^4]/(2*b*d*x*(a+b*ArcCos[-1+d*x^2])) -
          x*Cos[a/(2*b)]*CosIntegral[(a+b*ArcCos[-1+d*x^2])/(2*b)]/(2*Sqrt[2]*b^2*Sqrt[d*x^2]) -
          x*Sin[a/(2*b)]*SinIntegral[(a+b*ArcCos[-1+d*x^2])/(2*b)]/(2*Sqrt[2]*b^2*Sqrt[d*x^2]) /;
        FreeQ[{a,b,d},x]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: Atom::num(1) / (a__ + b__ * (-Atom::num(1) + d__ * x_.pow(2)).acos()).pow(2),
        with: [a__, b__, d__, x_],
        optional: [a__, b__, d__],
        when: { freeq!([a__, b__, d__], x_) },
        rhs: {
            let argument = &a__ + &b__ * (-Atom::num(1) + &d__ * x_.pow(2)).acos();
            let ab_half = &a__ / (Atom::num(2) * &b__);
            let radical = (Atom::num(2) * &d__ * x_.pow(2) - d__.pow(2) * x_.pow(4)).sqrt();
            let denom = Atom::num(2) * Atom::num(2).sqrt() * b__.pow(2) * (&d__ * x_.pow(2)).sqrt();
            rubi_simp(&(radical / (Atom::num(2) * &b__ * &d__ * x_ * &argument)), x_)
                    - rubi_simp(&(x_ * &ab_half.cos() * rubi_cos_integral(&argument / (Atom::num(2) * &b__)) / &denom), x_)
                    - rubi_simp(&(x_ * ab_half.sin() * rubi_sin_integral(argument / (Atom::num(2) * &b__)) / denom), x_)
        },
    ));
}

fn push_rules_rule_5327(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 5327,
        source: "Int[(a_.+b_.*ArcSin[c_+d_.*x_^2])^n_,x_Symbol] :=
          x*(a+b*ArcSin[c+d*x^2])^(n+2)/(4*b^2*(n+1)*(n+2)) +
          Sqrt[-2*c*d*x^2-d^2*x^4]*(a+b*ArcSin[c+d*x^2])^(n+1)/(2*b*d*(n+1)*x) -
          1/(4*b^2*(n+1)*(n+2)) \\[Star] Int[(a+b*ArcSin[c+d*x^2])^(n+2),x] /;
        FreeQ[{a,b,c,d},x] && EqQ[c^2,1] && LtQ[n,-1] && NeQ[n,-2]",
        desc: "Inverted integration by parts twice",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, n_, x_],
        optional: [a__, b__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && eqq!(c__.pow(2), 1)
                && ltq!(n_, -1)
                && neq!(n_, -2)
        },
        rhs: {
            let argument = &a__ + &b__ * (&c__ + &d__ * x_.pow(2)).asin();
            let radical = (-Atom::num(2) * &c__ * &d__ * x_.pow(2) - d__.pow(2) * x_.pow(4)).sqrt();
            let recursive = argument.pow(&n_ + Atom::num(2));
            rubi_simp(&(x_ * argument.pow(&n_ + Atom::num(2))
                    / (Atom::num(4) * b__.pow(2) * (&n_ + Atom::num(1)) * (&n_ + Atom::num(2)))), x_)
                    + rubi_simp(&(radical * argument.pow(&n_ + Atom::num(1)) / (Atom::num(2) * &b__ * &d__ * (&n_ + Atom::num(1)) * x_)), x_)
                    - rubi_star(Atom::num(1)
                            / (Atom::num(4)
                                * b__.pow(2)
                                * (&n_ + Atom::num(1))
                                * (&n_ + Atom::num(2))), rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_5328(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 5328,
        source: "Int[(a_.+b_.*ArcCos[c_+d_.*x_^2])^n_,x_Symbol] :=
          x*(a+b*ArcCos[c+d*x^2])^(n+2)/(4*b^2*(n+1)*(n+2)) -
          Sqrt[-2*c*d*x^2-d^2*x^4]*(a+b*ArcCos[c+d*x^2])^(n+1)/(2*b*d*(n+1)*x) -
          1/(4*b^2*(n+1)*(n+2)) \\[Star] Int[(a+b*ArcCos[c+d*x^2])^(n+2),x] /;
        FreeQ[{a,b,c,d},x] && EqQ[c^2,1] && LtQ[n,-1] && NeQ[n,-2]",
        desc: "Inverted integration by parts twice",
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
            let argument = &a__ + &b__ * (&c__ + &d__ * x_.pow(2)).acos();
            let radical = (-Atom::num(2) * &c__ * &d__ * x_.pow(2) - d__.pow(2) * x_.pow(4)).sqrt();
            let recursive = argument.pow(&n_ + Atom::num(2));
            rubi_simp(&(x_ * argument.pow(&n_ + Atom::num(2))
                    / (Atom::num(4) * b__.pow(2) * (&n_ + Atom::num(1)) * (&n_ + Atom::num(2)))), x_)
                    - rubi_simp(&(radical * argument.pow(&n_ + Atom::num(1)) / (Atom::num(2) * &b__ * &d__ * (&n_ + Atom::num(1)) * x_)), x_)
                    - rubi_star(Atom::num(1)
                            / (Atom::num(4)
                                * b__.pow(2)
                                * (&n_ + Atom::num(1))
                                * (&n_ + Atom::num(2))), rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_5329(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5329,
        source: "Int[ArcSin[a_.*x_^p_]^n_./x_,x_Symbol] :=
          1/p \\[Star] Subst[Int[x^n*Cot[x],x],x,ArcSin[a*x^p]] /;
        FreeQ[{a,p},x] && IGtQ[n,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (a__ * x_.pow(p_)).asin().pow(n_) / x_,
        with: [a__, p_, n_, x_],
        optional: [a__, n_],
        when: { freeq!([a__, p_], x_) && igtq!(n_, 0) },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let payload = sub_atom.pow(&n_) * sub_atom.cot();
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            rubi_star(Atom::num(1) / &p_, rubi_subst(&primitive, substitution_symbol, (&a__ * x_.pow(&p_)).asin()))
        },
    ));
}

fn push_rules_rule_5330(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5330,
        source: "Int[ArcCos[a_.*x_^p_]^n_./x_,x_Symbol] :=
          -1/p \\[Star] Subst[Int[x^n*Tan[x],x],x,ArcCos[a*x^p]] /;
        FreeQ[{a,p},x] && IGtQ[n,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (a__ * x_.pow(p_)).acos().pow(n_) / x_,
        with: [a__, p_, n_, x_],
        optional: [a__, n_],
        when: { freeq!([a__, p_], x_) && igtq!(n_, 0) },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let payload = sub_atom.pow(&n_) * sub_atom.tan();
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            rubi_star(-Atom::num(1) / &p_, rubi_subst(&primitive, substitution_symbol, (&a__ * x_.pow(&p_)).acos()))
        },
    ));
}

fn push_rules_rule_5331(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, m_, n_, u_, x_);
    rules.push(rubi_rule!(
        order: 5331,
        source: "Int[u_.*ArcSin[c_./(a_.+b_.*x_^n_.)]^m_.,x_Symbol] :=
          Int[u*ArcCsc[a/c+b*x^n/c]^m,x] /;
        FreeQ[{a,b,c,n,m},x]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: Atom::var(u_) * (c__ / (a__ + b__ * x_.pow(n_))).asin().pow(m_),
        with: [u_, c__, a__, b__, n_, m_, x_],
        optional: [u_, c__, a__, b__, n_, m_],
        when: { freeq!([a__, b__, c__, n_, m_], x_) },
        rhs: {
            let transformed = u_ * (&a__ / &c__ + &b__ * x_.pow(&n_) / &c__).acsc().pow(&m_);
            rubi_rhs_int(&transformed, x_)
        },
    ));
}

fn push_rules_rule_5332(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, m_, n_, u_, x_);
    rules.push(rubi_rule!(
        order: 5332,
        source: "Int[u_.*ArcCos[c_./(a_.+b_.*x_^n_.)]^m_.,x_Symbol] :=
          Int[u*ArcSec[a/c+b*x^n/c]^m,x] /;
        FreeQ[{a,b,c,n,m},x]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: Atom::var(u_) * (c__ / (a__ + b__ * x_.pow(n_))).acos().pow(m_),
        with: [u_, c__, a__, b__, n_, m_, x_],
        optional: [u_, c__, a__, b__, n_, m_],
        when: { freeq!([a__, b__, c__, n_, m_], x_) },
        rhs: {
            let transformed = u_ * (&a__ / &c__ + &b__ * x_.pow(&n_) / &c__).asec().pow(&m_);
            rubi_rhs_int(&transformed, x_)
        },
    ));
}

fn push_rules_rule_5333(rules: &mut Vec<RubiRule>) {
    rubi_symb!(b__, n_, x_);
    rules.push(rubi_rule!(
        order: 5333,
        source: "Int[ArcSin[Sqrt[1+b_.*x_^2]]^n_./Sqrt[1+b_.*x_^2],x_Symbol] :=
          Sqrt[-b*x^2]/(b*x) \\[Star] Subst[Int[ArcSin[x]^n/Sqrt[1-x^2],x],x,Sqrt[1+b*x^2]] /;
        FreeQ[{b,n},x]",
        desc: "Piecewise constant extraction and integration by substitution",
        refs: [],
        pattern: (Atom::num(1) + b__ * x_.pow(2)).sqrt().asin().pow(n_) / (Atom::num(1) + b__ * x_.pow(2)).sqrt(),
        with: [b__, n_, x_],
        optional: [b__, n_],
        when: { freeq!([b__, n_], x_) },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let payload = sub_atom.asin().pow(&n_) / (Atom::num(1) - sub_atom.pow(2)).sqrt();
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            rubi_star((-&b__ * x_.pow(2)).sqrt() / (&b__ * x_), rubi_subst(
                    &primitive,
                    substitution_symbol,
                    (Atom::num(1) + &b__ * x_.pow(2)).sqrt(),
                ))
        },
    ));
}

fn push_rules_rule_5334(rules: &mut Vec<RubiRule>) {
    rubi_symb!(b__, n_, x_);
    rules.push(rubi_rule!(
        order: 5334,
        source: "Int[ArcCos[Sqrt[1+b_.*x_^2]]^n_./Sqrt[1+b_.*x_^2],x_Symbol] :=
          Sqrt[-b*x^2]/(b*x) \\[Star] Subst[Int[ArcCos[x]^n/Sqrt[1-x^2],x],x,Sqrt[1+b*x^2]] /;
        FreeQ[{b,n},x]",
        desc: "Piecewise constant extraction and integration by substitution",
        refs: [],
        pattern: (Atom::num(1) + b__ * x_.pow(2)).sqrt().acos().pow(n_) / (Atom::num(1) + b__ * x_.pow(2)).sqrt(),
        with: [b__, n_, x_],
        optional: [b__, n_],
        when: { freeq!([b__, n_], x_) },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let payload = sub_atom.acos().pow(&n_) / (Atom::num(1) - sub_atom.pow(2)).sqrt();
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            rubi_star((-&b__ * x_.pow(2)).sqrt() / (&b__ * x_), rubi_subst(
                    &primitive,
                    substitution_symbol,
                    (Atom::num(1) + &b__ * x_.pow(2)).sqrt(),
                ))
        },
    ));
}

fn push_rules_rule_5335(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, f__, n_, u__, x_);
    rules.push(rubi_rule!(
        order: 5335,
        source: "Int[u_.*f_^(c_.*ArcSin[a_.+b_.*x_]^n_.),x_Symbol] :=
          1/b \\[Star] Subst[Int[ReplaceAll[u,x->-a/b+Sin[x]/b]*f^(c*x^n)*Cos[x],x],x,ArcSin[a+b*x]] /;
        FreeQ[{a,b,c,f},x] && IGtQ[n,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: Atom::var(u__) * f__.pow(c__ * (a__ + b__ * x_).asin().pow(n_)),
        with: [u__, f__, c__, a__, b__, n_, x_],
        optional: [u__, c__, a__, b__, n_],
        when: { freeq!([a__, b__, c__, f__], x_) && igtq!(n_, 0) },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let replaced = rubi_replace_all(&u__, x_, -&a__ / &b__ + &sub_atom.sin() / &b__);
            let payload = replaced * f__.pow(&c__ * sub_atom.pow(&n_)) * sub_atom.cos();
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            rubi_star(Atom::num(1) / &b__, rubi_subst(&primitive, substitution_symbol, (&a__ + &b__ * x_).asin()))
        },
    ));
}

fn push_rules_rule_5336(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, f__, n_, u__, x_);
    rules.push(rubi_rule!(
        order: 5336,
        source: "Int[u_.*f_^(c_.*ArcCos[a_.+b_.*x_]^n_.),x_Symbol] :=
          -1/b \\[Star] Subst[Int[ReplaceAll[u,x->-a/b+Cos[x]/b]*f^(c*x^n)*Sin[x],x],x,ArcCos[a+b*x]] /;
        FreeQ[{a,b,c,f},x] && IGtQ[n,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: Atom::var(u__) * f__.pow(c__ * (a__ + b__ * x_).acos().pow(n_)),
        with: [u__, f__, c__, a__, b__, n_, x_],
        optional: [u__, c__, a__, b__, n_],
        when: { freeq!([a__, b__, c__, f__], x_) && igtq!(n_, 0) },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let replaced = rubi_replace_all(&u__, x_, -&a__ / &b__ + &sub_atom.cos() / &b__);
            let payload = replaced * f__.pow(&c__ * sub_atom.pow(&n_)) * sub_atom.sin();
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            rubi_star(-Atom::num(1) / &b__, rubi_subst(&primitive, substitution_symbol, (&a__ + &b__ * x_).acos()))
        },
    ));
}

fn push_rules_rule_5337(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 5337,
        source: "Int[ArcSin[a_.*x_^2+b_.*Sqrt[c_+d_.*x_^2]],x_Symbol] :=
          x*ArcSin[a*x^2+b*Sqrt[c+d*x^2]] -
          x*Sqrt[b^2*d+a^2*x^2+2*a*b*Sqrt[c+d*x^2]]/Sqrt[(-x^2)*(b^2*d+a^2*x^2+2*a*b*Sqrt[c+d*x^2])] \\[Star]
            Int[x*(b*d+2*a*Sqrt[c+d*x^2])/(Sqrt[c+d*x^2]*Sqrt[b^2*d +a^2*x^2+2*a*b*Sqrt[c+d*x^2]]),x] /;
        FreeQ[{a,b,c,d},x] && EqQ[b^2*c,1]",
        desc: "Integration by parts and piecewise constant extraction",
        refs: [],
        pattern: (a__ * x_.pow(2) + b__ * (c__ + d__ * x_.pow(2)).sqrt()).asin(),
        with: [a__, b__, c__, d__, x_],
        optional: [a__, b__, d__],
        when: { freeq!([a__, b__, c__, d__], x_) && eqq!(b__.pow(2) * &c__, 1) },
        rhs: {
            let sqrt_quadratic = (&c__ + &d__ * x_.pow(2)).sqrt();
            let argument = &a__ * x_.pow(2) + &b__ * &sqrt_quadratic;
            let radical_payload = b__.pow(2) * &d__ + a__.pow(2) * x_.pow(2) + Atom::num(2) * &a__ * &b__ * &sqrt_quadratic;
            let recursive = x_
                * (&b__ * &d__ + Atom::num(2) * &a__ * &sqrt_quadratic)
                / (&sqrt_quadratic * &radical_payload.sqrt());
            rubi_simp(&(x_ * argument.asin()), x_)
                    - rubi_star(x_ * &radical_payload.sqrt()
                            / ((Atom::num(-1) * x_.pow(2)) * radical_payload).sqrt(), rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_5338(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 5338,
        source: "Int[ArcCos[a_.*x_^2+b_.*Sqrt[c_+d_.*x_^2]],x_Symbol] :=
          x*ArcCos[a*x^2+b*Sqrt[c+d*x^2]] +
          x*Sqrt[b^2*d+a^2*x^2+2*a*b*Sqrt[c+d*x^2]]/Sqrt[(-x^2)*(b^2*d+a^2*x^2+2*a*b*Sqrt[c+d*x^2])] \\[Star]
            Int[x*(b*d+2*a*Sqrt[c+d*x^2])/(Sqrt[c+d*x^2]*Sqrt[b^2*d+a^2*x^2+2*a*b*Sqrt[c+d*x^2]]),x] /;
        FreeQ[{a,b,c,d},x] && EqQ[b^2*c,1]",
        desc: "Integration by parts and piecewise constant extraction",
        refs: [],
        pattern: (a__ * x_.pow(2) + b__ * (c__ + d__ * x_.pow(2)).sqrt()).acos(),
        with: [a__, b__, c__, d__, x_],
        optional: [a__, b__, d__],
        when: { freeq!([a__, b__, c__, d__], x_) && eqq!(b__.pow(2) * &c__, 1) },
        rhs: {
            let sqrt_quadratic = (&c__ + &d__ * x_.pow(2)).sqrt();
            let argument = &a__ * x_.pow(2) + &b__ * &sqrt_quadratic;
            let radical_payload = b__.pow(2) * &d__ + a__.pow(2) * x_.pow(2) + Atom::num(2) * &a__ * &b__ * &sqrt_quadratic;
            let recursive = x_
                * (&b__ * &d__ + Atom::num(2) * &a__ * &sqrt_quadratic)
                / (&sqrt_quadratic * &radical_payload.sqrt());
            rubi_simp(&(x_ * argument.acos()), x_)
                    + rubi_star(x_ * &radical_payload.sqrt()
                            / ((Atom::num(-1) * x_.pow(2)) * radical_payload).sqrt(), rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_5339(rules: &mut Vec<RubiRule>) {
    rubi_symb!(u_);
    rules.push(rubi_rule!(
        order: 5339,
        source: "Int[ArcSin[u_],x_Symbol] :=
          x*ArcSin[u] -
          Int[SimplifyIntegrand[x*D[u,x]/Sqrt[1-u^2],x],x] /;
        InverseFunctionFreeQ[u,x] && Not[FunctionOfExponentialQ[u,x]]",
        desc: "Integration by parts",
        refs: [],
        pattern: Atom::var(u_).asin(),
        with: [u_, x_],
        when: { rubi_inverse_function_free_q(&u_, x_) && !rubi_function_of_exponential_q(u_.as_view(), x_) },
        rhs: {
            let recursive =
                rubi_simplify_integrand(&(x_ * u_.derivative(x_) / (Atom::num(1) - u_.pow(2)).sqrt()), x_);
            rubi_simp(&(x_ * u_.asin()), x_) - rubi_rhs_int(&recursive, x_)
        },
    ));
}

fn push_rules_rule_5340(rules: &mut Vec<RubiRule>) {
    rubi_symb!(u_);
    rules.push(rubi_rule!(
        order: 5340,
        source: "Int[ArcCos[u_],x_Symbol] :=
          x*ArcCos[u] +
          Int[SimplifyIntegrand[x*D[u,x]/Sqrt[1-u^2],x],x] /;
        InverseFunctionFreeQ[u,x] && Not[FunctionOfExponentialQ[u,x]]",
        desc: "Integration by parts",
        refs: [],
        pattern: Atom::var(u_).acos(),
        with: [u_, x_],
        when: { rubi_inverse_function_free_q(&u_, x_) && !rubi_function_of_exponential_q(u_.as_view(), x_) },
        rhs: {
            let recursive =
                rubi_simplify_integrand(&(x_ * u_.derivative(x_) / (Atom::num(1) - u_.pow(2)).sqrt()), x_);
            rubi_simp(&(x_ * u_.acos()), x_) + rubi_rhs_int(&recursive, x_)
        },
    ));
}

fn push_rules_rule_5341(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, u_, x_);
    rules.push(rubi_rule!(
        order: 5341,
        source: "Int[(c_.+d_.*x_)^m_.*(a_.+b_.*ArcSin[u_]),x_Symbol] :=
          (c+d*x)^(m+1)*(a+b*ArcSin[u])/(d*(m+1)) -
          b/(d*(m+1)) \\[Star] Int[SimplifyIntegrand[(c+d*x)^(m+1)*D[u,x]/Sqrt[1-u^2],x],x] /;
        FreeQ[{a,b,c,d,m},x] && NeQ[m,-1] && InverseFunctionFreeQ[u,x] && Not[FunctionOfQ[(c+d*x)^(m+1),u,x]] && Not[FunctionOfExponentialQ[u,x]]",
        desc: "Integration by parts",
        refs: [],
        pattern: (c__ + d__ * x_).pow(m_) * (a__ + b__ * Atom::var(u_).asin()),
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
            let argument = &a__ + &b__ * u_.asin();
            let recursive = rubi_simplify_integrand(
                &(linear.pow(&m_ + Atom::num(1)) * u_.derivative(x_) / (Atom::num(1) - u_.pow(2)).sqrt()),
                x_,
            );
            rubi_simp(&(linear.pow(&m_ + Atom::num(1)) * argument / (&d__ * (&m_ + Atom::num(1)))), x_)
                    - rubi_star(&b__ / (&d__ * (&m_ + Atom::num(1))), rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_5342(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, u_, x_);
    rules.push(rubi_rule!(
        order: 5342,
        source: "Int[(c_.+d_.*x_)^m_.*(a_.+b_.*ArcCos[u_]),x_Symbol] :=
          (c+d*x)^(m+1)*(a+b*ArcCos[u])/(d*(m+1)) +
          b/(d*(m+1)) \\[Star] Int[SimplifyIntegrand[(c+d*x)^(m+1)*D[u,x]/Sqrt[1-u^2],x],x] /;
        FreeQ[{a,b,c,d,m},x] && NeQ[m,-1] && InverseFunctionFreeQ[u,x] && Not[FunctionOfQ[(c+d*x)^(m+1),u,x]] && Not[FunctionOfExponentialQ[u,x]]",
        desc: "Integration by parts",
        refs: [],
        pattern: (c__ + d__ * x_).pow(m_) * (a__ + b__ * Atom::var(u_).acos()),
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
            let argument = &a__ + &b__ * u_.acos();
            let recursive = rubi_simplify_integrand(
                &(linear.pow(&m_ + Atom::num(1)) * u_.derivative(x_) / (Atom::num(1) - u_.pow(2)).sqrt()),
                x_,
            );
            rubi_simp(&(linear.pow(&m_ + Atom::num(1)) * argument / (&d__ * (&m_ + Atom::num(1)))), x_)
                    + rubi_star(&b__ / (&d__ * (&m_ + Atom::num(1))), rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_5343(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, u_, v_);
    rules.push(rubi_rule!(
        order: 5343,
        source: "Int[v_*(a_.+b_.*ArcSin[u_]),x_Symbol] :=
          With[{w=IntHide[v,x]},
          (a+b*ArcSin[u]) \\[Star] w -
          b \\[Star] Int[SimplifyIntegrand[w*D[u,x]/Sqrt[1-u^2],x],x] /;
         InverseFunctionFreeQ[w,x]] /;
        FreeQ[{a,b},x] && InverseFunctionFreeQ[u,x] && Not[MatchQ[v, (c_.+d_.*x)^m_. /; FreeQ[{c,d,m},x]]]",
        desc: "Integration by parts",
        refs: [],
        pattern: Atom::var(v_) * (a__ + b__ * Atom::var(u_).asin()),
        with: [v_, a__, b__, u_, x_],
        optional: [a__, b__],
        when: {
            freeq!([a__, b__], x_)
                && rubi_inverse_function_free_q(&u_, x_)
                && !rubi_match_optional_multiplier_linear_power_q(&v_, x_)
                && rubi_int_hide_inverse_function_free_q(&v_, x_)
        },
        rhs: {
            let v_int = rubi_int_hide(&v_, x_).rubi_rhs();
            let argument = &a__ + &b__ * u_.asin();
            let recursive =
                rubi_simplify_integrand(&(&v_int * u_.derivative(x_) / (Atom::num(1) - u_.pow(2)).sqrt()), x_);
            rubi_star(argument, v_int) - rubi_star(b__, rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_5344(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, u_, v_);
    rules.push(rubi_rule!(
        order: 5344,
        source: "Int[v_*(a_.+b_.*ArcCos[u_]),x_Symbol] :=
          With[{w=IntHide[v,x]},
          (a+b*ArcCos[u]) \\[Star] w +
          b \\[Star] Int[SimplifyIntegrand[w*D[u,x]/Sqrt[1-u^2],x],x] /;
         InverseFunctionFreeQ[w,x]] /;
        FreeQ[{a,b},x] && InverseFunctionFreeQ[u,x] && Not[MatchQ[v, (c_.+d_.*x)^m_. /; FreeQ[{c,d,m},x]]]",
        desc: "Integration by parts",
        refs: [],
        pattern: Atom::var(v_) * (a__ + b__ * Atom::var(u_).acos()),
        with: [v_, a__, b__, u_, x_],
        optional: [a__, b__],
        when: {
            freeq!([a__, b__], x_)
                && rubi_inverse_function_free_q(&u_, x_)
                && !rubi_match_optional_multiplier_linear_power_q(&v_, x_)
                && rubi_int_hide_inverse_function_free_q(&v_, x_)
        },
        rhs: {
            let v_int = rubi_int_hide(&v_, x_).rubi_rhs();
            let argument = &a__ + &b__ * u_.acos();
            let recursive =
                rubi_simplify_integrand(&(&v_int * u_.derivative(x_) / (Atom::num(1) - u_.pow(2)).sqrt()), x_);
            rubi_star(argument, v_int) + rubi_star(b__, rubi_rhs_int(&recursive, x_))
        },
    ));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn downvalues_5302_through_5342_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .filter(|order| (5302..=5342).contains(order))
            .collect::<Vec<_>>();
        assert_eq!(orders, (5302..=5342).collect::<Vec<_>>());
    }

    #[test]
    fn global_downvalues_5293_through_5342_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        crate::rules::push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .filter(|order| (5293..=5342).contains(order))
            .collect::<Vec<_>>();
        assert_eq!(orders, (5293..=5342).collect::<Vec<_>>());
    }

    #[test]
    fn downvalues_5343_through_5344_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .filter(|order| (5343..=5344).contains(order))
            .collect::<Vec<_>>();
        assert_eq!(orders, (5343..=5344).collect::<Vec<_>>());
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
    (a__ + b__ * (c__ + d__ * x_.pow(2)).acos()).pow(n_)
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    (a__ + b__ * (c__ + d__ * x_.pow(2)).asin()).pow(n_)
}
