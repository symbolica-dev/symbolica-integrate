use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_6273(rules);
    push_rules_rule_6274(rules);
    push_rules_rule_6275(rules);
    push_rules_rule_6276(rules);
    push_rules_rule_6277(rules);
    push_rules_rule_6278(rules);
    push_rules_rule_6279(rules);
    push_rules_rule_6280(rules);
    push_rules_rule_6281(rules);
    push_rules_rule_6282(rules);
    push_rules_rule_6283(rules);
    push_rules_rule_6284(rules);
    push_rules_rule_6285(rules);
    push_rules_rule_6286(rules);
    push_rules_rule_6287(rules);
    push_rules_rule_6288(rules);
    push_rules_rule_6289(rules);
    push_rules_rule_6290(rules);
    push_rules_rule_6291(rules);
    push_rules_rule_6292(rules);
    push_rules_rule_6293(rules);
}

fn push_rules_rule_6273(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 6273,
        source: "Int[(a_.+b_.*ArcSinh[c_+d_.*x_])^n_.,x_Symbol] :=
          1/d \\[Star] Subst[Int[(a+b*ArcSinh[x])^n,x],x,c+d*x] /;
        FreeQ[{a,b,c,d,n},x]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (a__ + b__ * (c__ + d__ * x_).asinh()).pow(n_),
        with: [a__, b__, c__, d__, n_, x_],
        optional: [a__, b__, d__, n_],
        when: { freeq!([a__, b__, c__, d__, n_], x_) },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let payload = (&a__ + &b__ * sub_atom.asinh()).pow(&n_);
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            let substituted = rubi_subst(&primitive, substitution_symbol, &c__ + &d__ * x_);
            rubi_star(Atom::num(1) / &d__, substituted)
        },
    ));
}

fn push_rules_rule_6274(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 6274,
        source: "Int[(e_.+f_.*x_)^m_.*(a_.+b_.*ArcSinh[c_+d_.*x_])^n_.,x_Symbol] :=
          1/d \\[Star] Subst[Int[((d*e-c*f)/d+f*x/d)^m*(a+b*ArcSinh[x])^n,x],x,c+d*x] /;
        FreeQ[{a,b,c,d,e,f,m,n},x]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (e__ + f__ * x_).pow(m_) * (a__ + b__ * (c__ + d__ * x_).asinh()).pow(n_),
        with: [e__, f__, m_, a__, b__, c__, d__, n_, x_],
        optional: [e__, f__, m_, a__, b__, d__, n_],
        when: { freeq!([a__, b__, c__, d__, e__, f__, m_, n_], x_) },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let transformed_linear = (&d__ * &e__ - &c__ * &f__) / &d__ + &f__ * &sub_atom / &d__;
            let payload = transformed_linear.pow(&m_) * (&a__ + &b__ * sub_atom.asinh()).pow(&n_);
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            let substituted = rubi_subst(&primitive, substitution_symbol, &c__ + &d__ * x_);
            rubi_star(Atom::num(1) / &d__, substituted)
        },
    ));
}

fn push_rules_rule_6275(rules: &mut Vec<RubiRule>) {
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
        order: 6275,
        source: "Int[(A_.+B_.*x_+C_.*x_^2)^p_.*(a_.+b_.*ArcSinh[c_+d_.*x_])^n_.,x_Symbol] :=
          1/d \\[Star] Subst[Int[(C/d^2+C/d^2*x^2)^p*(a+b*ArcSinh[x])^n,x],x,c+d*x] /;
        FreeQ[{a,b,c,d,A,B,C,n,p},x] && EqQ[B*(1+c^2)-2*A*c*d,0] && EqQ[2*c*C-B*d,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (capital_a__ + capital_b__ * x_ + capital_c__ * x_.pow(2)).pow(p_) * (a__ + b__ * (c__ + d__ * x_).asinh()).pow(n_),
        with: [capital_a__, capital_b__, capital_c__, p_, a__, b__, c__, d__, n_, x_],
        optional: [capital_a__, capital_b__, capital_c__, a__, b__, d__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, capital_a__, capital_b__, capital_c__, n_, p_], x_)
                && eqq!(&capital_b__ * (Atom::num(1) + c__.pow(2)) - Atom::num(2) * &capital_a__ * &c__ * &d__, 0)
                && eqq!(Atom::num(2) * &c__ * &capital_c__ - &capital_b__ * &d__, 0)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let transformed_quadratic = &capital_c__ / d__.pow(2) + &capital_c__ * sub_atom.pow(2) / d__.pow(2);
            let payload = transformed_quadratic.pow(&p_) * (&a__ + &b__ * sub_atom.asinh()).pow(&n_);
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            let substituted = rubi_subst(&primitive, substitution_symbol, &c__ + &d__ * x_);
            rubi_star(Atom::num(1) / &d__, substituted)
        },
    ));
}

fn push_rules_rule_6276(rules: &mut Vec<RubiRule>) {
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
        order: 6276,
        source: "Int[(e_.+f_.*x_)^m_.*(A_.+B_.*x_+C_.*x_^2)^p_.*(a_.+b_.*ArcSinh[c_+d_.*x_])^n_.,x_Symbol] :=
          1/d \\[Star] Subst[Int[((d*e-c*f)/d+f*x/d)^m*(C/d^2+C/d^2*x^2)^p*(a+b*ArcSinh[x])^n,x],x,c+d*x] /;
        FreeQ[{a,b,c,d,e,f,A,B,C,m,n,p},x] && EqQ[B*(1+c^2)-2*A*c*d,0] && EqQ[2*c*C-B*d,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (e__ + f__ * x_).pow(m_)
            * (capital_a__ + capital_b__ * x_ + capital_c__ * x_.pow(2)).pow(p_)
            * (a__ + b__ * (c__ + d__ * x_).asinh()).pow(n_),
        with: [e__, f__, m_, capital_a__, capital_b__, capital_c__, p_, a__, b__, c__, d__, n_, x_],
        optional: [e__, f__, m_, capital_a__, capital_b__, capital_c__, a__, b__, d__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, capital_a__, capital_b__, capital_c__, m_, n_, p_], x_)
                && eqq!(&capital_b__ * (Atom::num(1) + c__.pow(2)) - Atom::num(2) * &capital_a__ * &c__ * &d__, 0)
                && eqq!(Atom::num(2) * &c__ * &capital_c__ - &capital_b__ * &d__, 0)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let transformed_linear = (&d__ * &e__ - &c__ * &f__) / &d__ + &f__ * &sub_atom / &d__;
            let transformed_quadratic = &capital_c__ / d__.pow(2) + &capital_c__ * sub_atom.pow(2) / d__.pow(2);
            let payload = transformed_linear.pow(&m_)
                * transformed_quadratic.pow(&p_)
                * (&a__ + &b__ * sub_atom.asinh()).pow(&n_);
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            let substituted = rubi_subst(&primitive, substitution_symbol, &c__ + &d__ * x_);
            rubi_star(Atom::num(1) / &d__, substituted)
        },
    ));
}

fn push_rules_rule_6277(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 6277,
        source: "Int[Sqrt[a_.+b_.*ArcSinh[c_+d_.*x_^2]],x_Symbol] :=
          x*Sqrt[a+b*ArcSinh[c+d*x^2]] -
          Sqrt[Pi]*x*(Cosh[a/(2*b)]-c*Sinh[a/(2*b)])*FresnelC[Sqrt[-c/(Pi*b)]*Sqrt[a+b*ArcSinh[c+d*x^2]]]/
            (Sqrt[-(c/b)]*(Cosh[ArcSinh[c+d*x^2]/2]+c*Sinh[ArcSinh[c+d*x^2]/2])) +
          Sqrt[Pi]*x*(Cosh[a/(2*b)]+c*Sinh[a/(2*b)])*FresnelS[Sqrt[-c/(Pi*b)]*Sqrt[a+b*ArcSinh[c+d*x^2]]]/
            (Sqrt[-(c/b)]*(Cosh[ArcSinh[c+d*x^2]/2]+c*Sinh[ArcSinh[c+d*x^2]/2])) /;
        FreeQ[{a,b,c,d},x] && EqQ[c^2,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern: (a__ + b__ * (c__ + d__ * x_.pow(2)).asinh()).sqrt(),
        with: [a__, b__, c__, d__, x_],
        optional: [a__, b__, d__],
        when: { freeq!([a__, b__, c__, d__], x_) && eqq!(c__.pow(2), -1) },
        rhs: {
            let argument = &a__ + &b__ * (&c__ + &d__ * x_.pow(2)).asinh();
            let half_asinh = (&c__ + &d__ * x_.pow(2)).asinh() / Atom::num(2);
            let denom = (-( &c__ / &b__)).sqrt() * (&half_asinh.cosh() + &c__ * half_asinh.sinh());
            rubi_simp(&(x_ * &argument.sqrt()), x_)
                    - rubi_simp(&(Atom::var(Symbol::PI).sqrt()
                        * x_
                        * ((&a__ / (Atom::num(2) * &b__)).cosh() - &c__ * (&a__ / (Atom::num(2) * &b__)).sinh())
                        * rubi_fresnel_c((-&c__ / (Atom::var(Symbol::PI) * &b__)).sqrt() * &argument.sqrt())
                        / &denom), x_)
                    + rubi_simp(&(Atom::var(Symbol::PI).sqrt()
                        * x_
                        * ((&a__ / (Atom::num(2) * &b__)).cosh() + &c__ * (&a__ / (Atom::num(2) * &b__)).sinh())
                        * rubi_fresnel_s((-&c__ / (Atom::var(Symbol::PI) * &b__)).sqrt() * argument.sqrt())
                        / denom), x_)
        },
    ));
}

fn push_rules_rule_6278(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 6278,
        source: "Int[(a_.+b_.*ArcSinh[c_+d_.*x_^2])^n_,x_Symbol] :=
          x*(a+b*ArcSinh[c+d*x^2])^n -
          2*b*n*Sqrt[2*c*d*x^2+d^2*x^4]*(a+b*ArcSinh[c+d*x^2])^(n-1)/(d*x) +
          4*b^2*n*(n-1) \\[Star] Int[(a+b*ArcSinh[c+d*x^2])^(n-2),x] /;
        FreeQ[{a,b,c,d},x] && EqQ[c^2,-1] && GtQ[n,1]",
        desc: "Integration by parts twice",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, n_, x_],
        optional: [a__, b__, d__],
        when: { freeq!([a__, b__, c__, d__], x_) && eqq!(c__.pow(2), -1) && gtq!(n_, 1) },
        rhs: {
            let argument = &a__ + &b__ * (&c__ + &d__ * x_.pow(2)).asinh();
            let radical = (Atom::num(2) * &c__ * &d__ * x_.pow(2) + d__.pow(2) * x_.pow(4)).sqrt();
            let recursive = argument.pow(&n_ - Atom::num(2));
            let recursive_primitive = rubi_rhs_int(&recursive, x_);
            rubi_simp(&(x_ * argument.pow(&n_)), x_)
                    - rubi_simp(&(Atom::num(2) * &b__ * &n_ * radical * argument.pow(&n_ - Atom::num(1)) / (&d__ * x_)), x_)
                    + rubi_star(Atom::num(4) * b__.pow(2) * &n_ * (&n_ - Atom::num(1)), recursive_primitive)
        },
    ));
}

fn push_rules_rule_6279(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 6279,
        source: "Int[1/(a_.+b_.*ArcSinh[c_+d_.*x_^2]),x_Symbol] :=
          x*(c*Cosh[a/(2*b)]-Sinh[a/(2*b)])*CoshIntegral[(a+b*ArcSinh[c+d*x^2])/(2*b)]/
            (2*b*(Cosh[ArcSinh[c+d*x^2]/2]+c*Sinh[(1/2)*ArcSinh[c+d*x^2]])) +
          x*(Cosh[a/(2*b)]-c*Sinh[a/(2*b)])*SinhIntegral[(a+b*ArcSinh[c+d*x^2])/(2*b)]/
            (2*b*(Cosh[ArcSinh[c+d*x^2]/2]+c*Sinh[(1/2)*ArcSinh[c+d*x^2]])) /;
        FreeQ[{a,b,c,d},x] && EqQ[c^2,-1]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: Atom::num(1) / (a__ + b__ * (c__ + d__ * x_.pow(2)).asinh()),
        with: [a__, b__, c__, d__, x_],
        optional: [a__, b__, d__],
        when: { freeq!([a__, b__, c__, d__], x_) && eqq!(c__.pow(2), -1) },
        rhs: {
            let asinh = (&c__ + &d__ * x_.pow(2)).asinh();
            let argument = &a__ + &b__ * &asinh;
            let denom = Atom::num(2) * &b__ * (&asinh / Atom::num(2)).cosh()
                + Atom::num(2) * &b__ * &c__ * (asinh / Atom::num(2)).sinh();
            rubi_simp(&(x_ * (&c__ * (&a__ / (Atom::num(2) * &b__)).cosh() - (&a__ / (Atom::num(2) * &b__)).sinh())
                    * rubi_cosh_integral(&argument / (Atom::num(2) * &b__))
                    / &denom), x_)
                    + rubi_simp(&(x_ * ((&a__ / (Atom::num(2) * &b__)).cosh() - &c__ * (&a__ / (Atom::num(2) * &b__)).sinh())
                        * rubi_sinh_integral(argument / (Atom::num(2) * &b__))
                        / denom), x_)
        },
    ));
}

fn push_rules_rule_6280(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 6280,
        source: "Int[1/Sqrt[a_.+b_.*ArcSinh[c_+d_.*x_^2]],x_Symbol] :=
          (c+1)*Sqrt[Pi/2]*x*(Cosh[a/(2*b)]-Sinh[a/(2*b)])*Erfi[Sqrt[a+b*ArcSinh[c+d*x^2]]/Sqrt[2*b]]/
            (2*Sqrt[b]*(Cosh[ArcSinh[c+d*x^2]/2]+c*Sinh[ArcSinh[c+d*x^2]/2])) +
          (c-1)*Sqrt[Pi/2]*x*(Cosh[a/(2*b)]+Sinh[a/(2*b)])*Erf[Sqrt[a+b*ArcSinh[c+d*x^2]]/Sqrt[2*b]]/
            (2*Sqrt[b]*(Cosh[ArcSinh[c+d*x^2]/2]+c*Sinh[ArcSinh[c+d*x^2]/2])) /;
        FreeQ[{a,b,c,d},x] && EqQ[c^2,-1]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: Atom::num(1) / (a__ + b__ * (c__ + d__ * x_.pow(2)).asinh()).sqrt(),
        with: [a__, b__, c__, d__, x_],
        optional: [a__, b__, d__],
        when: { freeq!([a__, b__, c__, d__], x_) && eqq!(c__.pow(2), -1) },
        rhs: {
            let argument = &a__ + &b__ * (&c__ + &d__ * x_.pow(2)).asinh();
            let asinh = (&c__ + &d__ * x_.pow(2)).asinh();
            let denom = Atom::num(2) * b__.sqrt() * ((&asinh / Atom::num(2)).cosh() + &c__ * (asinh / Atom::num(2)).sinh());
            rubi_simp(&((&c__ + 1)
                    * (Atom::var(Symbol::PI) / Atom::num(2)).sqrt()
                    * x_
                    * ((&a__ / (Atom::num(2) * &b__)).cosh() - (&a__ / (Atom::num(2) * &b__)).sinh())
                    * rubi_erfi(&argument.sqrt() / (Atom::num(2) * &b__).sqrt())
                    / &denom), x_)
                    + rubi_simp(&((&c__ - 1)
                        * (Atom::var(Symbol::PI) / Atom::num(2)).sqrt()
                        * x_
                        * ((&a__ / (Atom::num(2) * &b__)).cosh() + (&a__ / (Atom::num(2) * &b__)).sinh())
                        * rubi_erf(argument.sqrt() / (Atom::num(2) * &b__).sqrt())
                        / denom), x_)
        },
    ));
}

fn push_rules_rule_6281(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 6281,
        source: "Int[1/(a_.+b_.*ArcSinh[c_+d_.*x_^2])^(3/2),x_Symbol] :=
          -Sqrt[2*c*d*x^2+d^2*x^4]/(b*d*x*Sqrt[a+b*ArcSinh[c+d*x^2]]) -
          (-c/b)^(3/2)*Sqrt[Pi]*x*(Cosh[a/(2*b)]-c*Sinh[a/(2*b)])*FresnelC[Sqrt[-c/(Pi*b)]*Sqrt[a+b*ArcSinh[c+d*x^2]]]/
            (Cosh[ArcSinh[c+d*x^2]/2]+c*Sinh[ArcSinh[c+d*x^2]/2]) +
          (-c/b)^(3/2)*Sqrt[Pi]*x*(Cosh[a/(2*b)]+c*Sinh[a/(2*b)])*FresnelS[Sqrt[-c/(Pi*b)]*Sqrt[a+b*ArcSinh[c+d*x^2]]]/
            (Cosh[ArcSinh[c+d*x^2]/2]+c*Sinh[ArcSinh[c+d*x^2]/2]) /;
        FreeQ[{a,b,c,d},x] && EqQ[c^2,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern: Atom::num(1) / (a__ + b__ * (c__ + d__ * x_.pow(2)).asinh()).pow(Atom::num(3) / Atom::num(2)),
        with: [a__, b__, c__, d__, x_],
        optional: [a__, b__, d__],
        when: { freeq!([a__, b__, c__, d__], x_) && eqq!(c__.pow(2), -1) },
        rhs: {
            let asinh = (&c__ + &d__ * x_.pow(2)).asinh();
            let argument = &a__ + &b__ * &asinh;
            let denom = (&asinh / Atom::num(2)).cosh() + &c__ * (asinh / Atom::num(2)).sinh();
            let radical = (Atom::num(2) * &c__ * &d__ * x_.pow(2) + d__.pow(2) * x_.pow(4)).sqrt();
            rubi_simp(&(-radical / (&b__ * &d__ * x_ * &argument.sqrt())), x_)
                    - rubi_simp(&((-&c__ / &b__).pow(Atom::num(3) / Atom::num(2))
                        * Atom::var(Symbol::PI).sqrt()
                        * x_
                        * ((&a__ / (Atom::num(2) * &b__)).cosh() - &c__ * (&a__ / (Atom::num(2) * &b__)).sinh())
                        * rubi_fresnel_c((-&c__ / (Atom::var(Symbol::PI) * &b__)).sqrt() * &argument.sqrt())
                        / &denom), x_)
                    + rubi_simp(&((-&c__ / &b__).pow(Atom::num(3) / Atom::num(2))
                        * Atom::var(Symbol::PI).sqrt()
                        * x_
                        * ((&a__ / (Atom::num(2) * &b__)).cosh() + &c__ * (&a__ / (Atom::num(2) * &b__)).sinh())
                        * rubi_fresnel_s((-&c__ / (Atom::var(Symbol::PI) * &b__)).sqrt() * argument.sqrt())
                        / denom), x_)
        },
    ));
}

fn push_rules_rule_6282(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 6282,
        source: "Int[1/(a_.+b_.*ArcSinh[c_+d_.*x_^2])^2,x_Symbol] :=
          -Sqrt[2*c*d*x^2+d^2*x^4]/(2*b*d*x*(a+b*ArcSinh[c+d*x^2])) +
          x*(Cosh[a/(2*b)]-c*Sinh[a/(2*b)])*CoshIntegral[(a+b*ArcSinh[c+d*x^2])/(2*b)]/
            (4*b^2*(Cosh[ArcSinh[c+d*x^2]/2]+c*Sinh[ArcSinh[c+d*x^2]/2])) +
          x*(c*Cosh[a/(2*b)]-Sinh[a/(2*b)])*SinhIntegral[(a+b*ArcSinh[c+d*x^2])/(2*b)]/
            (4*b^2*(Cosh[ArcSinh[c+d*x^2]/2]+c*Sinh[ArcSinh[c+d*x^2]/2])) /;
        FreeQ[{a,b,c,d},x] && EqQ[c^2,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern: Atom::num(1) / (a__ + b__ * (c__ + d__ * x_.pow(2)).asinh()).pow(2),
        with: [a__, b__, c__, d__, x_],
        optional: [a__, b__, d__],
        when: { freeq!([a__, b__, c__, d__], x_) && eqq!(c__.pow(2), -1) },
        rhs: {
            let asinh = (&c__ + &d__ * x_.pow(2)).asinh();
            let argument = &a__ + &b__ * &asinh;
            let denom = Atom::num(4) * b__.pow(2) * ((&asinh / Atom::num(2)).cosh() + &c__ * (asinh / Atom::num(2)).sinh());
            let radical = (Atom::num(2) * &c__ * &d__ * x_.pow(2) + d__.pow(2) * x_.pow(4)).sqrt();
            rubi_simp(&(-radical / (Atom::num(2) * &b__ * &d__ * x_ * &argument)), x_)
                    + rubi_simp(&(x_ * ((&a__ / (Atom::num(2) * &b__)).cosh() - &c__ * (&a__ / (Atom::num(2) * &b__)).sinh())
                        * rubi_cosh_integral(&argument / (Atom::num(2) * &b__))
                        / &denom), x_)
                    + rubi_simp(&(x_ * (&c__ * (&a__ / (Atom::num(2) * &b__)).cosh() - (&a__ / (Atom::num(2) * &b__)).sinh())
                        * rubi_sinh_integral(argument / (Atom::num(2) * &b__))
                        / denom), x_)
        },
    ));
}

fn push_rules_rule_6283(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 6283,
        source: "Int[(a_.+b_.*ArcSinh[c_+d_.*x_^2])^n_,x_Symbol] :=
          -x*(a+b*ArcSinh[c+d*x^2])^(n+2)/(4*b^2*(n+1)*(n+2)) +
          Sqrt[2*c*d*x^2+d^2*x^4]*(a+b*ArcSinh[c+d*x^2])^(n+1)/(2*b*d*(n+1)*x) +
          1/(4*b^2*(n+1)*(n+2)) \\[Star] Int[(a+b*ArcSinh[c+d*x^2])^(n+2),x] /;
        FreeQ[{a,b,c,d},x] && EqQ[c^2,-1] && LtQ[n,-1] && NeQ[n,-2]",
        desc: "Inverted integration by parts twice",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, n_, x_],
        optional: [a__, b__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && eqq!(c__.pow(2), -1)
                && ltq!(n_, -1)
                && neq!(n_, -2)
        },
        rhs: {
            let argument = &a__ + &b__ * (&c__ + &d__ * x_.pow(2)).asinh();
            let radical = (Atom::num(2) * &c__ * &d__ * x_.pow(2) + d__.pow(2) * x_.pow(4)).sqrt();
            let recursive = argument.pow(&n_ + Atom::num(2));
            let recursive_primitive = rubi_rhs_int(&recursive, x_);
            rubi_simp(&(Atom::num(-1) * x_ * argument.pow(&n_ + Atom::num(2))
                    / (Atom::num(4) * b__.pow(2) * (&n_ + Atom::num(1)) * (&n_ + Atom::num(2)))), x_)
                    + rubi_simp(&(radical * argument.pow(&n_ + Atom::num(1)) / (Atom::num(2) * &b__ * &d__ * (&n_ + Atom::num(1)) * x_)), x_)
                    + rubi_star(Atom::num(1)
                            / (Atom::num(4)
                                * b__.pow(2)
                                * (&n_ + Atom::num(1))
                                * (&n_ + Atom::num(2))), recursive_primitive)
        },
    ));
}

fn push_rules_rule_6284(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6284,
        source: "Int[ArcSinh[a_.*x_^p_]^n_./x_,x_Symbol] :=
          1/p \\[Star] Subst[Int[x^n*Coth[x],x],x,ArcSinh[a*x^p]] /;
        FreeQ[{a,p},x] && IGtQ[n,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (a__ * x_.pow(p_)).asinh().pow(n_) / x_,
        with: [a__, p_, n_, x_],
        optional: [a__, n_],
        when: { freeq!([a__, p_], x_) && igtq!(n_, 0) },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let payload = sub_atom.pow(&n_) * sub_atom.coth();
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            let substituted = rubi_subst(
                &primitive,
                substitution_symbol,
                (&a__ * x_.pow(&p_)).asinh(),
            );
            rubi_star(Atom::num(1) / &p_, substituted)
        },
    ));
}

fn push_rules_rule_6285(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, m_, n_, u__, x_);
    rules.push(rubi_rule!(
        order: 6285,
        source: "Int[u_.*ArcSinh[c_./(a_.+b_.*x_^n_.)]^m_.,x_Symbol] :=
          Int[u*ArcCsch[a/c+b*x^n/c]^m,x] /;
        FreeQ[{a,b,c,n,m},x]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: u__ * (c__ / (a__ + b__ * x_.pow(n_))).asinh().pow(m_),
        with: [u__, c__, a__, b__, n_, m_, x_],
        optional: [u__, a__, b__, n_, m_, c__],
        when: { freeq!([a__, b__, c__, n_, m_], x_) },
        rhs: {
            let transformed = u__ * (&a__ / &c__ + &b__ * x_.pow(&n_) / &c__).acsch().pow(&m_);
            rubi_rhs_int(&transformed, x_)
        },
    ));
}

fn push_rules_rule_6286(rules: &mut Vec<RubiRule>) {
    rubi_symb!(b__, n_, x_);
    rules.push(rubi_rule!(
        order: 6286,
        source: "Int[ArcSinh[Sqrt[-1+b_.*x_^2]]^n_./Sqrt[-1+b_.*x_^2],x_Symbol] :=
          Sqrt[b*x^2]/(b*x) \\[Star] Subst[Int[ArcSinh[x]^n/Sqrt[1+x^2],x],x,Sqrt[-1+b*x^2]] /;
        FreeQ[{b,n},x]",
        desc: "Piecewise constant extraction and integration by substitution",
        refs: [],
        pattern: (Atom::num(-1) + b__ * x_.pow(2)).sqrt().asinh().pow(n_)
            / (Atom::num(-1) + b__ * x_.pow(2)).sqrt(),
        with: [b__, n_, x_],
        optional: [b__, n_],
        when: { freeq!([b__, n_], x_) },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let payload = sub_atom.asinh().pow(&n_) / (Atom::num(1) + sub_atom.pow(2)).sqrt();
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            let substituted = rubi_subst(
                &primitive,
                substitution_symbol,
                (Atom::num(-1) + &b__ * x_.pow(2)).sqrt(),
            );
            rubi_star((&b__ * x_.pow(2)).sqrt() / (&b__ * x_), substituted)
        },
    ));
}

fn push_rules_rule_6287(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, f__, n_, x_);
    rules.push(rubi_rule!(
        order: 6287,
        source: "Int[f_^(c_.*ArcSinh[a_.+b_.*x_]^n_.),x_Symbol] :=
          1/b \\[Star] Subst[Int[f^(c*x^n)*Cosh[x],x],x,ArcSinh[a+b*x]] /;
        FreeQ[{a,b,c,f},x] && IGtQ[n,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: f__.pow(c__ * (a__ + b__ * x_).asinh().pow(n_)),
        with: [f__, c__, a__, b__, n_, x_],
        optional: [c__, a__, b__, n_],
        when: { freeq!([a__, b__, c__, f__], x_) && igtq!(n_, 0) },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let payload = f__.pow(&c__ * sub_atom.pow(&n_)) * sub_atom.cosh();
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            let substituted = rubi_subst(
                &primitive,
                substitution_symbol,
                (&a__ + &b__ * x_).asinh(),
            );
            rubi_star(Atom::num(1) / &b__, substituted)
        },
    ));
}

fn push_rules_rule_6288(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, f__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 6288,
        source: "Int[x_^m_.*f_^(c_.*ArcSinh[a_.+b_.*x_]^n_.),x_Symbol] :=
          1/b \\[Star] Subst[Int[(-a/b+Sinh[x]/b)^m*f^(c*x^n)*Cosh[x],x],x,ArcSinh[a+b*x]] /;
        FreeQ[{a,b,c,f},x] && IGtQ[m,0] && IGtQ[n,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: x_.pow(m_) * f__.pow(c__ * (a__ + b__ * x_).asinh().pow(n_)),
        with: [m_, f__, c__, a__, b__, n_, x_],
        optional: [m_, c__, a__, b__, n_],
        when: { freeq!([a__, b__, c__, f__], x_) && igtq!(m_, 0) && igtq!(n_, 0) },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let sub_atom = Atom::var(substitution_symbol);
            let payload = (-&a__ / &b__ + sub_atom.sinh() / &b__).pow(&m_)
                * f__.pow(&c__ * sub_atom.pow(&n_))
                * sub_atom.cosh();
            let primitive = rubi_rhs_int(&payload, substitution_symbol);
            let substituted = rubi_subst(
                &primitive,
                substitution_symbol,
                (&a__ + &b__ * x_).asinh(),
            );
            rubi_star(Atom::num(1) / &b__, substituted)
        },
    ));
}

fn push_rules_rule_6289(rules: &mut Vec<RubiRule>) {
    rubi_symb!(u_);
    rules.push(rubi_rule!(
        order: 6289,
        source: "Int[ArcSinh[u_],x_Symbol] :=
          x*ArcSinh[u] -
          Int[SimplifyIntegrand[x*D[u,x]/Sqrt[1+u^2],x],x] /;
        InverseFunctionFreeQ[u,x] && Not[FunctionOfExponentialQ[u,x]]",
        desc: "Integration by parts",
        refs: [],
        pattern: Atom::var(u_).asinh(),
        with: [u_, x_],
        when: { rubi_inverse_function_free_q(&u_, x_) && !rubi_function_of_exponential_q(u_.as_view(), x_) },
        rhs: {
            let recursive =
                rubi_simplify_integrand(&(x_ * u_.derivative(x_) / (Atom::num(1) + u_.pow(2)).sqrt()), x_);
            rubi_simp(&(x_ * u_.asinh()), x_) - rubi_rhs_int(&recursive, x_)
        },
    ));
}

fn push_rules_rule_6290(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, u_, x_);
    rules.push(rubi_rule!(
        order: 6290,
        source: "Int[(c_.+d_.*x_)^m_.*(a_.+b_.*ArcSinh[u_]),x_Symbol] :=
          (c+d*x)^(m+1)*(a+b*ArcSinh[u])/(d*(m+1)) -
          b/(d*(m+1)) \\[Star] Int[SimplifyIntegrand[(c+d*x)^(m+1)*D[u,x]/Sqrt[1+u^2],x],x] /;
        FreeQ[{a,b,c,d,m},x] && NeQ[m,-1] && InverseFunctionFreeQ[u,x] && Not[FunctionOfQ[(c+d*x)^(m+1),u,x]] && Not[FunctionOfExponentialQ[u,x]]",
        desc: "Integration by parts",
        refs: [],
        pattern: (c__ + d__ * x_).pow(m_) * (a__ + b__ * Atom::var(u_).asinh()),
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
            let argument = &a__ + &b__ * u_.asinh();
            let recursive = rubi_simplify_integrand(
                &(linear.pow(&m_ + Atom::num(1)) * u_.derivative(x_) / (Atom::num(1) + u_.pow(2)).sqrt()),
                x_,
            );
            let recursive_primitive = rubi_rhs_int(&recursive, x_);
            rubi_simp(&(linear.pow(&m_ + Atom::num(1)) * argument / (&d__ * (&m_ + Atom::num(1)))), x_)
                    - rubi_star(&b__ / (&d__ * (&m_ + Atom::num(1))), recursive_primitive)
        },
    ));
}

fn push_rules_rule_6291(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, u_, v__);
    rules.push(rubi_rule!(
        order: 6291,
        source: "Int[v_*(a_.+b_.*ArcSinh[u_]),x_Symbol] :=
          With[{w=IntHide[v,x]},
          (a+b*ArcSinh[u]) \\[Star] w - b \\[Star] Int[SimplifyIntegrand[w*D[u,x]/Sqrt[1+u^2],x],x] /;
         InverseFunctionFreeQ[w,x]] /;
        FreeQ[{a,b},x] && InverseFunctionFreeQ[u,x] && Not[MatchQ[v, (c_.+d_.*x)^m_. /; FreeQ[{c,d,m},x]]]",
        desc: "Integration by parts",
        refs: [],
        pattern: v__ * (a__ + b__ * Atom::var(u_).asinh()),
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
            let argument = &a__ + &b__ * u_.asinh();
            let recursive =
                rubi_simplify_integrand(&(&v_int * u_.derivative(x_) / (Atom::num(1) + u_.pow(2)).sqrt()), x_);
            rubi_star(argument, v_int)
                    - rubi_star(b__, rubi_rhs_int(&recursive, x_))
        },
    ));
}

fn push_rules_rule_6292(rules: &mut Vec<RubiRule>) {
    rubi_symb!(n_, u_);
    rules.push(rubi_rule!(
        order: 6292,
        source: "Int[E^(n_.*ArcSinh[u_]), x_Symbol] :=
          Int[(u+Sqrt[1+u^2])^n,x] /;
        IntegerQ[n] && PolyQ[u,x]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: (n_ * Atom::var(u_).asinh()).exp(),
        with: [n_, u_, x_],
        optional: [n_],
        when: { integerq!(n_) && rubi_poly_q(&u_, x_) },
        rhs: {
            let transformed = (&u_ + (Atom::num(1) + u_.pow(2)).sqrt()).pow(&n_);
            rubi_rhs_int(&transformed, x_)
        },
    ));
}

fn push_rules_rule_6293(rules: &mut Vec<RubiRule>) {
    rubi_symb!(m_, n_, u_, x_);
    rules.push(rubi_rule!(
        order: 6293,
        source: "Int[x_^m_.*E^(n_.*ArcSinh[u_]), x_Symbol] :=
          Int[x^m*(u+Sqrt[1+u^2])^n,x] /;
        RationalQ[m] && IntegerQ[n] && PolyQ[u,x]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: x_.pow(m_) * (n_ * Atom::var(u_).asinh()).exp(),
        with: [m_, n_, u_, x_],
        optional: [m_, n_],
        when: { rationalq!(m_) && integerq!(n_) && rubi_poly_q(&u_, x_) },
        rhs: {
            let transformed = x_.pow(&m_) * (&u_ + (Atom::num(1) + u_.pow(2)).sqrt()).pow(&n_);
            rubi_rhs_int(&transformed, x_)
        },
    ));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn downvalues_6273_through_6293_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .filter(|order| (6273..=6293).contains(order))
            .collect::<Vec<_>>();
        assert_eq!(orders, (6273..=6293).collect::<Vec<_>>());
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
    (a__ + b__ * (c__ + d__ * x_.pow(2)).asinh()).pow(n_)
}
