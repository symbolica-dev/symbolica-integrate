use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_4978(rules);
    push_rules_rule_4979(rules);
    push_rules_rule_4980(rules);
    push_rules_rule_4981(rules);
    push_rules_rule_4982(rules);
    push_rules_rule_4983(rules);
    push_rules_rule_4984(rules);
    push_rules_rule_4985(rules);
    push_rules_rule_4986(rules);
    push_rules_rule_4987(rules);
    push_rules_rule_4988(rules);
    push_rules_rule_4989(rules);
    push_rules_rule_4990(rules);
    push_rules_rule_4991(rules);
    push_rules_rule_4992(rules);
    push_rules_rule_4993(rules);
    push_rules_rule_4994(rules);
    push_rules_rule_4995(rules);
    push_rules_rule_4996(rules);
    push_rules_rule_4997(rules);
    push_rules_rule_4998(rules);
    push_rules_rule_4999(rules);
    push_rules_rule_5000(rules);
    push_rules_rule_5001(rules);
    push_rules_rule_5002(rules);
    push_rules_rule_5003(rules);
    push_rules_rule_5004(rules);
    push_rules_rule_5005(rules);
    push_rules_rule_5006(rules);
    push_rules_rule_5007(rules);
    push_rules_rule_5008(rules);
    push_rules_rule_5009(rules);
    push_rules_rule_5010(rules);
    push_rules_rule_5011(rules);
    push_rules_rule_5012(rules);
    push_rules_rule_5013(rules);
    push_rules_rule_5014(rules);
    push_rules_rule_5015(rules);
    push_rules_rule_5016(rules);
    push_rules_rule_5017(rules);
    push_rules_rule_5018(rules);
    push_rules_rule_5019(rules);
    push_rules_rule_5020(rules);
    push_rules_rule_5021(rules);
    push_rules_rule_5022(rules);
    push_rules_rule_5023(rules);
    push_rules_rule_5024(rules);
    push_rules_rule_5025(rules);
}

fn push_rules_rule_4978(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 4978,
        source: "Int[Sin[d_.*(a_.+b_.*Log[c_.*x_^n_.])],x_Symbol] :=
          x*Sin[d*(a+b*Log[c*x^n])]/(b^2*d^2*n^2+1) -
          b*d*n*x*Cos[d*(a+b*Log[c*x^n])]/(b^2*d^2*n^2+1) /;
        FreeQ[{a,b,c,d,n},x] && NeQ[b^2*d^2*n^2+1,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: (d__ * (a__ + b__ * (c__ * x_.pow(n_)).log())).sin(),
        with: [d__, a__, b__, c__, n_, x_],
        optional: [d__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, n_], x_)
                && neq!(b__.pow(2) * d__.pow(2) * n_.pow(2) + 1, 0)
        },
        rhs: {
            let angle = &d__ * (&a__ + &b__ * (&c__ * x_.pow(&n_)).log());
            let denominator = b__.pow(2) * d__.pow(2) * n_.pow(2) + 1;

            rubi_simp(&(x_ * angle.sin() / &denominator), x_)
                    - rubi_simp(&(&b__ * &d__ * &n_ * x_ * angle.cos() / denominator), x_)
        },
    ));
}

fn push_rules_rule_4979(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 4979,
        source: "Int[Cos[d_.*(a_.+b_.*Log[c_.*x_^n_.])],x_Symbol] :=
          x*Cos[d*(a+b*Log[c*x^n])]/(b^2*d^2*n^2+1) +
          b*d*n*x*Sin[d*(a+b*Log[c*x^n])]/(b^2*d^2*n^2+1) /;
        FreeQ[{a,b,c,d,n},x] && NeQ[b^2*d^2*n^2+1,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: (d__ * (a__ + b__ * (c__ * x_.pow(n_)).log())).cos(),
        with: [d__, a__, b__, c__, n_, x_],
        optional: [d__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, n_], x_)
                && neq!(b__.pow(2) * d__.pow(2) * n_.pow(2) + 1, 0)
        },
        rhs: {
            let angle = &d__ * (&a__ + &b__ * (&c__ * x_.pow(&n_)).log());
            let denominator = b__.pow(2) * d__.pow(2) * n_.pow(2) + 1;

            rubi_simp(&(x_ * angle.cos() / &denominator), x_)
                    + rubi_simp(&(&b__ * &d__ * &n_ * x_ * angle.sin() / denominator), x_)
        },
    ));
}

fn push_rules_rule_4980(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 4980,
        source: "Int[Sin[d_.*(a_.+b_.*Log[c_.*x_^n_.])]^p_,x_Symbol] :=
          x*Sin[d*(a+b*Log[c*x^n])]^p/(b^2*d^2*n^2*p^2+1) -
          b*d*n*p*x*Cos[d*(a+b*Log[c*x^n])]*Sin[d*(a+b*Log[c*x^n])]^(p-1)/(b^2*d^2*n^2*p^2+1) +
          b^2*d^2*n^2*p*(p-1)/(b^2*d^2*n^2*p^2+1) \\[Star] Int[Sin[d*(a+b*Log[c*x^n])]^(p-2),x] /;
        FreeQ[{a,b,c,d,n},x] && IGtQ[p,1] && NeQ[b^2*d^2*n^2*p^2+1,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [d__, a__, b__, c__, n_, p_, x_],
        optional: [d__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, n_], x_)
                && igtq!(p_, 1)
                && neq!(b__.pow(2) * d__.pow(2) * n_.pow(2) * p_.pow(2) + 1, 0)
        },
        rhs: {
            let angle = &d__ * (&a__ + &b__ * (&c__ * x_.pow(&n_)).log());
            let denominator = b__.pow(2) * d__.pow(2) * n_.pow(2) * p_.pow(2) + 1;
            let recursive_integrand = angle.sin().pow(&p_ - 2);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let recursive_term = rubi_simp(&(&(b__.pow(2) * d__.pow(2) * n_.pow(2) * &p_ * (&p_ - 1) / &denominator) * &recursive), x_);

            rubi_simp(&(x_ * angle.sin().pow(&p_) / &denominator), x_)
                    - rubi_simp(&(&b__ * &d__ * &n_ * &p_ * x_ * angle.cos() * angle.sin().pow(&p_ - 1) / &denominator), x_)
                    + rubi_star(Atom::num(1), recursive_term)
        },
    ));
}

fn push_rules_rule_4981(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 4981,
        source: "Int[Cos[d_.*(a_.+b_.*Log[c_.*x_^n_.])]^p_,x_Symbol] :=
          x*Cos[d*(a+b*Log[c*x^n])]^p/(b^2*d^2*n^2*p^2+1) +
          b*d*n*p*x*Cos[d*(a+b*Log[c*x^n])]^(p-1)*Sin[d*(a+b*Log[c*x^n])]/(b^2*d^2*n^2*p^2+1) +
          b^2*d^2*n^2*p*(p-1)/(b^2*d^2*n^2*p^2+1) \\[Star] Int[Cos[d*(a+b*Log[c*x^n])]^(p-2),x] /;
        FreeQ[{a,b,c,d,n},x] && IGtQ[p,1] && NeQ[b^2*d^2*n^2*p^2+1,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [d__, a__, b__, c__, n_, p_, x_],
        optional: [d__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, n_], x_)
                && igtq!(p_, 1)
                && neq!(b__.pow(2) * d__.pow(2) * n_.pow(2) * p_.pow(2) + 1, 0)
        },
        rhs: {
            let angle = &d__ * (&a__ + &b__ * (&c__ * x_.pow(&n_)).log());
            let denominator = b__.pow(2) * d__.pow(2) * n_.pow(2) * p_.pow(2) + 1;
            let recursive_integrand = angle.cos().pow(&p_ - 2);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let recursive_term = rubi_simp(&(&(b__.pow(2) * d__.pow(2) * n_.pow(2) * &p_ * (&p_ - 1) / &denominator) * &recursive), x_);

            rubi_simp(&(x_ * angle.cos().pow(&p_) / &denominator), x_)
                    + rubi_simp(&(&b__ * &d__ * &n_ * &p_ * x_ * angle.cos().pow(&p_ - 1) * angle.sin() / &denominator), x_)
                    + rubi_star(Atom::num(1), recursive_term)
        },
    ));
}

fn push_rules_rule_4982(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, p_, x_);
    rules.push(rubi_rule!(
        order: 4982,
        source: "Int[Sin[d_.*(a_.+b_.*Log[x_])]^p_.,x_Symbol] :=
          1/(2^p*b^p*d^p*p^p) \\[Star] Int[ExpandIntegrand[(E^(a*b*d^2*p)*x^(-1/p)-E^(-a*b*d^2*p)*x^(1/p))^p,x],x] /;
        FreeQ[{a,b,d},x] && IGtQ[p,0] && EqQ[b^2*d^2*p^2+1,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [d__, a__, b__, p_, x_],
        optional: [d__, a__, b__, p_],
        when: {
            freeq!([a__, b__, d__], x_)
                && igtq!(p_, 0)
                && eqq!(b__.pow(2) * d__.pow(2) * p_.pow(2) + 1, 0)
        },
        rhs: {
            let payload = ((&a__ * &b__ * d__.pow(2) * &p_).exp() * x_.pow(-Atom::num(1) / &p_)
                - (-&a__ * &b__ * d__.pow(2) * &p_).exp() * x_.pow(Atom::num(1) / &p_))
            .pow(&p_);
            let expanded = rubi_expand_integrand(&payload, x_);
            let recursive = rubi_rhs_int(&expanded, x_);
            let coefficient = Atom::num(1)
                / (Atom::num(2).pow(&p_) * b__.pow(&p_) * d__.pow(&p_) * p_.pow(&p_));

            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_4983(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, p_, x_);
    rules.push(rubi_rule!(
        order: 4983,
        source: "Int[Cos[d_.*(a_.+b_.*Log[x_])]^p_.,x_Symbol] :=
          1/2^p \\[Star] Int[ExpandIntegrand[(E^(a*b*d^2*p)*x^(-1/p)+E^(-a*b*d^2*p)*x^(1/p))^p,x],x] /;
        FreeQ[{a,b,d},x] && IGtQ[p,0] && EqQ[b^2*d^2*p^2+1,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [d__, a__, b__, p_, x_],
        optional: [d__, a__, b__, p_],
        when: {
            freeq!([a__, b__, d__], x_)
                && igtq!(p_, 0)
                && eqq!(b__.pow(2) * d__.pow(2) * p_.pow(2) + 1, 0)
        },
        rhs: {
            let payload = ((&a__ * &b__ * d__.pow(2) * &p_).exp() * x_.pow(-Atom::num(1) / &p_)
                + (-&a__ * &b__ * d__.pow(2) * &p_).exp() * x_.pow(Atom::num(1) / &p_))
            .pow(&p_);
            let expanded = rubi_expand_integrand(&payload, x_);
            let recursive = rubi_rhs_int(&expanded, x_);

            rubi_star(Atom::num(1) / Atom::num(2).pow(&p_), recursive)
        },
    ));
}

fn push_rules_rule_4984(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, p_, x_);
    rules.push(rubi_rule!(
        order: 4984,
        source: "Int[Sin[d_.*(a_.+b_.*Log[x_])]^p_,x_Symbol] :=
          Sin[d*(a+b*Log[x])]^p*x^(I*b*d*p)/(1-E^(2*I*a*d)*x^(2*I*b*d))^p \\[Star]
            Int[(1-E^(2*I*a*d)*x^(2*I*b*d))^p/x^(I*b*d*p),x] /;
        FreeQ[{a,b,d,p},x] && Not[IntegerQ[p]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [d__, a__, b__, p_, x_],
        optional: [d__, a__, b__],
        when: {
            freeq!([a__, b__, d__, p_], x_)
                && !integerq!(p_)
        },
        rhs: {
            let i = Atom::i();
            let angle = &d__ * (&a__ + &b__ * x_.log());
            let exponential = (Atom::num(2) * &i * &a__ * &d__).exp() * x_.pow(Atom::num(2) * &i * &b__ * &d__);
            let recursive_integrand = (Atom::num(1) - &exponential).pow(&p_) / x_.pow(&i * &b__ * &d__ * &p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let coefficient = angle.sin().pow(&p_) * x_.pow(&i * &b__ * &d__ * &p_)
                / (Atom::num(1) - exponential).pow(&p_);

            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_4985(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, p_, x_);
    rules.push(rubi_rule!(
        order: 4985,
        source: "Int[Cos[d_.*(a_.+b_.*Log[x_])]^p_,x_Symbol] :=
          Cos[d*(a+b*Log[x])]^p*x^(I*b*d*p)/(1+E^(2*I*a*d)*x^(2*I*b*d))^p \\[Star]
            Int[(1+E^(2*I*a*d)*x^(2*I*b*d))^p/x^(I*b*d*p),x] /;
        FreeQ[{a,b,d,p},x] && Not[IntegerQ[p]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [d__, a__, b__, p_, x_],
        optional: [d__, a__, b__],
        when: {
            freeq!([a__, b__, d__, p_], x_)
                && !integerq!(p_)
        },
        rhs: {
            let i = Atom::i();
            let angle = &d__ * (&a__ + &b__ * x_.log());
            let exponential = (Atom::num(2) * &i * &a__ * &d__).exp() * x_.pow(Atom::num(2) * &i * &b__ * &d__);
            let recursive_integrand = (Atom::num(1) + &exponential).pow(&p_) / x_.pow(&i * &b__ * &d__ * &p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let coefficient = angle.cos().pow(&p_) * x_.pow(&i * &b__ * &d__ * &p_)
                / (Atom::num(1) + exponential).pow(&p_);

            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_4986(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 4986,
        source: "Int[Sin[d_.*(a_.+b_.*Log[c_.*x_^n_.])]^p_.,x_Symbol] :=
          x/(n*(c*x^n)^(1/n)) \\[Star] Subst[Int[x^(1/n-1)*Sin[d*(a+b*Log[x])]^p,x],x,c*x^n] /;
        FreeQ[{a,b,c,d,n,p},x] && (NeQ[c,1] || NeQ[n,1])",
        desc: "Piecewise constant extraction and integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [d__, a__, b__, c__, n_, p_, x_],
        optional: [d__, a__, b__, c__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, n_, p_], x_)
                && (neq!(c__, 1) || neq!(n_, 1))
        },
        rhs: {
            let recursive_integrand = x_.pow(Atom::num(1) / &n_ - 1)
                * (&d__ * (&a__ + &b__ * x_.log())).sin().pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let replacement = &c__ * x_.pow(&n_);
            let substituted = rubi_subst(&recursive, x_, &replacement);
            let coefficient = x_ / (&n_ * replacement.pow(Atom::num(1) / &n_));

            rubi_star(coefficient, substituted)
        },
    ));
}

fn push_rules_rule_4987(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 4987,
        source: "Int[Cos[d_.*(a_.+b_.*Log[c_.*x_^n_.])]^p_.,x_Symbol] :=
          x/(n*(c*x^n)^(1/n)) \\[Star] Subst[Int[x^(1/n-1)*Cos[d*(a+b*Log[x])]^p,x],x,c*x^n] /;
        FreeQ[{a,b,c,d,n,p},x] && (NeQ[c,1] || NeQ[n,1])",
        desc: "Piecewise constant extraction and integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [d__, a__, b__, c__, n_, p_, x_],
        optional: [d__, a__, b__, c__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, n_, p_], x_)
                && (neq!(c__, 1) || neq!(n_, 1))
        },
        rhs: {
            let recursive_integrand = x_.pow(Atom::num(1) / &n_ - 1)
                * (&d__ * (&a__ + &b__ * x_.log())).cos().pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let replacement = &c__ * x_.pow(&n_);
            let substituted = rubi_subst(&recursive, x_, &replacement);
            let coefficient = x_ / (&n_ * replacement.pow(Atom::num(1) / &n_));

            rubi_star(coefficient, substituted)
        },
    ));
}

fn push_rules_rule_4988(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 4988,
        source: "Int[(e_.*x_)^m_.*Sin[d_.*(a_.+b_.*Log[c_.*x_^n_.])],x_Symbol] :=
          (m+1)*(e*x)^(m+1)*Sin[d*(a+b*Log[c*x^n])]/(b^2*d^2*e*n^2+e*(m+1)^2) -
          b*d*n*(e*x)^(m+1)*Cos[d*(a+b*Log[c*x^n])]/(b^2*d^2*e*n^2+e*(m+1)^2) /;
        FreeQ[{a,b,c,d,e,m,n},x] && NeQ[b^2*d^2*n^2+(m+1)^2,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: (e__ * x_).pow(m_) * (d__ * (a__ + b__ * (c__ * x_.pow(n_)).log())).sin(),
        with: [e__, m_, d__, a__, b__, c__, n_, x_],
        optional: [e__, m_, d__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_], x_)
                && neq!(b__.pow(2) * d__.pow(2) * n_.pow(2) + (&m_ + 1).pow(2), 0)
        },
        rhs: {
            let scaled_x = &e__ * x_;
            let angle = &d__ * (&a__ + &b__ * (&c__ * x_.pow(&n_)).log());
            let denominator = b__.pow(2) * d__.pow(2) * &e__ * n_.pow(2) + &e__ * (&m_ + 1).pow(2);

            rubi_simp(&((&m_ + 1) * scaled_x.pow(&m_ + 1) * angle.sin() / &denominator), x_)
                    - rubi_simp(&(&b__ * &d__ * &n_ * scaled_x.pow(&m_ + 1) * angle.cos() / denominator), x_)
        },
    ));
}

fn push_rules_rule_4989(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 4989,
        source: "Int[(e_.*x_)^m_.*Cos[d_.*(a_.+b_.*Log[c_.*x_^n_.])],x_Symbol] :=
          (m+1)*(e*x)^(m+1)*Cos[d*(a+b*Log[c*x^n])]/(b^2*d^2*e*n^2+e*(m+1)^2) +
          b*d*n*(e*x)^(m+1)*Sin[d*(a+b*Log[c*x^n])]/(b^2*d^2*e*n^2+e*(m+1)^2) /;
        FreeQ[{a,b,c,d,e,m,n},x] && NeQ[b^2*d^2*n^2+(m+1)^2,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: (e__ * x_).pow(m_) * (d__ * (a__ + b__ * (c__ * x_.pow(n_)).log())).cos(),
        with: [e__, m_, d__, a__, b__, c__, n_, x_],
        optional: [e__, m_, d__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_], x_)
                && neq!(b__.pow(2) * d__.pow(2) * n_.pow(2) + (&m_ + 1).pow(2), 0)
        },
        rhs: {
            let scaled_x = &e__ * x_;
            let angle = &d__ * (&a__ + &b__ * (&c__ * x_.pow(&n_)).log());
            let denominator = b__.pow(2) * d__.pow(2) * &e__ * n_.pow(2) + &e__ * (&m_ + 1).pow(2);

            rubi_simp(&((&m_ + 1) * scaled_x.pow(&m_ + 1) * angle.cos() / &denominator), x_)
                    + rubi_simp(&(&b__ * &d__ * &n_ * scaled_x.pow(&m_ + 1) * angle.sin() / denominator), x_)
        },
    ));
}

fn push_rules_rule_4990(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 4990,
        source: "Int[(e_.*x_)^m_.*Sin[d_.*(a_.+b_.*Log[c_.*x_^n_.])]^p_,x_Symbol] :=
          (m+1)*(e*x)^(m+1)*Sin[d*(a+b*Log[c*x^n])]^p/(b^2*d^2*e*n^2*p^2+e*(m+1)^2) -
          b*d*n*p*(e*x)^(m+1)*Cos[d*(a+b*Log[c*x^n])]*Sin[d*(a+b*Log[c*x^n])]^(p-1)/(b^2*d^2*e*n^2*p^2+e*(m+1)^2) +
          b^2*d^2*n^2*p*(p-1)/(b^2*d^2*n^2*p^2+(m+1)^2) \\[Star] Int[(e*x)^m*Sin[d*(a+b*Log[c*x^n])]^(p-2),x] /;
        FreeQ[{a,b,c,d,e,m,n},x] && IGtQ[p,1] && NeQ[b^2*d^2*n^2*p^2+(m+1)^2,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [e__, m_, d__, a__, b__, c__, n_, p_, x_],
        optional: [e__, m_, d__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_], x_)
                && igtq!(p_, 1)
                && neq!(b__.pow(2) * d__.pow(2) * n_.pow(2) * p_.pow(2) + (&m_ + 1).pow(2), 0)
        },
        rhs: {
            let scaled_x = &e__ * x_;
            let angle = &d__ * (&a__ + &b__ * (&c__ * x_.pow(&n_)).log());
            let denominator_with_e =
                b__.pow(2) * d__.pow(2) * &e__ * n_.pow(2) * p_.pow(2) + &e__ * (&m_ + 1).pow(2);
            let denominator = b__.pow(2) * d__.pow(2) * n_.pow(2) * p_.pow(2) + (&m_ + 1).pow(2);
            let recursive_integrand = scaled_x.pow(&m_) * angle.sin().pow(&p_ - 2);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let recursive_term = rubi_simp(&(&(b__.pow(2) * d__.pow(2) * n_.pow(2) * &p_ * (&p_ - 1) / &denominator) * &recursive), x_);

            rubi_simp(&((&m_ + 1) * scaled_x.pow(&m_ + 1) * angle.sin().pow(&p_) / &denominator_with_e), x_)
                    - rubi_simp(&(&b__ * &d__ * &n_ * &p_ * scaled_x.pow(&m_ + 1) * angle.cos() * angle.sin().pow(&p_ - 1)
                        / &denominator_with_e), x_)
                    + rubi_star(Atom::num(1), recursive_term)
        },
    ));
}

fn push_rules_rule_4991(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 4991,
        source: "Int[(e_.*x_)^m_.*Cos[d_.*(a_.+b_.*Log[c_.*x_^n_.])]^p_,x_Symbol] :=
          (m+1)*(e*x)^(m+1)*Cos[d*(a+b*Log[c*x^n])]^p/(b^2*d^2*e*n^2*p^2+e*(m+1)^2) +
          b*d*n*p*(e*x)^(m+1)*Sin[d*(a+b*Log[c*x^n])]*Cos[d*(a+b*Log[c*x^n])]^(p-1)/(b^2*d^2*e*n^2*p^2+e*(m+1)^2) +
          b^2*d^2*n^2*p*(p-1)/(b^2*d^2*n^2*p^2+(m+1)^2) \\[Star] Int[(e*x)^m*Cos[d*(a+b*Log[c*x^n])]^(p-2),x] /;
        FreeQ[{a,b,c,d,e,m,n},x] && IGtQ[p,1] && NeQ[b^2*d^2*n^2*p^2+(m+1)^2,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [e__, m_, d__, a__, b__, c__, n_, p_, x_],
        optional: [e__, m_, d__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_], x_)
                && igtq!(p_, 1)
                && neq!(b__.pow(2) * d__.pow(2) * n_.pow(2) * p_.pow(2) + (&m_ + 1).pow(2), 0)
        },
        rhs: {
            let scaled_x = &e__ * x_;
            let angle = &d__ * (&a__ + &b__ * (&c__ * x_.pow(&n_)).log());
            let denominator_with_e =
                b__.pow(2) * d__.pow(2) * &e__ * n_.pow(2) * p_.pow(2) + &e__ * (&m_ + 1).pow(2);
            let denominator = b__.pow(2) * d__.pow(2) * n_.pow(2) * p_.pow(2) + (&m_ + 1).pow(2);
            let recursive_integrand = scaled_x.pow(&m_) * angle.cos().pow(&p_ - 2);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let recursive_term = rubi_simp(&(&(b__.pow(2) * d__.pow(2) * n_.pow(2) * &p_ * (&p_ - 1) / &denominator) * &recursive), x_);

            rubi_simp(&((&m_ + 1) * scaled_x.pow(&m_ + 1) * angle.cos().pow(&p_) / &denominator_with_e), x_)
                    + rubi_simp(&(&b__ * &d__ * &n_ * &p_ * scaled_x.pow(&m_ + 1) * angle.sin() * angle.cos().pow(&p_ - 1)
                        / &denominator_with_e), x_)
                    + rubi_star(Atom::num(1), recursive_term)
        },
    ));
}

fn push_rules_rule_4992(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 4992,
        source: "Int[(e_.*x_)^m_.*Sin[d_.*(a_.+b_.*Log[x_])]^p_.,x_Symbol] :=
          (m+1)^p/(2^p*b^p*d^p*p^p) \\[Star]
            Int[ExpandIntegrand[(e*x)^m*(E^(a*b*d^2*p/(m+1))*x^(-(m+1)/p)-E^(-a*b*d^2*p/(m+1))*x^((m+1)/p))^p,x],x] /;
        FreeQ[{a,b,d,e,m},x] && IGtQ[p,0] && EqQ[b^2*d^2*p^2+(m+1)^2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_11(symbols),
        with: [e__, m_, d__, a__, b__, p_, x_],
        optional: [e__, m_, d__, a__, b__, p_],
        when: {
            freeq!([a__, b__, d__, e__, m_], x_)
                && igtq!(p_, 0)
                && eqq!(b__.pow(2) * d__.pow(2) * p_.pow(2) + (&m_ + 1).pow(2), 0)
        },
        rhs: {
            let scaled_x = &e__ * x_;
            let exponent = &a__ * &b__ * d__.pow(2) * &p_ / (&m_ + 1);
            let payload = scaled_x.pow(&m_)
                * (&exponent.exp() * x_.pow(-(&m_ + 1) / &p_)
                    - (-exponent).exp() * x_.pow((&m_ + 1) / &p_))
                .pow(&p_);
            let expanded = rubi_expand_integrand(&payload, x_);
            let recursive = rubi_rhs_int(&expanded, x_);
            let coefficient = (&m_ + 1).pow(&p_)
                / (Atom::num(2).pow(&p_) * b__.pow(&p_) * d__.pow(&p_) * p_.pow(&p_));

            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_4993(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 4993,
        source: "Int[(e_.*x_)^m_.*Cos[d_.*(a_.+b_.*Log[x_])]^p_.,x_Symbol] :=
          1/2^p \\[Star] Int[ExpandIntegrand[(e*x)^m*(E^(a*b*d^2*p/(m+1))*x^(-(m+1)/p)+E^(-a*b*d^2*p/(m+1))*x^((m+1)/p))^p,x],x] /;
        FreeQ[{a,b,d,e,m},x] && IGtQ[p,0] && EqQ[b^2*d^2*p^2+(m+1)^2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [e__, m_, d__, a__, b__, p_, x_],
        optional: [e__, m_, d__, a__, b__, p_],
        when: {
            freeq!([a__, b__, d__, e__, m_], x_)
                && igtq!(p_, 0)
                && eqq!(b__.pow(2) * d__.pow(2) * p_.pow(2) + (&m_ + 1).pow(2), 0)
        },
        rhs: {
            let scaled_x = &e__ * x_;
            let exponent = &a__ * &b__ * d__.pow(2) * &p_ / (&m_ + 1);
            let payload = scaled_x.pow(&m_)
                * (&exponent.exp() * x_.pow(-(&m_ + 1) / &p_)
                    + (-exponent).exp() * x_.pow((&m_ + 1) / &p_))
                .pow(&p_);
            let expanded = rubi_expand_integrand(&payload, x_);
            let recursive = rubi_rhs_int(&expanded, x_);

            rubi_star(Atom::num(1) / Atom::num(2).pow(&p_), recursive)
        },
    ));
}

fn push_rules_rule_4994(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 4994,
        source: "Int[(e_.*x_)^m_.*Sin[d_.*(a_.+b_.*Log[x_])]^p_,x_Symbol] :=
          Sin[d*(a+b*Log[x])]^p*x^(I*b*d*p)/(1-E^(2*I*a*d)*x^(2*I*b*d))^p \\[Star]
            Int[(e*x)^m*(1-E^(2*I*a*d)*x^(2*I*b*d))^p/x^(I*b*d*p),x] /;
        FreeQ[{a,b,d,e,m,p},x] && Not[IntegerQ[p]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_11(symbols),
        with: [e__, m_, d__, a__, b__, p_, x_],
        optional: [e__, m_, d__, a__, b__],
        when: {
            freeq!([a__, b__, d__, e__, m_, p_], x_)
                && !integerq!(p_)
        },
        rhs: {
            let i = Atom::i();
            let scaled_x = &e__ * x_;
            let angle = &d__ * (&a__ + &b__ * x_.log());
            let exponential = (Atom::num(2) * &i * &a__ * &d__).exp() * x_.pow(Atom::num(2) * &i * &b__ * &d__);
            let recursive_integrand =
                scaled_x.pow(&m_) * (Atom::num(1) - &exponential).pow(&p_) / x_.pow(&i * &b__ * &d__ * &p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let coefficient = angle.sin().pow(&p_) * x_.pow(&i * &b__ * &d__ * &p_)
                / (Atom::num(1) - exponential).pow(&p_);

            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_4995(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 4995,
        source: "Int[(e_.*x_)^m_.*Cos[d_.*(a_.+b_.*Log[x_])]^p_,x_Symbol] :=
          Cos[d*(a+b*Log[x])]^p*x^(I*b*d*p)/(1+E^(2*I*a*d)*x^(2*I*b*d))^p \\[Star]
            Int[(e*x)^m*(1+E^(2*I*a*d)*x^(2*I*b*d))^p/x^(I*b*d*p),x] /;
        FreeQ[{a,b,d,e,m,p},x] && Not[IntegerQ[p]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [e__, m_, d__, a__, b__, p_, x_],
        optional: [e__, m_, d__, a__, b__],
        when: {
            freeq!([a__, b__, d__, e__, m_, p_], x_)
                && !integerq!(p_)
        },
        rhs: {
            let i = Atom::i();
            let scaled_x = &e__ * x_;
            let angle = &d__ * (&a__ + &b__ * x_.log());
            let exponential = (Atom::num(2) * &i * &a__ * &d__).exp() * x_.pow(Atom::num(2) * &i * &b__ * &d__);
            let recursive_integrand =
                scaled_x.pow(&m_) * (Atom::num(1) + &exponential).pow(&p_) / x_.pow(&i * &b__ * &d__ * &p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let coefficient = angle.cos().pow(&p_) * x_.pow(&i * &b__ * &d__ * &p_)
                / (Atom::num(1) + exponential).pow(&p_);

            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_4998(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, h__, m_, n_, q_, x_);
    rules.push(rubi_rule!(
        order: 4998,
        source: "Int[(h_.*(e_.+f_.*Log[g_.*x_^m_.]))^q_.*Sin[d_.*(a_.+b_.*Log[c_.*x_^n_.])],x_Symbol] :=
          I*E^(-I*a*d)*(c*x^n)^(-I*b*d)/(2*x^(-I*b*d*n)) \\[Star] Int[x^(-I*b*d*n)*(h*(e+f*Log[g*x^m]))^q,x] -
          I*E^(I*a*d)*(c*x^n)^(I*b*d)/(2*x^(I*b*d*n)) \\[Star] Int[x^(I*b*d*n)*(h*(e+f*Log[g*x^m]))^q,x] /;
        FreeQ[{a,b,c,d,e,f,g,h,m,n,q},x]",
        desc: "Algebraic expansion and piecewise constant extraction",
        refs: [],
        pattern: (h__ * (e__ + f__ * (g__ * x_.pow(m_)).log())).pow(q_)
            * (d__ * (a__ + b__ * (c__ * x_.pow(n_)).log())).sin(),
        with: [h__, e__, f__, g__, m_, q_, d__, a__, b__, c__, n_, x_],
        optional: [h__, e__, f__, g__, m_, q_, d__, a__, b__, c__, n_],
        when: { freeq!([a__, b__, c__, d__, e__, f__, g__, h__, m_, n_, q_], x_) },
        rhs: {
            let i = Atom::i();
            let log_power = &h__ * (&e__ + &f__ * (&g__ * x_.pow(&m_)).log());
            let c_power = &c__ * x_.pow(&n_);
            let negative_power = -&i * &b__ * &d__ * &n_;
            let positive_power = &i * &b__ * &d__ * &n_;
            let negative_integrand = x_.pow(&negative_power) * log_power.pow(&q_);
            let positive_integrand = x_.pow(&positive_power) * log_power.pow(&q_);
            let negative_recursive = rubi_rhs_int(&negative_integrand, x_);
            let positive_recursive = rubi_rhs_int(&positive_integrand, x_);
            let negative_coefficient = &i * (-&i * &a__ * &d__).exp() * c_power.pow(-&i * &b__ * &d__)
                / (Atom::num(2) * x_.pow(&negative_power));
            let positive_coefficient = -&i * (&i * &a__ * &d__).exp() * c_power.pow(&i * &b__ * &d__)
                / (Atom::num(2) * x_.pow(&positive_power));

            rubi_star(negative_coefficient, negative_recursive)
                    + rubi_star(positive_coefficient, positive_recursive)
        },
    ));
}

fn push_rules_rule_4999(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, h__, m_, n_, q_, x_);
    rules.push(rubi_rule!(
        order: 4999,
        source: "Int[(h_.*(e_.+f_.*Log[g_.*x_^m_.]))^q_.*Cos[d_.*(a_.+b_.*Log[c_.*x_^n_.])],x_Symbol] :=
          E^(-I*a*d)*(c*x^n)^(-I*b*d)/(2*x^(-I*b*d*n)) \\[Star] Int[x^(-I*b*d*n)*(h*(e+f*Log[g*x^m]))^q,x] +
          E^(I*a*d)*(c*x^n)^(I*b*d)/(2*x^(I*b*d*n)) \\[Star] Int[x^(I*b*d*n)*(h*(e+f*Log[g*x^m]))^q,x] /;
        FreeQ[{a,b,c,d,e,f,g,h,m,n,q},x]",
        desc: "Algebraic expansion and piecewise constant extraction",
        refs: [],
        pattern: (h__ * (e__ + f__ * (g__ * x_.pow(m_)).log())).pow(q_)
            * (d__ * (a__ + b__ * (c__ * x_.pow(n_)).log())).cos(),
        with: [h__, e__, f__, g__, m_, q_, d__, a__, b__, c__, n_, x_],
        optional: [h__, e__, f__, g__, m_, q_, d__, a__, b__, c__, n_],
        when: { freeq!([a__, b__, c__, d__, e__, f__, g__, h__, m_, n_, q_], x_) },
        rhs: {
            let i = Atom::i();
            let log_power = &h__ * (&e__ + &f__ * (&g__ * x_.pow(&m_)).log());
            let c_power = &c__ * x_.pow(&n_);
            let negative_power = -&i * &b__ * &d__ * &n_;
            let positive_power = &i * &b__ * &d__ * &n_;
            let negative_integrand = x_.pow(&negative_power) * log_power.pow(&q_);
            let positive_integrand = x_.pow(&positive_power) * log_power.pow(&q_);
            let negative_recursive = rubi_rhs_int(&negative_integrand, x_);
            let positive_recursive = rubi_rhs_int(&positive_integrand, x_);
            let negative_coefficient = (-&i * &a__ * &d__).exp() * c_power.pow(-&i * &b__ * &d__)
                / (Atom::num(2) * x_.pow(&negative_power));
            let positive_coefficient = (&i * &a__ * &d__).exp() * c_power.pow(&i * &b__ * &d__)
                / (Atom::num(2) * x_.pow(&positive_power));

            rubi_star(negative_coefficient, negative_recursive)
                    + rubi_star(positive_coefficient, positive_recursive)
        },
    ));
}

fn push_rules_rule_5000(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        a__, b__, c__, d__, e__, f__, g__, h__, i__, m_, n_, q_, r_, x_
    );
    rules.push(rubi_rule!(
        order: 5000,
        source: "Int[(i_.*x_)^r_.*(h_.*(e_.+f_.*Log[g_.*x_^m_.]))^q_.*Sin[d_.*(a_.+b_.*Log[c_.*x_^n_.])],x_Symbol] :=
          I*E^(-I*a*d)*(i*x)^r*(c*x^n)^(-I*b*d)/(2*x^(r-I*b*d*n)) \\[Star] Int[x^(r-I*b*d*n)*(h*(e+f*Log[g*x^m]))^q,x] -
          I*E^(I*a*d)*(i*x)^r*(c*x^n)^(I*b*d)/(2*x^(r+I*b*d*n)) \\[Star] Int[x^(r+I*b*d*n)*(h*(e+f*Log[g*x^m]))^q,x] /;
        FreeQ[{a,b,c,d,e,f,g,h,i,m,n,q,r},x]",
        desc: "Algebraic expansion and piecewise constant extraction",
        refs: [],
        pattern: (i__ * x_).pow(r_)
            * (h__ * (e__ + f__ * (g__ * x_.pow(m_)).log())).pow(q_)
            * (d__ * (a__ + b__ * (c__ * x_.pow(n_)).log())).sin(),
        with: [i__, r_, h__, e__, f__, g__, m_, q_, d__, a__, b__, c__, n_, x_],
        optional: [i__, r_, h__, e__, f__, g__, m_, q_, d__, a__, b__, c__, n_],
        when: { freeq!([a__, b__, c__, d__, e__, f__, g__, h__, i__, m_, n_, q_, r_], x_) },
        rhs: {
            let imaginary = Atom::i();
            let scaled_x = &i__ * x_;
            let log_power = &h__ * (&e__ + &f__ * (&g__ * x_.pow(&m_)).log());
            let c_power = &c__ * x_.pow(&n_);
            let negative_power = &r_ - &imaginary * &b__ * &d__ * &n_;
            let positive_power = &r_ + &imaginary * &b__ * &d__ * &n_;
            let negative_integrand = x_.pow(&negative_power) * log_power.pow(&q_);
            let positive_integrand = x_.pow(&positive_power) * log_power.pow(&q_);
            let negative_recursive = rubi_rhs_int(&negative_integrand, x_);
            let positive_recursive = rubi_rhs_int(&positive_integrand, x_);
            let negative_coefficient = &imaginary
                * (-&imaginary * &a__ * &d__).exp()
                * scaled_x.pow(&r_)
                * c_power.pow(-&imaginary * &b__ * &d__)
                / (Atom::num(2) * x_.pow(&negative_power));
            let positive_coefficient = -&imaginary
                * (&imaginary * &a__ * &d__).exp()
                * scaled_x.pow(&r_)
                * c_power.pow(&imaginary * &b__ * &d__)
                / (Atom::num(2) * x_.pow(&positive_power));

            rubi_star(negative_coefficient, negative_recursive)
                    + rubi_star(positive_coefficient, positive_recursive)
        },
    ));
}

fn push_rules_rule_5001(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        a__, b__, c__, d__, e__, f__, g__, h__, i__, m_, n_, q_, r_, x_
    );
    rules.push(rubi_rule!(
        order: 5001,
        source: "Int[(i_.*x_)^r_.*(h_.*(e_.+f_.*Log[g_.*x_^m_.]))^q_.*Cos[d_.*(a_.+b_.*Log[c_.*x_^n_.])],x_Symbol] :=
          E^(-I*a*d)*(i*x)^r*(c*x^n)^(-I*b*d)/(2*x^(r-I*b*d*n)) \\[Star] Int[x^(r-I*b*d*n)*(h*(e+f*Log[g*x^m]))^q,x] +
          E^(I*a*d)*(i*x)^r*(c*x^n)^(I*b*d)/(2*x^(r+I*b*d*n)) \\[Star] Int[x^(r+I*b*d*n)*(h*(e+f*Log[g*x^m]))^q,x] /;
        FreeQ[{a,b,c,d,e,f,g,h,i,m,n,q,r},x]",
        desc: "Algebraic expansion and piecewise constant extraction",
        refs: [],
        pattern: (i__ * x_).pow(r_)
            * (h__ * (e__ + f__ * (g__ * x_.pow(m_)).log())).pow(q_)
            * (d__ * (a__ + b__ * (c__ * x_.pow(n_)).log())).cos(),
        with: [i__, r_, h__, e__, f__, g__, m_, q_, d__, a__, b__, c__, n_, x_],
        optional: [i__, r_, h__, e__, f__, g__, m_, q_, d__, a__, b__, c__, n_],
        when: { freeq!([a__, b__, c__, d__, e__, f__, g__, h__, i__, m_, n_, q_, r_], x_) },
        rhs: {
            let imaginary = Atom::i();
            let scaled_x = &i__ * x_;
            let log_power = &h__ * (&e__ + &f__ * (&g__ * x_.pow(&m_)).log());
            let c_power = &c__ * x_.pow(&n_);
            let negative_power = &r_ - &imaginary * &b__ * &d__ * &n_;
            let positive_power = &r_ + &imaginary * &b__ * &d__ * &n_;
            let negative_integrand = x_.pow(&negative_power) * log_power.pow(&q_);
            let positive_integrand = x_.pow(&positive_power) * log_power.pow(&q_);
            let negative_recursive = rubi_rhs_int(&negative_integrand, x_);
            let positive_recursive = rubi_rhs_int(&positive_integrand, x_);
            let negative_coefficient = (-&imaginary * &a__ * &d__).exp()
                * scaled_x.pow(&r_)
                * c_power.pow(-&imaginary * &b__ * &d__)
                / (Atom::num(2) * x_.pow(&negative_power));
            let positive_coefficient = (&imaginary * &a__ * &d__).exp()
                * scaled_x.pow(&r_)
                * c_power.pow(&imaginary * &b__ * &d__)
                / (Atom::num(2) * x_.pow(&positive_power));

            rubi_star(negative_coefficient, negative_recursive)
                    + rubi_star(positive_coefficient, positive_recursive)
        },
    ));
}

fn push_rules_rule_5002(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, d__, p_, x_);
    rules.push(rubi_rule!(
        order: 5002,
        source: "Int[Tan[d_.*(a_.+b_.*Log[x_])]^p_.,x_Symbol] :=
          Int[((I-I*E^(2*I*a*d)*x^(2*I*b*d))/(1+E^(2*I*a*d)*x^(2*I*b*d)))^p,x] /;
        FreeQ[{a,b,d,p},x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (d__ * (a__ + b__ * x_.log())).tan().pow(p_),
        with: [d__, a__, b__, p_, x_],
        optional: [d__, a__, b__, p_],
        when: { freeq!([a__, b__, d__, p_], x_) },
        rhs: {
            let i = Atom::i();
            let exponential = (Atom::num(2) * &i * &a__ * &d__).exp() * x_.pow(Atom::num(2) * &i * &b__ * &d__);
            let recursive_integrand = ((&i - &i * &exponential) / (Atom::num(1) + exponential)).pow(&p_);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_5003(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, d__, p_, x_);
    rules.push(rubi_rule!(
        order: 5003,
        source: "Int[Cot[d_.*(a_.+b_.*Log[x_])]^p_.,x_Symbol] :=
          Int[((-I-I*E^(2*I*a*d)*x^(2*I*b*d))/(1-E^(2*I*a*d)*x^(2*I*b*d)))^p,x] /;
        FreeQ[{a,b,d,p},x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (d__ * (a__ + b__ * x_.log())).cot().pow(p_),
        with: [d__, a__, b__, p_, x_],
        optional: [d__, a__, b__, p_],
        when: { freeq!([a__, b__, d__, p_], x_) },
        rhs: {
            let i = Atom::i();
            let exponential = (Atom::num(2) * &i * &a__ * &d__).exp() * x_.pow(Atom::num(2) * &i * &b__ * &d__);
            let recursive_integrand = ((-&i - &i * &exponential) / (Atom::num(1) - exponential)).pow(&p_);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_5006(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 5006,
        source: "Int[(e_.*x_)^m_.*Tan[d_.*(a_.+b_.*Log[x_])]^p_.,x_Symbol] :=
          Int[(e*x)^m*((I-I*E^(2*I*a*d)*x^(2*I*b*d))/(1+E^(2*I*a*d)*x^(2*I*b*d)))^p,x] /;
        FreeQ[{a,b,d,e,m,p},x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (e__ * x_).pow(m_) * (d__ * (a__ + b__ * x_.log())).tan().pow(p_),
        with: [e__, m_, d__, a__, b__, p_, x_],
        optional: [e__, m_, d__, a__, b__, p_],
        when: { freeq!([a__, b__, d__, e__, m_, p_], x_) },
        rhs: {
            let i = Atom::i();
            let scaled_x = &e__ * x_;
            let exponential = (Atom::num(2) * &i * &a__ * &d__).exp() * x_.pow(Atom::num(2) * &i * &b__ * &d__);
            let recursive_integrand =
                scaled_x.pow(&m_) * ((&i - &i * &exponential) / (Atom::num(1) + exponential)).pow(&p_);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_5007(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 5007,
        source: "Int[(e_.*x_)^m_.*Cot[d_.*(a_.+b_.*Log[x_])]^p_.,x_Symbol] :=
          Int[(e*x)^m*((-I-I*E^(2*I*a*d)*x^(2*I*b*d))/(1-E^(2*I*a*d)*x^(2*I*b*d)))^p,x] /;
        FreeQ[{a,b,d,e,m,p},x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (e__ * x_).pow(m_) * (d__ * (a__ + b__ * x_.log())).cot().pow(p_),
        with: [e__, m_, d__, a__, b__, p_, x_],
        optional: [e__, m_, d__, a__, b__, p_],
        when: { freeq!([a__, b__, d__, e__, m_, p_], x_) },
        rhs: {
            let i = Atom::i();
            let scaled_x = &e__ * x_;
            let exponential = (Atom::num(2) * &i * &a__ * &d__).exp() * x_.pow(Atom::num(2) * &i * &b__ * &d__);
            let recursive_integrand =
                scaled_x.pow(&m_) * ((-&i - &i * &exponential) / (Atom::num(1) - exponential)).pow(&p_);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_5010(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, p_, x_);
    rules.push(rubi_rule!(
        order: 5010,
        source: "Int[Sec[d_.*(a_.+b_.*Log[x_])]^p_.,x_Symbol] :=
          2^p*E^(I*a*d*p) \\[Star] Int[x^(I*b*d*p)/(1+E^(2*I*a*d)*x^(2*I*b*d))^p,x] /;
        FreeQ[{a,b,d},x] && IntegerQ[p]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [d__, a__, b__, p_, x_],
        optional: [d__, a__, b__, p_],
        when: { freeq!([a__, b__, d__], x_) && integerq!(p_) },
        rhs: {
            let i = Atom::i();
            let exponential = (Atom::num(2) * &i * &a__ * &d__).exp() * x_.pow(Atom::num(2) * &i * &b__ * &d__);
            let power = &i * &b__ * &d__ * &p_;
            let recursive_integrand = x_.pow(&power) / (Atom::num(1) + exponential).pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            let coefficient = Atom::num(2).pow(&p_) * (&i * &a__ * &d__ * &p_).exp();

            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_5011(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, p_, x_);
    rules.push(rubi_rule!(
        order: 5011,
        source: "Int[Csc[d_.*(a_.+b_.*Log[x_])]^p_.,x_Symbol] :=
          (-2*I)^p*E^(I*a*d*p) \\[Star] Int[x^(I*b*d*p)/(1-E^(2*I*a*d)*x^(2*I*b*d))^p,x] /;
        FreeQ[{a,b,d},x] && IntegerQ[p]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [d__, a__, b__, p_, x_],
        optional: [d__, a__, b__, p_],
        when: { freeq!([a__, b__, d__], x_) && integerq!(p_) },
        rhs: {
            let i = Atom::i();
            let exponential = (Atom::num(2) * &i * &a__ * &d__).exp() * x_.pow(Atom::num(2) * &i * &b__ * &d__);
            let power = &i * &b__ * &d__ * &p_;
            let recursive_integrand = x_.pow(&power) / (Atom::num(1) - exponential).pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            let coefficient = (-Atom::num(2) * &i).pow(&p_) * (&i * &a__ * &d__ * &p_).exp();

            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_5012(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, p_, x_);
    rules.push(rubi_rule!(
        order: 5012,
        source: "Int[Sec[d_.*(a_.+b_.*Log[x_])]^p_.,x_Symbol] :=
          Sec[d*(a+b*Log[x])]^p*(1+E^(2*I*a*d)*x^(2*I*b*d))^p/x^(I*b*d*p) \\[Star]
            Int[x^(I*b*d*p)/(1+E^(2*I*a*d)*x^(2*I*b*d))^p,x] /;
        FreeQ[{a,b,d,p},x] && Not[IntegerQ[p]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [d__, a__, b__, p_, x_],
        optional: [d__, a__, b__, p_],
        when: { freeq!([a__, b__, d__, p_], x_) && !integerq!(p_) },
        rhs: {
            let i = Atom::i();
            let angle = &d__ * (&a__ + &b__ * x_.log());
            let exponential = (Atom::num(2) * &i * &a__ * &d__).exp() * x_.pow(Atom::num(2) * &i * &b__ * &d__);
            let power = &i * &b__ * &d__ * &p_;
            let recursive_integrand = x_.pow(&power) / (Atom::num(1) + &exponential).pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let coefficient = angle.sec().pow(&p_) * (Atom::num(1) + exponential).pow(&p_)
                / x_.pow(&power);

            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_5013(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, p_, x_);
    rules.push(rubi_rule!(
        order: 5013,
        source: "Int[Csc[d_.*(a_.+b_.*Log[x_])]^p_.,x_Symbol] :=
          Csc[d*(a+b*Log[x])]^p*(1-E^(2*I*a*d)*x^(2*I*b*d))^p/x^(I*b*d*p) \\[Star]
            Int[x^(I*b*d*p)/(1-E^(2*I*a*d)*x^(2*I*b*d))^p,x] /;
        FreeQ[{a,b,d,p},x] && Not[IntegerQ[p]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [d__, a__, b__, p_, x_],
        optional: [d__, a__, b__, p_],
        when: { freeq!([a__, b__, d__, p_], x_) && !integerq!(p_) },
        rhs: {
            let i = Atom::i();
            let angle = &d__ * (&a__ + &b__ * x_.log());
            let exponential = (Atom::num(2) * &i * &a__ * &d__).exp() * x_.pow(Atom::num(2) * &i * &b__ * &d__);
            let power = &i * &b__ * &d__ * &p_;
            let recursive_integrand = x_.pow(&power) / (Atom::num(1) - &exponential).pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let coefficient = angle.csc().pow(&p_) * (Atom::num(1) - exponential).pow(&p_)
                / x_.pow(&power);

            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_5016(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 5016,
        source: "Int[(e_.*x_)^m_.*Sec[d_.*(a_.+b_.*Log[x_])]^p_.,x_Symbol] :=
          2^p*E^(I*a*d*p) \\[Star] Int[(e*x)^m*x^(I*b*d*p)/(1+E^(2*I*a*d)*x^(2*I*b*d))^p,x] /;
        FreeQ[{a,b,d,e,m},x] && IntegerQ[p]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_10(symbols),
        with: [e__, m_, d__, a__, b__, p_, x_],
        optional: [e__, m_, d__, a__, b__, p_],
        when: { freeq!([a__, b__, d__, e__, m_], x_) && integerq!(p_) },
        rhs: {
            let i = Atom::i();
            let scaled_x = &e__ * x_;
            let exponential = (Atom::num(2) * &i * &a__ * &d__).exp() * x_.pow(Atom::num(2) * &i * &b__ * &d__);
            let power = &i * &b__ * &d__ * &p_;
            let recursive_integrand = scaled_x.pow(&m_) * x_.pow(&power) / (Atom::num(1) + exponential).pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            let coefficient = Atom::num(2).pow(&p_) * (&i * &a__ * &d__ * &p_).exp();

            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_5017(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 5017,
        source: "Int[(e_.*x_)^m_.*Csc[d_.*(a_.+b_.*Log[x_])]^p_.,x_Symbol] :=
          (-2*I)^p*E^(I*a*d*p) \\[Star] Int[(e*x)^m*x^(I*b*d*p)/(1-E^(2*I*a*d)*x^(2*I*b*d))^p,x] /;
        FreeQ[{a,b,d,e,m},x] && IntegerQ[p]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [e__, m_, d__, a__, b__, p_, x_],
        optional: [e__, m_, d__, a__, b__, p_],
        when: { freeq!([a__, b__, d__, e__, m_], x_) && integerq!(p_) },
        rhs: {
            let i = Atom::i();
            let scaled_x = &e__ * x_;
            let exponential = (Atom::num(2) * &i * &a__ * &d__).exp() * x_.pow(Atom::num(2) * &i * &b__ * &d__);
            let power = &i * &b__ * &d__ * &p_;
            let recursive_integrand = scaled_x.pow(&m_) * x_.pow(&power) / (Atom::num(1) - exponential).pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            let coefficient = (-Atom::num(2) * &i).pow(&p_) * (&i * &a__ * &d__ * &p_).exp();

            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_5018(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 5018,
        source: "Int[(e_.*x_)^m_.*Sec[d_.*(a_.+b_.*Log[x_])]^p_.,x_Symbol] :=
          Sec[d*(a+b*Log[x])]^p*(1+E^(2*I*a*d)*x^(2*I*b*d))^p/x^(I*b*d*p) \\[Star]
            Int[(e*x)^m*x^(I*b*d*p)/(1+E^(2*I*a*d)*x^(2*I*b*d))^p,x] /;
        FreeQ[{a,b,d,e,m,p},x] && Not[IntegerQ[p]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_10(symbols),
        with: [e__, m_, d__, a__, b__, p_, x_],
        optional: [e__, m_, d__, a__, b__, p_],
        when: { freeq!([a__, b__, d__, e__, m_, p_], x_) && !integerq!(p_) },
        rhs: {
            let i = Atom::i();
            let scaled_x = &e__ * x_;
            let angle = &d__ * (&a__ + &b__ * x_.log());
            let exponential = (Atom::num(2) * &i * &a__ * &d__).exp() * x_.pow(Atom::num(2) * &i * &b__ * &d__);
            let power = &i * &b__ * &d__ * &p_;
            let recursive_integrand =
                scaled_x.pow(&m_) * x_.pow(&power) / (Atom::num(1) + &exponential).pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let coefficient = angle.sec().pow(&p_) * (Atom::num(1) + exponential).pow(&p_)
                / x_.pow(&power);

            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_5019(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 5019,
        source: "Int[(e_.*x_)^m_.*Csc[d_.*(a_.+b_.*Log[x_])]^p_.,x_Symbol] :=
          Csc[d*(a+b*Log[x])]^p*(1-E^(2*I*a*d)*x^(2*I*b*d))^p/x^(I*b*d*p) \\[Star]
            Int[(e*x)^m*x^(I*b*d*p)/(1-E^(2*I*a*d)*x^(2*I*b*d))^p,x] /;
        FreeQ[{a,b,d,e,m,p},x] && Not[IntegerQ[p]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [e__, m_, d__, a__, b__, p_, x_],
        optional: [e__, m_, d__, a__, b__, p_],
        when: { freeq!([a__, b__, d__, e__, m_, p_], x_) && !integerq!(p_) },
        rhs: {
            let i = Atom::i();
            let scaled_x = &e__ * x_;
            let angle = &d__ * (&a__ + &b__ * x_.log());
            let exponential = (Atom::num(2) * &i * &a__ * &d__).exp() * x_.pow(Atom::num(2) * &i * &b__ * &d__);
            let power = &i * &b__ * &d__ * &p_;
            let recursive_integrand =
                scaled_x.pow(&m_) * x_.pow(&power) / (Atom::num(1) - &exponential).pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let coefficient = angle.csc().pow(&p_) * (Atom::num(1) - exponential).pow(&p_)
                / x_.pow(&power);

            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_5022(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, x_);
    rules.push(rubi_rule!(
        order: 5022,
        source: "Int[Sin[a_.*x_*Log[b_.*x_]]*Log[b_.*x_],x_Symbol] :=
          -Cos[a*x*Log[b*x]]/a - Int[Sin[a*x*Log[b*x]],x] /;
        FreeQ[{a,b},x]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern: (a__ * x_ * (b__ * x_).log()).sin() * (b__ * x_).log(),
        with: [a__, b__, x_],
        optional: [a__, b__],
        when: { freeq!([a__, b__], x_) },
        rhs: {
            let angle = &a__ * x_ * (&b__ * x_).log();
            let recursive = rubi_rhs_int(&angle.sin(), x_);

            rubi_simp(&(-angle.cos() / &a__), x_) - recursive
        },
    ));
}

fn push_rules_rule_5023(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, x_);
    rules.push(rubi_rule!(
        order: 5023,
        source: "Int[Cos[a_.*x_*Log[b_.*x_]]*Log[b_.*x_],x_Symbol] :=
          Sin[a*x*Log[b*x]]/a - Int[Cos[a*x*Log[b*x]],x] /;
        FreeQ[{a,b},x]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern: (a__ * x_ * (b__ * x_).log()).cos() * (b__ * x_).log(),
        with: [a__, b__, x_],
        optional: [a__, b__],
        when: { freeq!([a__, b__], x_) },
        rhs: {
            let angle = &a__ * x_ * (&b__ * x_).log();
            let recursive = rubi_rhs_int(&angle.cos(), x_);

            rubi_simp(&(angle.sin() / &a__), x_) - recursive
        },
    ));
}

fn push_rules_rule_5024(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5024,
        source: "Int[x_^m_.*Sin[a_.*x_^n_.*Log[b_.*x_]]*Log[b_.*x_],x_Symbol] :=
          -Cos[a*x^n*Log[b*x]]/(a*n) - 1/n \\[Star] Int[x^m*Sin[a*x^n*Log[b*x]],x] /;
        FreeQ[{a,b,m,n},x] && EqQ[m,n-1]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern: x_.pow(m_) * (a__ * x_.pow(n_) * (b__ * x_).log()).sin() * (b__ * x_).log(),
        with: [m_, a__, n_, b__, x_],
        optional: [m_, a__, b__, n_],
        when: { freeq!([a__, b__, m_, n_], x_) && eqq!(m_, &n_ - 1) },
        rhs: {
            let angle = &a__ * x_.pow(&n_) * (&b__ * x_).log();
            let recursive_integrand = x_.pow(&m_) * angle.sin();
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(-angle.cos() / (&a__ * &n_)), x_)
                    + rubi_star(-Atom::num(1) / &n_, recursive)
        },
    ));
}

fn push_rules_rule_5025(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 5025,
        source: "Int[x_^m_.*Cos[a_.*x_^n_.*Log[b_.*x_]]*Log[b_.*x_],x_Symbol] :=
          Sin[a*x^n*Log[b*x]]/(a*n) - 1/n \\[Star] Int[x^m*Cos[a*x^n*Log[b*x]],x] /;
        FreeQ[{a,b,m,n},x] && EqQ[m,n-1]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern: x_.pow(m_) * (a__ * x_.pow(n_) * (b__ * x_).log()).cos() * (b__ * x_).log(),
        with: [m_, a__, n_, b__, x_],
        optional: [m_, a__, b__, n_],
        when: { freeq!([a__, b__, m_, n_], x_) && eqq!(m_, &n_ - 1) },
        rhs: {
            let angle = &a__ * x_.pow(&n_) * (&b__ * x_).log();
            let recursive_integrand = x_.pow(&m_) * angle.cos();
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(angle.sin() / (&a__ * &n_)), x_)
                    + rubi_star(-Atom::num(1) / &n_, recursive)
        },
    ));
}

fn push_rules_rule_4996(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 4996,
        source: "Int[(e_.*x_)^m_.*Sin[d_.*(a_.+b_.*Log[c_.*x_^n_.])]^p_.,x_Symbol] :=
          (e*x)^(m+1)/(e*n*(c*x^n)^((m+1)/n)) \\[Star] Subst[Int[x^((m+1)/n-1)*Sin[d*(a+b*Log[x])]^p,x],x,c*x^n] /;
        FreeQ[{a,b,c,d,e,m,n,p},x] && (NeQ[c,1] || NeQ[n,1])",
        desc: "Piecewise constant extraction and integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [e__, m_, d__, a__, b__, c__, n_, p_, x_],
        optional: [e__, m_, d__, a__, b__, c__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_, p_], x_)
                && (neq!(c__, 1) || neq!(n_, 1))
        },
        rhs: {
            let scaled_x = &e__ * x_;
            let exponent = (&m_ + 1) / &n_;
            let recursive_integrand = x_.pow(&exponent - 1)
                * (&d__ * (&a__ + &b__ * x_.log())).sin().pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let replacement = &c__ * x_.pow(&n_);
            let substituted = rubi_subst(&recursive, x_, &replacement);
            let coefficient = scaled_x.pow(&m_ + 1) / (&e__ * &n_ * replacement.pow(exponent));

            rubi_star(coefficient, substituted)
        },
    ));
}

fn push_rules_rule_4997(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 4997,
        source: "Int[(e_.*x_)^m_.*Cos[d_.*(a_.+b_.*Log[c_.*x_^n_.])]^p_.,x_Symbol] :=
          (e*x)^(m+1)/(e*n*(c*x^n)^((m+1)/n)) \\[Star] Subst[Int[x^((m+1)/n-1)*Cos[d*(a+b*Log[x])]^p,x],x,c*x^n] /;
        FreeQ[{a,b,c,d,e,m,n,p},x] && (NeQ[c,1] || NeQ[n,1])",
        desc: "Piecewise constant extraction and integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [e__, m_, d__, a__, b__, c__, n_, p_, x_],
        optional: [e__, m_, d__, a__, b__, c__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_, p_], x_)
                && (neq!(c__, 1) || neq!(n_, 1))
        },
        rhs: {
            let scaled_x = &e__ * x_;
            let exponent = (&m_ + 1) / &n_;
            let recursive_integrand = x_.pow(&exponent - 1)
                * (&d__ * (&a__ + &b__ * x_.log())).cos().pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let replacement = &c__ * x_.pow(&n_);
            let substituted = rubi_subst(&recursive, x_, &replacement);
            let coefficient = scaled_x.pow(&m_ + 1) / (&e__ * &n_ * replacement.pow(exponent));

            rubi_star(coefficient, substituted)
        },
    ));
}

fn push_rules_rule_5004(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5004,
        source: "Int[Tan[d_.*(a_.+b_.*Log[c_.*x_^n_.])]^p_.,x_Symbol] :=
          x/(n*(c*x^n)^(1/n)) \\[Star] Subst[Int[x^(1/n-1)*Tan[d*(a+b*Log[x])]^p,x],x,c*x^n] /;
        FreeQ[{a,b,c,d,n,p},x] && (NeQ[c,1] || NeQ[n,1])",
        desc: "Piecewise constant extraction and integration by substitution",
        refs: [],
        pattern: (d__ * (a__ + b__ * (c__ * x_.pow(n_)).log())).tan().pow(p_),
        with: [d__, a__, b__, c__, n_, p_, x_],
        optional: [d__, a__, b__, c__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, n_, p_], x_)
                && (neq!(c__, 1) || neq!(n_, 1))
        },
        rhs: {
            let recursive_integrand = x_.pow(Atom::num(1) / &n_ - 1)
                * (&d__ * (&a__ + &b__ * x_.log())).tan().pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let replacement = &c__ * x_.pow(&n_);
            let substituted = rubi_subst(&recursive, x_, &replacement);
            let coefficient = x_ / (&n_ * replacement.pow(Atom::num(1) / &n_));

            rubi_star(coefficient, substituted)
        },
    ));
}

fn push_rules_rule_5005(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5005,
        source: "Int[Cot[d_.*(a_.+b_.*Log[c_.*x_^n_.])]^p_.,x_Symbol] :=
          x/(n*(c*x^n)^(1/n)) \\[Star] Subst[Int[x^(1/n-1)*Cot[d*(a+b*Log[x])]^p,x],x,c*x^n] /;
        FreeQ[{a,b,c,d,n,p},x] && (NeQ[c,1] || NeQ[n,1])",
        desc: "Piecewise constant extraction and integration by substitution",
        refs: [],
        pattern: (d__ * (a__ + b__ * (c__ * x_.pow(n_)).log())).cot().pow(p_),
        with: [d__, a__, b__, c__, n_, p_, x_],
        optional: [d__, a__, b__, c__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, n_, p_], x_)
                && (neq!(c__, 1) || neq!(n_, 1))
        },
        rhs: {
            let recursive_integrand = x_.pow(Atom::num(1) / &n_ - 1)
                * (&d__ * (&a__ + &b__ * x_.log())).cot().pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let replacement = &c__ * x_.pow(&n_);
            let substituted = rubi_subst(&recursive, x_, &replacement);
            let coefficient = x_ / (&n_ * replacement.pow(Atom::num(1) / &n_));

            rubi_star(coefficient, substituted)
        },
    ));
}

fn push_rules_rule_5008(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5008,
        source: "Int[(e_.*x_)^m_.*Tan[d_.*(a_.+b_.*Log[c_.*x_^n_.])]^p_.,x_Symbol] :=
          (e*x)^(m+1)/(e*n*(c*x^n)^((m+1)/n)) \\[Star] Subst[Int[x^((m+1)/n-1)*Tan[d*(a+b*Log[x])]^p,x],x,c*x^n] /;
        FreeQ[{a,b,c,d,e,m,n,p},x] && (NeQ[c,1] || NeQ[n,1])",
        desc: "Piecewise constant extraction and integration by substitution",
        refs: [],
        pattern: (e__ * x_).pow(m_) * (d__ * (a__ + b__ * (c__ * x_.pow(n_)).log())).tan().pow(p_),
        with: [e__, m_, d__, a__, b__, c__, n_, p_, x_],
        optional: [e__, m_, d__, a__, b__, c__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_, p_], x_)
                && (neq!(c__, 1) || neq!(n_, 1))
        },
        rhs: {
            let scaled_x = &e__ * x_;
            let exponent = (&m_ + 1) / &n_;
            let recursive_integrand = x_.pow(&exponent - 1)
                * (&d__ * (&a__ + &b__ * x_.log())).tan().pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let replacement = &c__ * x_.pow(&n_);
            let substituted = rubi_subst(&recursive, x_, &replacement);
            let coefficient = scaled_x.pow(&m_ + 1) / (&e__ * &n_ * replacement.pow(exponent));

            rubi_star(coefficient, substituted)
        },
    ));
}

fn push_rules_rule_5009(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5009,
        source: "Int[(e_.*x_)^m_.*Cot[d_.*(a_.+b_.*Log[c_.*x_^n_.])]^p_.,x_Symbol] :=
          (e*x)^(m+1)/(e*n*(c*x^n)^((m+1)/n)) \\[Star] Subst[Int[x^((m+1)/n-1)*Cot[d*(a+b*Log[x])]^p,x],x,c*x^n] /;
        FreeQ[{a,b,c,d,e,m,n,p},x] && (NeQ[c,1] || NeQ[n,1])",
        desc: "Piecewise constant extraction and integration by substitution",
        refs: [],
        pattern: (e__ * x_).pow(m_) * (d__ * (a__ + b__ * (c__ * x_.pow(n_)).log())).cot().pow(p_),
        with: [e__, m_, d__, a__, b__, c__, n_, p_, x_],
        optional: [e__, m_, d__, a__, b__, c__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_, p_], x_)
                && (neq!(c__, 1) || neq!(n_, 1))
        },
        rhs: {
            let scaled_x = &e__ * x_;
            let exponent = (&m_ + 1) / &n_;
            let recursive_integrand = x_.pow(&exponent - 1)
                * (&d__ * (&a__ + &b__ * x_.log())).cot().pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let replacement = &c__ * x_.pow(&n_);
            let substituted = rubi_subst(&recursive, x_, &replacement);
            let coefficient = scaled_x.pow(&m_ + 1) / (&e__ * &n_ * replacement.pow(exponent));

            rubi_star(coefficient, substituted)
        },
    ));
}

fn push_rules_rule_5014(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5014,
        source: "Int[Sec[d_.*(a_.+b_.*Log[c_.*x_^n_.])]^p_.,x_Symbol] :=
          x/(n*(c*x^n)^(1/n)) \\[Star] Subst[Int[x^(1/n-1)*Sec[d*(a+b*Log[x])]^p,x],x,c*x^n] /;
        FreeQ[{a,b,c,d,n,p},x] && (NeQ[c,1] || NeQ[n,1])",
        desc: "Piecewise constant extraction and integration by substitution",
        refs: [],
        pattern: (d__ * (a__ + b__ * (c__ * x_.pow(n_)).log())).sec().pow(p_),
        with: [d__, a__, b__, c__, n_, p_, x_],
        optional: [d__, a__, b__, c__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, n_, p_], x_)
                && (neq!(c__, 1) || neq!(n_, 1))
        },
        rhs: {
            let recursive_integrand = x_.pow(Atom::num(1) / &n_ - 1)
                * (&d__ * (&a__ + &b__ * x_.log())).sec().pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let replacement = &c__ * x_.pow(&n_);
            let substituted = rubi_subst(&recursive, x_, &replacement);
            let coefficient = x_ / (&n_ * replacement.pow(Atom::num(1) / &n_));

            rubi_star(coefficient, substituted)
        },
    ));
}

fn push_rules_rule_5015(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5015,
        source: "Int[Csc[d_.*(a_.+b_.*Log[c_.*x_^n_.])]^p_.,x_Symbol] :=
          x/(n*(c*x^n)^(1/n)) \\[Star] Subst[Int[x^(1/n-1)*Csc[d*(a+b*Log[x])]^p,x],x,c*x^n] /;
        FreeQ[{a,b,c,d,n,p},x] && (NeQ[c,1] || NeQ[n,1])",
        desc: "Piecewise constant extraction and integration by substitution",
        refs: [],
        pattern: (d__ * (a__ + b__ * (c__ * x_.pow(n_)).log())).csc().pow(p_),
        with: [d__, a__, b__, c__, n_, p_, x_],
        optional: [d__, a__, b__, c__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, n_, p_], x_)
                && (neq!(c__, 1) || neq!(n_, 1))
        },
        rhs: {
            let recursive_integrand = x_.pow(Atom::num(1) / &n_ - 1)
                * (&d__ * (&a__ + &b__ * x_.log())).csc().pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let replacement = &c__ * x_.pow(&n_);
            let substituted = rubi_subst(&recursive, x_, &replacement);
            let coefficient = x_ / (&n_ * replacement.pow(Atom::num(1) / &n_));

            rubi_star(coefficient, substituted)
        },
    ));
}

fn push_rules_rule_5020(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5020,
        source: "Int[(e_.*x_)^m_.*Sec[d_.*(a_.+b_.*Log[c_.*x_^n_.])]^p_.,x_Symbol] :=
          (e*x)^(m+1)/(e*n*(c*x^n)^((m+1)/n)) \\[Star] Subst[Int[x^((m+1)/n-1)*Sec[d*(a+b*Log[x])]^p,x],x,c*x^n] /;
        FreeQ[{a,b,c,d,e,m,n,p},x] && (NeQ[c,1] || NeQ[n,1])",
        desc: "Piecewise constant extraction and integration by substitution",
        refs: [],
        pattern: (e__ * x_).pow(m_) * (d__ * (a__ + b__ * (c__ * x_.pow(n_)).log())).sec().pow(p_),
        with: [e__, m_, d__, a__, b__, c__, n_, p_, x_],
        optional: [e__, m_, d__, a__, b__, c__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_, p_], x_)
                && (neq!(c__, 1) || neq!(n_, 1))
        },
        rhs: {
            let scaled_x = &e__ * x_;
            let exponent = (&m_ + 1) / &n_;
            let recursive_integrand = x_.pow(&exponent - 1)
                * (&d__ * (&a__ + &b__ * x_.log())).sec().pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let replacement = &c__ * x_.pow(&n_);
            let substituted = rubi_subst(&recursive, x_, &replacement);
            let coefficient = scaled_x.pow(&m_ + 1) / (&e__ * &n_ * replacement.pow(exponent));

            rubi_star(coefficient, substituted)
        },
    ));
}

fn push_rules_rule_5021(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 5021,
        source: "Int[(e_.*x_)^m_.*Csc[d_.*(a_.+b_.*Log[c_.*x_^n_.])]^p_.,x_Symbol] :=
          (e*x)^(m+1)/(e*n*(c*x^n)^((m+1)/n)) \\[Star] Subst[Int[x^((m+1)/n-1)*Csc[d*(a+b*Log[x])]^p,x],x,c*x^n] /;
        FreeQ[{a,b,c,d,e,m,n,p},x] && (NeQ[c,1] || NeQ[n,1])",
        desc: "Piecewise constant extraction and integration by substitution",
        refs: [],
        pattern: (e__ * x_).pow(m_) * (d__ * (a__ + b__ * (c__ * x_.pow(n_)).log())).csc().pow(p_),
        with: [e__, m_, d__, a__, b__, c__, n_, p_, x_],
        optional: [e__, m_, d__, a__, b__, c__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_, p_], x_)
                && (neq!(c__, 1) || neq!(n_, 1))
        },
        rhs: {
            let scaled_x = &e__ * x_;
            let exponent = (&m_ + 1) / &n_;
            let recursive_integrand = x_.pow(&exponent - 1)
                * (&d__ * (&a__ + &b__ * x_.log())).csc().pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let replacement = &c__ * x_.pow(&n_);
            let substituted = rubi_subst(&recursive, x_, &replacement);
            let coefficient = scaled_x.pow(&m_ + 1) / (&e__ * &n_ * replacement.pow(exponent));

            rubi_star(coefficient, substituted)
        },
    ));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn downvalues_4978_through_4992_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .filter(|order| (4978..=4992).contains(order))
            .collect::<Vec<_>>();
        assert_eq!(orders, (4978..=4992).collect::<Vec<_>>());
    }

    #[test]
    fn downvalues_4993_through_5025_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .filter(|order| (4993..=5025).contains(order))
            .collect::<Vec<_>>();
        assert_eq!(orders, (4993..=5025).collect::<Vec<_>>());
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
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (d__ * (a__ + b__ * (c__ * x_.pow(n_)).log())).cos().pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (d__ * (a__ + b__ * (c__ * x_.pow(n_)).log())).sin().pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_2(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let d__ = symbols.d__;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (d__ * (a__ + b__ * x_.log())).cos().pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_3(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let d__ = symbols.d__;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (d__ * (a__ + b__ * x_.log())).csc().pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_4(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let d__ = symbols.d__;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (d__ * (a__ + b__ * x_.log())).sec().pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_5(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let d__ = symbols.d__;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (d__ * (a__ + b__ * x_.log())).sin().pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_6(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (e__ * x_).pow(m_) * (d__ * (a__ + b__ * (c__ * x_.pow(n_)).log())).cos().pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_7(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (e__ * x_).pow(m_) * (d__ * (a__ + b__ * (c__ * x_.pow(n_)).log())).sin().pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_8(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let m_ = symbols.m_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (e__ * x_).pow(m_) * (d__ * (a__ + b__ * x_.log())).cos().pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_9(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let m_ = symbols.m_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (e__ * x_).pow(m_) * (d__ * (a__ + b__ * x_.log())).csc().pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_10(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let m_ = symbols.m_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (e__ * x_).pow(m_) * (d__ * (a__ + b__ * x_.log())).sec().pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_11(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let m_ = symbols.m_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (e__ * x_).pow(m_) * (d__ * (a__ + b__ * x_.log())).sin().pow(p_)
}
