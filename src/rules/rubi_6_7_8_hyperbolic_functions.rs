use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_6041(rules);
    push_rules_rule_6042(rules);
    push_rules_rule_6043(rules);
    push_rules_rule_6044(rules);
    push_rules_rule_6045(rules);
    push_rules_rule_6046(rules);
    push_rules_rule_6047(rules);
    push_rules_rule_6048(rules);
    push_rules_rule_6049(rules);
    push_rules_rule_6050(rules);
    push_rules_rule_6051(rules);
    push_rules_rule_6052(rules);
    push_rules_rule_6053(rules);
    push_rules_rule_6054(rules);
    push_rules_rule_6055(rules);
    push_rules_rule_6056(rules);
    push_rules_rule_6057(rules);
    push_rules_rule_6058(rules);
    push_rules_rule_6059(rules);
    push_rules_rule_6060(rules);
    push_rules_rule_6061(rules);
    push_rules_rule_6062(rules);
    push_rules_rule_6063(rules);
    push_rules_rule_6064(rules);
    push_rules_rule_6065(rules);
    push_rules_rule_6066(rules);
    push_rules_rule_6067(rules);
    push_rules_rule_6068(rules);
    push_rules_rule_6069(rules);
    push_rules_rule_6070(rules);
    push_rules_rule_6071(rules);
    push_rules_rule_6072(rules);
    push_rules_rule_6073(rules);
    push_rules_rule_6074(rules);
    push_rules_rule_6075(rules);
    push_rules_rule_6076(rules);
    push_rules_rule_6077(rules);
    push_rules_rule_6078(rules);
    push_rules_rule_6079(rules);
    push_rules_rule_6080(rules);
    push_rules_rule_6081(rules);
    push_rules_rule_6082(rules);
    push_rules_rule_6083(rules);
    push_rules_rule_6084(rules);
    push_rules_rule_6085(rules);
    push_rules_rule_6086(rules);
    push_rules_rule_6087(rules);
    push_rules_rule_6088(rules);
    push_rules_rule_6089(rules);
    push_rules_rule_6090(rules);
}

fn push_rules_rule_6041(rules: &mut Vec<RubiRule>) {
    rubi_symb!(b__, c__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6041,
        source: "Int[Sinh[b_.*Log[c_.*x_^n_.]]^p_.,x_Symbol] :=
          Int[((c*x^n)^b/2 - 1/(2*(c*x^n)^b))^p,x] /;
        FreeQ[c,x] && RationalQ[b,n,p]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: (b__ * (c__ * x_.pow(n_)).log()).sinh().pow(p_),
        with: [b__, c__, n_, p_, x_],
        optional: [b__, c__, n_, p_],
        when: { freeq!(c__, x_) && rationalq!([b__, n_, p_]) },
        rhs: {
            let powered = (&c__ * x_.pow(&n_)).pow(&b__);
            let transformed = (&powered / 2 - Atom::num(1) / (Atom::num(2) * powered)).pow(&p_);

            rubi_rhs_int(&transformed, x_)
        },
    ));
}

fn push_rules_rule_6042(rules: &mut Vec<RubiRule>) {
    rubi_symb!(b__, c__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6042,
        source: "Int[Cosh[b_.*Log[c_.*x_^n_.]]^p_.,x_Symbol] :=
          Int[((c*x^n)^b/2 + 1/(2*(c*x^n)^b))^p,x] /;
        FreeQ[c,x] && RationalQ[b,n,p]",
        desc: "Algebraic simplification",
        refs: [],
        pattern: (b__ * (c__ * x_.pow(n_)).log()).cosh().pow(p_),
        with: [b__, c__, n_, p_, x_],
        optional: [b__, c__, n_, p_],
        when: { freeq!(c__, x_) && rationalq!([b__, n_, p_]) },
        rhs: {
            let powered = (&c__ * x_.pow(&n_)).pow(&b__);
            let transformed = (&powered / 2 + Atom::num(1) / (Atom::num(2) * powered)).pow(&p_);

            rubi_rhs_int(&transformed, x_)
        },
    ));
}

fn push_rules_rule_6043(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 6043,
        source: "Int[Sinh[d_.*(a_.+b_.*Log[c_.*x_^n_.])],x_Symbol] :=
          -x*Sinh[d*(a+b*Log[c*x^n])]/(b^2*d^2*n^2-1) +
          b*d*n*x*Cosh[d*(a+b*Log[c*x^n])]/(b^2*d^2*n^2-1) /;
        FreeQ[{a,b,c,d,n},x] && NeQ[b^2*d^2*n^2-1,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: (d__ * (a__ + b__ * (c__ * x_.pow(n_)).log())).sinh(),
        with: [d__, a__, b__, c__, n_, x_],
        optional: [d__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, n_], x_)
                && neq!(b__.pow(2) * d__.pow(2) * n_.pow(2) - 1, 0)
        },
        rhs: {
            let angle = &d__ * (&a__ + &b__ * (&c__ * x_.pow(&n_)).log());
            let denominator = b__.pow(2) * d__.pow(2) * n_.pow(2) - 1;

            rubi_simp(&(Atom::num(-1) * x_ * angle.sinh() / &denominator), x_)
                    + rubi_simp(&(&b__ * &d__ * &n_ * x_ * angle.cosh() / denominator), x_)
        },
    ));
}

fn push_rules_rule_6044(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 6044,
        source: "Int[Cosh[d_.*(a_.+b_.*Log[c_.*x_^n_.])],x_Symbol] :=
          -x*Cosh[d*(a+b*Log[c*x^n])]/(b^2*d^2*n^2-1) +
          b*d*n*x*Sinh[d*(a+b*Log[c*x^n])]/(b^2*d^2*n^2-1) /;
        FreeQ[{a,b,c,d,n},x] && NeQ[b^2*d^2*n^2-1,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: (d__ * (a__ + b__ * (c__ * x_.pow(n_)).log())).cosh(),
        with: [d__, a__, b__, c__, n_, x_],
        optional: [d__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, n_], x_)
                && neq!(b__.pow(2) * d__.pow(2) * n_.pow(2) - 1, 0)
        },
        rhs: {
            let angle = &d__ * (&a__ + &b__ * (&c__ * x_.pow(&n_)).log());
            let denominator = b__.pow(2) * d__.pow(2) * n_.pow(2) - 1;

            rubi_simp(&(Atom::num(-1) * x_ * angle.cosh() / &denominator), x_)
                    + rubi_simp(&(&b__ * &d__ * &n_ * x_ * angle.sinh() / denominator), x_)
        },
    ));
}

fn push_rules_rule_6045(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6045,
        source: "Int[Sinh[d_.*(a_.+b_.*Log[c_.*x_^n_.])]^p_,x_Symbol] :=
          -x*Sinh[d*(a+b*Log[c*x^n])]^p/(b^2*d^2*n^2*p^2-1) +
          b*d*n*p*x*Cosh[d*(a+b*Log[c*x^n])]*Sinh[d*(a+b*Log[c*x^n])]^(p-1)/(b^2*d^2*n^2*p^2-1) -
          b^2*d^2*n^2*p*(p-1)/(b^2*d^2*n^2*p^2-1) \\[Star] Int[Sinh[d*(a+b*Log[c*x^n])]^(p-2),x] /;
        FreeQ[{a,b,c,d,n},x] && IGtQ[p,1] && NeQ[b^2*d^2*n^2*p^2-1,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [d__, a__, b__, c__, n_, p_, x_],
        optional: [d__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, n_], x_)
                && igtq!(p_, 1)
                && neq!(b__.pow(2) * d__.pow(2) * n_.pow(2) * p_.pow(2) - 1, 0)
        },
        rhs: {
            let angle = &d__ * (&a__ + &b__ * (&c__ * x_.pow(&n_)).log());
            let denominator = b__.pow(2) * d__.pow(2) * n_.pow(2) * p_.pow(2) - 1;
            let recursive = rubi_rhs_int(&angle.sinh().pow(&p_ - 2), x_);

            rubi_simp(&(Atom::num(-1) * x_ * angle.sinh().pow(&p_) / &denominator), x_)
                    + rubi_simp(&(&b__ * &d__ * &n_ * &p_ * x_ * angle.cosh() * angle.sinh().pow(&p_ - 1)
                        / &denominator), x_)
                    - rubi_star(b__.pow(2) * d__.pow(2) * n_.pow(2) * &p_ * (&p_ - 1) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_6046(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6046,
        source: "Int[Cosh[d_.*(a_.+b_.*Log[c_.*x_^n_.])]^p_,x_Symbol] :=
          -x*Cosh[d*(a+b*Log[c*x^n])]^p/(b^2*d^2*n^2*p^2-1) +
          b*d*n*p*x*Cosh[d*(a+b*Log[c*x^n])]^(p-1)*Sinh[d*(a+b*Log[c*x^n])]/(b^2*d^2*n^2*p^2-1) +
          b^2*d^2*n^2*p*(p-1)/(b^2*d^2*n^2*p^2-1) \\[Star] Int[Cosh[d*(a+b*Log[c*x^n])]^(p-2),x] /;
        FreeQ[{a,b,c,d,n},x] && IGtQ[p,1] && NeQ[b^2*d^2*n^2*p^2-1,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [d__, a__, b__, c__, n_, p_, x_],
        optional: [d__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, n_], x_)
                && igtq!(p_, 1)
                && neq!(b__.pow(2) * d__.pow(2) * n_.pow(2) * p_.pow(2) - 1, 0)
        },
        rhs: {
            let angle = &d__ * (&a__ + &b__ * (&c__ * x_.pow(&n_)).log());
            let denominator = b__.pow(2) * d__.pow(2) * n_.pow(2) * p_.pow(2) - 1;
            let recursive = rubi_rhs_int(&angle.cosh().pow(&p_ - 2), x_);

            rubi_simp(&(Atom::num(-1) * x_ * angle.cosh().pow(&p_) / &denominator), x_)
                    + rubi_simp(&(&b__ * &d__ * &n_ * &p_ * x_ * angle.cosh().pow(&p_ - 1) * angle.sinh()
                        / &denominator), x_)
                    + rubi_star(b__.pow(2) * d__.pow(2) * n_.pow(2) * &p_ * (&p_ - 1) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_6047(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, p_, x_);
    rules.push(rubi_rule!(
        order: 6047,
        source: "Int[Sinh[d_.*(a_.+b_.*Log[x_])]^p_.,x_Symbol] :=
          1/(2^p*b^p*d^p*p^p) \\[Star] Int[ExpandIntegrand[(-E^(-a*b*d^2*p)*x^(-1/p)+E^(a*b*d^2*p)*x^(1/p))^p,x],x] /;
        FreeQ[{a,b,d},x] && IGtQ[p,0] && EqQ[b^2*d^2*p^2-1,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [d__, a__, b__, p_, x_],
        optional: [d__, a__, b__, p_],
        when: {
            freeq!([a__, b__, d__], x_)
                && igtq!(p_, 0)
                && eqq!(b__.pow(2) * d__.pow(2) * p_.pow(2) - 1, 0)
        },
        rhs: {
            let exponent = &a__ * &b__ * d__.pow(2) * &p_;
            let payload =
                (-(-&exponent).exp() * x_.pow(-Atom::num(1) / &p_) + exponent.exp() * x_.pow(Atom::num(1) / &p_))
                    .pow(&p_);
            let expanded = rubi_expand_integrand(&payload, x_);
            let recursive = rubi_rhs_int(&expanded, x_);

            let coefficient =
                Atom::num(1) / (Atom::num(2).pow(&p_) * b__.pow(&p_) * d__.pow(&p_) * p_.pow(&p_));

            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_6048(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, p_, x_);
    rules.push(rubi_rule!(
        order: 6048,
        source: "Int[Cosh[d_.*(a_.+b_.*Log[x_])]^p_.,x_Symbol] :=
          1/2^p \\[Star] Int[ExpandIntegrand[(E^(-a*b*d^2*p)*x^(-1/p)+E^(a*b*d^2*p)*x^(1/p))^p,x],x] /;
        FreeQ[{a,b,d},x] && IGtQ[p,0] && EqQ[b^2*d^2*p^2-1,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [d__, a__, b__, p_, x_],
        optional: [d__, a__, b__, p_],
        when: {
            freeq!([a__, b__, d__], x_)
                && igtq!(p_, 0)
                && eqq!(b__.pow(2) * d__.pow(2) * p_.pow(2) - 1, 0)
        },
        rhs: {
            let exponent = &a__ * &b__ * d__.pow(2) * &p_;
            let payload =
                ((-&exponent).exp() * x_.pow(-Atom::num(1) / &p_) + exponent.exp() * x_.pow(Atom::num(1) / &p_))
                    .pow(&p_);
            let expanded = rubi_expand_integrand(&payload, x_);
            let recursive = rubi_rhs_int(&expanded, x_);

            rubi_star(Atom::num(1) / Atom::num(2).pow(&p_), recursive)
        },
    ));
}

fn push_rules_rule_6049(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, p_, x_);
    rules.push(rubi_rule!(
        order: 6049,
        source: "Int[Sinh[d_.*(a_.+b_.*Log[x_])]^p_,x_Symbol] :=
          Sinh[d*(a+b*Log[x])]^p/(x^(b*d*p)*(1-1/(E^(2*a*d)*x^(2*b*d)))^p) \\[Star]
            Int[x^(b*d*p)*(1-1/(E^(2*a*d)*x^(2*b*d)))^p,x] /;
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
            let angle = &d__ * (&a__ + &b__ * x_.log());
            let power = x_.pow(&b__ * &d__ * &p_);
            let exponential = (Atom::num(2) * &a__ * &d__).exp() * x_.pow(Atom::num(2) * &b__ * &d__);
            let base = Atom::num(1) - Atom::num(1) / &exponential;
            let recursive = rubi_rhs_int(&(&power * base.pow(&p_)), x_);

            let coefficient = angle.sinh().pow(&p_) / (power * base.pow(&p_));

            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_6050(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, p_, x_);
    rules.push(rubi_rule!(
        order: 6050,
        source: "Int[Cosh[d_.*(a_.+b_.*Log[x_])]^p_,x_Symbol] :=
          Cosh[d*(a+b*Log[x])]^p/(x^(b*d*p)*(1+1/(E^(2*a*d)*x^(2*b*d)))^p) \\[Star]
            Int[x^(b*d*p)*(1+1/(E^(2*a*d)*x^(2*b*d)))^p,x] /;
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
            let angle = &d__ * (&a__ + &b__ * x_.log());
            let power = x_.pow(&b__ * &d__ * &p_);
            let exponential = (Atom::num(2) * &a__ * &d__).exp() * x_.pow(Atom::num(2) * &b__ * &d__);
            let base = Atom::num(1) + Atom::num(1) / &exponential;
            let recursive = rubi_rhs_int(&(&power * base.pow(&p_)), x_);

            let coefficient = angle.cosh().pow(&p_) / (power * base.pow(&p_));

            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_6053(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 6053,
        source: "Int[(e_.*x_)^m_.*Sinh[d_.*(a_.+b_.*Log[c_.*x_^n_.])],x_Symbol] :=
          -(m+1)*(e*x)^(m+1)*Sinh[d*(a+b*Log[c*x^n])]/(b^2*d^2*e*n^2-e*(m+1)^2) +
          b*d*n*(e*x)^(m+1)*Cosh[d*(a+b*Log[c*x^n])]/(b^2*d^2*e*n^2-e*(m+1)^2) /;
        FreeQ[{a,b,c,d,e,m,n},x] && NeQ[b^2*d^2*n^2-(m+1)^2,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: (e__ * x_).pow(m_) * (d__ * (a__ + b__ * (c__ * x_.pow(n_)).log())).sinh(),
        with: [e__, m_, d__, a__, b__, c__, n_, x_],
        optional: [e__, m_, d__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_], x_)
                && neq!(b__.pow(2) * d__.pow(2) * n_.pow(2) - (&m_ + 1).pow(2), 0)
        },
        rhs: {
            let scaled_x = &e__ * x_;
            let angle = &d__ * (&a__ + &b__ * (&c__ * x_.pow(&n_)).log());
            let denominator = b__.pow(2) * d__.pow(2) * &e__ * n_.pow(2) - &e__ * (&m_ + 1).pow(2);

            rubi_simp(&(-(&m_ + 1) * scaled_x.pow(&m_ + 1) * angle.sinh() / &denominator), x_)
                    + rubi_simp(&(&b__ * &d__ * &n_ * scaled_x.pow(&m_ + 1) * angle.cosh() / denominator), x_)
        },
    ));
}

fn push_rules_rule_6054(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 6054,
        source: "Int[(e_.*x_)^m_.*Cosh[d_.*(a_.+b_.*Log[c_.*x_^n_.])],x_Symbol] :=
          -(m+1)*(e*x)^(m+1)*Cosh[d*(a+b*Log[c*x^n])]/(b^2*d^2*e*n^2-e*(m+1)^2) +
          b*d*n*(e*x)^(m+1)*Sinh[d*(a+b*Log[c*x^n])]/(b^2*d^2*e*n^2-e*(m+1)^2) /;
        FreeQ[{a,b,c,d,e,m,n},x] && NeQ[b^2*d^2*n^2-(m+1)^2,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: (e__ * x_).pow(m_) * (d__ * (a__ + b__ * (c__ * x_.pow(n_)).log())).cosh(),
        with: [e__, m_, d__, a__, b__, c__, n_, x_],
        optional: [e__, m_, d__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_], x_)
                && neq!(b__.pow(2) * d__.pow(2) * n_.pow(2) - (&m_ + 1).pow(2), 0)
        },
        rhs: {
            let scaled_x = &e__ * x_;
            let angle = &d__ * (&a__ + &b__ * (&c__ * x_.pow(&n_)).log());
            let denominator = b__.pow(2) * d__.pow(2) * &e__ * n_.pow(2) - &e__ * (&m_ + 1).pow(2);

            rubi_simp(&(-(&m_ + 1) * scaled_x.pow(&m_ + 1) * angle.cosh() / &denominator), x_)
                    + rubi_simp(&(&b__ * &d__ * &n_ * scaled_x.pow(&m_ + 1) * angle.sinh() / denominator), x_)
        },
    ));
}

fn push_rules_rule_6055(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6055,
        source: "Int[(e_.*x_)^m_.*Sinh[d_.*(a_.+b_.*Log[c_.*x_^n_.])]^p_,x_Symbol] :=
          -(m+1)*(e*x)^(m+1)*Sinh[d*(a+b*Log[c*x^n])]^p/(b^2*d^2*e*n^2*p^2-e*(m+1)^2) +
          b*d*n*p*(e*x)^(m+1)*Cosh[d*(a+b*Log[c*x^n])]*Sinh[d*(a+b*Log[c*x^n])]^(p-1)/(b^2*d^2*e*n^2*p^2-e*(m+1)^2) -
          b^2*d^2*n^2*p*(p-1)/(b^2*d^2*n^2*p^2-(m+1)^2) \\[Star] Int[(e*x)^m*Sinh[d*(a+b*Log[c*x^n])]^(p-2),x] /;
        FreeQ[{a,b,c,d,e,m,n},x] && IGtQ[p,1] && NeQ[b^2*d^2*n^2*p^2-(m+1)^2,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [e__, m_, d__, a__, b__, c__, n_, p_, x_],
        optional: [e__, m_, d__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_], x_)
                && igtq!(p_, 1)
                && neq!(b__.pow(2) * d__.pow(2) * n_.pow(2) * p_.pow(2) - (&m_ + 1).pow(2), 0)
        },
        rhs: {
            let scaled_x = &e__ * x_;
            let angle = &d__ * (&a__ + &b__ * (&c__ * x_.pow(&n_)).log());
            let denominator_with_e =
                b__.pow(2) * d__.pow(2) * &e__ * n_.pow(2) * p_.pow(2) - &e__ * (&m_ + 1).pow(2);
            let denominator = b__.pow(2) * d__.pow(2) * n_.pow(2) * p_.pow(2) - (&m_ + 1).pow(2);
            let recursive = rubi_rhs_int(&(scaled_x.pow(&m_) * angle.sinh().pow(&p_ - 2)), x_);

            rubi_simp(&(-(&m_ + 1) * scaled_x.pow(&m_ + 1) * angle.sinh().pow(&p_) / &denominator_with_e), x_)
                    + rubi_simp(&(&b__ * &d__ * &n_ * &p_ * scaled_x.pow(&m_ + 1) * angle.cosh() * angle.sinh().pow(&p_ - 1)
                        / &denominator_with_e), x_)
                    - rubi_star(b__.pow(2) * d__.pow(2) * n_.pow(2) * &p_ * (&p_ - 1) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_6056(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6056,
        source: "Int[(e_.*x_)^m_.*Cosh[d_.*(a_.+b_.*Log[c_.*x_^n_.])]^p_,x_Symbol] :=
          -(m+1)*(e*x)^(m+1)*Cosh[d*(a+b*Log[c*x^n])]^p/(b^2*d^2*e*n^2*p^2-e*(m+1)^2) +
          b*d*n*p*(e*x)^(m+1)*Sinh[d*(a+b*Log[c*x^n])]*Cosh[d*(a+b*Log[c*x^n])]^(p-1)/(b^2*d^2*e*n^2*p^2-e*(m+1)^2) +
          b^2*d^2*n^2*p*(p-1)/(b^2*d^2*n^2*p^2-(m+1)^2) \\[Star] Int[(e*x)^m*Cosh[d*(a+b*Log[c*x^n])]^(p-2),x] /;
        FreeQ[{a,b,c,d,e,m,n},x] && IGtQ[p,1] && NeQ[b^2*d^2*n^2*p^2-(m+1)^2,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [e__, m_, d__, a__, b__, c__, n_, p_, x_],
        optional: [e__, m_, d__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_], x_)
                && igtq!(p_, 1)
                && neq!(b__.pow(2) * d__.pow(2) * n_.pow(2) * p_.pow(2) - (&m_ + 1).pow(2), 0)
        },
        rhs: {
            let scaled_x = &e__ * x_;
            let angle = &d__ * (&a__ + &b__ * (&c__ * x_.pow(&n_)).log());
            let denominator_with_e =
                b__.pow(2) * d__.pow(2) * &e__ * n_.pow(2) * p_.pow(2) - &e__ * (&m_ + 1).pow(2);
            let denominator = b__.pow(2) * d__.pow(2) * n_.pow(2) * p_.pow(2) - (&m_ + 1).pow(2);
            let recursive = rubi_rhs_int(&(scaled_x.pow(&m_) * angle.cosh().pow(&p_ - 2)), x_);

            rubi_simp(&(-(&m_ + 1) * scaled_x.pow(&m_ + 1) * angle.cosh().pow(&p_) / &denominator_with_e), x_)
                    + rubi_simp(&(&b__ * &d__ * &n_ * &p_ * scaled_x.pow(&m_ + 1) * angle.sinh() * angle.cosh().pow(&p_ - 1)
                        / &denominator_with_e), x_)
                    + rubi_star(b__.pow(2) * d__.pow(2) * n_.pow(2) * &p_ * (&p_ - 1) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_6057(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 6057,
        source: "Int[(e_.*x_)^m_.*Sinh[d_.*(a_.+b_.*Log[x_])]^p_.,x_Symbol] :=
          (m+1)^p/(2^p*b^p*d^p*p^p) \\[Star]
            Int[ExpandIntegrand[(e*x)^m*(-E^(-a*b*d^2*p/(m+1))*x^(-(m+1)/p)+E^(a*b*d^2*p/(m+1))*x^((m+1)/p))^p,x],x] /;
        FreeQ[{a,b,d,e,m},x] && IGtQ[p,0] && EqQ[b^2*d^2*p^2-(m+1)^2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_11(symbols),
        with: [e__, m_, d__, a__, b__, p_, x_],
        optional: [e__, m_, d__, a__, b__, p_],
        when: {
            freeq!([a__, b__, d__, e__, m_], x_)
                && igtq!(p_, 0)
                && eqq!(b__.pow(2) * d__.pow(2) * p_.pow(2) - (&m_ + 1).pow(2), 0)
        },
        rhs: {
            let scaled_x = &e__ * x_;
            let exponent = &a__ * &b__ * d__.pow(2) * &p_ / (&m_ + 1);
            let payload = scaled_x.pow(&m_)
                * (-(-&exponent).exp() * x_.pow(-(&m_ + 1) / &p_)
                    + exponent.exp() * x_.pow((&m_ + 1) / &p_))
                .pow(&p_);
            let expanded = rubi_expand_integrand(&payload, x_);
            let recursive = rubi_rhs_int(&expanded, x_);

            let coefficient = (&m_ + 1).pow(&p_)
                / (Atom::num(2).pow(&p_) * b__.pow(&p_) * d__.pow(&p_) * p_.pow(&p_));

            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_6058(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 6058,
        source: "Int[(e_.*x_)^m_.*Cosh[d_.*(a_.+b_.*Log[x_])]^p_.,x_Symbol] :=
          1/2^p \\[Star] Int[ExpandIntegrand[(e*x)^m*(E^(-a*b*d^2*p/(m+1))*x^(-(m+1)/p)+E^(a*b*d^2*p/(m+1))*x^((m+1)/p))^p,x],x] /;
        FreeQ[{a,b,d,e,m},x] && IGtQ[p,0] && EqQ[b^2*d^2*p^2-(m+1)^2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [e__, m_, d__, a__, b__, p_, x_],
        optional: [e__, m_, d__, a__, b__, p_],
        when: {
            freeq!([a__, b__, d__, e__, m_], x_)
                && igtq!(p_, 0)
                && eqq!(b__.pow(2) * d__.pow(2) * p_.pow(2) - (&m_ + 1).pow(2), 0)
        },
        rhs: {
            let scaled_x = &e__ * x_;
            let exponent = &a__ * &b__ * d__.pow(2) * &p_ / (&m_ + 1);
            let payload = scaled_x.pow(&m_)
                * ((-&exponent).exp() * x_.pow(-(&m_ + 1) / &p_)
                    + exponent.exp() * x_.pow((&m_ + 1) / &p_))
                .pow(&p_);
            let expanded = rubi_expand_integrand(&payload, x_);
            let recursive = rubi_rhs_int(&expanded, x_);

            rubi_star(Atom::num(1) / Atom::num(2).pow(&p_), recursive)
        },
    ));
}

fn push_rules_rule_6059(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 6059,
        source: "Int[(e_.*x_)^m_.*Sinh[d_.*(a_.+b_.*Log[x_])]^p_,x_Symbol] :=
          Sinh[d*(a+b*Log[x])]^p/(x^(b*d*p)*(1-1/(E^(2*a*d)*x^(2*b*d)))^p) \\[Star]
            Int[(e*x)^m*x^(b*d*p)*(1-1/(E^(2*a*d)*x^(2*b*d)))^p,x] /;
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
            let scaled_x = &e__ * x_;
            let angle = &d__ * (&a__ + &b__ * x_.log());
            let power = x_.pow(&b__ * &d__ * &p_);
            let exponential = (Atom::num(2) * &a__ * &d__).exp() * x_.pow(Atom::num(2) * &b__ * &d__);
            let base = Atom::num(1) - Atom::num(1) / &exponential;
            let recursive = rubi_rhs_int(&(scaled_x.pow(&m_) * &power * base.pow(&p_)), x_);

            let coefficient = angle.sinh().pow(&p_) / (power * base.pow(&p_));

            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_6060(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 6060,
        source: "Int[(e_.*x_)^m_.*Cosh[d_.*(a_.+b_.*Log[x_])]^p_,x_Symbol] :=
          Cosh[d*(a+b*Log[x])]^p/(x^(b*d*p)*(1+1/(E^(2*a*d)*x^(2*b*d)))^p) \\[Star]
            Int[(e*x)^m*x^(b*d*p)*(1+1/(E^(2*a*d)*x^(2*b*d)))^p,x] /;
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
            let scaled_x = &e__ * x_;
            let angle = &d__ * (&a__ + &b__ * x_.log());
            let power = x_.pow(&b__ * &d__ * &p_);
            let exponential = (Atom::num(2) * &a__ * &d__).exp() * x_.pow(Atom::num(2) * &b__ * &d__);
            let base = Atom::num(1) + Atom::num(1) / &exponential;
            let recursive = rubi_rhs_int(&(scaled_x.pow(&m_) * &power * base.pow(&p_)), x_);

            let coefficient = angle.cosh().pow(&p_) / (power * base.pow(&p_));

            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_6063(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, h__, m_, n_, q_, x_);
    rules.push(rubi_rule!(
        order: 6063,
        source: "Int[(h_.*(e_.+f_.*Log[g_.*x_^m_.]))^q_.*Sinh[d_.*(a_.+b_.*Log[c_.*x_^n_.])],x_Symbol] :=
          -E^(-a*d)*(c*x^n)^(-b*d)/(2*x^(-b*d*n)) \\[Star] Int[x^(-b*d*n)*(h*(e+f*Log[g*x^m]))^q,x] +
          E^(a*d)*(c*x^n)^(b*d)/(2*x^(b*d*n)) \\[Star] Int[x^(b*d*n)*(h*(e+f*Log[g*x^m]))^q,x] /;
        FreeQ[{a,b,c,d,e,f,g,h,m,n,q},x]",
        desc: "Algebraic expansion and piecewise constant extraction",
        refs: [],
        pattern: (h__ * (e__ + f__ * (g__ * x_.pow(m_)).log())).pow(q_)
            * (d__ * (a__ + b__ * (c__ * x_.pow(n_)).log())).sinh(),
        with: [h__, e__, f__, g__, m_, q_, d__, a__, b__, c__, n_, x_],
        optional: [h__, e__, f__, g__, m_, q_, d__, a__, b__, c__, n_],
        when: { freeq!([a__, b__, c__, d__, e__, f__, g__, h__, m_, n_, q_], x_) },
        rhs: {
            let log_power = &h__ * (&e__ + &f__ * (&g__ * x_.pow(&m_)).log());
            let c_power = &c__ * x_.pow(&n_);
            let negative_power = -&b__ * &d__ * &n_;
            let positive_power = &b__ * &d__ * &n_;
            let negative_recursive = rubi_rhs_int(&(x_.pow(&negative_power) * log_power.pow(&q_)), x_);
            let positive_recursive = rubi_rhs_int(&(x_.pow(&positive_power) * log_power.pow(&q_)), x_);

            rubi_star(-(&((-&a__ * &d__).exp() * c_power.pow(-&b__ * &d__)
                        / (Atom::num(2) * x_.pow(&negative_power)))), negative_recursive) + rubi_star((&a__ * &d__).exp() * c_power.pow(&b__ * &d__)
                        / (Atom::num(2) * x_.pow(&positive_power)), positive_recursive)
        },
    ));
}

fn push_rules_rule_6064(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, h__, m_, n_, q_, x_);
    rules.push(rubi_rule!(
        order: 6064,
        source: "Int[(h_.*(e_.+f_.*Log[g_.*x_^m_.]))^q_.*Cosh[d_.*(a_.+b_.*Log[c_.*x_^n_.])],x_Symbol] :=
          E^(-a*d)*(c*x^n)^(-b*d)/(2*x^(-b*d*n)) \\[Star] Int[x^(-b*d*n)*(h*(e+f*Log[g*x^m]))^q,x] +
          E^(a*d)*(c*x^n)^(b*d)/(2*x^(b*d*n)) \\[Star] Int[x^(b*d*n)*(h*(e+f*Log[g*x^m]))^q,x] /;
        FreeQ[{a,b,c,d,e,f,g,h,m,n,q},x]",
        desc: "Algebraic expansion and piecewise constant extraction",
        refs: [],
        pattern: (h__ * (e__ + f__ * (g__ * x_.pow(m_)).log())).pow(q_)
            * (d__ * (a__ + b__ * (c__ * x_.pow(n_)).log())).cosh(),
        with: [h__, e__, f__, g__, m_, q_, d__, a__, b__, c__, n_, x_],
        optional: [h__, e__, f__, g__, m_, q_, d__, a__, b__, c__, n_],
        when: { freeq!([a__, b__, c__, d__, e__, f__, g__, h__, m_, n_, q_], x_) },
        rhs: {
            let log_power = &h__ * (&e__ + &f__ * (&g__ * x_.pow(&m_)).log());
            let c_power = &c__ * x_.pow(&n_);
            let negative_power = -&b__ * &d__ * &n_;
            let positive_power = &b__ * &d__ * &n_;
            let negative_recursive = rubi_rhs_int(&(x_.pow(&negative_power) * log_power.pow(&q_)), x_);
            let positive_recursive = rubi_rhs_int(&(x_.pow(&positive_power) * log_power.pow(&q_)), x_);

            rubi_star((-&a__ * &d__).exp() * c_power.pow(-&b__ * &d__)
                        / (Atom::num(2) * x_.pow(&negative_power)), negative_recursive) + rubi_star((&a__ * &d__).exp() * c_power.pow(&b__ * &d__)
                        / (Atom::num(2) * x_.pow(&positive_power)), positive_recursive)
        },
    ));
}

fn push_rules_rule_6065(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        a__, b__, c__, d__, e__, f__, g__, h__, i__, m_, n_, q_, r_, x_
    );
    rules.push(rubi_rule!(
        order: 6065,
        source: "Int[(i_.*x_)^r_.*(h_.*(e_.+f_.*Log[g_.*x_^m_.]))^q_.*Sinh[d_.*(a_.+b_.*Log[c_.*x_^n_.])],x_Symbol] :=
          -E^(-a*d)*(i*x)^r*(c*x^n)^(-b*d)/(2*x^(r-b*d*n)) \\[Star] Int[x^(r-b*d*n)*(h*(e+f*Log[g*x^m]))^q,x] +
          E^(a*d)*(i*x)^r*(c*x^n)^(b*d)/(2*x^(r+b*d*n)) \\[Star] Int[x^(r+b*d*n)*(h*(e+f*Log[g*x^m]))^q,x] /;
        FreeQ[{a,b,c,d,e,f,g,h,i,m,n,q,r},x]",
        desc: "Algebraic expansion and piecewise constant extraction",
        refs: [],
        pattern: (i__ * x_).pow(r_)
            * (h__ * (e__ + f__ * (g__ * x_.pow(m_)).log())).pow(q_)
            * (d__ * (a__ + b__ * (c__ * x_.pow(n_)).log())).sinh(),
        with: [i__, r_, h__, e__, f__, g__, m_, q_, d__, a__, b__, c__, n_, x_],
        optional: [i__, r_, h__, e__, f__, g__, m_, q_, d__, a__, b__, c__, n_],
        when: { freeq!([a__, b__, c__, d__, e__, f__, g__, h__, i__, m_, n_, q_, r_], x_) },
        rhs: {
            let scaled_x = &i__ * x_;
            let log_power = &h__ * (&e__ + &f__ * (&g__ * x_.pow(&m_)).log());
            let c_power = &c__ * x_.pow(&n_);
            let negative_power = &r_ - &b__ * &d__ * &n_;
            let positive_power = &r_ + &b__ * &d__ * &n_;
            let negative_recursive = rubi_rhs_int(&(x_.pow(&negative_power) * log_power.pow(&q_)), x_);
            let positive_recursive = rubi_rhs_int(&(x_.pow(&positive_power) * log_power.pow(&q_)), x_);

            rubi_star(-(&((-&a__ * &d__).exp() * scaled_x.pow(&r_) * c_power.pow(-&b__ * &d__)
                        / (Atom::num(2) * x_.pow(&negative_power)))), negative_recursive) + rubi_star((&a__ * &d__).exp() * scaled_x.pow(&r_) * c_power.pow(&b__ * &d__)
                        / (Atom::num(2) * x_.pow(&positive_power)), positive_recursive)
        },
    ));
}

fn push_rules_rule_6066(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        a__, b__, c__, d__, e__, f__, g__, h__, i__, m_, n_, q_, r_, x_
    );
    rules.push(rubi_rule!(
        order: 6066,
        source: "Int[(i_.*x_)^r_.*(h_.*(e_.+f_.*Log[g_.*x_^m_.]))^q_.*Cosh[d_.*(a_.+b_.*Log[c_.*x_^n_.])],x_Symbol] :=
          E^(-a*d)*(i*x)^r*(c*x^n)^(-b*d)/(2*x^(r-b*d*n)) \\[Star] Int[x^(r-b*d*n)*(h*(e+f*Log[g*x^m]))^q,x] +
          E^(a*d)*(i*x)^r*(c*x^n)^(b*d)/(2*x^(r+b*d*n)) \\[Star] Int[x^(r+b*d*n)*(h*(e+f*Log[g*x^m]))^q,x] /;
        FreeQ[{a,b,c,d,e,f,g,h,i,m,n,q,r},x]",
        desc: "Algebraic expansion and piecewise constant extraction",
        refs: [],
        pattern: (i__ * x_).pow(r_)
            * (h__ * (e__ + f__ * (g__ * x_.pow(m_)).log())).pow(q_)
            * (d__ * (a__ + b__ * (c__ * x_.pow(n_)).log())).cosh(),
        with: [i__, r_, h__, e__, f__, g__, m_, q_, d__, a__, b__, c__, n_, x_],
        optional: [i__, r_, h__, e__, f__, g__, m_, q_, d__, a__, b__, c__, n_],
        when: { freeq!([a__, b__, c__, d__, e__, f__, g__, h__, i__, m_, n_, q_, r_], x_) },
        rhs: {
            let scaled_x = &i__ * x_;
            let log_power = &h__ * (&e__ + &f__ * (&g__ * x_.pow(&m_)).log());
            let c_power = &c__ * x_.pow(&n_);
            let negative_power = &r_ - &b__ * &d__ * &n_;
            let positive_power = &r_ + &b__ * &d__ * &n_;
            let negative_recursive = rubi_rhs_int(&(x_.pow(&negative_power) * log_power.pow(&q_)), x_);
            let positive_recursive = rubi_rhs_int(&(x_.pow(&positive_power) * log_power.pow(&q_)), x_);

            rubi_star((-&a__ * &d__).exp() * scaled_x.pow(&r_) * c_power.pow(-&b__ * &d__)
                        / (Atom::num(2) * x_.pow(&negative_power)), negative_recursive) + rubi_star((&a__ * &d__).exp() * scaled_x.pow(&r_) * c_power.pow(&b__ * &d__)
                        / (Atom::num(2) * x_.pow(&positive_power)), positive_recursive)
        },
    ));
}

fn push_rules_rule_6067(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, d__, p_, x_);
    rules.push(rubi_rule!(
        order: 6067,
        source: "Int[Tanh[d_.*(a_.+b_.*Log[x_])]^p_.,x_Symbol] :=
          Int[(-1+E^(2*a*d)*x^(2*b*d))^p/(1+E^(2*a*d)*x^(2*b*d))^p,x] /;
        FreeQ[{a,b,d,p},x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (d__ * (a__ + b__ * x_.log())).tanh().pow(p_),
        with: [d__, a__, b__, p_, x_],
        optional: [d__, a__, b__, p_],
        when: { freeq!([a__, b__, d__, p_], x_) },
        rhs: {
            let exponential = (Atom::num(2) * &a__ * &d__).exp() * x_.pow(Atom::num(2) * &b__ * &d__);
            let integrand =
                (-Atom::num(1) + &exponential).pow(&p_) / (Atom::num(1) + &exponential).pow(&p_);

            rubi_rhs_int(&integrand, x_)
        },
    ));
}

fn push_rules_rule_6068(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, d__, p_, x_);
    rules.push(rubi_rule!(
        order: 6068,
        source: "Int[Coth[d_.*(a_.+b_.*Log[x_])]^p_.,x_Symbol] :=
          Int[(-1-E^(2*a*d)*x^(2*b*d))^p/(1-E^(2*a*d)*x^(2*b*d))^p,x] /;
        FreeQ[{a,b,d,p},x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (d__ * (a__ + b__ * x_.log())).coth().pow(p_),
        with: [d__, a__, b__, p_, x_],
        optional: [d__, a__, b__, p_],
        when: { freeq!([a__, b__, d__, p_], x_) },
        rhs: {
            let exponential = (Atom::num(2) * &a__ * &d__).exp() * x_.pow(Atom::num(2) * &b__ * &d__);
            let integrand =
                (-Atom::num(1) - &exponential).pow(&p_) / (Atom::num(1) - &exponential).pow(&p_);

            rubi_rhs_int(&integrand, x_)
        },
    ));
}

fn push_rules_rule_6071(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 6071,
        source: "Int[(e_.*x_)^m_.*Tanh[d_.*(a_.+b_.*Log[x_])]^p_.,x_Symbol] :=
          Int[(e*x)^m*(-1+E^(2*a*d)*x^(2*b*d))^p/(1+E^(2*a*d)*x^(2*b*d))^p,x] /;
        FreeQ[{a,b,d,e,m,p},x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (e__ * x_).pow(m_) * (d__ * (a__ + b__ * x_.log())).tanh().pow(p_),
        with: [e__, m_, d__, a__, b__, p_, x_],
        optional: [e__, m_, d__, a__, b__, p_],
        when: { freeq!([a__, b__, d__, e__, m_, p_], x_) },
        rhs: {
            let scaled_x = &e__ * x_;
            let exponential = (Atom::num(2) * &a__ * &d__).exp() * x_.pow(Atom::num(2) * &b__ * &d__);
            let integrand = scaled_x.pow(&m_) * (-Atom::num(1) + &exponential).pow(&p_)
                / (Atom::num(1) + &exponential).pow(&p_);

            rubi_rhs_int(&integrand, x_)
        },
    ));
}

fn push_rules_rule_6072(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 6072,
        source: "Int[(e_.*x_)^m_.*Coth[d_.*(a_.+b_.*Log[x_])]^p_.,x_Symbol] :=
          Int[(e*x)^m*(-1-E^(2*a*d)*x^(2*b*d))^p/(1-E^(2*a*d)*x^(2*b*d))^p,x] /;
        FreeQ[{a,b,d,e,m,p},x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (e__ * x_).pow(m_) * (d__ * (a__ + b__ * x_.log())).coth().pow(p_),
        with: [e__, m_, d__, a__, b__, p_, x_],
        optional: [e__, m_, d__, a__, b__, p_],
        when: { freeq!([a__, b__, d__, e__, m_, p_], x_) },
        rhs: {
            let scaled_x = &e__ * x_;
            let exponential = (Atom::num(2) * &a__ * &d__).exp() * x_.pow(Atom::num(2) * &b__ * &d__);
            let integrand = scaled_x.pow(&m_) * (-Atom::num(1) - &exponential).pow(&p_)
                / (Atom::num(1) - &exponential).pow(&p_);

            rubi_rhs_int(&integrand, x_)
        },
    ));
}

fn push_rules_rule_6075(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, p_, x_);
    rules.push(rubi_rule!(
        order: 6075,
        source: "Int[Sech[d_.*(a_.+b_.*Log[x_])]^p_.,x_Symbol] :=
          2^p*E^(-a*d*p) \\[Star] Int[x^(-b*d*p)/(1+E^(-2*a*d)*x^(-2*b*d))^p,x] /;
        FreeQ[{a,b,d},x] && IntegerQ[p]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [d__, a__, b__, p_, x_],
        optional: [d__, a__, b__, p_],
        when: {
            freeq!([a__, b__, d__], x_)
                && integerq!(p_)
        },
        rhs: {
            let exponential = (-Atom::num(2) * &a__ * &d__).exp() * x_.pow(-Atom::num(2) * &b__ * &d__);
            let power = x_.pow(-&b__ * &d__ * &p_);
            let integrand = power / (Atom::num(1) + exponential).pow(&p_);

            let recursive = rubi_rhs_int(&integrand, x_);
            let coefficient = Atom::num(2).pow(&p_) * (-&a__ * &d__ * &p_).exp();

            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_6076(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, p_, x_);
    rules.push(rubi_rule!(
        order: 6076,
        source: "Int[Csch[d_.*(a_.+b_.*Log[x_])]^p_.,x_Symbol] :=
          2^p*E^(-a*d*p) \\[Star] Int[x^(-b*d*p)/(1-E^(-2*a*d)*x^(-2*b*d))^p,x] /;
        FreeQ[{a,b,d},x] && IntegerQ[p]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [d__, a__, b__, p_, x_],
        optional: [d__, a__, b__, p_],
        when: {
            freeq!([a__, b__, d__], x_)
                && integerq!(p_)
        },
        rhs: {
            let exponential = (-Atom::num(2) * &a__ * &d__).exp() * x_.pow(-Atom::num(2) * &b__ * &d__);
            let power = x_.pow(-&b__ * &d__ * &p_);
            let integrand = power / (Atom::num(1) - exponential).pow(&p_);

            let recursive = rubi_rhs_int(&integrand, x_);
            let coefficient = Atom::num(2).pow(&p_) * (-&a__ * &d__ * &p_).exp();

            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_6077(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, p_, x_);
    rules.push(rubi_rule!(
        order: 6077,
        source: "Int[Sech[d_.*(a_.+b_.*Log[x_])]^p_.,x_Symbol] :=
          Sech[d*(a+b*Log[x])]^p*(1+E^(-2*a*d)*x^(-2*b*d))^p/x^(-b*d*p) \\[Star]
            Int[x^(-b*d*p)/(1+E^(-2*a*d)*x^(-2*b*d))^p,x] /;
        FreeQ[{a,b,d,p},x] && Not[IntegerQ[p]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [d__, a__, b__, p_, x_],
        optional: [d__, a__, b__, p_],
        when: {
            freeq!([a__, b__, d__, p_], x_)
                && !integerq!(p_)
        },
        rhs: {
            let angle = &d__ * (&a__ + &b__ * x_.log());
            let exponential = (-Atom::num(2) * &a__ * &d__).exp() * x_.pow(-Atom::num(2) * &b__ * &d__);
            let power = x_.pow(-&b__ * &d__ * &p_);
            let base = Atom::num(1) + &exponential;
            let recursive = rubi_rhs_int(&(&power / base.pow(&p_)), x_);

            let coefficient = angle.sech().pow(&p_) * base.pow(&p_) / power;

            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_6078(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, p_, x_);
    rules.push(rubi_rule!(
        order: 6078,
        source: "Int[Csch[d_.*(a_.+b_.*Log[x_])]^p_.,x_Symbol] :=
          Csch[d*(a+b*Log[x])]^p*(1-E^(-2*a*d)*x^(-2*b*d))^p/x^(-b*d*p) \\[Star]
            Int[x^(-b*d*p)/(1-E^(-2*a*d)*x^(-2*b*d))^p,x] /;
        FreeQ[{a,b,d,p},x] && Not[IntegerQ[p]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [d__, a__, b__, p_, x_],
        optional: [d__, a__, b__, p_],
        when: {
            freeq!([a__, b__, d__, p_], x_)
                && !integerq!(p_)
        },
        rhs: {
            let angle = &d__ * (&a__ + &b__ * x_.log());
            let exponential = (-Atom::num(2) * &a__ * &d__).exp() * x_.pow(-Atom::num(2) * &b__ * &d__);
            let power = x_.pow(-&b__ * &d__ * &p_);
            let base = Atom::num(1) - &exponential;
            let recursive = rubi_rhs_int(&(&power / base.pow(&p_)), x_);

            let coefficient = angle.csch().pow(&p_) * base.pow(&p_) / power;

            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_6081(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 6081,
        source: "Int[(e_.*x_)^m_.*Sech[d_.*(a_.+b_.*Log[x_])]^p_.,x_Symbol] :=
          2^p*E^(-a*d*p) \\[Star] Int[(e*x)^m*x^(-b*d*p)/(1+E^(-2*a*d)*x^(-2*b*d))^p,x] /;
        FreeQ[{a,b,d,e,m},x] && IntegerQ[p]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_10(symbols),
        with: [e__, m_, d__, a__, b__, p_, x_],
        optional: [e__, m_, d__, a__, b__, p_],
        when: {
            freeq!([a__, b__, d__, e__, m_], x_)
                && integerq!(p_)
        },
        rhs: {
            let scaled_x = &e__ * x_;
            let exponential = (-Atom::num(2) * &a__ * &d__).exp() * x_.pow(-Atom::num(2) * &b__ * &d__);
            let integrand = scaled_x.pow(&m_) * x_.pow(-&b__ * &d__ * &p_)
                / (Atom::num(1) + exponential).pow(&p_);

            let recursive = rubi_rhs_int(&integrand, x_);
            let coefficient = Atom::num(2).pow(&p_) * (-&a__ * &d__ * &p_).exp();

            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_6082(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 6082,
        source: "Int[(e_.*x_)^m_.*Csch[d_.*(a_.+b_.*Log[x_])]^p_.,x_Symbol] :=
          2^p*E^(-a*d*p) \\[Star] Int[(e*x)^m*x^(-b*d*p)/(1-E^(-2*a*d)*x^(-2*b*d))^p,x] /;
        FreeQ[{a,b,d,e,m},x] && IntegerQ[p]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [e__, m_, d__, a__, b__, p_, x_],
        optional: [e__, m_, d__, a__, b__, p_],
        when: {
            freeq!([a__, b__, d__, e__, m_], x_)
                && integerq!(p_)
        },
        rhs: {
            let scaled_x = &e__ * x_;
            let exponential = (-Atom::num(2) * &a__ * &d__).exp() * x_.pow(-Atom::num(2) * &b__ * &d__);
            let integrand = scaled_x.pow(&m_) * x_.pow(-&b__ * &d__ * &p_)
                / (Atom::num(1) - exponential).pow(&p_);

            let recursive = rubi_rhs_int(&integrand, x_);
            let coefficient = Atom::num(2).pow(&p_) * (-&a__ * &d__ * &p_).exp();

            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_6083(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 6083,
        source: "Int[(e_.*x_)^m_.*Sech[d_.*(a_.+b_.*Log[x_])]^p_.,x_Symbol] :=
          Sech[d*(a+b*Log[x])]^p*(1+E^(-2*a*d)*x^(-2*b*d))^p/x^(-b*d*p) \\[Star]
            Int[(e*x)^m*x^(-b*d*p)/(1+E^(-2*a*d)*x^(-2*b*d))^p,x] /;
        FreeQ[{a,b,d,e,m,p},x] && Not[IntegerQ[p]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_10(symbols),
        with: [e__, m_, d__, a__, b__, p_, x_],
        optional: [e__, m_, d__, a__, b__, p_],
        when: {
            freeq!([a__, b__, d__, e__, m_, p_], x_)
                && !integerq!(p_)
        },
        rhs: {
            let scaled_x = &e__ * x_;
            let angle = &d__ * (&a__ + &b__ * x_.log());
            let exponential = (-Atom::num(2) * &a__ * &d__).exp() * x_.pow(-Atom::num(2) * &b__ * &d__);
            let power = x_.pow(-&b__ * &d__ * &p_);
            let base = Atom::num(1) + &exponential;
            let recursive = rubi_rhs_int(&(scaled_x.pow(&m_) * &power / base.pow(&p_)), x_);

            let coefficient = angle.sech().pow(&p_) * base.pow(&p_) / power;

            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_6084(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 6084,
        source: "Int[(e_.*x_)^m_.*Csch[d_.*(a_.+b_.*Log[x_])]^p_.,x_Symbol] :=
          Csch[d*(a+b*Log[x])]^p*(1-E^(-2*a*d)*x^(-2*b*d))^p/x^(-b*d*p) \\[Star]
            Int[(e*x)^m*x^(-b*d*p)/(1-E^(-2*a*d)*x^(-2*b*d))^p,x] /;
        FreeQ[{a,b,d,e,m,p},x] && Not[IntegerQ[p]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [e__, m_, d__, a__, b__, p_, x_],
        optional: [e__, m_, d__, a__, b__, p_],
        when: {
            freeq!([a__, b__, d__, e__, m_, p_], x_)
                && !integerq!(p_)
        },
        rhs: {
            let scaled_x = &e__ * x_;
            let angle = &d__ * (&a__ + &b__ * x_.log());
            let exponential = (-Atom::num(2) * &a__ * &d__).exp() * x_.pow(-Atom::num(2) * &b__ * &d__);
            let power = x_.pow(-&b__ * &d__ * &p_);
            let base = Atom::num(1) - &exponential;
            let recursive = rubi_rhs_int(&(scaled_x.pow(&m_) * &power / base.pow(&p_)), x_);

            let coefficient = angle.csch().pow(&p_) * base.pow(&p_) / power;

            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_6087(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, x_);
    rules.push(rubi_rule!(
        order: 6087,
        source: "Int[Sinh[a_.*x_*Log[b_.*x_]]*Log[b_.*x_],x_Symbol] :=
          Cosh[a*x*Log[b*x]]/a - Int[Sinh[a*x*Log[b*x]],x] /;
        FreeQ[{a,b},x]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern: (a__ * x_ * (b__ * x_).log()).sinh() * (b__ * x_).log(),
        with: [a__, b__, x_],
        optional: [a__, b__],
        when: { freeq!([a__, b__], x_) },
        rhs: {
            let angle = &a__ * x_ * (&b__ * x_).log();
            let recursive = rubi_rhs_int(&angle.sinh(), x_);

            rubi_simp(&(angle.cosh() / a__), x_) - recursive
        },
    ));
}

fn push_rules_rule_6088(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, x_);
    rules.push(rubi_rule!(
        order: 6088,
        source: "Int[Cosh[a_.*x_*Log[b_.*x_]]*Log[b_.*x_],x_Symbol] :=
          Sinh[a*x*Log[b*x]]/a - Int[Cosh[a*x*Log[b*x]],x] /;
        FreeQ[{a,b},x]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern: (a__ * x_ * (b__ * x_).log()).cosh() * (b__ * x_).log(),
        with: [a__, b__, x_],
        optional: [a__, b__],
        when: { freeq!([a__, b__], x_) },
        rhs: {
            let angle = &a__ * x_ * (&b__ * x_).log();
            let recursive = rubi_rhs_int(&angle.cosh(), x_);

            rubi_simp(&(angle.sinh() / a__), x_) - recursive
        },
    ));
}

fn push_rules_rule_6089(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 6089,
        source: "Int[x_^m_.*Sinh[a_.*x_^n_.*Log[b_.*x_]]*Log[b_.*x_],x_Symbol] :=
          Cosh[a*x^n*Log[b*x]]/(a*n) - 1/n \\[Star] Int[x^m*Sinh[a*x^n*Log[b*x]],x] /;
        FreeQ[{a,b,m,n},x] && EqQ[m,n-1]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern: x_.pow(m_) * (a__ * x_.pow(n_) * (b__ * x_).log()).sinh() * (b__ * x_).log(),
        with: [m_, a__, n_, b__, x_],
        optional: [m_, a__, n_, b__],
        when: {
            freeq!([a__, b__, m_, n_], x_)
                && eqq!(m_, &n_ - 1)
        },
        rhs: {
            let angle = &a__ * x_.pow(&n_) * (&b__ * x_).log();
            let recursive = rubi_rhs_int(&(x_.pow(&m_) * angle.sinh()), x_);

            rubi_simp(&(angle.cosh() / (&a__ * &n_)), x_)
                    - rubi_star(Atom::num(1) / &n_, recursive)
        },
    ));
}

fn push_rules_rule_6090(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 6090,
        source: "Int[x_^m_.*Cosh[a_.*x_^n_.*Log[b_.*x_]]*Log[b_.*x_],x_Symbol] :=
          Sinh[a*x^n*Log[b*x]]/(a*n) - 1/n \\[Star] Int[x^m*Cosh[a*x^n*Log[b*x]],x] /;
        FreeQ[{a,b,m,n},x] && EqQ[m,n-1]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern: x_.pow(m_) * (a__ * x_.pow(n_) * (b__ * x_).log()).cosh() * (b__ * x_).log(),
        with: [m_, a__, n_, b__, x_],
        optional: [m_, a__, n_, b__],
        when: {
            freeq!([a__, b__, m_, n_], x_)
                && eqq!(m_, &n_ - 1)
        },
        rhs: {
            let angle = &a__ * x_.pow(&n_) * (&b__ * x_).log();
            let recursive = rubi_rhs_int(&(x_.pow(&m_) * angle.cosh()), x_);

            rubi_simp(&(angle.sinh() / (&a__ * &n_)), x_)
                    - rubi_star(Atom::num(1) / &n_, recursive)
        },
    ));
}

fn push_rules_rule_6051(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6051,
        source: "Int[Sinh[d_.*(a_.+b_.*Log[c_.*x_^n_.])]^p_.,x_Symbol] :=
          x/(n*(c*x^n)^(1/n)) \\[Star] Subst[Int[x^(1/n-1)*Sinh[d*(a+b*Log[x])]^p,x],x,c*x^n] /;
        FreeQ[{a,b,c,d,n,p},x] && (NeQ[c,1] || NeQ[n,1])",
        desc: "Piecewise constant extraction and integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [d__, a__, b__, c__, n_, p_, x_],
        optional: [d__, a__, b__, c__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, n_, p_], x_) && (neq!(c__, 1) || neq!(n_, 1))
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let z = Atom::var(sub);
            let transformed = z.pow(Atom::num(1) / &n_ - 1) * (&d__ * (&a__ + &b__ * z.log())).sinh().pow(&p_);
            let primitive = rubi_rhs_int(&transformed, sub);
            let substitution = &c__ * x_.pow(&n_);
            let substituted = rubi_subst(&primitive, sub, &substitution);
            let coefficient = x_ / (&n_ * substitution.pow(Atom::num(1) / &n_));

            rubi_star(coefficient, substituted)
        },
    ));
}

fn push_rules_rule_6052(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6052,
        source: "Int[Cosh[d_.*(a_.+b_.*Log[c_.*x_^n_.])]^p_.,x_Symbol] :=
          x/(n*(c*x^n)^(1/n)) \\[Star] Subst[Int[x^(1/n-1)*Cosh[d*(a+b*Log[x])]^p,x],x,c*x^n] /;
        FreeQ[{a,b,c,d,n,p},x] && (NeQ[c,1] || NeQ[n,1])",
        desc: "Piecewise constant extraction and integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [d__, a__, b__, c__, n_, p_, x_],
        optional: [d__, a__, b__, c__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, n_, p_], x_) && (neq!(c__, 1) || neq!(n_, 1))
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let z = Atom::var(sub);
            let transformed = z.pow(Atom::num(1) / &n_ - 1) * (&d__ * (&a__ + &b__ * z.log())).cosh().pow(&p_);
            let primitive = rubi_rhs_int(&transformed, sub);
            let substitution = &c__ * x_.pow(&n_);
            let substituted = rubi_subst(&primitive, sub, &substitution);
            let coefficient = x_ / (&n_ * substitution.pow(Atom::num(1) / &n_));

            rubi_star(coefficient, substituted)
        },
    ));
}

fn push_rules_rule_6061(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6061,
        source: "Int[(e_.*x_)^m_.*Sinh[d_.*(a_.+b_.*Log[c_.*x_^n_.])]^p_.,x_Symbol] :=
          (e*x)^(m+1)/(e*n*(c*x^n)^((m+1)/n)) \\[Star] Subst[Int[x^((m+1)/n-1)*Sinh[d*(a+b*Log[x])]^p,x],x,c*x^n] /;
        FreeQ[{a,b,c,d,e,m,n,p},x] && (NeQ[c,1] || NeQ[n,1])",
        desc: "Piecewise constant extraction and integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [e__, m_, d__, a__, b__, c__, n_, p_, x_],
        optional: [e__, m_, d__, a__, b__, c__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_, p_], x_) && (neq!(c__, 1) || neq!(n_, 1))
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let z = Atom::var(sub);
            let substitution_exponent = (&m_ + 1) / &n_;
            let transformed = z.pow(&substitution_exponent - 1) * (&d__ * (&a__ + &b__ * z.log())).sinh().pow(&p_);
            let primitive = rubi_rhs_int(&transformed, sub);
            let substitution = &c__ * x_.pow(&n_);
            let substituted = rubi_subst(&primitive, sub, &substitution);
            let coefficient = (&e__ * x_).pow(&m_ + 1)
                / (&e__ * &n_ * substitution.pow(&substitution_exponent));

            rubi_star(coefficient, substituted)
        },
    ));
}

fn push_rules_rule_6062(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6062,
        source: "Int[(e_.*x_)^m_.*Cosh[d_.*(a_.+b_.*Log[c_.*x_^n_.])]^p_.,x_Symbol] :=
          (e*x)^(m+1)/(e*n*(c*x^n)^((m+1)/n)) \\[Star] Subst[Int[x^((m+1)/n-1)*Cosh[d*(a+b*Log[x])]^p,x],x,c*x^n] /;
        FreeQ[{a,b,c,d,e,m,n,p},x] && (NeQ[c,1] || NeQ[n,1])",
        desc: "Piecewise constant extraction and integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [e__, m_, d__, a__, b__, c__, n_, p_, x_],
        optional: [e__, m_, d__, a__, b__, c__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_, p_], x_) && (neq!(c__, 1) || neq!(n_, 1))
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let z = Atom::var(sub);
            let substitution_exponent = (&m_ + 1) / &n_;
            let transformed = z.pow(&substitution_exponent - 1) * (&d__ * (&a__ + &b__ * z.log())).cosh().pow(&p_);
            let primitive = rubi_rhs_int(&transformed, sub);
            let substitution = &c__ * x_.pow(&n_);
            let substituted = rubi_subst(&primitive, sub, &substitution);
            let coefficient = (&e__ * x_).pow(&m_ + 1)
                / (&e__ * &n_ * substitution.pow(&substitution_exponent));

            rubi_star(coefficient, substituted)
        },
    ));
}

fn push_rules_rule_6069(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6069,
        source: "Int[Tanh[d_.*(a_.+b_.*Log[c_.*x_^n_.])]^p_.,x_Symbol] :=
          x/(n*(c*x^n)^(1/n)) \\[Star] Subst[Int[x^(1/n-1)*Tanh[d*(a+b*Log[x])]^p,x],x,c*x^n] /;
        FreeQ[{a,b,c,d,n,p},x] && (NeQ[c,1] || NeQ[n,1])",
        desc: "Piecewise constant extraction and integration by substitution",
        refs: [],
        pattern: (d__ * (a__ + b__ * (c__ * x_.pow(n_)).log())).tanh().pow(p_),
        with: [d__, a__, b__, c__, n_, p_, x_],
        optional: [d__, a__, b__, c__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, n_, p_], x_) && (neq!(c__, 1) || neq!(n_, 1))
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let z = Atom::var(sub);
            let transformed = z.pow(Atom::num(1) / &n_ - 1) * (&d__ * (&a__ + &b__ * z.log())).tanh().pow(&p_);
            let primitive = rubi_rhs_int(&transformed, sub);
            let substitution = &c__ * x_.pow(&n_);
            let substituted = rubi_subst(&primitive, sub, &substitution);
            let coefficient = x_ / (&n_ * substitution.pow(Atom::num(1) / &n_));

            rubi_star(coefficient, substituted)
        },
    ));
}

fn push_rules_rule_6070(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6070,
        source: "Int[Coth[d_.*(a_.+b_.*Log[c_.*x_^n_.])]^p_.,x_Symbol] :=
          x/(n*(c*x^n)^(1/n)) \\[Star] Subst[Int[x^(1/n-1)*Coth[d*(a+b*Log[x])]^p,x],x,c*x^n] /;
        FreeQ[{a,b,c,d,n,p},x] && (NeQ[c,1] || NeQ[n,1])",
        desc: "Piecewise constant extraction and integration by substitution",
        refs: [],
        pattern: (d__ * (a__ + b__ * (c__ * x_.pow(n_)).log())).coth().pow(p_),
        with: [d__, a__, b__, c__, n_, p_, x_],
        optional: [d__, a__, b__, c__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, n_, p_], x_) && (neq!(c__, 1) || neq!(n_, 1))
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let z = Atom::var(sub);
            let transformed = z.pow(Atom::num(1) / &n_ - 1) * (&d__ * (&a__ + &b__ * z.log())).coth().pow(&p_);
            let primitive = rubi_rhs_int(&transformed, sub);
            let substitution = &c__ * x_.pow(&n_);
            let substituted = rubi_subst(&primitive, sub, &substitution);
            let coefficient = x_ / (&n_ * substitution.pow(Atom::num(1) / &n_));

            rubi_star(coefficient, substituted)
        },
    ));
}

fn push_rules_rule_6073(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6073,
        source: "Int[(e_.*x_)^m_.*Tanh[d_.*(a_.+b_.*Log[c_.*x_^n_.])]^p_.,x_Symbol] :=
          (e*x)^(m+1)/(e*n*(c*x^n)^((m+1)/n)) \\[Star] Subst[Int[x^((m+1)/n-1)*Tanh[d*(a+b*Log[x])]^p,x],x,c*x^n] /;
        FreeQ[{a,b,c,d,e,m,n,p},x] && (NeQ[c,1] || NeQ[n,1])",
        desc: "Piecewise constant extraction and integration by substitution",
        refs: [],
        pattern: (e__ * x_).pow(m_) * (d__ * (a__ + b__ * (c__ * x_.pow(n_)).log())).tanh().pow(p_),
        with: [e__, m_, d__, a__, b__, c__, n_, p_, x_],
        optional: [e__, m_, d__, a__, b__, c__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_, p_], x_) && (neq!(c__, 1) || neq!(n_, 1))
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let z = Atom::var(sub);
            let substitution_exponent = (&m_ + 1) / &n_;
            let transformed = z.pow(&substitution_exponent - 1) * (&d__ * (&a__ + &b__ * z.log())).tanh().pow(&p_);
            let primitive = rubi_rhs_int(&transformed, sub);
            let substitution = &c__ * x_.pow(&n_);
            let substituted = rubi_subst(&primitive, sub, &substitution);
            let coefficient = (&e__ * x_).pow(&m_ + 1)
                / (&e__ * &n_ * substitution.pow(&substitution_exponent));

            rubi_star(coefficient, substituted)
        },
    ));
}

fn push_rules_rule_6074(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6074,
        source: "Int[(e_.*x_)^m_.*Coth[d_.*(a_.+b_.*Log[c_.*x_^n_.])]^p_.,x_Symbol] :=
          (e*x)^(m+1)/(e*n*(c*x^n)^((m+1)/n)) \\[Star] Subst[Int[x^((m+1)/n-1)*Coth[d*(a+b*Log[x])]^p,x],x,c*x^n] /;
        FreeQ[{a,b,c,d,e,m,n,p},x] && (NeQ[c,1] || NeQ[n,1])",
        desc: "Piecewise constant extraction and integration by substitution",
        refs: [],
        pattern: (e__ * x_).pow(m_) * (d__ * (a__ + b__ * (c__ * x_.pow(n_)).log())).coth().pow(p_),
        with: [e__, m_, d__, a__, b__, c__, n_, p_, x_],
        optional: [e__, m_, d__, a__, b__, c__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_, p_], x_) && (neq!(c__, 1) || neq!(n_, 1))
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let z = Atom::var(sub);
            let substitution_exponent = (&m_ + 1) / &n_;
            let transformed = z.pow(&substitution_exponent - 1) * (&d__ * (&a__ + &b__ * z.log())).coth().pow(&p_);
            let primitive = rubi_rhs_int(&transformed, sub);
            let substitution = &c__ * x_.pow(&n_);
            let substituted = rubi_subst(&primitive, sub, &substitution);
            let coefficient = (&e__ * x_).pow(&m_ + 1)
                / (&e__ * &n_ * substitution.pow(&substitution_exponent));

            rubi_star(coefficient, substituted)
        },
    ));
}

fn push_rules_rule_6079(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6079,
        source: "Int[Sech[d_.*(a_.+b_.*Log[c_.*x_^n_.])]^p_.,x_Symbol] :=
          x/(n*(c*x^n)^(1/n)) \\[Star] Subst[Int[x^(1/n-1)*Sech[d*(a+b*Log[x])]^p,x],x,c*x^n] /;
        FreeQ[{a,b,c,d,n,p},x] && (NeQ[c,1] || NeQ[n,1])",
        desc: "Piecewise constant extraction and integration by substitution",
        refs: [],
        pattern: (d__ * (a__ + b__ * (c__ * x_.pow(n_)).log())).sech().pow(p_),
        with: [d__, a__, b__, c__, n_, p_, x_],
        optional: [d__, a__, b__, c__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, n_, p_], x_) && (neq!(c__, 1) || neq!(n_, 1))
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let z = Atom::var(sub);
            let transformed = z.pow(Atom::num(1) / &n_ - 1) * (&d__ * (&a__ + &b__ * z.log())).sech().pow(&p_);
            let primitive = rubi_rhs_int(&transformed, sub);
            let substitution = &c__ * x_.pow(&n_);
            let substituted = rubi_subst(&primitive, sub, &substitution);
            let coefficient = x_ / (&n_ * substitution.pow(Atom::num(1) / &n_));

            rubi_star(coefficient, substituted)
        },
    ));
}

fn push_rules_rule_6080(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6080,
        source: "Int[Csch[d_.*(a_.+b_.*Log[c_.*x_^n_.])]^p_.,x_Symbol] :=
          x/(n*(c*x^n)^(1/n)) \\[Star] Subst[Int[x^(1/n-1)*Csch[d*(a+b*Log[x])]^p,x],x,c*x^n] /;
        FreeQ[{a,b,c,d,n,p},x] && (NeQ[c,1] || NeQ[n,1])",
        desc: "Piecewise constant extraction and integration by substitution",
        refs: [],
        pattern: (d__ * (a__ + b__ * (c__ * x_.pow(n_)).log())).csch().pow(p_),
        with: [d__, a__, b__, c__, n_, p_, x_],
        optional: [d__, a__, b__, c__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, n_, p_], x_) && (neq!(c__, 1) || neq!(n_, 1))
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let z = Atom::var(sub);
            let transformed = z.pow(Atom::num(1) / &n_ - 1) * (&d__ * (&a__ + &b__ * z.log())).csch().pow(&p_);
            let primitive = rubi_rhs_int(&transformed, sub);
            let substitution = &c__ * x_.pow(&n_);
            let substituted = rubi_subst(&primitive, sub, &substitution);
            let coefficient = x_ / (&n_ * substitution.pow(Atom::num(1) / &n_));

            rubi_star(coefficient, substituted)
        },
    ));
}

fn push_rules_rule_6085(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6085,
        source: "Int[(e_.*x_)^m_.*Sech[d_.*(a_.+b_.*Log[c_.*x_^n_.])]^p_.,x_Symbol] :=
          (e*x)^(m+1)/(e*n*(c*x^n)^((m+1)/n)) \\[Star] Subst[Int[x^((m+1)/n-1)*Sech[d*(a+b*Log[x])]^p,x],x,c*x^n] /;
        FreeQ[{a,b,c,d,e,m,n,p},x] && (NeQ[c,1] || NeQ[n,1])",
        desc: "Piecewise constant extraction and integration by substitution",
        refs: [],
        pattern: (e__ * x_).pow(m_) * (d__ * (a__ + b__ * (c__ * x_.pow(n_)).log())).sech().pow(p_),
        with: [e__, m_, d__, a__, b__, c__, n_, p_, x_],
        optional: [e__, m_, d__, a__, b__, c__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_, p_], x_) && (neq!(c__, 1) || neq!(n_, 1))
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let z = Atom::var(sub);
            let substitution_exponent = (&m_ + 1) / &n_;
            let transformed = z.pow(&substitution_exponent - 1) * (&d__ * (&a__ + &b__ * z.log())).sech().pow(&p_);
            let primitive = rubi_rhs_int(&transformed, sub);
            let substitution = &c__ * x_.pow(&n_);
            let substituted = rubi_subst(&primitive, sub, &substitution);
            let coefficient = (&e__ * x_).pow(&m_ + 1)
                / (&e__ * &n_ * substitution.pow(&substitution_exponent));

            rubi_star(coefficient, substituted)
        },
    ));
}

fn push_rules_rule_6086(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 6086,
        source: "Int[(e_.*x_)^m_.*Csch[d_.*(a_.+b_.*Log[c_.*x_^n_.])]^p_.,x_Symbol] :=
          (e*x)^(m+1)/(e*n*(c*x^n)^((m+1)/n)) \\[Star] Subst[Int[x^((m+1)/n-1)*Csch[d*(a+b*Log[x])]^p,x],x,c*x^n] /;
        FreeQ[{a,b,c,d,e,m,n,p},x] && (NeQ[c,1] || NeQ[n,1])",
        desc: "Piecewise constant extraction and integration by substitution",
        refs: [],
        pattern: (e__ * x_).pow(m_) * (d__ * (a__ + b__ * (c__ * x_.pow(n_)).log())).csch().pow(p_),
        with: [e__, m_, d__, a__, b__, c__, n_, p_, x_],
        optional: [e__, m_, d__, a__, b__, c__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_, p_], x_) && (neq!(c__, 1) || neq!(n_, 1))
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let z = Atom::var(sub);
            let substitution_exponent = (&m_ + 1) / &n_;
            let transformed = z.pow(&substitution_exponent - 1) * (&d__ * (&a__ + &b__ * z.log())).csch().pow(&p_);
            let primitive = rubi_rhs_int(&transformed, sub);
            let substitution = &c__ * x_.pow(&n_);
            let substituted = rubi_subst(&primitive, sub, &substitution);
            let coefficient = (&e__ * x_).pow(&m_ + 1)
                / (&e__ * &n_ * substitution.pow(&substitution_exponent));

            rubi_star(coefficient, substituted)
        },
    ));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn downvalues_6041_through_6090_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .filter(|order| (6041..=6090).contains(order))
            .collect::<Vec<_>>();
        assert_eq!(orders, (6041..=6090).collect::<Vec<_>>());
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
    (d__ * (a__ + b__ * (c__ * x_.pow(n_)).log()))
        .cosh()
        .pow(p_)
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
    (d__ * (a__ + b__ * (c__ * x_.pow(n_)).log()))
        .sinh()
        .pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_2(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let d__ = symbols.d__;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (d__ * (a__ + b__ * x_.log())).cosh().pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_3(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let d__ = symbols.d__;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (d__ * (a__ + b__ * x_.log())).csch().pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_4(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let d__ = symbols.d__;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (d__ * (a__ + b__ * x_.log())).sech().pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_5(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let d__ = symbols.d__;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (d__ * (a__ + b__ * x_.log())).sinh().pow(p_)
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
    (e__ * x_).pow(m_)
        * (d__ * (a__ + b__ * (c__ * x_.pow(n_)).log()))
            .cosh()
            .pow(p_)
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
    (e__ * x_).pow(m_)
        * (d__ * (a__ + b__ * (c__ * x_.pow(n_)).log()))
            .sinh()
            .pow(p_)
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
    (e__ * x_).pow(m_) * (d__ * (a__ + b__ * x_.log())).cosh().pow(p_)
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
    (e__ * x_).pow(m_) * (d__ * (a__ + b__ * x_.log())).csch().pow(p_)
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
    (e__ * x_).pow(m_) * (d__ * (a__ + b__ * x_.log())).sech().pow(p_)
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
    (e__ * x_).pow(m_) * (d__ * (a__ + b__ * x_.log())).sinh().pow(p_)
}
