use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_1397(rules);
    push_rules_rule_1398(rules);
    push_rules_rule_1399(rules);
    push_rules_rule_1400(rules);
    push_rules_rule_1401(rules);
    push_rules_rule_1402(rules);
    push_rules_rule_1403(rules);
    push_rules_rule_1404(rules);
    push_rules_rule_1405(rules);
    push_rules_rule_1406(rules);
    push_rules_rule_1407(rules);
    push_rules_rule_1408(rules);
    push_rules_rule_1409(rules);
    push_rules_rule_1410(rules);
    push_rules_rule_1411(rules);
    push_rules_rule_1412(rules);
    push_rules_rule_1413(rules);
    push_rules_rule_1414(rules);
    push_rules_rule_1415(rules);
    push_rules_rule_1416(rules);
    push_rules_rule_1417(rules);
    push_rules_rule_1418(rules);
}

fn push_rules_rule_1397(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; b__, c__, p_, x_);
    rules.push(rubi_rule!(
        order: 1397,
        source: "Int[(b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
          Int[x^(2*p)*(b+c*x^2)^p,x] /;
        FreeQ[{b,c},x] && IntegerQ[p]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [b__, c__, p_, x_],
        optional: [b__, c__],
        x_free: [b__, c__],
        when: { freeq!([b__, c__], x_) && integerq!(p_) },
        rhs: {
            let recursive_integrand =
                x_.pow(Atom::num(2) * &p_) * (&b__ + &c__ * x_.pow(2)).pow(&p_);
            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_1398(rules: &mut Vec<RubiRule>) {
    rubi_symb!(b__, c__, x_);
    rules.push(rubi_rule!(
        order: 1398,
        source: "Int[Sqrt[b_.*x_^2+c_.*x_^4],x_Symbol] :=
          (b*x^2+c*x^4)^(3/2)/(3*c*x^3) /;
        FreeQ[{b,c},x]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: (b__ * x_.pow(2) + c__ * x_.pow(4)).sqrt(),
        with: [b__, c__, x_],
        optional: [b__, c__],
        x_free: [b__, c__],
        when: { freeq!([b__, c__], x_) },
        rhs: {
            let binomial = &b__ * x_.pow(2) + &c__ * x_.pow(4);
            rubi_simp(&(binomial.pow((3, 2)) / (Atom::num(3) * &c__ * x_.pow(3))), x_)
        },
    ));
}

fn push_rules_rule_1399(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; b__, c__, p_, x_);
    rules.push(rubi_rule!(
        order: 1399,
        source: "Int[(b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
          (b*x^2+c*x^4)^(p+1)/(c*(4*p+1)*x^3) -
          b*(2*p-1)/(c*(4*p+1)) \\[Star] Int[(b*x^2+c*x^4)^p/x^2,x] /;
        FreeQ[{b,c,p},x] && IGtQ[p-1/2,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [b__, c__, p_, x_],
        optional: [b__, c__],
        x_free: [b__, c__, p_],
        when: {
            freeq!([b__, c__, p_], x_)
                && igtq!(&p_ - Atom::num(1) / 2, 0)
        },
        rhs: {
            let binomial = &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let denominator = &c__ * (Atom::num(4) * &p_ + 1);
            let direct = binomial.pow(&p_ + 1) / (&denominator * x_.pow(3));
            let coefficient = &b__ * (Atom::num(2) * &p_ - 1) / denominator;
            let recursive_integrand = binomial.pow(&p_) / x_.pow(2);
            rubi_simp(&(direct), x_)
                    - rubi_star(coefficient, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1400(rules: &mut Vec<RubiRule>) {
    rubi_symb!(b__, c__, x_);
    rules.push(rubi_rule!(
        order: 1400,
        source: "Int[1/Sqrt[b_.*x_^2+c_.*x_^4],x_Symbol] :=
          -Subst[Int[1/(1-b*x^2),x],x,x/Sqrt[b*x^2+c*x^4]] /;
        FreeQ[{b,c},x]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern: Atom::num(1) / (b__ * x_.pow(2) + c__ * x_.pow(4)).sqrt(),
        with: [b__, c__, x_],
        optional: [b__, c__],
        x_free: [b__, c__],
        when: { freeq!([b__, c__], x_) },
        rhs: {
            let inner_integrand =
                Atom::num(1) / (Atom::num(1) - &b__ * x_.pow(2));
            let substitution = x_
                / (&b__ * x_.pow(2) + &c__ * x_.pow(4)).sqrt();
            -rubi_subst(
                &rubi_rhs_int(&inner_integrand, x_),
                x_,
                substitution,
            )
        },
    ));
}

fn push_rules_rule_1401(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; b__, c__, p_, x_);
    rules.push(rubi_rule!(
        order: 1401,
        source: "Int[(b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
          -(b*x^2+c*x^4)^(p+1)/(2*b*(p+1)*x) +
          (4*p+3)/(2*b*(p+1)) \\[Star] Int[(b*x^2+c*x^4)^(p+1)/x^2,x] /;
        FreeQ[{b,c},x] && Not[IntegerQ[p]] && LtQ[p,-1]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [b__, c__, p_, x_],
        optional: [b__, c__],
        x_free: [b__, c__],
        when: {
            freeq!([b__, c__], x_)
                && !integerq!(p_)
                && ltq!(p_, -1)
        },
        rhs: {
            let binomial = &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let denominator = Atom::num(2) * &b__ * (&p_ + 1);
            let direct = -binomial.pow(&p_ + 1) / (&denominator * x_);
            let coefficient = (Atom::num(4) * &p_ + 3) / denominator;
            let recursive_integrand = binomial.pow(&p_ + 1) / x_.pow(2);
            rubi_simp(&(direct), x_)
                    + rubi_star(coefficient, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1402(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; b__, c__, p_, x_);
    rules.push(rubi_rule!(
        order: 1402,
        source: "Int[(b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
          (b*x^2+c*x^4)^p/(x^(2*p)*(b+c*x^2)^p) \\[Star] Int[x^(2*p)*(b+c*x^2)^p,x] /;
        FreeQ[{b,c,p},x] && Not[IntegerQ[p]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [b__, c__, p_, x_],
        optional: [b__, c__],
        x_free: [b__, c__, p_],
        when: { freeq!([b__, c__, p_], x_) && !integerq!(p_) },
        rhs: {
            let binomial = &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let normalized = &b__ + &c__ * x_.pow(2);
            let factor = binomial.pow(&p_)
                / (x_.pow(Atom::num(2) * &p_) * normalized.pow(&p_));
            let recursive_integrand =
                x_.pow(Atom::num(2) * &p_) * normalized.pow(&p_);
            rubi_star(factor, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1403(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, p_, x_);
    rules.push(rubi_rule!(
        order: 1403,
        source: "Int[(a_.+b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
          Int[ExpandIntegrand[(a+b*x^2+c*x^4)^p,x],x] /;
        FreeQ[{a,b,c},x] && NeQ[b^2-4*a*c,0] && IGtQ[p,0]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, p_, x_],
        optional: [a__, b__, c__],
        x_free: [a__, b__, c__],
        when: {
            freeq!([a__, b__, c__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && igtq!(p_, 0)
        },
        rhs: {
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let expanded = rubi_expand_integrand(&quartic.pow(&p_), x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_1404(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, p_, x_);
    rules.push(rubi_rule!(
        order: 1404,
        source: "Int[(a_.+b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
          x*(a+b*x^2+c*x^4)^p/(4*p+1) +
          2*p/(4*p+1) \\[Star] Int[(2*a+b*x^2)*(a+b*x^2+c*x^4)^(p-1),x] /;
        FreeQ[{a,b,c},x] && NeQ[b^2-4*a*c,0] && GtQ[p,0] && IntegerQ[2*p]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, p_, x_],
        optional: [a__, b__, c__],
        x_free: [a__, b__, c__],
        when: {
            freeq!([a__, b__, c__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && gtq!(p_, 0)
                && integerq!(Atom::num(2) * &p_)
        },
        rhs: {
            let denominator = Atom::num(4) * &p_ + Atom::num(1);
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let recursive_integrand =
                (Atom::num(2) * &a__ + &b__ * x_.pow(2)) * quartic.pow(&p_ - Atom::num(1));
            rubi_simp(&(x_ * quartic.pow(&p_) / &denominator), x_)
                    + rubi_star(Atom::num(2) * &p_ / denominator, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1405(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, p_, x_);
    rules.push(rubi_rule!(
        order: 1405,
        source: "Int[(a_+b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
          -x*(b^2-2*a*c+b*c*x^2)*(a+b*x^2+c*x^4)^(p+1)/(2*a*(p+1)*(b^2-4*a*c)) +
          1/(2*a*(p+1)*(b^2-4*a*c)) \\[Star] Int[(b^2-2*a*c+2*(p+1)*(b^2-4*a*c)+b*c*(4*p+7)*x^2)*(a+b*x^2+c*x^4)^(p+1),x] /;
        FreeQ[{a,b,c},x] && NeQ[b^2-4*a*c,0] && LtQ[p,-1] && IntegerQ[2*p]",
        desc: "Trinomial recurrence 2b with m=0, A=1 and B=0",
        refs: ["G&R 2.161.5"],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, p_, x_],
        optional: [b__, c__],
        when: {
            freeq!([a__, b__, c__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && ltq!(p_, -1)
                && integerq!(Atom::num(2) * &p_)
        },
        rhs: {
            let discriminant = b__.pow(2) - Atom::num(4) * &a__ * &c__;
            let denominator = Atom::num(2) * &a__ * (&p_ + Atom::num(1)) * &discriminant;
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let raised_p = &p_ + Atom::num(1);
            let direct_numerator =
                Atom::num(-1) * x_ * (b__.pow(2) - Atom::num(2) * &a__ * &c__ + &b__ * &c__ * x_.pow(2)) * quartic.pow(&raised_p);
            let recursive_integrand = (b__.pow(2) - Atom::num(2) * &a__ * &c__
                + Atom::num(2) * &raised_p * &discriminant
                + &b__ * &c__ * (Atom::num(4) * &p_ + Atom::num(7)) * x_.pow(2))
                * quartic.pow(raised_p);
            rubi_simp(&(direct_numerator / &denominator), x_)
                    + rubi_star(Atom::num(1) / denominator, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1406(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, x_);
    rules.push(rubi_rule!(
        order: 1406,
        source: "Int[1/(a_+b_.*x_^2+c_.*x_^4),x_Symbol] :=
          With[{q=Rt[b^2-4*a*c,2]},
          c/q \\[Star] Int[1/(b/2-q/2+c*x^2),x] - c/q \\[Star] Int[1/(b/2+q/2+c*x^2),x]] /;
        FreeQ[{a,b,c},x] && NeQ[b^2-4*a*c,0] && PosQ[b^2-4*a*c]",
        desc: "Algebraic expansion",
        refs: ["G&R 2.161.1a"],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, x_],
        optional: [b__, c__],
        x_free: [a__, b__, c__],
        when: {
            let discriminant = b__.pow(2) - Atom::num(4) * &a__ * &c__;
            freeq!([a__, b__, c__], x_)
                && neq!(discriminant, 0)
                && posq!(discriminant)
        },
        rhs: {
            let discriminant = b__.pow(2) - Atom::num(4) * &a__ * &c__;
            let q = rubi_rt(&discriminant, 2);
            let first_integrand =
                Atom::num(1) / (&b__ / Atom::num(2) - &q / Atom::num(2) + &c__ * x_.pow(2));
            let second_integrand =
                Atom::num(1) / (&b__ / Atom::num(2) + &q / Atom::num(2) + &c__ * x_.pow(2));
            let coefficient = &c__ / &q;
            rubi_star(&coefficient, rubi_rhs_int(&first_integrand, x_))
                    - rubi_star(coefficient, rubi_rhs_int(&second_integrand, x_))
        },
    ));
}

fn push_rules_rule_1407(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, x_);
    rules.push(rubi_rule!(
        order: 1407,
        source: "Int[1/(a_+b_.*x_^2+c_.*x_^4),x_Symbol] :=
          With[{q=Rt[a/c,2]},
          With[{r=Rt[2*q-b/c,2]},
          1/(2*c*q*r) \\[Star] Int[(r-x)/(q-r*x+x^2),x] + 1/(2*c*q*r) \\[Star] Int[(r+x)/(q+r*x+x^2),x]]] /;
        FreeQ[{a,b,c},x] && NeQ[b^2-4*a*c,0] && NegQ[b^2-4*a*c]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, x_],
        optional: [b__, c__],
        x_free: [a__, b__, c__],
        when: {
            let discriminant = b__.pow(2) - Atom::num(4) * &a__ * &c__;
            freeq!([a__, b__, c__], x_)
                && neq!(discriminant, 0)
                && negq!(discriminant)
        },
        rhs: {
            let q = rubi_rt(&(&a__ / &c__), 2);
            let r = rubi_rt(&(Atom::num(2) * &q - &b__ / &c__), 2);
            let denominator = Atom::num(2) * &c__ * &q * &r;
            let first_integrand = (&r - x_) / (&q - &r * x_ + x_.pow(2));
            let second_integrand = (&r + x_) / (&q + &r * x_ + x_.pow(2));
            let coefficient = Atom::num(1) / denominator;
            rubi_star(&coefficient, rubi_rhs_int(&first_integrand, x_))
                    + rubi_star(coefficient, rubi_rhs_int(&second_integrand, x_))
        },
    ));
}

fn push_rules_rule_1408(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, x_);
    rules.push(rubi_rule!(
        order: 1408,
        source: "Int[1/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
          With[{q=Rt[b^2-4*a*c,2]},
          2*Sqrt[-c] \\[Star] Int[1/(Sqrt[b+q+2*c*x^2]*Sqrt[-b+q-2*c*x^2]),x]] /;
        FreeQ[{a,b,c},x] && GtQ[b^2-4*a*c,0] && LtQ[c,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, x_],
        optional: [b__, c__],
        x_free: [a__, b__, c__],
        when: {
            let discriminant = b__.pow(2) - Atom::num(4) * &a__ * &c__;
            freeq!([a__, b__, c__], x_)
                && gtq!(discriminant, 0)
                && ltq!(c__, 0)
        },
        rhs: {
            let discriminant = b__.pow(2) - Atom::num(4) * &a__ * &c__;
            let q = rubi_rt(&discriminant, 2);
            let recursive_integrand = Atom::num(1)
                / ((&b__ + &q + Atom::num(2) * &c__ * x_.pow(2)).sqrt()
                    * (-&b__ + &q - Atom::num(2) * &c__ * x_.pow(2)).sqrt());
            rubi_star(Atom::num(2) * (-&c__).sqrt(), rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1409(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, x_);
    rules.push(rubi_rule!(
        order: 1409,
        source: "Int[1/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
          With[{q=Rt[c/a,4]},
          (1+q^2*x^2)*Sqrt[(a+b*x^2+c*x^4)/(a*(1+q^2*x^2)^2)]/(2*q*Sqrt[a+b*x^2+c*x^4])*EllipticF[2*ArcTan[q*x],1/2-b*q^2/(4*c)]] /;
        FreeQ[{a,b,c},x] && GtQ[b^2-4*a*c,0] && GtQ[c/a,0] && LtQ[b/a,0]",
        desc: "Piecewise constant extraction",
        refs: ["G&R 3.165.2"],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, x_],
        optional: [b__, c__],
        x_free: [a__, b__, c__],
        when: {
            freeq!([a__, b__, c__], x_)
                && gtq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && gtq!(&c__ / &a__, 0)
                && ltq!(&b__ / &a__, 0)
        },
        rhs: {
            let q = rubi_rt(&(&c__ / &a__), 4);
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let one_plus = Atom::num(1) + q.pow(2) * x_.pow(2);
            let denominator = Atom::num(2) * &q * quartic.sqrt();
            rubi_simp(&(&one_plus
                    * (&quartic / (&a__ * one_plus.pow(2))).sqrt()
                    * rubi_elliptic_f(
                        Atom::num(2) * (&q * x_).atan(),
                        Atom::num(1) / Atom::num(2) - &b__ * q.pow(2) / (Atom::num(4) * &c__),
                    )
                    / denominator), x_)
        },
    ));
}

fn push_rules_rule_1410(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, x_);
    rules.push(rubi_rule!(
        order: 1410,
        source: "Int[1/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
          With[{q=Rt[b^2-4*a*c,2]},
          Sqrt[-2*a-(b-q)*x^2]*Sqrt[(2*a+(b+q)*x^2)/q]/(2*Sqrt[-a]*Sqrt[a+b*x^2+c*x^4])*
            EllipticF[ArcSin[x/Sqrt[(2*a+(b+q)*x^2)/(2*q)]],(b+q)/(2*q)] /;
          IntegerQ[q]] /;
        FreeQ[{a,b,c},x] && GtQ[b^2-4*a*c,0] && LtQ[a,0] && GtQ[c,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: ["G&R 3.152.3+"],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, x_],
        optional: [b__, c__],
        x_free: [a__, b__, c__],
        when: {
            let q = rubi_rt(&(b__.pow(2) - Atom::num(4) * &a__ * &c__), 2);
            freeq!([a__, b__, c__], x_)
                && gtq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && ltq!(a__, 0)
                && gtq!(c__, 0)
                && integerq!(q)
        },
        rhs: {
            let q = rubi_rt(&(b__.pow(2) - Atom::num(4) * &a__ * &c__), 2);
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let two_a_bq_x2 = Atom::num(2) * &a__ + (&b__ + &q) * x_.pow(2);
            let amplitude_denominator = (&two_a_bq_x2 / (Atom::num(2) * &q)).sqrt();
            let denominator = Atom::num(2) * (-&a__).sqrt() * quartic.sqrt();
            (-Atom::num(2) * &a__ - (&b__ - &q) * x_.pow(2)).sqrt()
                    * (&two_a_bq_x2 / &q).sqrt()
                    * rubi_elliptic_f(
                        (x_ / amplitude_denominator).asin(),
                        (&b__ + &q) / (Atom::num(2) * &q),
                    )
                    / denominator
        },
    ));
}

fn push_rules_rule_1411(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, x_);
    rules.push(rubi_rule!(
        order: 1411,
        source: "Int[1/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
          With[{q=Rt[b^2-4*a*c,2]},
          Sqrt[(2*a+(b-q)*x^2)/(2*a+(b+q)*x^2)]*Sqrt[(2*a+(b+q)*x^2)/q]/(2*Sqrt[a+b*x^2+c*x^4]*Sqrt[a/(2*a+(b+q)*x^2)])*
            EllipticF[ArcSin[x/Sqrt[(2*a+(b+q)*x^2)/(2*q)]],(b+q)/(2*q)]] /;
        FreeQ[{a,b,c},x] && GtQ[b^2-4*a*c,0] && LtQ[a,0] && GtQ[c,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: ["G&R 3.152.3+"],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, x_],
        optional: [b__, c__],
        x_free: [a__, b__, c__],
        when: {
            freeq!([a__, b__, c__], x_)
                && gtq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && ltq!(a__, 0)
                && gtq!(c__, 0)
        },
        rhs: {
            let q = rubi_rt(&(b__.pow(2) - Atom::num(4) * &a__ * &c__), 2);
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let two_a_bq_x2 = Atom::num(2) * &a__ + (&b__ + &q) * x_.pow(2);
            let amplitude_denominator = (&two_a_bq_x2 / (Atom::num(2) * &q)).sqrt();
            let denominator = Atom::num(2) * quartic.sqrt() * (&a__ / &two_a_bq_x2).sqrt();
            rubi_simp(&(((Atom::num(2) * &a__ + (&b__ - &q) * x_.pow(2)) / &two_a_bq_x2).sqrt()
                    * (two_a_bq_x2 / &q).sqrt()
                    * rubi_elliptic_f(
                        (x_ / amplitude_denominator).asin(),
                        (&b__ + &q) / (Atom::num(2) * &q),
                    )
                    / denominator), x_)
        },
    ));
}

fn push_rules_rule_1412(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, x_);
    rules.push(rubi_rule!(
        order: 1412,
        source: "Int[1/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
          With[{q=Rt[b^2-4*a*c,2]},
          (2*a+(b+q)*x^2)*Sqrt[(2*a+(b-q)*x^2)/(2*a+(b+q)*x^2)]/(2*a*Rt[(b+q)/(2*a),2]*Sqrt[a+b*x^2+c*x^4])*
            EllipticF[ArcTan[Rt[(b+q)/(2*a),2]*x],2*q/(b+q)] /;
         PosQ[(b+q)/a] && Not[PosQ[(b-q)/a] && SimplerSqrtQ[(b-q)/(2*a),(b+q)/(2*a)]]] /;
        FreeQ[{a,b,c},x] && GtQ[b^2-4*a*c,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, x_],
        optional: [b__, c__],
        x_free: [a__, b__, c__],
        when: {
            let q = rubi_rt(&(b__.pow(2) - Atom::num(4) * &a__ * &c__), 2);
            freeq!([a__, b__, c__], x_)
                && gtq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && posq!((&b__ + &q) / &a__)
                && !(posq!((&b__ - &q) / &a__)
                    && rubi_simpler_sqrt_q(
                        &((&b__ - &q) / (Atom::num(2) * &a__)),
                        &((&b__ + &q) / (Atom::num(2) * &a__)),
                    ))
        },
        rhs: {
            let q = rubi_rt(&(b__.pow(2) - Atom::num(4) * &a__ * &c__), 2);
            let b_plus_q = &b__ + &q;
            let rt = rubi_rt(&(&b_plus_q / (Atom::num(2) * &a__)), 2);
            let denominator = Atom::num(2) * &a__ * &rt;
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let two_a_bq_x2 = Atom::num(2) * &a__ + &b_plus_q * x_.pow(2);
            let displayed_denominator = &denominator * quartic.sqrt();
            &two_a_bq_x2
                    * ((Atom::num(2) * &a__ + (&b__ - &q) * x_.pow(2)) / &two_a_bq_x2).sqrt()
                    * rubi_elliptic_f(
                        (&rt * x_).atan(),
                        Atom::num(2) * &q / b_plus_q,
                    )
                    / displayed_denominator
        },
    ));
}

fn push_rules_rule_1413(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, x_);
    rules.push(rubi_rule!(
        order: 1413,
        source: "Int[1/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
          With[{q=Rt[b^2-4*a*c,2]},
          (2*a+(b-q)*x^2)*Sqrt[(2*a+(b+q)*x^2)/(2*a+(b-q)*x^2)]/(2*a*Rt[(b-q)/(2*a),2]*Sqrt[a+b*x^2+c*x^4])*
            EllipticF[ArcTan[Rt[(b-q)/(2*a),2]*x],-2*q/(b-q)] /;
         PosQ[(b-q)/a]] /;
        FreeQ[{a,b,c},x] && GtQ[b^2-4*a*c,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: ["G&R 3.152.1-"],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, x_],
        optional: [b__, c__],
        x_free: [a__, b__, c__],
        when: {
            let q = rubi_rt(&(b__.pow(2) - Atom::num(4) * &a__ * &c__), 2);
            freeq!([a__, b__, c__], x_)
                && gtq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && posq!((&b__ - &q) / &a__)
        },
        rhs: {
            let q = rubi_rt(&(b__.pow(2) - Atom::num(4) * &a__ * &c__), 2);
            let b_minus_q = &b__ - &q;
            let rt = rubi_rt(&(&b_minus_q / (Atom::num(2) * &a__)), 2);
            let denominator = Atom::num(2) * &a__ * &rt;
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let two_a_bq_x2 = Atom::num(2) * &a__ + &b_minus_q * x_.pow(2);
            let displayed_denominator = &denominator * quartic.sqrt();
            &two_a_bq_x2
                    * ((Atom::num(2) * &a__ + (&b__ + &q) * x_.pow(2)) / &two_a_bq_x2).sqrt()
                    * rubi_elliptic_f(
                        (&rt * x_).atan(),
                        -Atom::num(2) * &q / b_minus_q,
                    )
                    / displayed_denominator
        },
    ));
}

fn push_rules_rule_1414(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, x_);
    rules.push(rubi_rule!(
        order: 1414,
        source: "Int[1/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
          With[{q=Rt[b^2-4*a*c,2]},
          Sqrt[1+(b+q)*x^2/(2*a)]*Sqrt[1+(b-q)*x^2/(2*a)]/(Rt[-(b+q)/(2*a),2]*Sqrt[a+b*x^2+c*x^4])*
            EllipticF[ArcSin[Rt[-(b+q)/(2*a),2]*x],(b-q)/(b+q)] /;
         NegQ[(b+q)/a] && Not[NegQ[(b-q)/a] && SimplerSqrtQ[-(b-q)/(2*a),-(b+q)/(2*a)]]] /;
        FreeQ[{a,b,c},x] && GtQ[b^2-4*a*c,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, x_],
        optional: [b__, c__],
        x_free: [a__, b__, c__],
        when: {
            let q = rubi_rt(&(b__.pow(2) - Atom::num(4) * &a__ * &c__), 2);
            freeq!([a__, b__, c__], x_)
                && gtq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && negq!((&b__ + &q) / &a__)
                && !(negq!((&b__ - &q) / &a__)
                    && rubi_simpler_sqrt_q(
                        &(-(&b__ - &q) / (Atom::num(2) * &a__)),
                        &(-(&b__ + &q) / (Atom::num(2) * &a__)),
                    ))
        },
        rhs: {
            let q = rubi_rt(&(b__.pow(2) - Atom::num(4) * &a__ * &c__), 2);
            let b_plus_q = &b__ + &q;
            let rt = rubi_rt(&(-&b_plus_q / (Atom::num(2) * &a__)), 2);
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let displayed_denominator = &rt * quartic.sqrt();
            (Atom::num(1) + &b_plus_q * x_.pow(2) / (Atom::num(2) * &a__)).sqrt()
                    * (Atom::num(1) + (&b__ - &q) * x_.pow(2) / (Atom::num(2) * &a__)).sqrt()
                    * rubi_elliptic_f(
                        (&rt * x_).asin(),
                        (&b__ - &q) / b_plus_q,
                    )
                    / displayed_denominator
        },
    ));
}

fn push_rules_rule_1415(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, x_);
    rules.push(rubi_rule!(
        order: 1415,
        source: "Int[1/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
          With[{q=Rt[b^2-4*a*c,2]},
          Sqrt[1+(b-q)*x^2/(2*a)]*Sqrt[1+(b+q)*x^2/(2*a)]/(Rt[-(b-q)/(2*a),2]*Sqrt[a+b*x^2+c*x^4])*
            EllipticF[ArcSin[Rt[-(b-q)/(2*a),2]*x],(b+q)/(b-q)] /;
         NegQ[(b-q)/a]] /;
        FreeQ[{a,b,c},x] && GtQ[b^2-4*a*c,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: ["G&R 3.152.7-"],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, x_],
        optional: [b__, c__],
        x_free: [a__, b__, c__],
        when: {
            let q = rubi_rt(&(b__.pow(2) - Atom::num(4) * &a__ * &c__), 2);
            freeq!([a__, b__, c__], x_)
                && gtq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && negq!((&b__ - &q) / &a__)
        },
        rhs: {
            let q = rubi_rt(&(b__.pow(2) - Atom::num(4) * &a__ * &c__), 2);
            let b_minus_q = &b__ - &q;
            let rt = rubi_rt(&(-&b_minus_q / (Atom::num(2) * &a__)), 2);
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let displayed_denominator = &rt * quartic.sqrt();
            (Atom::num(1) + &b_minus_q * x_.pow(2) / (Atom::num(2) * &a__)).sqrt()
                    * (Atom::num(1) + (&b__ + &q) * x_.pow(2) / (Atom::num(2) * &a__)).sqrt()
                    * rubi_elliptic_f(
                        (&rt * x_).asin(),
                        (&b__ + &q) / b_minus_q,
                    )
                    / displayed_denominator
        },
    ));
}

fn push_rules_rule_1416(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, x_);
    rules.push(rubi_rule!(
        order: 1416,
        source: "Int[1/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
          With[{q=Rt[c/a,4]},
          (1+q^2*x^2)*Sqrt[(a+b*x^2+c*x^4)/(a*(1+q^2*x^2)^2)]/(2*q*Sqrt[a+b*x^2+c*x^4])*EllipticF[2*ArcTan[q*x],1/2-b*q^2/(4*c)]] /;
        FreeQ[{a,b,c},x] && NeQ[b^2-4*a*c,0] && PosQ[c/a]",
        desc: "Piecewise constant extraction",
        refs: ["G&R 3.165.2"],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, x_],
        optional: [b__, c__],
        x_free: [a__, b__, c__],
        when: {
            freeq!([a__, b__, c__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && posq!(&c__ / &a__)
        },
        rhs: {
            let q = rubi_rt(&(&c__ / &a__), 4);
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let one_plus = Atom::num(1) + q.pow(2) * x_.pow(2);
            let denominator = Atom::num(2) * &q * quartic.sqrt();
            rubi_simp(&(&one_plus
                    * (&quartic / (&a__ * one_plus.pow(2))).sqrt()
                    * rubi_elliptic_f(
                        Atom::num(2) * (&q * x_).atan(),
                        Atom::num(1) / Atom::num(2) - &b__ * q.pow(2) / (Atom::num(4) * &c__),
                    )
                    / denominator), x_)
        },
    ));
}

fn push_rules_rule_1417(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, x_);
    rules.push(rubi_rule!(
        order: 1417,
        source: "Int[1/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
          With[{q=Rt[b^2-4*a*c,2]},
          Sqrt[1+2*c*x^2/(b-q)]*Sqrt[1+2*c*x^2/(b+q)]/Sqrt[a+b*x^2+c*x^4] \\[Star]
            Int[1/(Sqrt[1+2*c*x^2/(b-q)]*Sqrt[1+2*c*x^2/(b+q)]),x]] /;
        FreeQ[{a,b,c},x] && NeQ[b^2-4*a*c,0] && NegQ[c/a]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, x_],
        optional: [b__, c__],
        x_free: [a__, b__, c__],
        when: {
            freeq!([a__, b__, c__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && negq!(&c__ / &a__)
        },
        rhs: {
            let q = rubi_rt(&(b__.pow(2) - Atom::num(4) * &a__ * &c__), 2);
            let b_plus_q = &b__ + &q;
            let b_minus_q = &b__ - &q;
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let first = Atom::num(1) + Atom::num(2) * &c__ * x_.pow(2) / &b_minus_q;
            let second = Atom::num(1) + Atom::num(2) * &c__ * x_.pow(2) / &b_plus_q;
            let denominator = quartic.sqrt();
            let recursive_integrand = Atom::num(1) / (&first.sqrt() * &second.sqrt());
            let factor = first.sqrt() * second.sqrt() / denominator;
            rubi_star(factor, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1418(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, p_, x_);
    rules.push(rubi_rule!(
        order: 1418,
        source: "Int[(a_+b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
          With[{q=Rt[b^2-4*a*c,2]},
          a^IntPart[p]*(a+b*x^2+c*x^4)^FracPart[p]/((1+2*c*x^2/(b+q))^FracPart[p]*(1+2*c*x^2/(b-q))^FracPart[p]) \\[Star]
            Int[(1+2*c*x^2/(b+q))^p*(1+2*c*x^2/(b-q))^p,x]] /;
        FreeQ[{a,b,c,p},x] && NeQ[b^2-4*a*c,0]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, p_, x_],
        optional: [b__, c__],
        x_free: [a__, b__, c__, p_],
        when: {
            freeq!([a__, b__, c__, p_], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
        },
        rhs: {
            let q = rubi_rt(&(b__.pow(2) - Atom::num(4) * &a__ * &c__), 2);
            let b_plus_q = &b__ + &q;
            let b_minus_q = &b__ - &q;
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let frac_p = rubi_frac_part(&p_);
            let first = Atom::num(1) + Atom::num(2) * &c__ * x_.pow(2) / &b_plus_q;
            let second = Atom::num(1) + Atom::num(2) * &c__ * x_.pow(2) / &b_minus_q;
            let denominator = first.pow(&frac_p) * second.pow(&frac_p);
            let factor = a__.pow(rubi_int_part(&p_)) * quartic.pow(&frac_p) / denominator;
            let recursive_integrand = first.pow(&p_) * second.pow(&p_);
            rubi_star(factor, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

// Generated shared pattern builders.

#[inline(never)]
fn rubi_shared_pattern_0(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (a__ + b__ * x_.pow(2) + c__ * x_.pow(4)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (b__ * x_.pow(2) + c__ * x_.pow(4)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_2(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let x_ = symbols.x_;
    Atom::num(1) / (a__ + b__ * x_.pow(2) + c__ * x_.pow(4))
}

#[inline(never)]
fn rubi_shared_pattern_3(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let x_ = symbols.x_;
    Atom::num(1) / (a__ + b__ * x_.pow(2) + c__ * x_.pow(4)).sqrt()
}
