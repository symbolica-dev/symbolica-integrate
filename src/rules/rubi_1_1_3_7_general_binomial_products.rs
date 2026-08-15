use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_2389(rules);
    push_rules_rule_2390(rules);
    push_rules_rule_2391(rules);
    push_rules_rule_2392(rules);
    push_rules_rule_2393(rules);
    push_rules_rule_2394(rules);
    push_rules_rule_2395(rules);
    push_rules_rule_2396(rules);
    push_rules_rule_2397(rules);
    push_rules_rule_2398(rules);
    push_rules_rule_2399(rules);
    push_rules_rule_2400(rules);
    push_rules_rule_2401(rules);
    push_rules_rule_2402(rules);
    push_rules_rule_2403(rules);
    push_rules_rule_2404(rules);
    push_rules_rule_2405(rules);
    push_rules_rule_2406(rules);
    push_rules_rule_2407(rules);
    push_rules_rule_2408(rules);
    push_rules_rule_2409(rules);
    push_rules_rule_2410(rules);
    push_rules_rule_2411(rules);
    push_rules_rule_2412(rules);
    push_rules_rule_2413(rules);
    push_rules_rule_2414(rules);
    push_rules_rule_2415(rules);
    push_rules_rule_2416(rules);
    push_rules_rule_2417(rules);
    push_rules_rule_2418(rules);
    push_rules_rule_2419(rules);
    push_rules_rule_2420(rules);
    push_rules_rule_2421(rules);
    push_rules_rule_2422(rules);
    push_rules_rule_2423(rules);
    push_rules_rule_2371(rules);
    push_rules_rule_2424(rules);
    push_rules_rule_2425(rules);
    push_rules_rule_2426(rules);
    push_rules_rule_2427(rules);
    push_rules_rule_2428(rules);
    push_rules_rule_2429(rules);
    push_rules_rule_2430(rules);
    push_rules_rule_2431(rules);
    push_rules_rule_2432(rules);
    push_rules_rule_2433(rules);
    push_rules_rule_2434(rules);
    push_rules_rule_2435(rules);
    push_rules_rule_2436(rules);
    push_rules_rule_2437(rules);
    push_rules_rule_2438(rules);
    push_rules_rule_2439(rules);
}

fn push_rules_rule_2389(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, n_, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2389,
        source: "Int[Pq_*(a_+b_.*x_^n_.)^p_.,x_Symbol] :=
          Int[ExpandIntegrand[Pq*(a+b*x^n)^p,x],x] /;
        FreeQ[{a,b,n},x] && PolyQ[Pq,x] && (IGtQ[p,0] || EqQ[n,1])",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [pq__, a__, b__, n_, p_, x_],
        optional: [b__, n_, p_],
        when: {
            freeq!([a__, b__, n_], x_)
                && poly_q(&pq__, x_)
                && (igtq!(p_, 0) || eqq!(n_, 1))
        },
        rhs: {
            let integrand = &pq__ * (&a__ + &b__ * x_.pow(&n_)).pow(&p_);
            let expanded = rubi_expand_integrand(&integrand, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_2390(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, n_, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2390,
        source: "Int[Pq_*(a_+b_.*x_^n_.)^p_,x_Symbol] :=
          Int[x*PolynomialQuotient[Pq,x,x]*(a+b*x^n)^p,x] /;
        FreeQ[{a,b,n,p},x] && PolyQ[Pq,x] && EqQ[Coeff[Pq,x,0],0] && Not[MatchQ[Pq,x^m_.*u_. /; IntegerQ[m]]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [pq__, a__, b__, n_, p_, x_],
        optional: [b__, n_],
        when: {
            freeq!([a__, b__, n_, p_], x_)
                && rubi_poly_q(&pq__, x_)
                && rubi_coeff(&pq__, x_, 0).is_some_and(|coeff| eqq!(coeff, 0))
                && !visible_integer_power_of_variable_factor(&pq__, x_)
        },
        rhs: {
            let quotient = rubi_polynomial_quotient(&pq__, x_, x_).unwrap();
            let transformed = x_ * quotient * (&a__ + &b__ * x_.pow(&n_)).pow(&p_);
            rubi_rhs_int(&transformed, x_)
        },
    ));
}

fn push_rules_rule_2391(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, n_, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2391,
        source: "Int[Pq_*(a_+b_.*x_^n_.)^p_.,x_Symbol] :=
          Int[PolynomialQuotient[Pq,a+b*x^n,x]*(a+b*x^n)^(p+1),x] /;
        FreeQ[{a,b,p},x] && PolyQ[Pq,x] && IGtQ[n,0] && GeQ[Expon[Pq,x],n] && EqQ[PolynomialRemainder[Pq,a+b*x^n,x],0]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [pq__, a__, b__, n_, p_, x_],
        optional: [b__, n_, p_],
        when: {
            let denominator = &a__ + &b__ * x_.pow(&n_);
            freeq!([a__, b__, p_], x_)
                && rubi_poly_q(&pq__, x_)
                && igtq!(n_, 0)
                && rubi_expon(&pq__, x_).is_some_and(|degree| geq!(Atom::num(degree), n_))
                && rubi_polynomial_remainder(&pq__, &denominator, x_).is_some_and(|remainder| eqq!(remainder, 0))
        },
        rhs: {
            let denominator = &a__ + &b__ * x_.pow(&n_);
            let quotient = rubi_polynomial_quotient(&pq__, &denominator, x_).unwrap();
            let transformed = quotient * denominator.pow(&p_ + Atom::num(1));
            rubi_rhs_int(&transformed, x_)
        },
    ));
}

fn push_rules_rule_2392(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, n_, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2392,
        source: "Int[Pq_*(a_+b_.*x_^n_.)^p_,x_Symbol] :=
          Module[{q=Expon[Pq,x],i},
          (a+b*x^n)^p*Sum[Coeff[Pq,x,i]*x^(i+1)/(n*p+i+1),{i,0,q}] +
          a*n*p \\[Star] Int[(a+b*x^n)^(p-1)*Sum[Coeff[Pq,x,i]*x^i/(n*p+i+1),{i,0,q}],x]] /;
        FreeQ[{a,b},x] && PolyQ[Pq,x] && IGtQ[(n-1)/2,0] && GtQ[p,0]",
        desc: "Binomial recurrence 1b applied qBold times",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [pq__, a__, b__, n_, p_, x_],
        optional: [b__, n_],
        when: {
            freeq!([a__, b__], x_)
                && poly_q(&pq__, x_)
                && igtq!((&n_ - Atom::num(1)) / Atom::num(2), 0)
                && gtq!(p_, 0)
        },
        rhs: {
            let q = rubi_expon(&pq__, x_).unwrap();
            let base = &a__ + &b__ * x_.pow(&n_);
            let mut direct_sum = Atom::num(0);
            let mut recursive_sum = Atom::num(0);
            for i in 0..=q {
                let coefficient = rubi_coeff(&pq__, x_, i).unwrap();
                let denominator = &n_ * &p_ + Atom::num(i + 1);
                direct_sum += &coefficient * x_.pow(i + 1) / &denominator;
                recursive_sum += coefficient * x_.pow(i) / denominator;
            }
            let recursive_integrand = base.pow(&p_ - Atom::num(1)) * recursive_sum;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let direct = rubi_simp(&(base.pow(&p_) * direct_sum), x_);
            let recursive_term = rubi_simp(&(&a__ * &n_ * &p_ * recursive), x_);

            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1), recursive_term)
        },
    ));
}

fn push_rules_rule_2393(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, n_, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2393,
        source: "Int[Pq_*(a_+b_.*x_^n_)^p_,x_Symbol] :=
          Module[{q=Expon[Pq,x],i},
          (a*Coeff[Pq,x,q]-b*x*ExpandToSum[Pq-Coeff[Pq,x,q]*x^q,x])*(a+b*x^n)^(p+1)/(a*b*n*(p+1)) +
          1/(a*n*(p+1)) \\[Star] Int[Sum[(n*(p+1)+i+1)*Coeff[Pq,x,i]*x^i,{i,0,q-1}]*(a+b*x^n)^(p+1),x] /;
         q==n-1] /;
        FreeQ[{a,b},x] && PolyQ[Pq,x] && IGtQ[n,0] && LtQ[p,-1]",
        desc: "Algebraic expansion and binomial recurrence 2b applied q-1Bold times",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [pq__, a__, b__, n_, p_, x_],
        optional: [b__],
        when: {
            match rubi_expon(&pq__, x_) {
                Some(q) => {
                    freeq!([a__, b__], x_)
                        && rubi_poly_q(&pq__, x_)
                        && igtq!(n_, 0)
                        && ltq!(p_, -1)
                        && eqq!(Atom::num(q), &n_ - Atom::num(1))
                }
                None => false,
            }
        },
        rhs: {
            let q = rubi_expon(&pq__, x_).unwrap();
            let coefficient = rubi_coeff(&pq__, x_, q).unwrap();
            let base = &a__ + &b__ * x_.pow(&n_);
            let raised_p = &p_ + Atom::num(1);
            let remainder = rubi_expand_to_sum(&(&pq__ - &coefficient * x_.pow(q)), x_);
            let direct = (&a__ * &coefficient - &b__ * x_ * remainder) * base.pow(&raised_p)
                / (&a__ * &b__ * &n_ * &raised_p);
            let mut payload = Atom::num(0);
            for i in 0..q {
                let coefficient_i = rubi_coeff(&pq__, x_, i).unwrap();
                payload += (&n_ * &raised_p + Atom::num(i + 1)) * coefficient_i * x_.pow(i);
            }
            let recursive_integrand = payload * base.pow(&raised_p);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&direct, x_)
                    + rubi_star(
                        Atom::num(1) / (&a__ * &n_ * raised_p),
                        recursive,
                    )
        },
    ));
}

fn push_rules_rule_2394(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, n_, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2394,
        source: "Int[Pq_*(a_+b_.*x_^n_.)^p_,x_Symbol] :=
          -x*Pq*(a+b*x^n)^(p+1)/(a*n*(p+1)) +
          1/(a*n*(p+1)) \\[Star] Int[ExpandToSum[n*(p+1)*Pq+D[x*Pq,x],x]*(a+b*x^n)^(p+1),x] /;
        FreeQ[{a,b},x] && PolyQ[Pq,x] && IGtQ[n,0] && LtQ[p,-1] && LtQ[Expon[Pq,x],n-1]",
        desc: "Binomial recurrence 2b applied qBold times",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [pq__, a__, b__, n_, p_, x_],
        optional: [b__, n_],
        when: {
            match rubi_expon(&pq__, x_) {
                Some(q) => {
                    freeq!([a__, b__], x_)
                        && rubi_poly_q(&pq__, x_)
                        && igtq!(n_, 0)
                        && ltq!(p_, -1)
                        && ltq!(Atom::num(q), &n_ - Atom::num(1))
                }
                None => false,
            }
        },
        rhs: {
            let base = &a__ + &b__ * x_.pow(&n_);
            let raised_p = &p_ + Atom::num(1);
            let direct = Atom::num(-1) * x_ * &pq__ * base.pow(&raised_p) / (&a__ * &n_ * &raised_p);
            let payload = rubi_expand_to_sum(&(&n_ * &raised_p * &pq__ + (x_ * &pq__).derivative(x_)), x_);
            let recursive_integrand = payload * base.pow(&raised_p);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&direct, x_) + rubi_star(Atom::num(1) / (&a__ * &n_ * raised_p), recursive)
        },
    ));
}

fn push_rules_rule_2395(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, p4__, x_);
    rules.push(rubi_rule!(
        order: 2395,
        source: "Int[P4_/(a_+b_.*x_^4)^(3/2),x_Symbol] :=
          With[{d=Coeff[P4,x,0],e=Coeff[P4,x,1],f=Coeff[P4,x,3],g=Coeff[P4,x,4]},
          -(a*f+2*a*g*x-b*e*x^2)/(2*a*b*Sqrt[a+b*x^4]) /;
         EqQ[b*d+a*g,0]] /;
        FreeQ[{a,b},x] && PolyQ[P4,x,4] && EqQ[Coeff[P4,x,2],0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: p4__ / (a__ + b__ * x_.pow(4)).pow((3, 2)),
        with: [p4__, a__, b__, x_],
        optional: [b__],
        when: {
            let d = rubi_coeff(&p4__, x_, 0);
            let g = rubi_coeff(&p4__, x_, 4);
            freeq!([a__, b__], x_)
                && rubi_poly_q_degree(&p4__, x_, 4)
                && rubi_coeff(&p4__, x_, 2).is_some_and(|coefficient| eqq!(coefficient, 0))
                && d.as_ref()
                    .zip(g.as_ref())
                    .is_some_and(|(d, g)| eqq!(&b__ * d + &a__ * g, 0))
        },
        rhs: {
            let e = rubi_coeff(&p4__, x_, 1).unwrap();
            let f = rubi_coeff(&p4__, x_, 3).unwrap();
            let g = rubi_coeff(&p4__, x_, 4).unwrap();
            let base = &a__ + &b__ * x_.pow(4);
            let result = -(&a__ * f + Atom::num(2) * &a__ * g * x_ - &b__ * e * x_.pow(2))
                / (Atom::num(2) * a__ * b__ * base.sqrt());

            rubi_simp(&result, x_)
        },
    ));
}

fn push_rules_rule_2396(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, p6__, x_);
    rules.push(rubi_rule!(
        order: 2396,
        source: "Int[P6_/(a_+b_.*x_^4)^(3/2),x_Symbol] :=
          With[{d=Coeff[P6,x,0],e=Coeff[P6,x,2],f=Coeff[P6,x,3],g=Coeff[P6,x,4],h=Coeff[P6,x,6]},
          -(a*f-2*b*d*x-2*a*h*x^3)/(2*a*b*Sqrt[a+b*x^4]) /;
         EqQ[b*e-3*a*h,0] && EqQ[b*d+a*g,0]] /;
        FreeQ[{a,b},x] && PolyQ[P6,x,6] && EqQ[Coeff[P6,x,1],0] && EqQ[Coeff[P6,x,5],0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: p6__ / (a__ + b__ * x_.pow(4)).pow((3, 2)),
        with: [p6__, a__, b__, x_],
        optional: [b__],
        when: {
            let d = rubi_coeff(&p6__, x_, 0);
            let e = rubi_coeff(&p6__, x_, 2);
            let g = rubi_coeff(&p6__, x_, 4);
            let h = rubi_coeff(&p6__, x_, 6);
            freeq!([a__, b__], x_)
                && rubi_poly_q_degree(&p6__, x_, 6)
                && rubi_coeff(&p6__, x_, 1).is_some_and(|coefficient| eqq!(coefficient, 0))
                && rubi_coeff(&p6__, x_, 5).is_some_and(|coefficient| eqq!(coefficient, 0))
                && e.as_ref()
                    .zip(h.as_ref())
                    .is_some_and(|(e, h)| eqq!(&b__ * e - Atom::num(3) * &a__ * h, 0))
                && d.as_ref()
                    .zip(g.as_ref())
                    .is_some_and(|(d, g)| eqq!(&b__ * d + &a__ * g, 0))
        },
        rhs: {
            let d = rubi_coeff(&p6__, x_, 0).unwrap();
            let f = rubi_coeff(&p6__, x_, 3).unwrap();
            let h = rubi_coeff(&p6__, x_, 6).unwrap();
            let base = &a__ + &b__ * x_.pow(4);
            let result = -(&a__ * f - Atom::num(2) * &b__ * d * x_ - Atom::num(2) * &a__ * h * x_.pow(3))
                / (Atom::num(2) * a__ * b__ * base.sqrt());

            rubi_simp(&result, x_)
        },
    ));
}

fn push_rules_rule_2397(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, n_, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2397,
        source: "Int[Pq_*(a_+b_.*x_^n_.)^p_,x_Symbol] :=
          With[{q=Expon[Pq,x]},
          Module[{Q=PolynomialQuotient[b^(Floor[(q-1)/n]+1)*Pq,a+b*x^n,x],
                  R=PolynomialRemainder[b^(Floor[(q-1)/n]+1)*Pq,a+b*x^n,x]},
          -x*R*(a+b*x^n)^(p+1)/(a*n*(p+1)*b^(Floor[(q-1)/n]+1)) +
          1/(a*n*(p+1)*b^(Floor[(q-1)/n]+1)) \\[Star] Int[(a+b*x^n)^(p+1)*ExpandToSum[a*n*(p+1)*Q+n*(p+1)*R+D[x*R,x],x],x]] /;
         GeQ[q,n]] /;
        FreeQ[{a,b},x] && PolyQ[Pq,x] && IGtQ[n,0] && LtQ[p,-1]",
        desc: "Algebraic expansion and binomial recurrence 2b applied n-1Bold times",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [pq__, a__, b__, n_, p_, x_],
        optional: [b__, n_],
        when: {
            match polynomial_degree(&pq__, x_) {
                Some(q) => {
                    freeq!([a__, b__], x_)
                        && poly_q(&pq__, x_)
                        && igtq!(n_, 0)
                        && ltq!(p_, -1)
                        && geq!(Atom::num(q), n_)
                }
                None => false,
            }
        },
        rhs: {
            let q = polynomial_degree(&pq__, x_).rubi_rhs();
            let n_integer = integer_i64(&n_).rubi_rhs();
            if n_integer <= 0 || q < n_integer {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }
            let k = (q - 1).div_euclid(n_integer) + 1;
            let scale = b__.pow(k);
            let base = &a__ + &b__ * x_.pow(&n_);
            let scaled_px = &scale * &pq__;
            let (capital_q, capital_r) = polynomial_quotient_remainder(&scaled_px, &base, x_).rubi_rhs();
            let raised_p = (&p_ + Atom::num(1)).expand();
            if raised_p.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }
            let denominator = &a__ * &n_ * &raised_p * &scale;
            let direct = Atom::num(-1) * x_ * &capital_r * base.pow(&raised_p) / &denominator;
            let payload = (&a__ * &n_ * &raised_p * capital_q
                + &n_ * &raised_p * &capital_r
                + (x_ * capital_r).derivative(x_))
            .expand();
            let recursive_integrand = base.pow(&raised_p) * payload;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            direct + rubi_star(Atom::num(1) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_2398(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_a__, capital_b__, a__, b__, x_);
    rules.push(rubi_rule!(
        order: 2398,
        source: "Int[(A_+B_.*x_)/(a_+b_.*x_^3),x_Symbol] :=
          B^3/b \\[Star] Int[1/(A^2-A*B*x+B^2*x^2),x] /;
        FreeQ[{a,b,A,B},x] && EqQ[a*B^3-b*A^3,0]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [capital_a__, capital_b__, a__, b__, x_],
        optional: [capital_b__, b__],
        when: {
            freeq!([capital_a__, capital_b__, a__, b__], x_)
                && eqq!(&a__ * capital_b__.pow(3) - &b__ * capital_a__.pow(3), 0)
        },
        rhs: {
            let recursive_integrand =
                Atom::num(1) / (capital_a__.pow(2) - &capital_a__ * &capital_b__ * x_ + capital_b__.pow(2) * x_.pow(2));
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(capital_b__.pow(3), recursive / b__)
        },
    ));
}

fn push_rules_rule_2399(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_a__, capital_b__, a__, b__, x_);
    rules.push(rubi_rule!(
        order: 2399,
        source: "Int[(A_+B_.*x_)/(a_+b_.*x_^3),x_Symbol] :=
          With[{r=Numerator[Rt[a/b,3]], s=Denominator[Rt[a/b,3]]},
          -r*(B*r-A*s)/(3*a*s) \\[Star] Int[1/(r+s*x),x] +
          r/(3*a*s) \\[Star] Int[(r*(B*r+2*A*s)+s*(B*r-A*s)*x)/(r^2-r*s*x+s^2*x^2),x]] /;
        FreeQ[{a,b,A,B},x] && NeQ[a*B^3-b*A^3,0] && PosQ[a/b]",
        desc: "Algebraic expansion",
        refs: ["G&R 2.126.2, CRC 75"],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [capital_a__, capital_b__, a__, b__, x_],
        optional: [capital_b__, b__],
        when: {
            freeq!([capital_a__, capital_b__, a__, b__], x_)
                && neq!(&a__ * capital_b__.pow(3) - &b__ * capital_a__.pow(3), 0)
                && posq!(&a__ / &b__)
        },
        rhs: {
            let rt = rubi_rt(&(&a__ / &b__), 3);
            let r = rubi_numerator(&rt);
            let s = rubi_denominator_atom(&rt);
            let first_integrand = Atom::num(1) / (&r + &s * x_);
            let first = rubi_rhs_int(&first_integrand, x_);
            let second_numerator =
                &r * (&capital_b__ * &r + Atom::num(2) * &capital_a__ * &s) + &s * (&capital_b__ * &r - &capital_a__ * &s) * x_;
            let second_denominator = r.pow(2) - &r * &s * x_ + s.pow(2) * x_.pow(2);
            let second = rubi_rhs_int(&(second_numerator / second_denominator), x_);

            rubi_star(-&r * (&capital_b__ * &r - &capital_a__ * &s) / (Atom::num(3) * &a__ * &s), first)
                    + rubi_star(r, second / (Atom::num(3) * a__ * s))
        },
    ));
}

fn push_rules_rule_2400(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_a__, capital_b__, a__, b__, x_);
    rules.push(rubi_rule!(
        order: 2400,
        source: "Int[(A_+B_.*x_)/(a_+b_.*x_^3),x_Symbol] :=
          With[{r=Numerator[Rt[-a/b,3]], s=Denominator[Rt[-a/b,3]]},
          r*(B*r+A*s)/(3*a*s) \\[Star] Int[1/(r-s*x),x] -
          r/(3*a*s) \\[Star] Int[(r*(B*r-2*A*s)-s*(B*r+A*s)*x)/(r^2+r*s*x+s^2*x^2),x]] /;
        FreeQ[{a,b,A,B},x] && NeQ[a*B^3-b*A^3,0] && NegQ[a/b]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [capital_a__, capital_b__, a__, b__, x_],
        optional: [capital_b__, b__],
        when: {
            freeq!([capital_a__, capital_b__, a__, b__], x_)
                && neq!(&a__ * capital_b__.pow(3) - &b__ * capital_a__.pow(3), 0)
                && negq!(&a__ / &b__)
        },
        rhs: {
            let rt = rubi_rt(&(-&a__ / &b__), 3);
            let r = rubi_numerator(&rt);
            let s = rubi_denominator_atom(&rt);
            let first_integrand = Atom::num(1) / (&r - &s * x_);
            let first = rubi_rhs_int(&first_integrand, x_);
            let second_numerator =
                &r * (&capital_b__ * &r - Atom::num(2) * &capital_a__ * &s) - &s * (&capital_b__ * &r + &capital_a__ * &s) * x_;
            let second_denominator = r.pow(2) + &r * &s * x_ + s.pow(2) * x_.pow(2);
            let second = rubi_rhs_int(&(second_numerator / second_denominator), x_);

            rubi_star(&r * (&capital_b__ * &r + &capital_a__ * &s) / (Atom::num(3) * &a__ * &s), first)
                    - rubi_star(r, second / (Atom::num(3) * a__ * s))
        },
    ));
}

fn push_rules_rule_2401(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, p2__, x_);
    rules.push(rubi_rule!(
        order: 2401,
        source: "Int[P2_/(a_+b_.*x_^3),x_Symbol] :=
          With[{A=Coeff[P2,x,0],B=Coeff[P2,x,1],C=Coeff[P2,x,2]},
            -C^2/b \\[Star] Int[1/(B-C*x),x] /;
          EqQ[B^2-A*C,0] && EqQ[b*B^3+a*C^3,0]] /;
        FreeQ[{a,b},x] && PolyQ[P2,x,2]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [p2__, a__, b__, x_],
        optional: [b__],
        when: {
            let capital_a = rubi_coeff(&p2__, x_, 0);
            let capital_b = rubi_coeff(&p2__, x_, 1);
            let capital_c = rubi_coeff(&p2__, x_, 2);
            freeq!([a__, b__], x_)
                && rubi_poly_q_degree(&p2__, x_, 2)
                && capital_a
                    .as_ref()
                    .zip(capital_b.as_ref())
                    .zip(capital_c.as_ref())
                    .is_some_and(|((capital_a, capital_b), capital_c)| {
                        eqq!(capital_b.pow(2) - capital_a * capital_c, 0)
                            && eqq!(&b__ * capital_b.pow(3) + &a__ * capital_c.pow(3), 0)
                    })
        },
        rhs: {
            let capital_b = rubi_coeff(&p2__, x_, 1).unwrap();
            let capital_c = rubi_coeff(&p2__, x_, 2).unwrap();
            let recursive_integrand = Atom::num(1) / (&capital_b - &capital_c * x_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(-capital_c.pow(2), recursive / b__)
        },
    ));
}

fn push_rules_rule_2402(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, p2__, x_);
    rules.push(rubi_rule!(
        order: 2402,
        source: "Int[P2_/(a_+b_.*x_^3),x_Symbol] :=
          With[{A=Coeff[P2,x,0],B=Coeff[P2,x,1],C=Coeff[P2,x,2]},
            With[{q=a^(1/3)/b^(1/3)}, C/b \\[Star] Int[1/(q+x),x] + (B+C*q)/b \\[Star] Int[1/(q^2-q*x+x^2),x]] /;
          EqQ[A*b^(2/3)-a^(1/3)*b^(1/3)*B-2*a^(2/3)*C,0]] /;
        FreeQ[{a,b},x] && PolyQ[P2,x,2]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [p2__, a__, b__, x_],
        optional: [b__],
        when: {
            let capital_a = rubi_coeff(&p2__, x_, 0);
            let capital_b = rubi_coeff(&p2__, x_, 1);
            let capital_c = rubi_coeff(&p2__, x_, 2);
            freeq!([a__, b__], x_)
                && rubi_poly_q_degree(&p2__, x_, 2)
                && capital_a
                    .as_ref()
                    .zip(capital_b.as_ref())
                    .zip(capital_c.as_ref())
                    .is_some_and(|((capital_a, capital_b), capital_c)| {
                        eqq!(
                            capital_a * b__.pow(Atom::num(2) / Atom::num(3))
                                - a__.pow(Atom::num(1) / Atom::num(3)) * b__.pow(Atom::num(1) / Atom::num(3)) * capital_b
                                - Atom::num(2) * a__.pow(Atom::num(2) / Atom::num(3)) * capital_c,
                            0
                        )
                    })
        },
        rhs: {
            let capital_b = rubi_coeff(&p2__, x_, 1).unwrap();
            let capital_c = rubi_coeff(&p2__, x_, 2).unwrap();
            let q = a__.pow(Atom::num(1) / Atom::num(3)) / b__.pow(Atom::num(1) / Atom::num(3));
            let first_integrand = Atom::num(1) / (&q + x_);
            let first = rubi_rhs_int(&first_integrand, x_);
            let second_integrand = Atom::num(1) / (q.pow(2) - &q * x_ + x_.pow(2));
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(&capital_c / &b__, first)
                    + rubi_star((&capital_b + &capital_c * q) / b__, second)
        },
    ));
}

fn push_rules_rule_2403(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, p2__, x_);
    rules.push(rubi_rule!(
        order: 2403,
        source: "Int[P2_/(a_+b_.*x_^3),x_Symbol] :=
          With[{A=Coeff[P2,x,0],B=Coeff[P2,x,1],C=Coeff[P2,x,2]},
            With[{q=(-a)^(1/3)/(-b)^(1/3)}, C/b \\[Star] Int[1/(q+x),x] + (B+C*q)/b \\[Star] Int[1/(q^2-q*x+x^2),x]] /;
          EqQ[A*(-b)^(2/3)-(-a)^(1/3)*(-b)^(1/3)*B-2*(-a)^(2/3)*C,0]] /;
        FreeQ[{a,b},x] && PolyQ[P2,x,2]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [p2__, a__, b__, x_],
        optional: [b__],
        when: {
            let capital_a = rubi_coeff(&p2__, x_, 0);
            let capital_b = rubi_coeff(&p2__, x_, 1);
            let capital_c = rubi_coeff(&p2__, x_, 2);
            freeq!([a__, b__], x_)
                && rubi_poly_q_degree(&p2__, x_, 2)
                && capital_a
                    .as_ref()
                    .zip(capital_b.as_ref())
                    .zip(capital_c.as_ref())
                    .is_some_and(|((capital_a, capital_b), capital_c)| {
                        eqq!(
                            capital_a * (-&b__).pow(Atom::num(2) / Atom::num(3))
                                - (-&a__).pow(Atom::num(1) / Atom::num(3)) * (-&b__).pow(Atom::num(1) / Atom::num(3)) * capital_b
                                - Atom::num(2) * (-&a__).pow(Atom::num(2) / Atom::num(3)) * capital_c,
                            0
                        )
                    })
        },
        rhs: {
            let capital_b = rubi_coeff(&p2__, x_, 1).unwrap();
            let capital_c = rubi_coeff(&p2__, x_, 2).unwrap();
            let q = (-&a__).pow(Atom::num(1) / Atom::num(3)) / (-&b__).pow(Atom::num(1) / Atom::num(3));
            let first_integrand = Atom::num(1) / (&q + x_);
            let first = rubi_rhs_int(&first_integrand, x_);
            let second_integrand = Atom::num(1) / (q.pow(2) - &q * x_ + x_.pow(2));
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(&capital_c / &b__, first)
                    + rubi_star((&capital_b + &capital_c * q) / b__, second)
        },
    ));
}

fn push_rules_rule_2404(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, p2__, x_);
    rules.push(rubi_rule!(
        order: 2404,
        source: "Int[P2_/(a_+b_.*x_^3),x_Symbol] :=
          With[{A=Coeff[P2,x,0],B=Coeff[P2,x,1],C=Coeff[P2,x,2]},
            With[{q=(-a)^(1/3)/b^(1/3)}, -C/b \\[Star] Int[1/(q-x),x] + (B-C*q)/b \\[Star] Int[1/(q^2+q*x+x^2),x]] /;
          EqQ[A*b^(2/3)+(-a)^(1/3)*b^(1/3)*B-2*(-a)^(2/3)*C,0]] /;
        FreeQ[{a,b},x] && PolyQ[P2,x,2]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [p2__, a__, b__, x_],
        optional: [b__],
        when: {
            let capital_a = rubi_coeff(&p2__, x_, 0);
            let capital_b = rubi_coeff(&p2__, x_, 1);
            let capital_c = rubi_coeff(&p2__, x_, 2);
            freeq!([a__, b__], x_)
                && rubi_poly_q_degree(&p2__, x_, 2)
                && capital_a
                    .as_ref()
                    .zip(capital_b.as_ref())
                    .zip(capital_c.as_ref())
                    .is_some_and(|((capital_a, capital_b), capital_c)| {
                        eqq!(
                            capital_a * b__.pow(Atom::num(2) / Atom::num(3))
                                + (-&a__).pow(Atom::num(1) / Atom::num(3)) * b__.pow(Atom::num(1) / Atom::num(3)) * capital_b
                                - Atom::num(2) * (-&a__).pow(Atom::num(2) / Atom::num(3)) * capital_c,
                            0
                        )
                    })
        },
        rhs: {
            let capital_b = rubi_coeff(&p2__, x_, 1).unwrap();
            let capital_c = rubi_coeff(&p2__, x_, 2).unwrap();
            let q = (-&a__).pow(Atom::num(1) / Atom::num(3)) / b__.pow(Atom::num(1) / Atom::num(3));
            let first_integrand = Atom::num(1) / (&q - x_);
            let first = rubi_rhs_int(&first_integrand, x_);
            let second_integrand = Atom::num(1) / (q.pow(2) + &q * x_ + x_.pow(2));
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(-&capital_c / &b__, first)
                    + rubi_star((&capital_b - &capital_c * q) / b__, second)
        },
    ));
}

fn push_rules_rule_2405(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, p2__, x_);
    rules.push(rubi_rule!(
        order: 2405,
        source: "Int[P2_/(a_+b_.*x_^3),x_Symbol] :=
          With[{A=Coeff[P2,x,0],B=Coeff[P2,x,1],C=Coeff[P2,x,2]},
            With[{q=a^(1/3)/(-b)^(1/3)}, -C/b \\[Star] Int[1/(q-x),x] + (B-C*q)/b \\[Star] Int[1/(q^2+q*x+x^2),x]] /;
          EqQ[A*(-b)^(2/3)+a^(1/3)*(-b)^(1/3)*B-2*a^(2/3)*C,0]] /;
        FreeQ[{a,b},x] && PolyQ[P2,x,2]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [p2__, a__, b__, x_],
        optional: [b__],
        when: {
            let capital_a = rubi_coeff(&p2__, x_, 0);
            let capital_b = rubi_coeff(&p2__, x_, 1);
            let capital_c = rubi_coeff(&p2__, x_, 2);
            freeq!([a__, b__], x_)
                && rubi_poly_q_degree(&p2__, x_, 2)
                && capital_a
                    .as_ref()
                    .zip(capital_b.as_ref())
                    .zip(capital_c.as_ref())
                    .is_some_and(|((capital_a, capital_b), capital_c)| {
                        eqq!(
                            capital_a * (-&b__).pow(Atom::num(2) / Atom::num(3))
                                + a__.pow(Atom::num(1) / Atom::num(3)) * (-&b__).pow(Atom::num(1) / Atom::num(3)) * capital_b
                                - Atom::num(2) * a__.pow(Atom::num(2) / Atom::num(3)) * capital_c,
                            0
                        )
                    })
        },
        rhs: {
            let capital_b = rubi_coeff(&p2__, x_, 1).unwrap();
            let capital_c = rubi_coeff(&p2__, x_, 2).unwrap();
            let q = a__.pow(Atom::num(1) / Atom::num(3)) / (-&b__).pow(Atom::num(1) / Atom::num(3));
            let first_integrand = Atom::num(1) / (&q - x_);
            let first = rubi_rhs_int(&first_integrand, x_);
            let second_integrand = Atom::num(1) / (q.pow(2) + &q * x_ + x_.pow(2));
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(-&capital_c / &b__, first)
                    + rubi_star((&capital_b - &capital_c * q) / b__, second)
        },
    ));
}

fn push_rules_rule_2406(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, p2__, x_);
    rules.push(rubi_rule!(
        order: 2406,
        source: "Int[P2_/(a_+b_.*x_^3),x_Symbol] :=
          With[{A=Coeff[P2,x,0],B=Coeff[P2,x,1],C=Coeff[P2,x,2]},
            With[{q=(a/b)^(1/3)}, C/b \\[Star] Int[1/(q+x),x] + (B+C*q)/b \\[Star] Int[1/(q^2-q*x+x^2),x]] /;
          EqQ[A-(a/b)^(1/3)*B-2*(a/b)^(2/3)*C,0]] /;
        FreeQ[{a,b},x] && PolyQ[P2,x,2]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [p2__, a__, b__, x_],
        optional: [b__],
        when: {
            let capital_a = rubi_coeff(&p2__, x_, 0);
            let capital_b = rubi_coeff(&p2__, x_, 1);
            let capital_c = rubi_coeff(&p2__, x_, 2);
            let q = (&a__ / &b__).pow(Atom::num(1) / Atom::num(3));
            freeq!([a__, b__], x_)
                && rubi_poly_q_degree(&p2__, x_, 2)
                && capital_a
                    .as_ref()
                    .zip(capital_b.as_ref())
                    .zip(capital_c.as_ref())
                    .is_some_and(|((capital_a, capital_b), capital_c)| {
                        eqq!(capital_a - &q * capital_b - Atom::num(2) * q.pow(2) * capital_c, 0)
                    })
        },
        rhs: {
            let capital_b = rubi_coeff(&p2__, x_, 1).unwrap();
            let capital_c = rubi_coeff(&p2__, x_, 2).unwrap();
            let q = (&a__ / &b__).pow(Atom::num(1) / Atom::num(3));
            let first_integrand = Atom::num(1) / (&q + x_);
            let first = rubi_rhs_int(&first_integrand, x_);
            let second_integrand = Atom::num(1) / (q.pow(2) - &q * x_ + x_.pow(2));
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(&capital_c / &b__, first)
                    + rubi_star((&capital_b + &capital_c * q) / b__, second)
        },
    ));
}

fn push_rules_rule_2407(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, p2__, x_);
    rules.push(rubi_rule!(
        order: 2407,
        source: "Int[P2_/(a_+b_.*x_^3),x_Symbol] :=
          With[{A=Coeff[P2,x,0],B=Coeff[P2,x,1],C=Coeff[P2,x,2]},
            With[{q=Rt[a/b,3]}, C/b \\[Star] Int[1/(q+x),x] + (B+C*q)/b \\[Star] Int[1/(q^2-q*x+x^2),x]] /;
          EqQ[A-Rt[a/b,3]*B-2*Rt[a/b,3]^2*C,0]] /;
        FreeQ[{a,b},x] && PolyQ[P2,x,2]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [p2__, a__, b__, x_],
        optional: [b__],
        when: {
            let capital_a = rubi_coeff(&p2__, x_, 0);
            let capital_b = rubi_coeff(&p2__, x_, 1);
            let capital_c = rubi_coeff(&p2__, x_, 2);
            let q = rubi_rt(&(&a__ / &b__), 3);
            freeq!([a__, b__], x_)
                && rubi_poly_q_degree(&p2__, x_, 2)
                && capital_a
                    .as_ref()
                    .zip(capital_b.as_ref())
                    .zip(capital_c.as_ref())
                    .is_some_and(|((capital_a, capital_b), capital_c)| {
                        eqq!(capital_a - &q * capital_b - Atom::num(2) * q.pow(2) * capital_c, 0)
                    })
        },
        rhs: {
            let capital_b = rubi_coeff(&p2__, x_, 1).unwrap();
            let capital_c = rubi_coeff(&p2__, x_, 2).unwrap();
            let q = rubi_rt(&(&a__ / &b__), 3);
            let first_integrand = Atom::num(1) / (&q + x_);
            let first = rubi_rhs_int(&first_integrand, x_);
            let second_integrand = Atom::num(1) / (q.pow(2) - &q * x_ + x_.pow(2));
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(&capital_c / &b__, first)
                    + rubi_star((&capital_b + &capital_c * q) / b__, second)
        },
    ));
}

fn push_rules_rule_2408(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, p2__, x_);
    rules.push(rubi_rule!(
        order: 2408,
        source: "Int[P2_/(a_+b_.*x_^3),x_Symbol] :=
          With[{A=Coeff[P2,x,0],B=Coeff[P2,x,1],C=Coeff[P2,x,2]},
            With[{q=(-a/b)^(1/3)}, -C/b \\[Star] Int[1/(q-x),x] + (B-C*q)/b \\[Star] Int[1/(q^2+q*x+x^2),x]] /;
          EqQ[A+(-a/b)^(1/3)*B-2*(-a/b)^(2/3)*C,0]] /;
        FreeQ[{a,b},x] && PolyQ[P2,x,2]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [p2__, a__, b__, x_],
        optional: [b__],
        when: {
            let capital_a = rubi_coeff(&p2__, x_, 0);
            let capital_b = rubi_coeff(&p2__, x_, 1);
            let capital_c = rubi_coeff(&p2__, x_, 2);
            let q = (-&a__ / &b__).pow(Atom::num(1) / Atom::num(3));
            freeq!([a__, b__], x_)
                && rubi_poly_q_degree(&p2__, x_, 2)
                && capital_a
                    .as_ref()
                    .zip(capital_b.as_ref())
                    .zip(capital_c.as_ref())
                    .is_some_and(|((capital_a, capital_b), capital_c)| {
                        eqq!(capital_a + &q * capital_b - Atom::num(2) * q.pow(2) * capital_c, 0)
                    })
        },
        rhs: {
            let capital_b = rubi_coeff(&p2__, x_, 1).unwrap();
            let capital_c = rubi_coeff(&p2__, x_, 2).unwrap();
            let q = (-&a__ / &b__).pow(Atom::num(1) / Atom::num(3));
            let first_integrand = Atom::num(1) / (&q - x_);
            let first = rubi_rhs_int(&first_integrand, x_);
            let second_integrand = Atom::num(1) / (q.pow(2) + &q * x_ + x_.pow(2));
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(-&capital_c / &b__, first)
                    + rubi_star((&capital_b - &capital_c * q) / b__, second)
        },
    ));
}

fn push_rules_rule_2409(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, p2__, x_);
    rules.push(rubi_rule!(
        order: 2409,
        source: "Int[P2_/(a_+b_.*x_^3),x_Symbol] :=
          With[{A=Coeff[P2,x,0],B=Coeff[P2,x,1],C=Coeff[P2,x,2]},
            With[{q=Rt[-a/b,3]}, -C/b \\[Star] Int[1/(q-x),x] + (B-C*q)/b \\[Star] Int[1/(q^2+q*x+x^2),x]] /;
          EqQ[A+Rt[-a/b,3]*B-2*Rt[-a/b,3]^2*C,0]] /;
        FreeQ[{a,b},x] && PolyQ[P2,x,2]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [p2__, a__, b__, x_],
        optional: [b__],
        when: {
            let capital_a = rubi_coeff(&p2__, x_, 0);
            let capital_b = rubi_coeff(&p2__, x_, 1);
            let capital_c = rubi_coeff(&p2__, x_, 2);
            let q = rubi_rt(&(-&a__ / &b__), 3);
            freeq!([a__, b__], x_)
                && rubi_poly_q_degree(&p2__, x_, 2)
                && capital_a
                    .as_ref()
                    .zip(capital_b.as_ref())
                    .zip(capital_c.as_ref())
                    .is_some_and(|((capital_a, capital_b), capital_c)| {
                        eqq!(capital_a + &q * capital_b - Atom::num(2) * q.pow(2) * capital_c, 0)
                    })
        },
        rhs: {
            let capital_b = rubi_coeff(&p2__, x_, 1).unwrap();
            let capital_c = rubi_coeff(&p2__, x_, 2).unwrap();
            let q = rubi_rt(&(-&a__ / &b__), 3);
            let first_integrand = Atom::num(1) / (&q - x_);
            let first = rubi_rhs_int(&first_integrand, x_);
            let second_integrand = Atom::num(1) / (q.pow(2) + &q * x_ + x_.pow(2));
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(-&capital_c / &b__, first)
                    + rubi_star((&capital_b - &capital_c * q) / b__, second)
        },
    ));
}

fn push_rules_rule_2410(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, p2__, x_);
    rules.push(rubi_rule!(
        order: 2410,
        source: "Int[P2_/(a_+b_.*x_^3),x_Symbol] :=
          With[{A=Coeff[P2,x,0],B=Coeff[P2,x,1],C=Coeff[P2,x,2]},
            Int[(A+B*x)/(a+b*x^3),x] + C \\[Star] Int[x^2/(a+b*x^3),x] /;
          EqQ[a*B^3-b*A^3,0] || Not[RationalQ[a/b]]] /;
        FreeQ[{a,b},x] && PolyQ[P2,x,2]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [p2__, a__, b__, x_],
        optional: [b__],
        when: {
            let capital_a = rubi_coeff(&p2__, x_, 0);
            let capital_b = rubi_coeff(&p2__, x_, 1);
            freeq!([a__, b__], x_)
                && rubi_poly_q_degree(&p2__, x_, 2)
                && capital_a.as_ref().zip(capital_b.as_ref()).is_some_and(|(capital_a, capital_b)| {
                    eqq!(&a__ * capital_b.pow(3) - &b__ * capital_a.pow(3), 0) || !rationalq!(&a__ / &b__)
                })
        },
        rhs: {
            let capital_a = rubi_coeff(&p2__, x_, 0).unwrap();
            let capital_b = rubi_coeff(&p2__, x_, 1).unwrap();
            let capital_c = rubi_coeff(&p2__, x_, 2).unwrap();
            let denominator = &a__ + &b__ * x_.pow(3);
            let first_integrand = (&capital_a + &capital_b * x_) / &denominator;
            let second_integrand = x_.pow(2) / denominator;
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            first + rubi_star(capital_c, second)
        },
    ));
}

fn push_rules_rule_2411(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, p2__, x_);
    rules.push(rubi_rule!(
        order: 2411,
        source: "Int[P2_/(a_+b_.*x_^3),x_Symbol] :=
          With[{A=Coeff[P2,x,0],B=Coeff[P2,x,1],C=Coeff[P2,x,2]},
            With[{q=(a/b)^(1/3)}, q^2/a \\[Star] Int[(A+C*q*x)/(q^2-q*x+x^2),x]] /;
          EqQ[A-B*(a/b)^(1/3)+C*(a/b)^(2/3),0]] /;
        FreeQ[{a,b},x] && PolyQ[P2,x,2]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [p2__, a__, b__, x_],
        optional: [b__],
        when: {
            let capital_a = rubi_coeff(&p2__, x_, 0);
            let capital_b = rubi_coeff(&p2__, x_, 1);
            let capital_c = rubi_coeff(&p2__, x_, 2);
            let q = (&a__ / &b__).pow(Atom::num(1) / Atom::num(3));
            freeq!([a__, b__], x_)
                && rubi_poly_q_degree(&p2__, x_, 2)
                && capital_a
                    .as_ref()
                    .zip(capital_b.as_ref())
                    .zip(capital_c.as_ref())
                    .is_some_and(|((capital_a, capital_b), capital_c)| {
                        eqq!(capital_a - capital_b * &q + capital_c * q.pow(2), 0)
                    })
        },
        rhs: {
            let capital_a = rubi_coeff(&p2__, x_, 0).unwrap();
            let capital_c = rubi_coeff(&p2__, x_, 2).unwrap();
            let q = (&a__ / &b__).pow(Atom::num(1) / Atom::num(3));
            let numerator = &capital_a + &capital_c * &q * x_;
            let recursive_integrand = numerator / (q.pow(2) - &q * x_ + x_.pow(2));
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(q.pow(2) / a__, recursive)
        },
    ));
}

fn push_rules_rule_2412(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, p2__, x_);
    rules.push(rubi_rule!(
        order: 2412,
        source: "Int[P2_/(a_+b_.*x_^3),x_Symbol] :=
          With[{A=Coeff[P2,x,0],B=Coeff[P2,x,1],C=Coeff[P2,x,2]},
            With[{q=(-a/b)^(1/3)}, q/a \\[Star] Int[(A*q+(A+B*q)*x)/(q^2+q*x+x^2),x]] /;
          EqQ[A+B*(-a/b)^(1/3)+C*(-a/b)^(2/3),0]] /;
        FreeQ[{a,b},x] && PolyQ[P2,x,2]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [p2__, a__, b__, x_],
        optional: [b__],
        when: {
            let capital_a = rubi_coeff(&p2__, x_, 0);
            let capital_b = rubi_coeff(&p2__, x_, 1);
            let capital_c = rubi_coeff(&p2__, x_, 2);
            let q = (-&a__ / &b__).pow(Atom::num(1) / Atom::num(3));
            freeq!([a__, b__], x_)
                && rubi_poly_q_degree(&p2__, x_, 2)
                && capital_a
                    .as_ref()
                    .zip(capital_b.as_ref())
                    .zip(capital_c.as_ref())
                    .is_some_and(|((capital_a, capital_b), capital_c)| {
                        eqq!(capital_a + capital_b * &q + capital_c * q.pow(2), 0)
                    })
        },
        rhs: {
            let capital_a = rubi_coeff(&p2__, x_, 0).unwrap();
            let capital_b = rubi_coeff(&p2__, x_, 1).unwrap();
            let q = (-&a__ / &b__).pow(Atom::num(1) / Atom::num(3));
            let numerator = &capital_a * &q + (&capital_a + &capital_b * &q) * x_;
            let recursive_integrand = numerator / (q.pow(2) + &q * x_ + x_.pow(2));
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(q / a__, recursive)
        },
    ));
}

fn push_rules_rule_2413(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, p2__, x_);
    rules.push(rubi_rule!(
        order: 2413,
        source: "Int[P2_/(a_+b_.*x_^3),x_Symbol] :=
          With[{A=Coeff[P2,x,0],B=Coeff[P2,x,1],C=Coeff[P2,x,2],q=(a/b)^(1/3)},
            q*(A-B*q+C*q^2)/(3*a) \\[Star] Int[1/(q+x),x] +
            q/(3*a) \\[Star] Int[(q*(2*A+B*q-C*q^2)-(A-B*q-2*C*q^2)*x)/(q^2-q*x+x^2),x] /;
          NeQ[a*B^3-b*A^3,0] && NeQ[A-B*q+C*q^2,0]] /;
        FreeQ[{a,b},x] && PolyQ[P2,x,2] && GtQ[a/b,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [p2__, a__, b__, x_],
        optional: [b__],
        when: {
            let capital_a = rubi_coeff(&p2__, x_, 0);
            let capital_b = rubi_coeff(&p2__, x_, 1);
            let capital_c = rubi_coeff(&p2__, x_, 2);
            let q = (&a__ / &b__).pow(Atom::num(1) / Atom::num(3));
            freeq!([a__, b__], x_)
                && rubi_poly_q_degree(&p2__, x_, 2)
                && gtq!(&a__ / &b__, 0)
                && capital_a
                    .as_ref()
                    .zip(capital_b.as_ref())
                    .zip(capital_c.as_ref())
                    .is_some_and(|((capital_a, capital_b), capital_c)| {
                        neq!(&a__ * capital_b.pow(3) - &b__ * capital_a.pow(3), 0)
                            && neq!(capital_a - capital_b * &q + capital_c * q.pow(2), 0)
                    })
        },
        rhs: {
            let capital_a = rubi_coeff(&p2__, x_, 0).unwrap();
            let capital_b = rubi_coeff(&p2__, x_, 1).unwrap();
            let capital_c = rubi_coeff(&p2__, x_, 2).unwrap();
            let q = (&a__ / &b__).pow(Atom::num(1) / Atom::num(3));
            let first_integrand = Atom::num(1) / (&q + x_);
            let first = rubi_rhs_int(&first_integrand, x_);
            let second_numerator = &q * (Atom::num(2) * &capital_a + &capital_b * &q - &capital_c * q.pow(2))
                - (&capital_a - &capital_b * &q - Atom::num(2) * &capital_c * q.pow(2)) * x_;
            let second_integrand = second_numerator / (q.pow(2) - &q * x_ + x_.pow(2));
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(&q * (&capital_a - &capital_b * &q + &capital_c * q.pow(2)) / (Atom::num(3) * &a__), first) + rubi_star(q, second / (Atom::num(3) * a__))
        },
    ));
}

fn push_rules_rule_2414(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, p2__, x_);
    rules.push(rubi_rule!(
        order: 2414,
        source: "Int[P2_/(a_+b_.*x_^3),x_Symbol] :=
          With[{A=Coeff[P2,x,0],B=Coeff[P2,x,1],C=Coeff[P2,x,2],q=(-a/b)^(1/3)},
            q*(A+B*q+C*q^2)/(3*a) \\[Star] Int[1/(q-x),x] +
            q/(3*a) \\[Star] Int[(q*(2*A-B*q-C*q^2)+(A+B*q-2*C*q^2)*x)/(q^2+q*x+x^2),x] /;
          NeQ[a*B^3-b*A^3,0] && NeQ[A+B*q+C*q^2,0]] /;
        FreeQ[{a,b},x] && PolyQ[P2,x,2] && LtQ[a/b,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [p2__, a__, b__, x_],
        optional: [b__],
        when: {
            let capital_a = rubi_coeff(&p2__, x_, 0);
            let capital_b = rubi_coeff(&p2__, x_, 1);
            let capital_c = rubi_coeff(&p2__, x_, 2);
            let q = (-&a__ / &b__).pow(Atom::num(1) / Atom::num(3));
            freeq!([a__, b__], x_)
                && rubi_poly_q_degree(&p2__, x_, 2)
                && ltq!(&a__ / &b__, 0)
                && capital_a
                    .as_ref()
                    .zip(capital_b.as_ref())
                    .zip(capital_c.as_ref())
                    .is_some_and(|((capital_a, capital_b), capital_c)| {
                        neq!(&a__ * capital_b.pow(3) - &b__ * capital_a.pow(3), 0)
                            && neq!(capital_a + capital_b * &q + capital_c * q.pow(2), 0)
                    })
        },
        rhs: {
            let capital_a = rubi_coeff(&p2__, x_, 0).unwrap();
            let capital_b = rubi_coeff(&p2__, x_, 1).unwrap();
            let capital_c = rubi_coeff(&p2__, x_, 2).unwrap();
            let q = (-&a__ / &b__).pow(Atom::num(1) / Atom::num(3));
            let first_integrand = Atom::num(1) / (&q - x_);
            let first = rubi_rhs_int(&first_integrand, x_);
            let second_numerator = &q * (Atom::num(2) * &capital_a - &capital_b * &q - &capital_c * q.pow(2))
                + (&capital_a + &capital_b * &q - Atom::num(2) * &capital_c * q.pow(2)) * x_;
            let second_integrand = second_numerator / (q.pow(2) + &q * x_ + x_.pow(2));
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(&q * (&capital_a + &capital_b * &q + &capital_c * q.pow(2)) / (Atom::num(3) * &a__), first) + rubi_star(q, second / (Atom::num(3) * a__))
        },
    ));
}

fn push_rules_rule_2415(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, n_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2415,
        source: "Int[Pq_/(a_+b_.*x_^n_),x_Symbol] :=
          With[{v=Sum[x^ii*(Coeff[Pq,x,ii]+Coeff[Pq,x,n/2+ii]*x^(n/2))/(a+b*x^n),{ii,0,n/2-1}]},
          Int[v,x] /;
         SumQ[v]] /;
        FreeQ[{a,b},x] && PolyQ[Pq,x] && IGtQ[n/2,0] && Expon[Pq,x]<n",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [pq__, a__, b__, n_, x_],
        optional: [b__],
        when: {
            match rubi_expon(&pq__, x_) {
                Some(q) => {
                    freeq!([a__, b__], x_)
                        && rubi_poly_q(&pq__, x_)
                        && igtq!(&n_ / Atom::num(2), 0)
                        && ltq!(Atom::num(q), n_)
                        && rubi_even_binomial_split_sum(&pq__, &a__, &b__, &n_, x_)
                            .is_some_and(|v_sum| rubi_sum_q(&v_sum))
                }
                None => false,
            }
        },
        rhs: {
            let v_sum = rubi_even_binomial_split_sum(&pq__, &a__, &b__, &n_, x_).unwrap();
            rubi_rhs_int(&v_sum, x_)
        },
    ));
}

fn push_rules_rule_2416(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 2416,
        source: "Int[(c_+d_.*x_)/Sqrt[a_+b_.*x_^3],x_Symbol] :=
          With[{r=Numer[Simplify[(1-Sqrt[3])*d/c]], s=Denom[Simplify[(1-Sqrt[3])*d/c]]},
          2*d*s^3*Sqrt[a+b*x^3]/(a*r^2*((1+Sqrt[3])*s+r*x)) -
          3^(1/4)*Sqrt[2-Sqrt[3]]*d*s*(s+r*x)*Sqrt[(s^2-r*s*x+r^2*x^2)/((1+Sqrt[3])*s+r*x)^2]/
            (r^2*Sqrt[a+b*x^3]*Sqrt[s*(s+r*x)/((1+Sqrt[3])*s+r*x)^2])*
            EllipticE[ArcSin[((1-Sqrt[3])*s+r*x)/((1+Sqrt[3])*s+r*x)],-7-4*Sqrt[3]]] /;
        FreeQ[{a,b,c,d},x] && PosQ[a] && EqQ[b*c^3-2*(5-3*Sqrt[3])*a*d^3,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: ["G&R 3.139"],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            let sqrt_three = Atom::num(3).sqrt();
            freeq!([a__, b__, c__, d__], x_)
                && posq!(a__)
                && eqq!(
                    &b__ * c__.pow(3) - Atom::num(2) * (Atom::num(5) - Atom::num(3) * &sqrt_three) * &a__ * d__.pow(3),
                    0
                )
        },
        rhs: {
            let sqrt_three = Atom::num(3).sqrt();
            let r = (Atom::num(1) - &sqrt_three) * &d__ / &c__;
            let s = Atom::num(1);
            if r.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }
            let base = &a__ + &b__ * x_.pow(3);
            let denominator_linear = (Atom::num(1) + &sqrt_three) * &s + &r * x_;
            let radical_quadratic =
                (s.pow(2) - &r * &s * x_ + r.pow(2) * x_.pow(2)) / denominator_linear.pow(2);
            let radical_linear = &s * (&s + &r * x_) / denominator_linear.pow(2);
            let amplitude =
                (((Atom::num(1) - &sqrt_three) * &s + &r * x_) / &denominator_linear).asin();

            rubi_simp(&(Atom::num(2) * &d__ * s.pow(3) * base.sqrt() / (&a__ * r.pow(2) * &denominator_linear)), x_)
                    - rubi_simp(&(Atom::num(3).pow(Atom::num(1) / Atom::num(4))
                        * (Atom::num(2) - &sqrt_three).sqrt()
                        * &d__
                        * &s
                        * (&s + &r * x_)
                        * radical_quadratic.sqrt()
                        * rubi_elliptic_e(amplitude, -Atom::num(7) - Atom::num(4) * sqrt_three)
                        / (r.pow(2) * base.sqrt() * radical_linear.sqrt())), x_)
        },
    ));
}

fn push_rules_rule_2417(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 2417,
        source: "Int[(c_+d_.*x_)/Sqrt[a_+b_.*x_^3],x_Symbol] :=
          With[{r=Numer[Rt[b/a,3]], s=Denom[Rt[b/a,3]]},
          (c*r-(1-Sqrt[3])*d*s)/r \\[Star] Int[1/Sqrt[a+b*x^3],x] + d/r \\[Star] Int[((1-Sqrt[3])*s+r*x)/Sqrt[a+b*x^3],x]] /;
        FreeQ[{a,b,c,d},x] && PosQ[a] && NeQ[b*c^3-2*(5-3*Sqrt[3])*a*d^3,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, d__],
        when: {
            let sqrt_three = Atom::num(3).sqrt();
            freeq!([a__, b__, c__, d__], x_)
                && posq!(a__)
                && neq!(
                    &b__ * c__.pow(3) - Atom::num(2) * (Atom::num(5) - Atom::num(3) * &sqrt_three) * &a__ * d__.pow(3),
                    0
                )
        },
        rhs: {
            let sqrt_three = Atom::num(3).sqrt();
            let r = rubi_rt(&(&b__ / &a__), 3);
            let s = Atom::num(1);
            if r.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }
            let base = &a__ + &b__ * x_.pow(3);
            let first_integrand = Atom::num(1) / base.sqrt();
            let first = rubi_rhs_int(&first_integrand, x_);
            let second_integrand = ((Atom::num(1) - &sqrt_three) * &s + &r * x_) / base.sqrt();
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(&c__ * &r - (Atom::num(1) - sqrt_three) * &d__ * &s, first / &r) + rubi_star(d__, second / r)
        },
    ));
}

fn push_rules_rule_2418(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 2418,
        source: "Int[(c_+d_.*x_)/Sqrt[a_+b_.*x_^3],x_Symbol] :=
          With[{r=Numer[Simplify[(1+Sqrt[3])*d/c]], s=Denom[Simplify[(1+Sqrt[3])*d/c]]},
          2*d*s^3*Sqrt[a+b*x^3]/(a*r^2*((1-Sqrt[3])*s+r*x)) +
          3^(1/4)*Sqrt[2+Sqrt[3]]*d*s*(s+r*x)*Sqrt[(s^2-r*s*x+r^2*x^2)/((1-Sqrt[3])*s+r*x)^2]/
            (r^2*Sqrt[a+b*x^3]*Sqrt[-s*(s+r*x)/((1-Sqrt[3])*s+r*x)^2])*
            EllipticE[ArcSin[((1+Sqrt[3])*s+r*x)/((1-Sqrt[3])*s+r*x)],-7+4*Sqrt[3]]] /;
        FreeQ[{a,b,c,d},x] && NegQ[a] && EqQ[b*c^3-2*(5+3*Sqrt[3])*a*d^3,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: ["G&R 3.139"],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, d__],
        when: {
            let sqrt_three = Atom::num(3).sqrt();
            freeq!([a__, b__, c__, d__], x_)
                && negq!(a__)
                && eqq!(
                    &b__ * c__.pow(3) - Atom::num(2) * (Atom::num(5) + Atom::num(3) * &sqrt_three) * &a__ * d__.pow(3),
                    0
                )
        },
        rhs: {
            let sqrt_three = Atom::num(3).sqrt();
            let r = (Atom::num(1) + &sqrt_three) * &d__ / &c__;
            let s = Atom::num(1);
            if r.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }
            let base = &a__ + &b__ * x_.pow(3);
            let denominator_linear = (Atom::num(1) - &sqrt_three) * &s + &r * x_;
            let radical_quadratic =
                (s.pow(2) - &r * &s * x_ + r.pow(2) * x_.pow(2)) / denominator_linear.pow(2);
            let radical_linear = -&s * (&s + &r * x_) / denominator_linear.pow(2);
            let amplitude =
                (((Atom::num(1) + &sqrt_three) * &s + &r * x_) / &denominator_linear).asin();

            rubi_simp(&(Atom::num(2) * &d__ * s.pow(3) * base.sqrt() / (&a__ * r.pow(2) * &denominator_linear)), x_)
                    + rubi_simp(&(Atom::num(3).pow(Atom::num(1) / Atom::num(4))
                        * (Atom::num(2) + &sqrt_three).sqrt()
                        * &d__
                        * &s
                        * (&s + &r * x_)
                        * radical_quadratic.sqrt()
                        * rubi_elliptic_e(amplitude, -Atom::num(7) + Atom::num(4) * sqrt_three)
                        / (r.pow(2) * base.sqrt() * radical_linear.sqrt())), x_)
        },
    ));
}

fn push_rules_rule_2419(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 2419,
        source: "Int[(c_+d_.*x_)/Sqrt[a_+b_.*x_^3],x_Symbol] :=
          With[{r=Numer[Rt[b/a,3]], s=Denom[Rt[b/a,3]]},
          (c*r-(1+Sqrt[3])*d*s)/r \\[Star] Int[1/Sqrt[a+b*x^3],x] + d/r \\[Star] Int[((1+Sqrt[3])*s+r*x)/Sqrt[a+b*x^3],x]] /;
        FreeQ[{a,b,c,d},x] && NegQ[a] && NeQ[b*c^3-2*(5+3*Sqrt[3])*a*d^3,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, d__],
        when: {
            let sqrt_three = Atom::num(3).sqrt();
            freeq!([a__, b__, c__, d__], x_)
                && negq!(a__)
                && neq!(
                    &b__ * c__.pow(3) - Atom::num(2) * (Atom::num(5) + Atom::num(3) * &sqrt_three) * &a__ * d__.pow(3),
                    0
                )
        },
        rhs: {
            let sqrt_three = Atom::num(3).sqrt();
            let r = rubi_rt(&(&b__ / &a__), 3);
            let s = Atom::num(1);
            if r.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }
            let base = &a__ + &b__ * x_.pow(3);
            let first_integrand = Atom::num(1) / base.sqrt();
            let first = rubi_rhs_int(&first_integrand, x_);
            let second_integrand = ((Atom::num(1) + &sqrt_three) * &s + &r * x_) / base.sqrt();
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(&c__ * &r - (Atom::num(1) + sqrt_three) * &d__ * &s, first / &r) + rubi_star(d__, second / r)
        },
    ));
}

fn push_rules_rule_2420(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 2420,
        source: "Int[(c_+d_.*x_^4)/Sqrt[a_+b_.*x_^6],x_Symbol] :=
          With[{r=Numer[Rt[b/a,3]], s=Denom[Rt[b/a,3]]},
          (1+Sqrt[3])*d*s^3*x*Sqrt[a+b*x^6]/(2*a*r^2*(s+(1+Sqrt[3])*r*x^2)) -
          3^(1/4)*d*s*x*(s+r*x^2)*Sqrt[(s^2-r*s*x^2+r^2*x^4)/(s+(1+Sqrt[3])*r*x^2)^2]/
            (2*r^2*Sqrt[(r*x^2*(s+r*x^2))/(s+(1+Sqrt[3])*r*x^2)^2]*Sqrt[a+b*x^6])*
            EllipticE[ArcCos[(s+(1-Sqrt[3])*r*x^2)/(s+(1+Sqrt[3])*r*x^2)],(2+Sqrt[3])/4]] /;
        FreeQ[{a,b,c,d},x] && EqQ[2*Rt[b/a,3]^2*c-(1-Sqrt[3])*d,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, d__],
        when: {
            let sqrt_three = Atom::num(3).sqrt();
            let q = rubi_rt(&(&b__ / &a__), 3);
            freeq!([a__, b__, c__, d__], x_)
                && eqq!(Atom::num(2) * q.pow(2) * &c__ - (Atom::num(1) - sqrt_three) * &d__, 0)
        },
        rhs: {
            let sqrt_three = Atom::num(3).sqrt();
            let r = rubi_rt(&(&b__ / &a__), 3);
            let s = Atom::num(1);
            if r.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }
            let base = &a__ + &b__ * x_.pow(6);
            let denominator_linear = &s + (Atom::num(1) + &sqrt_three) * &r * x_.pow(2);
            let radical_quadratic =
                (s.pow(2) - &r * &s * x_.pow(2) + r.pow(2) * x_.pow(4)) / denominator_linear.pow(2);
            let radical_linear = &r * x_.pow(2) * (&s + &r * x_.pow(2)) / denominator_linear.pow(2);
            let amplitude = ((&s + (Atom::num(1) - &sqrt_three) * &r * x_.pow(2)) / &denominator_linear).acos();

            rubi_simp(&((Atom::num(1) + &sqrt_three) * &d__ * s.pow(3) * x_ * base.sqrt()
                    / (Atom::num(2) * &a__ * r.pow(2) * &denominator_linear)), x_)
                    - rubi_simp(&(Atom::num(3).pow(Atom::num(1) / Atom::num(4))
                        * &d__
                        * &s
                        * x_
                        * (&s + &r * x_.pow(2))
                        * radical_quadratic.sqrt()
                        * rubi_elliptic_e(amplitude, (Atom::num(2) + sqrt_three) / Atom::num(4))
                        / (Atom::num(2) * r.pow(2) * radical_linear.sqrt() * base.sqrt())), x_)
        },
    ));
}

fn push_rules_rule_2421(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 2421,
        source: "Int[(c_+d_.*x_^4)/Sqrt[a_+b_.*x_^6],x_Symbol] :=
          With[{q=Rt[b/a,3]},
          (2*c*q^2-(1-Sqrt[3])*d)/(2*q^2) \\[Star] Int[1/Sqrt[a+b*x^6],x] + d/(2*q^2) \\[Star] Int[(1-Sqrt[3]+2*q^2*x^4)/Sqrt[a+b*x^6],x]] /;
        FreeQ[{a,b,c,d},x] && NeQ[2*Rt[b/a,3]^2*c-(1-Sqrt[3])*d,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, d__],
        when: {
            let sqrt_three = Atom::num(3).sqrt();
            let q = rubi_rt(&(&b__ / &a__), 3);
            freeq!([a__, b__, c__, d__], x_)
                && neq!(Atom::num(2) * q.pow(2) * &c__ - (Atom::num(1) - sqrt_three) * &d__, 0)
        },
        rhs: {
            let sqrt_three = Atom::num(3).sqrt();
            let q = rubi_rt(&(&b__ / &a__), 3);
            if q.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }
            let base = &a__ + &b__ * x_.pow(6);
            let first_integrand = Atom::num(1) / base.sqrt();
            let first = rubi_rhs_int(&first_integrand, x_);
            let second_integrand = (Atom::num(1) - &sqrt_three + Atom::num(2) * q.pow(2) * x_.pow(4)) / base.sqrt();
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(Atom::num(2) * &c__ * q.pow(2) - (Atom::num(1) - sqrt_three) * &d__, first / (Atom::num(2) * q.pow(2)))
                    + rubi_star(d__, second / (Atom::num(2) * q.pow(2)))
        },
    ));
}

fn push_rules_rule_2422(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 2422,
        source: "Int[(c_+d_.*x_^2)/Sqrt[a_+b_.*x_^8],x_Symbol] :=
          -c*d*x^3*Sqrt[-(c-d*x^2)^2/(c*d*x^2)]*Sqrt[-d^2*(a+b*x^8)/(b*c^2*x^4)]/(Sqrt[2+Sqrt[2]]*(c-d*x^2)*Sqrt[a+b*x^8])*
            EllipticF[ArcSin[1/2*Sqrt[(Sqrt[2]*c^2+2*c*d*x^2+Sqrt[2]*d^2*x^4)/(c*d*x^2)]],-2*(1-Sqrt[2])] /;
        FreeQ[{a,b,c,d},x] && EqQ[b*c^4-a*d^4,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && eqq!(&b__ * c__.pow(4) - &a__ * d__.pow(4), 0)
        },
        rhs: {
            let sqrt_two = Atom::num(2).sqrt();
            let base = &a__ + &b__ * x_.pow(8);
            let first_radical = (-(&c__ - &d__ * x_.pow(2)).pow(2) / (&c__ * &d__ * x_.pow(2))).sqrt();
            let second_radical = (-d__.pow(2) * &base / (&b__ * c__.pow(2) * x_.pow(4))).sqrt();
            let amplitude = (Atom::num(1)
                / Atom::num(2)
                * ((&sqrt_two * c__.pow(2) + Atom::num(2) * &c__ * &d__ * x_.pow(2) + &sqrt_two * d__.pow(2) * x_.pow(4))
                    / (&c__ * &d__ * x_.pow(2)))
                    .sqrt())
            .asin();

            rubi_simp(&(-&c__ * &d__ * x_.pow(3) * first_radical * second_radical
                    * rubi_elliptic_f(amplitude, -Atom::num(2) * (Atom::num(1) - &sqrt_two))
                    / ((Atom::num(2) + &sqrt_two).sqrt() * (&c__ - &d__ * x_.pow(2)) * base.sqrt())), x_)
        },
    ));
}

fn push_rules_rule_2423(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 2423,
        source: "Int[(c_+d_.*x_^2)/Sqrt[a_+b_.*x_^8],x_Symbol] :=
          (d+Rt[b/a,4]*c)/(2*Rt[b/a,4]) \\[Star] Int[(1+Rt[b/a,4]*x^2)/Sqrt[a+b*x^8],x] -
          (d-Rt[b/a,4]*c)/(2*Rt[b/a,4]) \\[Star] Int[(1-Rt[b/a,4]*x^2)/Sqrt[a+b*x^8],x] /;
        FreeQ[{a,b,c,d},x] && NeQ[b*c^4-a*d^4,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && neq!(&b__ * c__.pow(4) - &a__ * d__.pow(4), 0)
        },
        rhs: {
            let q = rubi_rt(&(&b__ / &a__), 4);
            if q.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }
            let base = &a__ + &b__ * x_.pow(8);
            let first_integrand = (Atom::num(1) + &q * x_.pow(2)) / base.sqrt();
            let second_integrand = (Atom::num(1) - &q * x_.pow(2)) / base.sqrt();
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(&d__ + &q * &c__, first / (Atom::num(2) * &q)) - rubi_star(&d__ - &q * &c__, second / (Atom::num(2) * q))
        },
    ));
}

fn push_rules_rule_2371(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, n_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2371,
        source: "Int[Pq_/(x_*Sqrt[a_+b_.*x_^n_]),x_Symbol] :=
          Coeff[Pq,x,0] \\[Star] Int[1/(x*Sqrt[a+b*x^n]),x] +
          Int[ExpandToSum[(Pq-Coeff[Pq,x,0])/x,x]/Sqrt[a+b*x^n],x] /;
        FreeQ[{a,b},x] && PolyQ[Pq,x] && IGtQ[n,0] && NeQ[Coeff[Pq,x,0],0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: pq__ / (x_ * (a__ + b__ * x_.pow(n_)).sqrt()),
        with: [pq__, a__, b__, n_, x_],
        optional: [b__],
        when: {
            freeq!([a__, b__], x_)
                && rubi_poly_q(&pq__, x_)
                && igtq!(n_, 0)
                && rubi_coeff(&pq__, x_, 0)
                    .is_some_and(|pq0| neq!(pq0, 0))
        },
        rhs: {
            let pq0 = rubi_coeff(&pq__, x_, 0).rubi_rhs();
            let radical = (&a__ + &b__ * x_.pow(&n_)).sqrt();
            let first = rubi_rhs_int(&(Atom::num(1) / (x_ * &radical)), x_);
            let direct = rubi_star(&pq0, first);
            let expanded = rubi_expand_to_sum(&((&pq__ - &pq0) / x_), x_);
            let second = rubi_rhs_int(&(expanded / radical), x_);

            direct + second
        },
    ));
}

fn push_rules_rule_2424(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, n_, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2424,
        source: "Int[Pq_*(a_+b_.*x_^n_)^p_,x_Symbol] :=
          Module[{q=Expon[Pq,x],j,k},
          Int[Sum[x^j*Sum[Coeff[Pq,x,j+k*n/2]*x^(k*n/2),{k,0,2*(q-j)/n+1}]*(a+b*x^n)^p,{j,0,n/2-1}],x]] /;
        FreeQ[{a,b,p},x] && PolyQ[Pq,x] && IGtQ[n/2,0] && Not[PolyQ[Pq,x^(n/2)]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [pq__, a__, b__, n_, p_, x_],
        optional: [b__],
        when: {
            freeq!([a__, b__, p_], x_)
                && rubi_poly_q(&pq__, x_)
                && igtq!(&n_ / Atom::num(2), 0)
                && !rubi_poly_q_power(&pq__, x_, &(&n_ / Atom::num(2)))
        },
        rhs: {
            let transformed = rubi_even_power_binomial_split_sum(&pq__, &a__, &b__, &n_, &p_, x_).unwrap();
            rubi_rhs_int(&transformed, x_)
        },
    ));
}

fn push_rules_rule_2425(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, n_, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2425,
        source: "Int[Pq_*(a_+b_.*x_^n_)^p_,x_Symbol] :=
          Coeff[Pq,x,n-1] \\[Star] Int[x^(n-1)*(a+b*x^n)^p,x] +
          Int[ExpandToSum[Pq-Coeff[Pq,x,n-1]*x^(n-1),x]*(a+b*x^n)^p,x] /;
        FreeQ[{a,b,p},x] && PolyQ[Pq,x] && IGtQ[n,0] && Expon[Pq,x]==n-1",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [pq__, a__, b__, n_, p_, x_],
        optional: [b__],
        when: {
            match rubi_expon(&pq__, x_) {
                Some(q) => {
                    freeq!([a__, b__, p_], x_)
                        && rubi_poly_q(&pq__, x_)
                        && igtq!(n_, 0)
                        && eqq!(Atom::num(q), &n_ - Atom::num(1))
                }
                None => false,
            }
        },
        rhs: {
            let n_i64 = integer_i64(&n_).unwrap();
            let base = &a__ + &b__ * x_.pow(&n_);
            let coefficient = rubi_coeff(&pq__, x_, n_i64 - 1).unwrap();
            let first_integrand = x_.pow(n_i64 - 1) * base.pow(&p_);
            let first = rubi_rhs_int(&first_integrand, x_);
            let expanded_to_sum = rubi_expand_to_sum(&(&pq__ - &coefficient * x_.pow(n_i64 - 1)), x_);
            let second_integrand = expanded_to_sum * base.pow(&p_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(coefficient, first) + second
        },
    ));
}

fn push_rules_rule_2426(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, n_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2426,
        source: "Int[Pq_/(a_+b_.*x_^n_),x_Symbol] :=
          Int[ExpandIntegrand[Pq/(a+b*x^n),x],x] /;
        FreeQ[{a,b},x] && PolyQ[Pq,x] && IntegerQ[n]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [pq__, a__, b__, n_, x_],
        optional: [b__],
        when: {
            freeq!([a__, b__], x_)
                && rubi_poly_q(&pq__, x_)
                && integerq!(n_)
        },
        rhs: {
            let integrand = &pq__ / (&a__ + &b__ * x_.pow(&n_));
            let expanded = rubi_expand_integrand(&integrand, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_2427(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, n_, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2427,
        source: "Int[Pq_*(a_+b_.*x_^n_)^p_,x_Symbol] :=
          With[{q=Expon[Pq,x]},
            With[{Pqq=Coeff[Pq,x,q]},
            Pqq*x^(q-n+1)*(a+b*x^n)^(p+1)/(b*(q+n*p+1)) +
            1/(b*(q+n*p+1)) \\[Star] Int[ExpandToSum[b*(q+n*p+1)*(Pq-Pqq*x^q)-a*Pqq*(q-n+1)*x^(q-n),x]*(a+b*x^n)^p,x]] /;
          NeQ[q+n*p+1,0] && q-n>=0 && (IntegerQ[2*p] || IntegerQ[p+(q+1)/(2*n)])] /;
        FreeQ[{a,b,p},x] && PolyQ[Pq,x] && IGtQ[n,0]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: ["G&R 2.110.5, CRC 88a", "G&R 2.104"],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [pq__, a__, b__, n_, p_, x_],
        optional: [b__],
        when: {
            match rubi_expon(&pq__, x_) {
                Some(q) => {
                    let denominator = Atom::num(q) + &n_ * &p_ + Atom::num(1);
                    freeq!([a__, b__, p_], x_)
                        && rubi_poly_q(&pq__, x_)
                        && igtq!(n_, 0)
                        && neq!(denominator, 0)
                        && geq!(Atom::num(q) - &n_, 0)
                        && (integerq!(Atom::num(2) * &p_)
                            || integerq!(&p_ + Atom::num(q + 1) / (Atom::num(2) * &n_)))
                }
                None => false,
            }
        },
        rhs: {
            let q = rubi_expon(&pq__, x_).unwrap();
            let n_i64 = integer_i64(&n_).unwrap();
            let base = &a__ + &b__ * x_.pow(&n_);
            let pqq = rubi_coeff(&pq__, x_, q).unwrap();
            let denominator = Atom::num(q) + &n_ * &p_ + Atom::num(1);
            let direct = &pqq * x_.pow(q - n_i64 + 1) * base.pow(&p_ + Atom::num(1)) / (&b__ * &denominator);
            let payload = rubi_expand_to_sum(
                &(&b__ * &denominator * (&pq__ - &pqq * x_.pow(q))
                    - &a__ * &pqq * Atom::num(q - n_i64 + 1) * x_.pow(q - n_i64)),
                x_,
            );
            let recursive_integrand = payload * base.pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&direct, x_)
                    + rubi_star(Atom::num(1) / (b__ * denominator), recursive)
        },
    ));
}

fn push_rules_rule_2428(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, n_, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2428,
        source: "Int[Pq_*(a_+b_.*x_^n_)^p_,x_Symbol] :=
          With[{q=Expon[Pq,x]},
          -Subst[Int[ExpandToSum[x^q*ReplaceAll[Pq,x->x^(-1)],x]*(a+b*x^(-n))^p/x^(q+2),x],x,1/x]] /;
        FreeQ[{a,b,p},x] && PolyQ[Pq,x] && ILtQ[n,0]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [pq__, a__, b__, n_, p_, x_],
        optional: [b__],
        when: {
            freeq!([a__, b__, p_], x_)
                && poly_q(&pq__, x_)
                && iltq!(n_, 0)
        },
        rhs: {
            let q = rubi_expon(&pq__, x_).unwrap();
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub_symbol = sub_guard.symbol();
            let sub_atom = Atom::var(sub_symbol);
            let replacement = sub_atom.pow(-1);
            let transformed_pq = rubi_expand_to_sum(&(sub_atom.pow(q) * substitute_symbol(&pq__, x_, replacement)), sub_symbol);
            let transformed_integrand =
                transformed_pq * (&a__ + &b__ * sub_atom.pow(-&n_)).pow(&p_) / sub_atom.pow(q + 2);
            let transformed = rubi_rhs_int(&transformed_integrand, sub_symbol);

            -rubi_subst(&transformed, sub_symbol, x_.pow(-1))
        },
    ));
}

fn push_rules_rule_2429(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, n_, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2429,
        source: "Int[Pq_*(a_+b_.*x_^n_)^p_,x_Symbol] :=
          With[{g=Denominator[n]},
          g \\[Star] Subst[Int[x^(g-1)*ReplaceAll[Pq,x->x^g]*(a+b*x^(g*n))^p,x],x,x^(1/g)]] /;
        FreeQ[{a,b,p},x] && PolyQ[Pq,x] && FractionQ[n]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [pq__, a__, b__, n_, p_, x_],
        optional: [b__],
        when: {
            freeq!([a__, b__, p_], x_)
                && poly_q(&pq__, x_)
                && fractionq!(n_)
        },
        rhs: {
            let g = rational_denominator(&n_).unwrap();
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub_symbol = sub_guard.symbol();
            let sub_atom = Atom::var(sub_symbol);
            let transformed_pq = substitute_symbol(&pq__, x_, sub_atom.pow(g));
            let transformed_integrand =
                sub_atom.pow(g - 1) * transformed_pq * (&a__ + &b__ * sub_atom.pow(Atom::num(g) * &n_)).pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, sub_symbol);
            let substituted = rubi_subst(&transformed, sub_symbol, x_.pow((1, g)));

            rubi_star(Atom::num(g), substituted)
        },
    ));
}

fn push_rules_rule_2430(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_a__, capital_b__, a__, b__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 2430,
        source: "Int[(A_+B_.*x_^m_.)*(a_+b_.*x_^n_)^p_.,x_Symbol] :=
          A \\[Star] Int[(a+b*x^n)^p,x] + B \\[Star] Int[x^m*(a+b*x^n)^p,x] /;
        FreeQ[{a,b,A,B,m,n,p},x] && EqQ[m-n+1,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (capital_a__ + capital_b__ * x_.pow(m_)) * (a__ + b__ * x_.pow(n_)).pow(p_),
        with: [capital_a__, capital_b__, a__, b__, m_, n_, p_, x_],
        optional: [capital_b__, b__, m_, p_],
        when: {
            freeq!([capital_a__, capital_b__, a__, b__, m_, n_, p_], x_)
                && eqq!(&m_ - &n_ + Atom::num(1), 0)
        },
        rhs: {
            let base = &a__ + &b__ * x_.pow(&n_);
            let first = rubi_rhs_int(&base.pow(&p_), x_);
            let second_integrand = x_.pow(&m_) * base.pow(&p_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(capital_a__, first)
                    + rubi_star(capital_b__, second)
        },
    ));
}

fn push_rules_rule_2431(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, n_, p3__, p_, x_);
    rules.push(rubi_rule!(
        order: 2431,
        source: "Int[P3_*(a_+b_.*x_^n_)^p_,x_Symbol] :=
          With[{A=Coeff[P3,x^(n/2),0],B=Coeff[P3,x^(n/2),1],C=Coeff[P3,x^(n/2),2],D=Coeff[P3,x^(n/2),3]},
          -(x*(b*A-a*C+(b*B-a*D)*x^(n/2))*(a+b*x^n)^(p+1))/(a*b*n*(p+1)) -
          1/(2*a*b*n*(p+1)) \\[Star] Int[(a+b*x^n)^(p+1)*Simp[2*a*C-2*b*A*(n*(p+1)+1)+(a*D*(n+2)-b*B*(n*(2*p+3)+2))*x^(n/2),x],x]] /;
        FreeQ[{a,b,n},x] && PolyQ[P3,x^(n/2),3] && ILtQ[p,-1]",
        desc: "OS and binomial recurrence",
        refs: [],
        pattern: p3__ * (a__ + b__ * x_.pow(n_)).pow(p_),
        with: [p3__, a__, b__, n_, p_, x_],
        optional: [b__],
        when: {
            freeq!([a__, b__, n_], x_)
                && rubi_poly_q_power_degree(&p3__, x_, &(&n_ / Atom::num(2)), 3)
                && iltq!(p_, -1)
        },
        rhs: {
            let capital_a = rubi_coeff_power(&p3__, x_, &(&n_ / Atom::num(2)), 0).unwrap();
            let capital_b = rubi_coeff_power(&p3__, x_, &(&n_ / Atom::num(2)), 1).unwrap();
            let capital_c = rubi_coeff_power(&p3__, x_, &(&n_ / Atom::num(2)), 2).unwrap();
            let capital_d = rubi_coeff_power(&p3__, x_, &(&n_ / Atom::num(2)), 3).unwrap();
            let x_half_n = x_.pow(&n_ / Atom::num(2));
            let base = &a__ + &b__ * x_.pow(&n_);
            let raised_p = &p_ + Atom::num(1);
            let direct_numerator = x_
                * (&b__ * &capital_a - &a__ * &capital_c
                    + (&b__ * &capital_b - &a__ * &capital_d) * &x_half_n)
                * base.pow(&raised_p);
            let direct = rubi_simp(
                &(-direct_numerator / (&a__ * &b__ * &n_ * &raised_p)),
                x_,
            );

            let recursive_multiplier = rubi_simp(
                &(Atom::num(2) * &a__ * &capital_c
                    - Atom::num(2)
                        * &b__
                        * &capital_a
                        * (&n_ * &raised_p + Atom::num(1))
                    + (&a__ * &capital_d * (&n_ + Atom::num(2))
                        - &b__ * &capital_b * (&n_ * (&p_ * Atom::num(2) + Atom::num(3)) + Atom::num(2)))
                        * &x_half_n),
                x_,
            );
            let recursive_integrand = base.pow(&raised_p) * recursive_multiplier;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let recursive = rubi_simp(
                &(recursive / (Atom::num(2) * &a__ * &b__ * &n_ * &raised_p)),
                x_,
            );

            rubi_simp(&(direct), x_) - rubi_star(Atom::num(1), recursive)
        },
    ));
}

fn push_rules_rule_2432(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, n_, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2432,
        source: "Int[Pq_*(a_+b_.*x_^n_)^p_.,x_Symbol] :=
          Int[ExpandIntegrand[Pq*(a+b*x^n)^p,x],x] /;
        FreeQ[{a,b,n,p},x] && (PolyQ[Pq,x] || PolyQ[Pq,x^n])",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [pq__, a__, b__, n_, p_, x_],
        optional: [b__, p_],
        when: {
            freeq!([a__, b__, n_, p_], x_)
                && (rubi_poly_q(&pq__, x_) || rubi_poly_q_power(&pq__, x_, &n_))
        },
        rhs: {
            let integrand = &pq__ * (&a__ + &b__ * x_.pow(&n_)).pow(&p_);
            let expanded = rubi_expand_integrand(&integrand, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_2433(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, n_, p_, pq__, v_);
    rules.push(rubi_rule!(
        order: 2433,
        source: "Int[Pq_*(a_+b_.*v_^n_.)^p_,x_Symbol] :=
          1/Coeff[v,x,1] \\[Star] Subst[Int[SubstFor[v,Pq,x]*(a+b*x^n)^p,x],x,v] /;
        FreeQ[{a,b,n,p},x] && LinearQ[v,x] && PolyQ[Pq,v^n]",
        desc: "Integration by substitution",
        refs: [],
        pattern: pq__ * (a__ + b__ * v_.pow(n_)).pow(p_),
        with: [pq__, a__, b__, v_, n_, p_, x_],
        optional: [b__, n_],
        when: {
            freeq!([a__, b__, n_, p_], x_)
                && rubi_linear_q(&v_, x_)
                && rubi_poly_q_power_of(&pq__, &v_, &n_, x_)
        },
        rhs: {
            let slope = rubi_coeff(&v_, x_, 1).unwrap();
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub_symbol = sub_guard.symbol();
            let sub_atom = Atom::var(sub_symbol);
            let transformed_px = rubi_subst_for(&pq__, &v_, sub_symbol);
            let transformed_integrand =
                transformed_px * (&a__ + &b__ * sub_atom.pow(&n_)).pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, sub_symbol);
            let substituted = rubi_subst(&transformed, sub_symbol, &v_);

            rubi_star(Atom::num(1) / slope, substituted)
        },
    ));
}

fn push_rules_rule_2434(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a1__, a2__, b1__, b2__, n_, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2434,
        source: "Int[Pq_*(a1_+b1_.*x_^n_.)^p_.*(a2_+b2_.*x_^n_.)^p_.,x_Symbol] :=
          Int[Pq*(a1*a2+b1*b2*x^(2*n))^p,x] /;
        FreeQ[{a1,b1,a2,b2,n,p},x] && PolyQ[Pq,x] && EqQ[a2*b1+a1*b2,0] && (IntegerQ[p] || GtQ[a1,0] && GtQ[a2,0])",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [pq__, a1__, b1__, a2__, b2__, n_, p_, x_],
        optional: [b1__, b2__, n_, p_],
        when: {
            freeq!([a1__, b1__, a2__, b2__, n_, p_], x_)
                && rubi_poly_q(&pq__, x_)
                && eqq!(&a2__ * &b1__ + &a1__ * &b2__, 0)
                && (integerq!(p_) || gtq!(a1__, 0) && gtq!(a2__, 0))
        },
        rhs: {
            let transformed =
                &pq__ * (&a1__ * &a2__ + &b1__ * &b2__ * x_.pow(Atom::num(2) * &n_)).pow(&p_);
            rubi_rhs_int(&transformed, x_)
        },
    ));
}

fn push_rules_rule_2435(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a1__, a2__, b1__, b2__, n_, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2435,
        source: "Int[Pq_*(a1_+b1_.*x_^n_.)^p_.*(a2_+b2_.*x_^n_.)^p_.,x_Symbol] :=
          (a1+b1*x^n)^FracPart[p]*(a2+b2*x^n)^FracPart[p]/(a1*a2+b1*b2*x^(2*n))^FracPart[p] \\[Star]
            Int[Pq*(a1*a2+b1*b2*x^(2*n))^p,x] /;
        FreeQ[{a1,b1,a2,b2,n,p},x] && PolyQ[Pq,x] && EqQ[a2*b1+a1*b2,0] && Not[EqQ[n,1] && LinearQ[Pq,x]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [pq__, a1__, b1__, a2__, b2__, n_, p_, x_],
        optional: [b1__, b2__, n_, p_],
        when: {
            freeq!([a1__, b1__, a2__, b2__, n_, p_], x_)
                && rubi_poly_q(&pq__, x_)
                && eqq!(&a2__ * &b1__ + &a1__ * &b2__, 0)
                && !(eqq!(n_, 1) && rubi_linear_q(&pq__, x_))
        },
        rhs: {
            let frac_part = rubi_frac_part(&p_);
            let first = &a1__ + &b1__ * x_.pow(&n_);
            let second = &a2__ + &b2__ * x_.pow(&n_);
            let combined = &a1__ * &a2__ + &b1__ * &b2__ * x_.pow(Atom::num(2) * &n_);
            let recursive = rubi_rhs_int(&(&pq__ * combined.pow(&p_)), x_);

            rubi_star(first.pow(&frac_part) * second.pow(&frac_part) / combined.pow(frac_part), recursive)
        },
    ));
}

fn push_rules_rule_2436(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 2436,
        source: "Int[(e_+f_.*x_^n_.+g_.*x_^n2_.)*(a_+b_.*x_^n_.)^p_.*(c_+d_.*x_^n_.)^p_.,x_Symbol] :=
          e*x*(a+b*x^n)^(p+1)*(c+d*x^n)^(p+1)/(a*c) /;
        FreeQ[{a,b,c,d,e,f,g,n,p},x] && EqQ[n2,2*n] && EqQ[a*c*f-e*(b*c+a*d)*(n*(p+1)+1),0] && EqQ[a*c*g-b*d*e*(2*n*(p+1)+1),0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: (e__ + f__ * x_.pow(n_) + g__ * x_.pow(n2_))
            * (a__ + b__ * x_.pow(n_)).pow(p_)
            * (c__ + d__ * x_.pow(n_)).pow(p_),
        with: [e__, f__, g__, a__, b__, c__, d__, n_, n2_, p_, x_],
        optional: [f__, g__, b__, d__, n_, n2_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, n_, p_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && eqq!(
                    &a__ * &c__ * &f__ - &e__ * (&b__ * &c__ + &a__ * &d__) * (&n_ * (&p_ + 1) + 1),
                    0
                )
                && eqq!(
                    &a__ * &c__ * &g__ - &b__ * &d__ * &e__ * (Atom::num(2) * &n_ * (&p_ + 1) + 1),
                    0
                )
        },
        rhs: {
            rubi_simp(
                &(
                &e__ * x_
                    * (&a__ + &b__ * x_.pow(&n_)).pow(&p_ + 1)
                    * (&c__ + &d__ * x_.pow(&n_)).pow(&p_ + 1)
                    / (&a__ * &c__)
                ),
                x_,
            )
        },
    ));
}

fn push_rules_rule_2437(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, g__, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 2437,
        source: "Int[(e_+g_.*x_^n2_.)*(a_+b_.*x_^n_.)^p_.*(c_+d_.*x_^n_.)^p_.,x_Symbol] :=
          e*x*(a+b*x^n)^(p+1)*(c+d*x^n)^(p+1)/(a*c) /;
        FreeQ[{a,b,c,d,e,g,n,p},x] && EqQ[n2,2*n] && EqQ[n*(p+1)+1,0] && EqQ[a*c*g-b*d*e*(2*n*(p+1)+1),0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: (e__ + g__ * x_.pow(n2_))
            * (a__ + b__ * x_.pow(n_)).pow(p_)
            * (c__ + d__ * x_.pow(n_)).pow(p_),
        with: [e__, g__, a__, b__, c__, d__, n_, n2_, p_, x_],
        optional: [g__, b__, d__, n_, n2_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, g__, n_, p_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && eqq!(&n_ * (&p_ + 1) + 1, 0)
                && eqq!(
                    &a__ * &c__ * &g__ - &b__ * &d__ * &e__ * (Atom::num(2) * &n_ * (&p_ + 1) + 1),
                    0
                )
        },
        rhs: {
            rubi_simp(
                &(
                &e__ * x_
                    * (&a__ + &b__ * x_.pow(&n_)).pow(&p_ + 1)
                    * (&c__ + &d__ * x_.pow(&n_)).pow(&p_ + 1)
                    / (&a__ * &c__)
                ),
                x_,
            )
        },
    ));
}

fn push_rules_rule_2438(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        capital_a__,
        capital_b__,
        a__,
        b__,
        c__,
        d__,
        m_,
        n_,
        p_,
        q_,
        x_
    );
    rules.push(rubi_rule!(
        order: 2438,
        source: "Int[(A_+B_.*x_^m_.)*(a_.+b_.*x_^n_)^p_.*(c_+d_.*x_^n_)^q_.,x_Symbol] :=
          A \\[Star] Int[(a+b*x^n)^p*(c+d*x^n)^q,x] + B \\[Star] Int[x^m*(a+b*x^n)^p*(c+d*x^n)^q,x] /;
        FreeQ[{a,b,c,d,A,B,m,n,p,q},x] && NeQ[b*c-a*d,0] && EqQ[m-n+1,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (capital_a__ + capital_b__ * x_.pow(m_))
            * (a__ + b__ * x_.pow(n_)).pow(p_)
            * (c__ + d__ * x_.pow(n_)).pow(q_),
        with: [capital_a__, capital_b__, a__, b__, c__, d__, m_, n_, p_, q_, x_],
        optional: [capital_b__, a__, b__, d__, m_, p_, q_],
        when: {
            freeq!([a__, b__, c__, d__, capital_a__, capital_b__, m_, n_, p_, q_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(&m_ - &n_ + Atom::num(1), 0)
        },
        rhs: {
            let first = (&a__ + &b__ * x_.pow(&n_)).pow(&p_);
            let second = (&c__ + &d__ * x_.pow(&n_)).pow(&q_);
            let first_integral = rubi_rhs_int(&(&first * &second), x_);
            let second_integral = rubi_rhs_int(&(x_.pow(&m_) * first * second), x_);

            rubi_star(capital_a__, first_integral)
                    + rubi_star(capital_b__, second_integral)
        },
    ));
}

fn push_rules_rule_2439(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, n_, p_, q_, px_, x_);
    rules.push(rubi_rule!(
        order: 2439,
        source: "Int[Px_^q_.*(a_.+b_.*(c_+d_.*x_)^n_)^p_,x_Symbol] :=
          With[{k=Denominator[n]},
          k/d \\[Star] Subst[Int[SimplifyIntegrand[x^(k-1)*ReplaceAll[Px,x->x^k/d-c/d]^q*(a+b*x^(k*n))^p,x],x],x,(c+d*x)^(1/k)]] /;
        FreeQ[{a,b,c,d,p},x] && PolynomialQ[Px,x] && IntegerQ[q] && FractionQ[n]",
        desc: "Integration by substitution",
        refs: [],
        pattern: px_.pow(q_) * (a__ + b__ * (c__ + d__ * x_).pow(n_)).pow(p_),
        with: [px_, q_, a__, b__, c__, d__, n_, p_, x_],
        optional: [q_, a__, b__, d__],
        when: {
            freeq!([a__, b__, c__, d__, p_], x_)
                && rubi_polynomial_q(&px_, x_)
                && integerq!(q_)
                && fractionq!(n_)
        },
        rhs: {
            let k_i = rational_denominator(&n_).unwrap();

            let k = Atom::num(k_i);
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let replacement = sub_atom.pow(&k) / &d__ - &c__ / &d__;
            let transformed_px = substitute_symbol(&px_, x_, replacement);
            let transformed_integrand = rubi_simplify_integrand(
                &(sub_atom.pow(k_i - 1)
                    * transformed_px.pow(&q_)
                    * (&a__ + &b__ * sub_atom.pow(&k * &n_)).pow(&p_)),
                sub,
            );
            let transformed = rubi_rhs_int(&transformed_integrand, sub);
            let substituted = rubi_subst(
                &transformed,
                sub,
                (&c__ + &d__ * x_).pow((1, k_i)),
            );

            rubi_star(k, substituted / d__)
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
    let x_ = symbols.x_;
    (c__ + d__ * x_) / (a__ + b__ * x_.pow(3)).sqrt()
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let x_ = symbols.x_;
    (c__ + d__ * x_.pow(2)) / (a__ + b__ * x_.pow(8)).sqrt()
}

#[inline(never)]
fn rubi_shared_pattern_2(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let x_ = symbols.x_;
    (c__ + d__ * x_.pow(4)) / (a__ + b__ * x_.pow(6)).sqrt()
}

#[inline(never)]
fn rubi_shared_pattern_3(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let capital_a__ = symbols.capital_a__;
    let capital_b__ = symbols.capital_b__;
    let x_ = symbols.x_;
    (capital_a__ + capital_b__ * x_) / (a__ + b__ * x_.pow(3))
}

#[inline(never)]
fn rubi_shared_pattern_4(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let p2__ = symbols.p2__;
    let x_ = symbols.x_;
    p2__ / (a__ + b__ * x_.pow(3))
}

#[inline(never)]
fn rubi_shared_pattern_5(symbols: &RubiSymbols) -> Atom {
    let a1__ = symbols.a1__;
    let a2__ = symbols.a2__;
    let b1__ = symbols.b1__;
    let b2__ = symbols.b2__;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let pq__ = symbols.pq__;
    let x_ = symbols.x_;
    pq__ * (a1__ + b1__ * x_.pow(n_)).pow(p_) * (a2__ + b2__ * x_.pow(n_)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_6(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let pq__ = symbols.pq__;
    let x_ = symbols.x_;
    pq__ * (a__ + b__ * x_.pow(n_)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_7(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let n_ = symbols.n_;
    let pq__ = symbols.pq__;
    let x_ = symbols.x_;
    pq__ / (a__ + b__ * x_.pow(n_))
}
