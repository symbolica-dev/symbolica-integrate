use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_2456(rules);
    push_rules_rule_2457(rules);
    push_rules_rule_2458(rules);
    push_rules_rule_2459(rules);
    push_rules_rule_2460(rules);
    push_rules_rule_2461(rules);
    push_rules_rule_2462(rules);
    push_rules_rule_2463(rules);
    push_rules_rule_2464(rules);
    push_rules_rule_2465(rules);
    push_rules_rule_2467(rules);
    push_rules_rule_2468(rules);
    push_rules_rule_2469(rules);
    push_rules_rule_2470(rules);
    push_rules_rule_2509(rules);
    push_rules_rule_2510(rules);
    push_rules_rule_2511(rules);
    push_rules_rule_2512(rules);
    push_rules_rule_2513(rules);
    push_rules_rule_2514(rules);
    push_rules_rule_2515(rules);
    push_rules_rule_2516(rules);
    push_rules_rule_2528(rules);
    push_rules_rule_2529(rules);
    push_rules_rule_2530(rules);
    push_rules_rule_2531(rules);
    push_rules_rule_2532(rules);
    push_rules_rule_2533(rules);
    push_rules_rule_2534(rules);
    push_rules_rule_2535(rules);
    push_rules_rule_2536(rules);
    push_rules_rule_2537(rules);
    push_rules_rule_2538(rules);
    push_rules_rule_2539(rules);
    push_rules_rule_2540(rules);
    push_rules_rule_2541(rules);
    push_rules_rule_2542(rules);
    push_rules_rule_2543(rules);
    push_rules_rule_2544(rules);
    push_rules_rule_2545(rules);
    push_rules_rule_2546(rules);
    push_rules_rule_2547(rules);
    push_rules_rule_2548(rules);
    push_rules_rule_2549(rules);
    push_rules_rule_2550(rules);
    push_rules_rule_2551(rules);
    push_rules_rule_2552(rules);
    push_rules_rule_2553(rules);
    push_rules_rule_2554(rules);
    push_rules_rule_2555(rules);
    push_rules_rule_2556(rules);
    push_rules_rule_2557(rules);
    push_rules_rule_2558(rules);
    push_rules_rule_2559(rules);
    push_rules_rule_2560(rules);
    push_rules_rule_2561(rules);
    push_rules_rule_2562(rules);
    push_rules_rule_2563(rules);
    push_rules_rule_2564(rules);
    push_rules_rule_2565(rules);
    push_rules_rule_2566(rules);
    push_rules_rule_2567(rules);
    push_rules_rule_2568(rules);
    push_rules_rule_2569(rules);
    push_rules_rule_2570(rules);
    push_rules_rule_2571(rules);
    push_rules_rule_2572(rules);
    push_rules_rule_2573(rules);
    push_rules_rule_2574(rules);
    push_rules_rule_2575(rules);
    push_rules_rule_2576(rules);
    push_rules_rule_2577(rules);
    push_rules_rule_2578(rules);
    push_rules_rule_2579(rules);
    push_rules_rule_2580(rules);
    push_rules_rule_2581(rules);
    push_rules_rule_2582(rules);
    push_rules_rule_2583(rules);
    push_rules_rule_2584(rules);
    push_rules_rule_2585(rules);
    push_rules_rule_2586(rules);
    push_rules_rule_2587(rules);
}

fn push_rules_rule_2456(rules: &mut Vec<RubiRule>) {
    rubi_symb!(p_, px_, q_, qx_, u__);
    rules.push(rubi_rule!(
        order: 2456,
        source: "Int[u_.*Px_^p_*Qx_^q_,x_Symbol] :=
          Module[{Rx=PolyGCD[Px,Qx,x]},
          Int[u*Rx^(p+q)*PolynomialQuotient[Px,Rx,x]^p*PolynomialQuotient[Qx,Rx,x]^q,x] /;
         NeQ[Rx,1]] /;
        IGtQ[p,0] && ILtQ[q,0] && PolyQ[Px,x] && PolyQ[Qx,x]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern: u__ * px_.pow(p_) * qx_.pow(q_),
        with: [u__, px_, p_, qx_, q_, x_],
        optional: [u__],
        when: {
            igtq!(p_, 0) && iltq!(q_, 0) && rubi_poly_q(&px_, x_) && rubi_poly_q(&qx_, x_)
                && rubi_poly_gcd(&px_, &qx_, x_).is_some_and(|rx| neq!(rx, 1))
        },
        rhs: {
            let rx = rubi_poly_gcd(&px_, &qx_, x_).unwrap();
            rubi_rhs_int(
                &(u__
                    * rx.pow(&p_ + &q_)
                    * rubi_polynomial_quotient(&px_, &rx, x_).unwrap().pow(p_)
                    * rubi_polynomial_quotient(&qx_, &rx, x_).unwrap().pow(q_)),
                x_,
            )
        },
    ));
}

fn push_rules_rule_2457(rules: &mut Vec<RubiRule>) {
    rubi_symb!(px__, q_, qx_, u__);
    rules.push(rubi_rule!(
        order: 2457,
        source: "Int[u_.*Px_*Qx_^q_,x_Symbol] :=
          Module[{Rx=PolyGCD[Px,Qx,x]},
          Int[u*Rx^(q+1)*PolynomialQuotient[Px,Rx,x]*PolynomialQuotient[Qx,Rx,x]^q,x] /;
         NeQ[Rx,1]] /;
        ILtQ[q,0] && PolyQ[Px,x] && PolyQ[Qx,x]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern: u__ * px__ * qx_.pow(q_),
        with: [u__, px__, qx_, q_, x_],
        optional: [u__],
        when: {
            iltq!(q_, 0)
                && rubi_poly_q(&px__, x_)
                && rubi_poly_q(&qx_, x_)
                && rubi_poly_gcd(&px__, &qx_, x_).is_some_and(|rx| neq!(rx, 1))
        },
        rhs: {
            let rx = rubi_poly_gcd(&px__, &qx_, x_).unwrap();
            rubi_rhs_int(
                &(u__
                    * rx.pow(&q_ + Atom::num(1))
                    * rubi_polynomial_quotient(&px__, &rx, x_).unwrap()
                    * rubi_polynomial_quotient(&qx_, &rx, x_).unwrap().pow(q_)),
                x_,
            )
        },
    ));
}

fn push_rules_rule_2458(rules: &mut Vec<RubiRule>) {
    rubi_symb!(p_, pn__);
    rules.push(rubi_rule!(
        order: 2458,
        source: "Int[Pn_^p_.,x_Symbol] :=
          With[{S=Coeff[Pn,x,Expon[Pn,x]-1]/(Expon[Pn,x]*Coeff[Pn,x,Expon[Pn,x]])},
          Subst[Int[ExpandToSum[ReplaceAll[Pn,x->x-S],x]^p,x],x,x+S] /;
         BinomialQ[ReplaceAll[Pn,x->x-S],x] || IntegerQ[Expon[Pn,x]/2] && TrinomialQ[ReplaceAll[Pn,x->x-S],x]] /;
        FreeQ[p,x] && PolyQ[Pn,x] && GtQ[Expon[Pn,x],2] && NeQ[Coeff[Pn,x,Expon[Pn,x]-1],0]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern: pn__.pow(p_),
        with: [pn__, p_, x_],
        optional: [p_],
        x_free: [p_],
        when: {
            (freeq!(p_, x_)
                && rubi_poly_q(&pn__, x_)
                && {
                    let n = rubi_expon(&pn__, x_).unwrap();
                    n > 2
                        && neq!(rubi_coeff(&pn__, x_, n - 1).unwrap(), 0)
                        && {
                            let s = rubi_coeff(&pn__, x_, n - 1).unwrap()
                                / (Atom::num(n) * rubi_coeff(&pn__, x_, n).unwrap());
                            let shifted = rubi_replace_all(&pn__, x_, x_ - s);
                            rubi_binomial_q(&shifted, x_)
                                || integerq!(Atom::num(n) / Atom::num(2))
                                    && rubi_trinomial_q(&shifted, x_)
                        }
                })
                .into()
        },
        rhs: {
            let n = rubi_expon(&pn__, x_).unwrap();
            let s = rubi_coeff(&pn__, x_, n - 1).unwrap()
                / (Atom::num(n) * rubi_coeff(&pn__, x_, n).unwrap());
            let shifted = rubi_replace_all(&pn__, x_, x_ - &s);
            let primitive = rubi_rhs_int(&rubi_expand_to_sum(&shifted, x_).pow(p_), x_);
            rubi_subst(&primitive, x_, x_ + s)
        },
    ));
}

fn push_rules_rule_2459(rules: &mut Vec<RubiRule>) {
    rubi_symb!(p_, pn__, qx__);
    rules.push(rubi_rule!(
        order: 2459,
        source: "Int[Pn_^p_.*Qx_,x_Symbol] :=
          With[{S=Coeff[Pn,x,Expon[Pn,x]-1]/(Expon[Pn,x]*Coeff[Pn,x,Expon[Pn,x]])},
          Subst[Int[ExpandToSum[ReplaceAll[Pn,x->x-S],x]^p*ExpandToSum[ReplaceAll[Qx,x->x-S],x],x],x,x+S] /;
         BinomialQ[ReplaceAll[Pn,x->x-S],x] || IntegerQ[Expon[Pn,x]/2] && TrinomialQ[ReplaceAll[Pn,x->x-S],x]] /;
        FreeQ[p,x] && PolyQ[Pn,x] && GtQ[Expon[Pn,x],2] && NeQ[Coeff[Pn,x,Expon[Pn,x]-1],0] && PolyQ[Qx,x] && Not[MonomialQ[Qx,x] && IGtQ[p,0]]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern: pn__.pow(p_) * qx__,
        with: [pn__, p_, qx__, x_],
        optional: [p_],
        x_free: [p_],
        when: {
            (freeq!(p_, x_)
                && rubi_poly_q(&pn__, x_)
                && {
                    let n = rubi_expon(&pn__, x_).unwrap();
                    n > 2
                        && neq!(rubi_coeff(&pn__, x_, n - 1).unwrap(), 0)
                        && rubi_poly_q(&qx__, x_)
                        && !(rubi_monomial_q(&qx__, x_) && igtq!(p_, 0))
                        && {
                            let s = rubi_coeff(&pn__, x_, n - 1).unwrap()
                                / (Atom::num(n) * rubi_coeff(&pn__, x_, n).unwrap());
                            let shifted = rubi_replace_all(&pn__, x_, x_ - s);
                            rubi_binomial_q(&shifted, x_)
                                || integerq!(Atom::num(n) / Atom::num(2))
                                    && rubi_trinomial_q(&shifted, x_)
                        }
                })
                .into()
        },
        rhs: {
            let n = rubi_expon(&pn__, x_).unwrap();
            let s = rubi_coeff(&pn__, x_, n - 1).unwrap()
                / (Atom::num(n) * rubi_coeff(&pn__, x_, n).unwrap());
            let shifted_pn = rubi_replace_all(&pn__, x_, x_ - &s);
            let shifted_qx = rubi_replace_all(&qx__, x_, x_ - &s);
            let primitive = rubi_rhs_int(
                &(rubi_expand_to_sum(&shifted_pn, x_).pow(p_)
                    * rubi_expand_to_sum(&shifted_qx, x_)),
                x_,
            );
            rubi_subst(&primitive, x_, x_ + s)
        },
    ));
}

fn push_rules_rule_2460(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; p_, px_, u__);
    rules.push(rubi_rule!(
        order: 2460,
        source: "Int[u_.*Px_^p_,x_Symbol] :=
          With[{Qx=Factor[ReplaceAll[Px,x->Sqrt[x]]]},
          Int[ExpandIntegrand[u*ReplaceAll[Qx,x->x^2]^p,x],x] /;
         Not[SumQ[NonfreeFactors[Qx,x]]]] /;
        PolyQ[Px,x^2] && GtQ[Expon[Px,x],2] && Not[BinomialQ[Px,x]] && Not[TrinomialQ[Px,x]] && ILtQ[p,0] && RationalFunctionQ[u,x]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_11(symbols),
        with: [u__, px_, p_, x_],
        optional: [u__],
        when: {
            rubi_poly_q_power(&px_, x_, &Atom::num(2))
                && rubi_expon(&px_, x_).is_some_and(|n| n > 2)
                && !rubi_binomial_q(&px_, x_)
                && !rubi_trinomial_q(&px_, x_)
                && iltq!(p_, 0)
                && rubi_rational_function_q(&u__, x_)
                && {
                    let qx = rubi_replace_all(&px_, x_, x_.sqrt()).factor();
                    !rubi_sum_q(&rubi_nonfree_factors(&qx, x_))
                }
        },
        rhs: {
            let qx = rubi_replace_all(&px_, x_, x_.sqrt()).factor();
            let restored = rubi_replace_all(&qx, x_, x_.pow(2));
            rubi_rhs_int(
                &rubi_expand_integrand(&(u__ * restored.pow(p_)), x_),
                x_,
            )
        },
    ));
}

fn push_rules_rule_2461(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; p_, px_, u__);
    rules.push(rubi_rule!(
        order: 2461,
        source: "Int[u_.*Px_^p_,x_Symbol] :=
          With[{Qx=Factor[ReplaceAll[Px,x->Sqrt[x]]]},
          Int[ExpandIntegrand[u,ReplaceAll[Qx,x->x^2]^p,x],x] /;
         Not[SumQ[NonfreeFactors[Qx,x]]]] /;
        PolyQ[Px,x^2] && GtQ[Expon[Px,x],2] && Not[BinomialQ[Px,x]] && Not[TrinomialQ[Px,x]] && ILtQ[p,0]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_11(symbols),
        with: [u__, px_, p_, x_],
        optional: [u__],
        when: {
            rubi_poly_q_power(&px_, x_, &Atom::num(2))
                && rubi_expon(&px_, x_).is_some_and(|n| n > 2)
                && !rubi_binomial_q(&px_, x_)
                && !rubi_trinomial_q(&px_, x_)
                && iltq!(p_, 0)
                && {
                    let qx = rubi_replace_all(&px_, x_, x_.sqrt()).factor();
                    !rubi_sum_q(&rubi_nonfree_factors(&qx, x_))
                }
        },
        rhs: {
            let qx = rubi_replace_all(&px_, x_, x_.sqrt()).factor();
            let restored = rubi_replace_all(&qx, x_, x_.pow(2));
            rubi_rhs_int(
                &rubi_expand_integrand_product(&u__, &restored.pow(p_), x_),
                x_,
            )
        },
    ));
}

fn push_rules_rule_2462(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; p_, px_, u__);
    rules.push(rubi_rule!(
        order: 2462,
        source: "Int[u_.*Px_^p_,x_Symbol] :=
          With[{Qx=Factor[Px]},
          Int[ExpandIntegrand[u*Qx^p,x],x] /;
         Not[SumQ[NonfreeFactors[Qx,x]]]] /;
        PolyQ[Px,x] && GtQ[Expon[Px,x],2] && Not[BinomialQ[Px,x]] && Not[TrinomialQ[Px,x]] && ILtQ[p,0] && RationalFunctionQ[u,x]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_11(symbols),
        with: [u__, px_, p_, x_],
        optional: [u__],
        when: {
            rubi_poly_q(&px_, x_)
                && rubi_expon(&px_, x_).is_some_and(|n| n > 2)
                && !rubi_binomial_q(&px_, x_)
                && !rubi_trinomial_q(&px_, x_)
                && iltq!(p_, 0)
                && rubi_rational_function_q(&u__, x_)
                && {
                    let qx = px_.factor();
                    !rubi_sum_q(&rubi_nonfree_factors(&qx, x_))
                }
        },
        rhs: {
            let qx = px_.factor();
            rubi_rhs_int(
                &rubi_expand_integrand(&(u__ * qx.pow(p_)), x_),
                x_,
            )
        },
    ));
}

fn push_rules_rule_2463(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; p_, px_, u__);
    rules.push(rubi_rule!(
        order: 2463,
        source: "Int[u_.*Px_^p_,x_Symbol] :=
          With[{Qx=Factor[Px]},
          Int[ExpandIntegrand[u,Qx^p,x],x] /;
         Not[SumQ[NonfreeFactors[Qx,x]]]] /;
        PolyQ[Px,x] && GtQ[Expon[Px,x],2] && Not[BinomialQ[Px,x]] && Not[TrinomialQ[Px,x]] && ILtQ[p,0]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_11(symbols),
        with: [u__, px_, p_, x_],
        optional: [u__],
        when: {
            rubi_poly_q(&px_, x_)
                && rubi_expon(&px_, x_).is_some_and(|n| n > 2)
                && !rubi_binomial_q(&px_, x_)
                && !rubi_trinomial_q(&px_, x_)
                && iltq!(p_, 0)
                && {
                    let qx = px_.factor();
                    !rubi_sum_q(&rubi_nonfree_factors(&qx, x_))
                }
        },
        rhs: {
            let qx = px_.factor();
            rubi_rhs_int(
                &rubi_expand_integrand_product(&u__, &qx.pow(p_), x_),
                x_,
            )
        },
    ));
}

fn push_rules_rule_2464(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; p_, px_, u__);
    rules.push(rubi_rule!(
        order: 2464,
        source: "Int[u_.*Px_^p_,x_Symbol] :=
          With[{Qx=Factor[Px]},
          Int[u*Qx^p,x] /;
         Not[SumQ[NonfreeFactors[Qx,x]]]] /;
        PolyQ[Px,x] && GtQ[Expon[Px,x],2] && Not[BinomialQ[Px,x]] && Not[TrinomialQ[Px,x]] && IGtQ[p,1]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_11(symbols),
        with: [u__, px_, p_, x_],
        optional: [u__],
        when: {
            rubi_poly_q(&px_, x_)
                && rubi_expon(&px_, x_).is_some_and(|n| n > 2)
                && !rubi_binomial_q(&px_, x_)
                && !rubi_trinomial_q(&px_, x_)
                && igtq!(p_, 1)
                && {
                    let qx = px_.factor();
                    !rubi_sum_q(&rubi_nonfree_factors(&qx, x_))
                }
        },
        rhs: {
            let qx = px_.factor();
            rubi_rhs_int(&(u__ * qx.pow(p_)), x_)
        },
    ));
}

fn push_rules_rule_2465(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; p_, px_, u__);
    rules.push(rubi_rule!(
        order: 2465,
        source: "Int[u_.*Px_^p_,x_Symbol] :=
          Int[ExpandToSum[u,Px^p,x],x] /;
        PolyQ[Px,x] && GtQ[Expon[Px,x],2] && Not[BinomialQ[Px,x]] && Not[TrinomialQ[Px,x]] && IGtQ[p,0]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_11(symbols),
        with: [u__, px_, p_, x_],
        optional: [u__],
        when: {
            rubi_poly_q(&px_, x_)
                && rubi_expon(&px_, x_).is_some_and(|n| n > 2)
                && !rubi_binomial_q(&px_, x_)
                && !rubi_trinomial_q(&px_, x_)
                && igtq!(p_, 0)
        },
        rhs: {
            rubi_rhs_int(
                &rubi_expand_to_sum_product(&u__, &px_.pow(p_), x_),
                x_,
            )
        },
    ));
}

fn push_rules_rule_2467(rules: &mut Vec<RubiRule>) {
    rubi_symb!(fx__, p_, px_);
    rules.push(rubi_rule!(
        order: 2467,
        source: "Int[Px_^p_*Fx_.,x_Symbol] :=
          With[{r=Expon[Px,x,Min]},
          Px^FracPart[p]/(x^(r*FracPart[p])*ExpandToSum[Px/x^r,x]^FracPart[p]) \\[Star] Int[x^(p*r)*ExpandToSum[Px/x^r,x]^p*Fx,x] /;
         IGtQ[r,0]] /;
        FreeQ[p,x] && PolyQ[Px,x] && Not[IntegerQ[p]] && Not[MonomialQ[Px,x]] && Not[PolyQ[Fx,x]]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern: px_.pow(p_) * fx__,
        with: [px_, p_, fx__, x_],
        optional: [fx__],
        x_free: [p_],
        when: {
            freeq!(p_, x_)
                && rubi_poly_q(&px_, x_)
                && !integerq!(p_)
                && !rubi_monomial_q(&px_, x_)
                && !rubi_poly_q(&fx__, x_)
                && rubi_expon_min(&px_, x_).is_some_and(|r| r > 0)
        },
        rhs: {
            let r = rubi_expon_min(&px_, x_).unwrap();
            let expanded = rubi_expand_to_sum(&(&px_ / x_.pow(r)), x_);
            let frac_p = rubi_frac_part(&p_);
            let multiplier = px_.pow(&frac_p)
                / (x_.pow(Atom::num(r) * &frac_p) * expanded.pow(&frac_p));
            let recursive = rubi_rhs_int(
                &(x_.pow(&p_ * r) * expanded.pow(&p_) * fx__),
                x_,
            );
            rubi_star(multiplier, recursive)
        },
    ));
}

fn push_rules_rule_2468(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, fx__, p_, r_, s_, x_);
    rules.push(rubi_rule!(
        order: 2468,
        source: "Int[(a_.*x_^r_.+b_.*x_^s_.)^p_*Fx_.,x_Symbol] :=
          (a*x^r+b*x^s)^p/(x^(p*r)*(a+b*x^(s-r))^p) \\[Star] Int[x^(p*r)*(a+b*x^(s-r))^p*Fx,x] /;
        FreeQ[{a,b,p,r,s},x] && Not[IntegerQ[p]] && PosQ[s-r] && Not[EqQ[p,1] && EqQ[Fx,1]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern: (a__ * x_.pow(r_) + b__ * x_.pow(s_)).pow(p_) * fx__,
        with: [a__, r_, b__, s_, p_, fx__, x_],
        optional: [a__, r_, b__, s_, fx__],
        x_free: [a__, b__, p_, r_, s_],
        when: {
            freeq!([a__, b__, p_, r_, s_], x_)
                && !integerq!(p_)
                && posq!(&s_ - &r_)
                && !(eqq!(p_, 1) && eqq!(fx__, 1))
        },
        rhs: {
            let original = (&a__ * x_.pow(&r_) + &b__ * x_.pow(&s_)).pow(&p_);
            let normalized = (&a__ + &b__ * x_.pow(&s_ - &r_)).pow(&p_);
            let recursive = rubi_rhs_int(
                &(x_.pow(&p_ * &r_) * &normalized * fx__),
                x_,
            );
            rubi_star(original / (x_.pow(&p_ * &r_) * normalized), recursive)
        },
    ));
}

fn push_rules_rule_2469(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, fx__, p_, r_, s_, t_, x_);
    rules.push(rubi_rule!(
        order: 2469,
        source: "Int[(a_.*x_^r_.+b_.*x_^s_.+c_.*x_^t_.)^p_*Fx_.,x_Symbol] :=
          (a*x^r+b*x^s+c*x^t)^p/(x^(p*r)*(a+b*x^(s-r)+c*x^(t-r))^p) \\[Star] Int[x^(p*r)*(a+b*x^(s-r)+c*x^(t-r))^p*Fx,x] /;
        FreeQ[{a,b,c,p,r,s,t},x] && Not[IntegerQ[p]] && PosQ[s-r] && PosQ[t-r] && Not[EqQ[p,1] && EqQ[Fx,1]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern: (a__ * x_.pow(r_) + b__ * x_.pow(s_) + c__ * x_.pow(t_)).pow(p_) * fx__,
        with: [a__, r_, b__, s_, c__, t_, p_, fx__, x_],
        optional: [a__, r_, b__, s_, c__, t_, fx__],
        x_free: [a__, b__, c__, p_, r_, s_, t_],
        when: {
            freeq!([a__, b__, c__, p_, r_, s_, t_], x_)
                && !integerq!(p_)
                && posq!(&s_ - &r_)
                && posq!(&t_ - &r_)
                && !(eqq!(p_, 1) && eqq!(fx__, 1))
        },
        rhs: {
            let original = (&a__ * x_.pow(&r_)
                + &b__ * x_.pow(&s_)
                + &c__ * x_.pow(&t_))
                .pow(&p_);
            let normalized = (&a__
                + &b__ * x_.pow(&s_ - &r_)
                + &c__ * x_.pow(&t_ - &r_))
                .pow(&p_);
            let recursive = rubi_rhs_int(
                &(x_.pow(&p_ * &r_) * &normalized * fx__),
                x_,
            );
            rubi_star(original / (x_.pow(&p_ * &r_) * normalized), recursive)
        },
    ));
}

fn push_rules_rule_2470(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, fx__, p_, q_, r_, s_, t_, x_);
    rules.push(rubi_rule!(
        order: 2470,
        source: "Int[(a_.*x_^r_.+b_.*x_^s_.+c_.*x_^t_.+d_.*x_^q_.)^p_*Fx_.,x_Symbol] :=
          (a*x^r+b*x^s+c*x^t+d*x^q)^p/(x^(p*r)*(a+b*x^(s-r)+c*x^(t-r)+d*x^(q-r))^p) \\[Star] Int[x^(p*r)*(a+b*x^(s-r)+c*x^(t-r)+d*x^(q-r))^p*Fx,x] /;
        FreeQ[{a,b,c,d,p,r,s,t,q},x] && Not[IntegerQ[p]] && PosQ[s-r] && PosQ[t-r] && PosQ[q-r] && Not[EqQ[p,1] && EqQ[Fx,1]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern: (a__ * x_.pow(r_) + b__ * x_.pow(s_) + c__ * x_.pow(t_) + d__ * x_.pow(q_)).pow(p_) * fx__,
        with: [a__, r_, b__, s_, c__, t_, d__, q_, p_, fx__, x_],
        optional: [a__, r_, b__, s_, c__, t_, d__, q_, fx__],
        x_free: [a__, b__, c__, d__, p_, r_, s_, t_, q_],
        when: {
            freeq!([a__, b__, c__, d__, p_, r_, s_, t_, q_], x_)
                && !integerq!(p_)
                && posq!(&s_ - &r_)
                && posq!(&t_ - &r_)
                && posq!(&q_ - &r_)
                && !(eqq!(p_, 1) && eqq!(fx__, 1))
        },
        rhs: {
            let original = (&a__ * x_.pow(&r_)
                + &b__ * x_.pow(&s_)
                + &c__ * x_.pow(&t_)
                + &d__ * x_.pow(&q_))
                .pow(&p_);
            let normalized = (&a__
                + &b__ * x_.pow(&s_ - &r_)
                + &c__ * x_.pow(&t_ - &r_)
                + &d__ * x_.pow(&q_ - &r_))
                .pow(&p_);
            let recursive = rubi_rhs_int(
                &(x_.pow(&p_ * &r_) * &normalized * fx__),
                x_,
            );
            rubi_star(original / (x_.pow(&p_ * &r_) * normalized), recursive)
        },
    ));
}

fn push_rules_rule_2509(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; g__, h__, m_, p_, pn__, x_);
    rules.push(rubi_rule!(
        order: 2509,
        source: "Int[(g_+h_.*x_)^m_.*Pn_^p_.,x_Symbol] :=
          With[{Px=ReplaceAll[Pn,x->(x-g)/h]},
          1/h \\[Star] Subst[Int[x^m*ExpandToSum[Px,x]^p,x],x,g+h*x] /;
         BinomialQ[Px,x]] /;
        FreeQ[{g,h,m,p},x] && PolyQ[Pn,x]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [g__, h__, m_, pn__, p_, x_],
        optional: [h__, m_, p_],
        x_free: [g__, h__, m_, p_],
        when: {
            freeq!([g__, h__, m_, p_], x_)
                && rubi_poly_q(&pn__, x_)
                && {
                    let px = rubi_replace_all(&pn__, x_, (x_ - &g__) / &h__);
                    rubi_binomial_q(&px, x_)
                }
        },
        rhs: {
            let px = rubi_replace_all(&pn__, x_, (x_ - &g__) / &h__);
            let primitive = rubi_rhs_int(
                &(x_.pow(&m_) * rubi_expand_to_sum(&px, x_).pow(&p_)),
                x_,
            );
            rubi_star(Atom::num(1) / &h__, rubi_subst(&primitive, x_, &g__ + &h__ * x_))
        },
    ));
}

fn push_rules_rule_2510(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; m_, p_, pn__, u_);
    rules.push(rubi_rule!(
        order: 2510,
        source: "Int[u_^m_.*Pn_^p_.,x_Symbol] :=
          With[{Px=ReplaceAll[Pn,x->(x-Coeff[u,x,0])/Coeff[u,x,1]]},
          1/Coeff[u,x,1] \\[Star] Subst[Int[x^m*ExpandToSum[Px,x]^p,x],x,u] /;
         BinomialQ[Px,x]] /;
        FreeQ[{m,p},x] && LinearQ[u,x] && PolyQ[Pn,x] && NeQ[Coeff[u,x,0],0]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_10(symbols),
        with: [u_, m_, pn__, p_, x_],
        optional: [m_, p_],
        x_free: [m_, p_],
        when: {
            freeq!([m_, p_], x_)
                && rubi_linear_q(&u_, x_)
                && rubi_poly_q(&pn__, x_)
                && rubi_coeff(&u_, x_, 0).is_some_and(|coefficient| neq!(coefficient, 0))
                && {
                    let u0 = rubi_coeff(&u_, x_, 0).unwrap();
                    let u1 = rubi_coeff(&u_, x_, 1).unwrap();
                    let px = rubi_replace_all(&pn__, x_, (x_ - u0) / u1);
                    rubi_binomial_q(&px, x_)
                }
        },
        rhs: {
            let u0 = rubi_coeff(&u_, x_, 0).unwrap();
            let u1 = rubi_coeff(&u_, x_, 1).unwrap();
            let px = rubi_replace_all(&pn__, x_, (x_ - u0) / &u1);
            let primitive = rubi_rhs_int(
                &(x_.pow(&m_) * rubi_expand_to_sum(&px, x_).pow(&p_)),
                x_,
            );
            rubi_star(Atom::num(1) / u1, rubi_subst(&primitive, x_, u_))
        },
    ));
}

fn push_rules_rule_2511(rules: &mut Vec<RubiRule>) {
    rubi_symb!(g__, h__, m_, p_, pn__, q_, qn_, x_);
    rules.push(rubi_rule!(
        order: 2511,
        source: "Int[(g_+h_.*x_)^m_.*Pn_^p_.*Qn_^q_.,x_Symbol] :=
          With[{Px=ReplaceAll[Pn,x->(x-g)/h], Qx=ReplaceAll[Qn,x->(x-g)/h]},
          1/h \\[Star] Subst[Int[x^m*ExpandToSum[Px,x]^p*ExpandToSum[Qx,x]^q,x],x,g+h*x] /;
         BinomialQ[Px,x] && BinomialQ[Qx,x]] /;
        FreeQ[{g,h,m,p,q},x] && PolyQ[Pn,x] && PolyQ[Qn,x] && EqQ[Expon[Pn,x],Expon[Qn,x]]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern: (g__ + h__ * x_).pow(m_) * pn__.pow(p_) * qn_.pow(q_),
        with: [g__, h__, m_, pn__, p_, qn_, q_, x_],
        optional: [h__, m_, p_, q_],
        x_free: [g__, h__, m_, p_, q_],
        when: {
            freeq!([g__, h__, m_, p_, q_], x_)
                && rubi_poly_q(&pn__, x_)
                && rubi_poly_q(&qn_, x_)
                && rubi_expon(&pn__, x_)
                    .zip(rubi_expon(&qn_, x_))
                    .is_some_and(|(pn_degree, qn_degree)| pn_degree == qn_degree)
                && {
                    let replacement = (x_ - &g__) / &h__;
                    let px = rubi_replace_all(&pn__, x_, &replacement);
                    let qx = rubi_replace_all(&qn_, x_, replacement);
                    rubi_binomial_q(&px, x_) && rubi_binomial_q(&qx, x_)
                }
        },
        rhs: {
            let replacement = (x_ - &g__) / &h__;
            let px = rubi_replace_all(&pn__, x_, &replacement);
            let qx = rubi_replace_all(&qn_, x_, replacement);
            let primitive = rubi_rhs_int(
                &(x_.pow(&m_)
                    * rubi_expand_to_sum(&px, x_).pow(&p_)
                    * rubi_expand_to_sum(&qx, x_).pow(&q_)),
                x_,
            );
            rubi_star(Atom::num(1) / &h__, rubi_subst(&primitive, x_, &g__ + &h__ * x_))
        },
    ));
}

fn push_rules_rule_2512(rules: &mut Vec<RubiRule>) {
    rubi_symb!(m_, p_, pn__, q_, qn_, u_);
    rules.push(rubi_rule!(
        order: 2512,
        source: "Int[u_^m_.*Pn_^p_.*Qn_^q_.,x_Symbol] :=
          With[{Px=ReplaceAll[Pn,x->(x-Coeff[u,x,0])/Coeff[u,x,1]], Qx=ReplaceAll[Qn,x->(x-Coeff[u,x,0])/Coeff[u,x,1]]},
          1/Coeff[u,x,1] \\[Star] Subst[Int[x^m*ExpandToSum[Px,x]^p*ExpandToSum[Qx,x]^q,x],x,u] /;
         BinomialQ[Px,x] && BinomialQ[Qx,x]] /;
        FreeQ[{m,p,q},x] && LinearQ[u,x] && PolyQ[Pn,x] && PolyQ[Qn,x] && EqQ[Expon[Pn,x],Expon[Qn,x]] && NeQ[Coeff[u,x,0],0]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern: u_.pow(m_) * pn__.pow(p_) * qn_.pow(q_),
        with: [u_, m_, pn__, p_, qn_, q_, x_],
        optional: [m_, p_, q_],
        x_free: [m_, p_, q_],
        when: {
            freeq!([m_, p_, q_], x_)
                && rubi_linear_q(&u_, x_)
                && rubi_poly_q(&pn__, x_)
                && rubi_poly_q(&qn_, x_)
                && rubi_expon(&pn__, x_)
                    .zip(rubi_expon(&qn_, x_))
                    .is_some_and(|(pn_degree, qn_degree)| pn_degree == qn_degree)
                && rubi_coeff(&u_, x_, 0).is_some_and(|coefficient| neq!(coefficient, 0))
                && {
                    let u0 = rubi_coeff(&u_, x_, 0).unwrap();
                    let u1 = rubi_coeff(&u_, x_, 1).unwrap();
                    let replacement = (x_ - u0) / u1;
                    let px = rubi_replace_all(&pn__, x_, &replacement);
                    let qx = rubi_replace_all(&qn_, x_, replacement);
                    rubi_binomial_q(&px, x_) && rubi_binomial_q(&qx, x_)
                }
        },
        rhs: {
            let u0 = rubi_coeff(&u_, x_, 0).unwrap();
            let u1 = rubi_coeff(&u_, x_, 1).unwrap();
            let replacement = (x_ - u0) / &u1;
            let px = rubi_replace_all(&pn__, x_, &replacement);
            let qx = rubi_replace_all(&qn_, x_, replacement);
            let primitive = rubi_rhs_int(
                &(x_.pow(&m_)
                    * rubi_expand_to_sum(&px, x_).pow(&p_)
                    * rubi_expand_to_sum(&qx, x_).pow(&q_)),
                x_,
            );
            rubi_star(Atom::num(1) / u1, rubi_subst(&primitive, x_, u_))
        },
    ));
}

fn push_rules_rule_2513(rules: &mut Vec<RubiRule>) {
    rubi_symb!(g__, h__, m_, p_, pn__, q_, qn_, r_, rn__, x_);
    rules.push(rubi_rule!(
        order: 2513,
        source: "Int[(g_+h_.*x_)^m_.*Pn_^p_.*Qn_^q_.*Rn_^r_.,x_Symbol] :=
          With[{Px=ReplaceAll[Pn,x->(x-g)/h], Qx=ReplaceAll[Qn,x->(x-g)/h], Rx=ReplaceAll[Rn,x->(x-g)/h]},
          1/h \\[Star] Subst[Int[x^m*ExpandToSum[Px,x]^p*ExpandToSum[Qx,x]^q*ExpandToSum[Rx,x]^r,x],x,g+h*x] /;
         BinomialQ[Px,x] && BinomialQ[Qx,x] && BinomialQ[Rx,x]] /;
        FreeQ[{g,h,m,p,q,r},x] && PolyQ[Pn,x] && PolyQ[Qn,x] && PolyQ[Rn,x] &&
          EqQ[Expon[Pn,x],Expon[Qn,x]] && EqQ[Expon[Pn,x],Expon[Rn,x]]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern: (g__ + h__ * x_).pow(m_) * pn__.pow(p_) * qn_.pow(q_) * rn__.pow(r_),
        with: [g__, h__, m_, pn__, p_, qn_, q_, rn__, r_, x_],
        optional: [h__, m_, p_, q_, r_],
        x_free: [g__, h__, m_, p_, q_, r_],
        when: {
            freeq!([g__, h__, m_, p_, q_, r_], x_)
                && rubi_poly_q(&pn__, x_)
                && rubi_poly_q(&qn_, x_)
                && rubi_poly_q(&rn__, x_)
                && rubi_expon(&pn__, x_)
                    .zip(rubi_expon(&qn_, x_))
                    .is_some_and(|(pn_degree, qn_degree)| pn_degree == qn_degree)
                && rubi_expon(&pn__, x_)
                    .zip(rubi_expon(&rn__, x_))
                    .is_some_and(|(pn_degree, rn_degree)| pn_degree == rn_degree)
                && {
                    let replacement = (x_ - &g__) / &h__;
                    let px = rubi_replace_all(&pn__, x_, &replacement);
                    let qx = rubi_replace_all(&qn_, x_, &replacement);
                    let rx = rubi_replace_all(&rn__, x_, replacement);
                    rubi_binomial_q(&px, x_)
                        && rubi_binomial_q(&qx, x_)
                        && rubi_binomial_q(&rx, x_)
                }
        },
        rhs: {
            let replacement = (x_ - &g__) / &h__;
            let px = rubi_replace_all(&pn__, x_, &replacement);
            let qx = rubi_replace_all(&qn_, x_, &replacement);
            let rx = rubi_replace_all(&rn__, x_, replacement);
            let primitive = rubi_rhs_int(
                &(x_.pow(&m_)
                    * rubi_expand_to_sum(&px, x_).pow(&p_)
                    * rubi_expand_to_sum(&qx, x_).pow(&q_)
                    * rubi_expand_to_sum(&rx, x_).pow(&r_)),
                x_,
            );
            rubi_star(Atom::num(1) / &h__, rubi_subst(&primitive, x_, &g__ + &h__ * x_))
        },
    ));
}

fn push_rules_rule_2514(rules: &mut Vec<RubiRule>) {
    rubi_symb!(m_, p_, pn__, q_, qn_, r_, rn__, u_);
    rules.push(rubi_rule!(
        order: 2514,
        source: "Int[u_^m_.*Pn_^p_.*Qn_^q_.*Rn_^r_.,x_Symbol] :=
          With[{Px=ReplaceAll[Pn,x->(x-Coeff[u,x,0])/Coeff[u,x,1]], Qx=ReplaceAll[Qn,x->(x-Coeff[u,x,0])/Coeff[u,x,1]],
            Rx=ReplaceAll[Rn,x->(x-Coeff[u,x,0])/Coeff[u,x,1]]},
          1/Coeff[u,x,1] \\[Star] Subst[Int[x^m*ExpandToSum[Px,x]^p*ExpandToSum[Qx,x]^q*ExpandToSum[Rx,x]^r,x],x,u] /;
         BinomialQ[Px,x] && BinomialQ[Qx,x] && BinomialQ[Rx,x]] /;
        FreeQ[{m,p,q,r},x] && LinearQ[u,x] && PolyQ[Pn,x] && PolyQ[Qn,x] && PolyQ[Rn,x] &&
          EqQ[Expon[Pn,x],Expon[Qn,x]] && EqQ[Expon[Pn,x],Expon[Rn,x]] && NeQ[Coeff[u,x,0],0]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern: u_.pow(m_) * pn__.pow(p_) * qn_.pow(q_) * rn__.pow(r_),
        with: [u_, m_, pn__, p_, qn_, q_, rn__, r_, x_],
        optional: [m_, p_, q_, r_],
        x_free: [m_, p_, q_, r_],
        when: {
            freeq!([m_, p_, q_, r_], x_)
                && rubi_linear_q(&u_, x_)
                && rubi_poly_q(&pn__, x_)
                && rubi_poly_q(&qn_, x_)
                && rubi_poly_q(&rn__, x_)
                && rubi_expon(&pn__, x_)
                    .zip(rubi_expon(&qn_, x_))
                    .is_some_and(|(pn_degree, qn_degree)| pn_degree == qn_degree)
                && rubi_expon(&pn__, x_)
                    .zip(rubi_expon(&rn__, x_))
                    .is_some_and(|(pn_degree, rn_degree)| pn_degree == rn_degree)
                && rubi_coeff(&u_, x_, 0).is_some_and(|coefficient| neq!(coefficient, 0))
                && {
                    let u0 = rubi_coeff(&u_, x_, 0).unwrap();
                    let u1 = rubi_coeff(&u_, x_, 1).unwrap();
                    let replacement = (x_ - u0) / u1;
                    let px = rubi_replace_all(&pn__, x_, &replacement);
                    let qx = rubi_replace_all(&qn_, x_, &replacement);
                    let rx = rubi_replace_all(&rn__, x_, replacement);
                    rubi_binomial_q(&px, x_)
                        && rubi_binomial_q(&qx, x_)
                        && rubi_binomial_q(&rx, x_)
                }
        },
        rhs: {
            let u0 = rubi_coeff(&u_, x_, 0).unwrap();
            let u1 = rubi_coeff(&u_, x_, 1).unwrap();
            let replacement = (x_ - u0) / &u1;
            let px = rubi_replace_all(&pn__, x_, &replacement);
            let qx = rubi_replace_all(&qn_, x_, &replacement);
            let rx = rubi_replace_all(&rn__, x_, replacement);
            let primitive = rubi_rhs_int(
                &(x_.pow(&m_)
                    * rubi_expand_to_sum(&px, x_).pow(&p_)
                    * rubi_expand_to_sum(&qx, x_).pow(&q_)
                    * rubi_expand_to_sum(&rx, x_).pow(&r_)),
                x_,
            );
            rubi_star(Atom::num(1) / u1, rubi_subst(&primitive, x_, u_))
        },
    ));
}

fn push_rules_rule_2515(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; g__, h__, m_, p_, pn__, x_);
    rules.push(rubi_rule!(
        order: 2515,
        source: "Int[(g_+h_.*x_)^m_.*Pn_^p_.,x_Symbol] :=
          With[{Px=ReplaceAll[Pn,x->(x-g)/h]},
          1/h \\[Star] Subst[Int[x^m*ExpandToSum[Px,x]^p,x],x,g+h*x] /;
         TrinomialQ[Px,x]] /;
        FreeQ[{g,h,m,p},x] && PolyQ[Pn,x]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [g__, h__, m_, pn__, p_, x_],
        optional: [h__, m_, p_],
        x_free: [g__, h__, m_, p_],
        when: {
            freeq!([g__, h__, m_, p_], x_)
                && rubi_poly_q(&pn__, x_)
                && {
                    let px = rubi_replace_all(&pn__, x_, (x_ - &g__) / &h__);
                    rubi_trinomial_q(&px, x_)
                }
        },
        rhs: {
            let px = rubi_replace_all(&pn__, x_, (x_ - &g__) / &h__);
            let primitive = rubi_rhs_int(
                &(x_.pow(&m_) * rubi_expand_to_sum(&px, x_).pow(&p_)),
                x_,
            );
            rubi_star(Atom::num(1) / &h__, rubi_subst(&primitive, x_, &g__ + &h__ * x_))
        },
    ));
}

fn push_rules_rule_2516(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; m_, p_, pn__, u_);
    rules.push(rubi_rule!(
        order: 2516,
        source: "Int[u_^m_.*Pn_^p_.,x_Symbol] :=
          With[{Px=ReplaceAll[Pn,x->(x-Coeff[u,x,0])/Coeff[u,x,1]]},
          1/Coeff[u,x,1] \\[Star] Subst[Int[x^m*ExpandToSum[Px,x]^p,x],x,u] /;
         TrinomialQ[Px,x]] /;
        FreeQ[{m,p},x] && LinearQ[u,x] && PolyQ[Pn,x] && NeQ[Coeff[u,x,0],0]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_10(symbols),
        with: [u_, m_, pn__, p_, x_],
        optional: [m_, p_],
        x_free: [m_, p_],
        when: {
            freeq!([m_, p_], x_)
                && rubi_linear_q(&u_, x_)
                && rubi_poly_q(&pn__, x_)
                && rubi_coeff(&u_, x_, 0).is_some_and(|coefficient| neq!(coefficient, 0))
                && {
                    let u0 = rubi_coeff(&u_, x_, 0).unwrap();
                    let u1 = rubi_coeff(&u_, x_, 1).unwrap();
                    let px = rubi_replace_all(&pn__, x_, (x_ - u0) / u1);
                    rubi_trinomial_q(&px, x_)
                }
        },
        rhs: {
            let u0 = rubi_coeff(&u_, x_, 0).unwrap();
            let u1 = rubi_coeff(&u_, x_, 1).unwrap();
            let px = rubi_replace_all(&pn__, x_, (x_ - u0) / &u1);
            let primitive = rubi_rhs_int(
                &(x_.pow(&m_) * rubi_expand_to_sum(&px, x_).pow(&p_)),
                x_,
            );
            rubi_star(Atom::num(1) / u1, rubi_subst(&primitive, x_, u_))
        },
    ));
}

fn push_rules_rule_2528(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, u__, x_);
    rules.push(rubi_rule!(
        order: 2528,
        source: "Int[u_/(e_.*Sqrt[a_.+b_.*x_]+f_.*Sqrt[c_.+d_.*x_]),x_Symbol] :=
          c/(e*(b*c-a*d)) \\[Star] Int[(u*Sqrt[a+b*x])/x,x] - a/(f*(b*c-a*d)) \\[Star] Int[(u*Sqrt[c+d*x])/x,x] /;
        FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d,0] && EqQ[a*e^2-c*f^2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_12(symbols),
        with: [u__, e__, a__, b__, f__, c__, d__, x_],
        optional: [e__, a__, b__, f__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(&a__ * e__.pow(2) - &c__ * f__.pow(2), 0)
        },
        rhs: {
            let determinant = &b__ * &c__ - &a__ * &d__;
            let first_denominator = &e__ * &determinant;
            let second_denominator = &f__ * &determinant;

            let first_integrand = &u__ * (&a__ + &b__ * x_).sqrt() / x_;
            let second_integrand = &u__ * (&c__ + &d__ * x_).sqrt() / x_;

            rubi_star(c__, rubi_rhs_int(&first_integrand, x_) / first_denominator) - rubi_star(a__, rubi_rhs_int(&second_integrand, x_) / second_denominator)
        },
    ));
}

fn push_rules_rule_2529(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, u__, x_);
    rules.push(rubi_rule!(
        order: 2529,
        source: "Int[u_/(e_.*Sqrt[a_.+b_.*x_]+f_.*Sqrt[c_.+d_.*x_]),x_Symbol] :=
          -d/(e*(b*c-a*d)) \\[Star] Int[u*Sqrt[a+b*x],x] + b/(f*(b*c-a*d)) \\[Star] Int[u*Sqrt[c+d*x],x] /;
        FreeQ[{a,b,c,d,e,f},x] && NeQ[b*c-a*d,0] && EqQ[b*e^2-d*f^2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_12(symbols),
        with: [u__, e__, a__, b__, f__, c__, d__, x_],
        optional: [e__, a__, b__, f__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(&b__ * e__.pow(2) - &d__ * f__.pow(2), 0)
        },
        rhs: {
            let determinant = &b__ * &c__ - &a__ * &d__;
            let first_denominator = &e__ * &determinant;
            let second_denominator = &f__ * &determinant;

            let first_integrand = &u__ * (&a__ + &b__ * x_).sqrt();
            let second_integrand = &u__ * (&c__ + &d__ * x_).sqrt();

            rubi_star(-&d__, rubi_rhs_int(&first_integrand, x_) / first_denominator) + rubi_star(b__, rubi_rhs_int(&second_integrand, x_) / second_denominator)
        },
    ));
}

fn push_rules_rule_2530(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, u__, x_);
    rules.push(rubi_rule!(
        order: 2530,
        source: "Int[u_/(e_.*Sqrt[a_.+b_.*x_]+f_.*Sqrt[c_.+d_.*x_]),x_Symbol] :=
          e \\[Star] Int[(u*Sqrt[a+b*x])/(a*e^2-c*f^2+(b*e^2-d*f^2)*x),x] -
          f \\[Star] Int[(u*Sqrt[c+d*x])/(a*e^2-c*f^2+(b*e^2-d*f^2)*x),x] /;
        FreeQ[{a,b,c,d,e,f},x] && NeQ[a*e^2-c*f^2,0] && NeQ[b*e^2-d*f^2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_12(symbols),
        with: [u__, e__, a__, b__, f__, c__, d__, x_],
        optional: [e__, a__, b__, f__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && neq!(&a__ * e__.pow(2) - &c__ * f__.pow(2), 0)
                && neq!(&b__ * e__.pow(2) - &d__ * f__.pow(2), 0)
        },
        rhs: {
            let denominator =
                &a__ * e__.pow(2) - &c__ * f__.pow(2) + (&b__ * e__.pow(2) - &d__ * f__.pow(2)) * x_;
            let first_integrand = &u__ * (&a__ + &b__ * x_).sqrt() / &denominator;
            let second_integrand = &u__ * (&c__ + &d__ * x_).sqrt() / denominator;

            rubi_star(e__, rubi_rhs_int(&first_integrand, x_))
                    - rubi_star(f__, rubi_rhs_int(&second_integrand, x_))
        },
    ));
}

fn push_rules_rule_2531(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, n_, p_, u__, x_);
    rules.push(rubi_rule!(
        order: 2531,
        source: "Int[u_./(d_.*x_^n_.+c_.*Sqrt[a_.+b_.*x_^p_.]),x_Symbol] :=
          -b/(a*d) \\[Star] Int[u*x^n,x] + 1/(a*c) \\[Star] Int[u*Sqrt[a+b*x^(2*n)],x] /;
        FreeQ[{a,b,c,d,n},x] && EqQ[p,2*n] && EqQ[b*c^2-d^2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: u__ / (d__ * x_.pow(n_) + c__ * (a__ + b__ * x_.pow(p_)).sqrt()),
        with: [u__, d__, n_, c__, a__, b__, p_, x_],
        optional: [u__, d__, n_, c__, a__, b__, p_],
        when: {
            freeq!([a__, b__, c__, d__, n_], x_)
                && eqq!(p_, Atom::num(2) * &n_)
                && eqq!(&b__ * c__.pow(2) - d__.pow(2), 0)
        },
        rhs: {
            let first_denominator = &a__ * &d__;
            let second_denominator = &a__ * &c__;

            let first_integrand = &u__ * x_.pow(&n_);
            let second_integrand = &u__ * (&a__ + &b__ * x_.pow(Atom::num(2) * &n_)).sqrt();

            rubi_star(-&b__, rubi_rhs_int(&first_integrand, x_) / first_denominator) + rubi_star(Atom::num(1) / second_denominator, rubi_rhs_int(&second_integrand, x_))
        },
    ));
}

fn push_rules_rule_2532(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 2532,
        source: "Int[x_^m_./(d_.*x_^n_.+c_.*Sqrt[a_.+b_.*x_^p_.]),x_Symbol] :=
          -d \\[Star] Int[x^(m+n)/(a*c^2+(b*c^2-d^2)*x^(2*n)),x] +
          c \\[Star] Int[(x^m*Sqrt[a+b*x^(2*n)])/(a*c^2+(b*c^2-d^2)*x^(2*n)),x] /;
        FreeQ[{a,b,c,d,m,n},x] && EqQ[p,2*n] && NeQ[b*c^2-d^2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: x_.pow(m_) / (d__ * x_.pow(n_) + c__ * (a__ + b__ * x_.pow(p_)).sqrt()),
        with: [m_, d__, n_, c__, a__, b__, p_, x_],
        optional: [m_, d__, n_, c__, a__, b__, p_],
        when: {
            freeq!([a__, b__, c__, d__, m_, n_], x_)
                && eqq!(p_, Atom::num(2) * &n_)
                && neq!(&b__ * c__.pow(2) - d__.pow(2), 0)
        },
        rhs: {
            let denominator =
                &a__ * c__.pow(2) + (&b__ * c__.pow(2) - d__.pow(2)) * x_.pow(Atom::num(2) * &n_);
            let first_integrand = x_.pow(&m_ + &n_) / &denominator;
            let second_integrand = x_.pow(&m_)
                * (&a__ + &b__ * x_.pow(Atom::num(2) * &n_)).sqrt()
                / denominator;

            rubi_star(-&d__, rubi_rhs_int(&first_integrand, x_))
                    + rubi_star(c__, rubi_rhs_int(&second_integrand, x_))
        },
    ));
}

fn push_rules_rule_2533(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 2533,
        source: "Int[1/((a_+b_.*x_^3)*Sqrt[d_.+e_.*x_+f_.*x_^2]),x_Symbol] :=
          With[{r=Numerator[Rt[a/b,3]], s=Denominator[Rt[a/b,3]]},
          r/(3*a) \\[Star] Int[1/((r+s*x)*Sqrt[d+e*x+f*x^2]),x] +
          r/(3*a) \\[Star] Int[(2*r-s*x)/((r^2-r*s*x+s^2*x^2)*Sqrt[d+e*x+f*x^2]),x]] /;
        FreeQ[{a,b,d,e,f},x] && PosQ[a/b]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [a__, b__, d__, e__, f__, x_],
        optional: [b__, d__, e__, f__],
        when: {
            freeq!([a__, b__, d__, e__, f__], x_)
                && posq!(&a__ / &b__)
        },
        rhs: {
            let rt = rubi_rt(&(&a__ / &b__), 3);
            let r = rubi_numerator(&rt);
            let s = rubi_denominator_atom(&rt);
            let coefficient_denominator = Atom::num(3) * &a__;

            let sqrt = (&d__ + &e__ * x_ + &f__ * x_.pow(2)).sqrt();
            let first_integrand =
                Atom::num(1) / ((&r + &s * x_) * &sqrt);
            let second_integrand = (Atom::num(2) * &r - &s * x_)
                / ((r.pow(2) - &r * &s * x_ + s.pow(2) * x_.pow(2)) * sqrt);

            rubi_star(&r, rubi_rhs_int(&first_integrand, x_) / &coefficient_denominator) + rubi_star(r, rubi_rhs_int(&second_integrand, x_) / coefficient_denominator)
        },
    ));
}

fn push_rules_rule_2534(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, f__, x_);
    rules.push(rubi_rule!(
        order: 2534,
        source: "Int[1/((a_+b_.*x_^3)*Sqrt[d_.+f_.*x_^2]),x_Symbol] :=
          With[{r=Numerator[Rt[a/b,3]], s=Denominator[Rt[a/b,3]]},
          r/(3*a) \\[Star] Int[1/((r+s*x)*Sqrt[d+f*x^2]),x] +
          r/(3*a) \\[Star] Int[(2*r-s*x)/((r^2-r*s*x+s^2*x^2)*Sqrt[d+f*x^2]),x]] /;
        FreeQ[{a,b,d,f},x] && PosQ[a/b]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [a__, b__, d__, f__, x_],
        optional: [b__, d__, f__],
        when: {
            freeq!([a__, b__, d__, f__], x_)
                && posq!(&a__ / &b__)
        },
        rhs: {
            let rt = rubi_rt(&(&a__ / &b__), 3);
            let r = rubi_numerator(&rt);
            let s = rubi_denominator_atom(&rt);
            let coefficient_denominator = Atom::num(3) * &a__;

            let sqrt = (&d__ + &f__ * x_.pow(2)).sqrt();
            let first_integrand =
                Atom::num(1) / ((&r + &s * x_) * &sqrt);
            let second_integrand = (Atom::num(2) * &r - &s * x_)
                / ((r.pow(2) - &r * &s * x_ + s.pow(2) * x_.pow(2)) * sqrt);

            rubi_star(&r, rubi_rhs_int(&first_integrand, x_) / &coefficient_denominator) + rubi_star(r, rubi_rhs_int(&second_integrand, x_) / coefficient_denominator)
        },
    ));
}

fn push_rules_rule_2535(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 2535,
        source: "Int[1/((a_+b_.*x_^3)*Sqrt[d_.+e_.*x_+f_.*x_^2]),x_Symbol] :=
          With[{r=Numerator[Rt[-a/b,3]], s=Denominator[Rt[-a/b,3]]},
          r/(3*a) \\[Star] Int[1/((r-s*x)*Sqrt[d+e*x+f*x^2]),x] +
          r/(3*a) \\[Star] Int[(2*r+s*x)/((r^2+r*s*x+s^2*x^2)*Sqrt[d+e*x+f*x^2]),x]] /;
        FreeQ[{a,b,d,e,f},x] && NegQ[a/b]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [a__, b__, d__, e__, f__, x_],
        optional: [b__, d__, e__, f__],
        when: {
            freeq!([a__, b__, d__, e__, f__], x_)
                && negq!(&a__ / &b__)
        },
        rhs: {
            let rt = rubi_rt(&(-&a__ / &b__), 3);
            let r = rubi_numerator(&rt);
            let s = rubi_denominator_atom(&rt);
            let coefficient_denominator = Atom::num(3) * &a__;

            let sqrt = (&d__ + &e__ * x_ + &f__ * x_.pow(2)).sqrt();
            let first_integrand =
                Atom::num(1) / ((&r - &s * x_) * &sqrt);
            let second_integrand = (Atom::num(2) * &r + &s * x_)
                / ((r.pow(2) + &r * &s * x_ + s.pow(2) * x_.pow(2)) * sqrt);

            rubi_star(&r, rubi_rhs_int(&first_integrand, x_) / &coefficient_denominator) + rubi_star(r, rubi_rhs_int(&second_integrand, x_) / coefficient_denominator)
        },
    ));
}

fn push_rules_rule_2536(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, d__, f__, x_);
    rules.push(rubi_rule!(
        order: 2536,
        source: "Int[1/((a_+b_.*x_^3)*Sqrt[d_.+f_.*x_^2]),x_Symbol] :=
          With[{r=Numerator[Rt[-a/b,3]], s=Denominator[Rt[-a/b,3]]},
          r/(3*a) \\[Star] Int[1/((r-s*x)*Sqrt[d+f*x^2]),x] +
          r/(3*a) \\[Star] Int[(2*r+s*x)/((r^2+r*s*x+s^2*x^2)*Sqrt[d+f*x^2]),x]] /;
        FreeQ[{a,b,d,f},x] && NegQ[a/b]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [a__, b__, d__, f__, x_],
        optional: [b__, d__, f__],
        when: {
            freeq!([a__, b__, d__, f__], x_)
                && negq!(&a__ / &b__)
        },
        rhs: {
            let rt = rubi_rt(&(-&a__ / &b__), 3);
            let r = rubi_numerator(&rt);
            let s = rubi_denominator_atom(&rt);
            let coefficient_denominator = Atom::num(3) * &a__;

            let sqrt = (&d__ + &f__ * x_.pow(2)).sqrt();
            let first_integrand =
                Atom::num(1) / ((&r - &s * x_) * &sqrt);
            let second_integrand = (Atom::num(2) * &r + &s * x_)
                / ((r.pow(2) + &r * &s * x_ + s.pow(2) * x_.pow(2)) * sqrt);

            rubi_star(&r, rubi_rhs_int(&first_integrand, x_) / &coefficient_denominator) + rubi_star(r, rubi_rhs_int(&second_integrand, x_) / coefficient_denominator)
        },
    ));
}

fn push_rules_rule_2537(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_a__, capital_b__, u__, v_, x_);
    rules.push(rubi_rule!(
        order: 2537,
        source: "Int[u_*(A_+B_.*x_^4)/Sqrt[v_],x_Symbol] :=
          With[{a=Coeff[v,x,0],b=Coeff[v,x,2],c=Coeff[v,x,4],d=Coeff[1/u,x,0],e=Coeff[1/u,x,2],f=Coeff[1/u,x,4]},
          A \\[Star] Subst[Int[1/(d-(b*d-a*e)*x^2),x],x,x/Sqrt[v]] /;
         EqQ[a*B+A*c,0] && EqQ[c*d-a*f,0]] /;
        FreeQ[{A,B},x] && PolyQ[v,x^2,2] && PolyQ[1/u,x^2,2]",
        desc: "Integration by substitution",
        refs: [],
        pattern: u__ * (capital_a__ + capital_b__ * x_.pow(4))
            / v_.pow(Atom::num(1) / Atom::num(2)),
        with: [u__, capital_a__, capital_b__, v_, x_],
        optional: [capital_b__],
        when: {
            freeq!([capital_a__, capital_b__], x_)
                && rubi_poly_q_power_degree(&v_, x_, &Atom::num(2), 2)
                && rubi_poly_q_power_degree(
                    &(Atom::num(1) / &u__),
                    x_,
                    &Atom::num(2),
                    2,
                )
                && {
                    let reciprocal_u = Atom::num(1) / &u__;
                    let a = rubi_coeff(&v_, x_, 0).unwrap();
                    let c = rubi_coeff(&v_, x_, 4).unwrap();
                    let d = rubi_coeff(&reciprocal_u, x_, 0).unwrap();
                    let f = rubi_coeff(&reciprocal_u, x_, 4).unwrap();
                    eqq!(&a * &capital_b__ + &capital_a__ * &c, 0)
                        && eqq!(&c * &d - &a * &f, 0)
                }
        },
        rhs: {
            let reciprocal_u = Atom::num(1) / &u__;
            let a = rubi_coeff(&v_, x_, 0).unwrap();
            let b = rubi_coeff(&v_, x_, 2).unwrap();
            let d = rubi_coeff(&reciprocal_u, x_, 0).unwrap();
            let e = rubi_coeff(&reciprocal_u, x_, 2).unwrap();
            let sqrt_v = v_.sqrt();

            let transformed = rubi_rhs_int(
                &(Atom::num(1) / (&d - (&b * &d - &a * &e) * x_.pow(2))),
                x_,
            );

            rubi_star(capital_a__, rubi_subst(&transformed, x_, x_ / sqrt_v))
        },
    ));
}

fn push_rules_rule_2538(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 2538,
        source: "Int[1/((a_+b_.*x_)*Sqrt[c_+d_.*x_^2]*Sqrt[e_+f_.*x_^2]),x_Symbol] :=
          a \\[Star] Int[1/((a^2-b^2*x^2)*Sqrt[c+d*x^2]*Sqrt[e+f*x^2]),x] - b \\[Star] Int[x/((a^2-b^2*x^2)*Sqrt[c+d*x^2]*Sqrt[e+f*x^2]),x] /;
        FreeQ[{a,b,c,d,e,f},x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: Atom::num(1)
            / ((a__ + b__ * x_)
                * (c__ + d__ * x_.pow(2)).sqrt()
                * (e__ + f__ * x_.pow(2)).sqrt()),
        with: [a__, b__, c__, d__, e__, f__, x_],
        optional: [b__, d__, f__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
        },
        rhs: {
            let denominator = (a__.pow(2) - b__.pow(2) * x_.pow(2))
                * (&c__ + &d__ * x_.pow(2)).sqrt()
                * (&e__ + &f__ * x_.pow(2)).sqrt();
            let first_integrand = Atom::num(1) / &denominator;
            let second_integrand = x_ / denominator;

            rubi_star(a__, rubi_rhs_int(&first_integrand, x_))
                    - rubi_star(b__, rubi_rhs_int(&second_integrand, x_))
        },
    ));
}

fn push_rules_rule_2539(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, h__, x_);
    rules.push(rubi_rule!(
        order: 2539,
        source: "Int[(g_.+h_.*x_)*Sqrt[d_.+e_.*x_+f_.*Sqrt[a_.+b_.*x_+c_.*x_^2]],x_Symbol] :=
          2*(f*(5*b*c*g^2-2*b^2*g*h-3*a*c*g*h+2*a*b*h^2)+c*f*(10*c*g^2-b*g*h+a*h^2)*x+9*c^2*f*g*h*x^2+3*c^2*f*h^2*x^3-
            (e*g-d*h)*(5*c*g-2*b*h+c*h*x)*Sqrt[a+b*x+c*x^2])/
          (15*c^2*f*(g+h*x))*Sqrt[d+e*x+f*Sqrt[a+b*x+c*x^2]] /;
        FreeQ[{a,b,c,d,e,f,g,h},x] && EqQ[(e*g-d*h)^2-f^2*(c*g^2-b*g*h+a*h^2),0] && EqQ[2*e^2*g-2*d*e*h-f^2*(2*c*g-b*h),0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (g__ + h__ * x_)
            * (d__ + e__ * x_ + f__ * (a__ + b__ * x_ + c__ * x_.pow(2)).sqrt()).sqrt(),
        with: [g__, h__, d__, e__, f__, a__, b__, c__, x_],
        optional: [g__, h__, d__, e__, f__, a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__], x_)
                && eqq!(
                    (&e__ * &g__ - &d__ * &h__).pow(2)
                        - f__.pow(2) * (&c__ * g__.pow(2) - &b__ * &g__ * &h__ + &a__ * h__.pow(2)),
                    0
                )
                && eqq!(
                    Atom::num(2) * e__.pow(2) * &g__
                        - Atom::num(2) * &d__ * &e__ * &h__
                        - f__.pow(2) * (Atom::num(2) * &c__ * &g__ - &b__ * &h__),
                    0
                )
        },
        rhs: {
            let denominator = Atom::num(15) * c__.pow(2) * &f__ * (&g__ + &h__ * x_);

            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let numerator = Atom::num(2)
                * (&f__
                    * (Atom::num(5) * &b__ * &c__ * g__.pow(2)
                        - Atom::num(2) * b__.pow(2) * &g__ * &h__
                        - Atom::num(3) * &a__ * &c__ * &g__ * &h__
                        + Atom::num(2) * &a__ * &b__ * h__.pow(2))
                    + &c__
                        * &f__
                        * (Atom::num(10) * &c__ * g__.pow(2) - &b__ * &g__ * &h__ + &a__ * h__.pow(2))
                        * x_
                    + Atom::num(9) * c__.pow(2) * &f__ * &g__ * &h__ * x_.pow(2)
                    + Atom::num(3) * c__.pow(2) * &f__ * h__.pow(2) * x_.pow(3)
                    - (&e__ * &g__ - &d__ * &h__)
                        * (Atom::num(5) * &c__ * &g__ - Atom::num(2) * &b__ * &h__
                            + &c__ * &h__ * x_)
                        * quadratic.sqrt());
            let nested = (&d__ + &e__ * x_ + &f__ * quadratic.sqrt()).sqrt();

            rubi_simp(&(numerator * nested / denominator), x_)
        },
    ));
}

fn push_rules_rule_2540(rules: &mut Vec<RubiRule>) {
    rubi_symb!(f__, g__, h__, j__, k__, m_, n_, u__, v_, x_);
    rules.push(rubi_rule!(
        order: 2540,
        source: "Int[(g_.+h_.*x_)^m_.*(u_+f_.*(j_.+k_.*Sqrt[v_]))^n_.,x_Symbol] :=
          Int[(g+h*x)^m*(ExpandToSum[u+f*j,x]+f*k*Sqrt[ExpandToSum[v,x]])^n,x] /;
        FreeQ[{f,g,h,j,k,m,n},x] && LinearQ[u,x] && QuadraticQ[v,x] &&
          Not[LinearMatchQ[u,x] && QuadraticMatchQ[v,x] && (EqQ[j,0] || EqQ[f,1])] &&
          EqQ[(Coefficient[u,x,1]*g-h*(Coefficient[u,x,0]+f*j))^2-f^2*k^2*(Coefficient[v,x,2]*g^2-Coefficient[v,x,1]*g*h+Coefficient[v,x,0]*h^2),0]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: (g__ + h__ * x_).pow(m_)
            * (u__ + f__ * (j__ + k__ * v_.pow(Atom::num(1) / Atom::num(2)))).pow(n_),
        with: [g__, h__, m_, u__, f__, j__, k__, v_, n_, x_],
        optional: [g__, h__, m_, f__, j__, k__, n_],
        when: {
            freeq!([f__, g__, h__, j__, k__, m_, n_], x_)
                && rubi_linear_q(&u__, x_)
                && rubi_quadratic_q(&v_, x_)
                && !(rubi_linear_match_q(&u__, x_)
                    && rubi_quadratic_match_q(&v_, x_)
                    && (eqq!(j__, 0) || eqq!(f__, 1)))
                && {
                    let u0 = rubi_coefficient(&u__, x_, 0).unwrap();
                    let u1 = rubi_coefficient(&u__, x_, 1).unwrap();
                    let v0 = rubi_coefficient(&v_, x_, 0).unwrap();
                    let v1 = rubi_coefficient(&v_, x_, 1).unwrap();
                    let v2 = rubi_coefficient(&v_, x_, 2).unwrap();
                    eqq!(
                        (&u1 * &g__ - &h__ * (&u0 + &f__ * &j__)).pow(2)
                            - f__.pow(2)
                                * k__.pow(2)
                                * (&v2 * g__.pow(2) - &v1 * &g__ * &h__ + &v0 * h__.pow(2)),
                        0
                    )
                }
        },
        rhs: {
            let transformed_integrand = (&g__ + &h__ * x_).pow(&m_)
                * (rubi_expand_to_sum(&(&u__ + &f__ * &j__), x_)
                    + &f__ * &k__ * rubi_expand_to_sum(&v_, x_).sqrt())
                .pow(&n_);

            rubi_rhs_int(&transformed_integrand, x_)
        },
    ));
}

fn push_rules_rule_2541(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, h__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 2541,
        source: "Int[(g_.+h_.*(d_.+e_.*x_+f_.*Sqrt[a_.+b_.*x_+c_.*x_^2])^n_)^p_.,x_Symbol] :=
          2 \\[Star] Subst[Int[(g+h*x^n)^p*(d^2*e-(b*d-a*e)*f^2-(2*d*e-b*f^2)*x+e*x^2)/(-2*d*e+b*f^2+2*e*x)^2,x],x,d+e*x+f*Sqrt[a+b*x+c*x^2]] /;
        FreeQ[{a,b,c,d,e,f,g,h,n},x] && EqQ[e^2-c*f^2,0] && IntegerQ[p]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (g__ + h__ * (d__ + e__ * x_ + f__ * (a__ + b__ * x_ + c__ * x_.pow(2)).sqrt()).pow(n_)).pow(p_),
        with: [g__, h__, d__, e__, f__, a__, b__, c__, n_, p_, x_],
        optional: [g__, h__, d__, e__, f__, a__, b__, c__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__, n_], x_)
                && eqq!(e__.pow(2) - &c__ * f__.pow(2), 0)
                && integerq!(p_)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_denominator =
                (-Atom::num(2) * &d__ * &e__ + &b__ * f__.pow(2) + Atom::num(2) * &e__ * &sub_atom).pow(2);

            let transformed_integrand = (&g__ + &h__ * sub_atom.pow(&n_)).pow(&p_)
                * (d__.pow(2) * &e__
                    - (&b__ * &d__ - &a__ * &e__) * f__.pow(2)
                    - (Atom::num(2) * &d__ * &e__ - &b__ * f__.pow(2)) * &sub_atom
                    + &e__ * sub_atom.pow(2))
                / transformed_denominator;
            let transformed = rubi_rhs_int(&transformed_integrand, sub);
            let replacement =
                &d__ + &e__ * x_ + &f__ * (&a__ + &b__ * x_ + &c__ * x_.pow(2)).sqrt();

            rubi_star(Atom::num(2), rubi_subst(&transformed, sub, replacement))
        },
    ));
}

fn push_rules_rule_2542(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, c__, d__, e__, f__, g__, h__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 2542,
        source: "Int[(g_.+h_.*(d_.+e_.*x_+f_.*Sqrt[a_+c_.*x_^2])^n_)^p_.,x_Symbol] :=
          1/(2*e) \\[Star] Subst[Int[(g+h*x^n)^p*(d^2+a*f^2-2*d*x+x^2)/(d-x)^2,x],x,d+e*x+f*Sqrt[a+c*x^2]] /;
        FreeQ[{a,c,d,e,f,g,h,n},x] && EqQ[e^2-c*f^2,0] && IntegerQ[p]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (g__ + h__ * (d__ + e__ * x_ + f__ * (a__ + c__ * x_.pow(2)).sqrt()).pow(n_)).pow(p_),
        with: [g__, h__, d__, e__, f__, a__, c__, n_, p_, x_],
        optional: [g__, h__, d__, e__, f__, c__, p_],
        when: {
            freeq!([a__, c__, d__, e__, f__, g__, h__, n_], x_)
                && eqq!(e__.pow(2) - &c__ * f__.pow(2), 0)
                && integerq!(p_)
        },
        rhs: {
            let coefficient_denominator = Atom::num(2) * &e__;
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_denominator = (&d__ - &sub_atom).pow(2);

            let transformed_integrand = (&g__ + &h__ * sub_atom.pow(&n_)).pow(&p_)
                * (d__.pow(2) + &a__ * f__.pow(2) - Atom::num(2) * &d__ * &sub_atom + sub_atom.pow(2))
                / transformed_denominator;
            let transformed = rubi_rhs_int(&transformed_integrand, sub);
            let replacement = &d__ + &e__ * x_ + &f__ * (&a__ + &c__ * x_.pow(2)).sqrt();

            rubi_star(Atom::num(1) / coefficient_denominator, rubi_subst(&transformed, sub, replacement))
        },
    ));
}

fn push_rules_rule_2543(rules: &mut Vec<RubiRule>) {
    rubi_symb!(f__, g__, h__, n_, p_, u__, v_);
    rules.push(rubi_rule!(
        order: 2543,
        source: "Int[(g_.+h_.*(u_+f_. Sqrt[v_])^n_)^p_.,x_Symbol] :=
          Int[(g+h*(ExpandToSum[u,x]+f*Sqrt[ExpandToSum[v,x]])^n)^p,x] /;
        FreeQ[{f,g,h,n},x] && LinearQ[u,x] && QuadraticQ[v,x] && Not[LinearMatchQ[u,x] && QuadraticMatchQ[v,x]] &&
          EqQ[Coefficient[u,x,1]^2-Coefficient[v,x,2]*f^2,0] && IntegerQ[p]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern: (g__ + h__ * (u__ + f__ * v_.pow(Atom::num(1) / Atom::num(2))).pow(n_)).pow(p_),
        with: [g__, h__, u__, f__, v_, n_, p_, x_],
        optional: [g__, h__, f__, p_],
        when: {
            freeq!([f__, g__, h__, n_], x_)
                && rubi_linear_q(&u__, x_)
                && rubi_quadratic_q(&v_, x_)
                && !(rubi_linear_match_q(&u__, x_) && rubi_quadratic_match_q(&v_, x_))
                && eqq!(
                    rubi_coefficient(&u__, x_, 1).unwrap().pow(2)
                        - rubi_coefficient(&v_, x_, 2).unwrap() * f__.pow(2),
                    0
                )
                && integerq!(p_)
        },
        rhs: {
            let transformed_integrand = (&g__
                + &h__ * (rubi_expand_to_sum(&u__, x_) + &f__ * rubi_expand_to_sum(&v_, x_).sqrt()).pow(&n_))
            .pow(&p_);

            rubi_rhs_int(&transformed_integrand, x_)
        },
    ));
}

fn push_rules_rule_2544(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, c__, e__, f__, g__, h__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 2544,
        source: "Int[(g_.+h_.*x_)^m_.*(e_.*x_+f_.*Sqrt[a_.+c_.*x_^2])^n_.,x_Symbol] :=
          1/(2^(m+1)*e^(m+1)) \\[Star] Subst[Int[x^(n-m-2)*(a*f^2+x^2)*(-a*f^2*h+2*e*g*x+h*x^2)^m,x],x,e*x+f*Sqrt[a+c*x^2]] /;
        FreeQ[{a,c,e,f,g,h,n},x] && EqQ[e^2-c*f^2,0] && IntegerQ[m]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (g__ + h__ * x_).pow(m_) * (e__ * x_ + f__ * (a__ + c__ * x_.pow(2)).sqrt()).pow(n_),
        with: [g__, h__, m_, e__, f__, a__, c__, n_, x_],
        optional: [g__, h__, m_, e__, f__, a__, c__, n_],
        when: {
            freeq!([a__, c__, e__, f__, g__, h__, n_], x_)
                && eqq!(e__.pow(2) - &c__ * f__.pow(2), 0)
                && integerq!(m_)
        },
        rhs: {
            let m_plus_1 = &m_ + 1;
            let coefficient_denominator = Atom::num(2).pow(&m_plus_1) * e__.pow(&m_plus_1);

            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = sub_atom.pow((&n_ - &m_ - 2).expand())
                * (&a__ * f__.pow(2) + sub_atom.pow(2))
                * (-&a__ * f__.pow(2) * &h__ + Atom::num(2) * &e__ * &g__ * &sub_atom + &h__ * sub_atom.pow(2)).pow(&m_);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);
            let replacement = &e__ * x_ + &f__ * (&a__ + &c__ * x_.pow(2)).sqrt();

            rubi_star(Atom::num(1) / coefficient_denominator, rubi_subst(&transformed, sub, replacement))
        },
    ));
}

fn push_rules_rule_2545(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, c__, e__, f__, g__, i__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 2545,
        source: "Int[x_^p_.*(g_+i_.*x_^2)^m_.*(e_.*x_+f_.*Sqrt[a_+c_.*x_^2])^n_.,x_Symbol] :=
          1/(2^(2*m+p+1)*e^(p+1)*f^(2*m))*(i/c)^m \\[Star] Subst[Int[x^(n-2*m-p-2)*(-a*f^2+x^2)^p*(a*f^2+x^2)^(2*m+1),x],x,e*x+f*Sqrt[a+c*x^2]] /;
        FreeQ[{a,c,e,f,g,i,n},x] && EqQ[e^2-c*f^2,0] && EqQ[c*g-a*i,0] && IntegersQ[p,2*m] && (IntegerQ[m] || GtQ[i/c,0])",
        desc: "Integration by substitution",
        refs: [],
        pattern: x_.pow(p_) * (g__ + i__ * x_.pow(2)).pow(m_) * (e__ * x_ + f__ * (a__ + c__ * x_.pow(2)).sqrt()).pow(n_),
        with: [p_, g__, i__, m_, e__, f__, a__, c__, n_, x_],
        optional: [p_, i__, e__, f__, c__, n_, m_],
        when: {
            freeq!([a__, c__, e__, f__, g__, i__, n_], x_)
                && eqq!(e__.pow(2) - &c__ * f__.pow(2), 0)
                && eqq!(&c__ * &g__ - &a__ * &i__, 0)
                && integersq!([p_, Atom::num(2) * &m_])
                && (integerq!(m_) || gtq!(&i__ / &c__, 0))
        },
        rhs: {
            let coefficient_denominator =
                Atom::num(2).pow((Atom::num(2) * &m_ + &p_ + 1).expand()) * e__.pow(&p_ + 1) * f__.pow(Atom::num(2) * &m_);

            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = sub_atom.pow((&n_ - Atom::num(2) * &m_ - &p_ - 2).expand())
                * (-&a__ * f__.pow(2) + sub_atom.pow(2)).pow(&p_)
                * (&a__ * f__.pow(2) + sub_atom.pow(2)).pow(Atom::num(2) * &m_ + 1);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);
            let replacement = &e__ * x_ + &f__ * (&a__ + &c__ * x_.pow(2)).sqrt();

            rubi_star((&i__ / &c__).pow(&m_), rubi_subst(&transformed, sub, replacement)
                    / coefficient_denominator)
        },
    ));
}

fn push_rules_rule_2546(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, h__, i__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 2546,
        source: "Int[(g_.+h_.*x_+i_.*x_^2)^m_.*(d_.+e_.*x_+f_.*Sqrt[a_.+b_.*x_+c_.*x_^2])^n_.,x_Symbol] :=
          2/f^(2*m)*(i/c)^m \\[Star]
            Subst[Int[x^n*(d^2*e-(b*d-a*e)*f^2-(2*d*e-b*f^2)*x+e*x^2)^(2*m+1)/(-2*d*e+b*f^2+2*e*x)^(2*(m+1)),x],x,d+e*x+f*Sqrt[a+b*x+c*x^2]] /;
        FreeQ[{a,b,c,d,e,f,g,h,i,n},x] && EqQ[e^2-c*f^2,0] && EqQ[c*g-a*i,0] && EqQ[c*h-b*i,0] && IntegerQ[2*m] && (IntegerQ[m] || GtQ[i/c,0])",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [g__, h__, i__, m_, d__, e__, f__, a__, b__, c__, n_, x_],
        optional: [g__, h__, i__, m_, d__, e__, f__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__, i__, n_], x_)
                && eqq!(e__.pow(2) - &c__ * f__.pow(2), 0)
                && eqq!(&c__ * &g__ - &a__ * &i__, 0)
                && eqq!(&c__ * &h__ - &b__ * &i__, 0)
                && integerq!(Atom::num(2) * &m_)
                && (integerq!(m_) || gtq!(&i__ / &c__, 0))
        },
        rhs: {
            let coefficient_denominator = f__.pow(Atom::num(2) * &m_);

            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_denominator_base =
                -Atom::num(2) * &d__ * &e__ + &b__ * f__.pow(2) + Atom::num(2) * &e__ * &sub_atom;
            let transformed_denominator = transformed_denominator_base.pow(Atom::num(2) * (&m_ + 1));

            let transformed_numerator = sub_atom.pow(&n_)
                * (d__.pow(2) * &e__
                    - (&b__ * &d__ - &a__ * &e__) * f__.pow(2)
                    - (Atom::num(2) * &d__ * &e__ - &b__ * f__.pow(2)) * &sub_atom
                    + &e__ * sub_atom.pow(2))
                .pow(Atom::num(2) * &m_ + 1);
            let transformed = rubi_rhs_int(&(transformed_numerator / transformed_denominator), sub);
            let replacement =
                &d__ + &e__ * x_ + &f__ * (&a__ + &b__ * x_ + &c__ * x_.pow(2)).sqrt();

            rubi_star(Atom::num(2) * (&i__ / &c__).pow(&m_) / coefficient_denominator, rubi_subst(&transformed, sub, replacement))
        },
    ));
}

fn push_rules_rule_2547(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, g__, i__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 2547,
        source: "Int[(g_+i_.*x_^2)^m_.*(d_.+e_.*x_+f_.*Sqrt[a_+c_.*x_^2])^n_.,x_Symbol] :=
          1/(2^(2*m+1)*e*f^(2*m))*(i/c)^m \\[Star]
            Subst[Int[x^n*(d^2+a*f^2-2*d*x+x^2)^(2*m+1)/(-d+x)^(2*(m+1)),x],x,d+e*x+f*Sqrt[a+c*x^2]] /;
        FreeQ[{a,c,d,e,f,g,i,n},x] && EqQ[e^2-c*f^2,0] && EqQ[c*g-a*i,0] && IntegerQ[2*m] && (IntegerQ[m] || GtQ[i/c,0])",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [g__, i__, m_, d__, e__, f__, a__, c__, n_, x_],
        optional: [i__, m_, d__, e__, f__, c__, n_],
        when: {
            freeq!([a__, c__, d__, e__, f__, g__, i__, n_], x_)
                && eqq!(e__.pow(2) - &c__ * f__.pow(2), 0)
                && eqq!(&c__ * &g__ - &a__ * &i__, 0)
                && integerq!(Atom::num(2) * &m_)
                && (integerq!(m_) || gtq!(&i__ / &c__, 0))
        },
        rhs: {
            let coefficient_denominator =
                Atom::num(2).pow((Atom::num(2) * &m_ + 1).expand()) * &e__ * f__.pow(Atom::num(2) * &m_);

            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_denominator = (-&d__ + &sub_atom).pow(Atom::num(2) * (&m_ + 1));

            let transformed_numerator = sub_atom.pow(&n_)
                * (d__.pow(2) + &a__ * f__.pow(2) - Atom::num(2) * &d__ * &sub_atom + sub_atom.pow(2))
                    .pow(Atom::num(2) * &m_ + 1);
            let transformed = rubi_rhs_int(&(transformed_numerator / transformed_denominator), sub);
            let replacement = &d__ + &e__ * x_ + &f__ * (&a__ + &c__ * x_.pow(2)).sqrt();

            rubi_star((&i__ / &c__).pow(&m_), rubi_subst(&transformed, sub, replacement)
                    / coefficient_denominator)
        },
    ));
}

fn push_rules_rule_2548(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, h__, i__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 2548,
        source: "Int[(g_.+h_.*x_+i_.*x_^2)^m_.*(d_.+e_.*x_+f_.*Sqrt[a_.+b_.*x_+c_.*x_^2])^n_.,x_Symbol] :=
          (i/c)^(m-1/2)*Sqrt[g+h*x+i*x^2]/Sqrt[a+b*x+c*x^2] \\[Star] Int[(a+b*x+c*x^2)^m*(d+e*x+f*Sqrt[a+b*x+c*x^2])^n,x] /;
        FreeQ[{a,b,c,d,e,f,g,h,i,n},x] && EqQ[e^2-c*f^2,0] && EqQ[c*g-a*i,0] && EqQ[c*h-b*i,0] && IGtQ[m+1/2,0] && Not[GtQ[i/c,0]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [g__, h__, i__, m_, d__, e__, f__, a__, b__, c__, n_, x_],
        optional: [g__, h__, i__, m_, d__, e__, f__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__, i__, n_], x_)
                && eqq!(e__.pow(2) - &c__ * f__.pow(2), 0)
                && eqq!(&c__ * &g__ - &a__ * &i__, 0)
                && eqq!(&c__ * &h__ - &b__ * &i__, 0)
                && igtq!(&m_ + Atom::num(1) / Atom::num(2), 0)
                && !gtq!(&i__ / &c__, 0)
        },
        rhs: {
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let quadratic_sqrt = quadratic.sqrt();

            let transformed_integrand =
                quadratic.pow(&m_) * (&d__ + &e__ * x_ + &f__ * quadratic.sqrt()).pow(&n_);

            rubi_star((&i__ / &c__).pow((&m_ - Atom::num(1) / Atom::num(2)).expand()) * (&g__ + &h__ * x_ + &i__ * x_.pow(2)).sqrt() / quadratic_sqrt, rubi_rhs_int(&transformed_integrand, x_))
        },
    ));
}

fn push_rules_rule_2549(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, g__, i__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 2549,
        source: "Int[(g_+i_.*x_^2)^m_.*(d_.+e_.*x_+f_.*Sqrt[a_+c_.*x_^2])^n_.,x_Symbol] :=
          (i/c)^(m-1/2)*Sqrt[g+i*x^2]/Sqrt[a+c*x^2] \\[Star] Int[(a+c*x^2)^m*(d+e*x+f*Sqrt[a+c*x^2])^n,x] /;
        FreeQ[{a,c,d,e,f,g,i,n},x] && EqQ[e^2-c*f^2,0] && EqQ[c*g-a*i,0] && IGtQ[m+1/2,0] && Not[GtQ[i/c,0]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [g__, i__, m_, d__, e__, f__, a__, c__, n_, x_],
        optional: [i__, m_, d__, e__, f__, c__, n_],
        when: {
            freeq!([a__, c__, d__, e__, f__, g__, i__, n_], x_)
                && eqq!(e__.pow(2) - &c__ * f__.pow(2), 0)
                && eqq!(&c__ * &g__ - &a__ * &i__, 0)
                && igtq!(&m_ + Atom::num(1) / Atom::num(2), 0)
                && !gtq!(&i__ / &c__, 0)
        },
        rhs: {
            let quadratic = &a__ + &c__ * x_.pow(2);
            let quadratic_sqrt = quadratic.sqrt();

            let transformed_integrand = quadratic.pow(&m_) * (&d__ + &e__ * x_ + &f__ * quadratic.sqrt()).pow(&n_);

            rubi_star((&i__ / &c__).pow((&m_ - Atom::num(1) / Atom::num(2)).expand()) * (&g__ + &i__ * x_.pow(2)).sqrt() / quadratic_sqrt, rubi_rhs_int(&transformed_integrand, x_))
        },
    ));
}

fn push_rules_rule_2550(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, h__, i__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 2550,
        source: "Int[(g_.+h_.*x_+i_.*x_^2)^m_.*(d_.+e_.*x_+f_.*Sqrt[a_.+b_.*x_+c_.*x_^2])^n_.,x_Symbol] :=
          (i/c)^(m+1/2)*Sqrt[a+b*x+c*x^2]/Sqrt[g+h*x+i*x^2] \\[Star] Int[(a+b*x+c*x^2)^m*(d+e*x+f*Sqrt[a+b*x+c*x^2])^n,x] /;
        FreeQ[{a,b,c,d,e,f,g,h,i,n},x] && EqQ[e^2-c*f^2,0] && EqQ[c*g-a*i,0] && EqQ[c*h-b*i,0] && ILtQ[m-1/2,0] && Not[GtQ[i/c,0]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [g__, h__, i__, m_, d__, e__, f__, a__, b__, c__, n_, x_],
        optional: [g__, h__, i__, m_, d__, e__, f__, a__, b__, c__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__, i__, n_], x_)
                && eqq!(e__.pow(2) - &c__ * f__.pow(2), 0)
                && eqq!(&c__ * &g__ - &a__ * &i__, 0)
                && eqq!(&c__ * &h__ - &b__ * &i__, 0)
                && iltq!(&m_ - Atom::num(1) / Atom::num(2), 0)
                && !gtq!(&i__ / &c__, 0)
        },
        rhs: {
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let transformed_integrand =
                quadratic.pow(&m_) * (&d__ + &e__ * x_ + &f__ * quadratic.sqrt()).pow(&n_);
            let denominator_sqrt = (&g__ + &h__ * x_ + &i__ * x_.pow(2)).sqrt();

            rubi_star((&i__ / &c__).pow((&m_ + Atom::num(1) / Atom::num(2)).expand()) * quadratic.sqrt() / denominator_sqrt, rubi_rhs_int(&transformed_integrand, x_))
        },
    ));
}

fn push_rules_rule_2551(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, g__, i__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 2551,
        source: "Int[(g_+i_.*x_^2)^m_.*(d_.+e_.*x_+f_.*Sqrt[a_+c_.*x_^2])^n_.,x_Symbol] :=
          (i/c)^(m+1/2)*Sqrt[a+c*x^2]/Sqrt[g+i*x^2] \\[Star] Int[(a+c*x^2)^m*(d+e*x+f*Sqrt[a+c*x^2])^n,x] /;
        FreeQ[{a,c,d,e,f,g,i,n},x] && EqQ[e^2-c*f^2,0] && EqQ[c*g-a*i,0] && ILtQ[m-1/2,0] && Not[GtQ[i/c,0]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [g__, i__, m_, d__, e__, f__, a__, c__, n_, x_],
        optional: [i__, m_, d__, e__, f__, c__, n_],
        when: {
            freeq!([a__, c__, d__, e__, f__, g__, i__, n_], x_)
                && eqq!(e__.pow(2) - &c__ * f__.pow(2), 0)
                && eqq!(&c__ * &g__ - &a__ * &i__, 0)
                && iltq!(&m_ - Atom::num(1) / Atom::num(2), 0)
                && !gtq!(&i__ / &c__, 0)
        },
        rhs: {
            let quadratic = &a__ + &c__ * x_.pow(2);
            let transformed_integrand = quadratic.pow(&m_) * (&d__ + &e__ * x_ + &f__ * quadratic.sqrt()).pow(&n_);
            let denominator_sqrt = (&g__ + &i__ * x_.pow(2)).sqrt();

            rubi_star((&i__ / &c__).pow((&m_ + Atom::num(1) / Atom::num(2)).expand()) * quadratic.sqrt() / denominator_sqrt, rubi_rhs_int(&transformed_integrand, x_))
        },
    ));
}

fn push_rules_rule_2552(rules: &mut Vec<RubiRule>) {
    rubi_symb!(f__, j__, k__, m_, n_, u__, v_, w_);
    rules.push(rubi_rule!(
        order: 2552,
        source: "Int[w_^m_.*(u_+f_.*(j_.+k_.*Sqrt[v_]))^n_.,x_Symbol] :=
          Int[ExpandToSum[w,x]^m*(ExpandToSum[u+f*j,x]+f*k*Sqrt[ExpandToSum[v,x]])^n,x] /;
        FreeQ[{f,j,k,m,n},x] && LinearQ[u,x] && QuadraticQ[{v,w},x] &&
          Not[LinearMatchQ[u,x] && QuadraticMatchQ[{v,w},x] && (EqQ[j,0] || EqQ[f,1])] &&
          EqQ[Coefficient[u,x,1]^2-Coefficient[v,x,2]*f^2*k^2,0]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: w_.pow(m_) * (u__ + f__ * (j__ + k__ * v_.pow(Atom::num(1) / Atom::num(2)))).pow(n_),
        with: [w_, m_, u__, f__, j__, k__, v_, n_, x_],
        optional: [m_, f__, j__, k__, n_],
        when: {
            freeq!([f__, j__, k__, m_, n_], x_)
                && rubi_linear_q(&u__, x_)
                && rubi_quadratic_q_list(&[&v_, &w_], x_)
                && !(rubi_linear_match_q(&u__, x_)
                    && rubi_quadratic_match_q_list(&[&v_, &w_], x_)
                    && (eqq!(j__, 0) || eqq!(f__, 1)))
                && eqq!(
                    rubi_coefficient(&u__, x_, 1).unwrap().pow(2)
                        - rubi_coefficient(&v_, x_, 2).unwrap()
                            * f__.pow(2)
                            * k__.pow(2),
                    0
                )
        },
        rhs: {
            let transformed_integrand = rubi_expand_to_sum(&w_, x_).pow(&m_)
                * (rubi_expand_to_sum(&(&u__ + &f__ * &j__), x_)
                    + &f__ * &k__ * rubi_expand_to_sum(&v_, x_).sqrt())
                .pow(&n_);

            rubi_rhs_int(&transformed_integrand, x_)
        },
    ));
}

fn push_rules_rule_2553(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 2553,
        source: "Int[1/((a_+b_.*x_^n_.)*Sqrt[c_.*x_^2+d_.*(a_+b_.*x_^n_.)^p_.]),x_Symbol] :=
          1/a \\[Star] Subst[Int[1/(1-c*x^2),x],x,x/Sqrt[c*x^2+d*(a+b*x^n)^(2/n)]] /;
        FreeQ[{a,b,c,d,n},x] && EqQ[p,2/n]",
        desc: "Integration by substitution",
        refs: ["Integration of FunctionsUnderline (1948) by A.F. Timofeev"],
        pattern: Atom::num(1)
            / ((a__ + b__ * x_.pow(n_))
                * (c__ * x_.pow(2) + d__ * (a__ + b__ * x_.pow(n_)).pow(p_)).sqrt()),
        with: [a__, b__, n_, c__, d__, p_, x_],
        optional: [b__, n_, c__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__, n_], x_)
                && eqq!(p_, Atom::num(2) / &n_)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_denominator = Atom::num(1) - &c__ * sub_atom.pow(2);

            let transformed = rubi_rhs_int(&(Atom::num(1) / transformed_denominator), sub);
            let substitution_denominator =
                (&c__ * x_.pow(2) + &d__ * (&a__ + &b__ * x_.pow(&n_)).pow(Atom::num(2) / &n_)).sqrt();

            rubi_star(Atom::num(1) / a__, rubi_subst(&transformed, sub, x_ / substitution_denominator))
        },
    ));
}

fn push_rules_rule_2554(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 2554,
        source: "Int[Sqrt[a_+b_.*Sqrt[c_+d_.*x_^2]],x_Symbol] :=
          2*b^2*d*x^3/(3*(a+b*Sqrt[c+d*x^2])^(3/2)) + 2*a*x/Sqrt[a+b*Sqrt[c+d*x^2]] /;
        FreeQ[{a,b,c,d},x] && EqQ[a^2-b^2*c,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (a__ + b__ * (c__ + d__ * x_.pow(2)).sqrt()).sqrt(),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_) && eqq!(a__.pow(2) - b__.pow(2) * &c__, 0)
        },
        rhs: {
            let nested = &a__ + &b__ * (&c__ + &d__ * x_.pow(2)).sqrt();
            let first_denominator = Atom::num(3) * nested.pow(Atom::num(3) / Atom::num(2));
            let second_denominator = nested.sqrt();

            rubi_simp(
                    &(Atom::num(2) * b__.pow(2) * &d__ * x_.pow(3)
                        / first_denominator),
                    x_,
                ) + rubi_simp(
                    &(Atom::num(2) * &a__ * x_ / second_denominator),
                    x_,
                )
        },
    ));
}

fn push_rules_rule_2555(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 2555,
        source: "Int[Sqrt[a_.*x_^2+b_.*x_*Sqrt[c_+d_.*x_^2]]/(x_*Sqrt[c_+d_.*x_^2]),x_Symbol] :=
          Sqrt[2]*b/a \\[Star] Subst[Int[1/Sqrt[1+x^2/a],x],x,a*x+b*Sqrt[c+d*x^2]] /;
        FreeQ[{a,b,c,d},x] && EqQ[a^2-b^2*d,0] && EqQ[b^2*c+a,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (a__ * x_.pow(2) + b__ * x_ * (c__ + d__ * x_.pow(2)).sqrt()).sqrt()
            / (x_ * (c__ + d__ * x_.pow(2)).sqrt()),
        with: [a__, b__, c__, d__, x_],
        optional: [a__, b__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && eqq!(a__.pow(2) - b__.pow(2) * &d__, 0)
                && eqq!(b__.pow(2) * &c__ + &a__, 0)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_denominator = (Atom::num(1) + sub_atom.pow(2) / &a__).sqrt();

            let transformed = rubi_rhs_int(&(Atom::num(1) / transformed_denominator), sub);
            let replacement = &a__ * x_ + &b__ * (&c__ + &d__ * x_.pow(2)).sqrt();

            rubi_star(Atom::num(2).sqrt() * (&b__ / &a__), rubi_subst(&transformed, sub, replacement))
        },
    ));
}

fn push_rules_rule_2556(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 2556,
        source: "Int[Sqrt[e_.*x_*(a_.*x_+b_.*Sqrt[c_+d_.*x_^2])]/(x_*Sqrt[c_+d_.*x_^2]),x_Symbol] :=
          Int[Sqrt[a*e*x^2+b*e*x*Sqrt[c+d*x^2]]/(x*Sqrt[c+d*x^2]),x] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[a^2-b^2*d,0] && EqQ[b^2*c*e+a,0]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: (e__ * x_ * (a__ * x_ + b__ * (c__ + d__ * x_.pow(2)).sqrt())).sqrt()
            / (x_ * (c__ + d__ * x_.pow(2)).sqrt()),
        with: [e__, a__, b__, c__, d__, x_],
        optional: [e__, a__, b__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(a__.pow(2) - b__.pow(2) * &d__, 0)
                && eqq!(b__.pow(2) * &c__ * &e__ + &a__, 0)
        },
        rhs: {
            let recursive_integrand =
                (&a__ * &e__ * x_.pow(2) + &b__ * &e__ * x_ * (&c__ + &d__ * x_.pow(2)).sqrt()).sqrt()
                    / (x_ * (&c__ + &d__ * x_.pow(2)).sqrt());

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_2557(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 2557,
        source: "Int[Sqrt[c_.*x_^2+d_.*Sqrt[a_+b_.*x_^4]]/Sqrt[a_+b_.*x_^4],x_Symbol] :=
          d \\[Star] Subst[Int[1/(1-2*c*x^2),x],x,x/Sqrt[c*x^2+d*Sqrt[a+b*x^4]]] /;
        FreeQ[{a,b,c,d},x] && EqQ[c^2-b*d^2,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (c__ * x_.pow(2) + d__ * (a__ + b__ * x_.pow(4)).sqrt()).sqrt()
            / (a__ + b__ * x_.pow(4)).sqrt(),
        with: [c__, d__, a__, b__, x_],
        optional: [c__, d__, b__],
        when: {
            freeq!([a__, b__, c__, d__], x_) && eqq!(c__.pow(2) - &b__ * d__.pow(2), 0)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed = rubi_rhs_int(
                &(Atom::num(1) / (Atom::num(1) - Atom::num(2) * &c__ * sub_atom.pow(2))),
                sub,
            );
            let substitution_denominator =
                (&c__ * x_.pow(2) + &d__ * (&a__ + &b__ * x_.pow(4)).sqrt()).sqrt();

            rubi_star(d__, rubi_subst(&transformed, sub, x_ / substitution_denominator))
        },
    ));
}

fn push_rules_rule_2558(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, x_);
    rules.push(rubi_rule!(
        order: 2558,
        source: "Int[(c_.+d_.*x_)^m_.*Sqrt[b_.*x_^2+Sqrt[a_+e_.*x_^4]]/Sqrt[a_+e_.*x_^4],x_Symbol] :=
          (1-I)/2 \\[Star] Int[(c+d*x)^m/Sqrt[Sqrt[a]-I*b*x^2],x] +
          (1+I)/2 \\[Star] Int[(c+d*x)^m/Sqrt[Sqrt[a]+I*b*x^2],x] /;
        FreeQ[{a,b,c,d,m},x] && EqQ[e,b^2] && GtQ[a,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (c__ + d__ * x_).pow(m_) * (b__ * x_.pow(2) + (a__ + e__ * x_.pow(4)).sqrt()).sqrt()
            / (a__ + e__ * x_.pow(4)).sqrt(),
        with: [c__, d__, m_, b__, a__, e__, x_],
        optional: [c__, d__, m_, b__, e__],
        when: {
            freeq!([a__, b__, c__, d__, m_], x_) && eqq!(e__, b__.pow(2)) && gtq!(a__, 0)
        },
        rhs: {
            let imaginary = rubi_i();
            let first_denominator = (a__.sqrt() - &imaginary * &b__ * x_.pow(2)).sqrt();
            let second_denominator = (a__.sqrt() + &imaginary * &b__ * x_.pow(2)).sqrt();

            let base = (&c__ + &d__ * x_).pow(&m_);
            let first_integral = rubi_rhs_int(&(&base / first_denominator), x_);
            let second_integral = rubi_rhs_int(&(base / second_denominator), x_);

            rubi_star(Atom::num(1) - &imaginary, first_integral / 2) + rubi_star(Atom::num(1) + imaginary, second_integral / 2)
        },
    ));
}

fn push_rules_rule_2559(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 2559,
        source: "Int[1/((c_+d_.*x_)*Sqrt[a_+b_.*x_^3]),x_Symbol] :=
          2/(3*c) \\[Star] Int[1/Sqrt[a+b*x^3],x] + 1/(3*c) \\[Star] Int[(c-2*d*x)/((c+d*x)*Sqrt[a+b*x^3]),x] /;
        FreeQ[{a,b,c,d},x] && EqQ[b*c^3-4*a*d^3,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [c__, d__, a__, b__, x_],
        optional: [d__, b__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && eqq!(&b__ * c__.pow(3) - Atom::num(4) * &a__ * d__.pow(3), 0)
        },
        rhs: {
            let radical = (&a__ + &b__ * x_.pow(3)).sqrt();
            let first_integrand = Atom::num(1) / &radical;
            let second_integrand = (&c__ - Atom::num(2) * &d__ * x_)
                / ((&c__ + &d__ * x_) * radical);

            rubi_star(Atom::num(2), rubi_rhs_int(&first_integrand, x_)
                        / (Atom::num(3) * &c__)) + rubi_star(Atom::num(1) / (Atom::num(3) * &c__), rubi_rhs_int(&second_integrand, x_))
        },
    ));
}

fn push_rules_rule_2560(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 2560,
        source: "Int[1/((c_+d_.*x_)*Sqrt[a_+b_.*x_^3]),x_Symbol] :=
          -6*a*d^3/(c*(b*c^3-28*a*d^3)) \\[Star] Int[1/Sqrt[a+b*x^3],x] +
          1/(c*(b*c^3-28*a*d^3)) \\[Star] Int[Simp[c*(b*c^3-22*a*d^3)+6*a*d^4*x,x]/((c+d*x)*Sqrt[a+b*x^3]),x] /;
        FreeQ[{a,b,c,d},x] && EqQ[b^2*c^6-20*a*b*c^3*d^3-8*a^2*d^6,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [c__, d__, a__, b__, x_],
        optional: [d__, b__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && eqq!(
                    b__.pow(2) * c__.pow(6)
                        - Atom::num(20) * &a__ * &b__ * c__.pow(3) * d__.pow(3)
                        - Atom::num(8) * a__.pow(2) * d__.pow(6),
                    0
                )
        },
        rhs: {
            let radical = (&a__ + &b__ * x_.pow(3)).sqrt();
            let first_integrand = Atom::num(1) / &radical;
            let simp = rubi_simp(
                &(&c__ * (&b__ * c__.pow(3) - Atom::num(22) * &a__ * d__.pow(3))
                    + Atom::num(6) * &a__ * d__.pow(4) * x_),
                x_,
            );
            let second_integrand = simp / ((&c__ + &d__ * x_) * radical);
            let coefficient_denominator =
                &c__ * (&b__ * c__.pow(3) - Atom::num(28) * &a__ * d__.pow(3));

            rubi_star(-Atom::num(6) * &a__ * d__.pow(3) / &coefficient_denominator, rubi_rhs_int(&first_integrand, x_)) + rubi_star(Atom::num(1) / coefficient_denominator, rubi_rhs_int(&second_integrand, x_))
        },
    ));
}

fn push_rules_rule_2561(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 2561,
        source: "Int[1/((c_+d_.*x_)*Sqrt[a_+b_.*x_^3]),x_Symbol] :=
          With[{q=Rt[b/a,3]},
          -q/((1+Sqrt[3])*d-c*q) \\[Star] Int[1/Sqrt[a+b*x^3],x] +
          d/((1+Sqrt[3])*d-c*q) \\[Star] Int[(1+Sqrt[3]+q*x)/((c+d*x)*Sqrt[a+b*x^3]),x]] /;
        FreeQ[{a,b,c,d},x] && NeQ[b^2*c^6-20*a*b*c^3*d^3-8*a^2*d^6,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [c__, d__, a__, b__, x_],
        optional: [d__, b__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && neq!(
                    b__.pow(2) * c__.pow(6)
                        - Atom::num(20) * &a__ * &b__ * c__.pow(3) * d__.pow(3)
                        - Atom::num(8) * a__.pow(2) * d__.pow(6),
                    0
                )
        },
        rhs: {
            let q = rubi_rt(&(&b__ / &a__), 3);
            let one_plus_sqrt_three = Atom::num(1) + Atom::num(3).sqrt();
            let coefficient_denominator = &one_plus_sqrt_three * &d__ - &c__ * &q;

            let radical = (&a__ + &b__ * x_.pow(3)).sqrt();
            let first_integrand = Atom::num(1) / &radical;
            let second_integrand =
                (&one_plus_sqrt_three + &q * x_) / ((&c__ + &d__ * x_) * radical);

            rubi_star(-&q, rubi_rhs_int(&first_integrand, x_) / &coefficient_denominator) + rubi_star(d__, rubi_rhs_int(&second_integrand, x_) / coefficient_denominator)
        },
    ));
}

fn push_rules_rule_2562(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 2562,
        source: "Int[(e_+f_.*x_)/((c_+d_.*x_)*Sqrt[a_+b_.*x_^3]),x_Symbol] :=
          2*e/d \\[Star] Subst[Int[1/(1+3*a*x^2),x],x,(1+2*d*x/c)/Sqrt[a+b*x^3]] /;
        FreeQ[{a,b,c,d,e,f},x] && NeQ[d*e-c*f,0] && EqQ[b*c^3-4*a*d^3,0] && EqQ[2*d*e+c*f,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [e__, f__, c__, d__, a__, b__, x_],
        optional: [f__, d__, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && neq!(&d__ * &e__ - &c__ * &f__, 0)
                && eqq!(&b__ * c__.pow(3) - Atom::num(4) * &a__ * d__.pow(3), 0)
                && eqq!(Atom::num(2) * &d__ * &e__ + &c__ * &f__, 0)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed = rubi_rhs_int(
                &(Atom::num(1) / (Atom::num(1) + Atom::num(3) * &a__ * sub_atom.pow(2))),
                sub,
            );
            let substitution_denominator = (&a__ + &b__ * x_.pow(3)).sqrt();

            let replacement =
                (Atom::num(1) + Atom::num(2) * &d__ * x_ / &c__) / substitution_denominator;

            rubi_star(Atom::num(2) * &e__ / &d__, rubi_subst(&transformed, sub, replacement))
        },
    ));
}

fn push_rules_rule_2563(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 2563,
        source: "Int[(e_+f_.*x_)/((c_+d_.*x_)*Sqrt[a_+b_.*x_^3]),x_Symbol] :=
          -2*e/d \\[Star] Subst[Int[1/(9-a*x^2),x],x,(1+f*x/e)^2/Sqrt[a+b*x^3]] /;
        FreeQ[{a,b,c,d,e,f},x] && NeQ[d*e-c*f,0] && EqQ[b*c^3+8*a*d^3,0] && EqQ[2*d*e+c*f,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [e__, f__, c__, d__, a__, b__, x_],
        optional: [f__, d__, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && neq!(&d__ * &e__ - &c__ * &f__, 0)
                && eqq!(&b__ * c__.pow(3) + Atom::num(8) * &a__ * d__.pow(3), 0)
                && eqq!(Atom::num(2) * &d__ * &e__ + &c__ * &f__, 0)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed = rubi_rhs_int(
                &(Atom::num(1) / (Atom::num(9) - &a__ * sub_atom.pow(2))),
                sub,
            );
            let substitution_denominator = (&a__ + &b__ * x_.pow(3)).sqrt();

            let replacement =
                (Atom::num(1) + &f__ * x_ / &e__).pow(2) / substitution_denominator;

            rubi_star(-Atom::num(2) * &e__ / &d__, rubi_subst(&transformed, sub, replacement))
        },
    ));
}

fn push_rules_rule_2564(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 2564,
        source: "Int[(e_.+f_.*x_)/((c_+d_.*x_)*Sqrt[a_+b_.*x_^3]),x_Symbol] :=
          (2*d*e+c*f)/(3*c*d) \\[Star] Int[1/Sqrt[a+b*x^3],x] +
          (d*e-c*f)/(3*c*d) \\[Star] Int[(c-2*d*x)/((c+d*x)*Sqrt[a+b*x^3]),x] /;
        FreeQ[{a,b,c,d,e,f},x] && NeQ[d*e-c*f,0] && (EqQ[b*c^3-4*a*d^3,0] || EqQ[b*c^3+8*a*d^3,0]) && NeQ[2*d*e+c*f,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [e__, f__, c__, d__, a__, b__, x_],
        optional: [e__, f__, d__, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && neq!(&d__ * &e__ - &c__ * &f__, 0)
                && (eqq!(&b__ * c__.pow(3) - Atom::num(4) * &a__ * d__.pow(3), 0)
                    || eqq!(&b__ * c__.pow(3) + Atom::num(8) * &a__ * d__.pow(3), 0))
                && neq!(Atom::num(2) * &d__ * &e__ + &c__ * &f__, 0)
        },
        rhs: {
            let radical = (&a__ + &b__ * x_.pow(3)).sqrt();
            let first_integrand = Atom::num(1) / &radical;
            let second_integrand = (&c__ - Atom::num(2) * &d__ * x_)
                / ((&c__ + &d__ * x_) * radical);
            let coefficient_denominator = Atom::num(3) * &c__ * &d__;

            rubi_star(Atom::num(2) * &d__ * &e__ + &c__ * &f__, rubi_rhs_int(&first_integrand, x_)
                        / &coefficient_denominator) + rubi_star(&d__ * &e__ - &c__ * &f__, rubi_rhs_int(&second_integrand, x_)
                        / coefficient_denominator)
        },
    ));
}

fn push_rules_rule_2565(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 2565,
        source: "Int[(e_+f_.*x_)/((c_+d_.*x_)*Sqrt[a_+b_.*x_^3]),x_Symbol] :=
          With[{k=Simplify[(d*e+2*c*f)/(c*f)]},
          (1+k)*e/d \\[Star] Subst[Int[1/(1+(3+2*k)*a*x^2),x],x,(1+(1+k)*d*x/c)/Sqrt[a+b*x^3]]] /;
        FreeQ[{a,b,c,d,e,f},x] && NeQ[d*e-c*f,0] && EqQ[b^2*c^6-20*a*b*c^3*d^3-8*a^2*d^6,0] && EqQ[6*a*d^4*e-c*f*(b*c^3-22*a*d^3),0]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [e__, f__, c__, d__, a__, b__, x_],
        optional: [f__, d__, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && neq!(&d__ * &e__ - &c__ * &f__, 0)
                && eqq!(
                    b__.pow(2) * c__.pow(6)
                        - Atom::num(20) * &a__ * &b__ * c__.pow(3) * d__.pow(3)
                        - Atom::num(8) * a__.pow(2) * d__.pow(6),
                    0
                )
                && eqq!(
                    Atom::num(6) * &a__ * d__.pow(4) * &e__
                        - &c__
                            * &f__
                            * (&b__ * c__.pow(3) - Atom::num(22) * &a__ * d__.pow(3)),
                    0
                )
        },
        rhs: {
            let k = rubi_simplify(
                &((&d__ * &e__ + Atom::num(2) * &c__ * &f__) / (&c__ * &f__)),
            );
            let one_plus_k = Atom::num(1) + &k;
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed = rubi_rhs_int(
                &(Atom::num(1)
                    / (Atom::num(1)
                        + (Atom::num(3) + Atom::num(2) * &k)
                            * &a__
                            * sub_atom.pow(2))),
                sub,
            );
            let substitution_denominator = (&a__ + &b__ * x_.pow(3)).sqrt();

            let replacement =
                (Atom::num(1) + &one_plus_k * &d__ * x_ / &c__) / substitution_denominator;

            rubi_star(one_plus_k * &e__ / &d__, rubi_subst(&transformed, sub, replacement))
        },
    ));
}

fn push_rules_rule_2566(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 2566,
        source: "Int[(e_.+f_.*x_)/((c_+d_.*x_)*Sqrt[a_+b_.*x_^3]),x_Symbol] :=
          -(6*a*d^4*e-c*f*(b*c^3-22*a*d^3))/(c*d*(b*c^3-28*a*d^3)) \\[Star] Int[1/Sqrt[a+b*x^3],x] +
          (d*e-c*f)/(c*d*(b*c^3-28*a*d^3)) \\[Star] Int[(c*(b*c^3-22*a*d^3)+6*a*d^4*x)/((c+d*x)*Sqrt[a+b*x^3]),x] /;
        FreeQ[{a,b,c,d,e,f},x] && NeQ[d*e-c*f,0] && EqQ[b^2*c^6-20*a*b*c^3*d^3-8*a^2*d^6,0] && NeQ[6*a*d^4*e-c*f*(b*c^3-22*a*d^3),0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [e__, f__, c__, d__, a__, b__, x_],
        optional: [e__, f__, d__, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && neq!(&d__ * &e__ - &c__ * &f__, 0)
                && eqq!(
                    b__.pow(2) * c__.pow(6)
                        - Atom::num(20) * &a__ * &b__ * c__.pow(3) * d__.pow(3)
                        - Atom::num(8) * a__.pow(2) * d__.pow(6),
                    0
                )
                && neq!(
                    Atom::num(6) * &a__ * d__.pow(4) * &e__
                        - &c__
                            * &f__
                            * (&b__ * c__.pow(3) - Atom::num(22) * &a__ * d__.pow(3)),
                    0
                )
        },
        rhs: {
            let coefficient_denominator =
                &c__ * &d__ * (&b__ * c__.pow(3) - Atom::num(28) * &a__ * d__.pow(3));

            let radical = (&a__ + &b__ * x_.pow(3)).sqrt();
            let first_coefficient_numerator = Atom::num(6) * &a__ * d__.pow(4) * &e__
                - &c__
                    * &f__
                    * (&b__ * c__.pow(3) - Atom::num(22) * &a__ * d__.pow(3));
            let first_integrand = Atom::num(1) / &radical;
            let second_integrand = (&c__
                * (&b__ * c__.pow(3) - Atom::num(22) * &a__ * d__.pow(3))
                + Atom::num(6) * &a__ * d__.pow(4) * x_)
                / ((&c__ + &d__ * x_) * radical);

            rubi_star(-first_coefficient_numerator, rubi_rhs_int(&first_integrand, x_)
                        / &coefficient_denominator) + rubi_star(&d__ * &e__ - &c__ * &f__, rubi_rhs_int(&second_integrand, x_)
                        / coefficient_denominator)
        },
    ));
}

fn push_rules_rule_2567(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 2567,
        source: "Int[(e_+f_.*x_)/((c_+d_.*x_)*Sqrt[a_+b_.*x_^3]),x_Symbol] :=
          With[{q=Simplify[(1+Sqrt[3])*f/e]},
          4*3^(1/4)*Sqrt[2-Sqrt[3]]*f*(1+q*x)*Sqrt[(1-q*x+q^2*x^2)/(1+Sqrt[3]+q*x)^2]/
            (q*Sqrt[a+b*x^3]*Sqrt[(1+q*x)/(1+Sqrt[3]+q*x)^2]) \\[Star]
            Subst[Int[1/(((1-Sqrt[3])*d-c*q+((1+Sqrt[3])*d-c*q)*x)*Sqrt[1-x^2]*Sqrt[7-4*Sqrt[3]+x^2]),x],x,(-1+Sqrt[3]-q*x)/(1+Sqrt[3]+q*x)]] /;
        FreeQ[{a,b,c,d,e,f},x] && NeQ[d*e-c*f,0] && EqQ[b*e^3-2*(5+3*Sqrt[3])*a*f^3,0] && NeQ[b*c^3-2*(5-3*Sqrt[3])*a*d^3,0]",
        desc: "Piecewise constant extraction and integration by substitution (the M\\[ODoubleDot]bius transformation)",
        refs: ["G&R 3.139"],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [e__, f__, c__, d__, a__, b__, x_],
        optional: [f__, d__, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && neq!(&d__ * &e__ - &c__ * &f__, 0)
                && eqq!(
                    &b__ * e__.pow(3)
                        - Atom::num(2)
                            * (Atom::num(5) + Atom::num(3) * Atom::num(3).sqrt())
                            * &a__
                            * f__.pow(3),
                    0
                )
                && neq!(
                    &b__ * c__.pow(3)
                        - Atom::num(2)
                            * (Atom::num(5) - Atom::num(3) * Atom::num(3).sqrt())
                            * &a__
                            * d__.pow(3),
                    0
                )
        },
        rhs: {
            let sqrt_three = Atom::num(3).sqrt();
            let one_plus_sqrt_three = Atom::num(1) + &sqrt_three;
            let q = rubi_simplify(&(&one_plus_sqrt_three * &f__ / &e__));

            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_linear = (Atom::num(1) - &sqrt_three) * &d__ - &c__ * &q
                + (&one_plus_sqrt_three * &d__ - &c__ * &q) * &sub_atom;
            let transformed_denominator = transformed_linear
                * (Atom::num(1) - sub_atom.pow(2)).sqrt()
                * (Atom::num(7) - Atom::num(4) * &sqrt_three + sub_atom.pow(2)).sqrt();
            let transformed =
                rubi_rhs_int(&(Atom::num(1) / transformed_denominator), sub);
            let radical = (&a__ + &b__ * x_.pow(3)).sqrt();
            let q_x = &q * x_;
            let one_plus_q_x = Atom::num(1) + &q_x;
            let one_plus_sqrt_three_plus_q_x = &one_plus_sqrt_three + &q_x;

            let numerator_sqrt = (Atom::num(1) - &q_x + q.pow(2) * x_.pow(2))
                / one_plus_sqrt_three_plus_q_x.pow(2);
            let denominator_sqrt =
                (&one_plus_q_x / one_plus_sqrt_three_plus_q_x.pow(2)).sqrt();
            let coefficient_denominator = &q * &radical * denominator_sqrt;

            let replacement =
                (-Atom::num(1) + &sqrt_three - &q * x_) / one_plus_sqrt_three_plus_q_x;

            rubi_star(Atom::num(4) * Atom::num(3).pow(Atom::num(1) / Atom::num(4)) * (Atom::num(2) - sqrt_three).sqrt() * &f__ * one_plus_q_x * numerator_sqrt.sqrt() / coefficient_denominator, rubi_subst(&transformed, sub, replacement))
        },
    ));
}

fn push_rules_rule_2568(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 2568,
        source: "Int[(e_+f_.*x_)/((c_+d_.*x_)*Sqrt[a_+b_.*x_^3]),x_Symbol] :=
          With[{q=Simplify[(-1+Sqrt[3])*f/e]},
          4*3^(1/4)*Sqrt[2+Sqrt[3]]*f*(1-q*x)*Sqrt[(1+q*x+q^2*x^2)/(1-Sqrt[3]-q*x)^2]/(q*Sqrt[a+b*x^3]*Sqrt[-(1-q*x)/(1-Sqrt[3]-q*x)^2]) \\[Star]
            Subst[Int[1/(((1+Sqrt[3])*d+c*q+((1-Sqrt[3])*d+c*q)*x)*Sqrt[1-x^2]*Sqrt[7+4*Sqrt[3]+x^2]),x],x,(1+Sqrt[3]-q*x)/(-1+Sqrt[3]+q*x)]] /;
        FreeQ[{a,b,c,d,e,f},x] && NeQ[d*e-c*f,0] && EqQ[b*e^3-2*(5-3*Sqrt[3])*a*f^3,0] && NeQ[b*c^3-2*(5+3*Sqrt[3])*a*d^3,0]",
        desc: "Piecewise constant extraction and integration by substitution (the M\\[ODoubleDot]bius transformation)",
        refs: ["G&R 3.139"],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [e__, f__, c__, d__, a__, b__, x_],
        optional: [f__, d__, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && neq!(&d__ * &e__ - &c__ * &f__, 0)
                && eqq!(
                    &b__ * e__.pow(3)
                        - Atom::num(2)
                            * (Atom::num(5) - Atom::num(3) * Atom::num(3).sqrt())
                            * &a__
                            * f__.pow(3),
                    0
                )
                && neq!(
                    &b__ * c__.pow(3)
                        - Atom::num(2)
                            * (Atom::num(5) + Atom::num(3) * Atom::num(3).sqrt())
                            * &a__
                            * d__.pow(3),
                    0
                )
        },
        rhs: {
            let sqrt_three = Atom::num(3).sqrt();
            let minus_one_plus_sqrt_three = -Atom::num(1) + &sqrt_three;
            let one_minus_sqrt_three = Atom::num(1) - &sqrt_three;
            let q = rubi_simplify(&(&minus_one_plus_sqrt_three * &f__ / &e__));

            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_linear = (Atom::num(1) + &sqrt_three) * &d__ + &c__ * &q
                + (&one_minus_sqrt_three * &d__ + &c__ * &q) * &sub_atom;
            let transformed_denominator = transformed_linear
                * (Atom::num(1) - sub_atom.pow(2)).sqrt()
                * (Atom::num(7) + Atom::num(4) * &sqrt_three + sub_atom.pow(2)).sqrt();
            let transformed =
                rubi_rhs_int(&(Atom::num(1) / transformed_denominator), sub);
            let radical = (&a__ + &b__ * x_.pow(3)).sqrt();
            let q_x = &q * x_;
            let one_minus_q_x = Atom::num(1) - &q_x;
            let one_minus_sqrt_three_minus_q_x = &one_minus_sqrt_three - &q_x;

            let numerator_sqrt = (Atom::num(1) + &q_x + q.pow(2) * x_.pow(2))
                / one_minus_sqrt_three_minus_q_x.pow(2);
            let denominator_sqrt =
                (-&one_minus_q_x / one_minus_sqrt_three_minus_q_x.pow(2)).sqrt();
            let coefficient_denominator = &q * &radical * denominator_sqrt;

            let replacement = (Atom::num(1) + &sqrt_three - &q * x_)
                / (-Atom::num(1) + &sqrt_three + &q * x_);

            rubi_star(Atom::num(4) * Atom::num(3).pow(Atom::num(1) / Atom::num(4)) * (Atom::num(2) + sqrt_three).sqrt() * &f__ * one_minus_q_x * numerator_sqrt.sqrt() / coefficient_denominator, rubi_subst(&transformed, sub, replacement))
        },
    ));
}

fn push_rules_rule_2569(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 2569,
        source: "Int[(e_.+f_.*x_)/((c_+d_.*x_)*Sqrt[a_+b_.*x_^3]),x_Symbol] :=
          With[{q=Rt[b/a,3]},
          ((1+Sqrt[3])*f-e*q)/((1+Sqrt[3])*d-c*q) \\[Star] Int[1/Sqrt[a+b*x^3],x] +
          (d*e-c*f)/((1+Sqrt[3])*d-c*q) \\[Star] Int[(1+Sqrt[3]+q*x)/((c+d*x)*Sqrt[a+b*x^3]),x]] /;
        FreeQ[{a,b,c,d,e,f},x] && NeQ[d*e-c*f,0] && NeQ[b^2*c^6-20*a*b*c^3*d^3-8*a^2*d^6,0] && NeQ[b^2*e^6-20*a*b*e^3*f^3-8*a^2*f^6,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [e__, f__, c__, d__, a__, b__, x_],
        optional: [e__, f__, d__, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && neq!(&d__ * &e__ - &c__ * &f__, 0)
                && neq!(
                    b__.pow(2) * c__.pow(6)
                        - Atom::num(20) * &a__ * &b__ * c__.pow(3) * d__.pow(3)
                        - Atom::num(8) * a__.pow(2) * d__.pow(6),
                    0
                )
                && neq!(
                    b__.pow(2) * e__.pow(6)
                        - Atom::num(20) * &a__ * &b__ * e__.pow(3) * f__.pow(3)
                        - Atom::num(8) * a__.pow(2) * f__.pow(6),
                    0
                )
        },
        rhs: {
            let q = rubi_rt(&(&b__ / &a__), 3);
            let one_plus_sqrt_three = Atom::num(1) + Atom::num(3).sqrt();
            let coefficient_denominator = &one_plus_sqrt_three * &d__ - &c__ * &q;

            let radical = (&a__ + &b__ * x_.pow(3)).sqrt();
            let first_integrand = Atom::num(1) / &radical;
            let second_integrand =
                (&one_plus_sqrt_three + &q * x_) / ((&c__ + &d__ * x_) * radical);

            rubi_star(&one_plus_sqrt_three * &f__ - &e__ * &q, rubi_rhs_int(&first_integrand, x_)
                        / &coefficient_denominator) + rubi_star(&d__ * &e__ - &c__ * &f__, rubi_rhs_int(&second_integrand, x_)
                        / coefficient_denominator)
        },
    ));
}

fn push_rules_rule_2570(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, h__, x_);
    rules.push(rubi_rule!(
        order: 2570,
        source: "Int[(f_+g_.*x_+h_.*x_^2)/((c_+d_.*x_+e_.*x_^2)*Sqrt[a_+b_.*x_^3]),x_Symbol] :=
          -2*g*h \\[Star] Subst[Int[1/(2*e*h-(b*d*f-2*a*e*h)*x^2),x],x,(1+2*h*x/g)/Sqrt[a+b*x^3]] /;
        FreeQ[{a,b,c,d,e,f,g,h},x] && NeQ[b*d*f-2*a*e*h,0] && EqQ[b*g^3-8*a*h^3,0] && EqQ[g^2+2*f*h,0] && EqQ[b*d*f+b*c*g-4*a*e*h,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (f__ + g__ * x_ + h__ * x_.pow(2))
            / ((c__ + d__ * x_ + e__ * x_.pow(2)) * (a__ + b__ * x_.pow(3)).sqrt()),
        with: [f__, g__, h__, c__, d__, e__, a__, b__, x_],
        optional: [g__, h__, d__, e__, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__], x_)
                && neq!(&b__ * &d__ * &f__ - Atom::num(2) * &a__ * &e__ * &h__, 0)
                && eqq!(&b__ * g__.pow(3) - Atom::num(8) * &a__ * h__.pow(3), 0)
                && eqq!(g__.pow(2) + Atom::num(2) * &f__ * &h__, 0)
                && eqq!(
                    &b__ * &d__ * &f__ + &b__ * &c__ * &g__
                        - Atom::num(4) * &a__ * &e__ * &h__,
                    0
                )
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_denominator = Atom::num(2) * &e__ * &h__
                - (&b__ * &d__ * &f__ - Atom::num(2) * &a__ * &e__ * &h__)
                    * sub_atom.pow(2);
            let transformed =
                rubi_rhs_int(&(Atom::num(1) / transformed_denominator), sub);
            let substitution_denominator = (&a__ + &b__ * x_.pow(3)).sqrt();

            let replacement =
                (Atom::num(1) + Atom::num(2) * &h__ * x_ / &g__) / substitution_denominator;

            rubi_star(-Atom::num(2) * &g__ * &h__, rubi_subst(&transformed, sub, replacement))
        },
    ));
}

fn push_rules_rule_2571(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, e__, f__, g__, h__, x_);
    rules.push(rubi_rule!(
        order: 2571,
        source: "Int[(f_+g_.*x_+h_.*x_^2)/((c_+e_.*x_^2)*Sqrt[a_+b_.*x_^3]),x_Symbol] :=
          -g/e \\[Star] Subst[Int[1/(1+a*x^2),x],x,(1+2*h*x/g)/Sqrt[a+b*x^3]] /;
        FreeQ[{a,b,c,e,f,g,h},x] && EqQ[b*g^3-8*a*h^3,0] && EqQ[g^2+2*f*h,0] && EqQ[b*c*g-4*a*e*h,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (f__ + g__ * x_ + h__ * x_.pow(2))
            / ((c__ + e__ * x_.pow(2)) * (a__ + b__ * x_.pow(3)).sqrt()),
        with: [f__, g__, h__, c__, e__, a__, b__, x_],
        optional: [g__, h__, e__, b__],
        when: {
            freeq!([a__, b__, c__, e__, f__, g__, h__], x_)
                && eqq!(&b__ * g__.pow(3) - Atom::num(8) * &a__ * h__.pow(3), 0)
                && eqq!(g__.pow(2) + Atom::num(2) * &f__ * &h__, 0)
                && eqq!(&b__ * &c__ * &g__ - Atom::num(4) * &a__ * &e__ * &h__, 0)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed = rubi_rhs_int(
                &(Atom::num(1) / (Atom::num(1) + &a__ * sub_atom.pow(2))),
                sub,
            );
            let substitution_denominator = (&a__ + &b__ * x_.pow(3)).sqrt();

            let replacement =
                (Atom::num(1) + Atom::num(2) * &h__ * x_ / &g__) / substitution_denominator;

            rubi_star(-&g__, rubi_subst(&transformed, sub, replacement) / &e__)
        },
    ));
}

fn push_rules_rule_2572(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 2572,
        source: "Int[Sqrt[a_+b_.*x_^3]/(c_+d_.*x_),x_Symbol] :=
          b/d \\[Star] Int[x^2/Sqrt[a+b*x^3],x] +
          b*c/d^3 \\[Star] Int[(c-d*x)/Sqrt[a+b*x^3],x] /;
        FreeQ[{a,b,c,d},x] && EqQ[b*c^3-a*d^3,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && eqq!(&b__ * c__.pow(3) - &a__ * d__.pow(3), 0)
        },
        rhs: {
            let radical = (&a__ + &b__ * x_.pow(3)).sqrt();
            let first_integrand = x_.pow(2) / &radical;
            let second_integrand = (&c__ - &d__ * x_) / radical;

            rubi_star(&b__, rubi_rhs_int(&first_integrand, x_) / &d__) + rubi_star(&b__ * &c__ / d__.pow(3), rubi_rhs_int(&second_integrand, x_))
        },
    ));
}

fn push_rules_rule_2573(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 2573,
        source: "Int[Sqrt[a_+b_.*x_^3]/(c_+d_.*x_),x_Symbol] :=
          b/d \\[Star] Int[x^2/Sqrt[a+b*x^3],x] +
          b*c/d^3 \\[Star] Int[(c-d*x)/Sqrt[a+b*x^3],x] -
          (b*c^3-a*d^3)/d^3 \\[Star] Int[1/((c+d*x)*Sqrt[a+b*x^3]),x] /;
        FreeQ[{a,b,c,d},x] && NeQ[b*c^3-a*d^3,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && neq!(&b__ * c__.pow(3) - &a__ * d__.pow(3), 0)
        },
        rhs: {
            let radical = (&a__ + &b__ * x_.pow(3)).sqrt();
            let first_integrand = x_.pow(2) / &radical;
            let second_integrand = (&c__ - &d__ * x_) / &radical;
            let third_integrand = Atom::num(1) / ((&c__ + &d__ * x_) * radical);

            rubi_star(&b__, rubi_rhs_int(&first_integrand, x_) / &d__) - rubi_star(&b__ * c__.pow(3) - &a__ * d__.pow(3), rubi_rhs_int(&third_integrand, x_)
                        / d__.pow(3)) + rubi_star(&b__ * &c__ / d__.pow(3), rubi_rhs_int(&second_integrand, x_))
        },
    ));
}

fn push_rules_rule_2574(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 2574,
        source: "Int[1/((c_+d_.*x_)*(a_+b_.*x_^3)^(1/3)),x_Symbol] :=
          Sqrt[3]*ArcTan[(1-2^(1/3)*Rt[b,3]*(c-d*x)/(d*(a+b*x^3)^(1/3)))/Sqrt[3]]/(2^(4/3)*Rt[b,3]*c) +
          Log[(c+d*x)^2*(c-d*x)]/(2^(7/3)*Rt[b,3]*c) -
          (3*Log[Rt[b,3]*(c-d*x)+2^(2/3)*d*(a+b*x^3)^(1/3)])/(2^(7/3)*Rt[b,3]*c) /;
        FreeQ[{a,b,c,d},x] && EqQ[b*c^3+a*d^3,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [c__, d__, a__, b__, x_],
        optional: [d__, b__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && eqq!(&b__ * c__.pow(3) + &a__ * d__.pow(3), 0)
        },
        rhs: {
            let q = rubi_rt(&b__, 3);
            let cubic_root = (&a__ + &b__ * x_.pow(3)).pow(Atom::num(1) / Atom::num(3));
            let arctan_denominator = &d__ * &cubic_root;

            let sqrt_three = Atom::num(3).sqrt();
            let two = Atom::num(2);
            let arctan_argument = (Atom::num(1)
                - two.pow(Atom::num(1) / Atom::num(3))
                    * &q
                    * (&c__ - &d__ * x_)
                    / arctan_denominator)
                / &sqrt_three;
            let first_denominator = two.pow(Atom::num(4) / Atom::num(3)) * &q * &c__;
            let log_denominator = two.pow(Atom::num(7) / Atom::num(3)) * &q * &c__;

            rubi_simp(
                    &(sqrt_three * arctan_argument.atan() / first_denominator),
                    x_,
                ) + rubi_simp(
                    &(((&c__ + &d__ * x_).pow(2) * (&c__ - &d__ * x_))
                        .log()
                        / &log_denominator),
                    x_,
                ) - rubi_simp(
                    &(Atom::num(3)
                        * (&q * (&c__ - &d__ * x_)
                            + two.pow(Atom::num(2) / Atom::num(3)) * &d__ * cubic_root)
                            .log()
                        / log_denominator),
                    x_,
                )
        },
    ));
}

fn push_rules_rule_2575(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 2575,
        source: "Int[1/((c_+d_.*x_)*(a_+b_.*x_^3)^(1/3)),x_Symbol] :=
          1/(2*c) \\[Star] Int[1/(a+b*x^3)^(1/3),x] + 1/(2*c) \\[Star] Int[(c-d*x)/((c+d*x)*(a+b*x^3)^(1/3)),x] /;
        FreeQ[{a,b,c,d},x] && EqQ[2*b*c^3-a*d^3,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [c__, d__, a__, b__, x_],
        optional: [d__, b__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && eqq!(Atom::num(2) * &b__ * c__.pow(3) - &a__ * d__.pow(3), 0)
        },
        rhs: {
            let cubic_root = (&a__ + &b__ * x_.pow(3)).pow(Atom::num(1) / Atom::num(3));
            let first_integrand = Atom::num(1) / &cubic_root;
            let second_integrand = (&c__ - &d__ * x_)
                / ((&c__ + &d__ * x_) * cubic_root);

            rubi_star(Atom::num(1) / (Atom::num(2) * &c__), rubi_rhs_int(&first_integrand, x_)) + rubi_star(Atom::num(1) / (Atom::num(2) * &c__), rubi_rhs_int(&second_integrand, x_))
        },
    ));
}

fn push_rules_rule_2576(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 2576,
        source: "Int[(e_+f_.*x_)/((c_+d_.*x_)*(a_+b_.*x_^3)^(1/3)),x_Symbol] :=
          Sqrt[3]*f*ArcTan[(1+2*Rt[b,3]*(2*c+d*x)/(d*(a+b*x^3)^(1/3)))/Sqrt[3]]/(Rt[b,3]*d) +
          (f*Log[c+d*x])/(Rt[b,3]*d) -
          (3*f*Log[Rt[b,3]*(2*c+d*x)-d*(a+b*x^3)^(1/3)])/(2*Rt[b,3]*d) /;
        FreeQ[{a,b,c,d,e,f},x] && EqQ[d*e+c*f,0] && EqQ[2*b*c^3-a*d^3,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [e__, f__, c__, d__, a__, b__, x_],
        optional: [f__, d__, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && eqq!(&d__ * &e__ + &c__ * &f__, 0)
                && eqq!(Atom::num(2) * &b__ * c__.pow(3) - &a__ * d__.pow(3), 0)
        },
        rhs: {
            let q = rubi_rt(&b__, 3);
            let coefficient_denominator = &q * &d__;

            let cubic_root = (&a__ + &b__ * x_.pow(3)).pow(Atom::num(1) / Atom::num(3));
            let arctan_denominator = &d__ * &cubic_root;

            let sqrt_three = Atom::num(3).sqrt();
            let arctan_argument = (Atom::num(1)
                + Atom::num(2)
                    * &q
                    * (Atom::num(2) * &c__ + &d__ * x_)
                    / arctan_denominator)
                / &sqrt_three;
            let log_argument =
                &q * (Atom::num(2) * &c__ + &d__ * x_) - &d__ * cubic_root;

            rubi_simp(
                    &(sqrt_three * &f__ * arctan_argument.atan()
                        / &coefficient_denominator),
                    x_,
                ) + rubi_simp(
                    &(&f__ * (&c__ + &d__ * x_).log() / &coefficient_denominator),
                    x_,
                ) - rubi_simp(
                    &(Atom::num(3) * &f__ * log_argument.log()
                        / (Atom::num(2) * coefficient_denominator)),
                    x_,
                )
        },
    ));
}

fn push_rules_rule_2577(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, x_);
    rules.push(rubi_rule!(
        order: 2577,
        source: "Int[(e_.+f_.*x_)/((c_.+d_.*x_)*(a_+b_.*x_^3)^(1/3)),x_Symbol] :=
          f/d \\[Star] Int[1/(a+b*x^3)^(1/3),x] + (d*e-c*f)/d \\[Star] Int[1/((c+d*x)*(a+b*x^3)^(1/3)),x] /;
        FreeQ[{a,b,c,d,e,f},x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [e__, f__, c__, d__, a__, b__, x_],
        optional: [e__, f__, c__, d__, b__],
        when: { freeq!([a__, b__, c__, d__, e__, f__], x_) },
        rhs: {
            let cubic_root = (&a__ + &b__ * x_.pow(3)).pow(Atom::num(1) / Atom::num(3));
            let first_integrand = Atom::num(1) / &cubic_root;
            let second_integrand = Atom::num(1) / ((&c__ + &d__ * x_) * cubic_root);

            rubi_star(&f__, rubi_rhs_int(&first_integrand, x_) / &d__) + rubi_star(&d__ * &e__ - &c__ * &f__, rubi_rhs_int(&second_integrand, x_)
                        / &d__)
        },
    ));
}

fn push_rules_rule_2578(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 2578,
        source: "Int[(a_+b_.*x_^3)^(2/3)/(c_+d_.*x_),x_Symbol] :=
          (a+b*x^3)^(2/3)/(2*d) -
          b*c/d^2 \\[Star] Int[x/(a+b*x^3)^(1/3),x] +
          1/d^2 \\[Star] Int[(a*d^2+b*c^2*x)/((c+d*x)*(a+b*x^3)^(1/3)),x] /;
        FreeQ[{a,b,c,d},x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (a__ + b__ * x_.pow(3)).pow(Atom::num(2) / Atom::num(3))
            / (c__ + d__ * x_),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, d__],
        when: { freeq!([a__, b__, c__, d__], x_) },
        rhs: {
            let base = &a__ + &b__ * x_.pow(3);
            let cubic_root = base.pow(Atom::num(1) / Atom::num(3));
            let first_integrand = x_ / &cubic_root;
            let second_integrand = (&a__ * d__.pow(2) + &b__ * c__.pow(2) * x_)
                / ((&c__ + &d__ * x_) * cubic_root);

            rubi_simp(
                    &(base.pow(Atom::num(2) / Atom::num(3)) / (Atom::num(2) * &d__)),
                    x_,
                ) + rubi_star(Atom::num(1) / d__.pow(2), rubi_rhs_int(&second_integrand, x_)) - rubi_star(&b__ * &c__ / d__.pow(2), rubi_rhs_int(&first_integrand, x_))
        },
    ));
}

fn push_rules_rule_2579(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 2579,
        source: "Int[1/((c_+d_.*x_)*(a_+b_.*x_^3)^(2/3)),x_Symbol] :=
          With[{q=Rt[b,3]},
          -d*ArcTan[(1+2*q*x/(a+b*x^3)^(1/3))/Sqrt[3]]/(2*Sqrt[3]*q^2*c^2) +
          Sqrt[3]*d*ArcTan[(1+2*q*(2*c+d*x)/(d*(a+b*x^3)^(1/3)))/Sqrt[3]]/(2*q^2*c^2) -
          d*Log[c+d*x]/(2*q^2*c^2) -
          d*Log[q*x-(a+b*x^3)^(1/3)]/(4*q^2*c^2) +
          3*d*Log[q*(2*c+d*x)-d*(a+b*x^3)^(1/3)]/(4*q^2*c^2)] /;
        FreeQ[{a,b,c,d},x] && EqQ[2*b*c^3-a*d^3,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: Atom::num(1)
            / ((c__ + d__ * x_)
                * (a__ + b__ * x_.pow(3)).pow(Atom::num(2) / Atom::num(3))),
        with: [c__, d__, a__, b__, x_],
        optional: [d__, b__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && eqq!(Atom::num(2) * &b__ * c__.pow(3) - &a__ * d__.pow(3), 0)
        },
        rhs: {
            let q = rubi_rt(&b__, 3);
            let cubic_root = (&a__ + &b__ * x_.pow(3)).pow(Atom::num(1) / Atom::num(3));

            let sqrt_three = Atom::num(3).sqrt();
            let q_squared_c_squared = q.pow(2) * c__.pow(2);

            let first_arctan_argument =
                (Atom::num(1) + Atom::num(2) * &q * x_ / &cubic_root) / &sqrt_three;
            let second_arctan_argument = (Atom::num(1)
                + Atom::num(2)
                    * &q
                    * (Atom::num(2) * &c__ + &d__ * x_)
                    / (&d__ * &cubic_root))
                / &sqrt_three;

            rubi_simp(
                    &(-&d__ * first_arctan_argument.atan()
                        / (Atom::num(2) * &sqrt_three * &q_squared_c_squared)),
                    x_,
                ) + rubi_simp(
                    &(sqrt_three * &d__ * second_arctan_argument.atan()
                        / (Atom::num(2) * &q_squared_c_squared)),
                    x_,
                ) - rubi_simp(
                    &(&d__ * (&c__ + &d__ * x_).log()
                        / (Atom::num(2) * &q_squared_c_squared)),
                    x_,
                ) - rubi_simp(
                    &(&d__ * (&q * x_ - &cubic_root).log()
                        / (Atom::num(4) * &q_squared_c_squared)),
                    x_,
                ) + rubi_simp(
                    &(Atom::num(3)
                        * &d__
                        * (&q * (Atom::num(2) * &c__ + &d__ * x_)
                            - &d__ * cubic_root)
                            .log()
                        / (Atom::num(4) * q_squared_c_squared)),
                    x_,
                )
        },
    ));
}

fn push_rules_rule_2580(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, p_, px_, q_, x_);
    rules.push(rubi_rule!(
        order: 2580,
        source: "Int[x_^m_.*Px_*(c_+d_.*x_)^q_*(a_+b_.*x_^3)^p_.,x_Symbol] :=
          Int[ExpandIntegrand[(c^3+d^3*x^3)^q*(a+b*x^3)^p,x^m*Px/(c^2-c*d*x+d^2*x^2)^q,x],x] /;
        FreeQ[{a,b,c,d,m,p},x] && PolyQ[Px,x] && ILtQ[q,0] && IntegerQ[m] && RationalQ[p] && EqQ[Denominator[p],3]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: x_.pow(m_) * px_ * (c__ + d__ * x_).pow(q_)
            * (a__ + b__ * x_.pow(3)).pow(p_),
        with: [m_, px_, c__, d__, q_, a__, b__, p_, x_],
        optional: [m_, d__, b__, p_],
        when: {
            freeq!([a__, b__, c__, d__, m_, p_], x_)
                && rubi_poly_q(&px_, x_)
                && iltq!(q_, 0)
                && integerq!(m_)
                && rationalq!(p_)
                && rubi_denominator(&p_) == Some(3)
        },
        rhs: {
            let u = (c__.pow(3) + d__.pow(3) * x_.pow(3)).pow(&q_)
                * (&a__ + &b__ * x_.pow(3)).pow(&p_);
            let v = x_.pow(&m_) * &px_
                / (c__.pow(2) - &c__ * &d__ * x_
                    + d__.pow(2) * x_.pow(2))
                .pow(&q_);
            let expanded =
                rubi_expand_integrand_product(&u, &v, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_2581(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, p_, px__, q_, x_);
    rules.push(rubi_rule!(
        order: 2581,
        source: "Int[Px_.*(c_+d_.*x_)^q_*(a_+b_.*x_^3)^p_.,x_Symbol] :=
          Int[ExpandIntegrand[(c^3+d^3*x^3)^q*(a+b*x^3)^p,Px/(c^2-c*d*x+d^2*x^2)^q,x],x] /;
        FreeQ[{a,b,c,d,p},x] && PolyQ[Px,x] && ILtQ[q,0] && RationalQ[p] && EqQ[Denominator[p],3]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: px__ * (c__ + d__ * x_).pow(q_) * (a__ + b__ * x_.pow(3)).pow(p_),
        with: [px__, c__, d__, q_, a__, b__, p_, x_],
        optional: [px__, d__, b__, p_],
        when: {
            freeq!([a__, b__, c__, d__, p_], x_)
                && rubi_poly_q(&px__, x_)
                && iltq!(q_, 0)
                && rationalq!(p_)
                && rubi_denominator(&p_) == Some(3)
        },
        rhs: {
            let u = (c__.pow(3) + d__.pow(3) * x_.pow(3)).pow(&q_)
                * (&a__ + &b__ * x_.pow(3)).pow(&p_);
            let v = &px__
                / (c__.pow(2) - &c__ * &d__ * x_
                    + d__.pow(2) * x_.pow(2))
                .pow(&q_);
            let expanded =
                rubi_expand_integrand_product(&u, &v, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_2582(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, p_, px_, q_, x_);
    rules.push(rubi_rule!(
        order: 2582,
        source: "Int[x_^m_.*Px_*(c_+d_.*x_+e_.*x_^2)^q_*(a_+b_.*x_^3)^p_.,x_Symbol] :=
          1/c^q \\[Star] Int[ExpandIntegrand[(c^3-d^3*x^3)^q*(a+b*x^3)^p,x^m*Px/(c-d*x)^q,x],x] /;
        FreeQ[{a,b,c,d,e,m,p},x] && PolyQ[Px,x] && EqQ[d^2-c*e,0] && ILtQ[q,0] && IntegerQ[m] && RationalQ[p] && EqQ[Denominator[p],3]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: x_.pow(m_) * px_ * (c__ + d__ * x_ + e__ * x_.pow(2)).pow(q_)
            * (a__ + b__ * x_.pow(3)).pow(p_),
        with: [m_, px_, c__, d__, e__, q_, a__, b__, p_, x_],
        optional: [m_, d__, e__, b__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, p_], x_)
                && rubi_poly_q(&px_, x_)
                && eqq!(d__.pow(2) - &c__ * &e__, 0)
                && iltq!(q_, 0)
                && integerq!(m_)
                && rationalq!(p_)
                && rubi_denominator(&p_) == Some(3)
        },
        rhs: {
            let u = (c__.pow(3) - d__.pow(3) * x_.pow(3)).pow(&q_)
                * (&a__ + &b__ * x_.pow(3)).pow(&p_);
            let v = x_.pow(&m_) * &px_ / (&c__ - &d__ * x_).pow(&q_);
            let expanded =
                rubi_expand_integrand_product(&u, &v, x_);

            rubi_star(Atom::num(1) / c__.pow(&q_), rubi_rhs_int(&expanded, x_))
        },
    ));
}

fn push_rules_rule_2583(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, p_, px__, q_, x_);
    rules.push(rubi_rule!(
        order: 2583,
        source: "Int[Px_.*(c_+d_.*x_+e_.*x_^2)^q_*(a_+b_.*x_^3)^p_.,x_Symbol] :=
          1/c^q \\[Star] Int[ExpandIntegrand[(c^3-d^3*x^3)^q*(a+b*x^3)^p,Px/(c-d*x)^q,x],x] /;
        FreeQ[{a,b,c,d,e,p},x] && PolyQ[Px,x] && EqQ[d^2-c*e,0] && ILtQ[q,0] && RationalQ[p] && EqQ[Denominator[p],3]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: px__ * (c__ + d__ * x_ + e__ * x_.pow(2)).pow(q_)
            * (a__ + b__ * x_.pow(3)).pow(p_),
        with: [px__, c__, d__, e__, q_, a__, b__, p_, x_],
        optional: [px__, d__, e__, b__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, p_], x_)
                && rubi_poly_q(&px__, x_)
                && eqq!(d__.pow(2) - &c__ * &e__, 0)
                && iltq!(q_, 0)
                && rationalq!(p_)
                && rubi_denominator(&p_) == Some(3)
        },
        rhs: {
            let u = (c__.pow(3) - d__.pow(3) * x_.pow(3)).pow(&q_)
                * (&a__ + &b__ * x_.pow(3)).pow(&p_);
            let v = &px__ / (&c__ - &d__ * x_).pow(&q_);
            let expanded =
                rubi_expand_integrand_product(&u, &v, x_);

            rubi_star(Atom::num(1) / c__.pow(&q_), rubi_rhs_int(&expanded, x_))
        },
    ));
}

fn push_rules_rule_2584(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, n_, nn_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 2584,
        source: "Int[(c_+d_.*x_^n_.)^q_*(a_+b_.*x_^nn_.)^p_,x_Symbol] :=
          Int[ExpandToSum[(c-d*x^n)^(-q),x]*(a+b*x^nn)^p/(c^2-d^2*x^(2*n))^(-q),x] /;
        FreeQ[{a,b,c,d,n,nn,p},x] && Not[IntegerQ[p]] && ILtQ[q,0] && IGtQ[Log[2,nn/n],0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (c__ + d__ * x_.pow(n_)).pow(q_) * (a__ + b__ * x_.pow(nn_)).pow(p_),
        with: [c__, d__, n_, q_, a__, b__, nn_, p_, x_],
        optional: [d__, n_, b__, nn_],
        when: {
            freeq!([a__, b__, c__, d__, n_, nn_, p_], x_)
                && !integerq!(p_)
                && iltq!(q_, 0)
                && igtq!(rubi_log_base(&Atom::num(2), &(&nn_ / &n_)), 0)
        },
        rhs: {
            let expanded_to_sum = rubi_expand_to_sum(
                &(&c__ - &d__ * x_.pow(&n_)).pow(-&q_),
                x_,
            );
            let quotient = (&a__ + &b__ * x_.pow(&nn_)).pow(&p_)
                / (c__.pow(2) - d__.pow(2) * x_.pow(Atom::num(2) * &n_)).pow(-&q_);

            rubi_rhs_int(&(expanded_to_sum * quotient), x_)
        },
    ));
}

fn push_rules_rule_2585(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, n_, nn_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 2585,
        source: "Int[(e_.*x_)^m_.*(c_+d_.*x_^n_.)^q_*(a_+b_.*x_^nn_.)^p_,x_Symbol] :=
          (e*x)^m/x^m \\[Star] Int[x^m*ExpandToSum[(c-d*x^n)^(-q),x]*(a+b*x^nn)^p/(c^2-d^2*x^(2*n))^(-q),x] /;
        FreeQ[{a,b,c,d,e,m,n,nn,p},x] && Not[IntegerQ[p]] && ILtQ[q,0] && IGtQ[Log[2,nn/n],0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (e__ * x_).pow(m_) * (c__ + d__ * x_.pow(n_)).pow(q_)
            * (a__ + b__ * x_.pow(nn_)).pow(p_),
        with: [e__, m_, c__, d__, n_, q_, a__, b__, nn_, p_, x_],
        optional: [e__, m_, d__, n_, b__, nn_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_, nn_, p_], x_)
                && !integerq!(p_)
                && iltq!(q_, 0)
                && igtq!(rubi_log_base(&Atom::num(2), &(&nn_ / &n_)), 0)
        },
        rhs: {
            let expanded_to_sum = rubi_expand_to_sum(
                &(&c__ - &d__ * x_.pow(&n_)).pow(-&q_),
                x_,
            );
            let quotient = (&a__ + &b__ * x_.pow(&nn_)).pow(&p_)
                / (c__.pow(2) - d__.pow(2) * x_.pow(Atom::num(2) * &n_)).pow(-&q_);
            let recursive_integrand = x_.pow(&m_) * expanded_to_sum * quotient;

            rubi_star((&e__ * x_).pow(&m_), rubi_rhs_int(&recursive_integrand, x_)
                    / x_.pow(&m_))
        },
    ));
}

fn push_rules_rule_2586(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 2586,
        source: "Int[x_^m_./(c_+d_.*x_^n_+e_.*Sqrt[a_+b_.*x_^n_]),x_Symbol] :=
          1/n \\[Star] Subst[Int[x^((m+1)/n-1)/(c+d*x+e*Sqrt[a+b*x]),x],x,x^n] /;
        FreeQ[{a,b,c,d,e,m,n},x] && EqQ[b*c-a*d,0] && IntegerQ[(m+1)/n]",
        desc: "Integration by substitution",
        refs: [],
        pattern: x_.pow(m_)
            / (c__ + d__ * x_.pow(n_) + e__ * (a__ + b__ * x_.pow(n_)).sqrt()),
        with: [m_, c__, d__, n_, e__, a__, b__, x_],
        optional: [m_, d__, e__, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_], x_)
                && eqq!(&b__ * &c__ - &a__ * &d__, 0)
                && integerq!((&m_ + 1) / &n_)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = sub_atom.pow((&m_ + 1) / &n_ - 1)
                / (&c__ + &d__ * &sub_atom + &e__ * (&a__ + &b__ * &sub_atom).sqrt());
            let transformed = rubi_rhs_int(&transformed_integrand, sub);
            rubi_star(Atom::num(1) / &n_, rubi_subst(&transformed, sub, x_.pow(&n_)))
        },
    ));
}

fn push_rules_rule_2587(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, n_, u__, x_);
    rules.push(rubi_rule!(
        order: 2587,
        source: "Int[u_./(c_+d_.*x_^n_+e_.*Sqrt[a_+b_.*x_^n_]),x_Symbol] :=
          c \\[Star] Int[u/(c^2-a*e^2+c*d*x^n),x] - a*e \\[Star] Int[u/((c^2-a*e^2+c*d*x^n)*Sqrt[a+b*x^n]),x] /;
        FreeQ[{a,b,c,d,e,n},x] && EqQ[b*c-a*d,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: u__
            / (c__ + d__ * x_.pow(n_) + e__ * (a__ + b__ * x_.pow(n_)).sqrt()),
        with: [u__, c__, d__, n_, e__, a__, b__, x_],
        optional: [u__, d__, e__, b__],
        when: {
            freeq!([a__, b__, c__, d__, e__, n_], x_)
                && eqq!(&b__ * &c__ - &a__ * &d__, 0)
        },
        rhs: {
            let denominator =
                c__.pow(2) - &a__ * e__.pow(2) + &c__ * &d__ * x_.pow(&n_);

            let radical = (&a__ + &b__ * x_.pow(&n_)).sqrt();
            let first_integrand = &u__ / &denominator;
            let second_integrand = &u__ / (denominator * radical);

            rubi_star(c__, rubi_rhs_int(&first_integrand, x_)) - rubi_star(&a__ * &e__, rubi_rhs_int(&second_integrand, x_))
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
    (a__ + b__ * x_.pow(3)).sqrt() / (c__ + d__ * x_)
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let x_ = symbols.x_;
    (e__ + f__ * x_) / ((c__ + d__ * x_) * (a__ + b__ * x_.pow(3)).pow(Atom::num(1) / Atom::num(3)))
}

#[inline(never)]
fn rubi_shared_pattern_2(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let x_ = symbols.x_;
    (e__ + f__ * x_) / ((c__ + d__ * x_) * (a__ + b__ * x_.pow(3)).sqrt())
}

#[inline(never)]
fn rubi_shared_pattern_3(symbols: &RubiSymbols) -> Atom {
    let g__ = symbols.g__;
    let h__ = symbols.h__;
    let m_ = symbols.m_;
    let p_ = symbols.p_;
    let pn__ = symbols.pn__;
    let x_ = symbols.x_;
    (g__ + h__ * x_).pow(m_) * pn__.pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_4(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let g__ = symbols.g__;
    let h__ = symbols.h__;
    let i__ = symbols.i__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    (g__ + h__ * x_ + i__ * x_.pow(2)).pow(m_)
        * (d__ + e__ * x_ + f__ * (a__ + b__ * x_ + c__ * x_.pow(2)).sqrt()).pow(n_)
}

#[inline(never)]
fn rubi_shared_pattern_5(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let g__ = symbols.g__;
    let i__ = symbols.i__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    (g__ + i__ * x_.pow(2)).pow(m_)
        * (d__ + e__ * x_ + f__ * (a__ + c__ * x_.pow(2)).sqrt()).pow(n_)
}

#[inline(never)]
fn rubi_shared_pattern_6(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let x_ = symbols.x_;
    Atom::num(1) / ((a__ + b__ * x_.pow(3)) * (d__ + e__ * x_ + f__ * x_.pow(2)).sqrt())
}

#[inline(never)]
fn rubi_shared_pattern_7(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let d__ = symbols.d__;
    let f__ = symbols.f__;
    let x_ = symbols.x_;
    Atom::num(1) / ((a__ + b__ * x_.pow(3)) * (d__ + f__ * x_.pow(2)).sqrt())
}

#[inline(never)]
fn rubi_shared_pattern_8(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let x_ = symbols.x_;
    Atom::num(1) / ((c__ + d__ * x_) * (a__ + b__ * x_.pow(3)).pow(Atom::num(1) / Atom::num(3)))
}

#[inline(never)]
fn rubi_shared_pattern_9(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let x_ = symbols.x_;
    Atom::num(1) / ((c__ + d__ * x_) * (a__ + b__ * x_.pow(3)).sqrt())
}

#[inline(never)]
fn rubi_shared_pattern_10(symbols: &RubiSymbols) -> Atom {
    let m_ = symbols.m_;
    let p_ = symbols.p_;
    let pn__ = symbols.pn__;
    let u_ = symbols.u_;
    u_.pow(m_) * pn__.pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_11(symbols: &RubiSymbols) -> Atom {
    let p_ = symbols.p_;
    let px_ = symbols.px_;
    let u__ = symbols.u__;
    u__ * px_.pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_12(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let u__ = symbols.u__;
    let x_ = symbols.x_;
    u__ / (e__ * (a__ + b__ * x_).sqrt() + f__ * (c__ + d__ * x_).sqrt())
}
