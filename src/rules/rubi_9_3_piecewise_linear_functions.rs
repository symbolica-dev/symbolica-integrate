use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_2588(rules);
    push_rules_rule_2589(rules);
    push_rules_rule_2590(rules);
    push_rules_rule_2591(rules);
    push_rules_rule_2592(rules);
    push_rules_rule_2593(rules);
    push_rules_rule_2594(rules);
    push_rules_rule_2595(rules);
    push_rules_rule_2596(rules);
    push_rules_rule_2597(rules);
    push_rules_rule_2598(rules);
    push_rules_rule_2599(rules);
    push_rules_rule_2600(rules);
    push_rules_rule_2601(rules);
    push_rules_rule_2602(rules);
    push_rules_rule_2603(rules);
    push_rules_rule_2604(rules);
    push_rules_rule_2605(rules);
    // Rubi 9.3 block 17 is commented out in the markdown source.

    push_rules_rule_2606(rules);
}

fn push_rules_rule_2588(rules: &mut Vec<RubiRule>) {
    rubi_symb!(m_, u_);
    rules.push(rubi_rule!(
        order: 2588,
        source: "Int[u_^m_.,x_Symbol] :=
          With[{c=Simplify[D[u,x]]},
          1/c \\[Star] Subst[Int[x^m,x],x,u]] /;
        FreeQ[m,x] && PiecewiseLinearQ[u,x]",
        desc: "Integration by substitution",
        refs: [],
        pattern: Atom::var(u_).pow(m_),
        with: [u_, m_, x_],
        optional: [m_],
        when: { freeq!(m_, x_) && rubi_piecewise_linear_q(&u_, x_) },
        rhs: {
            let c = rubi_slope(&u_, x_);
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let substitution_symbol = substitution_guard.symbol();
            let primitive = rubi_rhs_int(&Atom::var(substitution_symbol).pow(&m_), substitution_symbol);
            let substituted = rubi_subst(&primitive, substitution_symbol, u_);
            rubi_star(Atom::num(1) / c, substituted)
        },
    ));
}

fn push_rules_rule_2589(rules: &mut Vec<RubiRule>) {
    rubi_symb!(u_, v_);
    rules.push(rubi_rule!(
        order: 2589,
        source: "Int[v_/u_,x_Symbol] :=
          With[{a=Simplify[D[u,x]],b=Simplify[D[v,x]]},
          b*x/a - (b*u-a*v)/a \\[Star] Int[1/u,x] /;
         NeQ[b*u-a*v,0]] /;
        PiecewiseLinearQ[u,v,x]",
        desc: "Inverted integration by parts",
        refs: [],
        pattern: Atom::var(v_) / Atom::var(u_),
        with: [v_, u_, x_],
        when: {
            rubi_piecewise_linear_pair_q(&u_, &v_, x_) && {
                let (_a, _b, det) = rubi_piecewise_linear_pair_data(&u_, &v_, x_);
                neq!(det, 0)
            }
        },
        rhs: {
            let (a, b, det) = rubi_piecewise_linear_pair_data(&u_, &v_, x_);
            let recursive = rubi_rhs_int(&(Atom::num(1) / u_), x_);
            rubi_simp(&(&b * x_ / &a), x_)
                    - rubi_star(det, recursive / &a)
        },
    ));
}

fn push_rules_rule_2590(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; n_, u_, v_);
    rules.push(rubi_rule!(
        order: 2590,
        source: "Int[v_^n_/u_,x_Symbol] :=
          With[{a=Simplify[D[u,x]],b=Simplify[D[v,x]]},
          v^n/(a*n) - (b*u-a*v)/a \\[Star] Int[v^(n-1)/u,x] /;
         NeQ[b*u-a*v,0]] /;
        PiecewiseLinearQ[u,v,x] && GtQ[n,0] && NeQ[n,1]",
        desc: "Inverted integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [v_, n_, u_, x_],
        when: {
            rubi_piecewise_linear_pair_q(&u_, &v_, x_)
                && gtq!(n_, 0)
                && neq!(n_, 1)
                && {
                    let (_a, _b, det) = rubi_piecewise_linear_pair_data(&u_, &v_, x_);
                    neq!(det, 0)
                }
        },
        rhs: {
            let (a, _b, det) = rubi_piecewise_linear_pair_data(&u_, &v_, x_);
            let recursive = rubi_rhs_int(&(v_.pow(&n_ - 1) / u_), x_);
            rubi_simp(&(v_.pow(&n_) / (&a * &n_)), x_)
                    - rubi_star(det, recursive / a)
        },
    ));
}

fn push_rules_rule_2591(rules: &mut Vec<RubiRule>) {
    rubi_symb!(u_, v_);
    rules.push(rubi_rule!(
        order: 2591,
        source: "Int[1/(u_*v_),x_Symbol] :=
          With[{a=Simplify[D[u,x]],b=Simplify[D[v,x]]},
          b/(b*u-a*v) \\[Star] Int[1/v,x] - a/(b*u-a*v) \\[Star] Int[1/u,x] /;
         NeQ[b*u-a*v,0]] /;
        PiecewiseLinearQ[u,v,x]",
        desc: "Algebraic expansion and piecewise constant extraction",
        refs: [],
        pattern: Atom::num(1) / (Atom::var(u_) * Atom::var(v_)),
        with: [u_, v_, x_],
        when: {
            rubi_piecewise_linear_pair_q(&u_, &v_, x_) && {
                let (_a, _b, det) = rubi_piecewise_linear_pair_data(&u_, &v_, x_);
                neq!(det, 0)
            }
        },
        rhs: {
            let (a, b, det) = rubi_piecewise_linear_pair_data(&u_, &v_, x_);
            let first = rubi_rhs_int(&(Atom::num(1) / v_), x_);
            let second = rubi_rhs_int(&(Atom::num(1) / u_), x_);
            rubi_star(b, first / &det)
                    - rubi_star(a, second / det)
        },
    ));
}

fn push_rules_rule_2592(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; u_, v_);
    rules.push(rubi_rule!(
        order: 2592,
        source: "Int[1/(u_*Sqrt[v_]),x_Symbol] :=
          With[{a=Simplify[D[u,x]],b=Simplify[D[v,x]]},
          2*ArcTan[Sqrt[v]/Rt[(b*u-a*v)/a,2]]/(a*Rt[(b*u-a*v)/a,2]) /;
         NeQ[b*u-a*v,0] && PosQ[(b*u-a*v)/a]] /;
        PiecewiseLinearQ[u,v,x]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [u_, v_, x_],
        when: {
            rubi_piecewise_linear_pair_q(&u_, &v_, x_) && {
                let (a, _b, det) = rubi_piecewise_linear_pair_data(&u_, &v_, x_);
                neq!(det, 0) && posq!(&det / &a)
            }
        },
        rhs: {
            let (a, _b, det) = rubi_piecewise_linear_pair_data(&u_, &v_, x_);
            let rt = rubi_rt(&(det / &a), 2);
            rubi_simp(
                &(Atom::num(2) * (v_.sqrt() / &rt).atan() / (a * rt)),
                x_,
            )
        },
    ));
}

fn push_rules_rule_2593(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; u_, v_);
    rules.push(rubi_rule!(
        order: 2593,
        source: "Int[1/(u_*Sqrt[v_]),x_Symbol] :=
          With[{a=Simplify[D[u,x]],b=Simplify[D[v,x]]},
          -2*ArcTanh[Sqrt[v]/Rt[-(b*u-a*v)/a,2]]/(a*Rt[-(b*u-a*v)/a,2]) /;
         NeQ[b*u-a*v,0] && NegQ[(b*u-a*v)/a]] /;
        PiecewiseLinearQ[u,v,x]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [u_, v_, x_],
        when: {
            rubi_piecewise_linear_pair_q(&u_, &v_, x_) && {
                let (a, _b, det) = rubi_piecewise_linear_pair_data(&u_, &v_, x_);
                neq!(det, 0) && negq!(&det / &a)
            }
        },
        rhs: {
            let (a, _b, det) = rubi_piecewise_linear_pair_data(&u_, &v_, x_);
            let rt = rubi_rt(&(-det / &a), 2);
            rubi_simp(
                &(-Atom::num(2) * (v_.sqrt() / &rt).atanh() / (a * rt)),
                x_,
            )
        },
    ));
}

fn push_rules_rule_2594(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; n_, u_, v_);
    rules.push(rubi_rule!(
        order: 2594,
        source: "Int[v_^n_/u_,x_Symbol] :=
          With[{a=Simplify[D[u,x]],b=Simplify[D[v,x]]},
          v^(n+1)/((n+1)*(b*u-a*v)) -
          a*(n+1)/((n+1)*(b*u-a*v)) \\[Star] Int[v^(n+1)/u,x] /;
         NeQ[b*u-a*v,0]] /;
        PiecewiseLinearQ[u,v,x] && LtQ[n,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [v_, n_, u_, x_],
        when: {
            rubi_piecewise_linear_pair_q(&u_, &v_, x_)
                && ltq!(n_, -1)
                && {
                    let (_a, _b, det) = rubi_piecewise_linear_pair_data(&u_, &v_, x_);
                    neq!(det, 0)
                }
        },
        rhs: {
            let (a, _b, det) = rubi_piecewise_linear_pair_data(&u_, &v_, x_);
            let recursive = rubi_rhs_int(&(v_.pow(&n_ + 1) / u_), x_);
            let multiplier = &a * (&n_ + 1) / ((&n_ + 1) * &det);
            rubi_simp(&(v_.pow(&n_ + 1) / ((&n_ + 1) * &det)), x_)
                    - rubi_star(multiplier, recursive)
        },
    ));
}

fn push_rules_rule_2595(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; n_, u_, v_);
    rules.push(rubi_rule!(
        order: 2595,
        source: "Int[v_^n_/u_,x_Symbol] :=
          With[{a=Simplify[D[u,x]],b=Simplify[D[v,x]]},
          v^(n+1)/((n+1)*(b*u-a*v))*Hypergeometric2F1[1,n+1,n+2,-a*v/(b*u-a*v)] /;
         NeQ[b*u-a*v,0]] /;
        PiecewiseLinearQ[u,v,x] && Not[IntegerQ[n]]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [v_, n_, u_, x_],
        when: {
            rubi_piecewise_linear_pair_q(&u_, &v_, x_)
                && !integerq!(n_)
                && {
                    let (_a, _b, det) = rubi_piecewise_linear_pair_data(&u_, &v_, x_);
                    neq!(det, 0)
                }
        },
        rhs: {
            let (a, _b, det) = rubi_piecewise_linear_pair_data(&u_, &v_, x_);
            rubi_simp(
                &(v_.pow(&n_ + 1) / ((&n_ + 1) * &det)
                    * rubi_hypergeometric2f1(
                        Atom::num(1),
                        &n_ + 1,
                        &n_ + 2,
                        -a * v_ / det,
                    )),
                x_,
            )
        },
    ));
}

fn push_rules_rule_2596(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; u_, v_);
    rules.push(rubi_rule!(
        order: 2596,
        source: "Int[1/(Sqrt[u_]*Sqrt[v_]),x_Symbol] :=
          With[{a=Simplify[D[u,x]],b=Simplify[D[v,x]]},
          2/Rt[a*b,2]*ArcTanh[Rt[a*b,2]*Sqrt[u]/(a*Sqrt[v])] /;
         NeQ[b*u-a*v,0] && PosQ[a*b]] /;
        PiecewiseLinearQ[u,v,x]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [u_, v_, x_],
        when: {
            rubi_piecewise_linear_pair_q(&u_, &v_, x_) && {
                let (a, b, det) = rubi_piecewise_linear_pair_data(&u_, &v_, x_);
                neq!(det, 0) && posq!(&a * &b)
            }
        },
        rhs: {
            let (a, b, _det) = rubi_piecewise_linear_pair_data(&u_, &v_, x_);
            let rt = rubi_rt(&(&a * &b), 2);
            rubi_simp(
                &(Atom::num(2) / &rt * (&rt * u_.sqrt() / (a * v_.sqrt())).atanh()),
                x_,
            )
        },
    ));
}

fn push_rules_rule_2597(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; u_, v_);
    rules.push(rubi_rule!(
        order: 2597,
        source: "Int[1/(Sqrt[u_]*Sqrt[v_]),x_Symbol] :=
          With[{a=Simplify[D[u,x]],b=Simplify[D[v,x]]},
          2/Rt[-a*b,2]*ArcTan[Rt[-a*b,2]*Sqrt[u]/(a*Sqrt[v])] /;
         NeQ[b*u-a*v,0] && NegQ[a*b]] /;
        PiecewiseLinearQ[u,v,x]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [u_, v_, x_],
        when: {
            rubi_piecewise_linear_pair_q(&u_, &v_, x_) && {
                let (a, b, det) = rubi_piecewise_linear_pair_data(&u_, &v_, x_);
                neq!(det, 0) && negq!(&a * &b)
            }
        },
        rhs: {
            let (a, b, _det) = rubi_piecewise_linear_pair_data(&u_, &v_, x_);
            let rt = rubi_rt(&(-&a * &b), 2);
            rubi_simp(
                &(Atom::num(2) / &rt * (&rt * u_.sqrt() / (a * v_.sqrt())).atan()),
                x_,
            )
        },
    ));
}

fn push_rules_rule_2598(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; m_, n_, u_, v_);
    rules.push(rubi_rule!(
        order: 2598,
        source: "Int[u_^m_*v_^n_,x_Symbol] :=
          With[{a=Simplify[D[u,x]],b=Simplify[D[v,x]]},
          -u^(m+1)*v^(n+1)/((m+1)*(b*u-a*v)) /;
         NeQ[b*u-a*v,0]] /;
        FreeQ[{m,n},x] && PiecewiseLinearQ[u,v,x] && EqQ[m+n+2,0] && NeQ[m,-1]",
        desc: "Piecewise linear recurrence 3 with m+n+2\\[Equal]0",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [u_, m_, v_, n_, x_],
        when: {
            freeq!([m_, n_], x_)
                && rubi_piecewise_linear_pair_q(&u_, &v_, x_)
                && eqq!(&m_ + &n_ + 2, 0)
                && neq!(m_, -1)
                && {
                    let (_a, _b, det) = rubi_piecewise_linear_pair_data(&u_, &v_, x_);
                    neq!(det, 0)
                }
        },
        rhs: {
            let (_a, _b, det) = rubi_piecewise_linear_pair_data(&u_, &v_, x_);
            rubi_simp(
                &(-u_.pow(&m_ + 1) * v_.pow(&n_ + 1) / ((&m_ + 1) * det)),
                x_,
            )
        },
    ));
}

fn push_rules_rule_2599(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; m_, n_, u_, v_);
    rules.push(rubi_rule!(
        order: 2599,
        source: "Int[u_^m_*v_^n_.,x_Symbol] :=
          With[{a=Simplify[D[u,x]],b=Simplify[D[v,x]]},
          u^(m+1)*v^n/(a*(m+1)) -
          b*n/(a*(m+1)) \\[Star] Int[u^(m+1)*v^(n-1),x] /;
         NeQ[b*u-a*v,0]] /;
        FreeQ[{m,n},x] && PiecewiseLinearQ[u,v,x] (* && NeQ[m+n+2,0] *) && NeQ[m,-1] && (
          LtQ[m,-1] && GtQ[n,0] && Not[ILtQ[m+n,-2] && (FractionQ[m] || GeQ[2*n+m+1,0])] ||
          IGtQ[n,0] && IGtQ[m,0] && LeQ[n,m] ||
        (* ILtQ[n,0] && ILtQ[m,0] && LeQ[n,m] || *)
          IGtQ[n,0] && Not[IntegerQ[m]] ||
          ILtQ[m,0] && Not[IntegerQ[n]])",
        desc: "Inverted integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [u_, m_, v_, n_, x_],
        optional: [n_],
        when: {
            freeq!([m_, n_], x_)
                && rubi_piecewise_linear_pair_q(&u_, &v_, x_)
                && neq!(m_, -1)
                && ((ltq!(m_, -1)
                    && gtq!(n_, 0)
                    && !(iltq!(&m_ + &n_, -2) && (fractionq!(m_) || geq!(Atom::num(2) * &n_ + &m_ + 1, 0))))
                    || igtq!(n_, 0) && igtq!(m_, 0) && leq!(n_, m_)
                    || igtq!(n_, 0) && !integerq!(m_)
                    || iltq!(m_, 0) && !integerq!(n_))
                && {
                    let (_a, _b, det) = rubi_piecewise_linear_pair_data(&u_, &v_, x_);
                    neq!(det, 0)
                }
        },
        rhs: {
            let (a, b, _det) = rubi_piecewise_linear_pair_data(&u_, &v_, x_);
            let recursive = rubi_rhs_int(&(u_.pow(&m_ + 1) * v_.pow(&n_ - 1)), x_);
            let multiplier = &b * &n_ / (&a * (&m_ + 1));
            rubi_simp(
                    &(u_.pow(&m_ + 1) * v_.pow(&n_) / (&a * (&m_ + 1))),
                    x_,
                ) - rubi_star(multiplier, recursive)
        },
    ));
}

fn push_rules_rule_2600(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; m_, n_, u_, v_);
    rules.push(rubi_rule!(
        order: 2600,
        source: "Int[u_^m_*v_^n_.,x_Symbol] :=
          With[{a=Simplify[D[u,x]],b=Simplify[D[v,x]]},
          u^(m+1)*v^n/(a*(m+n+1)) -
          n*(b*u-a*v)/(a*(m+n+1)) \\[Star] Int[u^m*v^(n-1),x] /;
         NeQ[b*u-a*v,0]] /;
        PiecewiseLinearQ[u,v,x] && NeQ[m+n+2,0] && GtQ[n,0] && NeQ[m+n+1,0] &&
          Not[IGtQ[m,0] && (Not[IntegerQ[n]] || LtQ[0,m,n])] &&
          Not[ILtQ[m+n,-2]]",
        desc: "Inverted integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [u_, m_, v_, n_, x_],
        optional: [n_],
        when: {
            rubi_piecewise_linear_pair_q(&u_, &v_, x_)
                && neq!(&m_ + &n_ + 2, 0)
                && gtq!(n_, 0)
                && neq!(&m_ + &n_ + 1, 0)
                && !(igtq!(m_, 0) && (!integerq!(n_) || gtq!(m_, 0) && ltq!(m_, n_)))
                && !iltq!(&m_ + &n_, -2)
                && {
                    let (_a, _b, det) = rubi_piecewise_linear_pair_data(&u_, &v_, x_);
                    neq!(det, 0)
                }
        },
        rhs: {
            let (a, _b, det) = rubi_piecewise_linear_pair_data(&u_, &v_, x_);
            let recursive = rubi_rhs_int(&(u_.pow(&m_) * v_.pow(&n_ - 1)), x_);
            let multiplier = &n_ * det / (&a * (&m_ + &n_ + 1));
            rubi_simp(
                    &(u_.pow(&m_ + 1) * v_.pow(&n_) / (&a * (&m_ + &n_ + 1))),
                    x_,
                ) - rubi_star(multiplier, recursive)
        },
    ));
}

fn push_rules_rule_2601(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; m_, n_, u_, v_);
    rules.push(rubi_rule!(
        order: 2601,
        source: "Int[u_^m_*v_^n_,x_Symbol] :=
          With[{a=Simplify[D[u,x]],b=Simplify[D[v,x]]},
          u^(m+1)*v^n/(a*(m+n+1)) -
          n*(b*u-a*v)/(a*(m+n+1)) \\[Star] Int[u^m*v^Simplify[n-1],x] /;
         NeQ[b*u-a*v,0]] /;
        PiecewiseLinearQ[u,v,x] && NeQ[m+n+1,0] && Not[RationalQ[n]] && SumSimplerQ[n,-1]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [u_, m_, v_, n_, x_],
        when: {
            rubi_piecewise_linear_pair_q(&u_, &v_, x_)
                && neq!(&m_ + &n_ + 1, 0)
                && !rationalq!(n_)
                && sum_simplerq!(n_, -1)
                && {
                    let (_a, _b, det) = rubi_piecewise_linear_pair_data(&u_, &v_, x_);
                    neq!(det, 0)
                }
        },
        rhs: {
            let (a, _b, det) = rubi_piecewise_linear_pair_data(&u_, &v_, x_);
            let lower_n = rubi_simplify(&(&n_ - 1));
            let recursive = rubi_rhs_int(&(u_.pow(&m_) * v_.pow(lower_n)), x_);
            let multiplier = &n_ * det / (&a * (&m_ + &n_ + 1));
            rubi_simp(
                    &(u_.pow(&m_ + 1) * v_.pow(&n_) / (&a * (&m_ + &n_ + 1))),
                    x_,
                ) - rubi_star(multiplier, recursive)
        },
    ));
}

fn push_rules_rule_2602(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; m_, n_, u_, v_);
    rules.push(rubi_rule!(
        order: 2602,
        source: "Int[u_^m_*v_^n_,x_Symbol] :=
          With[{a=Simplify[D[u,x]],b=Simplify[D[v,x]]},
          -u^(m+1)*v^(n+1)/((m+1)*(b*u-a*v)) +
          b*(m+n+2)/((m+1)*(b*u-a*v)) \\[Star] Int[u^(m+1)*v^n,x] /;
         NeQ[b*u-a*v,0]] /;
        PiecewiseLinearQ[u,v,x] && NeQ[m+n+2,0] && LtQ[m,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [u_, m_, v_, n_, x_],
        when: {
            rubi_piecewise_linear_pair_q(&u_, &v_, x_)
                && neq!(&m_ + &n_ + 2, 0)
                && ltq!(m_, -1)
                && {
                    let (_a, _b, det) = rubi_piecewise_linear_pair_data(&u_, &v_, x_);
                    neq!(det, 0)
                }
        },
        rhs: {
            let (_a, b, det) = rubi_piecewise_linear_pair_data(&u_, &v_, x_);
            let recursive = rubi_rhs_int(&(u_.pow(&m_ + 1) * v_.pow(&n_)), x_);
            rubi_simp(
                    &(-u_.pow(&m_ + 1) * v_.pow(&n_ + 1) / ((&m_ + 1) * &det)),
                    x_,
                ) + rubi_star(b * (&m_ + &n_ + 2) / ((&m_ + 1) * det), recursive)
        },
    ));
}

fn push_rules_rule_2603(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; m_, n_, u_, v_);
    rules.push(rubi_rule!(
        order: 2603,
        source: "Int[u_^m_*v_^n_,x_Symbol] :=
          With[{a=Simplify[D[u,x]],b=Simplify[D[v,x]]},
          -u^(m+1)*v^(n+1)/((m+1)*(b*u-a*v)) +
          b*(m+n+2)/((m+1)*(b*u-a*v)) \\[Star] Int[u^Simplify[m+1]*v^n,x] /;
         NeQ[b*u-a*v,0]] /;
        PiecewiseLinearQ[u,v,x] && Not[RationalQ[m]] && SumSimplerQ[m,1]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [u_, m_, v_, n_, x_],
        when: {
            rubi_piecewise_linear_pair_q(&u_, &v_, x_)
                && !rationalq!(m_)
                && sum_simplerq!(m_, 1)
                && {
                    let (_a, _b, det) = rubi_piecewise_linear_pair_data(&u_, &v_, x_);
                    neq!(det, 0)
                }
        },
        rhs: {
            let (_a, b, det) = rubi_piecewise_linear_pair_data(&u_, &v_, x_);
            let raised_m = rubi_simplify(&(&m_ + 1));
            let recursive = rubi_rhs_int(&(u_.pow(raised_m) * v_.pow(&n_)), x_);
            rubi_simp(
                    &(-u_.pow(&m_ + 1) * v_.pow(&n_ + 1) / ((&m_ + 1) * &det)),
                    x_,
                ) + rubi_star(b * (&m_ + &n_ + 2) / ((&m_ + 1) * det), recursive)
        },
    ));
}

fn push_rules_rule_2604(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; m_, n_, u_, v_);
    rules.push(rubi_rule!(
        order: 2604,
        source: "Int[u_^m_*v_^n_,x_Symbol] :=
          With[{a=Simplify[D[u,x]],b=Simplify[D[v,x]]},
          u^m*v^(n+1)/(b*(n+1)*(b*u/(b*u-a*v))^m)*Hypergeometric2F1[-m,n+1,n+2,-a*v/(b*u-a*v)] /;
         NeQ[b*u-a*v,0]] /;
        PiecewiseLinearQ[u,v,x] && Not[IntegerQ[m]] && Not[IntegerQ[n]]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [u_, m_, v_, n_, x_],
        when: {
            rubi_piecewise_linear_pair_q(&u_, &v_, x_)
                && !integerq!(m_)
                && !integerq!(n_)
                && {
                    let (_a, _b, det) = rubi_piecewise_linear_pair_data(&u_, &v_, x_);
                    neq!(det, 0)
                }
        },
        rhs: {
            let (a, b, det) = rubi_piecewise_linear_pair_data(&u_, &v_, x_);
            rubi_simp(
                &(u_.pow(&m_) * v_.pow(&n_ + 1)
                    / (&b * (&n_ + 1) * (&b * &u_ / &det).pow(&m_))
                    * rubi_hypergeometric2f1(-m_, &n_ + 1, &n_ + 2, -a * v_ / det)),
                x_,
            )
        },
    ));
}

fn push_rules_rule_2605(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, n_, u_, x_);
    rules.push(rubi_rule!(
        order: 2605,
        source: "Int[u_^n_.*Log[a_.+b_.*x_],x_Symbol] :=
          With[{c=Simplify[D[u,x]]},
          u^n*(a+b*x)*Log[a+b*x]/b -
          Int[u^n,x] -
          c*n/b \\[Star] Int[u^(n-1)*(a+b*x)*Log[a+b*x],x]] /;
        FreeQ[{a,b},x] && PiecewiseLinearQ[u,x] && Not[LinearQ[u,x]] && GtQ[n,0]",
        desc: "Integration by parts",
        refs: [],
        pattern: Atom::var(u_).pow(n_) * (a__ + b__ * x_).log(),
        with: [u_, n_, a__, b__, x_],
        optional: [n_, a__, b__],
        when: {
            freeq!([a__, b__], x_)
                && rubi_piecewise_linear_q(&u_, x_)
                && !rubi_linear_q(&u_, x_)
                && gtq!(n_, 0)
        },
        rhs: {
            let c = rubi_slope(&u_, x_);
            let linear = &a__ + &b__ * x_;
            let first = rubi_rhs_int(&u_.pow(&n_), x_);
            let second = rubi_rhs_int(&(u_.pow(&n_ - 1) * &linear * &linear.log()), x_);
            rubi_simp(
                    &(u_.pow(&n_) * &linear * &linear.log() / &b__),
                    x_,
                )
                    - first
                    - rubi_star(c * &n_ / b__, second)
        },
    ));
}

fn push_rules_rule_2606(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, m_, n_, u_, x_);
    rules.push(rubi_rule!(
        order: 2606,
        source: "Int[u_^n_.*(a_.+b_.*x_)^m_.*Log[a_.+b_.*x_],x_Symbol] :=
          With[{c=Simplify[D[u,x]]},
          u^n*(a+b*x)^(m+1)*Log[a+b*x]/(b*(m+1)) -
          1/(m+1) \\[Star] Int[u^n*(a+b*x)^m,x] -
          c*n/(b*(m+1)) \\[Star] Int[u^(n-1)*(a+b*x)^(m+1)*Log[a+b*x],x]] /;
        FreeQ[{a,b,m},x] && PiecewiseLinearQ[u,x] && Not[LinearQ[u,x]] && GtQ[n,0] && NeQ[m,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern: Atom::var(u_).pow(n_) * (a__ + b__ * x_).pow(m_) * (a__ + b__ * x_).log(),
        with: [u_, n_, a__, b__, m_, x_],
        optional: [n_, a__, b__, m_],
        when: {
            freeq!([a__, b__, m_], x_)
                && rubi_piecewise_linear_q(&u_, x_)
                && !rubi_linear_q(&u_, x_)
                && gtq!(n_, 0)
                && neq!(m_, -1)
        },
        rhs: {
            let c = rubi_slope(&u_, x_);
            let linear = &a__ + &b__ * x_;
            let first = rubi_rhs_int(&(u_.pow(&n_) * linear.pow(&m_)), x_);
            let second = rubi_rhs_int(
                &(u_.pow(&n_ - 1) * linear.pow(&m_ + 1) * &linear.log()),
                x_,
            );
            let second_multiplier = c * &n_ / (&b__ * (&m_ + 1));
            rubi_simp(
                    &(u_.pow(&n_) * linear.pow(&m_ + 1) * &linear.log()
                        / (&b__ * (&m_ + 1))),
                    x_,
                ) - rubi_star(Atom::num(1) / (&m_ + 1), first)
                    - rubi_star(second_multiplier, second)
        },
    ));
}

// Generated shared pattern builders.

#[inline(never)]
fn rubi_shared_pattern_0(symbols: &RubiSymbols) -> Atom {
    let u_ = symbols.u_;
    let v_ = symbols.v_;
    Atom::num(1) / (Atom::var(u_) * Atom::var(v_).sqrt())
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let u_ = symbols.u_;
    let v_ = symbols.v_;
    Atom::num(1) / (Atom::var(u_).sqrt() * Atom::var(v_).sqrt())
}

#[inline(never)]
fn rubi_shared_pattern_2(symbols: &RubiSymbols) -> Atom {
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let u_ = symbols.u_;
    let v_ = symbols.v_;
    Atom::var(u_).pow(m_) * Atom::var(v_).pow(n_)
}

#[inline(never)]
fn rubi_shared_pattern_3(symbols: &RubiSymbols) -> Atom {
    let n_ = symbols.n_;
    let u_ = symbols.u_;
    let v_ = symbols.v_;
    Atom::var(v_).pow(n_) / Atom::var(u_)
}
