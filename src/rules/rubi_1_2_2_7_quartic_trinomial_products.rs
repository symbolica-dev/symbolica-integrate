use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_2208(rules);
    push_rules_rule_2209(rules);
    push_rules_rule_2210(rules);
    push_rules_rule_2211(rules);
    push_rules_rule_2212(rules);
    push_rules_rule_2213(rules);
    push_rules_rule_2214(rules);
    push_rules_rule_2215(rules);
    push_rules_rule_2216(rules);
    push_rules_rule_2217(rules);
    push_rules_rule_2218(rules);
    push_rules_rule_2219(rules);
    push_rules_rule_2220(rules);
    push_rules_rule_2221(rules);
    push_rules_rule_2222(rules);
    push_rules_rule_2223(rules);
    push_rules_rule_2224(rules);
    push_rules_rule_2225(rules);
    push_rules_rule_2226(rules);
    push_rules_rule_2227(rules);
    push_rules_rule_2228(rules);
    push_rules_rule_2229(rules);
    push_rules_rule_2230(rules);
    push_rules_rule_2231(rules);
    push_rules_rule_2232(rules);
    push_rules_rule_2233(rules);
    push_rules_rule_2234(rules);
    push_rules_rule_2235(rules);
    push_rules_rule_2236(rules);
    push_rules_rule_2237(rules);
    push_rules_rule_2238(rules);
    push_rules_rule_2239(rules);
    push_rules_rule_2240(rules);
    push_rules_rule_2241(rules);
    push_rules_rule_2242(rules);
    push_rules_rule_2243(rules);
    push_rules_rule_2244(rules);
    push_rules_rule_2245(rules);
    push_rules_rule_2246(rules);
    push_rules_rule_2247(rules);
    push_rules_rule_2248(rules);
    push_rules_rule_2249(rules);
    push_rules_rule_2250(rules);
    push_rules_rule_2251(rules);
    push_rules_rule_2252(rules);
    push_rules_rule_2253(rules);
    push_rules_rule_2254(rules);
    push_rules_rule_2255(rules);
    push_rules_rule_2256(rules);
    push_rules_rule_2257(rules);
    push_rules_rule_2258(rules);
    push_rules_rule_2259(rules);
    push_rules_rule_2260(rules);
    push_rules_rule_2261(rules);
}

fn push_rules_rule_2242(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, px_, x_);
    rules.push(rubi_rule!(
        order: 2242,
        source: "Int[Px_*x_^m_/((d_+e_.*x_^2)*Sqrt[a_+b_.*x_^2+c_.*x_^4]),x_Symbol] :=
          With[{A=Coeff[Px,x,0],B=Coeff[Px,x,2],C=Coeff[Px,x,4]},
          C*x^(m-1)*Sqrt[a+b*x^2+c*x^4]/(c*e*(m+1)) -
          1/(c*e*(m+1)) \\[Star] Int[(x^(m-2)/((d+e*x^2)*Sqrt[a+b*x^2+c*x^4]))*
            Simp[a*C*d*(m-1)-(A*c*e*(m+1)-C*(a*e*(m-1)+b*d*m))*x^2-(B*c*e*(m+1)-C*(b*e*m+c*d*(m+1)))*x^4,x],x]] /;
        FreeQ[{a,b,c,d,e},x] && PolyQ[Px,x^2,2] && NeQ[b^2-4*a*c,0] && IGtQ[m/2,0]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [px_, m_, d__, e__, a__, b__, c__, x_],
        optional: [e__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && rubi_poly_q_power_degree(&px_, x_, &Atom::num(2), 2)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && igtq!(&m_ / Atom::num(2), 0)
        },
        rhs: {
            let A = rubi_coeff(&px_, x_, 0).rubi_rhs();
            let B = rubi_coeff(&px_, x_, 2).rubi_rhs();
            let C = rubi_coeff(&px_, x_, 4).rubi_rhs();
            let quadratic = &d__ + &e__ * x_.pow(2);
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let denominator = &c__ * &e__ * (&m_ + Atom::num(1));

            let direct = &C * x_.pow(&m_ - Atom::num(1)) * quartic.sqrt() / &denominator;
            let simp = rubi_simp(
                &(&a__ * &C * &d__ * (&m_ - Atom::num(1))
                    - (&A * &c__ * &e__ * (&m_ + Atom::num(1))
                        - &C * (&a__ * &e__ * (&m_ - Atom::num(1)) + &b__ * &d__ * &m_))
                        * x_.pow(2)
                    - (&B * &c__ * &e__ * (&m_ + Atom::num(1))
                        - &C * (&b__ * &e__ * &m_ + &c__ * &d__ * (&m_ + Atom::num(1))))
                        * x_.pow(4)),
                x_,
            );
            let recursive_integrand =
                x_.pow(&m_ - Atom::num(2)) * simp / (quadratic * quartic.sqrt());
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) - rubi_star(Atom::num(1) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_2243(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, m_, px_, x_);
    rules.push(rubi_rule!(
        order: 2243,
        source: "Int[Px_*x_^m_/((d_+e_.*x_^2)*Sqrt[a_+c_.*x_^4]),x_Symbol] :=
          With[{A=Coeff[Px,x,0],B=Coeff[Px,x,2],C=Coeff[Px,x,4]},
          C*x^(m-1)*Sqrt[a+c*x^4]/(c*e*(m+1)) -
          1/(c*e*(m+1)) \\[Star] Int[(x^(m-2)/((d+e*x^2)*Sqrt[a+c*x^4]))*
            Simp[a*C*d*(m-1)-(A*c*e*(m+1)-C*a*e*(m-1))*x^2-(B*c*e*(m+1)-C*c*d*(m+1))*x^4,x],x]] /;
        FreeQ[{a,c,d,e},x] && PolyQ[Px,x^2,2] && IGtQ[m/2,0]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [px_, m_, d__, e__, a__, c__, x_],
        optional: [e__, c__],
        when: {
            freeq!([a__, c__, d__, e__], x_)
                && rubi_poly_q_power_degree(&px_, x_, &Atom::num(2), 2)
                && igtq!(&m_ / Atom::num(2), 0)
        },
        rhs: {
            let A = rubi_coeff(&px_, x_, 0).rubi_rhs();
            let B = rubi_coeff(&px_, x_, 2).rubi_rhs();
            let C = rubi_coeff(&px_, x_, 4).rubi_rhs();
            let quadratic = &d__ + &e__ * x_.pow(2);
            let quartic = &a__ + &c__ * x_.pow(4);
            let denominator = &c__ * &e__ * (&m_ + Atom::num(1));

            let direct = &C * x_.pow(&m_ - Atom::num(1)) * quartic.sqrt() / &denominator;
            let simp = rubi_simp(
                &(&a__ * &C * &d__ * (&m_ - Atom::num(1))
                    - (&A * &c__ * &e__ * (&m_ + Atom::num(1)) - &C * &a__ * &e__ * (&m_ - Atom::num(1)))
                        * x_.pow(2)
                    - (&B * &c__ * &e__ * (&m_ + Atom::num(1)) - &C * &c__ * &d__ * (&m_ + Atom::num(1)))
                        * x_.pow(4)),
                x_,
            );
            let recursive_integrand =
                x_.pow(&m_ - Atom::num(2)) * simp / (quadratic * quartic.sqrt());
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) - rubi_star(Atom::num(1) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_2244(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, px_, x_);
    rules.push(rubi_rule!(
        order: 2244,
        source: "Int[Px_*x_^m_/((d_+e_.*x_^2)*Sqrt[a_+b_.*x_^2+c_.*x_^4]),x_Symbol] :=
          With[{A=Coeff[Px,x,0],B=Coeff[Px,x,2],C=Coeff[Px,x,4]},
          A*x^(m+1)*Sqrt[a+b*x^2+c*x^4]/(a*d*(m+1)) +
          1/(a*d*(m+1)) \\[Star] Int[(x^(m+2)/((d+e*x^2)*Sqrt[a+b*x^2+c*x^4]))*
            Simp[a*B*d*(m+1)-A*(a*e*(m+1)+b*d*(m+2))+(a*C*d*(m+1)-A*(b*e*(m+2)+c*d*(m+3)))*x^2-A*c*e*(m+3)*x^4,x],x]] /;
        FreeQ[{a,b,c,d,e},x] && PolyQ[Px,x^2,2] && NeQ[b^2-4*a*c,0] && ILtQ[m/2,0]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [px_, m_, d__, e__, a__, b__, c__, x_],
        optional: [e__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && rubi_poly_q_power_degree(&px_, x_, &Atom::num(2), 2)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && iltq!(&m_ / Atom::num(2), 0)
        },
        rhs: {
            let A = rubi_coeff(&px_, x_, 0).rubi_rhs();
            let B = rubi_coeff(&px_, x_, 2).rubi_rhs();
            let C = rubi_coeff(&px_, x_, 4).rubi_rhs();
            let quadratic = &d__ + &e__ * x_.pow(2);
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let denominator = &a__ * &d__ * (&m_ + Atom::num(1));

            let direct = &A * x_.pow(&m_ + Atom::num(1)) * quartic.sqrt() / &denominator;
            let simp = rubi_simp(
                &(&a__ * &B * &d__ * (&m_ + Atom::num(1))
                    - &A * (&a__ * &e__ * (&m_ + Atom::num(1)) + &b__ * &d__ * (&m_ + Atom::num(2)))
                    + (&a__ * &C * &d__ * (&m_ + Atom::num(1))
                        - &A * (&b__ * &e__ * (&m_ + Atom::num(2)) + &c__ * &d__ * (&m_ + Atom::num(3))))
                        * x_.pow(2)
                    - &A * &c__ * &e__ * (&m_ + Atom::num(3)) * x_.pow(4)),
                x_,
            );
            let recursive_integrand =
                x_.pow(&m_ + Atom::num(2)) * simp / (quadratic * quartic.sqrt());
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_2245(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, m_, px_, x_);
    rules.push(rubi_rule!(
        order: 2245,
        source: "Int[Px_*x_^m_/((d_+e_.*x_^2)*Sqrt[a_+c_.*x_^4]),x_Symbol] :=
          With[{A=Coeff[Px,x,0],B=Coeff[Px,x,2],C=Coeff[Px,x,4]},
          A*x^(m+1)*Sqrt[a+c*x^4]/(a*d*(m+1)) +
          1/(a*d*(m+1)) \\[Star] Int[(x^(m+2)/((d+e*x^2)*Sqrt[a+c*x^4]))*
            Simp[a*B*d*(m+1)-A*a*e*(m+1)+(a*C*d*(m+1)-A*c*d*(m+3))*x^2-A*c*e*(m+3)*x^4,x],x]] /;
        FreeQ[{a,c,d,e},x] && PolyQ[Px,x^2,2] && ILtQ[m/2,0]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [px_, m_, d__, e__, a__, c__, x_],
        optional: [e__, c__],
        when: {
            freeq!([a__, c__, d__, e__], x_)
                && rubi_poly_q_power_degree(&px_, x_, &Atom::num(2), 2)
                && iltq!(&m_ / Atom::num(2), 0)
        },
        rhs: {
            let A = rubi_coeff(&px_, x_, 0).rubi_rhs();
            let B = rubi_coeff(&px_, x_, 2).rubi_rhs();
            let C = rubi_coeff(&px_, x_, 4).rubi_rhs();
            let quadratic = &d__ + &e__ * x_.pow(2);
            let quartic = &a__ + &c__ * x_.pow(4);
            let denominator = &a__ * &d__ * (&m_ + Atom::num(1));

            let direct = &A * x_.pow(&m_ + Atom::num(1)) * quartic.sqrt() / &denominator;
            let simp = rubi_simp(
                &(&a__ * &B * &d__ * (&m_ + Atom::num(1))
                    - &A * &a__ * &e__ * (&m_ + Atom::num(1))
                    + (&a__ * &C * &d__ * (&m_ + Atom::num(1))
                        - &A * &c__ * &d__ * (&m_ + Atom::num(3)))
                        * x_.pow(2)
                    - &A * &c__ * &e__ * (&m_ + Atom::num(3)) * x_.pow(4)),
                x_,
            );
            let recursive_integrand =
                x_.pow(&m_ + Atom::num(2)) * simp / (quadratic * quartic.sqrt());
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_2238(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, px__, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 2238,
        source: "Int[x_*Px_*(d_+e_.*x_^2)^q_.*(a_+b_.*x_^2+c_.*x_^4)^p_.,x_Symbol] :=
          1/2 \\[Star] Subst[Int[ReplaceAll[Px,x->Sqrt[x]]*(d+e*x)^q*(a+b*x+c*x^2)^p,x],x,x^2] /;
        FreeQ[{a,b,c,d,e,p,q},x] && PolyQ[Px,x^2]",
        desc: "Integration by substitution",
        refs: [],
        pattern: x_ * px__ * (d__ + e__ * x_.pow(2)).pow(q_) * (a__ + b__ * x_.pow(2) + c__ * x_.pow(4)).pow(p_),
        with: [px__, d__, e__, q_, a__, b__, c__, p_, x_],
        optional: [e__, q_, b__, c__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, p_, q_], x_)
                && rubi_poly_q_power(&px__, x_, &Atom::num(2))
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_px = rubi_replace_all(&px__, x_, sub_atom.sqrt());
            let transformed_integrand = transformed_px
                * (&d__ + &e__ * &sub_atom).pow(&q_)
                * (&a__ + &b__ * &sub_atom + &c__ * sub_atom.pow(2)).pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);
            let substituted = rubi_subst(&transformed, sub, x_.pow(2));

            rubi_star(Atom::num(1) / 2, substituted)
        },
    ));
}

fn push_rules_rule_2254(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, p_, pr__, q_, x_);
    rules.push(rubi_rule!(
        order: 2254,
        source: "Int[Pr_*(d_+e_.*x_^2)^q_.*(a_+b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
          Module[{r=Expon[Pr,x],k},
          Int[Sum[Coeff[Pr,x,2*k]*x^(2*k),{k,0,r/2}]*(d+e*x^2)^q*(a+b*x^2+c*x^4)^p,x] +
          Int[x*Sum[Coeff[Pr,x,2*k+1]*x^(2*k),{k,0,(r-1)/2}]*(d+e*x^2)^q*(a+b*x^2+c*x^4)^p,x]] /;
        FreeQ[{a,b,c,d,e,p,q},x] && PolyQ[Pr,x] && Not[PolyQ[Pr,x^2]]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern: pr__ * (d__ + e__ * x_.pow(2)).pow(q_) * (a__ + b__ * x_.pow(2) + c__ * x_.pow(4)).pow(p_),
        with: [pr__, d__, e__, q_, a__, b__, c__, p_, x_],
        optional: [e__, q_, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__, p_, q_], x_)
                && rubi_poly_q(&pr__, x_)
                && !rubi_poly_q_power(&pr__, x_, &Atom::num(2))
        },
        rhs: {
            let r = rubi_expon(&pr__, x_).rubi_rhs();
            let quadratic = &d__ + &e__ * x_.pow(2);
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);

            let mut even_sum = Atom::num(0);
            for k in 0..=(r / 2) {
                even_sum += rubi_coeff(&pr__, x_, 2 * k).rubi_rhs() * x_.pow(2 * k);
            }

            let mut odd_sum = Atom::num(0);
            if r >= 1 {
                for k in 0..=((r - 1) / 2) {
                    odd_sum += rubi_coeff(&pr__, x_, 2 * k + 1).rubi_rhs() * x_.pow(2 * k);
                }
            }

            let first = rubi_rhs_int(
                &(even_sum * quadratic.pow(&q_) * quartic.pow(&p_)),
                x_,
            );
            let second = rubi_rhs_int(
                &(x_ * odd_sum * quadratic.pow(&q_) * quartic.pow(&p_)),
                x_,
            );

            first + second
        },
    ));
}

fn push_rules_rule_2256(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, px__, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 2256,
        source: "Int[Px_*(d_+e_.*x_^2)^q_.*(a_+b_.*x_^2+c_.*x_^4)^p_.,x_Symbol] :=
          Int[ExpandIntegrand[Px*(d+e*x^2)^q*(a+b*x^2+c*x^4)^p,x],x] /;
        FreeQ[{a,b,c,d,e,q},x] && PolyQ[Px,x] && IntegerQ[p]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [px__, d__, e__, q_, a__, b__, c__, p_, x_],
        optional: [e__, q_, b__, c__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, q_], x_)
                && rubi_poly_q(&px__, x_)
                && integerq!(p_)
        },
        rhs: {
            let integrand = px__
                * (&d__ + &e__ * x_.pow(2)).pow(&q_)
                * (&a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4)).pow(&p_);
            let expanded = rubi_expand_integrand(&integrand, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_2257(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, px__, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 2257,
        source: "Int[Px_*(d_+e_.*x_^2)^q_.*(a_+c_.*x_^4)^p_.,x_Symbol] :=
          Int[ExpandIntegrand[Px*(d+e*x^2)^q*(a+c*x^4)^p,x],x] /;
        FreeQ[{a,c,d,e,q},x] && PolyQ[Px,x] && IntegerQ[p]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [px__, d__, e__, q_, a__, c__, p_, x_],
        optional: [e__, q_, c__, p_],
        when: {
            freeq!([a__, c__, d__, e__, q_], x_)
                && rubi_poly_q(&px__, x_)
                && integerq!(p_)
        },
        rhs: {
            let integrand = px__
                * (&d__ + &e__ * x_.pow(2)).pow(&q_)
                * (&a__ + &c__ * x_.pow(4)).pow(&p_);
            let expanded = rubi_expand_integrand(&integrand, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_2252(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, px__, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 2252,
        source: "Int[Px_*(d_+e_.*x_^2)^q_.*(a_+b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
          With[{m=Expon[Px,x,Min]},
          Int[x^m*ExpandToSum[Px/x^m,x]*(d+e*x^2)^q*(a+b*x^2+c*x^4)^p,x] /;
         GtQ[m,0] && Not[MatchQ[Px,x^m*u_.]]] /;
        FreeQ[{a,b,c,d,e,p,q},x] && PolyQ[Px,x]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [px__, d__, e__, q_, a__, b__, c__, p_, x_],
        optional: [e__, q_, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__, p_, q_], x_)
                && rubi_poly_q(&px__, x_)
                && rubi_minimum_monomial_exponent(&px__, x_).is_some_and(|m| {
                    gtq!(Atom::num(m), 0)
                        && !visible_integer_power_of_variable_factor(&px__, x_)
                })
        },
        rhs: {
            let m = rubi_minimum_monomial_exponent(&px__, x_).rubi_rhs();
            let expanded = rubi_expand_to_sum(&(&px__ / x_.pow(m)), x_);
            rubi_rhs_int(
                &(x_.pow(m)
                    * expanded
                    * (&d__ + &e__ * x_.pow(2)).pow(&q_)
                    * (&a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4)).pow(&p_)),
                x_,
            )
        },
    ));
}

fn push_rules_rule_2253(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, px__, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 2253,
        source: "Int[Px_*(d_+e_.*x_^2)^q_.*(a_+c_.*x_^4)^p_,x_Symbol] :=
          With[{m=Expon[Px,x,Min]},
          Int[x^m*ExpandToSum[Px/x^m,x]*(d+e*x^2)^q*(a+c*x^4)^p,x] /;
         GtQ[m,0] && Not[MatchQ[Px,x^m*u_.]]] /;
        FreeQ[{a,c,d,e,p,q},x] && PolyQ[Px,x]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [px__, d__, e__, q_, a__, c__, p_, x_],
        optional: [e__, q_, c__],
        when: {
            freeq!([a__, c__, d__, e__, p_, q_], x_)
                && rubi_poly_q(&px__, x_)
                && rubi_minimum_monomial_exponent(&px__, x_).is_some_and(|m| {
                    gtq!(Atom::num(m), 0)
                        && !visible_integer_power_of_variable_factor(&px__, x_)
                })
        },
        rhs: {
            let m = rubi_minimum_monomial_exponent(&px__, x_).rubi_rhs();
            let expanded = rubi_expand_to_sum(&(&px__ / x_.pow(m)), x_);
            rubi_rhs_int(
                &(x_.pow(m)
                    * expanded
                    * (&d__ + &e__ * x_.pow(2)).pow(&q_)
                    * (&a__ + &c__ * x_.pow(4)).pow(&p_)),
                x_,
            )
        },
    ));
}

fn push_rules_rule_2260(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, px__, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 2260,
        source: "Int[Px_*(d_+e_.*x_^2)^q_.*(a_+b_.*x_^2+c_.*x_^4)^p_.,x_Symbol] :=
          Unintegrable[Px*(d+e*x^2)^q*(a+b*x^2+c*x^4)^p,x] /;
        FreeQ[{a,b,c,d,e,p,q},x] && PolyQ[Px,x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [px__, d__, e__, q_, a__, b__, c__, p_, x_],
        optional: [e__, q_, b__, c__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, p_, q_], x_) && rubi_poly_q(&px__, x_)
        },
        rhs: {
            let integrand = px__
                * (&d__ + &e__ * x_.pow(2)).pow(&q_)
                * (&a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4)).pow(&p_);
            rubi_unintegrable(integrand, x_)
        },
    ));
}

fn push_rules_rule_2261(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, px__, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 2261,
        source: "Int[Px_*(d_+e_.*x_^2)^q_.*(a_+c_.*x_^4)^p_.,x_Symbol] :=
          Unintegrable[Px*(d+e*x^2)^q*(a+c*x^4)^p,x] /;
        FreeQ[{a,c,d,e,p,q},x] && PolyQ[Px,x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [px__, d__, e__, q_, a__, c__, p_, x_],
        optional: [e__, q_, c__, p_],
        when: {
            freeq!([a__, c__, d__, e__, p_, q_], x_) && rubi_poly_q(&px__, x_)
        },
        rhs: {
            let integrand = px__
                * (&d__ + &e__ * x_.pow(2)).pow(&q_)
                * (&a__ + &c__ * x_.pow(4)).pow(&p_);
            rubi_unintegrable(integrand, x_)
        },
    ));
}

fn push_rules_rule_2208(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, p4x__, q_, x_);
    rules.push(rubi_rule!(
        order: 2208,
        source: "Int[(d_+e_.*x_^2)^q_*P4x_/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
          With[{A=Coeff[P4x,x,0],B=Coeff[P4x,x,2],C=Coeff[P4x,x,4]},
          C*x*(d+e*x^2)^q*Sqrt[a+b*x^2+c*x^4]/(c*(2*q+3)) +
          1/(c*(2*q+3)) \\[Star] Int[(d+e*x^2)^(q-1)/Sqrt[a+b*x^2+c*x^4]*
            Simp[A*c*d*(2*q+3)-a*C*d+(c*(B*d+A*e)*(2*q+3)-C*(2*b*d+a*e+2*a*e*q))*x^2+(B*c*e*(2*q+3)-2*C*(b*e-c*d*q+b*e*q))*x^4,x],x]] /;
        FreeQ[{a,b,c,d,e},x] && PolyQ[P4x,x^2] && EqQ[Expon[P4x,x],4] && IGtQ[q,0]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [d__, e__, q_, p4x__, a__, b__, c__, x_],
        optional: [e__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && rubi_poly_q_power(&p4x__, x_, &Atom::num(2))
                && rubi_expon(&p4x__, x_) == Some(4)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && neq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && igtq!(q_, 0)
        },
        rhs: {
            let A = rubi_coeff(&p4x__, x_, 0).rubi_rhs();
            let B = rubi_coeff(&p4x__, x_, 2).rubi_rhs();
            let C = rubi_coeff(&p4x__, x_, 4).rubi_rhs();
            let quadratic = &d__ + &e__ * x_.pow(2);
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let two_q_plus_three = Atom::num(2) * &q_ + Atom::num(3);
            let denominator = &c__ * &two_q_plus_three;

            let direct = &C * x_ * quadratic.pow(&q_) * quartic.sqrt() / &denominator;
            let simp = rubi_simp(
                &(&A * &c__ * &d__ * &two_q_plus_three - &a__ * &C * &d__
                    + (&c__ * (&B * &d__ + &A * &e__) * &two_q_plus_three
                        - &C * (Atom::num(2) * &b__ * &d__ + &a__ * &e__
                            + Atom::num(2) * &a__ * &e__ * &q_))
                        * x_.pow(2)
                    + (&B * &c__ * &e__ * &two_q_plus_three
                        - Atom::num(2) * &C * (&b__ * &e__ - &c__ * &d__ * &q_ + &b__ * &e__ * &q_))
                        * x_.pow(4)),
                x_,
            );
            let recursive_integrand =
                quadratic.pow(&q_ - Atom::num(1)) * simp / quartic.sqrt();
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_2209(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, p4x__, q_, x_);
    rules.push(rubi_rule!(
        order: 2209,
        source: "Int[(d_+e_.*x_^2)^q_*P4x_/Sqrt[a_+c_.*x_^4],x_Symbol] :=
          With[{A=Coeff[P4x,x,0],B=Coeff[P4x,x,2],C=Coeff[P4x,x,4]},
          C*x*(d+e*x^2)^q*Sqrt[a+c*x^4]/(c*(2*q+3)) +
          1/(c*(2*q+3)) \\[Star] Int[(d+e*x^2)^(q-1)/Sqrt[a+c*x^4]*
            Simp[A*c*d*(2*q+3)-a*C*d+(c*(B*d+A*e)*(2*q+3)-a*C*e*(2*q+1))*x^2+(B*c*e*(2*q+3)+2*c*C*d*q)*x^4,x],x]] /;
        FreeQ[{a,c,d,e},x] && PolyQ[P4x,x^2] && EqQ[Expon[P4x,x],4] && IGtQ[q,0]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [d__, e__, q_, p4x__, a__, c__, x_],
        optional: [e__, c__],
        when: {
            freeq!([a__, c__, d__, e__], x_)
                && rubi_poly_q_power(&p4x__, x_, &Atom::num(2))
                && rubi_expon(&p4x__, x_) == Some(4)
                && neq!(&c__ * d__.pow(2) + &a__ * e__.pow(2), 0)
                && igtq!(q_, 0)
        },
        rhs: {
            let A = rubi_coeff(&p4x__, x_, 0).rubi_rhs();
            let B = rubi_coeff(&p4x__, x_, 2).rubi_rhs();
            let C = rubi_coeff(&p4x__, x_, 4).rubi_rhs();
            let quadratic = &d__ + &e__ * x_.pow(2);
            let quartic = &a__ + &c__ * x_.pow(4);
            let two_q_plus_three = Atom::num(2) * &q_ + Atom::num(3);
            let denominator = &c__ * &two_q_plus_three;

            let direct = &C * x_ * quadratic.pow(&q_) * quartic.sqrt() / &denominator;
            let simp = rubi_simp(
                &(&A * &c__ * &d__ * &two_q_plus_three - &a__ * &C * &d__
                    + (&c__ * (&B * &d__ + &A * &e__) * &two_q_plus_three
                        - &a__ * &C * &e__ * (Atom::num(2) * &q_ + Atom::num(1)))
                        * x_.pow(2)
                    + (&B * &c__ * &e__ * &two_q_plus_three
                        + Atom::num(2) * &c__ * &C * &d__ * &q_)
                        * x_.pow(4)),
                x_,
            );
            let recursive_integrand =
                quadratic.pow(&q_ - Atom::num(1)) * simp / quartic.sqrt();
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_2210(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, p4x__, q_, x_);
    rules.push(rubi_rule!(
        order: 2210,
        source: "Int[(d_+e_.*x_^2)^q_*P4x_/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
          With[{A=Coeff[P4x,x,0],B=Coeff[P4x,x,2],C=Coeff[P4x,x,4]},
          -(C*d^2-B*d*e+A*e^2)*x*(d+e*x^2)^(q+1)*Sqrt[a+b*x^2+c*x^4]/(2*d*(q+1)*(c*d^2-b*d*e+a*e^2)) +
          1/(2*d*(q+1)*(c*d^2-b*d*e+a*e^2)) \\[Star] Int[(d+e*x^2)^(q+1)/Sqrt[a+b*x^2+c*x^4]*
            Simp[a*d*(C*d-B*e)+A*(a*e^2*(2*q+3)+2*d*(c*d-b*e)*(q+1))-
              2*((B*d-A*e)*(b*e*(q+2)-c*d*(q+1))-C*d*(b*d+a*e*(q+1)))*x^2+
              c*(C*d^2-B*d*e+A*e^2)*(2*q+5)*x^4,x],x]] /;
        FreeQ[{a,b,c,d,e},x] && PolyQ[P4x,x^2] && LeQ[Expon[P4x,x],4] && ILtQ[q,-1]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [d__, e__, q_, p4x__, a__, b__, c__, x_],
        optional: [e__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && rubi_poly_q_power(&p4x__, x_, &Atom::num(2))
                && rubi_expon(&p4x__, x_).is_some_and(|exponent| exponent <= 4)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && neq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && iltq!(q_, -1)
        },
        rhs: {
            let A = rubi_coeff(&p4x__, x_, 0).rubi_rhs();
            let B = rubi_coeff(&p4x__, x_, 2).rubi_rhs();
            let C = rubi_coeff(&p4x__, x_, 4).rubi_rhs();
            let quadratic = &d__ + &e__ * x_.pow(2);
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let delta = &c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2);
            let balance = &C * d__.pow(2) - &B * &d__ * &e__ + &A * e__.pow(2);
            let denominator = Atom::num(2) * &d__ * (&q_ + Atom::num(1)) * &delta;

            let direct =
                -&balance * x_ * quadratic.pow(&q_ + Atom::num(1)) * quartic.sqrt()
                    / &denominator;
            let simp = rubi_simp(
                &(&a__ * &d__ * (&C * &d__ - &B * &e__)
                    + &A * (&a__ * e__.pow(2) * (Atom::num(2) * &q_ + Atom::num(3))
                        + Atom::num(2)
                            * &d__
                            * (&c__ * &d__ - &b__ * &e__)
                            * (&q_ + Atom::num(1)))
                    - Atom::num(2)
                        * ((&B * &d__ - &A * &e__)
                            * (&b__ * &e__ * (&q_ + Atom::num(2))
                                - &c__ * &d__ * (&q_ + Atom::num(1)))
                            - &C * &d__ * (&b__ * &d__ + &a__ * &e__ * (&q_ + Atom::num(1))))
                        * x_.pow(2)
                    + &c__ * &balance * (Atom::num(2) * &q_ + Atom::num(5)) * x_.pow(4)),
                x_,
            );
            let recursive_integrand =
                quadratic.pow(&q_ + Atom::num(1)) * simp / quartic.sqrt();
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_2211(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, p4x__, q_, x_);
    rules.push(rubi_rule!(
        order: 2211,
        source: "Int[(d_+e_.*x_^2)^q_*P4x_/Sqrt[a_+c_.*x_^4],x_Symbol] :=
          With[{A=Coeff[P4x,x,0],B=Coeff[P4x,x,2],C=Coeff[P4x,x,4]},
          -(C*d^2-B*d*e+A*e^2)*x*(d+e*x^2)^(q+1)*Sqrt[a+c*x^4]/(2*d*(q+1)*(c*d^2+a*e^2)) +
          1/(2*d*(q+1)*(c*d^2+a*e^2)) \\[Star] Int[(d+e*x^2)^(q+1)/Sqrt[a+c*x^4]*
            Simp[a*d*(C*d-B*e)+A*(a*e^2*(2*q+3)+2*c*d^2*(q+1))+2*d*(B*c*d-A*c*e+a*C*e)*(q+1)*x^2+c*(C*d^2-B*d*e+A*e^2)*(2*q+5)*x^4,x],x]] /;
        FreeQ[{a,c,d,e},x] && PolyQ[P4x,x^2] && LeQ[Expon[P4x,x],4] && ILtQ[q,-1]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [d__, e__, q_, p4x__, a__, c__, x_],
        optional: [e__, c__],
        when: {
            freeq!([a__, c__, d__, e__], x_)
                && rubi_poly_q_power(&p4x__, x_, &Atom::num(2))
                && rubi_expon(&p4x__, x_).is_some_and(|exponent| exponent <= 4)
                && neq!(&c__ * d__.pow(2) + &a__ * e__.pow(2), 0)
                && iltq!(q_, -1)
        },
        rhs: {
            let A = rubi_coeff(&p4x__, x_, 0).rubi_rhs();
            let B = rubi_coeff(&p4x__, x_, 2).rubi_rhs();
            let C = rubi_coeff(&p4x__, x_, 4).rubi_rhs();
            let quadratic = &d__ + &e__ * x_.pow(2);
            let quartic = &a__ + &c__ * x_.pow(4);
            let delta = &c__ * d__.pow(2) + &a__ * e__.pow(2);
            let balance = &C * d__.pow(2) - &B * &d__ * &e__ + &A * e__.pow(2);
            let denominator = Atom::num(2) * &d__ * (&q_ + Atom::num(1)) * &delta;

            let direct =
                -&balance * x_ * quadratic.pow(&q_ + Atom::num(1)) * quartic.sqrt()
                    / &denominator;
            let simp = rubi_simp(
                &(&a__ * &d__ * (&C * &d__ - &B * &e__)
                    + &A * (&a__ * e__.pow(2) * (Atom::num(2) * &q_ + Atom::num(3))
                        + Atom::num(2) * &c__ * d__.pow(2) * (&q_ + Atom::num(1)))
                    + Atom::num(2)
                        * &d__
                        * (&B * &c__ * &d__ - &A * &c__ * &e__ + &a__ * &C * &e__)
                        * (&q_ + Atom::num(1))
                        * x_.pow(2)
                    + &c__ * &balance * (Atom::num(2) * &q_ + Atom::num(5)) * x_.pow(4)),
                x_,
            );
            let recursive_integrand =
                quadratic.pow(&q_ + Atom::num(1)) * simp / quartic.sqrt();
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_2212(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_a__, capital_b__, a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 2212,
        source: "Int[(A_+B_.*x_^2)/((d_+e_.*x_^2)*Sqrt[a_+b_.*x_^2+c_.*x_^4]),x_Symbol] :=
          A \\[Star] Subst[Int[1/(d-(b*d-2*a*e)*x^2),x],x,x/Sqrt[a+b*x^2+c*x^4]] /;
        FreeQ[{a,b,c,d,e,A,B},x] && EqQ[c*d^2-a*e^2,0] && EqQ[B*d+A*e,0]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [capital_a__, capital_b__, d__, e__, a__, b__, c__, x_],
        optional: [capital_b__, e__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__, capital_a__, capital_b__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && neq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && eqq!(&c__ * d__.pow(2) - &a__ * e__.pow(2), 0)
                && eqq!(&capital_b__ * &d__ + &capital_a__ * &e__, 0)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let sub_atom = Atom::var(sub);
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let inner_integrand =
                Atom::num(1) / (&d__ - (&b__ * &d__ - Atom::num(2) * &a__ * &e__) * sub_atom.pow(2));
            let inner = rubi_rhs_int(&inner_integrand, sub);

            rubi_star(capital_a__, rubi_subst(&inner, sub, x_ / quartic.sqrt()))
        },
    ));
}

fn push_rules_rule_2213(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_a__, capital_b__, a__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 2213,
        source: "Int[(A_+B_.*x_^2)/((d_+e_.*x_^2)*Sqrt[a_+c_.*x_^4]),x_Symbol] :=
          A \\[Star] Subst[Int[1/(d+2*a*e*x^2),x],x,x/Sqrt[a+c*x^4]] /;
        FreeQ[{a,c,d,e,A,B},x] && EqQ[c*d^2-a*e^2,0] && EqQ[B*d+A*e,0]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [capital_a__, capital_b__, d__, e__, a__, c__, x_],
        optional: [capital_b__, e__, c__],
        when: {
            freeq!([a__, c__, d__, e__, capital_a__, capital_b__], x_)
                && neq!(&c__ * d__.pow(2) + &a__ * e__.pow(2), 0)
                && eqq!(&c__ * d__.pow(2) - &a__ * e__.pow(2), 0)
                && eqq!(&capital_b__ * &d__ + &capital_a__ * &e__, 0)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let sub_atom = Atom::var(sub);
            let quartic = &a__ + &c__ * x_.pow(4);
            let inner_integrand = Atom::num(1) / (&d__ + Atom::num(2) * &a__ * &e__ * sub_atom.pow(2));
            let inner = rubi_rhs_int(&inner_integrand, sub);

            rubi_star(capital_a__, rubi_subst(&inner, sub, x_ / quartic.sqrt()))
        },
    ));
}

fn push_rules_rule_2214(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_a__, capital_b__, a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 2214,
        source: "Int[(A_+B_.*x_^2)/((d_+e_.*x_^2)*Sqrt[a_+b_.*x_^2+c_.*x_^4]),x_Symbol] :=
          (B*d+A*e)/(2*d*e) \\[Star] Int[1/Sqrt[a+b*x^2+c*x^4],x] -
          (B*d-A*e)/(2*d*e) \\[Star] Int[(d-e*x^2)/((d+e*x^2)*Sqrt[a+b*x^2+c*x^4]),x] /;
        FreeQ[{a,b,c,d,e,A,B},x] && EqQ[c*d^2-a*e^2,0] && NeQ[B*d+A*e,0]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [capital_a__, capital_b__, d__, e__, a__, b__, c__, x_],
        optional: [capital_b__, e__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__, capital_a__, capital_b__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && neq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && eqq!(&c__ * d__.pow(2) - &a__ * e__.pow(2), 0)
                && neq!(&capital_b__ * &d__ + &capital_a__ * &e__, 0)
        },
        rhs: {
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let denominator = Atom::num(2) * &d__ * &e__;

            let first_integrand = Atom::num(1) / quartic.sqrt();
            let first = rubi_rhs_int(&first_integrand, x_);

            let second_integrand =
                (&d__ - &e__ * x_.pow(2)) / ((&d__ + &e__ * x_.pow(2)) * quartic.sqrt());
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(&capital_b__ * &d__ + &capital_a__ * &e__, first / &denominator)
                    - rubi_star(&capital_b__ * &d__ - &capital_a__ * &e__, second / denominator)
        },
    ));
}

fn push_rules_rule_2215(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_a__, capital_b__, a__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 2215,
        source: "Int[(A_+B_.*x_^2)/((d_+e_.*x_^2)*Sqrt[a_+c_.*x_^4]),x_Symbol] :=
          (B*d+A*e)/(2*d*e) \\[Star] Int[1/Sqrt[a+c*x^4],x] -
          (B*d-A*e)/(2*d*e) \\[Star] Int[(d-e*x^2)/((d+e*x^2)*Sqrt[a+c*x^4]),x] /;
        FreeQ[{a,c,d,e,A,B},x] && EqQ[c*d^2-a*e^2,0] && NeQ[B*d+A*e,0]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [capital_a__, capital_b__, d__, e__, a__, c__, x_],
        optional: [capital_b__, e__, c__],
        when: {
            freeq!([a__, c__, d__, e__, capital_a__, capital_b__], x_)
                && neq!(&c__ * d__.pow(2) + &a__ * e__.pow(2), 0)
                && eqq!(&c__ * d__.pow(2) - &a__ * e__.pow(2), 0)
                && neq!(&capital_b__ * &d__ + &capital_a__ * &e__, 0)
        },
        rhs: {
            let quartic = &a__ + &c__ * x_.pow(4);
            let denominator = Atom::num(2) * &d__ * &e__;

            let first_integrand = Atom::num(1) / quartic.sqrt();
            let first = rubi_rhs_int(&first_integrand, x_);

            let second_integrand =
                (&d__ - &e__ * x_.pow(2)) / ((&d__ + &e__ * x_.pow(2)) * quartic.sqrt());
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(&capital_b__ * &d__ + &capital_a__ * &e__, first / &denominator)
                    - rubi_star(&capital_b__ * &d__ - &capital_a__ * &e__, second / denominator)
        },
    ));
}

fn push_rules_rule_2216(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_a__, capital_b__, a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 2216,
        source: "Int[(A_+B_.*x_^2)/((d_+e_.*x_^2)*Sqrt[a_+b_.*x_^2+c_.*x_^4]),x_Symbol] :=
          Sqrt[A+B*x^2]*Sqrt[a/A+c*x^2/B]/Sqrt[a+b*x^2+c*x^4] \\[Star] Int[Sqrt[A+B*x^2]/((d+e*x^2)*Sqrt[a/A+c*x^2/B]),x] /;
        FreeQ[{a,b,c,d,e,A,B},x] && EqQ[c*A^2-b*A*B+a*B^2,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [capital_a__, capital_b__, d__, e__, a__, b__, c__, x_],
        optional: [capital_b__, e__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__, capital_a__, capital_b__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && neq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && eqq!(
                    &c__ * capital_a__.pow(2) - &b__ * &capital_a__ * &capital_b__
                        + &a__ * capital_b__.pow(2),
                    0
                )
        },
        rhs: {
            let numerator = &capital_a__ + &capital_b__ * x_.pow(2);
            let reduced = &a__ / &capital_a__ + &c__ * x_.pow(2) / &capital_b__;
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let recursive_integrand =
                numerator.sqrt() / ((&d__ + &e__ * x_.pow(2)) * &reduced.sqrt());
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(numerator.sqrt() * reduced.sqrt() / quartic.sqrt(), recursive)
        },
    ));
}

fn push_rules_rule_2217(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_a__, capital_b__, a__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 2217,
        source: "Int[(A_+B_.*x_^2)/((d_+e_.*x_^2)*Sqrt[a_+c_.*x_^4]),x_Symbol] :=
          Sqrt[A+B*x^2]*Sqrt[a/A+c*x^2/B]/Sqrt[a+c*x^4] \\[Star] Int[Sqrt[A+B*x^2]/((d+e*x^2)*Sqrt[a/A+c*x^2/B]),x] /;
        FreeQ[{a,c,d,e,A,B},x] && EqQ[c*A^2+a*B^2,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [capital_a__, capital_b__, d__, e__, a__, c__, x_],
        optional: [capital_b__, e__, c__],
        when: {
            freeq!([a__, c__, d__, e__, capital_a__, capital_b__], x_)
                && neq!(&c__ * d__.pow(2) + &a__ * e__.pow(2), 0)
                && eqq!(&c__ * capital_a__.pow(2) + &a__ * capital_b__.pow(2), 0)
        },
        rhs: {
            let numerator = &capital_a__ + &capital_b__ * x_.pow(2);
            let reduced = &a__ / &capital_a__ + &c__ * x_.pow(2) / &capital_b__;
            let quartic = &a__ + &c__ * x_.pow(4);
            let recursive_integrand =
                numerator.sqrt() / ((&d__ + &e__ * x_.pow(2)) * &reduced.sqrt());
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(numerator.sqrt() * reduced.sqrt() / quartic.sqrt(), recursive)
        },
    ));
}

fn push_rules_rule_2218(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_a__, capital_b__, a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 2218,
        source: "Int[(A_+B_.*x_^2)/((d_+e_.*x_^2)*Sqrt[a_+b_.*x_^2+c_.*x_^4]),x_Symbol] :=
          With[{q=Sqrt[b^2-4*a*c]},
          (2*a*B-A*(b+q))/(2*a*e-d*(b+q)) \\[Star] Int[1/Sqrt[a+b*x^2+c*x^4],x] -
          (B*d-A*e)/(2*a*e-d*(b+q)) \\[Star] Int[(2*a+(b+q)*x^2)/((d+e*x^2)*Sqrt[a+b*x^2+c*x^4]),x] /;
         RationalQ[q]] /;
        FreeQ[{a,b,c,d,e,A,B},x] && GtQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && NeQ[c*A^2-b*A*B+a*B^2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [capital_a__, capital_b__, d__, e__, a__, b__, c__, x_],
        optional: [capital_b__, e__, b__, c__],
        when: {
            let q = (b__.pow(2) - Atom::num(4) * &a__ * &c__).sqrt();
            freeq!([a__, b__, c__, d__, e__, capital_a__, capital_b__], x_)
                && gtq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && neq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && neq!(
                    &c__ * capital_a__.pow(2) - &b__ * &capital_a__ * &capital_b__
                        + &a__ * capital_b__.pow(2),
                    0
                )
                && rationalq!(q)
        },
        rhs: {
            let q = (b__.pow(2) - Atom::num(4) * &a__ * &c__).sqrt();
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let denominator = Atom::num(2) * &a__ * &e__ - &d__ * (&b__ + &q);

            let first_integrand = Atom::num(1) / quartic.sqrt();
            let first = rubi_rhs_int(&first_integrand, x_);

            let second_integrand = (Atom::num(2) * &a__ + (&b__ + &q) * x_.pow(2))
                / ((&d__ + &e__ * x_.pow(2)) * quartic.sqrt());
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(Atom::num(2) * &a__ * &capital_b__ - &capital_a__ * (&b__ + &q), first
                    / &denominator)
                    - rubi_star((&capital_b__ * &d__ - &capital_a__ * &e__) / denominator, second)
        },
    ));
}

fn push_rules_rule_2219(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_a__, capital_b__, a__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 2219,
        source: "Int[(A_+B_.*x_^2)/((d_+e_.*x_^2)*Sqrt[a_+c_.*x_^4]),x_Symbol] :=
          With[{q=Sqrt[-a*c]},
          (a*B-A*q)/(a*e-d*q) \\[Star] Int[1/Sqrt[a+c*x^4],x] -
          (B*d-A*e)/(a*e-d*q) \\[Star] Int[(a+q*x^2)/((d+e*x^2)*Sqrt[a+c*x^4]),x] /;
         RationalQ[q]] /;
        FreeQ[{a,c,d,e,A,B},x] && GtQ[-a*c,0] && EqQ[c*d^2+a*e^2,0] && NeQ[c*A^2+a*B^2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [capital_a__, capital_b__, d__, e__, a__, c__, x_],
        optional: [capital_b__, e__, c__],
        when: {
            let q = (-&a__ * &c__).sqrt();
            freeq!([a__, c__, d__, e__, capital_a__, capital_b__], x_)
                && gtq!(-&a__ * &c__, 0)
                && eqq!(&c__ * d__.pow(2) + &a__ * e__.pow(2), 0)
                && neq!(&c__ * capital_a__.pow(2) + &a__ * capital_b__.pow(2), 0)
                && rationalq!(q)
        },
        rhs: {
            let q = (-&a__ * &c__).sqrt();
            let quartic = &a__ + &c__ * x_.pow(4);
            let denominator = &a__ * &e__ - &d__ * &q;

            let first_integrand = Atom::num(1) / quartic.sqrt();
            let first = rubi_rhs_int(&first_integrand, x_);

            let second_integrand =
                (&a__ + &q * x_.pow(2)) / ((&d__ + &e__ * x_.pow(2)) * quartic.sqrt());
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(&a__ * &capital_b__ - &capital_a__ * &q, first / &denominator)
                    - rubi_star((&capital_b__ * &d__ - &capital_a__ * &e__) / denominator, second)
        },
    ));
}

fn push_rules_rule_2220(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_a__, capital_b__, a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 2220,
        source: "Int[(A_+B_.*x_^2)/((d_+e_.*x_^2)*Sqrt[a_+b_.*x_^2+c_.*x_^4]),x_Symbol] :=
          With[{q=Rt[B/A,2]},
          -(B*d-A*e)*ArcTan[Rt[-b+c*d/e+a*e/d,2]*x/Sqrt[a+b*x^2+c*x^4]]/(2*d*e*Rt[-b+c*d/e+a*e/d,2]) +
          (B*d+A*e)*(1+q^2*x^2)*Sqrt[(a+b*x^2+c*x^4)/(a*(1+q^2*x^2)^2)]/(4*d*e*q*Sqrt[a+b*x^2+c*x^4])*
            EllipticPi[-(e-d*q^2)^2/(4*d*e*q^2),2*ArcTan[q*x],1/2-b/(4*a*q^2)]] /;
        FreeQ[{a,b,c,d,e,A,B},x] && NeQ[c*d^2-a*e^2,0] && PosQ[c/a] && EqQ[c*A^2-a*B^2,0] && PosQ[B/A] && PosQ[-b+c*d/e+a*e/d]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [capital_a__, capital_b__, d__, e__, a__, b__, c__, x_],
        optional: [capital_b__, e__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__, capital_a__, capital_b__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && neq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && neq!(&c__ * d__.pow(2) - &a__ * e__.pow(2), 0)
                && posq!(&c__ / &a__)
                && eqq!(&c__ * capital_a__.pow(2) - &a__ * capital_b__.pow(2), 0)
                && posq!(&capital_b__ / &capital_a__)
                && posq!(-&b__ + &c__ * &d__ / &e__ + &a__ * &e__ / &d__)
        },
        rhs: {
            let q = rubi_rt(&(&capital_b__ / &capital_a__), 2);
            let r = rubi_rt(&(-&b__ + &c__ * &d__ / &e__ + &a__ * &e__ / &d__), 2);
            let numerator = &capital_a__ + &capital_b__ * x_.pow(2);
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let bd_minus_ae = &capital_b__ * &d__ - &capital_a__ * &e__;

            let direct = -&bd_minus_ae * (&r * x_ / quartic.sqrt()).atan()
                / (Atom::num(2) * &d__ * &e__ * &r);

            let elliptic_n = rubi_cancel(
                &(-bd_minus_ae.pow(2)
                    / (Atom::num(4) * &d__ * &e__ * &capital_a__ * &capital_b__)),
            );
            let elliptic_phi = Atom::num(2) * (&q * x_).atan();
            let elliptic_m =
                Atom::num(1) / Atom::num(2) - &b__ * &capital_a__ / (Atom::num(4) * &a__ * &capital_b__);
            let elliptic = rubi_elliptic_pi(elliptic_n, elliptic_phi, elliptic_m);

            let multiplier = (&capital_b__ * &d__ + &capital_a__ * &e__)
                * &numerator
                * (capital_a__.pow(2) * &quartic / (&a__ * numerator.pow(2))).sqrt()
                / (Atom::num(4) * &d__ * &e__ * &capital_a__ * &q * quartic.sqrt());

            rubi_simp(&(direct), x_) + rubi_simp(&(multiplier * elliptic), x_)
        },
    ));
}

fn push_rules_rule_2221(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_a__, capital_b__, a__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 2221,
        source: "Int[(A_+B_.*x_^2)/((d_+e_.*x_^2)*Sqrt[a_+c_.*x_^4]),x_Symbol] :=
          With[{q=Rt[B/A,2]},
          -(B*d-A*e)*ArcTan[Rt[c*d/e+a*e/d,2]*x/Sqrt[a+c*x^4]]/(2*d*e*Rt[c*d/e+a*e/d,2]) +
          (B*d+A*e)*(1+q^2*x^2)*Sqrt[(a+c*x^4)/(a*(1+q^2*x^2)^2)]/(4*d*e*q*Sqrt[a+c*x^4])*
            EllipticPi[-(e-d*q^2)^2/(4*d*e*q^2),2*ArcTan[q*x],1/2]] /;
        FreeQ[{a,c,d,e,A,B},x] && NeQ[c*d^2-a*e^2,0] && PosQ[c/a] && EqQ[c*A^2-a*B^2,0] && PosQ[B/A] && PosQ[c*d/e+a*e/d]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [capital_a__, capital_b__, d__, e__, a__, c__, x_],
        optional: [capital_b__, e__, c__],
        when: {
            freeq!([a__, c__, d__, e__, capital_a__, capital_b__], x_)
                && neq!(&c__ * d__.pow(2) + &a__ * e__.pow(2), 0)
                && neq!(&c__ * d__.pow(2) - &a__ * e__.pow(2), 0)
                && posq!(&c__ / &a__)
                && eqq!(&c__ * capital_a__.pow(2) - &a__ * capital_b__.pow(2), 0)
                && posq!(&capital_b__ / &capital_a__)
                && posq!(&c__ * &d__ / &e__ + &a__ * &e__ / &d__)
        },
        rhs: {
            let q = rubi_rt(&(&capital_b__ / &capital_a__), 2);
            let r = rubi_rt(&(&c__ * &d__ / &e__ + &a__ * &e__ / &d__), 2);
            let numerator = &capital_a__ + &capital_b__ * x_.pow(2);
            let quartic = &a__ + &c__ * x_.pow(4);
            let bd_minus_ae = &capital_b__ * &d__ - &capital_a__ * &e__;

            let direct = -&bd_minus_ae * (&r * x_ / quartic.sqrt()).atan()
                / (Atom::num(2) * &d__ * &e__ * &r);

            let elliptic_n = rubi_cancel(
                &(-bd_minus_ae.pow(2)
                    / (Atom::num(4) * &d__ * &e__ * &capital_a__ * &capital_b__)),
            );
            let elliptic_phi = Atom::num(2) * (&q * x_).atan();
            let elliptic_m = Atom::num(1) / Atom::num(2);
            let elliptic = rubi_elliptic_pi(elliptic_n, elliptic_phi, elliptic_m);

            let multiplier = (&capital_b__ * &d__ + &capital_a__ * &e__)
                * &numerator
                * (capital_a__.pow(2) * &quartic / (&a__ * numerator.pow(2))).sqrt()
                / (Atom::num(4) * &d__ * &e__ * &capital_a__ * &q * quartic.sqrt());

            rubi_simp(&(direct), x_) + rubi_simp(&(multiplier * elliptic), x_)
        },
    ));
}

fn push_rules_rule_2222(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_a__, capital_b__, a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 2222,
        source: "Int[(A_+B_.*x_^2)/((d_+e_.*x_^2)*Sqrt[a_+b_.*x_^2+c_.*x_^4]),x_Symbol] :=
          With[{q=Rt[B/A,2]},
          -(B*d-A*e)*ArcTanh[Rt[b-c*d/e-a*e/d,2]*x/Sqrt[a+b*x^2+c*x^4]]/(2*d*e*Rt[b-c*d/e-a*e/d,2]) +
          (B*d+A*e)*(1+q^2*x^2)*Sqrt[(a+b*x^2+c*x^4)/(a*(1+q^2*x^2)^2)]/(4*d*e*q*Sqrt[a+b*x^2+c*x^4])*
            EllipticPi[-(e-d*q^2)^2/(4*d*e*q^2),2*ArcTan[q*x],1/2-b/(4*a*q^2)]] /;
        FreeQ[{a,b,c,d,e,A,B},x] && NeQ[c*d^2-a*e^2,0] && PosQ[c/a] && EqQ[c*A^2-a*B^2,0] && PosQ[B/A] && NegQ[-b+c*d/e+a*e/d]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [capital_a__, capital_b__, d__, e__, a__, b__, c__, x_],
        optional: [capital_b__, e__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__, capital_a__, capital_b__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && neq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && neq!(&c__ * d__.pow(2) - &a__ * e__.pow(2), 0)
                && posq!(&c__ / &a__)
                && eqq!(&c__ * capital_a__.pow(2) - &a__ * capital_b__.pow(2), 0)
                && posq!(&capital_b__ / &capital_a__)
                && negq!(-&b__ + &c__ * &d__ / &e__ + &a__ * &e__ / &d__)
        },
        rhs: {
            let q = rubi_rt(&(&capital_b__ / &capital_a__), 2);
            let r = rubi_rt(&(&b__ - &c__ * &d__ / &e__ - &a__ * &e__ / &d__), 2);
            let numerator = &capital_a__ + &capital_b__ * x_.pow(2);
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let bd_minus_ae = &capital_b__ * &d__ - &capital_a__ * &e__;
            let direct = rubi_simp(
                &(-&bd_minus_ae * (&r * x_ / quartic.sqrt()).atanh()
                    / (Atom::num(2) * &d__ * &e__ * &r)),
                x_,
            );
            let elliptic_n = rubi_cancel(
                &(-bd_minus_ae.pow(2)
                    / (Atom::num(4) * &d__ * &e__ * &capital_a__ * &capital_b__)),
            );
            let elliptic_phi = Atom::num(2) * (&q * x_).atan();
            let elliptic_m =
                Atom::num(1) / Atom::num(2) - &b__ * &capital_a__ / (Atom::num(4) * &a__ * &capital_b__);
            let elliptic = rubi_elliptic_pi(elliptic_n, elliptic_phi, elliptic_m);
            let multiplier = (&capital_b__ * &d__ + &capital_a__ * &e__)
                * &numerator
                * (capital_a__.pow(2) * &quartic / (&a__ * numerator.pow(2))).sqrt()
                / (Atom::num(4) * &d__ * &e__ * &capital_a__ * &q * quartic.sqrt());

            rubi_simp(&(direct), x_) + rubi_simp(&(multiplier * elliptic), x_)
        },
    ));
}

fn push_rules_rule_2223(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_a__, capital_b__, a__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 2223,
        source: "Int[(A_+B_.*x_^2)/((d_+e_.*x_^2)*Sqrt[a_+c_.*x_^4]),x_Symbol] :=
          With[{q=Rt[B/A,2]},
          -(B*d-A*e)*ArcTanh[Rt[-c*d/e-a*e/d,2]*x/Sqrt[a+c*x^4]]/(2*d*e*Rt[-c*d/e-a*e/d,2]) +
          (B*d+A*e)*(1+q^2*x^2)*Sqrt[(a+c*x^4)/(a*(1+q^2*x^2)^2)]/(4*d*e*q*Sqrt[a+c*x^4])*
            EllipticPi[-(e-d*q^2)^2/(4*d*e*q^2),2*ArcTan[q*x],1/2]] /;
        FreeQ[{a,c,d,e,A,B},x] && NeQ[c*d^2-a*e^2,0] && PosQ[c/a] && EqQ[c*A^2-a*B^2,0] && PosQ[B/A] && NegQ[c*d/e+a*e/d]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [capital_a__, capital_b__, d__, e__, a__, c__, x_],
        optional: [capital_b__, e__, c__],
        when: {
            freeq!([a__, c__, d__, e__, capital_a__, capital_b__], x_)
                && neq!(&c__ * d__.pow(2) + &a__ * e__.pow(2), 0)
                && neq!(&c__ * d__.pow(2) - &a__ * e__.pow(2), 0)
                && posq!(&c__ / &a__)
                && eqq!(&c__ * capital_a__.pow(2) - &a__ * capital_b__.pow(2), 0)
                && posq!(&capital_b__ / &capital_a__)
                && negq!(&c__ * &d__ / &e__ + &a__ * &e__ / &d__)
        },
        rhs: {
            let q = rubi_rt(&(&capital_b__ / &capital_a__), 2);
            let r = rubi_rt(&(-&c__ * &d__ / &e__ - &a__ * &e__ / &d__), 2);
            let numerator = &capital_a__ + &capital_b__ * x_.pow(2);
            let quartic = &a__ + &c__ * x_.pow(4);
            let bd_minus_ae = &capital_b__ * &d__ - &capital_a__ * &e__;
            let direct = rubi_simp(
                &(-&bd_minus_ae * (&r * x_ / quartic.sqrt()).atanh()
                    / (Atom::num(2) * &d__ * &e__ * &r)),
                x_,
            );
            let elliptic_n = rubi_cancel(
                &(-bd_minus_ae.pow(2)
                    / (Atom::num(4) * &d__ * &e__ * &capital_a__ * &capital_b__)),
            );
            let elliptic_phi = Atom::num(2) * (&q * x_).atan();
            let elliptic = rubi_elliptic_pi(elliptic_n, elliptic_phi, Atom::num(1) / Atom::num(2));
            let multiplier = (&capital_b__ * &d__ + &capital_a__ * &e__)
                * &numerator
                * (capital_a__.pow(2) * &quartic / (&a__ * numerator.pow(2))).sqrt()
                / (Atom::num(4) * &d__ * &e__ * &capital_a__ * &q * quartic.sqrt());

            rubi_simp(&(direct), x_) + rubi_simp(&(multiplier * elliptic), x_)
        },
    ));
}

fn push_rules_rule_2224(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_a__, capital_b__, a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 2224,
        source: "Int[(A_+B_.*x_^2)/((d_+e_.*x_^2)*Sqrt[a_+b_.*x_^2+c_.*x_^4]),x_Symbol] :=
          2*A*B/(B*d+A*e) \\[Star] Int[1/Sqrt[a+b*x^2+c*x^4],x] - (B*d-A*e)/(B*d+A*e) \\[Star] Int[(A-B*x^2)/((d+e*x^2)*Sqrt[a+b*x^2+c*x^4]),x] /;
        FreeQ[{a,b,c,d,e,A,B},x] && NeQ[c*d^2-a*e^2,0] && PosQ[c/a] && EqQ[c*A^2-a*B^2,0] && NegQ[B/A]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [capital_a__, capital_b__, d__, e__, a__, b__, c__, x_],
        optional: [capital_b__, e__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__, capital_a__, capital_b__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && neq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && neq!(&c__ * d__.pow(2) - &a__ * e__.pow(2), 0)
                && posq!(&c__ / &a__)
                && eqq!(&c__ * capital_a__.pow(2) - &a__ * capital_b__.pow(2), 0)
                && negq!(&capital_b__ / &capital_a__)
        },
        rhs: {
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let denominator = &capital_b__ * &d__ + &capital_a__ * &e__;
            let first = rubi_rhs_int(&(Atom::num(1) / quartic.sqrt()), x_);
            let second = rubi_rhs_int(
                &((&capital_a__ - &capital_b__ * x_.pow(2))
                    / ((&d__ + &e__ * x_.pow(2)) * quartic.sqrt())),
                x_,
            );

            rubi_star(Atom::num(2) * &capital_a__ * &capital_b__ / &denominator, first)
                    - rubi_star(&capital_b__ * &d__ - &capital_a__ * &e__, second / denominator)
        },
    ));
}

fn push_rules_rule_2225(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_a__, capital_b__, a__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 2225,
        source: "Int[(A_+B_.*x_^2)/((d_+e_.*x_^2)*Sqrt[a_+c_.*x_^4]),x_Symbol] :=
          2*A*B/(B*d+A*e) \\[Star] Int[1/Sqrt[a+c*x^4],x] - (B*d-A*e)/(B*d+A*e) \\[Star] Int[(A-B*x^2)/((d+e*x^2)*Sqrt[a+c*x^4]),x] /;
        FreeQ[{a,c,d,e,A,B},x] && NeQ[c*d^2-a*e^2,0] && PosQ[c/a] && EqQ[c*A^2-a*B^2,0] && NegQ[B/A]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [capital_a__, capital_b__, d__, e__, a__, c__, x_],
        optional: [capital_b__, e__, c__],
        when: {
            freeq!([a__, c__, d__, e__, capital_a__, capital_b__], x_)
                && neq!(&c__ * d__.pow(2) + &a__ * e__.pow(2), 0)
                && neq!(&c__ * d__.pow(2) - &a__ * e__.pow(2), 0)
                && posq!(&c__ / &a__)
                && eqq!(&c__ * capital_a__.pow(2) - &a__ * capital_b__.pow(2), 0)
                && negq!(&capital_b__ / &capital_a__)
        },
        rhs: {
            let quartic = &a__ + &c__ * x_.pow(4);
            let denominator = &capital_b__ * &d__ + &capital_a__ * &e__;
            let first = rubi_rhs_int(&(Atom::num(1) / quartic.sqrt()), x_);
            let second = rubi_rhs_int(
                &((&capital_a__ - &capital_b__ * x_.pow(2))
                    / ((&d__ + &e__ * x_.pow(2)) * quartic.sqrt())),
                x_,
            );

            rubi_star(Atom::num(2) * &capital_a__ * &capital_b__ / &denominator, first)
                    - rubi_star(&capital_b__ * &d__ - &capital_a__ * &e__, second / denominator)
        },
    ));
}

fn push_rules_rule_2226(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_a__, capital_b__, a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 2226,
        source: "Int[(A_+B_.*x_^2)/((d_+e_.*x_^2)*Sqrt[a_+b_.*x_^2+c_.*x_^4]),x_Symbol] :=
          With[{q=Rt[c/a,2]},
          (A*(c*d+a*e*q)-a*B*(e+d*q))/(c*d^2-a*e^2) \\[Star] Int[1/Sqrt[a+b*x^2+c*x^4],x] +
          a*(B*d-A*e)*(e+d*q)/(c*d^2-a*e^2) \\[Star] Int[(1+q*x^2)/((d+e*x^2)*Sqrt[a+b*x^2+c*x^4]),x]] /;
        FreeQ[{a,b,c,d,e,A,B},x] && NeQ[c*d^2-a*e^2,0] && PosQ[c/a] && NeQ[c*A^2-a*B^2,0]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [capital_a__, capital_b__, d__, e__, a__, b__, c__, x_],
        optional: [capital_b__, e__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__, capital_a__, capital_b__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && neq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && neq!(&c__ * d__.pow(2) - &a__ * e__.pow(2), 0)
                && posq!(&c__ / &a__)
                && neq!(&c__ * capital_a__.pow(2) - &a__ * capital_b__.pow(2), 0)
        },
        rhs: {
            let q = rubi_rt(&(&c__ / &a__), 2);
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let denominator = &c__ * d__.pow(2) - &a__ * e__.pow(2);

            let first_integrand = Atom::num(1) / quartic.sqrt();
            let first = rubi_rhs_int(&first_integrand, x_);

            let second_integrand =
                (Atom::num(1) + &q * x_.pow(2)) / ((&d__ + &e__ * x_.pow(2)) * quartic.sqrt());
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(&capital_a__ * (&c__ * &d__ + &a__ * &e__ * &q)
                    - &a__ * &capital_b__ * (&e__ + &d__ * &q), first
                    / &denominator)
                    + rubi_star(&a__ * (&capital_b__ * &d__ - &capital_a__ * &e__) * (&e__ + &d__ * &q) / denominator, second)
        },
    ));
}

fn push_rules_rule_2227(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_a__, capital_b__, a__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 2227,
        source: "Int[(A_+B_.*x_^2)/((d_+e_.*x_^2)*Sqrt[a_+c_.*x_^4]),x_Symbol] :=
          With[{q=Rt[c/a,2]},
          (A*(c*d+a*e*q)-a*B*(e+d*q))/(c*d^2-a*e^2) \\[Star] Int[1/Sqrt[a+c*x^4],x] +
          a*(B*d-A*e)*(e+d*q)/(c*d^2-a*e^2) \\[Star] Int[(1+q*x^2)/((d+e*x^2)*Sqrt[a+c*x^4]),x]] /;
        FreeQ[{a,c,d,e,A,B},x] && NeQ[c*d^2-a*e^2,0] && PosQ[c/a] && NeQ[c*A^2-a*B^2,0]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [capital_a__, capital_b__, d__, e__, a__, c__, x_],
        optional: [capital_b__, e__, c__],
        when: {
            freeq!([a__, c__, d__, e__, capital_a__, capital_b__], x_)
                && neq!(&c__ * d__.pow(2) + &a__ * e__.pow(2), 0)
                && neq!(&c__ * d__.pow(2) - &a__ * e__.pow(2), 0)
                && posq!(&c__ / &a__)
                && neq!(&c__ * capital_a__.pow(2) - &a__ * capital_b__.pow(2), 0)
        },
        rhs: {
            let q = rubi_rt(&(&c__ / &a__), 2);
            let quartic = &a__ + &c__ * x_.pow(4);
            let denominator = &c__ * d__.pow(2) - &a__ * e__.pow(2);

            let first_integrand = Atom::num(1) / quartic.sqrt();
            let first = rubi_rhs_int(&first_integrand, x_);

            let second_integrand =
                (Atom::num(1) + &q * x_.pow(2)) / ((&d__ + &e__ * x_.pow(2)) * quartic.sqrt());
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(&capital_a__ * (&c__ * &d__ + &a__ * &e__ * &q)
                    - &a__ * &capital_b__ * (&e__ + &d__ * &q), first
                    / &denominator)
                    + rubi_star(&a__ * (&capital_b__ * &d__ - &capital_a__ * &e__) * (&e__ + &d__ * &q) / denominator, second)
        },
    ));
}

fn push_rules_rule_2228(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_a__, capital_b__, a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 2228,
        source: "Int[(A_+B_.*x_^2)/((d_+e_.*x_^2)*Sqrt[a_+b_.*x_^2+c_.*x_^4]),x_Symbol] :=
          B/e \\[Star] Int[1/Sqrt[a+b*x^2+c*x^4],x] + (e*A-d*B)/e \\[Star] Int[1/((d+e*x^2)*Sqrt[a+b*x^2+c*x^4]),x] /;
        FreeQ[{a,b,c,d,e,A,B},x] && NeQ[c*d^2-a*e^2,0] && NegQ[c/a]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [capital_a__, capital_b__, d__, e__, a__, b__, c__, x_],
        optional: [capital_b__, e__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__, capital_a__, capital_b__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && neq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && neq!(&c__ * d__.pow(2) - &a__ * e__.pow(2), 0)
                && negq!(&c__ / &a__)
        },
        rhs: {
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);

            let first_integrand = Atom::num(1) / quartic.sqrt();
            let first = rubi_rhs_int(&first_integrand, x_);

            let second_integrand = Atom::num(1) / ((&d__ + &e__ * x_.pow(2)) * quartic.sqrt());
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(&capital_b__, first / &e__)
                    + rubi_star(&e__ * &capital_a__ - &d__ * &capital_b__, second / &e__)
        },
    ));
}

fn push_rules_rule_2229(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_a__, capital_b__, a__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 2229,
        source: "Int[(A_+B_.*x_^2)/((d_+e_.*x_^2)*Sqrt[a_+c_.*x_^4]),x_Symbol] :=
          B/e \\[Star] Int[1/Sqrt[a+c*x^4],x] + (e*A-d*B)/e \\[Star] Int[1/((d+e*x^2)*Sqrt[a+c*x^4]),x] /;
        FreeQ[{a,c,d,e,A,B},x] && NeQ[c*d^2-a*e^2,0] && NegQ[c/a]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [capital_a__, capital_b__, d__, e__, a__, c__, x_],
        optional: [capital_b__, e__, c__],
        when: {
            freeq!([a__, c__, d__, e__, capital_a__, capital_b__], x_)
                && neq!(&c__ * d__.pow(2) + &a__ * e__.pow(2), 0)
                && neq!(&c__ * d__.pow(2) - &a__ * e__.pow(2), 0)
                && negq!(&c__ / &a__)
        },
        rhs: {
            let quartic = &a__ + &c__ * x_.pow(4);

            let first_integrand = Atom::num(1) / quartic.sqrt();
            let first = rubi_rhs_int(&first_integrand, x_);

            let second_integrand = Atom::num(1) / ((&d__ + &e__ * x_.pow(2)) * quartic.sqrt());
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(&capital_b__, first / &e__)
                    + rubi_star(&e__ * &capital_a__ - &d__ * &capital_b__, second / &e__)
        },
    ));
}

fn push_rules_rule_2230(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, p4x__, x_);
    rules.push(rubi_rule!(
        order: 2230,
        source: "Int[P4x_/((d_+e_.*x_^2)*Sqrt[a_+b_.*x_^2+c_.*x_^4]),x_Symbol] :=
          With[{A=Coeff[P4x,x,0],B=Coeff[P4x,x,2],C=Coeff[P4x,x,4]},
          -C/e^2 \\[Star] Int[(d-e*x^2)/Sqrt[a+b*x^2+c*x^4],x] +
          1/e^2 \\[Star] Int[(C*d^2+A*e^2+B*e^2*x^2)/((d+e*x^2)*Sqrt[a+b*x^2+c*x^4]),x]] /;
        FreeQ[{a,b,c,d,e},x] && PolyQ[P4x,x^2,2] && EqQ[c*d^2-a*e^2,0]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [p4x__, d__, e__, a__, b__, c__, x_],
        optional: [e__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && rubi_poly_q_power_degree(&p4x__, x_, &Atom::num(2), 2)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && neq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && eqq!(&c__ * d__.pow(2) - &a__ * e__.pow(2), 0)
        },
        rhs: {
            let A = rubi_coeff(&p4x__, x_, 0).rubi_rhs();
            let B = rubi_coeff(&p4x__, x_, 2).rubi_rhs();
            let C = rubi_coeff(&p4x__, x_, 4).rubi_rhs();
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);

            let first_integrand = (&d__ - &e__ * x_.pow(2)) / quartic.sqrt();
            let first = rubi_rhs_int(&first_integrand, x_);

            let second_integrand =
                (&C * d__.pow(2) + &A * e__.pow(2) + &B * e__.pow(2) * x_.pow(2))
                    / ((&d__ + &e__ * x_.pow(2)) * quartic.sqrt());
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(-&C, first / e__.pow(2)) + rubi_star(Atom::num(1) / e__.pow(2), second)
        },
    ));
}

fn push_rules_rule_2231(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, p4x__, x_);
    rules.push(rubi_rule!(
        order: 2231,
        source: "Int[P4x_/((d_+e_.*x_^2)*Sqrt[a_+c_.*x_^4]),x_Symbol] :=
          With[{A=Coeff[P4x,x,0],B=Coeff[P4x,x,2],C=Coeff[P4x,x,4]},
          -C/e^2 \\[Star] Int[(d-e*x^2)/Sqrt[a+c*x^4],x] +
          1/e^2 \\[Star] Int[(C*d^2+A*e^2+B*e^2*x^2)/((d+e*x^2)*Sqrt[a+c*x^4]),x]] /;
        FreeQ[{a,c,d,e},x] && PolyQ[P4x,x^2,2] && EqQ[c*d^2-a*e^2,0]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [p4x__, d__, e__, a__, c__, x_],
        optional: [e__, c__],
        when: {
            freeq!([a__, c__, d__, e__], x_)
                && rubi_poly_q_power_degree(&p4x__, x_, &Atom::num(2), 2)
                && neq!(&c__ * d__.pow(2) + &a__ * e__.pow(2), 0)
                && eqq!(&c__ * d__.pow(2) - &a__ * e__.pow(2), 0)
        },
        rhs: {
            let A = rubi_coeff(&p4x__, x_, 0).rubi_rhs();
            let B = rubi_coeff(&p4x__, x_, 2).rubi_rhs();
            let C = rubi_coeff(&p4x__, x_, 4).rubi_rhs();
            let quartic = &a__ + &c__ * x_.pow(4);

            let first_integrand = (&d__ - &e__ * x_.pow(2)) / quartic.sqrt();
            let first = rubi_rhs_int(&first_integrand, x_);

            let second_integrand =
                (&C * d__.pow(2) + &A * e__.pow(2) + &B * e__.pow(2) * x_.pow(2))
                    / ((&d__ + &e__ * x_.pow(2)) * quartic.sqrt());
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(-&C, first / e__.pow(2)) + rubi_star(Atom::num(1) / e__.pow(2), second)
        },
    ));
}

fn push_rules_rule_2232(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, p4x__, x_);
    rules.push(rubi_rule!(
        order: 2232,
        source: "Int[P4x_/((d_+e_.*x_^2)*Sqrt[a_+b_.*x_^2+c_.*x_^4]),x_Symbol] :=
          With[{q=Rt[c/a,2],A=Coeff[P4x,x,0],B=Coeff[P4x,x,2],C=Coeff[P4x,x,4]},
          -C/(e*q) \\[Star] Int[(1-q*x^2)/Sqrt[a+b*x^2+c*x^4],x] +
          1/(c*e) \\[Star] Int[(A*c*e+a*C*d*q+(B*c*e-C*(c*d-a*e*q))*x^2)/((d+e*x^2)*Sqrt[a+b*x^2+c*x^4]),x]] /;
        FreeQ[{a,b,c,d,e},x] && PolyQ[P4x,x^2,2] && NeQ[c*d^2-a*e^2,0] && PosQ[c/a] && Not[GtQ[b^2-4*a*c,0]]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [p4x__, d__, e__, a__, b__, c__, x_],
        optional: [e__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && rubi_poly_q_power_degree(&p4x__, x_, &Atom::num(2), 2)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && neq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && neq!(&c__ * d__.pow(2) - &a__ * e__.pow(2), 0)
                && posq!(&c__ / &a__)
                && !gtq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
        },
        rhs: {
            let q = rubi_rt(&(&c__ / &a__), 2);
            let A = rubi_coeff(&p4x__, x_, 0).rubi_rhs();
            let B = rubi_coeff(&p4x__, x_, 2).rubi_rhs();
            let C = rubi_coeff(&p4x__, x_, 4).rubi_rhs();
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);

            let first_integrand = (Atom::num(1) - &q * x_.pow(2)) / quartic.sqrt();
            let first = rubi_rhs_int(&first_integrand, x_);

            let second_integrand = (&A * &c__ * &e__
                + &a__ * &C * &d__ * &q
                + (&B * &c__ * &e__ - &C * (&c__ * &d__ - &a__ * &e__ * &q)) * x_.pow(2))
                / ((&d__ + &e__ * x_.pow(2)) * quartic.sqrt());
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(-&C, first / (&e__ * &q)) + rubi_star(Atom::num(1) / (&c__ * &e__), second)
        },
    ));
}

fn push_rules_rule_2233(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, p4x__, x_);
    rules.push(rubi_rule!(
        order: 2233,
        source: "Int[P4x_/((d_+e_.*x_^2)*Sqrt[a_+c_.*x_^4]),x_Symbol] :=
          With[{q=Rt[c/a,2],A=Coeff[P4x,x,0],B=Coeff[P4x,x,2],C=Coeff[P4x,x,4]},
          -C/(e*q) \\[Star] Int[(1-q*x^2)/Sqrt[a+c*x^4],x] +
          1/(c*e) \\[Star] Int[(A*c*e+a*C*d*q+(B*c*e-C*(c*d-a*e*q))*x^2)/((d+e*x^2)*Sqrt[a+c*x^4]),x]] /;
        FreeQ[{a,c,d,e},x] && PolyQ[P4x,x^2,2] && NeQ[c*d^2-a*e^2,0] && PosQ[c/a]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [p4x__, d__, e__, a__, c__, x_],
        optional: [e__, c__],
        when: {
            freeq!([a__, c__, d__, e__], x_)
                && rubi_poly_q_power_degree(&p4x__, x_, &Atom::num(2), 2)
                && neq!(&c__ * d__.pow(2) + &a__ * e__.pow(2), 0)
                && neq!(&c__ * d__.pow(2) - &a__ * e__.pow(2), 0)
                && posq!(&c__ / &a__)
        },
        rhs: {
            let q = rubi_rt(&(&c__ / &a__), 2);
            let A = rubi_coeff(&p4x__, x_, 0).rubi_rhs();
            let B = rubi_coeff(&p4x__, x_, 2).rubi_rhs();
            let C = rubi_coeff(&p4x__, x_, 4).rubi_rhs();
            let quartic = &a__ + &c__ * x_.pow(4);

            let first_integrand = (Atom::num(1) - &q * x_.pow(2)) / quartic.sqrt();
            let first = rubi_rhs_int(&first_integrand, x_);

            let second_integrand = (&A * &c__ * &e__
                + &a__ * &C * &d__ * &q
                + (&B * &c__ * &e__ - &C * (&c__ * &d__ - &a__ * &e__ * &q)) * x_.pow(2))
                / ((&d__ + &e__ * x_.pow(2)) * quartic.sqrt());
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(-&C, first / (&e__ * &q)) + rubi_star(Atom::num(1) / (&c__ * &e__), second)
        },
    ));
}

fn push_rules_rule_2234(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, p4x__, x_);
    rules.push(rubi_rule!(
        order: 2234,
        source: "Int[P4x_/((d_+e_.*x_^2)*Sqrt[a_+b_.*x_^2+c_.*x_^4]),x_Symbol] :=
          With[{A=Coeff[P4x,x,0],B=Coeff[P4x,x,2],C=Coeff[P4x,x,4]},
          -1/e^2 \\[Star] Int[(C*d-B*e-C*e*x^2)/Sqrt[a+b*x^2+c*x^4],x] +
          (C*d^2-B*d*e+A*e^2)/e^2 \\[Star] Int[1/((d+e*x^2)*Sqrt[a+b*x^2+c*x^4]),x]] /;
        FreeQ[{a,b,c,d,e},x] && PolyQ[P4x,x^2,2] && NeQ[c*d^2-a*e^2,0]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [p4x__, d__, e__, a__, b__, c__, x_],
        optional: [e__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && rubi_poly_q_power_degree(&p4x__, x_, &Atom::num(2), 2)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && neq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && neq!(&c__ * d__.pow(2) - &a__ * e__.pow(2), 0)
        },
        rhs: {
            let A = rubi_coeff(&p4x__, x_, 0).rubi_rhs();
            let B = rubi_coeff(&p4x__, x_, 2).rubi_rhs();
            let C = rubi_coeff(&p4x__, x_, 4).rubi_rhs();
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);

            let first_integrand = (&C * &d__ - &B * &e__ - &C * &e__ * x_.pow(2)) / quartic.sqrt();
            let first = rubi_rhs_int(&first_integrand, x_);

            let second_integrand = Atom::num(1) / ((&d__ + &e__ * x_.pow(2)) * quartic.sqrt());
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(-(Atom::num(1) / e__.pow(2)), first)
                    + rubi_star(&C * d__.pow(2) - &B * &d__ * &e__ + &A * e__.pow(2), second / e__.pow(2))
        },
    ));
}

fn push_rules_rule_2235(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, p4x__, x_);
    rules.push(rubi_rule!(
        order: 2235,
        source: "Int[P4x_/((d_+e_.*x_^2)*Sqrt[a_+c_.*x_^4]),x_Symbol] :=
          With[{A=Coeff[P4x,x,0],B=Coeff[P4x,x,2],C=Coeff[P4x,x,4]},
          -1/e^2 \\[Star] Int[(C*d-B*e-C*e*x^2)/Sqrt[a+c*x^4],x] +
          (C*d^2-B*d*e+A*e^2)/e^2 \\[Star] Int[1/((d+e*x^2)*Sqrt[a+c*x^4]),x]] /;
        FreeQ[{a,c,d,e},x] && PolyQ[P4x,x^2,2] && NeQ[c*d^2-a*e^2,0]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [p4x__, d__, e__, a__, c__, x_],
        optional: [e__, c__],
        when: {
            freeq!([a__, c__, d__, e__], x_)
                && rubi_poly_q_power_degree(&p4x__, x_, &Atom::num(2), 2)
                && neq!(&c__ * d__.pow(2) + &a__ * e__.pow(2), 0)
                && neq!(&c__ * d__.pow(2) - &a__ * e__.pow(2), 0)
        },
        rhs: {
            let A = rubi_coeff(&p4x__, x_, 0).rubi_rhs();
            let B = rubi_coeff(&p4x__, x_, 2).rubi_rhs();
            let C = rubi_coeff(&p4x__, x_, 4).rubi_rhs();
            let quartic = &a__ + &c__ * x_.pow(4);

            let first_integrand = (&C * &d__ - &B * &e__ - &C * &e__ * x_.pow(2)) / quartic.sqrt();
            let first = rubi_rhs_int(&first_integrand, x_);

            let second_integrand = Atom::num(1) / ((&d__ + &e__ * x_.pow(2)) * quartic.sqrt());
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(-(Atom::num(1) / e__.pow(2)), first)
                    + rubi_star(&C * d__.pow(2) - &B * &d__ * &e__ + &A * e__.pow(2), second / e__.pow(2))
        },
    ));
}

fn push_rules_rule_2236(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, px_, x_);
    rules.push(rubi_rule!(
        order: 2236,
        source: "Int[Px_/((d_+e_.*x_^2)*Sqrt[a_+b_.*x_^2+c_.*x_^4]),x_Symbol] :=
          With[{q=Expon[Px,x]},
          Coeff[Px,x,q]*x^(q-5)*Sqrt[a+b*x^2+c*x^4]/(c*e*(q-3)) +
          1/(c*e*(q-3)) \\[Star]
            Int[(c*e*(q-3)*Px-Coeff[Px,x,q]*x^(q-6)*(d+e*x^2)*(a*(q-5)+b*(q-4)*x^2+c*(q-3)*x^4))/
              ((d+e*x^2)*Sqrt[a+b*x^2+c*x^4]),x] /;
         GtQ[q,4]] /;
        FreeQ[{a,b,c,d,e},x] && PolyQ[Px,x]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern: px_ / ((d__ + e__ * x_.pow(2)) * (a__ + b__ * x_.pow(2) + c__ * x_.pow(4)).sqrt()),
        with: [px_, d__, e__, a__, b__, c__, x_],
        optional: [e__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && rubi_poly_q(&px_, x_)
                && rubi_expon(&px_, x_).is_some_and(|q| gtq!(Atom::num(q), 4))
        },
        rhs: {
            let q = rubi_expon(&px_, x_).rubi_rhs();
            let q_atom = Atom::num(q);
            let coeff = rubi_coeff(&px_, x_, q).rubi_rhs();
            let quadratic = &d__ + &e__ * x_.pow(2);
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let denominator = &c__ * &e__ * (&q_atom - Atom::num(3));

            let direct = &coeff * x_.pow(q - 5) * quartic.sqrt() / &denominator;
            let recursive_numerator = &c__ * &e__ * (&q_atom - Atom::num(3)) * &px_
                - &coeff
                    * x_.pow(q - 6)
                    * &quadratic
                    * (&a__ * (&q_atom - Atom::num(5))
                        + &b__ * (&q_atom - Atom::num(4)) * x_.pow(2)
                        + &c__ * (&q_atom - Atom::num(3)) * x_.pow(4));
            let recursive_integrand = recursive_numerator / (quadratic * quartic.sqrt());
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_2237(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, c__, d__, e__, px_, x_);
    rules.push(rubi_rule!(
        order: 2237,
        source: "Int[Px_/((d_+e_.*x_^2)*Sqrt[a_+c_.*x_^4]),x_Symbol] :=
          With[{q=Expon[Px,x]},
          Coeff[Px,x,q]*x^(q-5)*Sqrt[a+c*x^4]/(c*e*(q-3)) +
          1/(c*e*(q-3)) \\[Star]
            Int[(c*e*(q-3)*Px-Coeff[Px,x,q]*x^(q-6)*(d+e*x^2)*(a*(q-5)+c*(q-3)*x^4))/((d+e*x^2)*Sqrt[a+c*x^4]),x] /;
         GtQ[q,4]] /;
        FreeQ[{a,c,d,e},x] && PolyQ[Px,x]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern: px_ / ((d__ + e__ * x_.pow(2)) * (a__ + c__ * x_.pow(4)).sqrt()),
        with: [px_, d__, e__, a__, c__, x_],
        optional: [e__, c__],
        when: {
            freeq!([a__, c__, d__, e__], x_)
                && rubi_poly_q(&px_, x_)
                && rubi_expon(&px_, x_).is_some_and(|q| gtq!(Atom::num(q), 4))
        },
        rhs: {
            let q = rubi_expon(&px_, x_).rubi_rhs();
            let q_atom = Atom::num(q);
            let coeff = rubi_coeff(&px_, x_, q).rubi_rhs();
            let quadratic = &d__ + &e__ * x_.pow(2);
            let quartic = &a__ + &c__ * x_.pow(4);
            let denominator = &c__ * &e__ * (&q_atom - Atom::num(3));

            let direct = &coeff * x_.pow(q - 5) * quartic.sqrt() / &denominator;
            let recursive_numerator = &c__ * &e__ * (&q_atom - Atom::num(3)) * &px_
                - &coeff
                    * x_.pow(q - 6)
                    * &quadratic
                    * (&a__ * (&q_atom - Atom::num(5))
                        + &c__ * (&q_atom - Atom::num(3)) * x_.pow(4));
            let recursive_integrand = recursive_numerator / (quadratic * quartic.sqrt());
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_2258(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, px__, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 2258,
        source: "Int[Px_*(d_+e_.*x_^2)^q_.*(a_+b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
          Int[ExpandIntegrand[1/Sqrt[a+b*x^2+c*x^4],Px*(d+e*x^2)^q*(a+b*x^2+c*x^4)^(p+1/2),x],x] /;
        FreeQ[{a,b,c,d,e},x] && PolyQ[Px,x] && IntegerQ[p+1/2] && IntegerQ[q]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [px__, d__, e__, q_, a__, b__, c__, p_, x_],
        optional: [e__, q_, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && rubi_poly_q(&px__, x_)
                && integerq!(&p_ + Atom::num(1) / Atom::num(2))
                && integerq!(q_)
        },
        rhs: {
            let quadratic = &d__ + &e__ * x_.pow(2);
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let u = Atom::num(1) / quartic.sqrt();
            let v_expr = px__
                * quadratic.pow(&q_)
                * quartic.pow(&p_ + Atom::num(1) / Atom::num(2));
            let expanded = rubi_expand_integrand_product(&u, &v_expr, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_2259(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, px__, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 2259,
        source: "Int[Px_*(d_+e_.*x_^2)^q_.*(a_+c_.*x_^4)^p_,x_Symbol] :=
          Int[ExpandIntegrand[1/Sqrt[a+c*x^4],Px*(d+e*x^2)^q*(a+c*x^4)^(p+1/2),x],x] /;
        FreeQ[{a,c,d,e},x] && PolyQ[Px,x] && IntegerQ[p+1/2] && IntegerQ[q]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [px__, d__, e__, q_, a__, c__, p_, x_],
        optional: [e__, q_, c__],
        when: {
            freeq!([a__, c__, d__, e__], x_)
                && rubi_poly_q(&px__, x_)
                && integerq!(&p_ + Atom::num(1) / Atom::num(2))
                && integerq!(q_)
        },
        rhs: {
            let quadratic = &d__ + &e__ * x_.pow(2);
            let quartic = &a__ + &c__ * x_.pow(4);
            let u = Atom::num(1) / quartic.sqrt();
            let v_expr = px__
                * quadratic.pow(&q_)
                * quartic.pow(&p_ + Atom::num(1) / Atom::num(2));
            let expanded = rubi_expand_integrand_product(&u, &v_expr, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_2239(rules: &mut Vec<RubiRule>) {
    rubi_symb!(px__, a__, c__, d__, e__, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 2239,
        source: "Int[x_*Px_*(d_+e_.*x_^2)^q_.*(a_+c_.*x_^4)^p_.,x_Symbol] :=
          1/2 \\[Star] Subst[Int[ReplaceAll[Px,x->Sqrt[x]]*(d+e*x)^q*(a+c*x^2)^p,x],x,x^2] /;
        FreeQ[{a,c,d,e,p,q},x] && PolyQ[Px,x^2]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern: x_
            * px__
            * (d__ + e__ * x_.pow(2)).pow(q_)
            * (a__ + c__ * x_.pow(4)).pow(p_),
        with: [px__, d__, e__, q_, a__, c__, p_, x_],
        optional: [e__, q_, c__, p_],
        x_free: [a__, c__, d__, e__, p_, q_],
        when: { rubi_poly_q_power(&px__, x_, &Atom::num(2)) },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_px = rubi_replace_all(&px__, x_, sub_atom.sqrt());
            let transformed_integrand = transformed_px
                * (&d__ + &e__ * &sub_atom).pow(&q_)
                * (&a__ + &c__ * sub_atom.pow(2)).pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);
            let substituted = rubi_subst(&transformed, sub, x_.pow(2));

            rubi_star(Atom::num(1) / 2, substituted)
        },
    ));
}

fn push_rules_rule_2240(rules: &mut Vec<RubiRule>) {
    rubi_symb!(pr__, a__, b__, c__, d__, e__, f__, m_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 2240,
        source: "Int[Pr_*(f_.*x_)^m_.*(d_+e_.*x_^2)^q_.*(a_+b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
          Module[{r=Expon[Pr,x],k},
          Int[Sum[Coeff[Pr,x,2*k]*x^(2*k),{k,0,r/2+1}]*(f*x)^m*(d+e*x^2)^q*(a+b*x^2+c*x^4)^p,x] +
          1/f \\[Star] Int[Sum[Coeff[Pr,x,2*k+1]*x^(2*k),{k,0,(r+1)/2}]*(f*x)^(m+1)*(d+e*x^2)^q*(a+b*x^2+c*x^4)^p,x]] /;
        FreeQ[{a,b,c,d,e,f,m,p,q},x] && PolyQ[Pr,x] && Not[PolyQ[Pr,x^2]]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern: pr__
            * (f__ * x_).pow(m_)
            * (d__ + e__ * x_.pow(2)).pow(q_)
            * (a__ + b__ * x_.pow(2) + c__ * x_.pow(4)).pow(p_),
        with: [pr__, f__, m_, d__, e__, q_, a__, b__, c__, p_, x_],
        optional: [f__, m_, e__, q_, b__, c__],
        x_free: [a__, b__, c__, d__, e__, f__, m_, p_, q_],
        when: { rubi_poly_q(&pr__, x_) && !rubi_poly_q_power(&pr__, x_, &Atom::num(2)) },
        rhs: {
            let r = rubi_expon(&pr__, x_).rubi_rhs();
            let fx = &f__ * x_;
            let quadratic = &d__ + &e__ * x_.pow(2);
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let mut even_sum = Atom::num(0);
            for k in 0..=(r / 2 + 1) {
                even_sum += rubi_coeff(&pr__, x_, 2 * k).rubi_rhs() * x_.pow(2 * k);
            }
            let mut odd_sum = Atom::num(0);
            for k in 0..=((r - 1) / 2 + 1) {
                odd_sum += rubi_coeff(&pr__, x_, 2 * k + 1).rubi_rhs() * x_.pow(2 * k);
            }
            let first = rubi_rhs_int(
                &(even_sum * fx.pow(&m_) * quadratic.pow(&q_) * quartic.pow(&p_)),
                x_,
            );
            let second = rubi_rhs_int(
                &(odd_sum * fx.pow(&m_ + 1) * quadratic.pow(&q_) * quartic.pow(&p_)),
                x_,
            );

            first + rubi_star(Atom::num(1) / &f__, second)
        },
    ));
}

fn push_rules_rule_2241(rules: &mut Vec<RubiRule>) {
    rubi_symb!(pr__, a__, c__, d__, e__, f__, m_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 2241,
        source: "Int[Pr_*(f_.*x_)^m_.*(d_+e_.*x_^2)^q_.*(a_+c_.*x_^4)^p_,x_Symbol] :=
          Module[{r=Expon[Pr,x],k},
          Int[Sum[Coeff[Pr,x,2*k]*x^(2*k),{k,0,r/2+1}]*(f*x)^m*(d+e*x^2)^q*(a+c*x^4)^p,x] +
          1/f \\[Star] Int[Sum[Coeff[Pr,x,2*k+1]*x^(2*k),{k,0,(r+1)/2}]*(f*x)^(m+1)*(d+e*x^2)^q*(a+c*x^4)^p,x]] /;
        FreeQ[{a,c,d,e,f,m,p,q},x] && PolyQ[Pr,x] && Not[PolyQ[Pr,x^2]]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern: pr__
            * (f__ * x_).pow(m_)
            * (d__ + e__ * x_.pow(2)).pow(q_)
            * (a__ + c__ * x_.pow(4)).pow(p_),
        with: [pr__, f__, m_, d__, e__, q_, a__, c__, p_, x_],
        optional: [f__, m_, e__, q_, c__],
        x_free: [a__, c__, d__, e__, f__, m_, p_, q_],
        when: { rubi_poly_q(&pr__, x_) && !rubi_poly_q_power(&pr__, x_, &Atom::num(2)) },
        rhs: {
            let r = rubi_expon(&pr__, x_).rubi_rhs();
            let fx = &f__ * x_;
            let quadratic = &d__ + &e__ * x_.pow(2);
            let quartic = &a__ + &c__ * x_.pow(4);
            let mut even_sum = Atom::num(0);
            for k in 0..=(r / 2 + 1) {
                even_sum += rubi_coeff(&pr__, x_, 2 * k).rubi_rhs() * x_.pow(2 * k);
            }
            let mut odd_sum = Atom::num(0);
            for k in 0..=((r - 1) / 2 + 1) {
                odd_sum += rubi_coeff(&pr__, x_, 2 * k + 1).rubi_rhs() * x_.pow(2 * k);
            }
            let first = rubi_rhs_int(
                &(even_sum * fx.pow(&m_) * quadratic.pow(&q_) * quartic.pow(&p_)),
                x_,
            );
            let second = rubi_rhs_int(
                &(odd_sum * fx.pow(&m_ + 1) * quadratic.pow(&q_) * quartic.pow(&p_)),
                x_,
            );

            first + rubi_star(Atom::num(1) / &f__, second)
        },
    ));
}

fn push_rules_rule_2246(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; px__, a__, b__, c__, d__, e__, f__, m_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 2246,
        source: "Int[Px_*(f_.*x_)^m_.*(d_+e_.*x_^2)^q_.*(a_+b_.*x_^2+c_.*x_^4)^p_.,x_Symbol] :=
          Int[ExpandIntegrand[Px*(f*x)^m*(d+e*x^2)^q*(a+b*x^2+c*x^4)^p,x],x] /;
        FreeQ[{a,b,c,d,e,f,m,q},x] && PolyQ[Px,x] && IntegerQ[p]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_10(symbols),
        with: [px__, f__, m_, d__, e__, q_, a__, b__, c__, p_, x_],
        optional: [f__, m_, e__, q_, b__, c__, p_],
        x_free: [a__, b__, c__, d__, e__, f__, m_, q_],
        when: { rubi_poly_q(&px__, x_) && integerq!(p_) },
        rhs: {
            let integrand = &px__
                * (&f__ * x_).pow(&m_)
                * (&d__ + &e__ * x_.pow(2)).pow(&q_)
                * (&a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4)).pow(&p_);
            let expanded = rubi_expand_integrand(&integrand, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_2247(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; px__, a__, c__, d__, e__, f__, m_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 2247,
        source: "Int[Px_*(f_.*x_)^m_.*(d_+e_.*x_^2)^q_.*(a_+c_.*x_^4)^p_.,x_Symbol] :=
          Int[ExpandIntegrand[Px*(f*x)^m*(d+e*x^2)^q*(a+c*x^4)^p,x],x] /;
        FreeQ[{a,c,d,e,f,m,q},x] && PolyQ[Px,x] && IntegerQ[p]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_11(symbols),
        with: [px__, f__, m_, d__, e__, q_, a__, c__, p_, x_],
        optional: [f__, m_, e__, q_, c__, p_],
        x_free: [a__, c__, d__, e__, f__, m_, q_],
        when: { rubi_poly_q(&px__, x_) && integerq!(p_) },
        rhs: {
            let integrand = &px__
                * (&f__ * x_).pow(&m_)
                * (&d__ + &e__ * x_.pow(2)).pow(&q_)
                * (&a__ + &c__ * x_.pow(4)).pow(&p_);
            let expanded = rubi_expand_integrand(&integrand, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_2248(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; px__, a__, b__, c__, d__, e__, f__, m_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 2248,
        source: "Int[Px_*(f_.*x_)^m_.*(d_+e_.*x_^2)^q_.*(a_+b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
          Int[ExpandIntegrand[1/Sqrt[a+b*x^2+c*x^4],Px*(f*x)^m*(d+e*x^2)^q*(a+b*x^2+c*x^4)^(p+1/2),x],x] /;
        FreeQ[{a,b,c,d,e,f,m},x] && PolyQ[Px,x] && IntegerQ[p+1/2] && IntegerQ[q]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_10(symbols),
        with: [px__, f__, m_, d__, e__, q_, a__, b__, c__, p_, x_],
        optional: [f__, m_, e__, q_, b__, c__],
        x_free: [a__, b__, c__, d__, e__, f__, m_],
        when: { rubi_poly_q(&px__, x_) && integerq!(&p_ + (1, 2)) && integerq!(q_) },
        rhs: {
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let first_factor = Atom::num(1) / quartic.sqrt();
            let second_factor = &px__
                * (&f__ * x_).pow(&m_)
                * (&d__ + &e__ * x_.pow(2)).pow(&q_)
                * quartic.pow(&p_ + (1, 2));
            let expanded = rubi_expand_integrand_product(&first_factor, &second_factor, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_2249(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; px__, a__, c__, d__, e__, f__, m_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 2249,
        source: "Int[Px_*(f_.*x_)^m_.*(d_+e_.*x_^2)^q_.*(a_+c_.*x_^4)^p_,x_Symbol] :=
          Int[ExpandIntegrand[1/Sqrt[a+c*x^4],Px*(f*x)^m*(d+e*x^2)^q*(a+c*x^4)^(p+1/2),x],x] /;
        FreeQ[{a,c,d,e,f,m},x] && PolyQ[Px,x] && IntegerQ[p+1/2] && IntegerQ[q]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_11(symbols),
        with: [px__, f__, m_, d__, e__, q_, a__, c__, p_, x_],
        optional: [f__, m_, e__, q_, c__],
        x_free: [a__, c__, d__, e__, f__, m_],
        when: { rubi_poly_q(&px__, x_) && integerq!(&p_ + (1, 2)) && integerq!(q_) },
        rhs: {
            let quartic = &a__ + &c__ * x_.pow(4);
            let first_factor = Atom::num(1) / quartic.sqrt();
            let second_factor = &px__
                * (&f__ * x_).pow(&m_)
                * (&d__ + &e__ * x_.pow(2)).pow(&q_)
                * quartic.pow(&p_ + (1, 2));
            let expanded = rubi_expand_integrand_product(&first_factor, &second_factor, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_2250(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; px__, a__, b__, c__, d__, e__, f__, m_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 2250,
        source: "Int[Px_*(f_.*x_)^m_.*(d_+e_.*x_^2)^q_.*(a_+b_.*x_^2+c_.*x_^4)^p_.,x_Symbol] :=
          Unintegrable[Px*(f*x)^m*(d+e*x^2)^q*(a+b*x^2+c*x^4)^p,x] /;
        FreeQ[{a,b,c,d,e,f,m,p,q},x] && PolyQ[Px,x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_10(symbols),
        with: [px__, f__, m_, d__, e__, q_, a__, b__, c__, p_, x_],
        optional: [f__, m_, e__, q_, b__, c__, p_],
        x_free: [a__, b__, c__, d__, e__, f__, m_, p_, q_],
        when: { rubi_poly_q(&px__, x_) },
        rhs: {
            rubi_unintegrable(
                &px__
                    * (&f__ * x_).pow(&m_)
                    * (&d__ + &e__ * x_.pow(2)).pow(&q_)
                    * (&a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4)).pow(&p_),
                x_,
            )
        },
    ));
}

fn push_rules_rule_2251(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; px__, a__, c__, d__, e__, f__, m_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 2251,
        source: "Int[Px_*(f_.*x_)^m_.*(d_+e_.*x_^2)^q_.*(a_+c_.*x_^4)^p_.,x_Symbol] :=
          Unintegrable[Px*(f*x)^m*(d+e*x^2)^q*(a+c*x^4)^p,x] /;
        FreeQ[{a,c,d,e,f,m,p,q},x] && PolyQ[Px,x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_11(symbols),
        with: [px__, f__, m_, d__, e__, q_, a__, c__, p_, x_],
        optional: [f__, m_, e__, q_, c__, p_],
        x_free: [a__, c__, d__, e__, f__, m_, p_, q_],
        when: { rubi_poly_q(&px__, x_) },
        rhs: {
            rubi_unintegrable(
                &px__
                    * (&f__ * x_).pow(&m_)
                    * (&d__ + &e__ * x_.pow(2)).pow(&q_)
                    * (&a__ + &c__ * x_.pow(4)).pow(&p_),
                x_,
            )
        },
    ));
}

fn push_rules_rule_2255(rules: &mut Vec<RubiRule>) {
    rubi_symb!(pr__, a__, c__, d__, e__, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 2255,
        source: "Int[Pr_*(d_+e_.*x_^2)^q_.*(a_+c_.*x_^4)^p_,x_Symbol] :=
          Module[{r=Expon[Pr,x],k},
          Int[Sum[Coeff[Pr,x,2*k]*x^(2*k),{k,0,r/2}]*(d+e*x^2)^q*(a+c*x^4)^p,x] +
          Int[x*Sum[Coeff[Pr,x,2*k+1]*x^(2*k),{k,0,(r-1)/2}]*(d+e*x^2)^q*(a+c*x^4)^p,x]] /;
        FreeQ[{a,c,d,e,p,q},x] && PolyQ[Pr,x] && Not[PolyQ[Pr,x^2]]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern: pr__
            * (d__ + e__ * x_.pow(2)).pow(q_)
            * (a__ + c__ * x_.pow(4)).pow(p_),
        with: [pr__, d__, e__, q_, a__, c__, p_, x_],
        optional: [e__, q_, c__],
        x_free: [a__, c__, d__, e__, p_, q_],
        when: { rubi_poly_q(&pr__, x_) && !rubi_poly_q_power(&pr__, x_, &Atom::num(2)) },
        rhs: {
            let r = rubi_expon(&pr__, x_).rubi_rhs();
            let quadratic = &d__ + &e__ * x_.pow(2);
            let quartic = &a__ + &c__ * x_.pow(4);
            let mut even_sum = Atom::num(0);
            for k in 0..=(r / 2) {
                even_sum += rubi_coeff(&pr__, x_, 2 * k).rubi_rhs() * x_.pow(2 * k);
            }
            let mut odd_sum = Atom::num(0);
            if r >= 1 {
                for k in 0..=((r - 1) / 2) {
                    odd_sum += rubi_coeff(&pr__, x_, 2 * k + 1).rubi_rhs() * x_.pow(2 * k);
                }
            }
            let first = rubi_rhs_int(
                &(even_sum * quadratic.pow(&q_) * quartic.pow(&p_)),
                x_,
            );
            let second = rubi_rhs_int(
                &(x_ * odd_sum * quadratic.pow(&q_) * quartic.pow(&p_)),
                x_,
            );

            first + second
        },
    ));
}

// Generated shared pattern builders.

#[inline(never)]
fn rubi_shared_pattern_0(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let capital_a__ = symbols.capital_a__;
    let capital_b__ = symbols.capital_b__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let x_ = symbols.x_;
    (capital_a__ + capital_b__ * x_.pow(2))
        / ((d__ + e__ * x_.pow(2)) * (a__ + b__ * x_.pow(2) + c__ * x_.pow(4)).sqrt())
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let c__ = symbols.c__;
    let capital_a__ = symbols.capital_a__;
    let capital_b__ = symbols.capital_b__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let x_ = symbols.x_;
    (capital_a__ + capital_b__ * x_.pow(2))
        / ((d__ + e__ * x_.pow(2)) * (a__ + c__ * x_.pow(4)).sqrt())
}

#[inline(never)]
fn rubi_shared_pattern_2(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let p4x__ = symbols.p4x__;
    let q_ = symbols.q_;
    let x_ = symbols.x_;
    (d__ + e__ * x_.pow(2)).pow(q_) * p4x__ / (a__ + b__ * x_.pow(2) + c__ * x_.pow(4)).sqrt()
}

#[inline(never)]
fn rubi_shared_pattern_3(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let p4x__ = symbols.p4x__;
    let q_ = symbols.q_;
    let x_ = symbols.x_;
    (d__ + e__ * x_.pow(2)).pow(q_) * p4x__ / (a__ + c__ * x_.pow(4)).sqrt()
}

#[inline(never)]
fn rubi_shared_pattern_4(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let p4x__ = symbols.p4x__;
    let x_ = symbols.x_;
    p4x__ / ((d__ + e__ * x_.pow(2)) * (a__ + b__ * x_.pow(2) + c__ * x_.pow(4)).sqrt())
}

#[inline(never)]
fn rubi_shared_pattern_5(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let p4x__ = symbols.p4x__;
    let x_ = symbols.x_;
    p4x__ / ((d__ + e__ * x_.pow(2)) * (a__ + c__ * x_.pow(4)).sqrt())
}

#[inline(never)]
fn rubi_shared_pattern_6(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let m_ = symbols.m_;
    let px_ = symbols.px_;
    let x_ = symbols.x_;
    px_ * x_.pow(m_) / ((d__ + e__ * x_.pow(2)) * (a__ + b__ * x_.pow(2) + c__ * x_.pow(4)).sqrt())
}

#[inline(never)]
fn rubi_shared_pattern_7(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let m_ = symbols.m_;
    let px_ = symbols.px_;
    let x_ = symbols.x_;
    px_ * x_.pow(m_) / ((d__ + e__ * x_.pow(2)) * (a__ + c__ * x_.pow(4)).sqrt())
}

#[inline(never)]
fn rubi_shared_pattern_8(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let p_ = symbols.p_;
    let px__ = symbols.px__;
    let q_ = symbols.q_;
    let x_ = symbols.x_;
    px__ * (d__ + e__ * x_.pow(2)).pow(q_) * (a__ + b__ * x_.pow(2) + c__ * x_.pow(4)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_9(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let p_ = symbols.p_;
    let px__ = symbols.px__;
    let q_ = symbols.q_;
    let x_ = symbols.x_;
    px__ * (d__ + e__ * x_.pow(2)).pow(q_) * (a__ + c__ * x_.pow(4)).pow(p_)
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
    let p_ = symbols.p_;
    let px__ = symbols.px__;
    let q_ = symbols.q_;
    let x_ = symbols.x_;
    px__ * (f__ * x_).pow(m_)
        * (d__ + e__ * x_.pow(2)).pow(q_)
        * (a__ + b__ * x_.pow(2) + c__ * x_.pow(4)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_11(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let p_ = symbols.p_;
    let px__ = symbols.px__;
    let q_ = symbols.q_;
    let x_ = symbols.x_;
    px__ * (f__ * x_).pow(m_) * (d__ + e__ * x_.pow(2)).pow(q_) * (a__ + c__ * x_.pow(4)).pow(p_)
}
