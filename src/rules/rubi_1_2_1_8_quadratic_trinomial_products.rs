use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_2188(rules);
    push_rules_rule_2189(rules);
    push_rules_rule_2190(rules);
    push_rules_rule_2191(rules);
    push_rules_rule_2192(rules);
}

fn push_rules_rule_2188(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2188,
        source: "Int[Pq_*(a_+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
          Int[ExpandIntegrand[Pq*(a+b*x+c*x^2)^p,x],x] /;
        FreeQ[{a,b,c},x] && PolyQ[Pq,x] && IGtQ[p,-2]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [pq__, a__, b__, c__, p_, x_],
        optional: [b__, c__, p_],
        when: {
            freeq!([a__, b__, c__], x_) && poly_q(&pq__, x_) && igtq!(p_, -2)
        },
        rhs: {
            let integrand = &pq__ * (&a__ + &b__ * x_ + &c__ * x_.pow(2)).pow(&p_);
            let expanded = rubi_expand_integrand(&integrand, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_2189(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2189,
        source: "Int[Pq_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          Int[x*PolynomialQuotient[Pq,x,x]*(a+b*x+c*x^2)^p,x] /;
        FreeQ[{a,b,c,p},x] && PolyQ[Pq,x] && EqQ[Coeff[Pq,x,0],0] && Not[MatchQ[Pq,x^m_.*u_. /; IntegerQ[m]]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [pq__, a__, b__, c__, p_, x_],
        optional: [a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, p_], x_)
                && poly_q(&pq__, x_)
                && polynomial_coefficient(&pq__, x_, 0).is_some_and(|coefficient| eqq!(coefficient, 0))
                && !visible_integer_power_of_variable_factor(&pq__, x_)
        },
        rhs: {
            let quotient = rubi_polynomial_quotient(&pq__, x_, x_).rubi_rhs();
            let transformed = x_ * quotient * (&a__ + &b__ * x_ + &c__ * x_.pow(2)).pow(&p_);

            rubi_rhs_int(&transformed, x_)
        },
    ));
}

fn push_rules_rule_2190(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2190,
        source: "Int[Pq_*(a_+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          (a+b*x+c*x^2)^FracPart[p]/((4*c)^IntPart[p]*(b+2*c*x)^(2*FracPart[p])) \\[Star] Int[Pq*(b+2*c*x)^(2*p),x] /;
        FreeQ[{a,b,c,p},x] && PolyQ[Pq,x] && EqQ[b^2-4*a*c,0]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [pq__, a__, b__, c__, p_, x_],
        optional: [b__, c__],
        when: {
            freeq!([a__, b__, c__, p_], x_)
                && poly_q(&pq__, x_)
                && !c__.expand().is_zero()
                && eqq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
        },
        rhs: {
            if c__.expand().is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let frac_p = rubi_frac_part(&p_);
            let linear = &b__ + Atom::num(2) * &c__ * x_;
            let denominator = (Atom::num(4) * &c__).pow(rubi_int_part(&p_)) * linear.pow(Atom::num(2) * &frac_p);
            if denominator.expand().is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let trinomial = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let recursive = rubi_rhs_int(&(&pq__ * linear.pow(Atom::num(2) * &p_)), x_);

            rubi_star(trinomial.pow(&frac_p), recursive / denominator)
        },
    ));
}

fn push_rules_rule_2191(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2191,
        source: "Int[Pq_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          With[{Q=PolynomialQuotient[Pq,a+b*x+c*x^2,x],
                f=Coeff[PolynomialRemainder[Pq,a+b*x+c*x^2,x],x,0],
                g=Coeff[PolynomialRemainder[Pq,a+b*x+c*x^2,x],x,1]},
          (b*f-2*a*g+(2*c*f-b*g)*x)*(a+b*x+c*x^2)^(p+1)/((p+1)*(b^2-4*a*c)) +
          1/((p+1)*(b^2-4*a*c)) \\[Star] Int[(a+b*x+c*x^2)^(p+1)*ExpandToSum[(p+1)*(b^2-4*a*c)*Q-(2*p+3)*(2*c*f-b*g),x],x]] /;
        FreeQ[{a,b,c},x] && PolyQ[Pq,x] && NeQ[b^2-4*a*c,0] && LtQ[p,-1]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [pq__, a__, b__, c__, p_, x_],
        optional: [a__, b__, c__],
        when: {
            freeq!([a__, b__, c__], x_)
                && poly_q(&pq__, x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && ltq!(p_, -1)
        },
        rhs: {
            let trinomial = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let discriminant = b__.pow(2) - Atom::num(4) * &a__ * &c__;
            let raised_p = &p_ + Atom::num(1);
            let denominator = &raised_p * &discriminant;
            if denominator.expand().is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let (capital_q, capital_r) = polynomial_quotient_remainder(&pq__, &trinomial, x_).rubi_rhs();
            let f = polynomial_coefficient(&capital_r, x_, 0).rubi_rhs();
            let g = polynomial_coefficient(&capital_r, x_, 1).rubi_rhs();
            let direct_numerator = &b__ * &f - Atom::num(2) * &a__ * &g + (Atom::num(2) * &c__ * &f - &b__ * &g) * x_;
            let direct = direct_numerator * trinomial.pow(&raised_p) / &denominator;
            let expand_to_sum = rubi_expand_to_sum(
                &(&raised_p * &discriminant * capital_q
                    - (Atom::num(2) * &p_ + Atom::num(3))
                        * (Atom::num(2) * &c__ * &f - &b__ * &g)),
                x_,
            );
            let recursive = rubi_rhs_int(&(trinomial.pow(raised_p) * expand_to_sum), x_);

            rubi_simp(&direct, x_) + rubi_star(Atom::num(1) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_2192(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2192,
        source: "Int[Pq_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          With[{q=Expon[Pq,x],e=Coeff[Pq,x,Expon[Pq,x]]},
          e*x^(q-1)*(a+b*x+c*x^2)^(p+1)/(c*(q+2*p+1)) +
          1/(c*(q+2*p+1)) \\[Star] Int[(a+b*x+c*x^2)^p*
            ExpandToSum[c*(q+2*p+1)*Pq-a*e*(q-1)*x^(q-2)-b*e*(q+p)*x^(q-1)-c*e*(q+2*p+1)*x^q,x],x]] /;
        FreeQ[{a,b,c,p},x] && PolyQ[Pq,x] && NeQ[b^2-4*a*c,0] && Not[LeQ[p,-1]]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [pq__, a__, b__, c__, p_, x_],
        optional: [a__, b__, c__],
        when: {
            freeq!([a__, b__, c__, p_], x_)
                && poly_q(&pq__, x_)
                && !c__.expand().is_zero()
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && !leq!(p_, -1)
        },
        rhs: {
            if c__.expand().is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let q = rubi_expon(&pq__, x_).rubi_rhs();
            let e = rubi_coeff(&pq__, x_, q).rubi_rhs();
            let q_atom = Atom::num(q);
            let denominator = &c__ * (&q_atom + Atom::num(2) * &p_ + Atom::num(1));
            if denominator.expand().is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let trinomial = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let raised_p = &p_ + Atom::num(1);
            let direct = &e * x_.pow(q - 1) * trinomial.pow(&raised_p) / &denominator;
            let expand_to_sum = rubi_expand_to_sum(
                &(&c__ * (&q_atom + Atom::num(2) * &p_ + Atom::num(1)) * &pq__
                    - &a__ * &e * (&q_atom - Atom::num(1)) * x_.pow(q - 2)
                    - &b__ * &e * (&q_atom + &p_) * x_.pow(q - 1)
                    - &c__
                        * &e
                        * (&q_atom + Atom::num(2) * &p_ + Atom::num(1))
                        * x_.pow(q)),
                x_,
            );
            let recursive = rubi_rhs_int(&(trinomial.pow(&p_) * expand_to_sum), x_);

            rubi_simp(&direct, x_) + rubi_star(Atom::num(1) / denominator, recursive)
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
    let pq__ = symbols.pq__;
    let x_ = symbols.x_;
    pq__ * (a__ + b__ * x_ + c__ * x_.pow(2)).pow(p_)
}
