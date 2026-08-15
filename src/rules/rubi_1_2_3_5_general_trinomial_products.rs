use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_2308(rules);
    push_rules_rule_2309(rules);
    push_rules_rule_2310(rules);
    push_rules_rule_2311(rules);
    push_rules_rule_2312(rules);
    push_rules_rule_2313(rules);
    push_rules_rule_2314(rules);
    push_rules_rule_2315(rules);
    push_rules_rule_2316(rules);
    push_rules_rule_2317(rules);
    push_rules_rule_2318(rules);
    push_rules_rule_2319(rules);
    push_rules_rule_2320(rules);
    push_rules_rule_2321(rules);
    push_rules_rule_2322(rules);
    push_rules_rule_2323(rules);
    push_rules_rule_2324(rules);
    push_rules_rule_2325(rules);
    push_rules_rule_2326(rules);
    push_rules_rule_2327(rules);
    push_rules_rule_2328(rules);
    push_rules_rule_2329(rules);
    push_rules_rule_2330(rules);
}

fn push_rules_rule_2308(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, n_, n2_, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2308,
        source: "Int[Pq_*(a_+b_.*x_^n_.+c_.*x_^n2_.)^p_.,x_Symbol] :=
          Int[ExpandIntegrand[Pq*(a+b*x^n+c*x^(2*n))^p,x],x] /;
        FreeQ[{a,b,c,n},x] && EqQ[n2,2*n] && PolyQ[Pq,x] && IGtQ[p,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [pq__, a__, b__, n_, c__, n2_, p_, x_],
        optional: [b__, n_, c__, n2_, p_],
        when: {
            freeq!([a__, b__, c__, n_], x_)
                && igtq!(p_, 0)
                && eqq!(n2_, Atom::num(2) * &n_)
                && rubi_poly_q(&pq__, x_)
        },
        rhs: {
            let integrand =
                &pq__ * (&a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_)).pow(&p_);
            let expanded = rubi_expand_integrand(&integrand, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_2309(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 2309,
        source: "Int[(d_+e_.*x_^n_.+f_.*x_^n2_.)*(a_+b_.*x_^n_.+c_.*x_^n2_.)^p_.,x_Symbol] :=
          d*x*(a+b*x^n+c*x^(2*n))^(p+1)/a /;
        FreeQ[{a,b,c,d,e,f,n,p},x] && EqQ[n2,2*n] && EqQ[a*e-b*d*(n*(p+1)+1),0] && EqQ[a*f-c*d*(2*n*(p+1)+1),0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: (d__ + e__ * x_.pow(n_) + f__ * x_.pow(n2_)) * (a__ + b__ * x_.pow(n_) + c__ * x_.pow(n2_)).pow(p_),
        with: [d__, e__, n_, f__, n2_, a__, b__, c__, p_, x_],
        optional: [e__, n_, f__, n2_, b__, c__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, n_, p_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && eqq!(&a__ * &e__ - &b__ * &d__ * (&n_ * (&p_ + 1) + 1), 0)
                && eqq!(&a__ * &f__ - &c__ * &d__ * (Atom::num(2) * &n_ * (&p_ + 1) + 1), 0)
        },
        rhs: {
            if a__.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let trinomial = &a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_);

            rubi_simp(&(&d__ * x_ * trinomial.pow(&p_ + 1) / a__), x_)
        },
    ));
}

fn push_rules_rule_2310(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, f__, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 2310,
        source: "Int[(d_+f_.*x_^n2_.)*(a_+b_.*x_^n_.+c_.*x_^n2_.)^p_.,x_Symbol] :=
          d*x*(a+b*x^n+c*x^(2*n))^(p+1)/a /;
        FreeQ[{a,b,c,d,f,n,p},x] && EqQ[n2,2*n] && EqQ[n*(p+1)+1,0] && EqQ[c*d+a*f,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: (d__ + f__ * x_.pow(n2_)) * (a__ + b__ * x_.pow(n_) + c__ * x_.pow(n2_)).pow(p_),
        with: [d__, f__, n2_, a__, b__, n_, c__, p_, x_],
        optional: [f__, n2_, b__, n_, c__, p_],
        when: {
            freeq!([a__, b__, c__, d__, f__, n_, p_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && eqq!(&n_ * (&p_ + 1) + 1, 0)
                && eqq!(&c__ * &d__ + &a__ * &f__, 0)
        },
        rhs: {
            if a__.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let trinomial = &a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_);

            rubi_simp(&(&d__ * x_ * trinomial.pow(&p_ + 1) / a__), x_)
        },
    ));
}

fn push_rules_rule_2311(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, n_, n2_, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2311,
        source: "Int[Pq_*(a_+b_.*x_^n_.+c_.*x_^n2_.)^p_,x_Symbol] :=
          Int[x*PolynomialQuotient[Pq,x,x]*(a+b*x^n+c*x^(2*n))^p,x] /;
        FreeQ[{a,b,c,n,p},x] && EqQ[n2,2*n] && PolyQ[Pq,x] && EqQ[Coeff[Pq,x,0],0] && Not[MatchQ[Pq,x^m_.*u_. /; IntegerQ[m]]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [pq__, a__, b__, n_, c__, n2_, p_, x_],
        optional: [b__, n_, c__, n2_],
        when: {
            freeq!([a__, b__, c__, n_, p_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && rubi_poly_q(&pq__, x_)
                && rubi_coeff(&pq__, x_, 0).is_some_and(|coefficient| eqq!(coefficient, 0))
                && !visible_integer_power_of_variable_factor(&pq__, x_)
        },
        rhs: {
            let quotient = rubi_polynomial_quotient(&pq__, x_, x_).rubi_rhs();
            let integrand = x_
                * quotient
                * (&a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_)).pow(&p_);

            rubi_rhs_int(&integrand, x_)
        },
    ));
}

fn push_rules_rule_2312(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, n_, n2_, n3_, p_, x_);
    rules.push(rubi_rule!(
        order: 2312,
        source: "Int[(d_+e_.*x_^n_+f_.*x_^n2_.+g_.*x_^n3_.)*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_.,x_Symbol] :=
          x*(a*d*(n+1)+(a*e-b*d*(n*(p+1)+1))*x^n)*(a+b*x^n+c*x^(2*n))^(p+1)/(a^2*(n+1)) /;
        FreeQ[{a,b,c,d,e,f,g,n,p},x] && EqQ[n2,2*n] && EqQ[n3,3*n] && NeQ[b^2-4*a*c,0] &&
          EqQ[a^2*g*(n+1)-c*(n*(2*p+3)+1)*(a*e-b*d*(n*(p+1)+1)),0] &&
          EqQ[a^2*f*(n+1)-a*c*d*(n+1)*(2*n*(p+1)+1)-b*(n*(p+2)+1)*(a*e-b*d*(n*(p+1)+1)),0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: (d__ + e__ * x_.pow(n_) + f__ * x_.pow(n2_) + g__ * x_.pow(n3_))
            * (a__ + b__ * x_.pow(n_) + c__ * x_.pow(n2_)).pow(p_),
        with: [d__, e__, n_, f__, n2_, g__, n3_, a__, b__, c__, p_, x_],
        optional: [e__, f__, n2_, g__, n3_, b__, c__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, n_, p_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && eqq!(n3_, Atom::num(3) * &n_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && eqq!(
                    a__.pow(2) * &g__ * (&n_ + 1)
                        - &c__ * (&n_ * (Atom::num(2) * &p_ + 3) + 1) * (&a__ * &e__ - &b__ * &d__ * (&n_ * (&p_ + 1) + 1)),
                    0
                )
                && eqq!(
                    a__.pow(2) * &f__ * (&n_ + 1)
                        - &a__ * &c__ * &d__ * (&n_ + 1) * (Atom::num(2) * &n_ * (&p_ + 1) + 1)
                        - &b__ * (&n_ * (&p_ + 2) + 1) * (&a__ * &e__ - &b__ * &d__ * (&n_ * (&p_ + 1) + 1)),
                    0
                )
        },
        rhs: {
            let denominator = a__.pow(2) * (&n_ + 1);
            if denominator.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let trinomial = &a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_);

            rubi_simp(&(x_
                    * (&a__ * &d__ * (&n_ + 1)
                        + (&a__ * &e__ - &b__ * &d__ * (&n_ * (&p_ + 1) + 1)) * x_.pow(&n_))
                    * trinomial.pow(&p_ + 1)
                    / denominator), x_)
        },
    ));
}

fn push_rules_rule_2313(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, f__, g__, n_, n2_, n3_, p_, x_);
    rules.push(rubi_rule!(
        order: 2313,
        source: "Int[(d_+f_.*x_^n2_.+g_.*x_^n3_.)*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_.,x_Symbol] :=
          d*x*(a*(n+1)-b*(n*(p+1)+1)*x^n)*(a+b*x^n+c*x^(2*n))^(p+1)/(a^2*(n+1)) /;
        FreeQ[{a,b,c,d,f,g,n,p},x] && EqQ[n2,2*n] && EqQ[n3,3*n] && NeQ[b^2-4*a*c,0] &&
          EqQ[a^2*g*(n+1)+c*b*d*(n*(2*p+3)+1)*(n*(p+1)+1),0] &&
          EqQ[a^2*f*(n+1)-a*c*d*(n+1)*(2*n*(p+1)+1)+b^2*d*(n*(p+2)+1)*(n*(p+1)+1),0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: (d__ + f__ * x_.pow(n2_) + g__ * x_.pow(n3_))
            * (a__ + b__ * x_.pow(n_) + c__ * x_.pow(n2_)).pow(p_),
        with: [d__, f__, n2_, g__, n3_, a__, b__, n_, c__, p_, x_],
        optional: [f__, n2_, g__, n3_, b__, c__, p_],
        when: {
            freeq!([a__, b__, c__, d__, f__, g__, n_, p_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && eqq!(n3_, Atom::num(3) * &n_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && eqq!(
                    a__.pow(2) * &g__ * (&n_ + 1)
                        + &c__ * &b__ * &d__ * (&n_ * (Atom::num(2) * &p_ + 3) + 1) * (&n_ * (&p_ + 1) + 1),
                    0
                )
                && eqq!(
                    a__.pow(2) * &f__ * (&n_ + 1)
                        - &a__ * &c__ * &d__ * (&n_ + 1) * (Atom::num(2) * &n_ * (&p_ + 1) + 1)
                        + b__.pow(2) * &d__ * (&n_ * (&p_ + 2) + 1) * (&n_ * (&p_ + 1) + 1),
                    0
                )
        },
        rhs: {
            let denominator = a__.pow(2) * (&n_ + 1);
            if denominator.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let trinomial = &a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_);

            rubi_simp(&(&d__ * x_ * (&a__ * (&n_ + 1) - &b__ * (&n_ * (&p_ + 1) + 1) * x_.pow(&n_))
                    * trinomial.pow(&p_ + 1)
                    / denominator), x_)
        },
    ));
}

fn push_rules_rule_2314(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, g__, n_, n2_, n3_, p_, x_);
    rules.push(rubi_rule!(
        order: 2314,
        source: "Int[(d_+e_.*x_^n_+g_.*x_^n3_.)*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_.,x_Symbol] :=
          x*(a*d*(n+1)+(a*e-b*d*(n*(p+1)+1))*x^n)*(a+b*x^n+c*x^(2*n))^(p+1)/(a^2*(n+1)) /;
        FreeQ[{a,b,c,d,e,g,n,p},x] && EqQ[n2,2*n] && EqQ[n3,3*n] && NeQ[b^2-4*a*c,0] &&
          EqQ[a^2*g*(n+1)-c*(n*(2*p+3)+1)*(a*e-b*d*(n*(p+1)+1)),0] &&
          EqQ[a*c*d*(n+1)*(2*n*(p+1)+1)+b*(n*(p+2)+1)*(a*e-b*d*(n*(p+1)+1)),0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: (d__ + e__ * x_.pow(n_) + g__ * x_.pow(n3_))
            * (a__ + b__ * x_.pow(n_) + c__ * x_.pow(n2_)).pow(p_),
        with: [d__, e__, n_, g__, n3_, a__, b__, c__, n2_, p_, x_],
        optional: [e__, g__, n3_, b__, c__, n2_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, g__, n_, p_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && eqq!(n3_, Atom::num(3) * &n_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && eqq!(
                    a__.pow(2) * &g__ * (&n_ + 1)
                        - &c__ * (&n_ * (Atom::num(2) * &p_ + 3) + 1) * (&a__ * &e__ - &b__ * &d__ * (&n_ * (&p_ + 1) + 1)),
                    0
                )
                && eqq!(
                    &a__ * &c__ * &d__ * (&n_ + 1) * (Atom::num(2) * &n_ * (&p_ + 1) + 1)
                        + &b__ * (&n_ * (&p_ + 2) + 1) * (&a__ * &e__ - &b__ * &d__ * (&n_ * (&p_ + 1) + 1)),
                    0
                )
        },
        rhs: {
            let denominator = a__.pow(2) * (&n_ + 1);
            if denominator.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let trinomial = &a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_);

            rubi_simp(&(x_
                    * (&a__ * &d__ * (&n_ + 1)
                        + (&a__ * &e__ - &b__ * &d__ * (&n_ * (&p_ + 1) + 1)) * x_.pow(&n_))
                    * trinomial.pow(&p_ + 1)
                    / denominator), x_)
        },
    ));
}

fn push_rules_rule_2315(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, g__, n_, n2_, n3_, p_, x_);
    rules.push(rubi_rule!(
        order: 2315,
        source: "Int[(d_+g_.*x_^n3_.)*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_.,x_Symbol] :=
          d*x*(a*(n+1)-b*(n*(p+1)+1)*x^n)*(a+b*x^n+c*x^(2*n))^(p+1)/(a^2*(n+1)) /;
        FreeQ[{a,b,c,d,g,n,p},x] && EqQ[n2,2*n] && EqQ[n3,3*n] && NeQ[b^2-4*a*c,0] &&
          EqQ[a^2*g*(n+1)+c*b*d*(n*(2*p+3)+1)*(n*(p+1)+1),0] &&
          EqQ[a*c*d*(n+1)*(2*n*(p+1)+1)-b^2*d*(n*(p+2)+1)*(n*(p+1)+1),0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: (d__ + g__ * x_.pow(n3_)) * (a__ + b__ * x_.pow(n_) + c__ * x_.pow(n2_)).pow(p_),
        with: [d__, g__, n3_, a__, b__, n_, c__, n2_, p_, x_],
        optional: [g__, n3_, b__, c__, n2_, p_],
        when: {
            freeq!([a__, b__, c__, d__, g__, n_, p_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && eqq!(n3_, Atom::num(3) * &n_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && eqq!(
                    a__.pow(2) * &g__ * (&n_ + 1)
                        + &c__ * &b__ * &d__ * (&n_ * (Atom::num(2) * &p_ + 3) + 1) * (&n_ * (&p_ + 1) + 1),
                    0
                )
                && eqq!(
                    &a__ * &c__ * &d__ * (&n_ + 1) * (Atom::num(2) * &n_ * (&p_ + 1) + 1)
                        - b__.pow(2) * &d__ * (&n_ * (&p_ + 2) + 1) * (&n_ * (&p_ + 1) + 1),
                    0
                )
        },
        rhs: {
            let denominator = a__.pow(2) * (&n_ + 1);
            if denominator.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let trinomial = &a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_);

            rubi_simp(&(&d__ * x_ * (&a__ * (&n_ + 1) - &b__ * (&n_ * (&p_ + 1) + 1) * x_.pow(&n_))
                    * trinomial.pow(&p_ + 1)
                    / denominator), x_)
        },
    ));
}

fn push_rules_rule_2316(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, n_, n2_, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2316,
        source: "Int[Pq_*(a_+b_.*x_^n_+c_.*x_^n2_)^p_,x_Symbol] :=
          Module[{q=Expon[Pq,x],i},
          -x*(a+b*x^n+c*x^(2*n))^(p+1)/(a*n*(p+1)*(b^2-4*a*c))*
            Sum[((b^2-2*a*c)*Coeff[Pq,x,i]-a*b*Coeff[Pq,x,n+i])*x^i+
              c*(b*Coeff[Pq,x,i]-2*a*Coeff[Pq,x,n+i])*x^(n+i),{i,0,n-1}] +
          1/(a*n*(p+1)*(b^2-4*a*c)) \\[Star] Int[(a+b*x^n+c*x^(2*n))^(p+1)*
            Sum[((b^2*(n*(p+1)+i+1)-2*a*c*(2*n*(p+1)+i+1))*Coeff[Pq,x,i]-a*b*(i+1)*Coeff[Pq,x,n+i])*x^i+
              c*(n*(2*p+3)+i+1)*(b*Coeff[Pq,x,i]-2*a*Coeff[Pq,x,n+i])*x^(n+i),{i,0,n-1}],x] /;
         LtQ[q,2*n]] /;
        FreeQ[{a,b,c},x] && EqQ[n2,2*n] && PolyQ[Pq,x] && NeQ[b^2-4*a*c,0] && IGtQ[n,0] && LtQ[p,-1]",
        desc: "Trinomial recurrence 2b applied n-1Bold times",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [pq__, a__, b__, n_, c__, n2_, p_, x_],
        optional: [b__, c__],
        when: {
            freeq!([a__, b__, c__], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && rubi_poly_q(&pq__, x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && igtq!(n_, 0)
                && ltq!(p_, -1)
                && rubi_expon(&pq__, x_).is_some_and(|q| ltq!(Atom::num(q), Atom::num(2) * &n_))
        },
        rhs: {
            let n_i = integer_i64(&n_).rubi_rhs();
            let discriminant = b__.pow(2) - Atom::num(4) * &a__ * &c__;
            let denominator = &a__ * &n_ * (&p_ + 1) * &discriminant;
            if denominator.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let trinomial = &a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_);
            let mut direct_sum = Atom::num(0);
            let mut recursive_sum = Atom::num(0);
            for i in 0..n_i {
                let i_atom = Atom::num(i);
                let coeff_i = rubi_coeff(&pq__, x_, i).rubi_rhs();
                let coeff_n_i = rubi_coeff(&pq__, x_, n_i + i).rubi_rhs();

                direct_sum += ((b__.pow(2) - Atom::num(2) * &a__ * &c__) * &coeff_i
                    - &a__ * &b__ * &coeff_n_i)
                    * x_.pow(i)
                    + &c__ * (&b__ * &coeff_i - Atom::num(2) * &a__ * &coeff_n_i)
                        * x_.pow(n_i + i);
                recursive_sum += ((b__.pow(2) * (&n_ * (&p_ + 1) + &i_atom + 1)
                    - Atom::num(2) * &a__ * &c__ * (Atom::num(2) * &n_ * (&p_ + 1) + &i_atom + 1))
                    * &coeff_i
                    - &a__ * &b__ * (&i_atom + 1) * &coeff_n_i)
                    * x_.pow(i)
                    + &c__
                        * (&n_ * (Atom::num(2) * &p_ + 3) + &i_atom + 1)
                        * (&b__ * &coeff_i - Atom::num(2) * &a__ * &coeff_n_i)
                        * x_.pow(n_i + i);
            }

            let direct = Atom::num(-1) * x_ * trinomial.pow(&p_ + 1) * direct_sum / &denominator;
            let recursive_integrand = trinomial.pow(&p_ + 1) * recursive_sum;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_2317(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, n_, n2_, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2317,
        source: "Int[Pq_*(a_+b_.*x_^n_+c_.*x_^n2_)^p_,x_Symbol] :=
          With[{q=Expon[Pq,x]},
          Module[{Q=PolynomialQuotient[(b*c)^(Floor[(q-1)/n]+1)*Pq,a+b*x^n+c*x^(2*n),x],
                  R=PolynomialRemainder[(b*c)^(Floor[(q-1)/n]+1)*Pq,a+b*x^n+c*x^(2*n),x],i},
          -x*(a+b*x^n+c*x^(2*n))^(p+1)/(a*n*(p+1)*(b^2-4*a*c)*(b*c)^(Floor[(q-1)/n]+1))*
            Sum[((b^2-2*a*c)*Coeff[R,x,i]-a*b*Coeff[R,x,n+i])*x^i+
              c*(b*Coeff[R,x,i]-2*a*Coeff[R,x,n+i])*x^(n+i),{i,0,n-1}] +
          1/(a*n*(p+1)*(b^2-4*a*c)*(b*c)^(Floor[(q-1)/n]+1)) \\[Star] Int[(a+b*x^n+c*x^(2*n))^(p+1)*ExpandToSum[a*n*(p+1)*(b^2-4*a*c)*Q+
            Sum[((b^2*(n*(p+1)+i+1)-2*a*c*(2*n*(p+1)+i+1))*Coeff[R,x,i]-a*b*(i+1)*Coeff[R,x,n+i])*x^i+
             c*(n*(2*p+3)+i+1)*(b*Coeff[R,x,i]-2*a*Coeff[R,x,n+i])*x^(n+i),{i,0,n-1}],x],x]] /;
         GeQ[q,2*n]] /;
        FreeQ[{a,b,c},x] && EqQ[n2,2*n] && PolyQ[Pq,x] && NeQ[b^2-4*a*c,0] && IGtQ[n,0] && LtQ[p,-1]",
        desc: "Algebraic expansion and trinomial recurrence 2b applied n-1Bold times",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [pq__, a__, b__, n_, c__, n2_, p_, x_],
        optional: [b__, c__],
        when: {
            freeq!([a__, b__, c__], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && rubi_poly_q(&pq__, x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && igtq!(n_, 0)
                && ltq!(p_, -1)
                && rubi_expon(&pq__, x_).is_some_and(|q| geq!(Atom::num(q), Atom::num(2) * &n_))
        },
        rhs: {
            let q = rubi_expon(&pq__, x_).rubi_rhs();
            let n_i = integer_i64(&n_).rubi_rhs();
            let trinomial = &a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_);
            let discriminant = b__.pow(2) - Atom::num(4) * &a__ * &c__;
            let k = rubi_floor(q - 1, n_i).rubi_rhs() + 1;
            let bc_power = (&b__ * &c__).pow(k);
            let denominator = &a__ * &n_ * (&p_ + 1) * &discriminant * &bc_power;
            if denominator.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let dividend = &bc_power * &pq__;
            let capital_q = rubi_polynomial_quotient(&dividend, &trinomial, x_).rubi_rhs();
            let capital_r = rubi_polynomial_remainder(&dividend, &trinomial, x_).rubi_rhs();
            let mut direct_sum = Atom::num(0);
            let mut recursive_sum = Atom::num(0);
            for i in 0..n_i {
                let i_atom = Atom::num(i);
                let coeff_i = rubi_coeff(&capital_r, x_, i).rubi_rhs();
                let coeff_n_i = rubi_coeff(&capital_r, x_, n_i + i).rubi_rhs();

                direct_sum += ((b__.pow(2) - Atom::num(2) * &a__ * &c__) * &coeff_i
                    - &a__ * &b__ * &coeff_n_i)
                    * x_.pow(i)
                    + &c__ * (&b__ * &coeff_i - Atom::num(2) * &a__ * &coeff_n_i)
                        * x_.pow(n_i + i);
                recursive_sum += ((b__.pow(2) * (&n_ * (&p_ + 1) + &i_atom + 1)
                    - Atom::num(2) * &a__ * &c__ * (Atom::num(2) * &n_ * (&p_ + 1) + &i_atom + 1))
                    * &coeff_i
                    - &a__ * &b__ * (&i_atom + 1) * &coeff_n_i)
                    * x_.pow(i)
                    + &c__
                        * (&n_ * (Atom::num(2) * &p_ + 3) + &i_atom + 1)
                        * (&b__ * &coeff_i - Atom::num(2) * &a__ * &coeff_n_i)
                        * x_.pow(n_i + i);
            }

            let direct = Atom::num(-1) * x_ * trinomial.pow(&p_ + 1) * direct_sum / &denominator;
            let expand_to_sum_payload =
                &a__ * &n_ * (&p_ + 1) * &discriminant * capital_q + recursive_sum;
            let expand_to_sum = rubi_expand_to_sum(&expand_to_sum_payload, x_);
            let recursive_integrand = trinomial.pow(&p_ + 1) * expand_to_sum;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            direct + rubi_star(Atom::num(1) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_2318(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2318,
        source: "Int[Pq_*(a_+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          With[{q=Expon[Pq,x]},
            With[{Pqq=Coeff[Pq,x,q]},
            c^p*Pqq*Log[a+b*x+c*x^2]/2 +
            1/2 \\[Star] Int[ExpandToSum[2*Pq-c^p*Pqq*(b+2*c*x)/(a+b*x+c*x^2)^(p+1),x]*(a+b*x+c*x^2)^p,x]] /;
          EqQ[q+2*p+1,0]] /;
        FreeQ[{a,b,c},x] && PolyQ[Pq,x] && NeQ[b^2-4*a*c,0] && ILtQ[p,0]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [pq__, a__, b__, c__, p_, x_],
        optional: [b__, c__],
        when: {
            freeq!([a__, b__, c__], x_)
                && rubi_poly_q(&pq__, x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && iltq!(p_, 0)
                && rubi_expon(&pq__, x_).is_some_and(|q| eqq!(Atom::num(q) + Atom::num(2) * &p_ + 1, 0))
        },
        rhs: {
            let q = rubi_expon(&pq__, x_).rubi_rhs();
            let Pqq = rubi_coeff(&pq__, x_, q).rubi_rhs();
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let direct = c__.pow(&p_) * &Pqq * quadratic.log() / 2;
            let expand_to_sum_payload =
                Atom::num(2) * &pq__ - c__.pow(&p_) * &Pqq * (&b__ + Atom::num(2) * &c__ * x_) / quadratic.pow(&p_ + 1);
            let expand_to_sum = rubi_expand_to_sum(&expand_to_sum_payload, x_);
            let recursive_integrand = expand_to_sum * quadratic.pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            direct + rubi_star(Atom::num(1) / 2, recursive)
        },
    ));
}

fn push_rules_rule_2319(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2319,
        source: "Int[Pq_*(a_+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          With[{q=Expon[Pq,x]},
            With[{Pqq=Coeff[Pq,x,q]},
            c^p*Pqq*ArcTanh[(b+2*c*x)/(2*Rt[c,2]*Sqrt[a+b*x+c*x^2])] +
            Int[ExpandToSum[Pq-c^(p+1/2)*Pqq/(a+b*x+c*x^2)^(p+1/2),x]*(a+b*x+c*x^2)^p,x]] /;
          EqQ[q+2*p+1,0]] /;
        FreeQ[{a,b,c},x] && PolyQ[Pq,x] && NeQ[b^2-4*a*c,0] && ILtQ[p+1/2,0] && PosQ[c]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [pq__, a__, b__, c__, p_, x_],
        optional: [b__, c__],
        when: {
            freeq!([a__, b__, c__], x_)
                && rubi_poly_q(&pq__, x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && iltq!(&p_ + Atom::num(1) / Atom::num(2), 0)
                && posq!(c__)
                && rubi_expon(&pq__, x_).is_some_and(|q| eqq!(Atom::num(q) + Atom::num(2) * &p_ + 1, 0))
        },
        rhs: {
            let q = rubi_expon(&pq__, x_).rubi_rhs();
            let Pqq = rubi_coeff(&pq__, x_, q).rubi_rhs();
            let rt_c = rubi_rt(&c__, 2);
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let argument_denominator = Atom::num(2) * &rt_c * quadratic.sqrt();
            if argument_denominator.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let direct =
                c__.pow(&p_) * &Pqq * ((&b__ + Atom::num(2) * &c__ * x_) / argument_denominator).atanh();
            let expand_to_sum_payload =
                &pq__ - c__.pow(&p_ + &(Atom::num(1) / 2)) * &Pqq / quadratic.pow(&p_ + &(Atom::num(1) / 2));
            let expand_to_sum = rubi_expand_to_sum(&expand_to_sum_payload, x_);
            let recursive_integrand = expand_to_sum * quadratic.pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            direct + recursive
        },
    ));
}

fn push_rules_rule_2320(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2320,
        source: "Int[Pq_*(a_+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
          With[{q=Expon[Pq,x]},
            With[{Pqq=Coeff[Pq,x,q]},
            -(-c)^p*Pqq*ArcTan[(b+2*c*x)/(2*Rt[-c,2]*Sqrt[a+b*x+c*x^2])] +
            Int[ExpandToSum[Pq-(-c)^(p+1/2)*Pqq/(a+b*x+c*x^2)^(p+1/2),x]*(a+b*x+c*x^2)^p,x]] /;
          EqQ[q+2*p+1,0]] /;
        FreeQ[{a,b,c},x] && PolyQ[Pq,x] && NeQ[b^2-4*a*c,0] && ILtQ[p+1/2,0] && NegQ[c]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [pq__, a__, b__, c__, p_, x_],
        optional: [b__, c__],
        when: {
            freeq!([a__, b__, c__], x_)
                && rubi_poly_q(&pq__, x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && iltq!(&p_ + Atom::num(1) / Atom::num(2), 0)
                && negq!(c__)
                && rubi_expon(&pq__, x_).is_some_and(|q| eqq!(Atom::num(q) + Atom::num(2) * &p_ + 1, 0))
        },
        rhs: {
            let q = rubi_expon(&pq__, x_).rubi_rhs();
            let Pqq = rubi_coeff(&pq__, x_, q).rubi_rhs();
            let rt_neg_c = rubi_rt(&(-&c__), 2);
            let quadratic = &a__ + &b__ * x_ + &c__ * x_.pow(2);
            let argument_denominator = Atom::num(2) * &rt_neg_c * quadratic.sqrt();
            if argument_denominator.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let direct =
                -(-&c__).pow(&p_) * &Pqq * ((&b__ + Atom::num(2) * &c__ * x_) / argument_denominator).atan();
            let expand_to_sum_payload =
                &pq__ - (-&c__).pow(&p_ + &(Atom::num(1) / 2)) * &Pqq / quadratic.pow(&p_ + &(Atom::num(1) / 2));
            let expand_to_sum = rubi_expand_to_sum(&expand_to_sum_payload, x_);
            let recursive_integrand = expand_to_sum * quadratic.pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            direct + recursive
        },
    ));
}

fn push_rules_rule_2321(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, n_, n2_, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2321,
        source: "Int[Pq_*(a_+b_.*x_^n_.+c_.*x_^n2_)^p_,x_Symbol] :=
          With[{q=Expon[Pq,x]},
            With[{Pqq=Coeff[Pq,x,q]},
            Pqq*x^(q-2*n+1)*(a+b*x^n+c*x^(2*n))^(p+1)/(c*(q+2*n*p+1)) +
            Int[ExpandToSum[Pq-Pqq*x^q-Pqq*(a*(q-2*n+1)*x^(q-2*n)+b*(q+n*(p-1)+1)*x^(q-n))/(c*(q+2*n*p+1)),x]*(a+b*x^n+c*x^(2*n))^p,x]] /;
          GeQ[q,2*n] && NeQ[q+2*n*p+1,0] && (IntegerQ[2*p] || EqQ[n,1] && IntegerQ[4*p] || IntegerQ[p+(q+1)/(2*n)])] /;
        FreeQ[{a,b,c,p},x] && EqQ[n2,2*n] && PolyQ[Pq,x^n] && NeQ[b^2-4*a*c,0] && IGtQ[n,0]",
        desc: "Trinomial recurrence 3a with A=0, B=1 and m=m-n",
        refs: ["G&R 2.160.3", "G&R 2.104"],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [pq__, a__, b__, n_, c__, n2_, p_, x_],
        optional: [b__, n_, c__],
        when: {
            if let Some(q) = rubi_expon(&pq__, x_) {
                let q_atom = Atom::num(q);
                freeq!([a__, b__, c__, p_], x_)
                    && eqq!(n2_, Atom::num(2) * &n_)
                    && rubi_poly_q_power(&pq__, x_, &n_)
                    && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                    && igtq!(n_, 0)
                    && geq!(q_atom, Atom::num(2) * &n_)
                    && neq!(&q_atom + Atom::num(2) * &n_ * &p_ + 1, 0)
                    && (integerq!(Atom::num(2) * &p_)
                        || eqq!(n_, 1) && integerq!(Atom::num(4) * &p_)
                        || integerq!(&p_ + (&q_atom + 1) / (Atom::num(2) * &n_)))
            } else {
                false
            }
        },
        rhs: {
            let q = rubi_expon(&pq__, x_).rubi_rhs();
            let q_atom = Atom::num(q);
            let Pqq = rubi_coeff(&pq__, x_, q).rubi_rhs();
            let denominator = &c__ * (&q_atom + Atom::num(2) * &n_ * &p_ + 1);
            if denominator.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let trinomial = &a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_);
            let direct = &Pqq
                * x_.pow(&q_atom - Atom::num(2) * &n_ + 1)
                * trinomial.pow(&p_ + 1)
                / &denominator;
            let expand_to_sum_payload = &pq__
                - &Pqq * x_.pow(&q_atom)
                - &Pqq
                    * (&a__ * (&q_atom - Atom::num(2) * &n_ + 1)
                        * x_.pow(&q_atom - Atom::num(2) * &n_)
                        + &b__ * (&q_atom + &n_ * (&p_ - 1) + 1) * x_.pow(&q_atom - &n_))
                    / denominator;
            let expand_to_sum = rubi_expand_to_sum(&expand_to_sum_payload, x_);
            let recursive_integrand = expand_to_sum * trinomial.pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            direct + recursive
        },
    ));
}

fn push_rules_rule_2322(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, n_, n2_, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2322,
        source: "Int[Pq_*(a_+b_.*x_^n_+c_.*x_^n2_)^p_,x_Symbol] :=
          Module[{q=Expon[Pq,x],j,k},
          Int[Sum[x^j*Sum[Coeff[Pq,x,j+k*n]*x^(k*n),{k,0,(q-j)/n+1}]*(a+b*x^n+c*x^(2*n))^p,{j,0,n-1}],x]] /;
        FreeQ[{a,b,c,p},x] && EqQ[n2,2*n] && PolyQ[Pq,x] && NeQ[b^2-4*a*c,0] && IGtQ[n,0] && Not[PolyQ[Pq,x^n]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [pq__, a__, b__, n_, c__, n2_, p_, x_],
        optional: [b__, c__],
        when: {
            freeq!([a__, b__, c__, p_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && rubi_poly_q(&pq__, x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && igtq!(n_, 0)
                && !rubi_poly_q_power(&pq__, x_, &n_)
        },
        rhs: {
            let q = rubi_expon(&pq__, x_).rubi_rhs();
            let n_i = integer_i64(&n_).rubi_rhs();
            let trinomial = &a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_);
            let mut outer_sum = Atom::num(0);

            for j in 0..n_i {
                let mut inner_sum = Atom::num(0);
                let upper = (q - j).div_euclid(n_i) + 1;
                if upper >= 0 {
                    for k in 0..=upper {
                        inner_sum += rubi_coeff(&pq__, x_, j + k * n_i).rubi_rhs() * x_.pow(k * n_i);
                    }
                }
                outer_sum += x_.pow(j) * inner_sum * trinomial.pow(&p_);
            }

            rubi_rhs_int(&outer_sum, x_)
        },
    ));
}

fn push_rules_rule_2323(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, n_, n2_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2323,
        source: "Int[Pq_/(a_+b_.*x_^n_.+c_.*x_^n2_.),x_Symbol] :=
          Int[RationalFunctionExpand[Pq/(a+b*x^n+c*x^(2*n)),x],x] /;
        FreeQ[{a,b,c},x] && EqQ[n2,2*n] && PolyQ[Pq,x] && NeQ[b^2-4*a*c,0] && IGtQ[n,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [pq__, a__, b__, n_, c__, n2_, x_],
        optional: [b__, n_, c__, n2_],
        when: {
            freeq!([a__, b__, c__], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && rubi_poly_q(&pq__, x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && igtq!(n_, 0)
        },
        rhs: {
            let payload = &pq__ / (&a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_));
            let expanded = rubi_rational_function_expand(&payload, x_).rubi_rhs();

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_2324(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, n_, n2_, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2324,
        source: "Int[Pq_*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
          With[{g=Denominator[n]},
          g \\[Star] Subst[Int[x^(g-1)*ReplaceAll[Pq,x->x^g]*(a+b*x^(g*n)+c*x^(2*g*n))^p,x],x,x^(1/g)]] /;
        FreeQ[{a,b,c,p},x] && EqQ[n2,2*n] && PolyQ[Pq,x] && NeQ[b^2-4*a*c,0] && FractionQ[n]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [pq__, a__, b__, n_, c__, n2_, p_, x_],
        optional: [b__, c__, n2_],
        when: {
            freeq!([a__, b__, c__, p_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && rubi_poly_q(&pq__, x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && fractionq!(n_)
        },
        rhs: {
            let g_i = rubi_denominator(&n_).rubi_rhs();
            let g = Atom::num(g_i);
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let sub_atom = Atom::var(sub);
            let replaced_pq = rubi_replace_all(&pq__, x_, sub_atom.pow(&g));
            let transformed_integrand = sub_atom.pow(&g - 1)
                * replaced_pq
                * (&a__
                    + &b__ * sub_atom.pow(&g * &n_)
                    + &c__ * sub_atom.pow(Atom::num(2) * &g * &n_))
                .pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);

            rubi_star(g, rubi_subst(&transformed, sub, x_.pow(Atom::num(1) / g_i)))
        },
    ));
}

fn push_rules_rule_2325(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, n_, n2_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2325,
        source: "Int[Pq_/(a_+b_.*x_^n_.+c_.*x_^n2_.),x_Symbol] :=
          With[{q=Rt[b^2-4*a*c,2]},
          2*c/q \\[Star] Int[Pq/(b-q+2*c*x^n),x] -
          2*c/q \\[Star] Int[Pq/(b+q+2*c*x^n),x]] /;
        FreeQ[{a,b,c,n},x] && EqQ[n2,2*n] && PolyQ[Pq,x] && NeQ[b^2-4*a*c,0]",
        desc: "Algebraic expansion",
        refs: ["G&R 2.161.1a"],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [pq__, a__, b__, n_, c__, n2_, x_],
        optional: [b__, n_, c__, n2_],
        when: {
            freeq!([a__, b__, c__, n_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && rubi_poly_q(&pq__, x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
        },
        rhs: {
            let q = rubi_rt(&(b__.pow(2) - Atom::num(4) * &a__ * &c__), 2);
            let first = rubi_rhs_int(
                &(&pq__ / (&b__ - &q + Atom::num(2) * &c__ * x_.pow(&n_))),
                x_,
            );
            let second = rubi_rhs_int(
                &(&pq__ / (&b__ + &q + Atom::num(2) * &c__ * x_.pow(&n_))),
                x_,
            );
            let scale = Atom::num(2) * &c__ / &q;

            rubi_star(&scale, first) - rubi_star(scale, second)
        },
    ));
}

fn push_rules_rule_2326(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, n_, n2_, p_, p3__, x_);
    rules.push(rubi_rule!(
        order: 2326,
        source: "Int[P3_*(a_+b_.*x_^n_+c_.*x_^n2_)^p_,x_Symbol] :=
          With[{d=Coeff[P3,x^n,0],e=Coeff[P3,x^n,1],f=Coeff[P3,x^n,2],g=Coeff[P3,x^n,3]},
          -x*(b^2*c*d-2*a*c*(c*d-a*f)-a*b*(c*e+a*g)+(b*c*(c*d+a*f)-a*b^2*g-2*a*c*(c*e-a*g))*x^n)*(a+b*x^n+c*x^(2*n))^(p+1)/
            (a*c*n*(p+1)*(b^2-4*a*c)) -
          1/(a*c*n*(p+1)*(b^2-4*a*c)) \\[Star] Int[(a+b*x^n+c*x^(2*n))^(p+1)*
            Simp[a*b*(c*e+a*g)-b^2*c*d*(n+n*p+1)-2*a*c*(a*f-c*d*(2*n*(p+1)+1))+
              (a*b^2*g*(n*(p+2)+1)-b*c*(c*d+a*f)*(n*(2*p+3)+1)-2*a*c*(a*g*(n+1)-c*e*(n*(2*p+3)+1)))*x^n,x],x]] /;
        FreeQ[{a,b,c,n},x] && EqQ[n2,2*n] && PolyQ[P3,x^n,3] && NeQ[b^2-4*a*c,0] && ILtQ[p,-1]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern: p3__ * (a__ + b__ * x_.pow(n_) + c__ * x_.pow(n2_)).pow(p_),
        with: [p3__, a__, b__, n_, c__, n2_, p_, x_],
        optional: [b__, c__],
        when: {
            freeq!([a__, b__, c__, n_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && rubi_poly_q_power_degree(&p3__, x_, &n_, 3)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && iltq!(p_, -1)
        },
        rhs: {
            let d = rubi_coeff_power(&p3__, x_, &n_, 0).rubi_rhs();
            let e = rubi_coeff_power(&p3__, x_, &n_, 1).rubi_rhs();
            let f = rubi_coeff_power(&p3__, x_, &n_, 2).rubi_rhs();
            let g = rubi_coeff_power(&p3__, x_, &n_, 3).rubi_rhs();
            let x_n = x_.pow(&n_);
            let x_2n = x_.pow(Atom::num(2) * &n_);
            let discriminant = b__.pow(2) - Atom::num(4) * &a__ * &c__;
            let p1 = &p_ + 1;
            let denominator = &a__ * &c__ * &n_ * &p1 * &discriminant;
            if denominator.expand().is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let trinomial = &a__ + &b__ * &x_n + &c__ * x_2n;
            let direct_payload = b__.pow(2) * &c__ * &d
                - Atom::num(2) * &a__ * &c__ * (&c__ * &d - &a__ * &f)
                - &a__ * &b__ * (&c__ * &e + &a__ * &g)
                + (&b__ * &c__ * (&c__ * &d + &a__ * &f)
                    - &a__ * b__.pow(2) * &g
                    - Atom::num(2) * &a__ * &c__ * (&c__ * &e - &a__ * &g))
                    * &x_n;
            let direct = Atom::num(-1) * x_ * direct_payload * trinomial.pow(&p1) / &denominator;
            let simp_payload = &a__ * &b__ * (&c__ * &e + &a__ * &g)
                - b__.pow(2) * &c__ * &d * (&n_ + &n_ * &p_ + 1)
                - Atom::num(2)
                    * &a__
                    * &c__
                    * (&a__ * &f - &c__ * &d * (Atom::num(2) * &n_ * &p1 + 1))
                + (&a__ * b__.pow(2) * &g * (&n_ * (&p_ + 2) + 1)
                    - &b__ * &c__ * (&c__ * &d + &a__ * &f) * (&n_ * (Atom::num(2) * &p_ + 3) + 1)
                    - Atom::num(2)
                        * &a__
                        * &c__
                        * (&a__ * &g * (&n_ + 1)
                            - &c__ * &e * (&n_ * (Atom::num(2) * &p_ + 3) + 1)))
                    * &x_n;
            let recursive_integrand = trinomial.pow(&p1) * rubi_simp(&simp_payload, x_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) - rubi_star(Atom::num(1) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_2327(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, n_, n2_, p_, p2__, x_);
    rules.push(rubi_rule!(
        order: 2327,
        source: "Int[P2_*(a_+b_.*x_^n_+c_.*x_^n2_)^p_,x_Symbol] :=
          With[{d=Coeff[P2,x^n,0],e=Coeff[P2,x^n,1],f=Coeff[P2,x^n,2]},
          -x*(b^2*d-2*a*(c*d-a*f)-a*b*e+(b*(c*d+a*f)-2*a*c*e)*x^n)*(a+b*x^n+c*x^(2*n))^(p+1)/(a*n*(p+1)*(b^2-4*a*c)) -
          1/(a*n*(p+1)*(b^2-4*a*c)) \\[Star] Int[(a+b*x^n+c*x^(2*n))^(p+1)*
            Simp[a*b*e-b^2*d*(n+n*p+1)-2*a*(a*f-c*d*(2*n*(p+1)+1))-(b*(c*d+a*f)*(n*(2*p+3)+1)-2*a*c*e*(n*(2*p+3)+1))*x^n,x],x]] /;
        FreeQ[{a,b,c,n},x] && EqQ[n2,2*n] && PolyQ[P2,x^n,2] && NeQ[b^2-4*a*c,0] && ILtQ[p,-1]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern: p2__ * (a__ + b__ * x_.pow(n_) + c__ * x_.pow(n2_)).pow(p_),
        with: [p2__, a__, b__, n_, c__, n2_, p_, x_],
        optional: [b__, c__],
        when: {
            freeq!([a__, b__, c__, n_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && rubi_poly_q_power_degree(&p2__, x_, &n_, 2)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && iltq!(p_, -1)
        },
        rhs: {
            let d = rubi_coeff_power(&p2__, x_, &n_, 0).rubi_rhs();
            let e = rubi_coeff_power(&p2__, x_, &n_, 1).rubi_rhs();
            let f = rubi_coeff_power(&p2__, x_, &n_, 2).rubi_rhs();
            let x_n = x_.pow(&n_);
            let x_2n = x_.pow(Atom::num(2) * &n_);
            let discriminant = b__.pow(2) - Atom::num(4) * &a__ * &c__;
            let p1 = &p_ + 1;
            let denominator = &a__ * &n_ * &p1 * &discriminant;
            if denominator.expand().is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let trinomial = &a__ + &b__ * &x_n + &c__ * x_2n;
            let direct_payload = b__.pow(2) * &d
                - Atom::num(2) * &a__ * (&c__ * &d - &a__ * &f)
                - &a__ * &b__ * &e
                + (&b__ * (&c__ * &d + &a__ * &f) - Atom::num(2) * &a__ * &c__ * &e) * &x_n;
            let direct = Atom::num(-1) * x_ * direct_payload * trinomial.pow(&p1) / &denominator;
            let simp_payload = &a__ * &b__ * &e
                - b__.pow(2) * &d * (&n_ + &n_ * &p_ + 1)
                - Atom::num(2) * &a__ * (&a__ * &f - &c__ * &d * (Atom::num(2) * &n_ * &p1 + 1))
                - (&b__ * (&c__ * &d + &a__ * &f) * (&n_ * (Atom::num(2) * &p_ + 3) + 1)
                    - Atom::num(2) * &a__ * &c__ * &e * (&n_ * (Atom::num(2) * &p_ + 3) + 1))
                    * &x_n;
            let recursive_integrand = trinomial.pow(&p1) * rubi_simp(&simp_payload, x_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) - rubi_star(Atom::num(1) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_2328(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, n_, n2_, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2328,
        source: "Int[Pq_*(a_+b_.*x_^n_.+c_.*x_^n2_.)^p_,x_Symbol] :=
          Int[ExpandIntegrand[Pq*(a+b*x^n+c*x^(2*n))^p,x],x] /;
        FreeQ[{a,b,c,n},x] && EqQ[n2,2*n] && PolyQ[Pq,x] && ILtQ[p,-1]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [pq__, a__, b__, n_, c__, n2_, p_, x_],
        optional: [b__, n_, c__, n2_],
        when: {
            freeq!([a__, b__, c__, n_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && rubi_poly_q(&pq__, x_)
                && iltq!(p_, -1)
        },
        rhs: {
            let integrand =
                &pq__ * (&a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_)).pow(&p_);
            let expanded = rubi_expand_integrand(&integrand, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_2329(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, n_, n2_, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2329,
        source: "Int[Pq_*(a_+b_.*x_^n_.+c_.*x_^n2_.)^p_.,x_Symbol] :=
          Unintegrable[Pq*(a+b*x^n+c*x^(2*n))^p,x] /;
        FreeQ[{a,b,c,n,p},x] && EqQ[n2,2*n] && (PolyQ[Pq,x] || PolyQ[Pq,x^n])",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [pq__, a__, b__, n_, c__, n2_, p_, x_],
        optional: [b__, n_, c__, n2_, p_],
        x_free: [a__, b__, c__, n_, p_],
        when: {
            freeq!([a__, b__, c__, n_, p_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && (rubi_poly_q(&pq__, x_) || rubi_poly_q_power(&pq__, x_, &n_))
        },
        rhs: {
            let integrand = &pq__
                * (&a__
                    + &b__ * x_.pow(&n_)
                    + &c__ * x_.pow(Atom::num(2) * &n_))
                    .pow(&p_);
            rubi_unintegrable(integrand, x_)
        },
    ));
}

fn push_rules_rule_2330(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, n_, n2_, p_, pq__, u_);
    rules.push(rubi_rule!(
        order: 2330,
        source: "Int[Pq_*(a_+b_.*v_^n_+c_.*v_^n2_.)^p_.,x_Symbol] :=
          1/Coefficient[v,x,1] \\[Star] Subst[Int[SubstFor[v,Pq,x]*(a+b*x^n+c*x^(2*n))^p,x],x,v] /;
        FreeQ[{a,b,c,n,p},x] && EqQ[n2,2*n] && LinearQ[v,x] && PolyQ[Pq,v^n]",
        desc: "Integration by substitution",
        refs: [],
        pattern: pq__ * (a__ + b__ * u_.pow(n_) + c__ * u_.pow(n2_)).pow(p_),
        with: [pq__, a__, b__, u_, n_, c__, n2_, p_, x_],
        optional: [b__, c__, n2_, p_],
        x_dep: [u_],
        x_free: [a__, b__, c__, n_, p_],
        x_linear: [u_],
        when: {
            freeq!([a__, b__, c__, n_, p_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && rubi_linear_q(&u_, x_)
                && u_ != x_
                && rubi_poly_q_power_of(&pq__, &u_, &n_, x_)
        },
        rhs: {
            let coefficient = rubi_coefficient(&u_, x_, 1).rubi_rhs();
            if coefficient.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let sub_atom = Atom::var(sub);
            let subst_for = rubi_subst_for(&pq__, &u_, sub);
            let transformed_integrand = subst_for
                * (&a__
                    + &b__ * sub_atom.pow(&n_)
                    + &c__ * sub_atom.pow(Atom::num(2) * &n_))
                .pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);

            rubi_star(Atom::num(1) / coefficient, rubi_subst(&transformed, sub, u_))
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

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let n2_ = symbols.n2_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let pq__ = symbols.pq__;
    let x_ = symbols.x_;
    pq__ * (a__ + b__ * x_.pow(n_) + c__ * x_.pow(n2_)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_2(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let n2_ = symbols.n2_;
    let n_ = symbols.n_;
    let pq__ = symbols.pq__;
    let x_ = symbols.x_;
    pq__ / (a__ + b__ * x_.pow(n_) + c__ * x_.pow(n2_))
}
