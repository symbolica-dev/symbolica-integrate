use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_2283(rules);
    push_rules_rule_2284(rules);
    push_rules_rule_2285(rules);
    push_rules_rule_2286(rules);
    push_rules_rule_2287(rules);
    push_rules_rule_2288(rules);
    push_rules_rule_2289(rules);
    push_rules_rule_2290(rules);
    push_rules_rule_2291(rules);
    push_rules_rule_2292(rules);
    push_rules_rule_2293(rules);
    push_rules_rule_2294(rules);
    push_rules_rule_2295(rules);
    push_rules_rule_2296(rules);
    push_rules_rule_2297(rules);
    push_rules_rule_2298(rules);
    push_rules_rule_2299(rules);
    push_rules_rule_2300(rules);
    push_rules_rule_2301(rules);
    push_rules_rule_2302(rules);
    push_rules_rule_2303(rules);
    push_rules_rule_2304(rules);
    push_rules_rule_2305(rules);
    push_rules_rule_2306(rules);
    push_rules_rule_2307(rules);
}

fn push_rules_rule_2283(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, n2_, p_, px__, x_);
    rules.push(rubi_rule!(
        order: 2283,
        source: "Int[x_^m_.*Px_*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_.,x_Symbol] :=
          1/n \\[Star] Subst[Int[SubstFor[x^n,Px,x]*(a+b*x+c*x^2)^p,x],x,x^n] /;
        FreeQ[{a,b,c,m,n,p},x] && EqQ[n2,2*n] && PolyQ[Px,x^n] && EqQ[Simplify[m-n+1],0]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [m_, px__, a__, b__, n_, c__, n2_, p_, x_],
        optional: [m_, b__, c__, n2_, p_],
        when: {
            freeq!([a__, b__, c__, m_, n_, p_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && rubi_poly_q_power(&px__, x_, &n_)
                && eqq!(rubi_simplify(&(&m_ - &n_ + 1)), 0)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let sub_atom = Atom::var(sub);
            let subst_for = rubi_subst_for_power(&px__, x_, &n_, sub).rubi_rhs();
            let transformed_integrand =
                subst_for * (&a__ + &b__ * &sub_atom + &c__ * sub_atom.pow(2)).pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);
            let substituted = rubi_subst(&transformed, sub, x_.pow(&n_));

            rubi_star(Atom::num(1) / &n_, substituted)
        },
    ));
}

fn push_rules_rule_2284(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, n2_, p_, px__, x_);
    rules.push(rubi_rule!(
        order: 2284,
        source: "Int[(d_.*x_)^m_.*Px_*(a_+b_.*x_^n_.+c_.*x_^n2_.)^p_.,x_Symbol] :=
          Int[ExpandIntegrand[(d*x)^m*Px*(a+b*x^n+c*x^(2*n))^p,x],x] /;
        FreeQ[{a,b,c,d,m,n},x] && EqQ[n2,2*n] && PolyQ[Px,x] && IGtQ[p,0]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [d__, m_, px__, a__, b__, n_, c__, n2_, p_, x_],
        optional: [d__, m_, b__, n_, c__, n2_, p_],
        when: {
            freeq!([a__, b__, c__, d__, m_, n_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && rubi_poly_q(&px__, x_)
                && igtq!(p_, 0)
        },
        rhs: {
            let integrand = (&d__ * x_).pow(&m_)
                * &px__
                * (&a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_))
                    .pow(&p_);
            let expanded = rubi_expand_integrand(&integrand, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_2285(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, m_, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 2285,
        source: "Int[(g_.*x_)^m_.*(d_+e_.*x_^n_.+f_.*x_^n2_.)*(a_+b_.*x_^n_.+c_.*x_^n2_.)^p_.,x_Symbol] :=
          d*(g*x)^(m+1)*(a+b*x^n+c*x^(2*n))^(p+1)/(a*g*(m+1)) /;
        FreeQ[{a,b,c,d,e,f,g,m,n,p},x] && EqQ[n2,2*n] && EqQ[a*e*(m+1)-b*d*(m+n*(p+1)+1),0] && EqQ[a*f*(m+1)-c*d*(m+2*n*(p+1)+1),0] && NeQ[m,-1]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: (g__ * x_).pow(m_)
            * (d__ + e__ * x_.pow(n_) + f__ * x_.pow(n2_))
            * (a__ + b__ * x_.pow(n_) + c__ * x_.pow(n2_)).pow(p_),
        with: [g__, m_, d__, e__, n_, f__, n2_, a__, b__, c__, p_, x_],
        optional: [g__, m_, e__, n_, f__, n2_, b__, c__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, m_, n_, p_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && eqq!(&a__ * &e__ * (&m_ + 1) - &b__ * &d__ * (&m_ + &n_ * (&p_ + 1) + 1), 0)
                && eqq!(
                    &a__ * &f__ * (&m_ + 1) - &c__ * &d__ * (&m_ + Atom::num(2) * &n_ * (&p_ + 1) + 1),
                    0
                )
                && neq!(m_, -1)
        },
        rhs: {
            let trinomial = &a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_);

            rubi_simp(&(&d__ * (&g__ * x_).pow(&m_ + 1) * trinomial.pow(&p_ + 1)
                    / (&a__ * &g__ * (&m_ + 1))), x_)
        },
    ));
}

fn push_rules_rule_2286(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, f__, g__, m_, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 2286,
        source: "Int[(g_.*x_)^m_.*(d_+f_.*x_^n2_.)*(a_+b_.*x_^n_.+c_.*x_^n2_.)^p_.,x_Symbol] :=
          d*(g*x)^(m+1)*(a+b*x^n+c*x^(2*n))^(p+1)/(a*g*(m+1)) /;
        FreeQ[{a,b,c,d,f,g,m,n,p},x] && EqQ[n2,2*n] && EqQ[m+n*(p+1)+1,0] && EqQ[c*d+a*f,0] && NeQ[m,-1]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: (g__ * x_).pow(m_)
            * (d__ + f__ * x_.pow(n2_))
            * (a__ + b__ * x_.pow(n_) + c__ * x_.pow(n2_)).pow(p_),
        with: [g__, m_, d__, f__, n2_, a__, b__, n_, c__, p_, x_],
        optional: [g__, m_, f__, n2_, b__, n_, c__, p_],
        when: {
            freeq!([a__, b__, c__, d__, f__, g__, m_, n_, p_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && eqq!(&m_ + &n_ * (&p_ + 1) + 1, 0)
                && eqq!(&c__ * &d__ + &a__ * &f__, 0)
                && neq!(m_, -1)
        },
        rhs: {
            let trinomial = &a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_);

            rubi_simp(&(&d__ * (&g__ * x_).pow(&m_ + 1) * trinomial.pow(&p_ + 1)
                    / (&a__ * &g__ * (&m_ + 1))), x_)
        },
    ));
}

fn push_rules_rule_2287(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, n2_, p_, px__, x_);
    rules.push(rubi_rule!(
        order: 2287,
        source: "Int[x_^m_.*Px_*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
          1/n \\[Star] Subst[Int[x^(Simplify[(m+1)/n]-1)*SubstFor[x^n,Px,x]*(a+b*x+c*x^2)^p,x],x,x^n] /;
        FreeQ[{a,b,c,m,n,p},x] && EqQ[n2,2*n] && PolyQ[Px,x^n] && NeQ[b^2-4*a*c,0] && IntegerQ[Simplify[(m+1)/n]]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [m_, px__, a__, b__, n_, c__, n2_, p_, x_],
        optional: [m_, b__, c__, n2_],
        when: {
            freeq!([a__, b__, c__, m_, n_, p_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && rubi_poly_q_power(&px__, x_, &n_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && integerq!(rubi_simplify(&((&m_ + 1) / &n_)))
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let sub_atom = Atom::var(sub);
            let exponent = rubi_simplify(&((&m_ + 1) / &n_));
            let subst_for = rubi_subst_for_power(&px__, x_, &n_, sub).rubi_rhs();
            let transformed_integrand = sub_atom.pow(&exponent - 1)
                * subst_for
                * (&a__ + &b__ * &sub_atom + &c__ * sub_atom.pow(2)).pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);
            let substituted = rubi_subst(&transformed, sub, x_.pow(&n_));

            rubi_star(Atom::num(1) / &n_, substituted)
        },
    ));
}

fn push_rules_rule_2288(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, n2_, p_, px__, x_);
    rules.push(rubi_rule!(
        order: 2288,
        source: "Int[(d_*x_)^m_.*Px_*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
          (d*x)^m/x^m \\[Star] Int[x^m*Px*(a+b*x^n+c*x^(2*n))^p,x] /;
        FreeQ[{a,b,c,d,m,n,p},x] && EqQ[n2,2*n] && PolyQ[Px,x^n] && NeQ[b^2-4*a*c,0] && IntegerQ[Simplify[(m+1)/n]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [d__, m_, px__, a__, b__, n_, c__, n2_, p_, x_],
        optional: [m_, b__, c__, n2_],
        when: {
            freeq!([a__, b__, c__, d__, m_, n_, p_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && rubi_poly_q_power(&px__, x_, &n_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && integerq!(rubi_simplify(&((&m_ + 1) / &n_)))
        },
        rhs: {
            let recursive_integrand = x_.pow(&m_)
                * &px__
                * (&a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_))
                    .pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let multiplier = (&d__ * x_).pow(&m_) / x_.pow(&m_);

            rubi_star(multiplier, recursive)
        },
    ));
}

fn push_rules_rule_2289(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        a__, b__, c__, e__, f__, g__, h__, m_, n_, n2_, q_, r_, s_, x_
    );
    rules.push(rubi_rule!(
        order: 2289,
        source: "Int[x_^m_.*(e_+f_.*x_^q_.+g_.*x_^r_.+h_.*x_^s_.)/(a_+b_.*x_^n_.+c_.*x_^n2_.)^(3/2),x_Symbol] :=
          -(2*c*(b*f-2*a*g)+2*h*(b^2-4*a*c)*x^(n/2)+2*c*(2*c*f-b*g)*x^n)/(c*n*(b^2-4*a*c)*Sqrt[a+b*x^n+c*x^(2*n)]) /;
        FreeQ[{a,b,c,e,f,g,h,m,n},x] && EqQ[n2,2*n] && EqQ[q,n/2] && EqQ[r,3*n/2] && EqQ[s,2*n] &&
          NeQ[b^2-4*a*c,0] && EqQ[2*m-n+2,0] && EqQ[c*e+a*h,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: x_.pow(m_)
            * (e__ + f__ * x_.pow(q_) + g__ * x_.pow(r_) + h__ * x_.pow(s_))
            / (a__ + b__ * x_.pow(n_) + c__ * x_.pow(n2_)).pow(Atom::num(3) / Atom::num(2)),
        with: [m_, e__, f__, q_, g__, r_, h__, s_, a__, b__, n_, c__, n2_, x_],
        optional: [m_, f__, q_, g__, r_, h__, s_, b__, n_, c__, n2_],
        when: {
            freeq!([a__, b__, c__, e__, f__, g__, h__, m_, n_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && eqq!(q_, &n_ / 2)
                && eqq!(r_, Atom::num(3) * &n_ / 2)
                && eqq!(s_, Atom::num(2) * &n_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && eqq!(Atom::num(2) * &m_ - &n_ + 2, 0)
                && eqq!(&c__ * &e__ + &a__ * &h__, 0)
        },
        rhs: {
            let discriminant = b__.pow(2) - Atom::num(4) * &a__ * &c__;
            let trinomial = &a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_);
            let numerator = Atom::num(2) * &c__ * (&b__ * &f__ - Atom::num(2) * &a__ * &g__)
                + Atom::num(2) * &h__ * &discriminant * x_.pow(&n_ / 2)
                + Atom::num(2) * &c__ * (Atom::num(2) * &c__ * &f__ - &b__ * &g__)
                    * x_.pow(&n_);

            rubi_simp(&(-numerator / (&c__ * &n_ * &discriminant * trinomial.sqrt())), x_)
        },
    ));
}

fn push_rules_rule_2290(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        a__, b__, c__, d__, e__, f__, g__, h__, m_, n_, n2_, q_, r_, s_, x_
    );
    rules.push(rubi_rule!(
        order: 2290,
        source: "Int[(d_*x_)^m_.*(e_+f_.*x_^q_.+g_.*x_^r_.+h_.*x_^s_.)/(a_+b_.*x_^n_.+c_.*x_^n2_.)^(3/2),x_Symbol] :=
          (d*x)^m/x^m \\[Star] Int[x^m*(e+f*x^(n/2)+g*x^((3*n)/2)+h*x^(2*n))/(a+b*x^n+c*x^(2*n))^(3/2),x] /;
        FreeQ[{a,b,c,d,e,f,g,h,m,n},x] && EqQ[n2,2*n] && EqQ[q,n/2] && EqQ[r,3*n/2] && EqQ[s,2*n] &&
          NeQ[b^2-4*a*c,0] && EqQ[2*m-n+2,0] && EqQ[c*e+a*h,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern: (d__ * x_).pow(m_)
            * (e__ + f__ * x_.pow(q_) + g__ * x_.pow(r_) + h__ * x_.pow(s_))
            / (a__ + b__ * x_.pow(n_) + c__ * x_.pow(n2_)).pow(Atom::num(3) / Atom::num(2)),
        with: [d__, m_, e__, f__, q_, g__, r_, h__, s_, a__, b__, n_, c__, n2_, x_],
        optional: [m_, f__, q_, g__, r_, h__, s_, b__, n_, c__, n2_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__, m_, n_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && eqq!(q_, &n_ / 2)
                && eqq!(r_, Atom::num(3) * &n_ / 2)
                && eqq!(s_, Atom::num(2) * &n_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && eqq!(Atom::num(2) * &m_ - &n_ + 2, 0)
                && eqq!(&c__ * &e__ + &a__ * &h__, 0)
        },
        rhs: {
            let numerator = &e__
                + &f__ * x_.pow(&n_ / 2)
                + &g__ * x_.pow(Atom::num(3) * &n_ / 2)
                + &h__ * x_.pow(Atom::num(2) * &n_);
            let denominator = (&a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_))
                .pow(Atom::num(3) / Atom::num(2));
            let recursive_integrand = x_.pow(&m_) * numerator / denominator;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let multiplier = (&d__ * x_).pow(&m_) / x_.pow(&m_);

            rubi_star(multiplier, recursive)
        },
    ));
}

fn push_rules_rule_2291(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, n2_, p_, px__, x_);
    rules.push(rubi_rule!(
        order: 2291,
        source: "Int[x_^m_*Px_*(a_+b_.*x_^n_+c_.*x_^n2_)^p_,x_Symbol] :=
          Module[{q=Expon[Px,x]},
          Module[{Q=PolynomialQuotient[a*(b*c)^(Floor[(q-1)/n]+1)*x^m*Px,a+b*x^n+c*x^(2*n),x],
                  R=PolynomialRemainder[a*(b*c)^(Floor[(q-1)/n]+1)*x^m*Px,a+b*x^n+c*x^(2*n),x],i},
          -x*(a+b*x^n+c*x^(2*n))^(p+1)/(a^2*n*(p+1)*(b^2-4*a*c)*(b*c)^(Floor[(q-1)/n]+1))*
            Sum[((b^2-2*a*c)*Coeff[R,x,i]-a*b*Coeff[R,x,n+i])*x^i+
              c*(b*Coeff[R,x,i]-2*a*Coeff[R,x,n+i])*x^(n+i),{i,0,n-1}] +
          1/(a*n*(p+1)*(b^2-4*a*c)*(b*c)^(Floor[(q-1)/n]+1)) \\[Star] Int[x^m*(a+b*x^n+c*x^(2*n))^(p+1)*
            ExpandToSum[n*(p+1)*(b^2-4*a*c)*x^(-m)*Q+
              Sum[((b^2*(n*(p+1)+i+1)/a-2*c*(2*n*(p+1)+i+1))*Coeff[R,x,i]-b*(i+1)*Coeff[R,x,n+i])*x^(i-m)+
               c*(n*(2*p+3)+i+1)*(b/a*Coeff[R,x,i]-2*Coeff[R,x,n+i])*x^(n+i-m),{i,0,n-1}],x],x]] /;
         GeQ[q,2*n]] /;
        FreeQ[{a,b,c},x] && EqQ[n2,2*n] && PolyQ[Px,x] && NeQ[b^2-4*a*c,0] && IGtQ[n,0] && LtQ[p,-1] && ILtQ[m,0]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [m_, px__, a__, b__, n_, c__, n2_, p_, x_],
        optional: [b__, c__],
        when: {
            freeq!([a__, b__, c__], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && rubi_poly_q(&px__, x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && igtq!(n_, 0)
                && ltq!(p_, -1)
                && iltq!(m_, 0)
                && rubi_expon(&px__, x_).is_some_and(|q| geq!(Atom::num(q), Atom::num(2) * &n_))
        },
        rhs: {
            let q = rubi_expon(&px__, x_).rubi_rhs();
            let n_i = integer_i64(&n_).rubi_rhs();
            let m_i = integer_i64(&m_).rubi_rhs();
            let k = rubi_floor(q - 1, n_i).rubi_rhs() + 1;
            let trinomial = &a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_);
            let discriminant = b__.pow(2) - Atom::num(4) * &a__ * &c__;
            let bc_power = (&b__ * &c__).pow(k);
            let direct_denominator =
                a__.pow(2) * &n_ * (&p_ + 1) * &discriminant * &bc_power;
            let recursive_denominator = &a__ * &n_ * (&p_ + 1) * &discriminant * &bc_power;
            let dividend = &a__ * &bc_power * x_.pow(&m_) * &px__;
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
                recursive_sum += ((b__.pow(2) * (&n_ * (&p_ + 1) + &i_atom + 1) / &a__
                    - Atom::num(2) * &c__ * (Atom::num(2) * &n_ * (&p_ + 1) + &i_atom + 1))
                    * &coeff_i
                    - &b__ * (&i_atom + 1) * &coeff_n_i)
                    * x_.pow(i - m_i)
                    + &c__
                        * (&n_ * (Atom::num(2) * &p_ + 3) + &i_atom + 1)
                        * (&b__ * &coeff_i / &a__ - Atom::num(2) * &coeff_n_i)
                        * x_.pow(n_i + i - m_i);
            }

            let direct = Atom::num(-1) * x_ * trinomial.pow(&p_ + 1) * direct_sum / &direct_denominator;
            let expand_to_sum_payload =
                &n_ * (&p_ + 1) * &discriminant * x_.pow(-&m_) * capital_q + recursive_sum;
            let expand_to_sum = rubi_expand_to_sum(&expand_to_sum_payload, x_);
            let recursive_integrand = x_.pow(&m_) * trinomial.pow(&p_ + 1) * expand_to_sum;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            direct
                    + rubi_star(Atom::num(1) / recursive_denominator, recursive)
        },
    ));
}

fn push_rules_rule_2292(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, n2_, p_, px__, x_);
    rules.push(rubi_rule!(
        order: 2292,
        source: "Int[x_^m_.*Px_*(a_+b_.*x_^n_+c_.*x_^n2_)^p_,x_Symbol] :=
          With[{g=GCD[m+1,n]},
          1/g \\[Star] Subst[Int[x^((m+1)/g-1)*ReplaceAll[Px,x->x^(1/g)]*(a+b*x^(n/g)+c*x^(2*n/g))^p,x],x,x^g] /;
         NeQ[g,1]] /;
        FreeQ[{a,b,c,p},x] && EqQ[n2,2*n] && PolyQ[Px,x^n] && NeQ[b^2-4*a*c,0] && IGtQ[n,0] && IntegerQ[m]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [m_, px__, a__, b__, n_, c__, n2_, p_, x_],
        optional: [m_, b__, c__],
        when: {
            freeq!([a__, b__, c__, p_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && rubi_poly_q_power(&px__, x_, &n_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && igtq!(n_, 0)
                && integerq!(m_)
                && rubi_gcd(&(&m_ + 1), &n_).is_some_and(|g| g != 1)
        },
        rhs: {
            let g_i = rubi_gcd(&(&m_ + Atom::num(1)), &n_).rubi_rhs();
            let g = Atom::num(g_i);
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let sub_atom = Atom::var(sub);
            let replaced =
                rubi_replace_all(&px__, x_, sub_atom.pow(Atom::num(1) / &g));
            let transformed_integrand = sub_atom.pow((&m_ + Atom::num(1)) / &g - 1)
                * replaced
                * (&a__
                    + &b__ * sub_atom.pow(&n_ / &g)
                    + &c__ * sub_atom.pow(Atom::num(2) * &n_ / &g))
                .pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);
            let substituted = rubi_subst(&transformed, sub, x_.pow(g));

            rubi_star(Atom::num(1) / g_i, substituted)
        },
    ));
}

fn push_rules_rule_2293(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, n2_, p_, px__, x_);
    rules.push(rubi_rule!(
        order: 2293,
        source: "Int[Px_*(d_.*x_)^m_.*(a_+b_.*x_^n_.+c_.*x_^n2_)^p_,x_Symbol] :=
          With[{q=Expon[Px,x^n]},
          Coeff[Px,x^n,q]*(d*x)^(m+n*q-2*n+1)*(a+b*x^n+c*x^(2*n))^(p+1)/(c*d^(n*q-2*n+1)*(m+n*(2*p+q)+1)) +
          Int[(d*x)^m*(a+b*x^n+c*x^(2*n))^p*
            ExpandToSum[Px-Coeff[Px,x^n,q]*x^(n*q)-Coeff[Px,x^n,q]*(a*(m+n*q-2*n+1)*x^(n*(q-2))+b*(m+n*(p+q-1)+1)*x^(n*(q-1)))/(c*(m+n*(2*p+q)+1)),x],x] /;
         GtQ[q,1] && NeQ[m+n*(2*p+q)+1,0] && (IntegerQ[2*p] || EqQ[n,1] && IntegerQ[4*p] || IntegerQ[p+(n*q+1)/(2*n)])] /;
        FreeQ[{a,b,c,d,m,p},x] && EqQ[n2,2*n] && PolyQ[Px,x^n] && NeQ[b^2-4*a*c,0] && IGtQ[n,0]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [d__, m_, px__, a__, b__, n_, c__, n2_, p_, x_],
        optional: [d__, m_, b__, n_, c__],
        when: {
            freeq!([a__, b__, c__, d__, m_, p_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && rubi_poly_q_power(&px__, x_, &n_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && igtq!(n_, 0)
                && rubi_expon_power(&px__, x_, &n_).is_some_and(|q_i| {
                    let q = Atom::num(q_i);
                    gtq!(&q, 1)
                        && neq!(&m_ + &n_ * (Atom::num(2) * &p_ + &q) + 1, 0)
                        && (integerq!(Atom::num(2) * &p_)
                            || eqq!(n_, 1) && integerq!(Atom::num(4) * &p_)
                            || integerq!(&p_ + (&n_ * &q + 1) / (Atom::num(2) * &n_)))
                })
        },
        rhs: {
            let q_i = rubi_expon_power(&px__, x_, &n_).rubi_rhs();
            let q = Atom::num(q_i);
            let pqq = rubi_coeff_power(&px__, x_, &n_, q_i).rubi_rhs();
            let trinomial = &a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_);
            let denominator_factor = &m_ + &n_ * (Atom::num(2) * &p_ + &q) + 1;
            let d_exponent = &n_ * &q - Atom::num(2) * &n_ + 1;
            let direct_denominator = &c__ * d__.pow(&d_exponent) * &denominator_factor;
            let payload_denominator = &c__ * &denominator_factor;

            let direct = &pqq
                * (&d__ * x_).pow(&m_ + &n_ * &q - Atom::num(2) * &n_ + 1)
                * trinomial.pow(&p_ + 1)
                / direct_denominator;
            let expand_to_sum_payload = &px__
                - &pqq * x_.pow(&n_ * &q)
                - &pqq
                    * (&a__ * (&m_ + &n_ * &q - Atom::num(2) * &n_ + 1)
                        * x_.pow(&n_ * (&q - 2))
                        + &b__ * (&m_ + &n_ * (&p_ + &q - 1) + 1)
                            * x_.pow(&n_ * (&q - 1)))
                    / payload_denominator;
            let expand_to_sum = rubi_expand_to_sum(&expand_to_sum_payload, x_);
            let recursive_integrand =
                (&d__ * x_).pow(&m_) * expand_to_sum * trinomial.pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) + recursive
        },
    ));
}

fn push_rules_rule_2294(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, n2_, p_, px__, x_);
    rules.push(rubi_rule!(
        order: 2294,
        source: "Int[(d_.*x_)^m_.*Px_*(a_+b_.*x_^n_+c_.*x_^n2_)^p_,x_Symbol] :=
          Module[{q=Expon[Px,x],j,k},
          Int[Sum[1/d^j*(d*x)^(m+j)*Sum[Coeff[Px,x,j+k*n]*x^(k*n),{k,0,(q-j)/n+1}]*(a+b*x^n+c*x^(2*n))^p,{j,0,n-1}],x]] /;
        FreeQ[{a,b,c,d,m,p},x] && EqQ[n2,2*n] && PolyQ[Px,x] && NeQ[b^2-4*a*c,0] && IGtQ[n,0] && Not[PolyQ[Px,x^n]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [d__, m_, px__, a__, b__, n_, c__, n2_, p_, x_],
        optional: [d__, m_, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, m_, p_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && rubi_poly_q(&px__, x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && igtq!(n_, 0)
                && !rubi_poly_q_power(&px__, x_, &n_)
        },
        rhs: {
            let q_i = rubi_expon(&px__, x_).rubi_rhs();
            let n_i = integer_i64(&n_).rubi_rhs();
            let trinomial = &a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_);
            let mut regrouped = Atom::num(0);
            for j in 0..n_i {
                let j_atom = Atom::num(j);
                let mut inner_sum = Atom::num(0);
                let upper = rubi_floor(q_i - j, n_i).rubi_rhs() + 1;
                for k in 0..=upper {
                    inner_sum +=
                        rubi_coeff(&px__, x_, j + k * n_i).rubi_rhs() * x_.pow(k * n_i);
                }

                regrouped += d__.pow(-j)
                    * (&d__ * x_).pow(&m_ + &j_atom)
                    * inner_sum
                    * trinomial.pow(&p_);
            }

            rubi_rhs_int(&regrouped, x_)
        },
    ));
}

fn push_rules_rule_2295(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, n2_, px__, x_);
    rules.push(rubi_rule!(
        order: 2295,
        source: "Int[(d_.*x_)^m_.*Px_/(a_+b_.*x_^n_.+c_.*x_^n2_.),x_Symbol] :=
          Int[RationalFunctionExpand[(d*x)^m*Px/(a+b*x^n+c*x^(2*n)),x],x] /;
        FreeQ[{a,b,c,d,m},x] && EqQ[n2,2*n] && PolyQ[Px,x] && NeQ[b^2-4*a*c,0] && IGtQ[n,0]",
        desc: "Expand the rational function into simpler fractions.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [d__, m_, px__, a__, b__, n_, c__, n2_, x_],
        optional: [d__, m_, b__, n_, c__, n2_],
        when: {
            freeq!([a__, b__, c__, d__, m_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && rubi_poly_q(&px__, x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && igtq!(n_, 0)
        },
        rhs: {
            let payload = (&d__ * x_).pow(&m_) * &px__
                / (&a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_));
            let expanded = rubi_rational_function_expand(&payload, x_).rubi_rhs();

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_2296(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, n2_, p_, px__, x_);
    rules.push(rubi_rule!(
        order: 2296,
        source: "Int[x_^m_.*Px_*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
          With[{q=Expon[Px,x]},
          -Subst[Int[ExpandToSum[x^q*ReplaceAll[Px,x->x^(-1)],x]*(a+b*x^(-n)+c*x^(-2*n))^p/x^(m+q+2),x],x,1/x]] /;
        FreeQ[{a,b,c,p},x] && EqQ[n2,2*n] && PolyQ[Px,x] && NeQ[b^2-4*a*c,0] && ILtQ[n,0] && IntegerQ[m]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [m_, px__, a__, b__, n_, c__, n2_, p_, x_],
        optional: [m_, b__, c__, n2_],
        when: {
            freeq!([a__, b__, c__, p_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && rubi_poly_q(&px__, x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && iltq!(n_, 0)
                && integerq!(m_)
        },
        rhs: {
            let q_i = rubi_expon(&px__, x_).rubi_rhs();
            let q = Atom::num(q_i);
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let sub_atom = Atom::var(sub);
            let replaced = rubi_replace_all(&px__, x_, sub_atom.pow(-1));
            let expand_to_sum = rubi_expand_to_sum(&(sub_atom.pow(&q) * replaced), sub);
            let transformed_integrand = expand_to_sum
                * (&a__ + &b__ * sub_atom.pow(-&n_) + &c__ * sub_atom.pow(Atom::num(-2) * &n_))
                    .pow(&p_)
                / sub_atom.pow(&m_ + &q + 2);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);

            -rubi_subst(&transformed, sub, Atom::num(1) / x_)
        },
    ));
}

fn push_rules_rule_2297(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, n2_, p_, px__, x_);
    rules.push(rubi_rule!(
        order: 2297,
        source: "Int[(d_.*x_)^m_.*Px_*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
          With[{g=Denominator[m],q=Expon[Px,x]},
          -g/d \\[Star] Subst[Int[ExpandToSum[x^(g*q)*ReplaceAll[Px,x->d^(-1)*x^(-g)],x]*
            (a+b*d^(-n)*x^(-g*n)+c*d^(-2*n)*x^(-2*g*n))^p/x^(g*(m+q+1)+1),x],x,1/(d*x)^(1/g)]] /;
        FreeQ[{a,b,c,d,p},x] && EqQ[n2,2*n] && PolyQ[Px,x] && NeQ[b^2-4*a*c,0] && ILtQ[n,0] && FractionQ[m]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [d__, m_, px__, a__, b__, n_, c__, n2_, p_, x_],
        optional: [d__, m_, b__, c__, n2_],
        when: {
            freeq!([a__, b__, c__, d__, p_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && rubi_poly_q(&px__, x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && iltq!(n_, 0)
                && fractionq!(m_)
        },
        rhs: {
            let g_i = rubi_denominator(&m_).rubi_rhs();
            let g = Atom::num(g_i);
            let q_i = rubi_expon(&px__, x_).rubi_rhs();
            let q = Atom::num(q_i);
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let sub_atom = Atom::var(sub);
            let replaced = rubi_replace_all(&px__, x_, d__.pow(-1) * sub_atom.pow(-&g));
            let expand_to_sum =
                rubi_expand_to_sum(&(sub_atom.pow(&g * &q) * replaced), sub);
            let transformed_integrand = expand_to_sum
                * (&a__
                    + &b__ * d__.pow(-&n_) * sub_atom.pow(-&g * &n_)
                    + &c__ * d__.pow(Atom::num(-2) * &n_)
                        * sub_atom.pow(Atom::num(-2) * &g * &n_))
                .pow(&p_)
                / sub_atom.pow(&g * (&m_ + &q + 1) + 1);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);
            let replacement = Atom::num(1) / (&d__ * x_).pow(Atom::num(1) / &g);
            let substituted = rubi_subst(&transformed, sub, replacement);

            rubi_star(-&g / &d__, substituted)
        },
    ));
}

fn push_rules_rule_2298(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, n2_, p_, px__, x_);
    rules.push(rubi_rule!(
        order: 2298,
        source: "Int[(d_.*x_)^m_*Px_*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
          With[{q=Expon[Px,x]},
          -(d*x)^m*(x^(-1))^m \\[Star] Subst[Int[ExpandToSum[x^q*ReplaceAll[Px,x->x^(-1)],x]*(a+b*x^(-n)+c*x^(-2*n))^p/x^(m+q+2),x],x,1/x]] /;
        FreeQ[{a,b,c,d,m,p},x] && EqQ[n2,2*n] && PolyQ[Px,x] && NeQ[b^2-4*a*c,0] && ILtQ[n,0] && Not[RationalQ[m]]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [d__, m_, px__, a__, b__, n_, c__, n2_, p_, x_],
        optional: [d__, b__, c__, n2_],
        when: {
            freeq!([a__, b__, c__, d__, m_, p_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && rubi_poly_q(&px__, x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && iltq!(n_, 0)
                && !rationalq!(m_)
        },
        rhs: {
            let q_i = rubi_expon(&px__, x_).rubi_rhs();
            let q = Atom::num(q_i);
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let sub_atom = Atom::var(sub);
            let replaced = rubi_replace_all(&px__, x_, sub_atom.pow(-1));
            let expand_to_sum = rubi_expand_to_sum(&(sub_atom.pow(&q) * replaced), sub);
            let transformed_integrand = expand_to_sum
                * (&a__ + &b__ * sub_atom.pow(-&n_) + &c__ * sub_atom.pow(Atom::num(-2) * &n_))
                    .pow(&p_)
                / sub_atom.pow(&m_ + &q + 2);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);
            let substituted = rubi_subst(&transformed, sub, Atom::num(1) / x_);
            let multiplier = -(&d__ * x_).pow(&m_) * x_.pow(-1).pow(&m_);

            rubi_star(multiplier, substituted)
        },
    ));
}

fn push_rules_rule_2299(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, n2_, p_, px__, x_);
    rules.push(rubi_rule!(
        order: 2299,
        source: "Int[x_^m_.*Px_*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
          With[{g=Denominator[n]},
          g \\[Star] Subst[Int[x^(g*(m+1)-1)*ReplaceAll[Px,x->x^g]*(a+b*x^(g*n)+c*x^(2*g*n))^p,x],x,x^(1/g)]] /;
        FreeQ[{a,b,c,m,p},x] && EqQ[n2,2*n] && PolyQ[Px,x] && NeQ[b^2-4*a*c,0] && FractionQ[n]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [m_, px__, a__, b__, n_, c__, n2_, p_, x_],
        optional: [m_, b__, c__, n2_],
        when: {
            freeq!([a__, b__, c__, m_, p_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && rubi_poly_q(&px__, x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && fractionq!(n_)
        },
        rhs: {
            let g_i = rubi_denominator(&n_).rubi_rhs();
            let g = Atom::num(g_i);
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let sub_atom = Atom::var(sub);
            let replaced = rubi_replace_all(&px__, x_, sub_atom.pow(&g));
            let transformed_integrand = sub_atom.pow(&g * (&m_ + 1) - 1)
                * replaced
                * (&a__
                    + &b__ * sub_atom.pow(&g * &n_)
                    + &c__ * sub_atom.pow(Atom::num(2) * &g * &n_))
                .pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);
            let substituted = rubi_subst(
                &transformed,
                sub,
                x_.pow(Atom::num(1) / g_i),
            );

            rubi_star(g, substituted)
        },
    ));
}

fn push_rules_rule_2300(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, n2_, p_, px__, x_);
    rules.push(rubi_rule!(
        order: 2300,
        source: "Int[(d_*x_)^m_*Px_*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
          d^(m-1/2)*Sqrt[d*x]/Sqrt[x] \\[Star] Int[x^m*Px*(a+b*x^n+c*x^(2*n))^p,x] /;
        FreeQ[{a,b,c,d,p},x] && EqQ[n2,2*n] && PolyQ[Px,x] && NeQ[b^2-4*a*c,0] && FractionQ[n] && IGtQ[m+1/2,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [d__, m_, px__, a__, b__, n_, c__, n2_, p_, x_],
        optional: [b__, c__, n2_],
        when: {
            freeq!([a__, b__, c__, d__, p_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && rubi_poly_q(&px__, x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && fractionq!(n_)
                && igtq!(&m_ + Atom::num(1) / Atom::num(2), 0)
        },
        rhs: {
            let recursive_integrand = x_.pow(&m_)
                * &px__
                * (&a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_))
                    .pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let multiplier = d__.pow(&m_ - Atom::num(1) / Atom::num(2))
                * (&d__ * x_).sqrt()
                / x_.sqrt();

            rubi_star(multiplier, recursive)
        },
    ));
}

fn push_rules_rule_2301(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, n2_, p_, px__, x_);
    rules.push(rubi_rule!(
        order: 2301,
        source: "Int[(d_*x_)^m_*Px_*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
          d^(m+1/2)*Sqrt[x]/Sqrt[d*x] \\[Star] Int[x^m*Px*(a+b*x^n+c*x^(2*n))^p,x] /;
        FreeQ[{a,b,c,d,p},x] && EqQ[n2,2*n] && PolyQ[Px,x] && NeQ[b^2-4*a*c,0] && FractionQ[n] && ILtQ[m-1/2,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [d__, m_, px__, a__, b__, n_, c__, n2_, p_, x_],
        optional: [b__, c__, n2_],
        when: {
            freeq!([a__, b__, c__, d__, p_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && rubi_poly_q(&px__, x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && fractionq!(n_)
                && iltq!(&m_ - Atom::num(1) / Atom::num(2), 0)
        },
        rhs: {
            let recursive_integrand = x_.pow(&m_)
                * &px__
                * (&a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_))
                    .pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let multiplier = d__.pow(&m_ + Atom::num(1) / Atom::num(2))
                * x_.sqrt()
                / (&d__ * x_).sqrt();

            rubi_star(multiplier, recursive)
        },
    ));
}

fn push_rules_rule_2302(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, n2_, p_, px__, x_);
    rules.push(rubi_rule!(
        order: 2302,
        source: "Int[(d_*x_)^m_*Px_*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
          (d*x)^m/x^m \\[Star] Int[x^m*Px*(a+b*x^n+c*x^(2*n))^p,x] /;
        FreeQ[{a,b,c,d,m,p},x] && EqQ[n2,2*n] && PolyQ[Px,x] && NeQ[b^2-4*a*c,0] && FractionQ[n]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [d__, m_, px__, a__, b__, n_, c__, n2_, p_, x_],
        optional: [b__, c__, n2_],
        when: {
            freeq!([a__, b__, c__, d__, m_, p_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && rubi_poly_q(&px__, x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && fractionq!(n_)
        },
        rhs: {
            let recursive_integrand = x_.pow(&m_)
                * &px__
                * (&a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_))
                    .pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let multiplier = (&d__ * x_).pow(&m_) / x_.pow(&m_);

            rubi_star(multiplier, recursive)
        },
    ));
}

fn push_rules_rule_2303(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, n2_, p_, px__, x_);
    rules.push(rubi_rule!(
        order: 2303,
        source: "Int[x_^m_.*Px_*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
          1/(m+1) \\[Star] Subst[Int[ReplaceAll[SubstFor[x^n,Px,x],x->x^Simplify[n/(m+1)]]*(a+b*x^Simplify[n/(m+1)]+c*x^Simplify[2*n/(m+1)])^p,x],x,x^(m+1)] /;
        FreeQ[{a,b,c,m,n,p},x] && EqQ[n2,2*n] && PolyQ[Px,x^n] && NeQ[b^2-4*a*c,0] && IntegerQ[Simplify[n/(m+1)]] && Not[IntegerQ[n]]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [m_, px__, a__, b__, n_, c__, n2_, p_, x_],
        optional: [m_, b__, c__, n2_],
        when: {
            let m_plus_one = &m_ + 1;

            freeq!([a__, b__, c__, m_, n_, p_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && rubi_poly_q_power(&px__, x_, &n_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && integerq!(rubi_simplify(&(&n_ / &m_plus_one)))
                && !integerq!(n_)
        },
        rhs: {
            let m_plus_one = &m_ + 1;
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let sub_atom = Atom::var(sub);
            let exponent = rubi_simplify(&(&n_ / &m_plus_one));
            let exponent2 = rubi_simplify(&(Atom::num(2) * &n_ / &m_plus_one));
            let subst_for = rubi_subst_for_power(&px__, x_, &n_, sub).rubi_rhs();
            let replaced = rubi_replace_all(&subst_for, sub, sub_atom.pow(&exponent));
            let transformed_integrand =
                replaced * (&a__ + &b__ * sub_atom.pow(&exponent) + &c__ * sub_atom.pow(&exponent2)).pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);
            let substituted = rubi_subst(&transformed, sub, x_.pow(&m_plus_one));

            rubi_star(Atom::num(1) / &m_plus_one, substituted)
        },
    ));
}

fn push_rules_rule_2304(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, n2_, p_, px__, x_);
    rules.push(rubi_rule!(
        order: 2304,
        source: "Int[(d_*x_)^m_*Px_*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
          (d*x)^m/x^m \\[Star] Int[x^m*Px*(a+b*x^n+c*x^(2*n))^p,x] /;
        FreeQ[{a,b,c,d,m,p},x] && EqQ[n2,2*n] && PolyQ[Px,x^n] && NeQ[b^2-4*a*c,0] && IntegerQ[Simplify[n/(m+1)]] && Not[IntegerQ[n]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [d__, m_, px__, a__, b__, n_, c__, n2_, p_, x_],
        optional: [b__, c__, n2_],
        when: {
            let m_plus_one = &m_ + 1;

            freeq!([a__, b__, c__, d__, m_, p_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && rubi_poly_q_power(&px__, x_, &n_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && integerq!(rubi_simplify(&(&n_ / &m_plus_one)))
                && !integerq!(n_)
        },
        rhs: {
            let recursive_integrand = x_.pow(&m_)
                * &px__
                * (&a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_))
                    .pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let multiplier = (&d__ * x_).pow(&m_) / x_.pow(&m_);

            rubi_star(multiplier, recursive)
        },
    ));
}

fn push_rules_rule_2305(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, n2_, px__, x_);
    rules.push(rubi_rule!(
        order: 2305,
        source: "Int[(d_.*x_)^m_.*Px_/(a_+b_.*x_^n_.+c_.*x_^n2_.),x_Symbol] :=
          With[{q=Rt[b^2-4*a*c,2]},
          2*c/q \\[Star] Int[(d*x)^m*Px/(b-q+2*c*x^n),x] -
          2*c/q \\[Star] Int[(d*x)^m*Px/(b+q+2*c*x^n),x]] /;
        FreeQ[{a,b,c,d,m,n},x] && EqQ[n2,2*n] && PolyQ[Px,x] && NeQ[b^2-4*a*c,0]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [d__, m_, px__, a__, b__, n_, c__, n2_, x_],
        optional: [d__, m_, b__, n_, c__, n2_],
        when: {
            freeq!([a__, b__, c__, d__, m_, n_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && rubi_poly_q(&px__, x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
        },
        rhs: {
            let q = rubi_rt(&(b__.pow(2) - Atom::num(4) * &a__ * &c__), 2);
            let first_integrand = (&d__ * x_).pow(&m_) * &px__
                / (&b__ - &q + Atom::num(2) * &c__ * x_.pow(&n_));
            let second_integrand = (&d__ * x_).pow(&m_) * &px__
                / (&b__ + &q + Atom::num(2) * &c__ * x_.pow(&n_));
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);
            let multiplier = Atom::num(2) * &c__ / &q;

            rubi_star(&multiplier, first) - rubi_star(multiplier, second)
        },
    ));
}

fn push_rules_rule_2306(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, n2_, p_, px__, x_);
    rules.push(rubi_rule!(
        order: 2306,
        source: "Int[(d_.*x_)^m_.*Px_*(a_+b_.*x_^n_.+c_.*x_^n2_.)^p_,x_Symbol] :=
          Int[ExpandIntegrand[(d*x)^m*Px*(a+b*x^n+c*x^(2*n))^p,x],x] /;
        FreeQ[{a,b,c,d,m,n},x] && EqQ[n2,2*n] && PolyQ[Px,x]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [d__, m_, px__, a__, b__, n_, c__, n2_, p_, x_],
        optional: [d__, m_, b__, n_, c__, n2_],
        when: {
            freeq!([a__, b__, c__, d__, m_, n_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && rubi_poly_q(&px__, x_)
        },
        rhs: {
            let integrand = (&d__ * x_).pow(&m_)
                * &px__
                * (&a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_))
                    .pow(&p_);
            let expanded = rubi_expand_integrand(&integrand, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_2307(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, m_, n_, n2_, p_, px__, u__, v__);
    rules.push(rubi_rule!(
        order: 2307,
        source: "Int[u_^m_.*Px_*(a_+b_.*v_^n_+c_.*v_^n2_.)^p_.,x_Symbol] :=
          u^m/(Coefficient[v,x,1]*v^m) \\[Star] Subst[Int[x^m*SubstFor[v,Px,x]*(a+b*x^n+c*x^(2*n))^p,x],x,v] /;
        FreeQ[{a,b,c,m,n,p},x] && EqQ[n2,2*n] && LinearPairQ[u,v,x] && PolyQ[Px,v^n]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern: u__.pow(m_) * px__ * (a__ + b__ * v__.pow(n_) + c__ * v__.pow(n2_)).pow(p_),
        with: [u__, m_, px__, a__, b__, v__, n_, c__, n2_, p_, x_],
        optional: [m_, b__, c__, n2_, p_],
        x_dep: [u__, v__],
        x_free: [a__, b__, c__, m_, n_, p_],
        x_linear: [u__, v__],
        when: {
            freeq!([a__, b__, c__, m_, n_, p_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && rubi_linear_pair_q(&u__, &v__, x_)
                && rubi_poly_q_power_of(&px__, &v__, &n_, x_)
        },
        rhs: {
            let coefficient = rubi_coefficient(&v__, x_, 1).rubi_rhs();
            let multiplier = u__.pow(&m_) / (&coefficient * v__.pow(&m_));

            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let sub_atom = Atom::var(sub);
            let subst_for = rubi_subst_for(&px__, &v__, sub);
            let transformed_integrand = sub_atom.pow(&m_)
                * subst_for
                * (&a__
                    + &b__ * sub_atom.pow(&n_)
                    + &c__ * sub_atom.pow(Atom::num(2) * &n_))
                .pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);

            let substituted = rubi_subst(&transformed, sub, v__);

            rubi_star(multiplier, substituted)
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
    let m_ = symbols.m_;
    let n2_ = symbols.n2_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let px__ = symbols.px__;
    let x_ = symbols.x_;
    (d__ * x_).pow(m_) * px__ * (a__ + b__ * x_.pow(n_) + c__ * x_.pow(n2_)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let m_ = symbols.m_;
    let n2_ = symbols.n2_;
    let n_ = symbols.n_;
    let px__ = symbols.px__;
    let x_ = symbols.x_;
    (d__ * x_).pow(m_) * px__ / (a__ + b__ * x_.pow(n_) + c__ * x_.pow(n2_))
}

#[inline(never)]
fn rubi_shared_pattern_2(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let m_ = symbols.m_;
    let n2_ = symbols.n2_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let px__ = symbols.px__;
    let x_ = symbols.x_;
    x_.pow(m_) * px__ * (a__ + b__ * x_.pow(n_) + c__ * x_.pow(n2_)).pow(p_)
}
