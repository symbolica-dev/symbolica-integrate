use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_2356(rules);
    push_rules_rule_2357(rules);
    push_rules_rule_2358(rules);
    push_rules_rule_2359(rules);
    push_rules_rule_2360(rules);
    push_rules_rule_2361(rules);
    push_rules_rule_2362(rules);
    push_rules_rule_2363(rules);
    push_rules_rule_2364(rules);
    push_rules_rule_2365(rules);
    push_rules_rule_2366(rules);
    push_rules_rule_2367(rules);
    push_rules_rule_2368(rules);
    push_rules_rule_2369(rules);
    push_rules_rule_2370(rules);
    push_rules_rule_2372(rules);
    push_rules_rule_2373(rules);
    push_rules_rule_2374(rules);
    push_rules_rule_2375(rules);
    push_rules_rule_2376(rules);
    push_rules_rule_2377(rules);
    push_rules_rule_2378(rules);
    push_rules_rule_2379(rules);
    push_rules_rule_2380(rules);
    push_rules_rule_2381(rules);
    push_rules_rule_2382(rules);
    push_rules_rule_2383(rules);
    push_rules_rule_2384(rules);
    push_rules_rule_2385(rules);
    push_rules_rule_2386(rules);
    push_rules_rule_2387(rules);
    push_rules_rule_2388(rules);
}

fn push_rules_rule_2356(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, c__, e__, f__, g__, h__, m_, n_, q_, r_, x_);
    let three_halves_1 = Atom::num(3) / Atom::num(2);
    rules.push(rubi_rule!(
        order: 2356,
        source: "Int[x_^m_.*(e_+f_.*x_^q_.+g_.*x_^r_.+h_.*x_^n_.)/(a_+c_.*x_^n_.)^(3/2),x_Symbol] :=
          -(2*a*g+4*a*h*x^(n/4)-2*c*f*x^(n/2))/(a*c*n*Sqrt[a+c*x^n]) /;
        FreeQ[{a,c,e,f,g,h,m,n},x] && EqQ[q,n/4] && EqQ[r,3*n/4] && EqQ[4*m-n+4,0] && EqQ[c*e+a*h,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: x_.pow(m_) * (e__ + f__ * x_.pow(q_) + g__ * x_.pow(r_) + h__ * x_.pow(n_))
            / (a__ + c__ * x_.pow(n_)).pow(&three_halves_1),
        with: [a__, c__, e__, f__, g__, h__, m_, n_, q_, r_, x_],
        optional: [m_, c__, f__, q_, g__, r_, h__, n_],
        when: {
            freeq!([a__, c__, e__, f__, g__, h__, m_, n_], x_)
                && eqq!(q_, &n_ / Atom::num(4))
                && eqq!(r_, Atom::num(3) * &n_ / Atom::num(4))
                && eqq!(Atom::num(4) * &m_ - &n_ + Atom::num(4), 0)
                && eqq!(&c__ * &e__ + &a__ * &h__, 0)
        },
        rhs: {
            rubi_simp(&(-(Atom::num(2) * &a__ * &g__ + Atom::num(4) * &a__ * &h__ * x_.pow(&n_ / Atom::num(4))
                    - Atom::num(2) * &c__ * &f__ * x_.pow(&n_ / Atom::num(2)))
                    / (&a__ * &c__ * &n_ * (&a__ + &c__ * x_.pow(&n_)).sqrt())), x_)
        },
    ));
}

fn push_rules_rule_2357(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, c__, d__, e__, f__, g__, h__, m_, n_, q_, r_, x_);
    let three_halves_2 = Atom::num(3) / Atom::num(2);
    rules.push(rubi_rule!(
        order: 2357,
        source: "Int[(d_*x_)^m_.*(e_+f_.*x_^q_.+g_.*x_^r_.+h_.*x_^n_.)/(a_+c_.*x_^n_.)^(3/2),x_Symbol] :=
          (d*x)^m/x^m \\[Star] Int[x^m*(e+f*x^(n/4)+g*x^((3*n)/4)+h*x^n)/(a+c*x^n)^(3/2),x] /;
        FreeQ[{a,c,d,e,f,g,h,m,n},x] && EqQ[4*m-n+4,0] && EqQ[q,n/4] && EqQ[r,3*n/4] && EqQ[c*e+a*h,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern: (d__ * x_).pow(m_)
            * (e__ + f__ * x_.pow(q_) + g__ * x_.pow(r_) + h__ * x_.pow(n_))
            / (a__ + c__ * x_.pow(n_)).pow(&three_halves_2),
        with: [a__, c__, d__, e__, f__, g__, h__, m_, n_, q_, r_, x_],
        optional: [m_, c__, f__, q_, g__, r_, h__, n_],
        when: {
            freeq!([a__, c__, d__, e__, f__, g__, h__, m_, n_], x_)
                && eqq!(Atom::num(4) * &m_ - &n_ + Atom::num(4), 0)
                && eqq!(q_, &n_ / Atom::num(4))
                && eqq!(r_, Atom::num(3) * &n_ / Atom::num(4))
                && eqq!(&c__ * &e__ + &a__ * &h__, 0)
        },
        rhs: {
            let integrand = x_.pow(&m_)
                * (&e__
                    + &f__ * x_.pow(&n_ / Atom::num(4))
                    + &g__ * x_.pow(Atom::num(3) * &n_ / Atom::num(4))
                    + &h__ * x_.pow(&n_))
                / (&a__ + &c__ * x_.pow(&n_)).pow((3, 2));
            let recursive = rubi_rhs_int(&integrand, x_);

            rubi_star((&d__ * x_).pow(&m_), recursive / x_.pow(m_))
        },
    ));
}

fn push_rules_rule_2358(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, m_, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2358,
        source: "Int[(c_.*x_)^m_*Pq_*(a_+b_.*x_)^p_,x_Symbol] :=
          With[{n=Denominator[p]},
          n/b \\[Star] Subst[Int[x^(n*p+n-1)*(-a*c/b+c*x^n/b)^m*ReplaceAll[Pq,x->-a/b+x^n/b],x],x,(a+b*x)^(1/n)]] /;
        FreeQ[{a,b,c,m},x] && PolyQ[Pq,x] && FractionQ[p] && ILtQ[m,-1]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (c__ * x_).pow(m_) * pq__ * (a__ + b__ * x_).pow(p_),
        with: [a__, b__, c__, m_, p_, pq__, x_],
        optional: [c__, b__],
        when: {
            freeq!([a__, b__, c__, m_], x_)
                && rubi_poly_q(&pq__, x_)
                && fractionq!(p_)
                && iltq!(m_, -1)
        },
        rhs: {
            if b__.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let k_i = rubi_denominator(&p_).rubi_rhs();
            let k = Atom::num(k_i);
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub_symbol = sub_guard.symbol();
            let sub_atom = Atom::var(sub_symbol);
            let replacement = -&a__ / &b__ + sub_atom.pow(&k) / &b__;
            let transformed_px = rubi_replace_all(&pq__, x_, replacement);
            let transformed_integrand = sub_atom.pow((&k * &p_ + &k - Atom::num(1)).expand())
                * (-&a__ * &c__ / &b__ + &c__ * sub_atom.pow(&k) / &b__).pow(&m_)
                * transformed_px;
            let transformed = rubi_rhs_int(&transformed_integrand, sub_symbol);

            rubi_star(k, rubi_subst(
                    &transformed,
                    sub_symbol,
                    (&a__ + &b__ * x_).pow(Atom::num(1) / k_i),
                ) / b__)
        },
    ));
}

fn push_rules_rule_2359(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, n_, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2359,
        source: "Int[x_^m_.*Pq_*(a_+b_.*x_^n_)^p_.,x_Symbol] :=
          1/(m+1) \\[Star] Subst[Int[SubstFor[x^(m+1),Pq,x]*(a+b*x^Simplify[n/(m+1)])^p,x],x,x^(m+1)] /;
        FreeQ[{a,b,m,n,p},x] && NeQ[m,-1] && IGtQ[Simplify[n/(m+1)],0] && PolyQ[Pq,x^(m+1)]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, m_, n_, p_, pq__, x_],
        optional: [m_, b__, p_],
        when: {
            let m1 = &m_ + Atom::num(1);
            freeq!([a__, b__, m_, n_, p_], x_)
                && neq!(m_, -Atom::num(1))
                && igtq!((&n_ / &m1).expand(), 0)
                && rubi_poly_q_power(&pq__, x_, &m1)
        },
        rhs: {
            let m1 = (&m_ + Atom::num(1)).expand();
            if m1.is_zero() || eqq!(m1, 1) {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub_symbol = sub_guard.symbol();
            let sub_atom = Atom::var(sub_symbol);
            let transformed_px = subst_for_power(&pq__, x_, &m1, sub_symbol).rubi_rhs();
            let transformed_power = (&n_ / &m1).expand();
            let transformed_integrand = transformed_px * (&a__ + &b__ * sub_atom.pow(transformed_power)).pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, sub_symbol);

            rubi_star(Atom::num(1) / &m1, rubi_subst(&transformed, sub_symbol, x_.pow(&m1)))
        },
    ));
}

fn push_rules_rule_2360(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2360,
        source: "Int[(c_.*x_)^m_.*Pq_*(a_+b_.*x_^n_.)^p_.,x_Symbol] :=
          Int[ExpandIntegrand[(c*x)^m*Pq*(a+b*x^n)^p,x],x] /;
        FreeQ[{a,b,c,m,n},x] && PolyQ[Pq,x] && (IGtQ[p,0] || EqQ[n,1])",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, m_, n_, p_, pq__, x_],
        optional: [c__, m_, b__, n_, p_],
        when: {
            freeq!([a__, b__, c__, m_, n_], x_)
                && rubi_poly_q(&pq__, x_)
                && (igtq!(p_, 0) || eqq!(n_, 1))
        },
        rhs: {
            let integrand = (&c__ * x_).pow(&m_) * &pq__ * (&a__ + &b__ * x_.pow(&n_)).pow(&p_);
            let expanded = rubi_expand_integrand(&integrand, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_2361(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, n_, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2361,
        source: "Int[x_^m_.*Pq_*(a_+b_.*x_^n_)^p_.,x_Symbol] :=
          1/n \\[Star] Subst[Int[x^(Simplify[(m+1)/n]-1)*SubstFor[x^n,Pq,x]*(a+b*x)^p,x],x,x^n] /;
        FreeQ[{a,b,m,n,p},x] && PolyQ[Pq,x^n] && IntegerQ[Simplify[(m+1)/n]]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, m_, n_, p_, pq__, x_],
        optional: [m_, b__, p_],
        when: {
            let ratio = ((&m_ + Atom::num(1)) / &n_).expand();
            freeq!([a__, b__, m_, n_, p_], x_)
                && rubi_poly_q_power(&pq__, x_, &n_)
                && integerq!(ratio)
        },
        rhs: {
            if n_.is_zero() || eqq!(n_, 1) {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub_symbol = sub_guard.symbol();
            let sub_atom = Atom::var(sub_symbol);
            let transformed_px = subst_for_power(&pq__, x_, &n_, sub_symbol).rubi_rhs();
            let transformed_power = ((&m_ + Atom::num(1)) / &n_).expand();
            let transformed_integrand =
                sub_atom.pow(&transformed_power - Atom::num(1)) * transformed_px * (&a__ + &b__ * &sub_atom).pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, sub_symbol);

            rubi_star(Atom::num(1) / &n_, rubi_subst(&transformed, sub_symbol, x_.pow(&n_)))
        },
    ));
}

fn push_rules_rule_2362(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2362,
        source: "Int[(c_*x_)^m_.*Pq_*(a_+b_.*x_^n_)^p_.,x_Symbol] :=
          c^IntPart[m]*(c*x)^FracPart[m]/x^FracPart[m] \\[Star] Int[x^m*Pq*(a+b*x^n)^p,x] /;
        FreeQ[{a,b,c,m,n,p},x] && PolyQ[Pq,x^n] && IntegerQ[Simplify[(m+1)/n]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, m_, n_, p_, pq__, x_],
        optional: [m_, b__, p_],
        when: {
            let ratio = ((&m_ + Atom::num(1)) / &n_).expand();
            freeq!([a__, b__, c__, m_, n_, p_], x_)
                && rubi_poly_q_power(&pq__, x_, &n_)
                && integerq!(ratio)
        },
        rhs: {
            let frac_m = rubi_frac_part(&m_);
            let recursive_integrand = x_.pow(&m_) * &pq__ * (&a__ + &b__ * x_.pow(&n_)).pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(c__.pow(rubi_int_part(&m_)) * (&c__ * x_).pow(&frac_m) / x_.pow(frac_m), recursive)
        },
    ));
}

fn push_rules_rule_2363(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, n_, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2363,
        source: "Int[x_^m_.*Pq_*(a_+b_.*x_^n_)^p_,x_Symbol] :=
          Pq*(a+b*x^n)^(p+1)/(b*n*(p+1)) -
          1/(b*n*(p+1)) \\[Star] Int[D[Pq,x]*(a+b*x^n)^(p+1),x] /;
        FreeQ[{a,b,m,n},x] && PolyQ[Pq,x] && EqQ[m-n+1,0] && LtQ[p,-1]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, m_, n_, p_, pq__, x_],
        optional: [m_, b__],
        when: {
            freeq!([a__, b__, m_, n_], x_)
                && rubi_poly_q(&pq__, x_)
                && eqq!(&m_ - &n_ + Atom::num(1), 0)
                && ltq!(p_, -1)
        },
        rhs: {
            let raised_p = (&p_ + Atom::num(1)).expand();
            if b__.is_zero() || n_.is_zero() || raised_p.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let base = &a__ + &b__ * x_.pow(&n_);
            let denominator = &b__ * &n_ * &raised_p;
            let direct = &pq__ * base.pow(&raised_p) / &denominator;
            let recursive_integrand = rubi_d(&pq__, x_) * base.pow(raised_p);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) - rubi_star(Atom::num(1) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_2364(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, n_, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2364,
        source: "Int[x_^m_.*Pq_*(a_+b_.*x_^n_.)^p_,x_Symbol] :=
          Module[{u=IntHide[x^m*Pq,x]},
          u*(a+b*x^n)^p - b*n*p \\[Star] Int[x^(m+n)*(a+b*x^n)^(p-1)*ExpandToSum[u/x^(m+1),x],x]] /;
        FreeQ[{a,b},x] && PolyQ[Pq,x] && IGtQ[n,0] && GtQ[p,0] && LtQ[m+Expon[Pq,x]+1,0]",
        desc: "Integration by parts",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, m_, n_, p_, pq__, x_],
        optional: [m_, b__, n_],
        when: {
            freeq!([a__, b__], x_)
                && rubi_poly_q(&pq__, x_)
                && igtq!(n_, 0)
                && gtq!(p_, 0)
                && rubi_expon(&pq__, x_)
                    .is_some_and(|q| ltq!(&m_ + Atom::num(q + 1), 0))
        },
        rhs: {
            let u_integrand = x_.pow(&m_) * &pq__;
            let u = rubi_int_hide(&u_integrand, x_).rubi_rhs();
            let expand_to_sum =
                rubi_expand_to_sum(&(&u / x_.pow(&m_ + 1)), x_);
            let base = &a__ + &b__ * x_.pow(&n_);
            let direct = rubi_simp(&(&u * base.pow(&p_)), x_);
            let recursive_integrand = x_.pow(&m_ + &n_)
                * base.pow(&p_ - 1)
                * expand_to_sum;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_)
                    - rubi_star(&b__ * &n_ * &p_, recursive)
        },
    ));
}

fn push_rules_rule_2365(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2365,
        source: "Int[(c_.*x_)^m_.*Pq_*(a_+b_.*x_^n_.)^p_,x_Symbol] :=
          Module[{q=Expon[Pq,x],i},
          (c*x)^m*(a+b*x^n)^p*Sum[Coeff[Pq,x,i]*x^(i+1)/(m+n*p+i+1),{i,0,q}] +
          a*n*p \\[Star] Int[(c*x)^m*(a+b*x^n)^(p-1)*Sum[Coeff[Pq,x,i]*x^i/(m+n*p+i+1),{i,0,q}],x]] /;
        FreeQ[{a,b,c,m},x] && PolyQ[Pq,x] && IGtQ[(n-1)/2,0] && GtQ[p,0]",
        desc: "Binomial recurrence 1b applied qBold times",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, m_, n_, p_, pq__, x_],
        optional: [c__, m_, b__, n_],
        when: {
            freeq!([a__, b__, c__, m_], x_)
                && rubi_poly_q(&pq__, x_)
                && igtq!((&n_ - Atom::num(1)) / Atom::num(2), 0)
                && gtq!(p_, 0)
        },
        rhs: {
            let q = rubi_expon(&pq__, x_).rubi_rhs();
            let mut direct_sum = Atom::num(0);
            let mut recursive_sum = Atom::num(0);

            for i in 0..=q {
                let coefficient = rubi_coeff(&pq__, x_, i).rubi_rhs();
                let denominator = (&m_ + &n_ * &p_ + Atom::num(i + 1)).expand();
                if denominator.is_zero() {
                    panic!("Rubi RHS invariant was not established by the rule condition");
                }

                direct_sum += &coefficient * x_.pow(i + 1) / &denominator;
                recursive_sum += coefficient * x_.pow(i) / denominator;
            }

            let base = &a__ + &b__ * x_.pow(&n_);
            let direct = (&c__ * x_).pow(&m_) * base.pow(&p_) * direct_sum;
            let recursive_integrand =
                (&c__ * x_).pow(&m_) * base.pow((&p_ - Atom::num(1)).expand()) * recursive_sum;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) + rubi_star(&a__ * &n_ * &p_, recursive)
        },
    ));
}

fn push_rules_rule_2366(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, p4__, x_);
    let three_halves_3 = Atom::num(3) / Atom::num(2);
    rules.push(rubi_rule!(
        order: 2366,
        source: "Int[x_^2*P4_/(a_+b_.*x_^4)^(3/2),x_Symbol] :=
          With[{e=Coeff[P4,x,0],f=Coeff[P4,x,1],h=Coeff[P4,x,4]},
          -(f-2*h*x^3)/(2*b*Sqrt[a+b*x^4]) /;
         EqQ[b*e-3*a*h,0]] /;
        FreeQ[{a,b},x] && PolyQ[P4,x,4] && EqQ[Coeff[P4,x,2],0] && EqQ[Coeff[P4,x,3],0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: x_.pow(2) * p4__ / (a__ + b__ * x_.pow(4)).pow(&three_halves_3),
        with: [a__, b__, p4__, x_],
        optional: [b__],
        when: {
            let e = rubi_coeff(&p4__, x_, 0);
            let h = rubi_coeff(&p4__, x_, 4);
            freeq!([a__, b__], x_)
                && rubi_poly_q_degree(&p4__, x_, 4)
                && rubi_coeff(&p4__, x_, 2).is_some_and(|coefficient| eqq!(coefficient, 0))
                && rubi_coeff(&p4__, x_, 3).is_some_and(|coefficient| eqq!(coefficient, 0))
                && e.as_ref()
                    .zip(h.as_ref())
                    .is_some_and(|(e, h)| eqq!(&b__ * e - Atom::num(3) * &a__ * h, 0))
        },
        rhs: {
            let f = rubi_coeff(&p4__, x_, 1).rubi_rhs();
            let h = rubi_coeff(&p4__, x_, 4).rubi_rhs();

            let result = -(f - Atom::num(2) * h * x_.pow(3))
                / (Atom::num(2) * &b__ * (&a__ + &b__ * x_.pow(4)).sqrt());
            rubi_simp(&result, x_)
        },
    ));
}

fn push_rules_rule_2367(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, n_, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2367,
        source: "Int[x_^m_.*Pq_*(a_+b_.*x_^n_.)^p_,x_Symbol] :=
          With[{q=m+Expon[Pq,x]},
            Module[{Q=PolynomialQuotient[b^(Floor[(q-1)/n]+1)*x^m*Pq,a+b*x^n,x],
                    R=PolynomialRemainder[b^(Floor[(q-1)/n]+1)*x^m*Pq,a+b*x^n,x]},
            -x*R*(a+b*x^n)^(p+1)/(a*n*(p+1)*b^(Floor[(q-1)/n]+1)) +
            1/(a*n*(p+1)*b^(Floor[(q-1)/n]+1)) \\[Star] Int[(a+b*x^n)^(p+1)*ExpandToSum[a*n*(p+1)*Q+n*(p+1)*R+D[x*R,x],x],x]] /;
          GeQ[q,n]] /;
        FreeQ[{a,b},x] && PolyQ[Pq,x] && IGtQ[n,0] && LtQ[p,-1] && IGtQ[m,0]",
        desc: "Algebraic expansion and binomial recurrence 2b applied n-1Bold times",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, m_, n_, p_, pq__, x_],
        optional: [m_, b__, n_],
        when: {
            freeq!([a__, b__], x_)
                && rubi_poly_q(&pq__, x_)
                && igtq!(n_, 0)
                && ltq!(p_, -1)
                && igtq!(m_, 0)
                && rubi_expon(&pq__, x_).is_some_and(|degree| {
                    let q = &m_ + Atom::num(degree);
                    geq!(q, n_)
                })
        },
        rhs: {
            let m_i = integer_i64(&m_).rubi_rhs();
            let n_i = integer_i64(&n_).rubi_rhs();
            let q = m_i + rubi_expon(&pq__, x_).rubi_rhs();
            let raised_p = &p_ + 1;
            let floor_power = (q - 1).div_euclid(n_i) + 1;
            let scale = b__.pow(floor_power);
            let base = &a__ + &b__ * x_.pow(&n_);
            let numerator = &scale * x_.pow(m_i) * &pq__;
            let capital_q = rubi_polynomial_quotient(&numerator, &base, x_).rubi_rhs();
            let capital_r = rubi_polynomial_remainder(&numerator, &base, x_).rubi_rhs();
            let denominator = &a__ * &n_ * &raised_p * &scale;
            let direct = rubi_simp(
                &(Atom::num(-1) * x_ * &capital_r * base.pow(&raised_p) / &denominator),
                x_,
            );
            let expand_to_sum_payload = &a__ * &n_ * &raised_p * &capital_q
                + &n_ * &raised_p * &capital_r
                + rubi_d(&(x_ * &capital_r), x_);
            let expand_to_sum = rubi_expand_to_sum(&expand_to_sum_payload, x_);
            let recursive_integrand = base.pow(raised_p) * expand_to_sum;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            direct
                    + rubi_star(Atom::num(1) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_2368(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, n_, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2368,
        source: "Int[x_^m_*Pq_*(a_+b_.*x_^n_.)^p_,x_Symbol] :=
          With[{q=Expon[Pq,x]},
          Module[{Q=PolynomialQuotient[a*b^(Floor[(q-1)/n]+1)*x^m*Pq,a+b*x^n,x],
                  R=PolynomialRemainder[a*b^(Floor[(q-1)/n]+1)*x^m*Pq,a+b*x^n,x],i},
            -x*R*(a+b*x^n)^(p+1)/(a^2*n*(p+1)*b^(Floor[(q-1)/n]+1)) +
            1/(a*n*(p+1)*b^(Floor[(q-1)/n]+1)) \\[Star] Int[x^m*(a+b*x^n)^(p+1)*
              ExpandToSum[n*(p+1)*x^(-m)*Q+Sum[(n*(p+1)+i+1)/a*Coeff[R,x,i]*x^(i-m),{i,0,n-1}],x],x]]] /;
        FreeQ[{a,b},x] && PolyQ[Pq,x] && IGtQ[n,0] && LtQ[p,-1] && ILtQ[m,0]",
        desc: "Algebraic expansion and binomial recurrence 2b applied n-1Bold times",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, m_, n_, p_, pq__, x_],
        optional: [b__, n_],
        when: {
            freeq!([a__, b__], x_)
                && rubi_poly_q(&pq__, x_)
                && igtq!(n_, 0)
                && ltq!(p_, -1)
                && iltq!(m_, 0)
        },
        rhs: {
            let m_i = integer_i64(&m_).rubi_rhs();
            let n_i = integer_i64(&n_).rubi_rhs();
            let q = rubi_expon(&pq__, x_).rubi_rhs();
            let raised_p = (&p_ + Atom::num(1)).expand();
            let floor_power = (q - 1).div_euclid(n_i) + 1;
            let scale = b__.pow(floor_power);
            if a__.is_zero() || b__.is_zero() || n_i == 0 || raised_p.is_zero() || scale.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let base = &a__ + &b__ * x_.pow(&n_);
            let numerator = &a__ * &scale * x_.pow(m_i) * &pq__;
            let (capital_q, capital_r) = laurent_quotient_remainder_by_polynomial(&numerator, &base, x_).rubi_rhs();
            let denominator_direct = a__.pow(2) * &n_ * &raised_p * &scale;
            let denominator_recursive = &a__ * &n_ * &raised_p * &scale;
            let direct = Atom::num(-1) * x_ * &capital_r * base.pow(&raised_p) / denominator_direct;

            let mut coefficient_sum = Atom::num(0);
            let r_terms = collect_laurent_terms(&capital_r, x_).rubi_rhs();
            if r_terms.keys().any(|degree| *degree < 0) {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }
            for i in 0..n_i {
                let coefficient = r_terms.get(&i).cloned().unwrap_or_else(|| Atom::num(0));
                coefficient_sum += (&n_ * &raised_p + Atom::num(i + 1)) * coefficient * x_.pow(i - m_i) / &a__;
            }

            let expand_to_sum_payload =
                &n_ * &raised_p * x_.pow(-m_i) * capital_q + coefficient_sum;
            let expand_to_sum = rubi_expand_to_sum(&expand_to_sum_payload, x_);
            let recursive_integrand = x_.pow(&m_) * base.pow(raised_p) * expand_to_sum;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            direct + rubi_star(Atom::num(1) / denominator_recursive, recursive)
        },
    ));
}

fn push_rules_rule_2369(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, n_, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2369,
        source: "Int[x_^m_.*Pq_*(a_+b_.*x_^n_)^p_,x_Symbol] :=
          With[{g=GCD[m+1,n]},
          1/g \\[Star] Subst[Int[x^((m+1)/g-1)*ReplaceAll[Pq,x->x^(1/g)]*(a+b*x^(n/g))^p,x],x,x^g] /;
         g!=1] /;
        FreeQ[{a,b,p},x] && PolyQ[Pq,x^n] && IGtQ[n,0] && IntegerQ[m]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, m_, n_, p_, pq__, x_],
        optional: [m_, b__],
        when: {
            freeq!([a__, b__, p_], x_)
                && rubi_poly_q_power(&pq__, x_, &n_)
                && igtq!(n_, 0)
                && integerq!(m_)
                && rubi_gcd(&(&m_ + 1), &n_).is_some_and(|g| g != 1)
        },
        rhs: {
            let g = rubi_gcd(&(&m_ + 1), &n_).rubi_rhs();
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub_symbol = sub_guard.symbol();
            let sub_atom = Atom::var(sub_symbol);
            let transformed_px =
                rubi_replace_all(&pq__, x_, sub_atom.pow(Atom::num(1) / Atom::num(g)));
            let transformed_integrand = sub_atom.pow((&m_ + 1) / g - 1)
                * transformed_px
                * (&a__ + &b__ * sub_atom.pow(&n_ / g)).pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, sub_symbol);
            let substituted = rubi_subst(&transformed, sub_symbol, x_.pow(g));

            rubi_star(Atom::num(1) / Atom::num(g), substituted)
        },
    ));
}

fn push_rules_rule_2370(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2370,
        source: "Int[(c_.*x_)^m_.*Pq_/(a_+b_.*x_^n_),x_Symbol] :=
          With[{v=Sum[(c*x)^(m+ii)*(Coeff[Pq,x,ii]+Coeff[Pq,x,n/2+ii]*x^(n/2))/(c^ii*(a+b*x^n)),{ii,0,n/2-1}]},
          Int[v,x] /;
         SumQ[v]] /;
        FreeQ[{a,b,c,m},x] && PolyQ[Pq,x] && IGtQ[n/2,0] && Expon[Pq,x]<n",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, m_, n_, pq__, x_],
        optional: [c__, m_, b__],
        when: {
            let v = (|| {
                let half_n = integer_i64(&(&n_ / Atom::num(2)))?;
                let denominator = &a__ + &b__ * x_.pow(&n_);
                let mut v = Atom::num(0);
                for ii in 0..half_n {
                    let lower = rubi_coeff(&pq__, x_, ii)?;
                    let upper = rubi_coeff(&pq__, x_, half_n + ii)?;
                    v += (&c__ * x_).pow(&m_ + Atom::num(ii))
                        * (lower + upper * x_.pow(half_n))
                        / (c__.pow(ii) * &denominator);
                }
                Some(v)
            })();
            freeq!([a__, b__, c__, m_], x_)
                && rubi_poly_q(&pq__, x_)
                && igtq!(&n_ / Atom::num(2), 0)
                && rubi_expon(&pq__, x_)
                    .is_some_and(|q| ltq!(Atom::num(q), n_))
                && v.is_some_and(|v| rubi_sum_q(&v))
        },
        rhs: {
            let half_n = integer_i64(&(&n_ / Atom::num(2))).rubi_rhs();
            let denominator = &a__ + &b__ * x_.pow(&n_);
            let mut v = Atom::num(0);
            for ii in 0..half_n {
                let lower = rubi_coeff(&pq__, x_, ii).rubi_rhs();
                let upper = rubi_coeff(&pq__, x_, half_n + ii).rubi_rhs();
                v += (&c__ * x_).pow((&m_ + Atom::num(ii)).expand())
                    * (lower + upper * x_.pow(half_n))
                    / (c__.pow(ii) * &denominator);
            }

            rubi_rhs_int(&v, x_)
        },
    ));
}

fn push_rules_rule_2372(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2372,
        source: "Int[(c_.*x_)^m_.*Pq_*(a_+b_.*x_^n_)^p_,x_Symbol] :=
          Module[{q=Expon[Pq,x],j,k},
          Int[Sum[(c*x)^(m+j)/c^j*Sum[Coeff[Pq,x,j+k*n/2]*x^(k*n/2),{k,0,2*(q-j)/n+1}]*(a+b*x^n)^p,{j,0,n/2-1}],x]] /;
        FreeQ[{a,b,c,m,p},x] && PolyQ[Pq,x] && IGtQ[n/2,0] && Not[PolyQ[Pq,x^(n/2)]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, m_, n_, p_, pq__, x_],
        optional: [c__, m_, b__],
        when: {
            let half_n = integer_i64(&(&n_ / Atom::num(2)));
            freeq!([a__, b__, c__, m_, p_], x_)
                && rubi_poly_q(&pq__, x_)
                && igtq!(&n_ / Atom::num(2), 0)
                && half_n.is_some_and(|half_n| !rubi_poly_q_power(&pq__, x_, &Atom::num(half_n)))
        },
        rhs: {
            let q = rubi_expon(&pq__, x_).rubi_rhs();
            let half_n = integer_i64(&(&n_ / Atom::num(2))).rubi_rhs();

            let base = &a__ + &b__ * x_.pow(&n_);
            let mut transformed = Atom::num(0);
            for j in 0..half_n {
                let mut inner = Atom::num(0);
                let mut degree = j;
                while degree <= q + half_n {
                    let coefficient = rubi_coeff(&pq__, x_, degree).rubi_rhs();
                    if !coefficient.is_zero() {
                        inner += coefficient * x_.pow(degree - j);
                    }
                    degree += half_n;
                }
                if !inner.is_zero() {
                    transformed += (&c__ * x_).pow((&m_ + Atom::num(j)).expand()) * inner * base.pow(&p_) / c__.pow(j);
                }
            }

            rubi_rhs_int(&transformed, x_)
        },
    ));
}

fn push_rules_rule_2373(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2373,
        source: "Int[(c_.*x_)^m_.*Pq_/(a_+b_.*x_^n_),x_Symbol] :=
          Int[ExpandIntegrand[(c*x)^m*Pq/(a+b*x^n),x],x] /;
        FreeQ[{a,b,c,m},x] && PolyQ[Pq,x] && IntegerQ[n] && Not[IGtQ[m,0]]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, m_, n_, pq__, x_],
        optional: [c__, m_, b__],
        when: {
            freeq!([a__, b__, c__, m_], x_)
                && rubi_poly_q(&pq__, x_)
                && integerq!(n_)
                && !igtq!(m_, 0)
        },
        rhs: {
            let integrand = (&c__ * x_).pow(&m_) * &pq__ / (&a__ + &b__ * x_.pow(&n_));
            let expanded = rubi_expand_integrand(&integrand, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_2374(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2374,
        source: "Int[(c_.*x_)^m_*Pq_*(a_+b_.*x_^n_)^p_,x_Symbol] :=
          With[{Pq0=Coeff[Pq,x,0]},
            Pq0*(c*x)^(m+1)*(a+b*x^n)^(p+1)/(a*c*(m+1)) +
            1/(2*a*c*(m+1)) \\[Star] Int[(c*x)^(m+1)*ExpandToSum[2*a*(m+1)*(Pq-Pq0)/x-2*b*Pq0*(m+n*(p+1)+1)*x^(n-1),x]*(a+b*x^n)^p,x] /;
         NeQ[Pq0,0]] /;
        FreeQ[{a,b,c,p},x] && PolyQ[Pq,x] && IGtQ[n,0] && LtQ[m,-1] && LeQ[n-1,Expon[Pq,x]]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, m_, n_, p_, pq__, x_],
        optional: [c__, b__],
        when: {
            let q = rubi_expon(&pq__, x_);
            freeq!([a__, b__, c__, p_], x_)
                && rubi_poly_q(&pq__, x_)
                && igtq!(n_, 0)
                && ltq!(m_, -1)
                && q.is_some_and(|q| leq!((&n_ - Atom::num(1)).expand(), Atom::num(q)))
                && rubi_coeff(&pq__, x_, 0)
                    .is_some_and(|pq0| neq!(pq0, 0))
        },
        rhs: {
            let pq0 = rubi_coeff(&pq__, x_, 0).rubi_rhs();
            let raised_m = &m_ + 1;
            let raised_p = &p_ + 1;
            let base = &a__ + &b__ * x_.pow(&n_);
            let direct = rubi_simp(
                &(&pq0
                    * (&c__ * x_).pow(&raised_m)
                    * base.pow(&raised_p)
                    / (&a__ * &c__ * &raised_m)),
                x_,
            );
            let expand_to_sum_payload = Atom::num(2) * &a__ * &raised_m * (&pq__ - &pq0) / x_
                - Atom::num(2)
                    * &b__
                    * &pq0
                    * (&m_ + &n_ * (&p_ + 1) + 1)
                    * x_.pow(&n_ - 1);
            let expand_to_sum = rubi_expand_to_sum(&expand_to_sum_payload, x_);
            let recursive_integrand =
                (&c__ * x_).pow(raised_m) * expand_to_sum * base.pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_)
                    + rubi_star(Atom::num(1)
                            / (Atom::num(2) * &a__ * &c__ * (&m_ + 1)), recursive)
        },
    ));
}

fn push_rules_rule_2375(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2375,
        source: "Int[(c_.*x_)^m_.*Pq_*(a_+b_.*x_^n_)^p_,x_Symbol] :=
          With[{q=Expon[Pq,x]},
            With[{Pqq=Coeff[Pq,x,q]},
            Pqq*(c*x)^(m+q-n+1)*(a+b*x^n)^(p+1)/(b*c^(q-n+1)*(m+q+n*p+1)) +
            1/(b*(m+q+n*p+1)) \\[Star] Int[(c*x)^m*ExpandToSum[b*(m+q+n*p+1)*(Pq-Pqq*x^q)-a*Pqq*(m+q-n+1)*x^(q-n),x]*(a+b*x^n)^p,x]] /;
          NeQ[m+q+n*p+1,0] && q-n>=0 && (IntegerQ[2*p] || IntegerQ[p+(q+1)/(2*n)])] /;
        FreeQ[{a,b,c,m,p},x] && PolyQ[Pq,x] && IGtQ[n,0]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: ["G&R 2.110.5, CRC 88a", "G&R 2.104"],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, m_, n_, p_, pq__, x_],
        optional: [c__, m_, b__],
        when: {
            let q = rubi_expon(&pq__, x_);
            freeq!([a__, b__, c__, m_, p_], x_)
                && rubi_poly_q(&pq__, x_)
                && igtq!(n_, 0)
                && q.is_some_and(|q| {
                    let denominator = (&m_ + Atom::num(q) + &n_ * &p_ + Atom::num(1)).expand();
                    neq!(denominator, 0)
                        && geq!((Atom::num(q) - &n_).expand(), 0)
                        && (integerq!((Atom::num(2) * &p_).expand())
                            || integerq!(
                                (&p_ + Atom::num(q + 1) / (Atom::num(2) * &n_)).expand()
                            ))
                })
        },
        rhs: {
            let q = rubi_expon(&pq__, x_).rubi_rhs();
            let pqq = rubi_coeff(&pq__, x_, q).rubi_rhs();
            let denominator = &m_ + Atom::num(q) + &n_ * &p_ + 1;
            let q_minus_n = Atom::num(q) - &n_;
            let lowered_q = &q_minus_n + 1;
            let recurrence_factor = &m_ + &lowered_q;
            let base = &a__ + &b__ * x_.pow(&n_);
            let direct = rubi_simp(
                &(&pqq
                    * (&c__ * x_).pow(&recurrence_factor)
                    * base.pow(&p_ + 1)
                    / (&b__ * c__.pow(&lowered_q) * &denominator)),
                x_,
            );
            let expand_to_sum_payload = &b__
                * &denominator
                * (&pq__ - &pqq * x_.pow(q))
                - &a__ * &pqq * recurrence_factor * x_.pow(q_minus_n);
            let expand_to_sum = rubi_expand_to_sum(&expand_to_sum_payload, x_);
            let recursive_integrand =
                (&c__ * x_).pow(&m_) * expand_to_sum * base.pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            direct
                    + rubi_star(Atom::num(1) / (&b__ * denominator), recursive)
        },
    ));
}

fn push_rules_rule_2376(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, n_, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2376,
        source: "Int[x_^m_.*Pq_*(a_+b_.*x_^n_)^p_,x_Symbol] :=
          With[{q=Expon[Pq,x]},
          -Subst[Int[ExpandToSum[x^q*ReplaceAll[Pq,x->x^(-1)],x]*(a+b*x^(-n))^p/x^(m+q+2),x],x,1/x]] /;
        FreeQ[{a,b,p},x] && PolyQ[Pq,x] && ILtQ[n,0] && IntegerQ[m]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, m_, n_, p_, pq__, x_],
        optional: [m_, b__],
        when: {
            freeq!([a__, b__, p_], x_)
                && rubi_poly_q(&pq__, x_)
                && iltq!(n_, 0)
                && integerq!(m_)
        },
        rhs: {
            let q = rubi_expon(&pq__, x_).rubi_rhs();
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let replacement = sub_atom.pow(-1);
            let expand_to_sum =
                rubi_expand_to_sum(&(sub_atom.pow(q) * rubi_replace_all(&pq__, x_, replacement)), sub);
            let transformed_integrand =
                expand_to_sum * (&a__ + &b__ * sub_atom.pow(-&n_)).pow(&p_)
                    / sub_atom.pow((&m_ + Atom::num(q + 2)).expand());
            let transformed = rubi_rhs_int(&transformed_integrand, sub);

            -rubi_subst(&transformed, sub, Atom::num(1) / x_)
        },
    ));
}

fn push_rules_rule_2377(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2377,
        source: "Int[(c_.*x_)^m_.*Pq_*(a_+b_.*x_^n_)^p_,x_Symbol] :=
          With[{g=Denominator[m],q=Expon[Pq,x]},
          -g/c \\[Star] Subst[Int[ExpandToSum[x^(g*q)*ReplaceAll[Pq,x->c^(-1)*x^(-g)],x]*
            (a+b*c^(-n)*x^(-g*n))^p/x^(g*(m+q+1)+1),x],x,1/(c*x)^(1/g)]] /;
        FreeQ[{a,b,c,p},x] && PolyQ[Pq,x] && ILtQ[n,0] && FractionQ[m]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, m_, n_, p_, pq__, x_],
        optional: [c__, m_, b__],
        when: {
            freeq!([a__, b__, c__, p_], x_)
                && rubi_poly_q(&pq__, x_)
                && iltq!(n_, 0)
                && fractionq!(m_)
        },
        rhs: {
            let g_i = rubi_denominator(&m_).rubi_rhs();
            if c__.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let g = Atom::num(g_i);
            let q = rubi_expon(&pq__, x_).rubi_rhs();
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let expand_to_sum_payload =
                sub_atom.pow(g_i * q) * rubi_replace_all(&pq__, x_, c__.pow(-1) * sub_atom.pow(-g_i));
            let expand_to_sum = rubi_expand_to_sum(&expand_to_sum_payload, sub);
            let transformed_integrand = expand_to_sum
                * (&a__ + &b__ * c__.pow(-&n_) * sub_atom.pow((-&g * &n_).expand())).pow(&p_)
                / sub_atom.pow((&g * (&m_ + Atom::num(q + 1)) + Atom::num(1)).expand());
            let transformed = rubi_rhs_int(&transformed_integrand, sub);
            let replacement = Atom::num(1) / (&c__ * x_).pow(Atom::num(1) / &g);

            rubi_star(-g, rubi_subst(&transformed, sub, replacement) / c__)
        },
    ));
}

fn push_rules_rule_2378(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2378,
        source: "Int[(c_.*x_)^m_*Pq_*(a_+b_.*x_^n_)^p_,x_Symbol] :=
          With[{q=Expon[Pq,x]},
          -(c*x)^m*(x^(-1))^m \\[Star] Subst[Int[ExpandToSum[x^q*ReplaceAll[Pq,x->x^(-1)],x]*(a+b*x^(-n))^p/x^(m+q+2),x],x,1/x]] /;
        FreeQ[{a,b,c,m,p},x] && PolyQ[Pq,x] && ILtQ[n,0] && Not[RationalQ[m]]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, m_, n_, p_, pq__, x_],
        optional: [c__, b__],
        when: {
            freeq!([a__, b__, c__, m_, p_], x_)
                && rubi_poly_q(&pq__, x_)
                && iltq!(n_, 0)
                && !rationalq!(m_)
        },
        rhs: {
            let q = rubi_expon(&pq__, x_).rubi_rhs();
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let replacement = sub_atom.pow(-1);
            let expand_to_sum =
                rubi_expand_to_sum(&(sub_atom.pow(q) * rubi_replace_all(&pq__, x_, replacement)), sub);
            let transformed_integrand =
                expand_to_sum * (&a__ + &b__ * sub_atom.pow(-&n_)).pow(&p_)
                    / sub_atom.pow((&m_ + Atom::num(q + 2)).expand());
            let transformed = rubi_rhs_int(&transformed_integrand, sub);

            rubi_star(-(&c__ * x_).pow(&m_) * x_.pow(-1).pow(&m_), rubi_subst(&transformed, sub, Atom::num(1) / x_))
        },
    ));
}

fn push_rules_rule_2379(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, n_, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2379,
        source: "Int[x_^m_.*Pq_*(a_+b_.*x_^n_)^p_,x_Symbol] :=
          With[{g=Denominator[n]},
          g \\[Star] Subst[Int[x^(g*(m+1)-1)*ReplaceAll[Pq,x->x^g]*(a+b*x^(g*n))^p,x],x,x^(1/g)]] /;
        FreeQ[{a,b,m,p},x] && PolyQ[Pq,x] && FractionQ[n]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, m_, n_, p_, pq__, x_],
        optional: [m_, b__],
        when: {
            freeq!([a__, b__, m_, p_], x_)
                && rubi_poly_q(&pq__, x_)
                && fractionq!(n_)
        },
        rhs: {
            let g_i = rubi_denominator(&n_).rubi_rhs();
            let g = Atom::num(g_i);
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_px = rubi_replace_all(&pq__, x_, sub_atom.pow(g_i));
            let transformed_integrand = sub_atom.pow((&g * (&m_ + Atom::num(1)) - Atom::num(1)).expand())
                * transformed_px
                * (&a__ + &b__ * sub_atom.pow((&g * &n_).expand())).pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);

            rubi_star(g, rubi_subst(&transformed, sub, x_.pow(Atom::num(1) / g_i)))
        },
    ));
}

fn push_rules_rule_2380(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2380,
        source: "Int[(c_*x_)^m_*Pq_*(a_+b_.*x_^n_)^p_,x_Symbol] :=
          c^IntPart[m]*(c*x)^FracPart[m]/x^FracPart[m] \\[Star] Int[x^m*Pq*(a+b*x^n)^p,x] /;
        FreeQ[{a,b,c,m,p},x] && PolyQ[Pq,x] && FractionQ[n]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, m_, n_, p_, pq__, x_],
        optional: [b__],
        when: {
            freeq!([a__, b__, c__, m_, p_], x_)
                && rubi_poly_q(&pq__, x_)
                && fractionq!(n_)
        },
        rhs: {
            let frac_m = rubi_frac_part(&m_);
            let recursive_integrand = x_.pow(&m_) * &pq__ * (&a__ + &b__ * x_.pow(&n_)).pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(c__.pow(rubi_int_part(&m_)) * (&c__ * x_).pow(&frac_m) / x_.pow(frac_m), recursive)
        },
    ));
}

fn push_rules_rule_2381(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, n_, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2381,
        source: "Int[x_^m_.*Pq_*(a_+b_.*x_^n_)^p_,x_Symbol] :=
          1/(m+1) \\[Star] Subst[Int[ReplaceAll[SubstFor[x^n,Pq,x],x->x^Simplify[n/(m+1)]]*(a+b*x^Simplify[n/(m+1)])^p,x],x,x^(m+1)] /;
        FreeQ[{a,b,m,n,p},x] && PolyQ[Pq,x^n] && IntegerQ[Simplify[n/(m+1)]] && Not[IntegerQ[n]]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, m_, n_, p_, pq__, x_],
        optional: [m_, b__],
        when: {
            let m1 = &m_ + Atom::num(1);
            freeq!([a__, b__, m_, n_, p_], x_)
                && rubi_poly_q_power(&pq__, x_, &n_)
                && integerq!(rubi_simplify(&(&n_ / &m1)))
                && !integerq!(n_)
        },
        rhs: {
            let m1 = &m_ + Atom::num(1);
            let ratio = rubi_simplify(&(&n_ / &m1));
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let subst_for = rubi_subst_for(&pq__, x_.pow(&n_), sub);
            let transformed_px = rubi_replace_all(&subst_for, sub, sub_atom.pow(&ratio));
            let transformed_integrand = transformed_px * (&a__ + &b__ * sub_atom.pow(&ratio)).pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);
            let substituted = rubi_subst(&transformed, sub, x_.pow(&m1));

            rubi_star(Atom::num(1) / m1, substituted)
        },
    ));
}

fn push_rules_rule_2382(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2382,
        source: "Int[(c_*x_)^m_*Pq_*(a_+b_.*x_^n_)^p_,x_Symbol] :=
          c^IntPart[m]*(c*x)^FracPart[m]/x^FracPart[m] \\[Star] Int[x^m*Pq*(a+b*x^n)^p,x] /;
        FreeQ[{a,b,c,m,n,p},x] && PolyQ[Pq,x^n] && IntegerQ[Simplify[n/(m+1)]] && Not[IntegerQ[n]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, m_, n_, p_, pq__, x_],
        optional: [b__],
        when: {
            let m1 = &m_ + Atom::num(1);
            freeq!([a__, b__, c__, m_, n_, p_], x_)
                && rubi_poly_q_power(&pq__, x_, &n_)
                && integerq!(rubi_simplify(&(&n_ / &m1)))
                && !integerq!(n_)
        },
        rhs: {
            let frac_m = rubi_frac_part(&m_);
            let recursive_integrand = x_.pow(&m_) * &pq__ * (&a__ + &b__ * x_.pow(&n_)).pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let result = c__.pow(rubi_int_part(&m_)) * (&c__ * x_).pow(&frac_m) * recursive / x_.pow(frac_m);

            rubi_star(Atom::num(1), result)
        },
    ));
}

fn push_rules_rule_2383(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2383,
        source: "Int[(c_.*x_)^m_.*Pq_*(a_+b_.*x_^n_)^p_.,x_Symbol] :=
          Int[ExpandIntegrand[(c*x)^m*Pq*(a+b*x^n)^p,x],x] /;
        FreeQ[{a,b,c,m,n,p},x] && (PolyQ[Pq,x] || PolyQ[Pq,x^n]) && Not[IGtQ[m,0]]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, m_, n_, p_, pq__, x_],
        optional: [c__, m_, b__, p_],
        when: {
            freeq!([a__, b__, c__, m_, n_, p_], x_)
                && (rubi_poly_q(&pq__, x_) || rubi_poly_q_power(&pq__, x_, &n_))
                && !igtq!(m_, 0)
        },
        rhs: {
            let integrand = (&c__ * x_).pow(&m_) * &pq__ * (&a__ + &b__ * x_.pow(&n_)).pow(&p_);
            let expanded = rubi_expand_integrand(&integrand, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_2384(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, m_, n_, p_, pq__, u_, v_);
    rules.push(rubi_rule!(
        order: 2384,
        source: "Int[u_^m_.*Pq_*(a_+b_.*v_^n_.)^p_,x_Symbol] :=
          u^m/(Coeff[v,x,1]*v^m) \\[Star] Subst[Int[x^m*SubstFor[v,Pq,x]*(a+b*x^n)^p,x],x,v] /;
        FreeQ[{a,b,m,n,p},x] && LinearPairQ[u,v,x] && PolyQ[Pq,v^n]",
        desc: "Integration by substitution and piecewise constant extraction",
        refs: [],
        pattern: u_.pow(m_) * pq__ * (a__ + b__ * v_.pow(n_)).pow(p_),
        with: [u_, a__, b__, v_, m_, n_, p_, pq__, x_],
        optional: [m_, b__, n_],
        x_dep: [u_, v_],
        x_free: [a__, b__, m_, n_, p_],
        x_linear: [u_, v_],
        when: {
            freeq!([a__, b__, m_, n_, p_], x_)
                && rubi_linear_pair_q(&u_, &v_, x_)
                && rubi_poly_q_power_of(&pq__, &v_, &n_, x_)
        },
        rhs: {
            let (_v0, v1) = linear_coefficients(&v_, x_).rubi_rhs();
            let denominator = &v1 * v_.pow(&m_);
            if denominator.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let subst_for = rubi_subst_for(&pq__, &v_, sub);
            let transformed_integrand =
                sub_atom.pow(&m_) * subst_for * (&a__ + &b__ * sub_atom.pow(&n_)).pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);

            rubi_star(u_.pow(&m_), rubi_subst(&transformed, sub, &v_) / denominator)
        },
    ));
}

fn push_rules_rule_2385(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a1__, a2__, b1__, b2__, c__, m_, n_, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2385,
        source: "Int[(c_.*x_)^m_.*Pq_*(a1_+b1_.*x_^n_.)^p_.*(a2_+b2_.*x_^n_.)^p_.,x_Symbol] :=
          Int[(c*x)^m*Pq*(a1*a2+b1*b2*x^(2*n))^p,x] /;
        FreeQ[{a1,b1,a2,b2,c,m,n,p},x] && PolyQ[Pq,x] && EqQ[a2*b1+a1*b2,0] && (IntegerQ[p] || GtQ[a1,0] && GtQ[a2,0])",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a1__, b1__, a2__, b2__, c__, m_, n_, p_, pq__, x_],
        optional: [c__, m_, b1__, b2__, n_, p_],
        when: {
            freeq!([a1__, b1__, a2__, b2__, c__, m_, n_, p_], x_)
                && rubi_poly_q(&pq__, x_)
                && eqq!(&a2__ * &b1__ + &a1__ * &b2__, 0)
                && (integerq!(p_) || gtq!(a1__, 0) && gtq!(a2__, 0))
        },
        rhs: {
            let transformed_integrand = (&c__ * x_).pow(&m_)
                * &pq__
                * (&a1__ * &a2__ + &b1__ * &b2__ * x_.pow(Atom::num(2) * &n_)).pow(&p_);

            rubi_rhs_int(&transformed_integrand, x_)
        },
    ));
}

fn push_rules_rule_2386(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a1__, a2__, b1__, b2__, c__, m_, n_, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2386,
        source: "Int[(c_.*x_)^m_.*Pq_*(a1_+b1_.*x_^n_.)^p_.*(a2_+b2_.*x_^n_.)^p_.,x_Symbol] :=
          (a1+b1*x^n)^FracPart[p]*(a2+b2*x^n)^FracPart[p]/(a1*a2+b1*b2*x^(2*n))^FracPart[p] \\[Star]
            Int[(c*x)^m*Pq*(a1*a2+b1*b2*x^(2*n))^p,x] /;
        FreeQ[{a1,b1,a2,b2,c,m,n,p},x] && PolyQ[Pq,x] && EqQ[a2*b1+a1*b2,0] && Not[EqQ[n,1] && LinearQ[Pq,x]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a1__, b1__, a2__, b2__, c__, m_, n_, p_, pq__, x_],
        optional: [c__, m_, b1__, b2__, n_, p_],
        when: {
            freeq!([a1__, b1__, a2__, b2__, c__, m_, n_, p_], x_)
                && rubi_poly_q(&pq__, x_)
                && eqq!(&a2__ * &b1__ + &a1__ * &b2__, 0)
                && !(eqq!(n_, 1) && rubi_linear_q(&pq__, x_))
        },
        rhs: {
            let frac_part = rubi_frac_part(&p_);
            let first = &a1__ + &b1__ * x_.pow(&n_);
            let second = &a2__ + &b2__ * x_.pow(&n_);
            let combined = &a1__ * &a2__ + &b1__ * &b2__ * x_.pow(Atom::num(2) * &n_);
            let recursive = rubi_rhs_int(&((&c__ * x_).pow(&m_) * &pq__ * combined.pow(&p_)), x_);

            rubi_star(first.pow(&frac_part) * second.pow(&frac_part) / combined.pow(frac_part), recursive)
        },
    ));
}

fn push_rules_rule_2387(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, h__, m_, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 2387,
        source: "Int[(h_.*x_)^m_.*(e_+f_.*x_^n_.+g_.*x_^n2_.)*(a_+b_.*x_^n_.)^p_.*(c_+d_.*x_^n_.)^p_.,x_Symbol] :=
          e*(h*x)^(m+1)*(a+b*x^n)^(p+1)*(c+d*x^n)^(p+1)/(a*c*h*(m+1)) /;
        FreeQ[{a,b,c,d,e,f,g,h,m,n,p},x] && EqQ[n2,2*n] && EqQ[a*c*f*(m+1)-e*(b*c+a*d)*(m+n*(p+1)+1),0] &&
          EqQ[a*c*g*(m+1)-b*d*e*(m+2*n*(p+1)+1),0] && NeQ[m,-1]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: (h__ * x_).pow(m_)
            * (e__ + f__ * x_.pow(n_) + g__ * x_.pow(n2_))
            * (a__ + b__ * x_.pow(n_)).pow(p_)
            * (c__ + d__ * x_.pow(n_)).pow(p_),
        with: [a__, b__, c__, d__, e__, f__, g__, h__, m_, n_, n2_, p_, x_],
        optional: [h__, m_, f__, g__, b__, d__, n_, n2_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, h__, m_, n_, p_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && eqq!(
                    &a__ * &c__ * &f__ * (&m_ + Atom::num(1))
                        - &e__ * (&b__ * &c__ + &a__ * &d__) * (&m_ + &n_ * (&p_ + Atom::num(1)) + Atom::num(1)),
                    0
                )
                && eqq!(
                    &a__ * &c__ * &g__ * (&m_ + Atom::num(1))
                        - &b__ * &d__ * &e__ * (&m_ + Atom::num(2) * &n_ * (&p_ + Atom::num(1)) + Atom::num(1)),
                    0
                )
                && neq!(m_, -Atom::num(1))
        },
        rhs: {
            let denominator = &a__ * &c__ * &h__ * (&m_ + Atom::num(1));
            if denominator.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            rubi_simp(&(&e__ * (&h__ * x_).pow(&m_ + Atom::num(1))
                    * (&a__ + &b__ * x_.pow(&n_)).pow(&p_ + Atom::num(1))
                    * (&c__ + &d__ * x_.pow(&n_)).pow(&p_ + Atom::num(1))
                    / denominator), x_)
        },
    ));
}

fn push_rules_rule_2388(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, g__, h__, m_, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 2388,
        source: "Int[(h_.*x_)^m_.*(e_+g_.*x_^n2_.)*(a_+b_.*x_^n_.)^p_.*(c_+d_.*x_^n_.)^p_.,x_Symbol] :=
          e*(h*x)^(m+1)*(a+b*x^n)^(p+1)*(c+d*x^n)^(p+1)/(a*c*h*(m+1)) /;
        FreeQ[{a,b,c,d,e,g,h,m,n,p},x] && EqQ[n2,2*n] && EqQ[m+n*(p+1)+1,0] && EqQ[a*c*g*(m+1)-b*d*e*(m+2*n*(p+1)+1),0] &&
          NeQ[m,-1]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: (h__ * x_).pow(m_)
            * (e__ + g__ * x_.pow(n2_))
            * (a__ + b__ * x_.pow(n_)).pow(p_)
            * (c__ + d__ * x_.pow(n_)).pow(p_),
        with: [a__, b__, c__, d__, e__, g__, h__, m_, n_, n2_, p_, x_],
        optional: [h__, m_, g__, b__, d__, n_, n2_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, g__, h__, m_, n_, p_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && eqq!(&m_ + &n_ * (&p_ + Atom::num(1)) + Atom::num(1), 0)
                && eqq!(
                    &a__ * &c__ * &g__ * (&m_ + Atom::num(1))
                        - &b__ * &d__ * &e__ * (&m_ + Atom::num(2) * &n_ * (&p_ + Atom::num(1)) + Atom::num(1)),
                    0
                )
                && neq!(m_, -Atom::num(1))
        },
        rhs: {
            let denominator = &a__ * &c__ * &h__ * (&m_ + Atom::num(1));
            if denominator.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            rubi_simp(&(&e__ * (&h__ * x_).pow(&m_ + Atom::num(1))
                    * (&a__ + &b__ * x_.pow(&n_)).pow(&p_ + Atom::num(1))
                    * (&c__ + &d__ * x_.pow(&n_)).pow(&p_ + Atom::num(1))
                    / denominator), x_)
        },
    ));
}

// Generated shared pattern builders.

#[inline(never)]
fn rubi_shared_pattern_0(symbols: &RubiSymbols) -> Atom {
    let a1__ = symbols.a1__;
    let a2__ = symbols.a2__;
    let b1__ = symbols.b1__;
    let b2__ = symbols.b2__;
    let c__ = symbols.c__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let pq__ = symbols.pq__;
    let x_ = symbols.x_;
    (c__ * x_).pow(m_)
        * pq__
        * (a1__ + b1__ * x_.pow(n_)).pow(p_)
        * (a2__ + b2__ * x_.pow(n_)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let pq__ = symbols.pq__;
    let x_ = symbols.x_;
    (c__ * x_).pow(m_) * pq__ * (a__ + b__ * x_.pow(n_)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_2(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let pq__ = symbols.pq__;
    let x_ = symbols.x_;
    (c__ * x_).pow(m_) * pq__ / (a__ + b__ * x_.pow(n_))
}

#[inline(never)]
fn rubi_shared_pattern_3(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let pq__ = symbols.pq__;
    let x_ = symbols.x_;
    x_.pow(m_) * pq__ * (a__ + b__ * x_.pow(n_)).pow(p_)
}
