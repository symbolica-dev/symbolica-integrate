use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_1690(rules);
    push_rules_rule_1691(rules);
    push_rules_rule_1692(rules);
    push_rules_rule_1693(rules);
    push_rules_rule_1694(rules);
    push_rules_rule_1695(rules);
    push_rules_rule_1696(rules);
    push_rules_rule_1697(rules);
    push_rules_rule_1698(rules);
    push_rules_rule_1699(rules);
    push_rules_rule_1700(rules);
    push_rules_rule_1701(rules);
    push_rules_rule_1702(rules);
    push_rules_rule_1703(rules);
    push_rules_rule_1704(rules);
    push_rules_rule_1705(rules);
    push_rules_rule_1706(rules);
    push_rules_rule_1707(rules);
    push_rules_rule_1708(rules);
    push_rules_rule_1709(rules);
    push_rules_rule_1710(rules);
    push_rules_rule_1711(rules);
    push_rules_rule_1712(rules);
    push_rules_rule_1713(rules);
    push_rules_rule_1714(rules);
    push_rules_rule_1715(rules);
    push_rules_rule_1716(rules);
    push_rules_rule_1717(rules);
    push_rules_rule_1718(rules);
    push_rules_rule_1719(rules);
    push_rules_rule_1720(rules);
    push_rules_rule_1721(rules);
    push_rules_rule_1722(rules);
    push_rules_rule_1723(rules);
    push_rules_rule_1724(rules);
    push_rules_rule_1725(rules);
    push_rules_rule_1726(rules);
}

fn push_rules_rule_1690(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 1690,
        source: "Int[x_^m_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_.,x_Symbol] :=
          1/n \\[Star] Subst[Int[(a+b*x+c*x^2)^p,x],x,x^n] /;
        FreeQ[{a,b,c,m,n,p},x] && EqQ[n2,2*n] && EqQ[Simplify[m-n+1],0]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [m_, a__, b__, n_, c__, n2_, p_, x_],
        optional: [m_, b__, c__, n2_, p_],
        x_free: [a__, b__, c__, m_, n_, p_],
        scaled: [(n2_, 2, n_)],
        when: {
            freeq!([a__, b__, c__, m_, n_, p_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && eqq!(rubi_simplify(&(&m_ - &n_ + Atom::num(1))), 0)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = (&a__ + &b__ * &sub_atom + &c__ * sub_atom.pow(2)).pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);
            let substituted = rubi_subst(&transformed, sub, x_.pow(&n_));

            rubi_star(Atom::num(1) / n_, substituted)
        },
    ));
}

fn push_rules_rule_1691(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 1691,
        source: "Int[(d_.*x_)^m_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_.,x_Symbol] :=
          Int[ExpandIntegrand[(d*x)^m*(a+b*x^n+c*x^(2*n))^p,x],x] /;
        FreeQ[{a,b,c,d,m,n},x] && EqQ[n2,2*n] && IGtQ[p,0] && Not[IntegerQ[Simplify[(m+1)/n]]]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [d__, m_, a__, b__, n_, c__, n2_, p_, x_],
        optional: [d__, m_, b__, c__, n2_, p_],
        x_free: [a__, b__, c__, d__, m_, n_],
        when: {
            freeq!([a__, b__, c__, d__, m_, n_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && igtq!(p_, 0)
                && !integerq!(rubi_simplify(&((&m_ + Atom::num(1)) / &n_)))
        },
        rhs: {
            let integrand =
                (&d__ * x_).pow(&m_)
                    * (&a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_))
                        .pow(&p_);
            let expanded = rubi_expand_integrand(&integrand, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_1692(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 1692,
        source: "Int[x_^m_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
          Int[x^(m+2*n*p)*(c+b*x^(-n)+a*x^(-2*n))^p,x] /;
        FreeQ[{a,b,c,m,n},x] && EqQ[n2,2*n] && ILtQ[p,0] && NegQ[n]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [m_, a__, b__, n_, c__, n2_, p_, x_],
        optional: [m_, b__, c__, n2_],
        x_free: [a__, b__, c__, m_, n_],
        when: {
            freeq!([a__, b__, c__, m_, n_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && iltq!(p_, 0)
                && negq!(n_)
        },
        rhs: {
            let recursive_integrand = x_.pow(&m_ + Atom::num(2) * &n_ * &p_)
                * (&c__ + &b__ * x_.pow(-&n_) + &a__ * x_.pow(Atom::num(-2) * &n_))
                    .pow(p_);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_1693(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 1693,
        source: "Int[x_^m_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_.,x_Symbol] :=
          1/n \\[Star] Subst[Int[x^(Simplify[(m+1)/n]-1)*(a+b*x+c*x^2)^p,x],x,x^n] /;
        FreeQ[{a,b,c,m,n,p},x] && EqQ[n2,2*n] && IntegerQ[Simplify[(m+1)/n]]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [m_, a__, b__, n_, c__, n2_, p_, x_],
        optional: [m_, b__, c__, n2_, p_],
        x_free: [a__, b__, c__, m_, n_, p_],
        scaled: [(n2_, 2, n_)],
        when: {
            freeq!([a__, b__, c__, m_, n_, p_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && integerq!(rubi_simplify(&((&m_ + Atom::num(1)) / &n_)))
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let sub_atom = Atom::var(sub);
            let exponent = rubi_simplify(&((&m_ + Atom::num(1)) / &n_));
            let transformed_integrand = sub_atom.pow(&exponent - Atom::num(1))
                * (&a__ + &b__ * &sub_atom + &c__ * sub_atom.pow(2)).pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);
            let substituted = rubi_subst(&transformed, sub, x_.pow(&n_));

            rubi_star(Atom::num(1) / n_, substituted)
        },
    ));
}

fn push_rules_rule_1694(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 1694,
        source: "Int[(d_*x_)^m_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_.,x_Symbol] :=
          d^IntPart[m]*(d*x)^FracPart[m]/x^FracPart[m] \\[Star] Int[x^m*(a+b*x^n+c*x^(2*n))^p,x] /;
        FreeQ[{a,b,c,d,m,n,p},x] && EqQ[n2,2*n] && IntegerQ[Simplify[(m+1)/n]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [d__, m_, a__, b__, n_, c__, n2_, p_, x_],
        optional: [m_, b__, c__, n2_, p_],
        x_free: [a__, b__, c__, d__, m_, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, m_, n_, p_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && integerq!(rubi_simplify(&((&m_ + Atom::num(1)) / &n_)))
        },
        rhs: {
            let frac_m = rubi_frac_part(&m_);
            let recursive_integrand =
                x_.pow(&m_)
                    * (&a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_))
                        .pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let coefficient = d__.pow(rubi_int_part(&m_)) * (&d__ * x_).pow(&frac_m)
                / x_.pow(frac_m);

            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_1695(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 1695,
        source: "Int[x_^m_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
          With[{k=GCD[m+1,n]},
          1/k \\[Star] Subst[Int[x^((m+1)/k-1)*(a+b*x^(n/k)+c*x^(2*n/k))^p,x],x,x^k] /;
         k!=1] /;
        FreeQ[{a,b,c,p},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c,0] && IGtQ[n,0] && IntegerQ[m]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [m_, a__, b__, n_, c__, n2_, p_, x_],
        optional: [m_, b__, c__, n2_],
        x_free: [a__, b__, c__, p_],
        when: {
            freeq!([a__, b__, c__, p_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && igtq!(n_, 0)
                && integerq!(m_)
                && rubi_gcd(&(&m_ + Atom::num(1)), &n_).is_some_and(|k| k != 1)
        },
        rhs: {
            let k = Atom::num(rubi_gcd(&(&m_ + Atom::num(1)), &n_).rubi_rhs());
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = sub_atom.pow((&m_ + Atom::num(1)) / &k - Atom::num(1))
                * (&a__
                    + &b__ * sub_atom.pow(&n_ / &k)
                    + &c__ * sub_atom.pow(Atom::num(2) * (&n_ / &k)))
                .pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);
            let substituted = rubi_subst(&transformed, sub, x_.pow(&k));

            rubi_star(Atom::num(1) / k, substituted)
        },
    ));
}

fn push_rules_rule_1696(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 1696,
        source: "Int[(d_.*x_)^m_*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
          With[{k=Denominator[m]},
          k/d \\[Star] Subst[Int[x^(k*(m+1)-1)*(a+b*x^(k*n)/d^n+c*x^(2*k*n)/d^(2*n))^p,x],x,(d*x)^(1/k)]] /;
        FreeQ[{a,b,c,d,p},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c,0] && IGtQ[n,0] && FractionQ[m] && IntegerQ[p]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [d__, m_, a__, b__, n_, c__, n2_, p_, x_],
        optional: [d__, b__, c__, n2_],
        x_free: [a__, b__, c__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__, p_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && igtq!(n_, 0)
                && fractionq!(m_)
                && integerq!(p_)
        },
        rhs: {
            let k_i = rubi_denominator(&m_).unwrap();
            let k = Atom::num(k_i);
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = sub_atom.pow(&k * (&m_ + Atom::num(1)) - Atom::num(1))
                * (&a__
                    + &b__ * sub_atom.pow(&k * &n_) / d__.pow(&n_)
                    + &c__ * sub_atom.pow(Atom::num(2) * &k * &n_)
                        / d__.pow(Atom::num(2) * &n_))
                .pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);
            let substituted = rubi_subst(
                &transformed,
                sub,
                (&d__ * x_).pow(Atom::num(1) / &k),
            );

            rubi_star(&k / &d__, substituted)
        },
    ));
}

fn push_rules_rule_1697(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 1697,
        source: "Int[(d_.*x_)^m_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
          d^(n-1)*(d*x)^(m-n+1)*(a+b*x^n+c*x^(2*n))^p*(b*n*p+c*(m+n*(2*p-1)+1)*x^n)/(c*(m+2*n*p+1)*(m+n*(2*p-1)+1)) -
          n*p*d^n/(c*(m+2*n*p+1)*(m+n*(2*p-1)+1)) \\[Star]
            Int[(d*x)^(m-n)*(a+b*x^n+c*x^(2*n))^(p-1)*Simp[a*b*(m-n+1)-(2*a*c*(m+n*(2*p-1)+1)-b^2*(m+n*(p-1)+1))*x^n,x],x] /;
        FreeQ[{a,b,c,d},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c,0] && IGtQ[n,0] && IGtQ[p,0] && GtQ[m,n-1] && NeQ[m+2*n*p+1,0] && NeQ[m+n*(2*p-1)+1,0]",
        desc: "Trinomial recurrence 1b with A=0, B=1 and m=m-n",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [d__, m_, a__, b__, n_, c__, n2_, p_, x_],
        optional: [d__, m_, b__, c__, n2_],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && igtq!(n_, 0)
                && igtq!(p_, 0)
                && gtq!(m_, &n_ - Atom::num(1))
                && neq!(&m_ + Atom::num(2) * &n_ * &p_ + Atom::num(1), 0)
                && neq!(&m_ + &n_ * (Atom::num(2) * &p_ - Atom::num(1)) + Atom::num(1), 0)
        },
        rhs: {
            let trinomial = &a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_);
            let first_denominator_factor = &m_ + Atom::num(2) * &n_ * &p_ + Atom::num(1);
            let second_denominator_factor =
                &m_ + &n_ * (Atom::num(2) * &p_ - Atom::num(1)) + Atom::num(1);
            let denominator = &c__ * &first_denominator_factor * &second_denominator_factor;
            let direct = d__.pow(&n_ - Atom::num(1))
                * (&d__ * x_).pow(&m_ - &n_ + Atom::num(1))
                * trinomial.pow(&p_)
                * (&b__ * &n_ * &p_ + &c__ * &second_denominator_factor * x_.pow(&n_))
                / &denominator;
            let simp = rubi_simp(
                &(&a__ * &b__ * (&m_ - &n_ + Atom::num(1))
                    - (Atom::num(2) * &a__ * &c__ * &second_denominator_factor
                        - b__.pow(2) * (&m_ + &n_ * (&p_ - Atom::num(1)) + Atom::num(1)))
                        * x_.pow(&n_)),
                x_,
            );
            let recursive_integrand = (&d__ * x_).pow(&m_ - &n_)
                * trinomial.pow(&p_ - Atom::num(1))
                * simp;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let coefficient = &n_ * &p_ * d__.pow(&n_) / &denominator;

            rubi_simp(&(direct), x_) - rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_1698(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 1698,
        source: "Int[(d_.*x_)^m_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
          (d*x)^(m+1)*(a+b*x^n+c*x^(2*n))^p/(d*(m+1)) -
          n*p/(d^n*(m+1)) \\[Star] Int[(d*x)^(m+n)*(b+2*c*x^n)*(a+b*x^n+c*x^(2*n))^(p-1),x] /;
        FreeQ[{a,b,c,d},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c,0] && IGtQ[n,0] && IGtQ[p,0] && LtQ[m,-1]",
        desc: "Trinomial recurrence 1a with A=1 and B=0",
        refs: ["G&R 2.160.2"],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [d__, m_, a__, b__, n_, c__, n2_, p_, x_],
        optional: [d__, m_, b__, c__, n2_],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && igtq!(n_, 0)
                && igtq!(p_, 0)
                && ltq!(m_, -1)
        },
        rhs: {
            let trinomial = &a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_);
            let m1 = &m_ + Atom::num(1);
            let direct = (&d__ * x_).pow(&m1) * trinomial.pow(&p_) / (&d__ * &m1);
            let recursive_integrand = (&d__ * x_).pow(&m_ + &n_)
                * (&b__ + Atom::num(2) * &c__ * x_.pow(&n_))
                * trinomial.pow(&p_ - Atom::num(1));
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let coefficient = &n_ * &p_ / (d__.pow(&n_) * &m1);

            rubi_simp(&(direct), x_) - rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_1699(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 1699,
        source: "Int[(d_.*x_)^m_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
          (d*x)^(m+1)*(a+b*x^n+c*x^(2*n))^p/(d*(m+2*n*p+1)) +
          n*p/(m+2*n*p+1) \\[Star] Int[(d*x)^m*(2*a+b*x^n)*(a+b*x^n+c*x^(2*n))^(p-1),x] /;
        FreeQ[{a,b,c,d,m},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c,0] && IGtQ[n,0] && IGtQ[p,0] && NeQ[m+2*n*p+1,0]",
        desc: "Trinomial recurrence 1b with A=1 and B=0",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [d__, m_, a__, b__, n_, c__, n2_, p_, x_],
        optional: [d__, m_, b__, c__, n2_],
        x_free: [a__, b__, c__, d__, m_],
        when: {
            freeq!([a__, b__, c__, d__, m_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && igtq!(n_, 0)
                && igtq!(p_, 0)
                && neq!(&m_ + Atom::num(2) * &n_ * &p_ + Atom::num(1), 0)
        },
        rhs: {
            let trinomial = &a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_);
            let denominator = &m_ + Atom::num(2) * &n_ * &p_ + Atom::num(1);
            let direct = (&d__ * x_).pow(&m_ + Atom::num(1)) * trinomial.pow(&p_)
                / (&d__ * &denominator);
            let recursive_integrand = (&d__ * x_).pow(&m_)
                * (Atom::num(2) * &a__ + &b__ * x_.pow(&n_))
                * trinomial.pow(&p_ - Atom::num(1));
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let coefficient = &n_ * &p_ / &denominator;

            rubi_simp(&(direct), x_) + rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_1700(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 1700,
        source: "Int[(d_.*x_)^m_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
          d^(n-1)*(d*x)^(m-n+1)*(b+2*c*x^n)*(a+b*x^n+c*x^(2*n))^(p+1)/(n*(p+1)*(b^2-4*a*c)) -
          d^n/(n*(p+1)*(b^2-4*a*c)) \\[Star]
            Int[(d*x)^(m-n)*(b*(m-n+1)+2*c*(m+2*n*(p+1)+1)*x^n)*(a+b*x^n+c*x^(2*n))^(p+1),x] /;
        FreeQ[{a,b,c,d},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c,0] && IGtQ[n,0] && ILtQ[p,-1] && GtQ[m,n-1] && LeQ[m,2*n-1]",
        desc: "Trinomial recurrence 2b with A=0, B=1 and m=m-n",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [d__, m_, a__, b__, n_, c__, n2_, p_, x_],
        optional: [d__, m_, b__, c__, n2_],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && igtq!(n_, 0)
                && iltq!(p_, -1)
                && gtq!(m_, &n_ - Atom::num(1))
                && leq!(m_, Atom::num(2) * &n_ - Atom::num(1))
        },
        rhs: {
            let trinomial = &a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_);
            let discriminant = b__.pow(2) - Atom::num(4) * &a__ * &c__;
            let denominator = &n_ * (&p_ + Atom::num(1)) * &discriminant;
            let direct = d__.pow(&n_ - Atom::num(1))
                * (&d__ * x_).pow(&m_ - &n_ + Atom::num(1))
                * (&b__ + Atom::num(2) * &c__ * x_.pow(&n_))
                * trinomial.pow(&p_ + Atom::num(1))
                / &denominator;
            let recursive_integrand = (&d__ * x_).pow(&m_ - &n_)
                * (&b__ * (&m_ - &n_ + Atom::num(1))
                    + Atom::num(2)
                        * &c__
                        * (&m_ + Atom::num(2) * &n_ * (&p_ + Atom::num(1)) + Atom::num(1))
                        * x_.pow(&n_))
                * trinomial.pow(&p_ + Atom::num(1));
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let coefficient = d__.pow(&n_) / &denominator;

            rubi_simp(&(direct), x_) - rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_1701(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 1701,
        source: "Int[(d_.*x_)^m_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
          -d^(2*n-1)*(d*x)^(m-2*n+1)*(2*a+b*x^n)*(a+b*x^n+c*x^(2*n))^(p+1)/(n*(p+1)*(b^2-4*a*c)) +
          d^(2*n)/(n*(p+1)*(b^2-4*a*c)) \\[Star]
            Int[(d*x)^(m-2*n)*(2*a*(m-2*n+1)+b*(m+n*(2*p+1)+1)*x^n)*(a+b*x^n+c*x^(2*n))^(p+1),x] /;
        FreeQ[{a,b,c,d},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c,0] && IGtQ[n,0] && ILtQ[p,-1] && GtQ[m,2*n-1]",
        desc: "Trinomial recurrence 2a with A=0, B=1 and m=m-n",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [d__, m_, a__, b__, n_, c__, n2_, p_, x_],
        optional: [d__, m_, b__, c__, n2_],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && igtq!(n_, 0)
                && iltq!(p_, -1)
                && gtq!(m_, Atom::num(2) * &n_ - Atom::num(1))
        },
        rhs: {
            let trinomial = &a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_);
            let discriminant = b__.pow(2) - Atom::num(4) * &a__ * &c__;
            let denominator = &n_ * (&p_ + Atom::num(1)) * &discriminant;
            let direct = -d__.pow(Atom::num(2) * &n_ - Atom::num(1))
                * (&d__ * x_).pow(&m_ - Atom::num(2) * &n_ + Atom::num(1))
                * (Atom::num(2) * &a__ + &b__ * x_.pow(&n_))
                * trinomial.pow(&p_ + Atom::num(1))
                / &denominator;
            let recursive_integrand = (&d__ * x_).pow(&m_ - Atom::num(2) * &n_)
                * (Atom::num(2) * &a__ * (&m_ - Atom::num(2) * &n_ + Atom::num(1))
                    + &b__ * (&m_ + &n_ * (Atom::num(2) * &p_ + Atom::num(1)) + Atom::num(1))
                        * x_.pow(&n_))
                * trinomial.pow(&p_ + Atom::num(1));
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let coefficient = d__.pow(Atom::num(2) * &n_) / &denominator;

            rubi_simp(&(direct), x_) + rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_1702(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 1702,
        source: "Int[(d_.*x_)^m_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
          -(d*x)^(m+1)*(b^2-2*a*c+b*c*x^n)*(a+b*x^n+c*x^(2*n))^(p+1)/(a*d*n*(p+1)*(b^2-4*a*c)) +
          1/(a*n*(p+1)*(b^2-4*a*c)) \\[Star]
            Int[(d*x)^m*(a+b*x^n+c*x^(2*n))^(p+1)*Simp[b^2*(m+n*(p+1)+1)-2*a*c*(m+2*n*(p+1)+1)+b*c*(m+n*(2*p+3)+1)*x^n,x],x] /;
        FreeQ[{a,b,c,d,m},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c,0] && IGtQ[n,0] && ILtQ[p,-1]",
        desc: "Trinomial recurrence 2b with A=1 and B=0",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [d__, m_, a__, b__, n_, c__, n2_, p_, x_],
        optional: [d__, m_, b__, c__, n2_],
        x_free: [a__, b__, c__, d__, m_],
        when: {
            freeq!([a__, b__, c__, d__, m_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && igtq!(n_, 0)
                && iltq!(p_, -1)
        },
        rhs: {
            let trinomial = &a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_);
            let discriminant = b__.pow(2) - Atom::num(4) * &a__ * &c__;
            let denominator = &a__ * &n_ * (&p_ + Atom::num(1)) * &discriminant;
            let direct = -(&d__ * x_).pow(&m_ + Atom::num(1))
                * (b__.pow(2) - Atom::num(2) * &a__ * &c__ + &b__ * &c__ * x_.pow(&n_))
                * trinomial.pow(&p_ + Atom::num(1))
                / (&d__ * &denominator);
            let simp = rubi_simp(
                &(b__.pow(2) * (&m_ + &n_ * (&p_ + Atom::num(1)) + Atom::num(1))
                    - Atom::num(2)
                        * &a__
                        * &c__
                        * (&m_ + Atom::num(2) * &n_ * (&p_ + Atom::num(1)) + Atom::num(1))
                    + &b__
                        * &c__
                        * (&m_ + &n_ * (Atom::num(2) * &p_ + Atom::num(3)) + Atom::num(1))
                        * x_.pow(&n_)),
                x_,
            );
            let recursive_integrand =
                (&d__ * x_).pow(&m_) * trinomial.pow(&p_ + Atom::num(1)) * simp;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let coefficient = Atom::num(1) / &denominator;

            rubi_simp(&(direct), x_) + rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_1703(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 1703,
        source: "Int[(d_.*x_)^m_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
          d^(2*n-1)*(d*x)^(m-2*n+1)*(a+b*x^n+c*x^(2*n))^(p+1)/(c*(m+2*n*p+1)) -
          d^(2*n)/(c*(m+2*n*p+1)) \\[Star]
            Int[(d*x)^(m-2*n)*Simp[a*(m-2*n+1)+b*(m+n*(p-1)+1)*x^n,x]*(a+b*x^n+c*x^(2*n))^p,x] /;
        FreeQ[{a,b,c,d,p},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c,0] && IGtQ[n,0] && GtQ[m,2*n-1] && NeQ[m+2*n*p+1,0] && IntegerQ[p]",
        desc: "Trinomial recurrence 3a with A=0, B=1 and m=m-n",
        refs: ["G&R 2.160.3"],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [d__, m_, a__, b__, n_, c__, n2_, p_, x_],
        optional: [d__, m_, b__, c__, n2_],
        x_free: [a__, b__, c__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__, p_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && igtq!(n_, 0)
                && gtq!(m_, Atom::num(2) * &n_ - Atom::num(1))
                && neq!(&m_ + Atom::num(2) * &n_ * &p_ + Atom::num(1), 0)
                && integerq!(p_)
        },
        rhs: {
            let trinomial = &a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_);
            let denominator = &c__ * (&m_ + Atom::num(2) * &n_ * &p_ + Atom::num(1));
            let direct = d__.pow(Atom::num(2) * &n_ - Atom::num(1))
                * (&d__ * x_).pow(&m_ - Atom::num(2) * &n_ + Atom::num(1))
                * trinomial.pow(&p_ + Atom::num(1))
                / &denominator;
            let simp = rubi_simp(
                &(&a__ * (&m_ - Atom::num(2) * &n_ + Atom::num(1))
                    + &b__ * (&m_ + &n_ * (&p_ - Atom::num(1)) + Atom::num(1))
                        * x_.pow(&n_)),
                x_,
            );
            let recursive_integrand =
                (&d__ * x_).pow(&m_ - Atom::num(2) * &n_) * simp * trinomial.pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let coefficient = d__.pow(Atom::num(2) * &n_) / &denominator;

            rubi_simp(&(direct), x_) - rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_1704(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 1704,
        source: "Int[(d_.*x_)^m_*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
          (d*x)^(m+1)*(a+b*x^n+c*x^(2*n))^(p+1)/(a*d*(m+1)) -
          1/(a*d^n*(m+1)) \\[Star] Int[(d*x)^(m+n)*(b*(m+n*(p+1)+1)+c*(m+2*n*(p+1)+1)*x^n)*(a+b*x^n+c*x^(2*n))^p,x] /;
        FreeQ[{a,b,c,d,p},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c,0] && IGtQ[n,0] && LtQ[m,-1] && IntegerQ[p]",
        desc: "Trinomial recurrence 3b with A=1 and B=0",
        refs: ["G&R 2.160.1"],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [d__, m_, a__, b__, n_, c__, n2_, p_, x_],
        optional: [d__, b__, c__, n2_],
        x_free: [a__, b__, c__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__, p_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && igtq!(n_, 0)
                && ltq!(m_, -1)
                && integerq!(p_)
        },
        rhs: {
            let trinomial = &a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_);
            let m1 = &m_ + Atom::num(1);
            let direct = (&d__ * x_).pow(&m1) * trinomial.pow(&p_ + Atom::num(1))
                / (&a__ * &d__ * &m1);
            let recursive_integrand = (&d__ * x_).pow(&m_ + &n_)
                * (&b__ * (&m_ + &n_ * (&p_ + Atom::num(1)) + Atom::num(1))
                    + &c__ * (&m_ + Atom::num(2) * &n_ * (&p_ + Atom::num(1)) + Atom::num(1))
                        * x_.pow(&n_))
                * trinomial.pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let coefficient = Atom::num(1) / (&a__ * d__.pow(&n_) * &m1);

            rubi_simp(&(direct), x_) - rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_1705(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, n2_, x_);
    rules.push(rubi_rule!(
        order: 1705,
        source: "Int[(d_.*x_)^m_/(a_+b_.*x_^n_+c_.*x_^n2_.),x_Symbol] :=
          (d*x)^(m+1)/(a*d*(m+1)) -
          1/(a*d^n) \\[Star] Int[(d*x)^(m+n)*(b+c*x^n)/(a+b*x^n+c*x^(2*n)),x] /;
        FreeQ[{a,b,c,d},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c,0] && IGtQ[n,0] && LtQ[m,-1]",
        desc: "Algebraic expansion",
        refs: ["G&R 2.176, CRC 123"],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [d__, m_, a__, b__, n_, c__, n2_, x_],
        optional: [d__, b__, c__, n2_],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && igtq!(n_, 0)
                && ltq!(m_, -1)
        },
        rhs: {
            let denominator = &a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_);
            let m1 = &m_ + Atom::num(1);
            let direct = (&d__ * x_).pow(&m1) / (&a__ * &d__ * &m1);
            let recursive_integrand =
                (&d__ * x_).pow(&m_ + &n_) * (&b__ + &c__ * x_.pow(&n_)) / denominator;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let coefficient = Atom::num(1) / (&a__ * d__.pow(&n_));

            rubi_simp(&(direct), x_) - rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_1706(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, n2_, x_);
    rules.push(rubi_rule!(
        order: 1706,
        source: "Int[x_^m_/(a_+b_.*x_^n_+c_.*x_^n2_.),x_Symbol] :=
          Int[PolynomialDivide[x^m,(a+b*x^n+c*x^(2*n)),x],x] /;
        FreeQ[{a,b,c},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c,0] && IGtQ[n,0] && IGtQ[m,3*n-1]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [m_, a__, b__, n_, c__, n2_, x_],
        optional: [b__, c__, n2_],
        x_free: [a__, b__, c__],
        when: {
            freeq!([a__, b__, c__], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && igtq!(n_, 0)
                && igtq!(m_, Atom::num(3) * &n_ - Atom::num(1))
        },
        rhs: {
            let denominator = &a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_);
            let divided = rubi_polynomial_divide(x_.pow(&m_), &denominator, x_).rubi_rhs();

            rubi_rhs_int(&divided, x_)
        },
    ));
}

fn push_rules_rule_1707(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, n2_, x_);
    rules.push(rubi_rule!(
        order: 1707,
        source: "Int[(d_.*x_)^m_/(a_+b_.*x_^n_+c_.*x_^n2_.),x_Symbol] :=
          d^(2*n-1)*(d*x)^(m-2*n+1)/(c*(m-2*n+1)) -
          d^(2*n)/c \\[Star] Int[(d*x)^(m-2*n)*(a+b*x^n)/(a+b*x^n+c*x^(2*n)),x] /;
        FreeQ[{a,b,c,d},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c,0] && IGtQ[n,0] && GtQ[m,2*n-1]",
        desc: "Algebraic expansion",
        refs: ["G&R 2.174.1, CRC 119"],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [d__, m_, a__, b__, n_, c__, n2_, x_],
        optional: [d__, b__, c__, n2_],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && igtq!(n_, 0)
                && gtq!(m_, Atom::num(2) * &n_ - Atom::num(1))
        },
        rhs: {
            let denominator = &a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_);
            let shifted_m = &m_ - Atom::num(2) * &n_;
            let direct = d__.pow(Atom::num(2) * &n_ - Atom::num(1))
                * (&d__ * x_).pow(&shifted_m + Atom::num(1))
                / (&c__ * (&shifted_m + Atom::num(1)));
            let recursive_integrand = (&d__ * x_).pow(shifted_m)
                * (&a__ + &b__ * x_.pow(&n_))
                / denominator;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let coefficient = d__.pow(Atom::num(2) * &n_) / &c__;

            rubi_simp(&(direct), x_) - rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_1708(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, n2_, x_);
    rules.push(rubi_rule!(
        order: 1708,
        source: "Int[x_^m_./(a_+b_.*x_^n_+c_.*x_^n2_.),x_Symbol] :=
          With[{q=Rt[a/c,2]},
          With[{r=Rt[2*q-b/c,2]},
          1/(2*c*r) \\[Star] Int[x^(m-3*(n/2))*(q+r*x^(n/2))/(q+r*x^(n/2)+x^n),x] -
          1/(2*c*r) \\[Star] Int[x^(m-3*(n/2))*(q-r*x^(n/2))/(q-r*x^(n/2)+x^n),x]]] /;
        FreeQ[{a,b,c},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c,0] && IGtQ[n/2,0] && IGtQ[m,0] && GeQ[m,3*n/2] && LtQ[m,2*n] && NegQ[b^2-4*a*c]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [m_, a__, b__, n_, c__, n2_, x_],
        optional: [m_, b__, c__, n2_],
        x_free: [a__, b__, c__],
        when: {
            freeq!([a__, b__, c__], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && igtq!(&n_ / Atom::num(2), 0)
                && igtq!(m_, 0)
                && geq!(m_, Atom::num(3) * &n_ / Atom::num(2))
                && ltq!(m_, Atom::num(2) * &n_)
                && negq!(b__.pow(2) - Atom::num(4) * &a__ * &c__)
        },
        rhs: {
            let q = rubi_rt(&(&a__ / &c__), 2);
            let r = rubi_rt(&(Atom::num(2) * &q - &b__ / &c__), 2);
            let half_power = x_.pow(&n_ / Atom::num(2));
            let power = &m_ - Atom::num(3) * (&n_ / Atom::num(2));
            let first_integrand = x_.pow(&power)
                * (&q + &r * &half_power)
                / (&q + &r * &half_power + x_.pow(&n_));
            let second_integrand = x_.pow(power) * (&q - &r * &half_power)
                / (&q - &r * &half_power + x_.pow(n_));
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);
            let coefficient = Atom::num(1) / (Atom::num(2) * &c__ * &r);

            rubi_star(&coefficient, first)
                    - rubi_star(coefficient, second)
        },
    ));
}

fn push_rules_rule_1709(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, n2_, x_);
    rules.push(rubi_rule!(
        order: 1709,
        source: "Int[x_^m_./(a_+b_.*x_^n_+c_.*x_^n2_.),x_Symbol] :=
          With[{q=Rt[a/c,2]},
          With[{r=Rt[2*q-b/c,2]},
          1/(2*c*r) \\[Star] Int[x^(m-n/2)/(q-r*x^(n/2)+x^n),x] -
          1/(2*c*r) \\[Star] Int[x^(m-n/2)/(q+r*x^(n/2)+x^n),x]]] /;
        FreeQ[{a,b,c},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c,0] && IGtQ[n/2,0] && IGtQ[m,0] && GeQ[m,n/2] && LtQ[m,3*n/2] && NegQ[b^2-4*a*c]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [m_, a__, b__, n_, c__, n2_, x_],
        optional: [m_, b__, c__, n2_],
        x_free: [a__, b__, c__],
        when: {
            freeq!([a__, b__, c__], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && igtq!(&n_ / Atom::num(2), 0)
                && igtq!(m_, 0)
                && geq!(m_, &n_ / Atom::num(2))
                && ltq!(m_, Atom::num(3) * &n_ / Atom::num(2))
                && negq!(b__.pow(2) - Atom::num(4) * &a__ * &c__)
        },
        rhs: {
            let q = rubi_rt(&(&a__ / &c__), 2);
            let r = rubi_rt(&(Atom::num(2) * &q - &b__ / &c__), 2);
            let half_power = x_.pow(&n_ / Atom::num(2));
            let power = &m_ - &n_ / Atom::num(2);
            let first_integrand =
                x_.pow(&power) / (&q - &r * &half_power + x_.pow(&n_));
            let second_integrand = x_.pow(power) / (&q + &r * &half_power + x_.pow(n_));
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);
            let coefficient = Atom::num(1) / (Atom::num(2) * &c__ * &r);

            rubi_star(&coefficient, first)
                    - rubi_star(coefficient, second)
        },
    ));
}

fn push_rules_rule_1710(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, n2_, x_);
    rules.push(rubi_rule!(
        order: 1710,
        source: "Int[(d_.*x_)^m_/(a_+b_.*x_^n_+c_.*x_^n2_.),x_Symbol] :=
          With[{q=Rt[b^2-4*a*c,2]},
          d^n/2*(b/q+1) \\[Star] Int[(d*x)^(m-n)/(b/2+q/2+c*x^n),x] -
          d^n/2*(b/q-1) \\[Star] Int[(d*x)^(m-n)/(b/2-q/2+c*x^n),x]] /;
        FreeQ[{a,b,c,d},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c,0] && IGtQ[n,0] && GeQ[m,n]",
        desc: "Algebraic expansion",
        refs: ["G&R 2.161.1a & G&R 2.161.3"],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [d__, m_, a__, b__, n_, c__, n2_, x_],
        optional: [d__, b__, c__, n2_],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && igtq!(n_, 0)
                && geq!(m_, n_)
        },
        rhs: {
            let q = rubi_rt(&(b__.pow(2) - Atom::num(4) * &a__ * &c__), 2);
            let first_integrand = (&d__ * x_).pow(&m_ - &n_)
                / (&b__ / Atom::num(2) + &q / Atom::num(2) + &c__ * x_.pow(&n_));
            let second_integrand = (&d__ * x_).pow(&m_ - &n_)
                / (&b__ / Atom::num(2) - &q / Atom::num(2) + &c__ * x_.pow(&n_));
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);
            let d_n = d__.pow(&n_);
            let first_coefficient = &d_n / Atom::num(2) * (&b__ / &q + Atom::num(1));
            let second_coefficient = &d_n / Atom::num(2) * (&b__ / &q - Atom::num(1));

            rubi_star(first_coefficient, first)
                    - rubi_star(second_coefficient, second)
        },
    ));
}

fn push_rules_rule_1711(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, n2_, x_);
    rules.push(rubi_rule!(
        order: 1711,
        source: "Int[(d_.*x_)^m_./(a_+b_.*x_^n_+c_.*x_^n2_.),x_Symbol] :=
          With[{q=Rt[b^2-4*a*c,2]},
          c/q \\[Star] Int[(d*x)^m/(b/2-q/2+c*x^n),x] - c/q \\[Star] Int[(d*x)^m/(b/2+q/2+c*x^n),x]] /;
        FreeQ[{a,b,c,d,m},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c,0] && IGtQ[n,0]",
        desc: "Algebraic expansion",
        refs: ["G&R 2.161.1a"],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [d__, m_, a__, b__, n_, c__, n2_, x_],
        optional: [d__, m_, b__, c__, n2_],
        x_free: [a__, b__, c__, d__, m_],
        when: {
            freeq!([a__, b__, c__, d__, m_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && igtq!(n_, 0)
        },
        rhs: {
            let q = rubi_rt(&(b__.pow(2) - Atom::num(4) * &a__ * &c__), 2);
            let first_integrand = (&d__ * x_).pow(&m_)
                / (&b__ / Atom::num(2) - &q / Atom::num(2) + &c__ * x_.pow(&n_));
            let second_integrand = (&d__ * x_).pow(m_)
                / (&b__ / Atom::num(2) + &q / Atom::num(2) + &c__ * x_.pow(n_));
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);
            let coefficient = &c__ / &q;

            rubi_star(&coefficient, first) - rubi_star(coefficient, second)
        },
    ));
}

fn push_rules_rule_1712(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 1712,
        source: "Int[x_^m_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
          -Subst[Int[(a+b*x^(-n)+c*x^(-2*n))^p/x^(m+2),x],x,1/x] /;
        FreeQ[{a,b,c,p},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c,0] && ILtQ[n,0] && IntegerQ[m]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [m_, a__, b__, n_, c__, n2_, p_, x_],
        optional: [m_, b__, c__, n2_],
        x_free: [a__, b__, c__, p_],
        when: {
            freeq!([a__, b__, c__, p_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && iltq!(n_, 0)
                && integerq!(m_)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = (&a__
                + &b__ * sub_atom.pow(-&n_)
                + &c__ * sub_atom.pow(Atom::num(-2) * &n_))
            .pow(&p_)
                / sub_atom.pow(&m_ + Atom::num(2));
            let transformed = rubi_rhs_int(&transformed_integrand, sub);

            -rubi_subst(&transformed, sub, Atom::num(1) / x_)
        },
    ));
}

fn push_rules_rule_1713(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 1713,
        source: "Int[(d_.*x_)^m_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
          With[{k=Denominator[m]},
          -k/d \\[Star] Subst[Int[(a+b*d^(-n)*x^(-k*n)+c*d^(-2*n)*x^(-2*k*n))^p/x^(k*(m+1)+1),x],x,1/(d*x)^(1/k)]] /;
        FreeQ[{a,b,c,d,p},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c,0] && ILtQ[n,0] && FractionQ[m]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [d__, m_, a__, b__, n_, c__, n2_, p_, x_],
        optional: [d__, b__, c__, n2_, m_],
        x_free: [a__, b__, c__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__, p_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && iltq!(n_, 0)
                && fractionq!(m_)
        },
        rhs: {
            let k_i = rubi_denominator(&m_).unwrap();
            let k = Atom::num(k_i);
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = (&a__
                + &b__ * d__.pow(-&n_) * sub_atom.pow(-&k * &n_)
                + &c__ * d__.pow(Atom::num(-2) * &n_) * sub_atom.pow(Atom::num(-2) * &k * &n_))
            .pow(&p_)
                / sub_atom.pow(&k * (&m_ + Atom::num(1)) + Atom::num(1));
            let transformed = rubi_rhs_int(&transformed_integrand, sub);
            let substituted = rubi_subst(
                &transformed,
                sub,
                Atom::num(1) / (&d__ * x_).pow(Atom::num(1) / &k),
            );

            rubi_star(-&k / &d__, substituted)
        },
    ));
}

fn push_rules_rule_1714(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 1714,
        source: "Int[(d_.*x_)^m_*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
          -d^IntPart[m]*(d*x)^FracPart[m]*(x^(-1))^FracPart[m] \\[Star] Subst[Int[(a+b*x^(-n)+c*x^(-2*n))^p/x^(m+2),x],x,1/x] /;
        FreeQ[{a,b,c,d,m,p},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c,0] && ILtQ[n,0] && Not[RationalQ[m]]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [d__, m_, a__, b__, n_, c__, n2_, p_, x_],
        optional: [d__, b__, c__, n2_],
        x_free: [a__, b__, c__, d__, m_, p_],
        when: {
            freeq!([a__, b__, c__, d__, m_, p_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && iltq!(n_, 0)
                && !rationalq!(m_)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let sub_atom = Atom::var(sub);
            let frac_m = rubi_frac_part(&m_);
            let transformed_integrand = (&a__
                + &b__ * sub_atom.pow(-&n_)
                + &c__ * sub_atom.pow(Atom::num(-2) * &n_))
            .pow(&p_)
                / sub_atom.pow(&m_ + Atom::num(2));
            let transformed = rubi_rhs_int(&transformed_integrand, sub);
            let substituted = rubi_subst(&transformed, sub, Atom::num(1) / x_);
            let coefficient = -d__.pow(rubi_int_part(&m_))
                * (&d__ * x_).pow(&frac_m)
                * (Atom::num(1) / x_).pow(&frac_m);

            rubi_star(coefficient, substituted)
        },
    ));
}

fn push_rules_rule_1715(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 1715,
        source: "Int[x_^m_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
          With[{k=Denominator[n]},
          k \\[Star] Subst[Int[x^(k*(m+1)-1)*(a+b*x^(k*n)+c*x^(2*k*n))^p,x],x,x^(1/k)]] /;
        FreeQ[{a,b,c,m,p},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c,0] && FractionQ[n]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [m_, a__, b__, n_, c__, n2_, p_, x_],
        optional: [m_, b__, c__, n2_],
        x_free: [a__, b__, c__, m_, p_],
        when: {
            freeq!([a__, b__, c__, m_, p_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && fractionq!(n_)
        },
        rhs: {
            let k_i = rubi_denominator(&n_).unwrap();
            let k = Atom::num(k_i);
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = sub_atom.pow(&k * (&m_ + Atom::num(1)) - Atom::num(1))
                * (&a__
                    + &b__ * sub_atom.pow(&k * &n_)
                    + &c__ * sub_atom.pow(Atom::num(2) * &k * &n_))
                .pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);
            let substituted =
                rubi_subst(&transformed, sub, x_.pow(Atom::num(1) / &k));

            rubi_star(k, substituted)
        },
    ));
}

fn push_rules_rule_1716(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 1716,
        source: "Int[(d_*x_)^m_*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
          d^IntPart[m]*(d*x)^FracPart[m]/x^FracPart[m] \\[Star] Int[x^m*(a+b*x^n+c*x^(2*n))^p,x] /;
        FreeQ[{a,b,c,d,m,p},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c,0] && FractionQ[n]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [d__, m_, a__, b__, n_, c__, n2_, p_, x_],
        optional: [b__, c__, n2_],
        x_free: [a__, b__, c__, d__, m_, p_],
        when: {
            freeq!([a__, b__, c__, d__, m_, p_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && fractionq!(n_)
        },
        rhs: {
            let frac_m = rubi_frac_part(&m_);
            let recursive_integrand =
                x_.pow(&m_)
                    * (&a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_))
                        .pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let coefficient = d__.pow(rubi_int_part(&m_)) * (&d__ * x_).pow(&frac_m)
                / x_.pow(frac_m);

            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_1717(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 1717,
        source: "Int[x_^m_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
          1/(m+1) \\[Star] Subst[Int[(a+b*x^Simplify[n/(m+1)]+c*x^Simplify[2*n/(m+1)])^p,x],x,x^(m+1)] /;
        FreeQ[{a,b,c,m,n,p},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c,0] && IntegerQ[Simplify[n/(m+1)]] && Not[IntegerQ[n]]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [m_, a__, b__, n_, c__, n2_, p_, x_],
        optional: [m_, b__, c__, n2_],
        x_free: [a__, b__, c__, m_, n_, p_],
        when: {
            if !(freeq!([a__, b__, c__, m_, n_, p_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0))
            {
                return ConditionResult::False;
            }

            let n_over_m_plus_1 = rubi_simplify(&(&n_ / (&m_ + Atom::num(1))));

            integerq!(n_over_m_plus_1) && !integerq!(n_)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = (&a__
                + &b__ * sub_atom.pow(rubi_simplify(&(&n_ / (&m_ + Atom::num(1)))))
                + &c__ * sub_atom.pow(rubi_simplify(
                    &(Atom::num(2) * &n_ / (&m_ + Atom::num(1))),
                )))
            .pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);
            let substituted =
                rubi_subst(&transformed, sub, x_.pow(&m_ + Atom::num(1)));
            let coefficient = Atom::num(1) / (&m_ + Atom::num(1));

            rubi_star(coefficient, substituted)
        },
    ));
}

fn push_rules_rule_1718(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 1718,
        source: "Int[(d_*x_)^m_*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
          d^IntPart[m]*(d*x)^FracPart[m]/x^FracPart[m] \\[Star] Int[x^m*(a+b*x^n+c*x^(2*n))^p,x] /;
        FreeQ[{a,b,c,d,m,n,p},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c,0] && IntegerQ[Simplify[n/(m+1)]] && Not[IntegerQ[n]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [d__, m_, a__, b__, n_, c__, n2_, p_, x_],
        optional: [b__, c__, n2_],
        x_free: [a__, b__, c__, d__, m_, n_, p_],
        when: {
            if !(freeq!([a__, b__, c__, d__, m_, n_, p_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0))
            {
                return ConditionResult::False;
            }

            let n_over_m_plus_1 = rubi_simplify(&(&n_ / (&m_ + Atom::num(1))));

            integerq!(n_over_m_plus_1) && !integerq!(n_)
        },
        rhs: {
            let frac_m = rubi_frac_part(&m_);
            let recursive_integrand =
                x_.pow(&m_)
                    * (&a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_))
                        .pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let coefficient = d__.pow(rubi_int_part(&m_)) * (&d__ * x_).pow(&frac_m)
                / x_.pow(frac_m);

            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_1719(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, n2_, x_);
    rules.push(rubi_rule!(
        order: 1719,
        source: "Int[(d_.*x_)^m_./(a_+b_.*x_^n_+c_.*x_^n2_.),x_Symbol] :=
          With[{q=Rt[b^2-4*a*c,2]},
          2*c/q \\[Star] Int[(d*x)^m/(b-q+2*c*x^n),x] -
          2*c/q \\[Star] Int[(d*x)^m/(b+q+2*c*x^n),x]] /;
        FreeQ[{a,b,c,d,m,n},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c,0]",
        desc: "Algebraic expansion",
        refs: ["G&R 2.161.1a"],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [d__, m_, a__, b__, n_, c__, n2_, x_],
        optional: [d__, m_, b__, c__, n2_],
        x_free: [a__, b__, c__, d__, m_, n_],
        when: {
            freeq!([a__, b__, c__, d__, m_, n_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
        },
        rhs: {
            let q = rubi_rt(&(b__.pow(2) - Atom::num(4) * &a__ * &c__), 2);
            let first_integrand =
                (&d__ * x_).pow(&m_) / (&b__ - &q + Atom::num(2) * &c__ * x_.pow(&n_));
            let second_integrand =
                (&d__ * x_).pow(&m_) / (&b__ + &q + Atom::num(2) * &c__ * x_.pow(&n_));
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);
            let coefficient = Atom::num(2) * &c__ / &q;

            rubi_star(&coefficient, first) - rubi_star(coefficient, second)
        },
    ));
}

fn push_rules_rule_1720(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 1720,
        source: "Int[(d_.*x_)^m_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
          -(d*x)^(m+1)*(b^2-2*a*c+b*c*x^n)*(a+b*x^n+c*x^(2*n))^(p+1)/(a*d*n*(p+1)*(b^2-4*a*c)) +
          1/(a*n*(p+1)*(b^2-4*a*c)) \\[Star]
            Int[(d*x)^m*(a+b*x^n+c*x^(2*n))^(p+1)*Simp[b^2*(n*(p+1)+m+1)-2*a*c*(m+2*n*(p+1)+1)+b*c*(2*n*p+3*n+m+1)*x^n,x],x] /;
        FreeQ[{a,b,c,d,m,n},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c,0] && ILtQ[p+1,0]",
        desc: "Trinomial recurrence 2b with A=1 and B=0",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [d__, m_, a__, b__, n_, c__, n2_, p_, x_],
        optional: [d__, m_, b__, c__, n2_],
        x_free: [a__, b__, c__, d__, m_, n_],
        when: {
            freeq!([a__, b__, c__, d__, m_, n_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && iltq!(&p_ + Atom::num(1), 0)
        },
        rhs: {
            let trinomial =
                &a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_);
            let discriminant = b__.pow(2) - Atom::num(4) * &a__ * &c__;
            let direct = -(&d__ * x_).pow(&m_ + Atom::num(1))
                * (b__.pow(2) - Atom::num(2) * &a__ * &c__ + &b__ * &c__ * x_.pow(&n_))
                * trinomial.pow(&p_ + Atom::num(1))
                / (&a__ * &d__ * &n_ * (&p_ + Atom::num(1)) * &discriminant);
            let simp_payload = rubi_simp(
                &(b__.pow(2) * (&n_ * (&p_ + Atom::num(1)) + &m_ + Atom::num(1))
                    - Atom::num(2)
                        * &a__
                        * &c__
                        * (&m_ + Atom::num(2) * &n_ * (&p_ + Atom::num(1)) + Atom::num(1))
                    + &b__
                        * &c__
                        * (Atom::num(2) * &n_ * &p_ + Atom::num(3) * &n_ + &m_ + Atom::num(1))
                        * x_.pow(&n_)),
                x_,
            );
            let recursive_integrand = (&d__ * x_).pow(&m_)
                * trinomial.pow(&p_ + Atom::num(1))
                * simp_payload;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let coefficient = Atom::num(1)
                / (&a__ * &n_ * (&p_ + Atom::num(1)) * &discriminant);

            rubi_simp(&(direct), x_) + rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_1721(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 1721,
        source: "Int[(d_.*x_)^m_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
          a^IntPart[p]*(a+b*x^n+c*x^(2*n))^FracPart[p]/
            ((1+2*c*x^n/(b+Rt[b^2-4*a*c,2]))^FracPart[p]*(1+2*c*x^n/(b-Rt[b^2-4*a*c,2]))^FracPart[p]) \\[Star]
            Int[(d*x)^m*(1+2*c*x^n/(b+Sqrt[b^2-4*a*c]))^p*(1+2*c*x^n/(b-Sqrt[b^2-4*a*c]))^p,x] /;
        FreeQ[{a,b,c,d,m,n,p},x] && EqQ[n2,2*n]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [d__, m_, a__, b__, n_, c__, n2_, p_, x_],
        optional: [d__, m_, b__, c__, n2_],
        x_free: [a__, b__, c__, d__, m_, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, m_, n_, p_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
        },
        rhs: {
            let discriminant = b__.pow(2) - Atom::num(4) * &a__ * &c__;
            let rt = rubi_rt(&discriminant, 2);
            let sqrt = discriminant.sqrt();
            let frac_p = rubi_frac_part(&p_);
            let plus_rt = Atom::num(1) + Atom::num(2) * &c__ * x_.pow(&n_) / (&b__ + &rt);
            let minus_rt = Atom::num(1) + Atom::num(2) * &c__ * x_.pow(&n_) / (&b__ - &rt);
            let plus_sqrt =
                Atom::num(1) + Atom::num(2) * &c__ * x_.pow(&n_) / (&b__ + &sqrt);
            let minus_sqrt =
                Atom::num(1) + Atom::num(2) * &c__ * x_.pow(&n_) / (&b__ - &sqrt);
            let recursive_integrand =
                (&d__ * x_).pow(&m_) * plus_sqrt.pow(&p_) * minus_sqrt.pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let coefficient = a__.pow(rubi_int_part(&p_))
                * (&a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_))
                    .pow(&frac_p)
                / (plus_rt.pow(&frac_p) * minus_rt.pow(frac_p));

            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_1722(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, mn_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 1722,
        source: "Int[x_^m_.*(a_+b_.*x_^mn_+c_.*x_^n_.)^p_.,x_Symbol] :=
          Int[x^(m-n*p)*(b+a*x^n+c*x^(2*n))^p,x] /;
        FreeQ[{a,b,c,m,n},x] && EqQ[mn,-n] && IntegerQ[p] && PosQ[n]",
        desc: "Algebraic normalization",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [m_, a__, b__, mn_, c__, n_, p_, x_],
        optional: [m_, b__, c__, n_, p_],
        x_free: [a__, b__, c__, m_, n_, p_],
        scaled: [(mn_, -1, n_)],
        when: {
            freeq!([a__, b__, c__, m_, n_], x_)
                && eqq!(mn_, -&n_)
                && integerq!(p_)
                && posq!(n_)
        },
        rhs: {
            let recursive_integrand = x_.pow(&m_ - &n_ * &p_)
                * (&b__ + &a__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_)).pow(&p_);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_1723(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, mn_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 1723,
        source: "Int[x_^m_.*(a_+b_.*x_^mn_+c_.*x_^n_.)^p_.,x_Symbol] :=
          x^(n*FracPart[p])*(a+b/x^n+c*x^n)^FracPart[p]/(b+a*x^n+c*x^(2*n))^FracPart[p] \\[Star] Int[x^(m-n*p)*(b+a*x^n+c*x^(2*n))^p,x] /;
        FreeQ[{a,b,c,m,n,p},x] && EqQ[mn,-n] && Not[IntegerQ[p]] && PosQ[n]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [m_, a__, b__, mn_, c__, n_, p_, x_],
        optional: [m_, b__, c__, n_, p_],
        x_free: [a__, b__, c__, m_, n_, p_],
        scaled: [(mn_, -1, n_)],
        when: {
            freeq!([a__, b__, c__, m_, n_, p_], x_)
                && eqq!(mn_, -&n_)
                && !integerq!(p_)
                && posq!(n_)
        },
        rhs: {
            let frac_p = rubi_frac_part(&p_);
            let original = &a__ + &b__ / x_.pow(&n_) + &c__ * x_.pow(&n_);
            let transformed = &b__ + &a__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_);
            let recursive_integrand = x_.pow(&m_ - &n_ * &p_) * transformed.pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let coefficient = x_.pow(&n_ * &frac_p) * original.pow(&frac_p)
                / transformed.pow(frac_p);

            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_1724(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, mn_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 1724,
        source: "Int[(d_*x_)^m_.*(a_+b_.*x_^mn_+c_.*x_^n_.)^p_.,x_Symbol] :=
          d^IntPart[m]*(d*x)^FracPart[m]/x^FracPart[m] \\[Star] Int[x^m*(a+b*x^(-n)+c*x^n)^p,x] /;
        FreeQ[{a,b,c,d,m,n,p},x] && EqQ[mn,-n]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: (d__ * x_).pow(m_) * (a__ + b__ * x_.pow(mn_) + c__ * x_.pow(n_)).pow(p_),
        with: [d__, m_, a__, b__, mn_, c__, n_, p_, x_],
        optional: [m_, b__, c__, n_, p_],
        x_free: [a__, b__, c__, d__, m_, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, m_, n_, p_], x_) && eqq!(mn_, -&n_)
        },
        rhs: {
            let frac_m = rubi_frac_part(&m_);
            let recursive_integrand = x_.pow(&m_)
                * (&a__ + &b__ * x_.pow(-&n_) + &c__ * x_.pow(&n_)).pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let coefficient = d__.pow(rubi_int_part(&m_)) * (&d__ * x_).pow(&frac_m)
                / x_.pow(frac_m);

            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_1726(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, m_, n_, n2_, p_, v__, x_);
    let rule = rubi_rule!(
        order: 1726,
        source: "Int[x_^m_.*(a_.+b_.*v_^n_+c_.*v_^n2_.)^p_.,x_Symbol] :=
          1/Coefficient[v,x,1]^(m+1) \\[Star] Subst[Int[SimplifyIntegrand[(x-Coefficient[v,x,0])^m*(a+b*x^n+c*x^(2*n))^p,x],x],x,v] /;
        FreeQ[{a,b,c,n,p},x] && EqQ[n2,2*n] && LinearQ[v,x] && IntegerQ[m] && NeQ[v,x]",
        desc: "Integration by substitution",
        refs: [],
        pattern: x_.pow(m_) * (a__ + b__ * v__.pow(n_) + c__ * v__.pow(n2_)).pow(p_),
        with: [m_, a__, b__, v__, n_, c__, n2_, p_, x_],
        optional: [m_, a__, b__, c__, n2_, p_],
        x_dep: [v__],
        x_free: [a__, b__, c__, n_, p_],
        x_linear: [v__],
        when: {
            freeq!([a__, b__, c__, n_, p_], x_)
                && integerq!(m_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && neq!(v__, x_)
        },
        rhs: {
            let coefficient_1 = rubi_coeff(&v__, x_, 1).unwrap();
            let coefficient_0 = rubi_coeff(&v__, x_, 0).unwrap();
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = rubi_simplify_integrand(
                &((sub_atom - coefficient_0).pow(&m_)
                    * (&a__
                        + &b__ * Atom::var(sub).pow(&n_)
                        + &c__ * Atom::var(sub).pow(Atom::num(2) * &n_))
                    .pow(&p_)),
                sub,
            );
            let transformed = rubi_rhs_int(&transformed_integrand, sub);
            let substituted = rubi_subst(&transformed, sub, v__);
            let coefficient = Atom::num(1) / coefficient_1.pow(&m_ + Atom::num(1));

            rubi_star(coefficient, substituted)
        },
    );
    rules.push(
        rule.with_early_not_integration_variable(v__)
            .with_repeated_proper_x_dependent_subexpression(),
    );
}

fn push_rules_rule_1725(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, m_, n_, n2_, p_, u__, v__);
    let rule = rubi_rule!(
        order: 1725,
        source: "Int[u_^m_.*(a_.+b_.*v_^n_+c_.*v_^n2_.)^p_.,x_Symbol] :=
          u^m/(Coefficient[v,x,1]*v^m) \\[Star] Subst[Int[x^m*(a+b*x^n+c*x^(2*n))^p,x],x,v] /;
        FreeQ[{a,b,c,m,n,p},x] && EqQ[n2,2*n] && LinearPairQ[u,v,x]",
        desc: "Integration by substitution and piecewise constant extraction",
        refs: [],
        pattern: u__.pow(m_) * (a__ + b__ * v__.pow(n_) + c__ * v__.pow(n2_)).pow(p_),
        with: [u__, m_, a__, b__, v__, n_, c__, n2_, p_, x_],
        optional: [m_, a__, b__, c__, n2_, p_],
        x_dep: [u__, v__],
        x_free: [a__, b__, c__, m_, n_, p_],
        x_linear: [u__, v__],
        when: {
            freeq!([a__, b__, c__, m_, n_, p_], x_)
                && rubi_linear_pair_q(&u__, &v__, x_)
                && eqq!(n2_, Atom::num(2) * &n_)
        },
        rhs: {
            let linear_coefficient = rubi_coeff(&v__, x_, 1).unwrap();
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = sub_atom.pow(&m_)
                * (&a__
                    + &b__ * sub_atom.pow(&n_)
                    + &c__ * sub_atom.pow(Atom::num(2) * &n_))
                .pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);
            let coefficient = u__.pow(&m_) / (linear_coefficient * v__.pow(&m_));
            let substituted = rubi_subst(&transformed, sub, v__);

            rubi_star(coefficient, substituted)
        },
    );
    rules.push(
        rule.with_early_not_integration_variable(u__)
            .with_repeated_proper_x_dependent_subexpression(),
    );
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
    let x_ = symbols.x_;
    (d__ * x_).pow(m_) * (a__ + b__ * x_.pow(n_) + c__ * x_.pow(n2_)).pow(p_)
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
    let x_ = symbols.x_;
    (d__ * x_).pow(m_) / (a__ + b__ * x_.pow(n_) + c__ * x_.pow(n2_))
}

#[inline(never)]
fn rubi_shared_pattern_2(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let m_ = symbols.m_;
    let mn_ = symbols.mn_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    x_.pow(m_) * (a__ + b__ * x_.pow(mn_) + c__ * x_.pow(n_)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_3(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let m_ = symbols.m_;
    let n2_ = symbols.n2_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    x_.pow(m_) * (a__ + b__ * x_.pow(n_) + c__ * x_.pow(n2_)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_4(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let m_ = symbols.m_;
    let n2_ = symbols.n2_;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    x_.pow(m_) / (a__ + b__ * x_.pow(n_) + c__ * x_.pow(n2_))
}
