use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_1958(rules);
    push_rules_rule_1959(rules);
    push_rules_rule_1960(rules);
    push_rules_rule_1961(rules);
    push_rules_rule_1962(rules);
    push_rules_rule_1963(rules);
    push_rules_rule_1964(rules);
    push_rules_rule_1965(rules);
    push_rules_rule_1966(rules);
    push_rules_rule_1967(rules);
    push_rules_rule_1968(rules);
    push_rules_rule_1969(rules);
    push_rules_rule_1970(rules);
    push_rules_rule_1971(rules);
    push_rules_rule_1972(rules);
    push_rules_rule_1973(rules);
    push_rules_rule_1974(rules);
    push_rules_rule_1975(rules);
    push_rules_rule_1976(rules);
    push_rules_rule_1977(rules);
    push_rules_rule_1978(rules);
}

fn push_rules_rule_1958(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, p_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 1958,
        source: "Int[x_^m_.*(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^r_.)^p_.,x_Symbol] :=
          Int[x^m*((a+b+c)*x^n)^p,x] /;
        FreeQ[{a,b,c,m,n,p},x] && EqQ[q,n] && EqQ[r,n]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [m_, a__, q_, b__, n_, c__, r_, p_, x_],
        optional: [m_, a__, q_, b__, n_, c__, r_, p_],
        when: {
            freeq!([a__, b__, c__, m_, n_, p_], x_)
                && eqq!(q_, n_)
                && eqq!(r_, n_)
        },
        rhs: {
            let integrand = x_.pow(&m_) * ((&a__ + &b__ + &c__) * x_.pow(&n_)).pow(&p_);

            rubi_rhs_int(&integrand, x_)
        },
    ));
}

fn push_rules_rule_1959(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, p_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 1959,
        source: "Int[x_^m_.*(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^r_.)^p_.,x_Symbol] :=
          Int[x^(m+p*q)*(a+b*x^(n-q)+c*x^(2*(n-q)))^p,x] /;
        FreeQ[{a,b,c,m,n,q},x] && EqQ[r,2*n-q] && IntegerQ[p] && PosQ[n-q]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [m_, a__, q_, b__, n_, c__, r_, p_, x_],
        optional: [m_, a__, q_, b__, n_, c__, r_, p_],
        when: {
            freeq!([a__, b__, c__, m_, n_, q_], x_)
                && eqq!(r_, Atom::num(2) * &n_ - &q_)
                && integerq!(p_)
                && posq!(&n_ - &q_)
        },
        rhs: {
            let n_minus_q = &n_ - &q_;
            let integrand = x_.pow(&m_ + &p_ * &q_)
                * (&a__
                    + &b__ * x_.pow(&n_minus_q)
                    + &c__ * x_.pow(Atom::num(2) * &n_minus_q))
                .pow(&p_);

            rubi_rhs_int(&integrand, x_)
        },
    ));
}

fn push_rules_rule_1960(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 1960,
        source: "Int[x_^m_./Sqrt[a_.*x_^q_.+b_.*x_^n_.+c_.*x_^r_.],x_Symbol] :=
          -2/(n-q) \\[Star] Subst[Int[1/(4*a-x^2),x],x,x^(m+1)*(2*a+b*x^(n-q))/Sqrt[a*x^q+b*x^n+c*x^r]] /;
        FreeQ[{a,b,c,m,n,q,r},x] && EqQ[r,2*n-q] && PosQ[n-q] && NeQ[b^2-4*a*c,0] && EqQ[m,q/2-1]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [m_, a__, q_, b__, n_, c__, r_, x_],
        optional: [m_, a__, q_, b__, n_, c__, r_],
        when: {
            freeq!([a__, b__, c__, m_, n_, q_, r_], x_)
                && eqq!(r_, Atom::num(2) * &n_ - &q_)
                && posq!(&n_ - &q_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && eqq!(m_, &q_ / 2 - 1)
        },
        rhs: {
            let denominator = &n_ - &q_;
            if denominator.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let sub_atom = Atom::var(sub);
            let trinomial = &a__ * x_.pow(&q_) + &b__ * x_.pow(&n_) + &c__ * x_.pow(&r_);
            let substitution = x_.pow(&m_ + 1)
                * (Atom::num(2) * &a__ + &b__ * x_.pow(&n_ - &q_))
                / trinomial.sqrt();
            let transformed =
                rubi_rhs_int(&(Atom::num(1) / (Atom::num(4) * &a__ - sub_atom.pow(2))), sub);

            rubi_star(Atom::num(-2), rubi_subst(&transformed, sub, substitution) / denominator)
        },
    ));
}

fn push_rules_rule_1962(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 1962,
        source: "Int[x_^m_./(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^r_.)^(3/2),x_Symbol] :=
          -2*x^((n-1)/2)*(b+2*c*x)/((b^2-4*a*c)*Sqrt[a*x^(n-1)+b*x^n+c*x^(n+1)]) /;
        FreeQ[{a,b,c,n},x] && EqQ[m,3*(n-1)/2] && EqQ[q,n-1] && EqQ[r,n+1] && NeQ[b^2-4*a*c,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [m_, a__, q_, b__, n_, c__, r_, x_],
        optional: [m_, a__, q_, b__, n_, c__, r_],
        when: {
            freeq!([a__, b__, c__, n_], x_)
                && eqq!(m_, Atom::num(3) * (&n_ - 1) / 2)
                && eqq!(q_, &n_ - 1)
                && eqq!(r_, &n_ + 1)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
        },
        rhs: {
            let denominator = (b__.pow(2) - Atom::num(4) * &a__ * &c__)
                * (&a__ * x_.pow(&n_ - 1) + &b__ * x_.pow(&n_) + &c__ * x_.pow(&n_ + 1))
                    .sqrt();
            if denominator.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            rubi_simp(&(-Atom::num(2)
                    * x_.pow((&n_ - 1) / 2)
                    * (&b__ + Atom::num(2) * &c__ * x_)
                    / denominator), x_)
        },
    ));
}

fn push_rules_rule_1963(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 1963,
        source: "Int[x_^m_./(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^r_.)^(3/2),x_Symbol] :=
          x^((n-1)/2)*(4*a+2*b*x)/((b^2-4*a*c)*Sqrt[a*x^(n-1)+b*x^n+c*x^(n+1)]) /;
        FreeQ[{a,b,c,n},x] && EqQ[m,(3*n-1)/2] && EqQ[q,n-1] && EqQ[r,n+1] && NeQ[b^2-4*a*c,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [m_, a__, q_, b__, n_, c__, r_, x_],
        optional: [m_, a__, q_, b__, n_, c__, r_],
        when: {
            freeq!([a__, b__, c__, n_], x_)
                && eqq!(m_, (Atom::num(3) * &n_ - 1) / 2)
                && eqq!(q_, &n_ - 1)
                && eqq!(r_, &n_ + 1)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
        },
        rhs: {
            let denominator = (b__.pow(2) - Atom::num(4) * &a__ * &c__)
                * (&a__ * x_.pow(&n_ - 1) + &b__ * x_.pow(&n_) + &c__ * x_.pow(&n_ + 1))
                    .sqrt();
            if denominator.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            rubi_simp(&(x_.pow((&n_ - 1) / 2)
                    * (Atom::num(4) * &a__ + Atom::num(2) * &b__ * x_)
                    / denominator), x_)
        },
    ));
}

fn push_rules_rule_1964(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, p_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 1964,
        source: "Int[x_^m_.*(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^r_.)^p_,x_Symbol] :=
          x^(m-n)*(a*x^(n-1)+b*x^n+c*x^(n+1))^(p+1)/(2*c*(p+1)) -
          b/(2*c) \\[Star] Int[x^(m-1)*(a*x^(n-1)+b*x^n+c*x^(n+1))^p,x] /;
        FreeQ[{a,b,c},x] && EqQ[r,2*n-q] && PosQ[n-q] && Not[IntegerQ[p]] && NeQ[b^2-4*a*c,0] && IGtQ[n,0] &&
          RationalQ[m,p,q] && EqQ[m+p*(n-1)-1,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [m_, a__, q_, b__, n_, c__, r_, p_, x_],
        optional: [m_, a__, q_, b__, n_, c__, r_],
        when: {
            freeq!([a__, b__, c__], x_)
                && eqq!(r_, Atom::num(2) * &n_ - &q_)
                && posq!(&n_ - &q_)
                && !integerq!(p_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && igtq!(n_, 0)
                && rationalq!([m_, p_, q_])
                && eqq!(&m_ + &p_ * (&n_ - 1) - 1, 0)
        },
        rhs: {
            let direct_denominator = Atom::num(2) * &c__ * (&p_ + 1);
            let recursive_denominator = Atom::num(2) * &c__;
            if direct_denominator.is_zero() || recursive_denominator.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let trinomial = &a__ * x_.pow(&n_ - 1) + &b__ * x_.pow(&n_) + &c__ * x_.pow(&n_ + 1);
            let direct = x_.pow(&m_ - &n_) * trinomial.pow(&p_ + 1) / direct_denominator;
            let recursive_integrand = x_.pow(&m_ - 1) * trinomial.pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) - rubi_star(b__, recursive / recursive_denominator)
        },
    ));
}

fn push_rules_rule_1965(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, p_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 1965,
        source: "Int[x_^m_.*(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^r_.)^p_,x_Symbol] :=
          x^(m-n+q+1)*(b+2*c*x^(n-q))*(a*x^q+b*x^n+c*x^(2*n-q))^p/(2*c*(n-q)*(2*p+1)) -
          p*(b^2-4*a*c)/(2*c*(2*p+1)) \\[Star] Int[x^(m+q)*(a*x^q+b*x^n+c*x^(2*n-q))^(p-1),x] /;
        FreeQ[{a,b,c},x] && EqQ[r,2*n-q] && PosQ[n-q] && Not[IntegerQ[p]] && NeQ[b^2-4*a*c,0] && IGtQ[n,0] && GtQ[p,0] &&
          RationalQ[m,q] && EqQ[m+p*q+1,n-q]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [m_, a__, q_, b__, n_, c__, r_, p_, x_],
        optional: [m_, a__, q_, b__, n_, c__, r_],
        when: {
            freeq!([a__, b__, c__], x_)
                && eqq!(r_, Atom::num(2) * &n_ - &q_)
                && posq!(&n_ - &q_)
                && !integerq!(p_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && igtq!(n_, 0)
                && gtq!(p_, 0)
                && rationalq!([m_, q_])
                && eqq!(&m_ + &p_ * &q_ + 1, &n_ - &q_)
        },
        rhs: {
            let direct_denominator = Atom::num(2) * &c__ * (&n_ - &q_) * (Atom::num(2) * &p_ + 1);
            let recursive_denominator = Atom::num(2) * &c__ * (Atom::num(2) * &p_ + 1);
            if direct_denominator.is_zero() || recursive_denominator.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let n_minus_q = &n_ - &q_;
            let trinomial = &a__ * x_.pow(&q_)
                + &b__ * x_.pow(&n_)
                + &c__ * x_.pow(Atom::num(2) * &n_ - &q_);
            let direct = x_.pow(&m_ - &n_ + &q_ + 1)
                * (&b__ + Atom::num(2) * &c__ * x_.pow(&n_minus_q))
                * trinomial.pow(&p_)
                / direct_denominator;
            let recursive_integrand = x_.pow(&m_ + &q_) * trinomial.pow(&p_ - 1);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) - rubi_star(&p_ * (b__.pow(2) - Atom::num(4) * &a__ * &c__) / recursive_denominator, recursive)
        },
    ));
}

fn push_rules_rule_1966(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, p_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 1966,
        source: "Int[x_^m_.*(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^r_.)^p_,x_Symbol] :=
          x^(m-n+q+1)*(b*(n-q)*p+c*(m+p*q+(n-q)*(2*p-1)+1)*x^(n-q))*(a*x^q+b*x^n+c*x^(2*n-q))^p/(c*(m+p*(2*n-q)+1)*(m+p*q+(n-q)*(2*p-1)+1)) +
          (n-q)*p/(c*(m+p*(2*n-q)+1)*(m+p*q+(n-q)*(2*p-1)+1)) \\[Star]
            Int[x^(m-(n-2*q))*
              Simp[-a*b*(m+p*q-n+q+1)+(2*a*c*(m+p*q+(n-q)*(2*p-1)+1)-b^2*(m+p*q+(n-q)*(p-1)+1))*x^(n-q),x]*
              (a*x^q+b*x^n+c*x^(2*n-q))^(p-1),x] /;
        FreeQ[{a,b,c},x] && EqQ[r,2*n-q] && PosQ[n-q] && Not[IntegerQ[p]] && NeQ[b^2-4*a*c,0] && IGtQ[n,0] && GtQ[p,0] &&
          RationalQ[m,q] && GtQ[m+p*q+1,n-q] && NeQ[m+p*(2*n-q)+1,0] && NeQ[m+p*q+(n-q)*(2*p-1)+1,0]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [m_, a__, q_, b__, n_, c__, r_, p_, x_],
        optional: [m_, a__, q_, b__, n_, c__, r_],
        when: {
            freeq!([a__, b__, c__], x_)
                && eqq!(r_, Atom::num(2) * &n_ - &q_)
                && posq!(&n_ - &q_)
                && !integerq!(p_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && igtq!(n_, 0)
                && gtq!(p_, 0)
                && rationalq!([m_, q_])
                && gtq!(&m_ + &p_ * &q_ + 1, &n_ - &q_)
                && neq!(&m_ + &p_ * (Atom::num(2) * &n_ - &q_) + 1, 0)
                && neq!(&m_ + &p_ * &q_ + (&n_ - &q_) * (Atom::num(2) * &p_ - 1) + 1, 0)
        },
        rhs: {
            let factor1 = &m_ + &p_ * (Atom::num(2) * &n_ - &q_) + 1;
            let factor2 = &m_ + &p_ * &q_ + (&n_ - &q_) * (Atom::num(2) * &p_ - 1) + 1;
            let denominator = &c__ * &factor1 * &factor2;
            if denominator.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let n_minus_q = &n_ - &q_;
            let trinomial = &a__ * x_.pow(&q_)
                + &b__ * x_.pow(&n_)
                + &c__ * x_.pow(Atom::num(2) * &n_ - &q_);
            let direct = x_.pow(&m_ - &n_ + &q_ + 1)
                * (&b__ * (&n_ - &q_) * &p_ + &c__ * &factor2 * x_.pow(&n_minus_q))
                * trinomial.pow(&p_)
                / &denominator;
            let simp_payload = -&a__ * &b__ * (&m_ + &p_ * &q_ - &n_ + &q_ + 1)
                + (Atom::num(2) * &a__ * &c__ * &factor2
                    - b__.pow(2) * (&m_ + &p_ * &q_ + (&n_ - &q_) * (&p_ - 1) + 1))
                    * x_.pow(&n_minus_q);
            let recursive_integrand = x_.pow(&m_ - (&n_ - Atom::num(2) * &q_))
                * rubi_simp(&simp_payload, x_)
                * trinomial.pow(&p_ - 1);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) + rubi_star((&n_ - &q_) * &p_ / denominator, recursive)
        },
    ));
}

fn push_rules_rule_1967(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, p_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 1967,
        source: "Int[x_^m_.*(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^r_.)^p_,x_Symbol] :=
          x^(m+1)*(a*x^q+b*x^n+c*x^(2*n-q))^p/(m+p*q+1) -
          (n-q)*p/(m+p*q+1) \\[Star] Int[x^(m+n)*(b+2*c*x^(n-q))*(a*x^q+b*x^n+c*x^(2*n-q))^(p-1),x] /;
        FreeQ[{a,b,c},x] && EqQ[r,2*n-q] && PosQ[n-q] && Not[IntegerQ[p]] && NeQ[b^2-4*a*c,0] && IGtQ[n,0] && GtQ[p,0] &&
          RationalQ[m,q] && LeQ[m+p*q+1,-(n-q)+1] && NeQ[m+p*q+1,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [m_, a__, q_, b__, n_, c__, r_, p_, x_],
        optional: [m_, a__, q_, b__, n_, c__, r_],
        when: {
            let lower_bound = -(&n_ - &q_) + 1;

            freeq!([a__, b__, c__], x_)
                && eqq!(r_, Atom::num(2) * &n_ - &q_)
                && posq!(&n_ - &q_)
                && !integerq!(p_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && igtq!(n_, 0)
                && gtq!(p_, 0)
                && rationalq!([m_, q_])
                && leq!(&m_ + &p_ * &q_ + 1, lower_bound)
                && neq!(&m_ + &p_ * &q_ + 1, 0)
        },
        rhs: {
            let denominator = &m_ + &p_ * &q_ + 1;
            if denominator.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let n_minus_q = &n_ - &q_;
            let trinomial = &a__ * x_.pow(&q_)
                + &b__ * x_.pow(&n_)
                + &c__ * x_.pow(Atom::num(2) * &n_ - &q_);
            let direct = x_.pow(&m_ + 1) * trinomial.pow(&p_) / &denominator;
            let recursive_integrand = x_.pow(&m_ + &n_)
                * (&b__ + Atom::num(2) * &c__ * x_.pow(&n_minus_q))
                * trinomial.pow(&p_ - 1);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_)
                    - rubi_star((&n_ - &q_) * &p_ / denominator, recursive)
        },
    ));
}

fn push_rules_rule_1968(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, p_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 1968,
        source: "Int[x_^m_.*(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^r_.)^p_,x_Symbol] :=
          x^(m+1)*(a*x^q+b*x^n+c*x^(2*n-q))^p/(m+p*(2*n-q)+1) +
          (n-q)*p/(m+p*(2*n-q)+1) \\[Star] Int[x^(m+q)*(2*a+b*x^(n-q))*(a*x^q+b*x^n+c*x^(2*n-q))^(p-1),x] /;
        FreeQ[{a,b,c},x] && EqQ[r,2*n-q] && PosQ[n-q] && Not[IntegerQ[p]] && NeQ[b^2-4*a*c,0] && IGtQ[n,0] && GtQ[p,0] &&
          RationalQ[m,q] && GtQ[m+p*q+1,-(n-q)] && NeQ[m+p*(2*n-q)+1,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [m_, a__, q_, b__, n_, c__, r_, p_, x_],
        optional: [m_, a__, q_, b__, n_, c__, r_],
        when: {
            let lower_bound = -(&n_ - &q_);

            freeq!([a__, b__, c__], x_)
                && eqq!(r_, Atom::num(2) * &n_ - &q_)
                && posq!(&n_ - &q_)
                && !integerq!(p_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && igtq!(n_, 0)
                && gtq!(p_, 0)
                && rationalq!([m_, q_])
                && gtq!(&m_ + &p_ * &q_ + 1, lower_bound)
                && neq!(&m_ + &p_ * (Atom::num(2) * &n_ - &q_) + 1, 0)
        },
        rhs: {
            let denominator = &m_ + &p_ * (Atom::num(2) * &n_ - &q_) + 1;
            if denominator.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let n_minus_q = &n_ - &q_;
            let trinomial = &a__ * x_.pow(&q_)
                + &b__ * x_.pow(&n_)
                + &c__ * x_.pow(Atom::num(2) * &n_ - &q_);
            let direct = x_.pow(&m_ + 1) * trinomial.pow(&p_) / &denominator;
            let recursive_integrand = x_.pow(&m_ + &q_)
                * (Atom::num(2) * &a__ + &b__ * x_.pow(&n_minus_q))
                * trinomial.pow(&p_ - 1);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_)
                    + rubi_star((&n_ - &q_) * &p_ / denominator, recursive)
        },
    ));
}

fn push_rules_rule_1969(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, p_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 1969,
        source: "Int[x_^m_.*(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^r_.)^p_,x_Symbol] :=
          -x^(m-q+1)*(b^2-2*a*c+b*c*x^(n-q))*(a*x^q+b*x^n+c*x^(2*n-q))^(p+1)/(a*(n-q)*(p+1)*(b^2-4*a*c)) +
          (2*a*c-b^2*(p+2))/(a*(p+1)*(b^2-4*a*c)) \\[Star]
            Int[x^(m-q)*(a*x^q+b*x^n+c*x^(2*n-q))^(p+1),x] /;
        FreeQ[{a,b,c},x] && EqQ[r,2*n-q] && PosQ[n-q] && Not[IntegerQ[p]] && NeQ[b^2-4*a*c,0] && IGtQ[n,0] && LtQ[p,-1] &&
          RationalQ[m,p,q] && EqQ[m+p*q+1,-(n-q)*(2*p+3)]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [m_, a__, q_, b__, n_, c__, r_, p_, x_],
        optional: [m_, a__, q_, b__, n_, c__, r_],
        when: {
            freeq!([a__, b__, c__], x_)
                && eqq!(r_, Atom::num(2) * &n_ - &q_)
                && posq!(&n_ - &q_)
                && !integerq!(p_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && igtq!(n_, 0)
                && ltq!(p_, -1)
                && rationalq!([m_, p_, q_])
                && eqq!(&m_ + &p_ * &q_ + 1, -(&n_ - &q_) * (Atom::num(2) * &p_ + 3))
        },
        rhs: {
            let discriminant = b__.pow(2) - Atom::num(4) * &a__ * &c__;
            let direct_denominator = &a__ * (&n_ - &q_) * (&p_ + 1) * &discriminant;
            let recursive_denominator = &a__ * (&p_ + 1) * &discriminant;
            if direct_denominator.is_zero() || recursive_denominator.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let n_minus_q = &n_ - &q_;
            let trinomial = &a__ * x_.pow(&q_)
                + &b__ * x_.pow(&n_)
                + &c__ * x_.pow(Atom::num(2) * &n_ - &q_);
            let direct = Atom::num(-1) * x_.pow(&m_ - &q_ + 1)
                * (b__.pow(2) - Atom::num(2) * &a__ * &c__ + &b__ * &c__ * x_.pow(&n_minus_q))
                * trinomial.pow(&p_ + 1)
                / direct_denominator;
            let recursive_integrand = x_.pow(&m_ - &q_) * trinomial.pow(&p_ + 1);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_)
                    + rubi_star(Atom::num(2) * &a__ * &c__ - b__.pow(2) * (&p_ + 2), recursive
                        / recursive_denominator)
        },
    ));
}

fn push_rules_rule_1970(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, p_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 1970,
        source: "Int[x_^m_.*(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^r_.)^p_,x_Symbol] :=
          -x^(m-2*n+q+1)*(2*a+b*x^(n-q))*(a*x^q+b*x^n+c*x^(2*n-q))^(p+1)/((n-q)*(p+1)*(b^2-4*a*c)) +
          1/((n-q)*(p+1)*(b^2-4*a*c)) \\[Star]
            Int[x^(m-2*n+q)*(2*a*(m+p*q-2*(n-q)+1)+b*(m+p*q+(n-q)*(2*p+1)+1)*x^(n-q))*(a*x^q+b*x^n+c*x^(2*n-q))^(p+1),x] /;
        FreeQ[{a,b,c},x] && EqQ[r,2*n-q] && PosQ[n-q] && Not[IntegerQ[p]] && NeQ[b^2-4*a*c,0] && IGtQ[n,0] && LtQ[p,-1] &&
          RationalQ[m,q] && GtQ[m+p*q+1,2*(n-q)]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [m_, a__, q_, b__, n_, c__, r_, p_, x_],
        optional: [m_, a__, q_, b__, n_, c__, r_],
        when: {
            freeq!([a__, b__, c__], x_)
                && eqq!(r_, Atom::num(2) * &n_ - &q_)
                && posq!(&n_ - &q_)
                && !integerq!(p_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && igtq!(n_, 0)
                && ltq!(p_, -1)
                && rationalq!([m_, q_])
                && gtq!(&m_ + &p_ * &q_ + 1, Atom::num(2) * (&n_ - &q_))
        },
        rhs: {
            let denominator = (&n_ - &q_) * (&p_ + 1) * (b__.pow(2) - Atom::num(4) * &a__ * &c__);
            if denominator.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let n_minus_q = &n_ - &q_;
            let trinomial = &a__ * x_.pow(&q_)
                + &b__ * x_.pow(&n_)
                + &c__ * x_.pow(Atom::num(2) * &n_ - &q_);
            let direct = Atom::num(-1) * x_.pow(&m_ - Atom::num(2) * &n_ + &q_ + 1)
                * (Atom::num(2) * &a__ + &b__ * x_.pow(&n_minus_q))
                * trinomial.pow(&p_ + 1)
                / &denominator;
            let payload = Atom::num(2) * &a__ * (&m_ + &p_ * &q_ - Atom::num(2) * (&n_ - &q_) + 1)
                + &b__ * (&m_ + &p_ * &q_ + (&n_ - &q_) * (Atom::num(2) * &p_ + 1) + 1)
                    * x_.pow(&n_minus_q);
            let recursive_integrand =
                x_.pow(&m_ - Atom::num(2) * &n_ + &q_) * payload * trinomial.pow(&p_ + 1);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_1971(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, p_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 1971,
        source: "Int[x_^m_.*(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^r_.)^p_,x_Symbol] :=
          -x^(m-q+1)*(b^2-2*a*c+b*c*x^(n-q))*(a*x^q+b*x^n+c*x^(2*n-q))^(p+1)/(a*(n-q)*(p+1)*(b^2-4*a*c)) +
          1/(a*(n-q)*(p+1)*(b^2-4*a*c)) \\[Star]
            Int[x^(m-q)*
              (b^2*(m+p*q+(n-q)*(p+1)+1)-2*a*c*(m+p*q+2*(n-q)*(p+1)+1)+b*c*(m+p*q+(n-q)*(2*p+3)+1)*x^(n-q))*
              (a*x^q+b*x^n+c*x^(2*n-q))^(p+1),x] /;
        FreeQ[{a,b,c},x] && EqQ[r,2*n-q] && PosQ[n-q] && Not[IntegerQ[p]] && NeQ[b^2-4*a*c,0] && IGtQ[n,0] && LtQ[p,-1] &&
          RationalQ[m,q] && LtQ[m+p*q+1,n-q]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [m_, a__, q_, b__, n_, c__, r_, p_, x_],
        optional: [m_, a__, q_, b__, n_, c__, r_],
        when: {
            freeq!([a__, b__, c__], x_)
                && eqq!(r_, Atom::num(2) * &n_ - &q_)
                && posq!(&n_ - &q_)
                && !integerq!(p_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && igtq!(n_, 0)
                && ltq!(p_, -1)
                && rationalq!([m_, q_])
                && ltq!(&m_ + &p_ * &q_ + 1, &n_ - &q_)
        },
        rhs: {
            let denominator =
                &a__ * (&n_ - &q_) * (&p_ + 1) * (b__.pow(2) - Atom::num(4) * &a__ * &c__);
            if denominator.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let n_minus_q = &n_ - &q_;
            let trinomial = &a__ * x_.pow(&q_)
                + &b__ * x_.pow(&n_)
                + &c__ * x_.pow(Atom::num(2) * &n_ - &q_);
            let direct = Atom::num(-1) * x_.pow(&m_ - &q_ + 1)
                * (b__.pow(2) - Atom::num(2) * &a__ * &c__ + &b__ * &c__ * x_.pow(&n_minus_q))
                * trinomial.pow(&p_ + 1)
                / &denominator;
            let payload = b__.pow(2) * (&m_ + &p_ * &q_ + (&n_ - &q_) * (&p_ + 1) + 1)
                - Atom::num(2)
                    * &a__
                    * &c__
                    * (&m_ + &p_ * &q_ + Atom::num(2) * (&n_ - &q_) * (&p_ + 1) + 1)
                + &b__
                    * &c__
                    * (&m_ + &p_ * &q_ + (&n_ - &q_) * (Atom::num(2) * &p_ + 3) + 1)
                    * x_.pow(&n_minus_q);
            let recursive_integrand = x_.pow(&m_ - &q_) * payload * trinomial.pow(&p_ + 1);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_1972(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, p_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 1972,
        source: "Int[x_^m_.*(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^r_.)^p_,x_Symbol] :=
          x^(m-n+1)*(b+2*c*x^(n-q))*(a*x^q+b*x^n+c*x^(2*n-q))^(p+1)/((n-q)*(p+1)*(b^2-4*a*c)) -
          1/((n-q)*(p+1)*(b^2-4*a*c)) \\[Star]
            Int[x^(m-n)*(b*(m+p*q-n+q+1)+2*c*(m+p*q+2*(n-q)*(p+1)+1)*x^(n-q))*(a*x^q+b*x^n+c*x^(2*n-q))^(p+1),x] /;
        FreeQ[{a,b,c},x] && EqQ[r,2*n-q] && PosQ[n-q] && Not[IntegerQ[p]] && NeQ[b^2-4*a*c,0] && IGtQ[n,0] && LtQ[p,-1] &&
          RationalQ[m,q] && LtQ[n-q,m+p*q+1,2*(n-q)]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [m_, a__, q_, b__, n_, c__, r_, p_, x_],
        optional: [m_, a__, q_, b__, n_, c__, r_],
        when: {
            let u = &m_ + &p_ * &q_ + 1;
            let lower = &n_ - &q_;
            let upper = Atom::num(2) * (&n_ - &q_);

            freeq!([a__, b__, c__], x_)
                && eqq!(r_, Atom::num(2) * &n_ - &q_)
                && posq!(&n_ - &q_)
                && !integerq!(p_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && igtq!(n_, 0)
                && ltq!(p_, -1)
                && rationalq!([m_, q_])
                && gtq!(u, lower)
                && ltq!(u, upper)
        },
        rhs: {
            let denominator = (&n_ - &q_) * (&p_ + 1) * (b__.pow(2) - Atom::num(4) * &a__ * &c__);
            if denominator.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let n_minus_q = &n_ - &q_;
            let trinomial = &a__ * x_.pow(&q_)
                + &b__ * x_.pow(&n_)
                + &c__ * x_.pow(Atom::num(2) * &n_ - &q_);
            let direct = x_.pow(&m_ - &n_ + 1)
                * (&b__ + Atom::num(2) * &c__ * x_.pow(&n_minus_q))
                * trinomial.pow(&p_ + 1)
                / &denominator;
            let payload = &b__ * (&m_ + &p_ * &q_ - &n_ + &q_ + 1)
                + Atom::num(2)
                    * &c__
                    * (&m_ + &p_ * &q_ + Atom::num(2) * (&n_ - &q_) * (&p_ + 1) + 1)
                    * x_.pow(&n_minus_q);
            let recursive_integrand = x_.pow(&m_ - &n_) * payload * trinomial.pow(&p_ + 1);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) - rubi_star(Atom::num(1) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_1973(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, p_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 1973,
        source: "Int[x_^m_.*(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^r_.)^p_,x_Symbol] :=
          x^(m-2*n+q+1)*(a*x^q+b*x^n+c*x^(2*n-q))^(p+1)/(2*c*(n-q)*(p+1)) -
          b/(2*c) \\[Star] Int[x^(m-n+q)*(a*x^q+b*x^n+c*x^(2*n-q))^p,x] /;
        FreeQ[{a,b,c},x] && EqQ[r,2*n-q] && PosQ[n-q] && Not[IntegerQ[p]] && NeQ[b^2-4*a*c,0] && IGtQ[n,0] && GeQ[p,-1] && LtQ[p,0] &&
          RationalQ[m,q] && EqQ[m+p*q+1,2*(n-q)]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [m_, a__, q_, b__, n_, c__, r_, p_, x_],
        optional: [m_, a__, q_, b__, n_, c__, r_],
        when: {
            freeq!([a__, b__, c__], x_)
                && eqq!(r_, Atom::num(2) * &n_ - &q_)
                && posq!(&n_ - &q_)
                && !integerq!(p_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && igtq!(n_, 0)
                && geq!(p_, -1)
                && ltq!(p_, 0)
                && rationalq!([m_, q_])
                && eqq!(&m_ + &p_ * &q_ + 1, Atom::num(2) * (&n_ - &q_))
        },
        rhs: {
            let direct_denominator = Atom::num(2) * &c__ * (&n_ - &q_) * (&p_ + 1);
            let recursive_denominator = Atom::num(2) * &c__;
            if direct_denominator.is_zero() || recursive_denominator.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let trinomial = &a__ * x_.pow(&q_)
                + &b__ * x_.pow(&n_)
                + &c__ * x_.pow(Atom::num(2) * &n_ - &q_);
            let direct =
                x_.pow(&m_ - Atom::num(2) * &n_ + &q_ + 1) * trinomial.pow(&p_ + 1)
                    / direct_denominator;
            let recursive_integrand = x_.pow(&m_ - &n_ + &q_) * trinomial.pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) - rubi_star(b__, recursive / recursive_denominator)
        },
    ));
}

fn push_rules_rule_1974(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, p_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 1974,
        source: "Int[x_^m_.*(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^r_.)^p_,x_Symbol] :=
          -x^(m-q+1)*(a*x^q+b*x^n+c*x^(2*n-q))^(p+1)/(2*a*(n-q)*(p+1)) -
          b/(2*a) \\[Star] Int[x^(m+n-q)*(a*x^q+b*x^n+c*x^(2*n-q))^p,x] /;
        FreeQ[{a,b,c},x] && EqQ[r,2*n-q] && PosQ[n-q] && Not[IntegerQ[p]] && NeQ[b^2-4*a*c,0] && IGtQ[n,0] && GeQ[p,-1] && LtQ[p,0] &&
          RationalQ[m,q] && EqQ[m+p*q+1,-2*(n-q)*(p+1)]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [m_, a__, q_, b__, n_, c__, r_, p_, x_],
        optional: [m_, a__, q_, b__, n_, c__, r_],
        when: {
            freeq!([a__, b__, c__], x_)
                && eqq!(r_, Atom::num(2) * &n_ - &q_)
                && posq!(&n_ - &q_)
                && !integerq!(p_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && igtq!(n_, 0)
                && geq!(p_, -1)
                && ltq!(p_, 0)
                && rationalq!([m_, q_])
                && eqq!(
                    &m_ + &p_ * &q_ + 1,
                    -Atom::num(2) * (&n_ - &q_) * (&p_ + 1)
                )
        },
        rhs: {
            let direct_denominator = Atom::num(2) * &a__ * (&n_ - &q_) * (&p_ + 1);
            let recursive_denominator = Atom::num(2) * &a__;
            if direct_denominator.is_zero() || recursive_denominator.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let trinomial = &a__ * x_.pow(&q_)
                + &b__ * x_.pow(&n_)
                + &c__ * x_.pow(Atom::num(2) * &n_ - &q_);
            let direct =
                Atom::num(-1) * x_.pow(&m_ - &q_ + 1) * trinomial.pow(&p_ + 1) / direct_denominator;
            let recursive_integrand = x_.pow(&m_ + &n_ - &q_) * trinomial.pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) - rubi_star(b__, recursive / recursive_denominator)
        },
    ));
}

fn push_rules_rule_1975(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, p_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 1975,
        source: "Int[x_^m_.*(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^r_.)^p_,x_Symbol] :=
          x^(m-2*n+q+1)*(a*x^q+b*x^n+c*x^(2*n-q))^(p+1)/(c*(m+p*q+2*(n-q)*p+1)) -
          1/(c*(m+p*q+2*(n-q)*p+1)) \\[Star]
            Int[x^(m-2*(n-q))*(a*(m+p*q-2*(n-q)+1)+b*(m+p*q+(n-q)*(p-1)+1)*x^(n-q))*(a*x^q+b*x^n+c*x^(2*n-q))^p,x] /;
        FreeQ[{a,b,c},x] && EqQ[r,2*n-q] && PosQ[n-q] && Not[IntegerQ[p]] && NeQ[b^2-4*a*c,0] && IGtQ[n,0] && GeQ[p,-1] && LtQ[p,0] &&
          RationalQ[m,q] && GtQ[m+p*q+1,2*(n-q)]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [m_, a__, q_, b__, n_, c__, r_, p_, x_],
        optional: [m_, a__, q_, b__, n_, c__, r_],
        when: {
            freeq!([a__, b__, c__], x_)
                && eqq!(r_, Atom::num(2) * &n_ - &q_)
                && posq!(&n_ - &q_)
                && !integerq!(p_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && igtq!(n_, 0)
                && geq!(p_, -1)
                && ltq!(p_, 0)
                && rationalq!([m_, q_])
                && gtq!(&m_ + &p_ * &q_ + 1, Atom::num(2) * (&n_ - &q_))
        },
        rhs: {
            let denominator = &c__ * (&m_ + &p_ * &q_ + Atom::num(2) * (&n_ - &q_) * &p_ + 1);
            if denominator.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let n_minus_q = &n_ - &q_;
            let trinomial = &a__ * x_.pow(&q_)
                + &b__ * x_.pow(&n_)
                + &c__ * x_.pow(Atom::num(2) * &n_ - &q_);
            let direct =
                x_.pow(&m_ - Atom::num(2) * &n_ + &q_ + 1) * trinomial.pow(&p_ + 1)
                    / &denominator;
            let payload = &a__ * (&m_ + &p_ * &q_ - Atom::num(2) * (&n_ - &q_) + 1)
                + &b__ * (&m_ + &p_ * &q_ + (&n_ - &q_) * (&p_ - 1) + 1)
                    * x_.pow(&n_minus_q);
            let recursive_integrand =
                x_.pow(&m_ - Atom::num(2) * (&n_ - &q_)) * payload * trinomial.pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) - rubi_star(Atom::num(1) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_1976(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, p_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 1976,
        source: "Int[x_^m_.*(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^r_.)^p_,x_Symbol] :=
          x^(m-q+1)*(a*x^q+b*x^n+c*x^(2*n-q))^(p+1)/(a*(m+p*q+1)) -
          1/(a*(m+p*q+1)) \\[Star]
            Int[x^(m+n-q)*(b*(m+p*q+(n-q)*(p+1)+1)+c*(m+p*q+2*(n-q)*(p+1)+1)*x^(n-q))*(a*x^q+b*x^n+c*x^(2*n-q))^p,x] /;
        FreeQ[{a,b,c},x] && EqQ[r,2*n-q] && PosQ[n-q] && Not[IntegerQ[p]] && NeQ[b^2-4*a*c,0] && IGtQ[n,0] && GeQ[p,-1] && LtQ[p,0] &&
          RationalQ[m,q] && LtQ[m+p*q+1,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [m_, a__, q_, b__, n_, c__, r_, p_, x_],
        optional: [m_, a__, q_, b__, n_, c__, r_],
        when: {
            freeq!([a__, b__, c__], x_)
                && eqq!(r_, Atom::num(2) * &n_ - &q_)
                && posq!(&n_ - &q_)
                && !integerq!(p_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && igtq!(n_, 0)
                && geq!(p_, -1)
                && ltq!(p_, 0)
                && rationalq!([m_, q_])
                && ltq!(&m_ + &p_ * &q_ + 1, 0)
        },
        rhs: {
            let denominator = &a__ * (&m_ + &p_ * &q_ + 1);
            if denominator.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let n_minus_q = &n_ - &q_;
            let trinomial = &a__ * x_.pow(&q_)
                + &b__ * x_.pow(&n_)
                + &c__ * x_.pow(Atom::num(2) * &n_ - &q_);
            let direct = x_.pow(&m_ - &q_ + 1) * trinomial.pow(&p_ + 1) / &denominator;
            let payload = &b__ * (&m_ + &p_ * &q_ + (&n_ - &q_) * (&p_ + 1) + 1)
                + &c__
                    * (&m_ + &p_ * &q_ + Atom::num(2) * (&n_ - &q_) * (&p_ + 1) + 1)
                    * x_.pow(&n_minus_q);
            let recursive_integrand =
                x_.pow(&m_ + &n_ - &q_) * payload * trinomial.pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) - rubi_star(Atom::num(1) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_1977(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, p_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 1977,
        source: "Int[x_^m_.*(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^r_.)^p_,x_Symbol] :=
          (a*x^q+b*x^n+c*x^(2*n-q))^p/(x^(p*q)*(a+b*x^(n-q)+c*x^(2*(n-q)))^p) \\[Star]
            Int[x^(m+p*q)*(a+b*x^(n-q)+c*x^(2*(n-q)))^p,x] /;
        FreeQ[{a,b,c,m,n,p,q},x] && EqQ[r,2*n-q] && Not[IntegerQ[p]] && PosQ[n-q]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [m_, a__, q_, b__, n_, c__, r_, p_, x_],
        optional: [m_, a__, q_, b__, n_, c__, r_],
        when: {
            freeq!([a__, b__, c__, m_, n_, p_, q_], x_)
                && eqq!(r_, Atom::num(2) * &n_ - &q_)
                && !integerq!(p_)
                && posq!(&n_ - &q_)
        },
        rhs: {
            let n_minus_q = &n_ - &q_;
            let trinomial = &a__ * x_.pow(&q_)
                + &b__ * x_.pow(&n_)
                + &c__ * x_.pow(Atom::num(2) * &n_ - &q_);
            let shifted_trinomial = &a__
                + &b__ * x_.pow(&n_minus_q)
                + &c__ * x_.pow(Atom::num(2) * &n_minus_q);
            let denominator = x_.pow(&p_ * &q_) * shifted_trinomial.pow(&p_);
            if denominator.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let recursive_integrand = x_.pow(&m_ + &p_ * &q_) * shifted_trinomial.pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(trinomial.pow(&p_), recursive / denominator)
        },
    ));
}

fn push_rules_rule_1978(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, m_, n_, p_, q_, r_, u__);
    rules.push(rubi_rule!(
        order: 1978,
        source: "Int[u_^m_.*(a_.*u_^q_.+b_.*u_^n_.+c_.*u_^r_.)^p_.,x_Symbol] :=
          1/Coefficient[u,x,1] \\[Star] Subst[Int[x^m*(a*x^q+b*x^n+c*x^(2*n-q))^p,x],x,u] /;
        FreeQ[{a,b,c,m,n,p,q},x] && EqQ[r,2*n-q] && LinearQ[u,x] && NeQ[u,x]",
        desc: "Integration by substitution",
        refs: [],
        pattern: u__.pow(m_) * (a__ * u__.pow(q_) + b__ * u__.pow(n_) + c__ * u__.pow(r_)).pow(p_),
        with: [u__, m_, a__, q_, b__, n_, c__, r_, p_, x_],
        optional: [m_, a__, q_, b__, n_, c__, r_, p_],
        when: {
            freeq!([a__, b__, c__, m_, n_, p_, q_], x_)
                && eqq!(r_, Atom::num(2) * &n_ - &q_)
                && rubi_linear_q(&u__, x_)
                && neq!(u__, x_)
        },
        rhs: {
            let coefficient = rubi_coefficient(&u__, x_, 1).rubi_rhs();
            if coefficient.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = sub_atom.pow(&m_)
                * (&a__ * sub_atom.pow(&q_)
                    + &b__ * sub_atom.pow(&n_)
                    + &c__ * sub_atom.pow(Atom::num(2) * &n_ - &q_))
                .pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);

            rubi_star(Atom::num(1) / coefficient, rubi_subst(&transformed, sub, u__))
        },
    ));
}

fn push_rules_rule_1961(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 1961,
        source: "Int[x_^m_./Sqrt[a_.*x_^q_.+b_.*x_^n_.+c_.*x_^r_.],x_Symbol] :=
          x^(q/2)*Sqrt[a+b*x^(n-q)+c*x^(2*(n-q))]/Sqrt[a*x^q+b*x^n+c*x^(2*n-q)] \\[Star]
            Int[x^(m-q/2)/Sqrt[a+b*x^(n-q)+c*x^(2*(n-q))],x] /;
        FreeQ[{a,b,c,m,n,q},x] && EqQ[r,2*n-q] && PosQ[n-q] && (EqQ[m,1] && EqQ[n,3] && EqQ[q,2]  ||
          (EqQ[m+1/2] || EqQ[m,3/2] || EqQ[m,1/2] || EqQ[m,5/2]) && EqQ[n,3] && EqQ[q,1])",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [m_, a__, q_, b__, n_, c__, r_, x_],
        optional: [m_, a__, q_, b__, n_, c__, r_],
        x_free: [a__, b__, c__, m_, n_, q_],
        when: {
            eqq!(r_, Atom::num(2) * &n_ - &q_)
                && posq!(&n_ - &q_)
                && (eqq!(m_, 1) && eqq!(n_, 3) && eqq!(q_, 2)
                    || (eqq!(&m_ + (1, 2), 0)
                        || eqq!(m_, (3, 2))
                        || eqq!(m_, (1, 2))
                        || eqq!(m_, (5, 2)))
                        && eqq!(n_, 3)
                        && eqq!(q_, 1))
        },
        rhs: {
            let original = &a__ * x_.pow(&q_)
                + &b__ * x_.pow(&n_)
                + &c__ * x_.pow(Atom::num(2) * &n_ - &q_);
            let reduced = &a__
                + &b__ * x_.pow(&n_ - &q_)
                + &c__ * x_.pow(Atom::num(2) * (&n_ - &q_));
            let coefficient = x_.pow(&q_ / 2) * reduced.sqrt() / original.sqrt();
            let recursive = rubi_rhs_int(
                &(x_.pow(&m_ - &q_ / 2) / reduced.sqrt()),
                x_,
            );

            rubi_star(coefficient, recursive)
        },
    ));
}

// Generated shared pattern builders.

#[inline(never)]
fn rubi_shared_pattern_0(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let q_ = symbols.q_;
    let r_ = symbols.r_;
    let x_ = symbols.x_;
    x_.pow(m_) * (a__ * x_.pow(q_) + b__ * x_.pow(n_) + c__ * x_.pow(r_)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let q_ = symbols.q_;
    let r_ = symbols.r_;
    let x_ = symbols.x_;
    x_.pow(m_)
        / (a__ * x_.pow(q_) + b__ * x_.pow(n_) + c__ * x_.pow(r_)).pow(Atom::num(3) / Atom::num(2))
}

#[inline(never)]
fn rubi_shared_pattern_2(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let q_ = symbols.q_;
    let r_ = symbols.r_;
    let x_ = symbols.x_;
    x_.pow(m_) / (a__ * x_.pow(q_) + b__ * x_.pow(n_) + c__ * x_.pow(r_)).sqrt()
}
