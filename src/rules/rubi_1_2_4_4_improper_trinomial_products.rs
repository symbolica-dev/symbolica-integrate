use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_1987(rules);
    push_rules_rule_1988(rules);
    push_rules_rule_1989(rules);
    push_rules_rule_1990(rules);
    push_rules_rule_1991(rules);
    push_rules_rule_1992(rules);
    push_rules_rule_1993(rules);
    push_rules_rule_1994(rules);
    push_rules_rule_1995(rules);
    push_rules_rule_1996(rules);
    push_rules_rule_1997(rules);
    push_rules_rule_1998(rules);
    push_rules_rule_1999(rules);
    push_rules_rule_2000(rules);
    push_rules_rule_2001(rules);
    push_rules_rule_2002(rules);
}

fn push_rules_rule_1987(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_a__,
        capital_b__,
        a__,
        b__,
        c__,
        j_,
        m_,
        n_,
        p_,
        q_,
        r_,
        x_
    );
    rules.push(rubi_rule!(
        order: 1987,
        source: "Int[x_^m_.*(A_+B_.*x_^r_.)*(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^j_.)^p_.,x_Symbol] :=
          Int[x^(m+p*q)*(A+B*x^(n-q))*(a+b*x^(n-q)+c*x^(2*(n-q)))^p,x] /;
        FreeQ[{a,b,c,A,B,m,n,q},x] && EqQ[r,n-q] && EqQ[j,2*n-q] && IntegerQ[p] && PosQ[n-q]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [m_, capital_a__, capital_b__, r_, a__, q_, b__, n_, c__, j_, p_, x_],
        optional: [m_, capital_b__, r_, a__, q_, b__, n_, c__, j_, p_],
        when: {
            freeq!([a__, b__, c__, capital_a__, capital_b__, m_, n_, q_], x_)
                && eqq!(r_, &n_ - &q_)
                && eqq!(j_, Atom::num(2) * &n_ - &q_)
                && integerq!(p_)
                && posq!(&n_ - &q_)
        },
        rhs: {
            let n_minus_q = &n_ - &q_;
            let integrand = x_.pow(&m_ + &p_ * &q_)
                * (&capital_a__ + &capital_b__ * x_.pow(&n_minus_q))
                * (&a__
                    + &b__ * x_.pow(&n_minus_q)
                    + &c__ * x_.pow(Atom::num(2) * &n_minus_q))
                .pow(&p_);

            rubi_rhs_int(&integrand, x_)
        },
    ));
}

fn push_rules_rule_1988(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_a__,
        capital_b__,
        a__,
        b__,
        c__,
        j_,
        m_,
        n_,
        p_,
        q_,
        r_,
        x_
    );
    rules.push(rubi_rule!(
        order: 1988,
        source: "Int[x_^m_.*(A_+B_.*x_^r_.)*(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^j_.)^p_.,x_Symbol] :=
          x^(m+1)*(A*(m+p*q+(n-q)*(2*p+1)+1)+B*(m+p*q+1)*x^(n-q))*(a*x^q+b*x^n+c*x^(2*n-q))^p/((m+p*q+1)*(m+p*q+(n-q)*(2*p+1)+1)) +
          (n-q)*p/((m+p*q+1)*(m+p*q+(n-q)*(2*p+1)+1)) \\[Star]
            Int[x^(n+m)*
              Simp[2*a*B*(m+p*q+1)-A*b*(m+p*q+(n-q)*(2*p+1)+1)+(b*B*(m+p*q+1)-2*A*c*(m+p*q+(n-q)*(2*p+1)+1))*x^(n-q),x]*
              (a*x^q+b*x^n+c*x^(2*n-q))^(p-1),x] /;
        FreeQ[{a,b,c,A,B},x] && EqQ[r,n-q] && EqQ[j,2*n-q] && Not[IntegerQ[p]] && NeQ[b^2-4*a*c,0] && IGtQ[n,0] && GtQ[p,0] &&
          RationalQ[m,q] && LeQ[m+p*q,-(n-q)] && NeQ[m+p*q+1,0] && NeQ[m+p*q+(n-q)*(2*p+1)+1,0]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [m_, capital_a__, capital_b__, r_, a__, q_, b__, n_, c__, j_, p_, x_],
        optional: [m_, capital_b__, r_, a__, q_, b__, n_, c__, j_, p_],
        when: {
            freeq!([a__, b__, c__, capital_a__, capital_b__], x_)
                && eqq!(r_, &n_ - &q_)
                && eqq!(j_, Atom::num(2) * &n_ - &q_)
                && !integerq!(p_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && igtq!(n_, 0)
                && gtq!(p_, 0)
                && rationalq!([m_, q_])
                && leq!(&m_ + &p_ * &q_, Atom::num(-1) * (&n_ - &q_))
                && neq!(&m_ + &p_ * &q_ + 1, 0)
                && neq!(&m_ + &p_ * &q_ + (&n_ - &q_) * (Atom::num(2) * &p_ + 1) + 1, 0)
        },
        rhs: {
            let factor1 = &m_ + &p_ * &q_ + 1;
            let factor2 = &m_ + &p_ * &q_ + (&n_ - &q_) * (Atom::num(2) * &p_ + 1) + 1;
            let denominator = &factor1 * &factor2;
            if denominator.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let n_minus_q = &n_ - &q_;
            let trinomial = &a__ * x_.pow(&q_)
                + &b__ * x_.pow(&n_)
                + &c__ * x_.pow(Atom::num(2) * &n_ - &q_);
            let direct = x_.pow(&m_ + 1)
                * (&capital_a__ * &factor2 + &capital_b__ * &factor1 * x_.pow(&n_minus_q))
                * trinomial.pow(&p_)
                / &denominator;
            let simp_payload = Atom::num(2) * &a__ * &capital_b__ * &factor1
                - &capital_a__ * &b__ * &factor2
                + (&b__ * &capital_b__ * &factor1 - Atom::num(2) * &capital_a__ * &c__ * &factor2)
                    * x_.pow(&n_minus_q);
            let recursive_integrand =
                x_.pow(&n_ + &m_) * rubi_simp(&simp_payload, x_) * trinomial.pow(&p_ - 1);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) + rubi_star((&n_ - &q_) * &p_ / denominator, recursive)
        },
    ));
}

fn push_rules_rule_1989(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_a__, capital_b__, a__, c__, j_, m_, p_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 1989,
        source: "Int[x_^m_.*(A_+B_.*x_^r_.)*(a_.*x_^q_.+c_.*x_^j_.)^p_.,x_Symbol] :=
          With[{n=q+r},
          x^(m+1)*(A*(m+p*q+(n-q)*(2*p+1)+1)+B*(m+p*q+1)*x^(n-q))*(a*x^q+c*x^(2*n-q))^p/((m+p*q+1)*(m+p*q+(n-q)*(2*p+1)+1)) +
          2*(n-q)*p/((m+p*q+1)*(m+p*q+(n-q)*(2*p+1)+1)) \\[Star]
            Int[x^(n+m)*Simp[a*B*(m+p*q+1)-A*c*(m+p*q+(n-q)*(2*p+1)+1)*x^(n-q),x]*(a*x^q+c*x^(2*n-q))^(p-1),x] /;
         EqQ[j,2*n-q] && IGtQ[n,0] && LeQ[m+p*q,-(n-q)] && NeQ[m+p*q+1,0] && NeQ[m+p*q+(n-q)*(2*p+1)+1,0]] /;
        FreeQ[{a,c,A,B},x] && Not[IntegerQ[p]] && RationalQ[m,p,q] && GtQ[p,0]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [m_, capital_a__, capital_b__, r_, a__, q_, c__, j_, p_, x_],
        optional: [m_, capital_b__, r_, a__, q_, c__, j_, p_],
        when: {
            let n = &q_ + &r_;

            freeq!([a__, c__, capital_a__, capital_b__], x_)
                && !integerq!(p_)
                && rationalq!([m_, p_, q_])
                && gtq!(p_, 0)
                && eqq!(j_, Atom::num(2) * &n - &q_)
                && igtq!(n, 0)
                && leq!(&m_ + &p_ * &q_, Atom::num(-1) * (&n - &q_))
                && neq!(&m_ + &p_ * &q_ + 1, 0)
                && neq!(&m_ + &p_ * &q_ + (&n - &q_) * (Atom::num(2) * &p_ + 1) + 1, 0)
        },
        rhs: {
            let n = &q_ + &r_;
            let factor1 = &m_ + &p_ * &q_ + 1;
            let factor2 = &m_ + &p_ * &q_ + (&n - &q_) * (Atom::num(2) * &p_ + 1) + 1;
            let denominator = &factor1 * &factor2;
            if denominator.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let n_minus_q = &n - &q_;
            let trinomial = &a__ * x_.pow(&q_) + &c__ * x_.pow(Atom::num(2) * &n - &q_);
            let direct = x_.pow(&m_ + 1)
                * (&capital_a__ * &factor2 + &capital_b__ * &factor1 * x_.pow(&n_minus_q))
                * trinomial.pow(&p_)
                / &denominator;
            let simp_payload = &a__ * &capital_b__ * &factor1
                - &capital_a__ * &c__ * &factor2 * x_.pow(&n_minus_q);
            let recursive_integrand =
                x_.pow(&n + &m_) * rubi_simp(&simp_payload, x_) * trinomial.pow(&p_ - 1);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) + rubi_star(Atom::num(2) * (&n - &q_) * &p_ / denominator, recursive)
        },
    ));
}

fn push_rules_rule_1990(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_a__,
        capital_b__,
        a__,
        b__,
        c__,
        j_,
        m_,
        n_,
        p_,
        q_,
        r_,
        x_
    );
    rules.push(rubi_rule!(
        order: 1990,
        source: "Int[x_^m_.*(A_+B_.*x_^r_.)*(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^j_.)^p_.,x_Symbol] :=
          x^(m-n+1)*(A*b-2*a*B-(b*B-2*A*c)*x^(n-q))*(a*x^q+b*x^n+c*x^(2*n-q))^(p+1)/((n-q)*(p+1)*(b^2-4*a*c)) +
          1/((n-q)*(p+1)*(b^2-4*a*c)) \\[Star]
            Int[x^(m-n)*
              Simp[(m+p*q-n+q+1)*(2*a*B-A*b)+(m+p*q+2*(n-q)*(p+1)+1)*(b*B-2*A*c)*x^(n-q),x]*
              (a*x^q+b*x^n+c*x^(2*n-q))^(p+1),x] /;
        FreeQ[{a,b,c,A,B},x] && EqQ[r,n-q] && EqQ[j,2*n-q] && Not[IntegerQ[p]] && NeQ[b^2-4*a*c,0] && IGtQ[n,0] && LtQ[p,-1] &&
          RationalQ[m,q] && GtQ[m+p*q,n-q-1]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [m_, capital_a__, capital_b__, r_, a__, q_, b__, n_, c__, j_, p_, x_],
        optional: [m_, capital_b__, r_, a__, q_, b__, n_, c__, j_, p_],
        when: {
            freeq!([a__, b__, c__, capital_a__, capital_b__], x_)
                && eqq!(r_, &n_ - &q_)
                && eqq!(j_, Atom::num(2) * &n_ - &q_)
                && !integerq!(p_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && igtq!(n_, 0)
                && ltq!(p_, -1)
                && rationalq!([m_, q_])
                && gtq!(&m_ + &p_ * &q_, &n_ - &q_ - 1)
        },
        rhs: {
            let discriminant = b__.pow(2) - Atom::num(4) * &a__ * &c__;
            let denominator = (&n_ - &q_) * (&p_ + 1) * &discriminant;
            if denominator.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let n_minus_q = &n_ - &q_;
            let trinomial = &a__ * x_.pow(&q_)
                + &b__ * x_.pow(&n_)
                + &c__ * x_.pow(Atom::num(2) * &n_ - &q_);
            let direct = x_.pow(&m_ - &n_ + 1)
                * (&capital_a__ * &b__
                    - Atom::num(2) * &a__ * &capital_b__
                    - (&b__ * &capital_b__ - Atom::num(2) * &capital_a__ * &c__)
                        * x_.pow(&n_minus_q))
                * trinomial.pow(&p_ + 1)
                / &denominator;
            let simp_payload = (&m_ + &p_ * &q_ - &n_ + &q_ + 1)
                * (Atom::num(2) * &a__ * &capital_b__ - &capital_a__ * &b__)
                + (&m_ + &p_ * &q_ + Atom::num(2) * (&n_ - &q_) * (&p_ + 1) + 1)
                    * (&b__ * &capital_b__ - Atom::num(2) * &capital_a__ * &c__)
                    * x_.pow(&n_minus_q);
            let recursive_integrand =
                x_.pow(&m_ - &n_) * rubi_simp(&simp_payload, x_) * trinomial.pow(&p_ + 1);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_1991(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_a__, capital_b__, a__, c__, j_, m_, p_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 1991,
        source: "Int[x_^m_.*(A_+B_.*x_^r_.)*(a_.*x_^q_.+c_.*x_^j_.)^p_.,x_Symbol] :=
          With[{n=q+r},
          x^(m-n+1)*(a*B-A*c*x^(n-q))*(a*x^q+c*x^(2*n-q))^(p+1)/(2*a*c*(n-q)*(p+1)) -
          1/(2*a*c*(n-q)*(p+1)) \\[Star]
            Int[x^(m-n)*Simp[a*B*(m+p*q-n+q+1)-A*c*(m+p*q+(n-q)*2*(p+1)+1)*x^(n-q),x]*(a*x^q+c*x^(2*n-q))^(p+1),x] /;
         EqQ[j,2*n-q] && IGtQ[n,0] && m+p*q>n-q-1] /;
        FreeQ[{a,c,A,B},x] && Not[IntegerQ[p]] && RationalQ[m,q] && LtQ[p,-1]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [m_, capital_a__, capital_b__, r_, a__, q_, c__, j_, p_, x_],
        optional: [m_, capital_b__, r_, a__, q_, c__, j_, p_],
        when: {
            let n = &q_ + &r_;

            freeq!([a__, c__, capital_a__, capital_b__], x_)
                && !integerq!(p_)
                && rationalq!([m_, q_])
                && ltq!(p_, -1)
                && eqq!(j_, Atom::num(2) * &n - &q_)
                && igtq!(n, 0)
                && gtq!(&m_ + &p_ * &q_, &n - &q_ - 1)
        },
        rhs: {
            let n = &q_ + &r_;
            let denominator = Atom::num(2) * &a__ * &c__ * (&n - &q_) * (&p_ + 1);
            if denominator.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let n_minus_q = &n - &q_;
            let trinomial = &a__ * x_.pow(&q_) + &c__ * x_.pow(Atom::num(2) * &n - &q_);
            let direct = x_.pow(&m_ - &n + 1)
                * (&a__ * &capital_b__ - &capital_a__ * &c__ * x_.pow(&n_minus_q))
                * trinomial.pow(&p_ + 1)
                / &denominator;
            let simp_payload = &a__ * &capital_b__ * (&m_ + &p_ * &q_ - &n + &q_ + 1)
                - &capital_a__
                    * &c__
                    * (&m_ + &p_ * &q_ + (&n - &q_) * Atom::num(2) * (&p_ + 1) + 1)
                    * x_.pow(&n_minus_q);
            let recursive_integrand =
                x_.pow(&m_ - &n) * rubi_simp(&simp_payload, x_) * trinomial.pow(&p_ + 1);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            direct - rubi_star(Atom::num(1) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_1992(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_a__,
        capital_b__,
        a__,
        b__,
        c__,
        j_,
        m_,
        n_,
        p_,
        q_,
        r_,
        x_
    );
    rules.push(rubi_rule!(
        order: 1992,
        source: "Int[x_^m_.*(A_+B_.*x_^r_.)*(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^j_.)^p_.,x_Symbol] :=
          x^(m+1)*(b*B*(n-q)*p+A*c*(m+p*q+(n-q)*(2*p+1)+1)+B*c*(m+p*q+2*(n-q)*p+1)*x^(n-q))*(a*x^q+b*x^n+c*x^(2*n-q))^p/
            (c*(m+p*(2*n-q)+1)*(m+p*q+(n-q)*(2*p+1)+1)) +
          (n-q)*p/(c*(m+p*(2*n-q)+1)*(m+p*q+(n-q)*(2*p+1)+1)) \\[Star]
            Int[x^(m+q)*
              Simp[2*a*A*c*(m+p*q+(n-q)*(2*p+1)+1)-a*b*B*(m+p*q+1)+
                (2*a*B*c*(m+p*q+2*(n-q)*p+1)+A*b*c*(m+p*q+(n-q)*(2*p+1)+1)-b^2*B*(m+p*q+(n-q)*p+1))*x^(n-q),x]*
              (a*x^q+b*x^n+c*x^(2*n-q))^(p-1),x] /;
        FreeQ[{a,b,c,A,B},x] && EqQ[r,n-q] && EqQ[j,2*n-q] && Not[IntegerQ[p]] && NeQ[b^2-4*a*c,0] && IGtQ[n,0] && GtQ[p,0] &&
          RationalQ[m,q] && GtQ[m+p*q,-(n-q)-1] && NeQ[m+p*(2*n-q)+1,0] && NeQ[m+p*q+(n-q)*(2*p+1)+1,0]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [m_, capital_a__, capital_b__, r_, a__, q_, b__, n_, c__, j_, p_, x_],
        optional: [m_, capital_b__, r_, a__, q_, b__, n_, c__, j_, p_],
        when: {
            freeq!([a__, b__, c__, capital_a__, capital_b__], x_)
                && eqq!(r_, &n_ - &q_)
                && eqq!(j_, Atom::num(2) * &n_ - &q_)
                && !integerq!(p_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && igtq!(n_, 0)
                && gtq!(p_, 0)
                && rationalq!([m_, q_])
                && gtq!(
                    &m_ + &p_ * &q_,
                    Atom::num(-1) * (&n_ - &q_) - Atom::num(1)
                )
                && neq!(&m_ + &p_ * (Atom::num(2) * &n_ - &q_) + 1, 0)
                && neq!(&m_ + &p_ * &q_ + (&n_ - &q_) * (Atom::num(2) * &p_ + 1) + 1, 0)
        },
        rhs: {
            let factor1 = &m_ + &p_ * (Atom::num(2) * &n_ - &q_) + 1;
            let factor2 = &m_ + &p_ * &q_ + (&n_ - &q_) * (Atom::num(2) * &p_ + 1) + 1;
            let factor3 = &m_ + &p_ * &q_ + Atom::num(2) * (&n_ - &q_) * &p_ + 1;
            let denominator = &c__ * &factor1 * &factor2;
            if denominator.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let n_minus_q = &n_ - &q_;
            let trinomial = &a__ * x_.pow(&q_)
                + &b__ * x_.pow(&n_)
                + &c__ * x_.pow(Atom::num(2) * &n_ - &q_);
            let direct = x_.pow(&m_ + 1)
                * (&b__ * &capital_b__ * (&n_ - &q_) * &p_
                    + &capital_a__ * &c__ * &factor2
                    + &capital_b__ * &c__ * &factor3 * x_.pow(&n_minus_q))
                * trinomial.pow(&p_)
                / &denominator;
            let simp_payload = Atom::num(2) * &a__ * &capital_a__ * &c__ * &factor2
                - &a__ * &b__ * &capital_b__ * (&m_ + &p_ * &q_ + 1)
                + (Atom::num(2) * &a__ * &capital_b__ * &c__ * &factor3
                    + &capital_a__ * &b__ * &c__ * &factor2
                    - b__.pow(2) * &capital_b__ * (&m_ + &p_ * &q_ + (&n_ - &q_) * &p_ + 1))
                    * x_.pow(&n_minus_q);
            let recursive_integrand =
                x_.pow(&m_ + &q_) * rubi_simp(&simp_payload, x_) * trinomial.pow(&p_ - 1);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) + rubi_star((&n_ - &q_) * &p_ / denominator, recursive)
        },
    ));
}

fn push_rules_rule_1993(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_a__, capital_b__, a__, c__, j_, m_, p_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 1993,
        source: "Int[x_^m_.*(A_+B_.*x_^r_.)*(a_.*x_^q_.+c_.*x_^j_.)^p_.,x_Symbol] :=
          With[{n=q+r},
          x^(m+1)*(A*(m+p*q+(n-q)*(2*p+1)+1)+B*(m+p*q+2*(n-q)*p+1)*x^(n-q))*(a*x^q+c*x^(2*n-q))^p/
            ((m+p*(2*n-q)+1)*(m+p*q+(n-q)*(2*p+1)+1)) +
          (n-q)*p/((m+p*(2*n-q)+1)*(m+p*q+(n-q)*(2*p+1)+1)) \\[Star]
            Int[x^(m+q)*Simp[2*a*A*(m+p*q+(n-q)*(2*p+1)+1)+2*a*B*(m+p*q+2*(n-q)*p+1)*x^(n-q),x]*(a*x^q+c*x^(2*n-q))^(p-1),x] /;
         EqQ[j,2*n-q] && IGtQ[n,0] && GtQ[m+p*q,-(n-q)] && NeQ[m+p*q+2*(n-q)*p+1,0] && NeQ[m+p*q+(n-q)*(2*p+1)+1,0] && NeQ[m+1,n]] /;
        FreeQ[{a,c,A,B},x] && Not[IntegerQ[p]] && RationalQ[m,q] && GtQ[p,0]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [m_, capital_a__, capital_b__, r_, a__, q_, c__, j_, p_, x_],
        optional: [m_, capital_b__, r_, a__, q_, c__, j_, p_],
        when: {
            let n = &q_ + &r_;

            freeq!([a__, c__, capital_a__, capital_b__], x_)
                && !integerq!(p_)
                && rationalq!([m_, q_])
                && gtq!(p_, 0)
                && eqq!(j_, Atom::num(2) * &n - &q_)
                && igtq!(n, 0)
                && gtq!(&m_ + &p_ * &q_, Atom::num(-1) * (&n - &q_))
                && neq!(&m_ + &p_ * &q_ + Atom::num(2) * (&n - &q_) * &p_ + 1, 0)
                && neq!(&m_ + &p_ * &q_ + (&n - &q_) * (Atom::num(2) * &p_ + 1) + 1, 0)
                && neq!(&m_ + 1, n)
        },
        rhs: {
            let n = &q_ + &r_;
            let factor1 = &m_ + &p_ * (Atom::num(2) * &n - &q_) + 1;
            let factor2 = &m_ + &p_ * &q_ + (&n - &q_) * (Atom::num(2) * &p_ + 1) + 1;
            let factor3 = &m_ + &p_ * &q_ + Atom::num(2) * (&n - &q_) * &p_ + 1;
            let denominator = &factor1 * &factor2;
            if denominator.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let n_minus_q = &n - &q_;
            let trinomial = &a__ * x_.pow(&q_) + &c__ * x_.pow(Atom::num(2) * &n - &q_);
            let direct = x_.pow(&m_ + 1)
                * (&capital_a__ * &factor2 + &capital_b__ * &factor3 * x_.pow(&n_minus_q))
                * trinomial.pow(&p_)
                / &denominator;
            let simp_payload = Atom::num(2) * &a__ * &capital_a__ * &factor2
                + Atom::num(2) * &a__ * &capital_b__ * &factor3 * x_.pow(&n_minus_q);
            let recursive_integrand =
                x_.pow(&m_ + &q_) * rubi_simp(&simp_payload, x_) * trinomial.pow(&p_ - 1);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) + rubi_star((&n - &q_) * &p_ / denominator, recursive)
        },
    ));
}

fn push_rules_rule_1994(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_a__,
        capital_b__,
        a__,
        b__,
        c__,
        j_,
        m_,
        n_,
        p_,
        q_,
        r_,
        x_
    );
    rules.push(rubi_rule!(
        order: 1994,
        source: "Int[x_^m_.*(A_+B_.*x_^r_.)*(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^j_.)^p_.,x_Symbol] :=
          -x^(m-q+1)*(A*b^2-a*b*B-2*a*A*c+(A*b-2*a*B)*c*x^(n-q))*(a*x^q+b*x^n+c*x^(2*n-q))^(p+1)/(a*(n-q)*(p+1)*(b^2-4*a*c)) +
          1/(a*(n-q)*(p+1)*(b^2-4*a*c)) \\[Star]
            Int[x^(m-q)*
              Simp[A*b^2*(m+p*q+(n-q)*(p+1)+1)-a*b*B*(m+p*q+1)-2*a*A*c*(m+p*q+2*(n-q)*(p+1)+1)+
                (m+p*q+(n-q)*(2*p+3)+1)*(A*b-2*a*B)*c*x^(n-q),x]*
              (a*x^q+b*x^n+c*x^(2*n-q))^(p+1),x] /;
        FreeQ[{a,b,c,A,B},x] && EqQ[r,n-q] && EqQ[j,2*n-q] && Not[IntegerQ[p]] && NeQ[b^2-4*a*c,0] && IGtQ[n,0] && LtQ[p,-1] &&
          RationalQ[m,q] && m+p*q<n-q-1",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [m_, capital_a__, capital_b__, r_, a__, q_, b__, n_, c__, j_, p_, x_],
        optional: [m_, capital_b__, r_, a__, q_, b__, n_, c__, j_, p_],
        when: {
            freeq!([a__, b__, c__, capital_a__, capital_b__], x_)
                && eqq!(r_, &n_ - &q_)
                && eqq!(j_, Atom::num(2) * &n_ - &q_)
                && !integerq!(p_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && igtq!(n_, 0)
                && ltq!(p_, -1)
                && rationalq!([m_, q_])
                && ltq!(&m_ + &p_ * &q_, &n_ - &q_ - 1)
        },
        rhs: {
            let discriminant = b__.pow(2) - Atom::num(4) * &a__ * &c__;
            let denominator = &a__ * (&n_ - &q_) * (&p_ + 1) * &discriminant;
            if denominator.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let n_minus_q = &n_ - &q_;
            let trinomial = &a__ * x_.pow(&q_)
                + &b__ * x_.pow(&n_)
                + &c__ * x_.pow(Atom::num(2) * &n_ - &q_);
            let direct = Atom::num(-1) * x_.pow(&m_ - &q_ + 1)
                * (&capital_a__ * b__.pow(2)
                    - &a__ * &b__ * &capital_b__
                    - Atom::num(2) * &a__ * &capital_a__ * &c__
                    + (&capital_a__ * &b__ - Atom::num(2) * &a__ * &capital_b__)
                        * &c__
                        * x_.pow(&n_minus_q))
                * trinomial.pow(&p_ + 1)
                / &denominator;
            let simp_payload =
                &capital_a__ * b__.pow(2) * (&m_ + &p_ * &q_ + (&n_ - &q_) * (&p_ + 1) + 1)
                    - &a__ * &b__ * &capital_b__ * (&m_ + &p_ * &q_ + 1)
                    - Atom::num(2)
                        * &a__
                        * &capital_a__
                        * &c__
                        * (&m_ + &p_ * &q_ + Atom::num(2) * (&n_ - &q_) * (&p_ + 1) + 1)
                    + (&m_ + &p_ * &q_ + (&n_ - &q_) * (Atom::num(2) * &p_ + 3) + 1)
                        * (&capital_a__ * &b__ - Atom::num(2) * &a__ * &capital_b__)
                        * &c__
                        * x_.pow(&n_minus_q);
            let recursive_integrand =
                x_.pow(&m_ - &q_) * rubi_simp(&simp_payload, x_) * trinomial.pow(&p_ + 1);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_1995(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_a__, capital_b__, a__, c__, j_, m_, p_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 1995,
        source: "Int[x_^m_.*(A_+B_.*x_^r_.)*(a_.*x_^q_.+c_.*x_^j_.)^p_.,x_Symbol] :=
          With[{n=q+r},
          -x^(m-q+1)*(A*c+B*c*x^(n-q))*(a*x^q+c*x^(2*n-q))^(p+1)/(2*a*c*(n-q)*(p+1)) +
          1/(2*a*c*(n-q)*(p+1)) \\[Star]
            Int[x^(m-q)*Simp[A*c*(m+p*q+2*(n-q)*(p+1)+1)+B*(m+p*q+(n-q)*(2*p+3)+1)*c*x^(n-q),x]*(a*x^q+c*x^(2*n-q))^(p+1),x] /;
         EqQ[j,2*n-q] && IGtQ[n,0] && LtQ[m+p*q,n-q-1]] /;
        FreeQ[{a,c,A,B},x] && Not[IntegerQ[p]] && RationalQ[m,q] && LtQ[p,-1]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [m_, capital_a__, capital_b__, r_, a__, q_, c__, j_, p_, x_],
        optional: [m_, capital_b__, r_, a__, q_, c__, j_, p_],
        when: {
            let n = &q_ + &r_;

            freeq!([a__, c__, capital_a__, capital_b__], x_)
                && !integerq!(p_)
                && rationalq!([m_, q_])
                && ltq!(p_, -1)
                && eqq!(j_, Atom::num(2) * &n - &q_)
                && igtq!(n, 0)
                && ltq!(&m_ + &p_ * &q_, &n - &q_ - 1)
        },
        rhs: {
            let n = &q_ + &r_;
            let denominator = Atom::num(2) * &a__ * &c__ * (&n - &q_) * (&p_ + 1);
            if denominator.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let n_minus_q = &n - &q_;
            let trinomial = &a__ * x_.pow(&q_) + &c__ * x_.pow(Atom::num(2) * &n - &q_);
            let direct = Atom::num(-1) * x_.pow(&m_ - &q_ + 1)
                * (&capital_a__ * &c__ + &capital_b__ * &c__ * x_.pow(&n_minus_q))
                * trinomial.pow(&p_ + 1)
                / &denominator;
            let simp_payload = &capital_a__
                * &c__
                * (&m_ + &p_ * &q_ + Atom::num(2) * (&n - &q_) * (&p_ + 1) + 1)
                + &capital_b__
                    * (&m_ + &p_ * &q_ + (&n - &q_) * (Atom::num(2) * &p_ + 3) + 1)
                    * &c__
                    * x_.pow(&n_minus_q);
            let recursive_integrand =
                x_.pow(&m_ - &q_) * rubi_simp(&simp_payload, x_) * trinomial.pow(&p_ + 1);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_1996(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_a__,
        capital_b__,
        a__,
        b__,
        c__,
        j_,
        m_,
        n_,
        p_,
        q_,
        r_,
        x_
    );
    rules.push(rubi_rule!(
        order: 1996,
        source: "Int[x_^m_.*(A_+B_.*x_^r_.)*(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^j_.)^p_.,x_Symbol] :=
          B*x^(m-n+1)*(a*x^q+b*x^n+c*x^(2*n-q))^(p+1)/(c*(m+p*q+(n-q)*(2*p+1)+1)) -
          1/(c*(m+p*q+(n-q)*(2*p+1)+1)) \\[Star]
            Int[x^(m-n+q)*
              Simp[a*B*(m+p*q-n+q+1)+(b*B*(m+p*q+(n-q)*p+1)-A*c*(m+p*q+(n-q)*(2*p+1)+1))*x^(n-q),x]*
              (a*x^q+b*x^n+c*x^(2*n-q))^p,x] /;
        FreeQ[{a,b,c,A,B},x] && EqQ[r,n-q] && EqQ[j,2*n-q] && Not[IntegerQ[p]] && NeQ[b^2-4*a*c,0] && IGtQ[n,0] && GeQ[p,-1] && LtQ[p,0] &&
          RationalQ[m,q] && GeQ[m+p*q,n-q-1] && NeQ[m+p*q+(n-q)*(2*p+1)+1,0]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [m_, capital_a__, capital_b__, r_, a__, q_, b__, n_, c__, j_, p_, x_],
        optional: [m_, capital_b__, r_, a__, q_, b__, n_, c__, j_, p_],
        when: {
            freeq!([a__, b__, c__, capital_a__, capital_b__], x_)
                && eqq!(r_, &n_ - &q_)
                && eqq!(j_, Atom::num(2) * &n_ - &q_)
                && !integerq!(p_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && igtq!(n_, 0)
                && geq!(p_, -1)
                && ltq!(p_, 0)
                && rationalq!([m_, q_])
                && geq!(&m_ + &p_ * &q_, &n_ - &q_ - 1)
                && neq!(&m_ + &p_ * &q_ + (&n_ - &q_) * (Atom::num(2) * &p_ + 1) + 1, 0)
        },
        rhs: {
            let factor = &m_ + &p_ * &q_ + (&n_ - &q_) * (Atom::num(2) * &p_ + 1) + 1;
            let denominator = &c__ * &factor;
            if denominator.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let n_minus_q = &n_ - &q_;
            let trinomial = &a__ * x_.pow(&q_)
                + &b__ * x_.pow(&n_)
                + &c__ * x_.pow(Atom::num(2) * &n_ - &q_);
            let direct =
                &capital_b__ * x_.pow(&m_ - &n_ + 1) * trinomial.pow(&p_ + 1) / &denominator;
            let simp_payload = &a__ * &capital_b__ * (&m_ + &p_ * &q_ - &n_ + &q_ + 1)
                + (&b__ * &capital_b__ * (&m_ + &p_ * &q_ + (&n_ - &q_) * &p_ + 1)
                    - &capital_a__ * &c__ * &factor)
                    * x_.pow(&n_minus_q);
            let recursive_integrand =
                x_.pow(&m_ - &n_ + &q_) * rubi_simp(&simp_payload, x_) * trinomial.pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) - rubi_star(Atom::num(1) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_1997(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_a__, capital_b__, a__, c__, j_, m_, p_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 1997,
        source: "Int[x_^m_.*(A_+B_.*x_^r_.)*(a_.*x_^q_.+c_.*x_^j_.)^p_.,x_Symbol] :=
          With[{n=q+r},
          B*x^(m-n+1)*(a*x^q+c*x^(2*n-q))^(p+1)/(c*(m+p*q+(n-q)*(2*p+1)+1)) -
          1/(c*(m+p*q+(n-q)*(2*p+1)+1)) \\[Star]
            Int[x^(m-n+q)*Simp[a*B*(m+p*q-n+q+1)-A*c*(m+p*q+(n-q)*(2*p+1)+1)*x^(n-q),x]*(a*x^q+c*x^(2*n-q))^p,x] /;
         EqQ[j,2*n-q] && IGtQ[n,0] && GeQ[m+p*q,n-q-1] && NeQ[m+p*q+(n-q)*(2*p+1)+1,0]] /;
        FreeQ[{a,c,A,B},x] && Not[IntegerQ[p]] && RationalQ[m,p,q] && GeQ[p,-1] && LtQ[p,0]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [m_, capital_a__, capital_b__, r_, a__, q_, c__, j_, p_, x_],
        optional: [m_, capital_b__, r_, a__, q_, c__, j_, p_],
        when: {
            let n = &q_ + &r_;

            freeq!([a__, c__, capital_a__, capital_b__], x_)
                && !integerq!(p_)
                && rationalq!([m_, p_, q_])
                && geq!(p_, -1)
                && ltq!(p_, 0)
                && eqq!(j_, Atom::num(2) * &n - &q_)
                && igtq!(n, 0)
                && geq!(&m_ + &p_ * &q_, &n - &q_ - 1)
                && neq!(&m_ + &p_ * &q_ + (&n - &q_) * (Atom::num(2) * &p_ + 1) + 1, 0)
        },
        rhs: {
            let n = &q_ + &r_;
            let factor = &m_ + &p_ * &q_ + (&n - &q_) * (Atom::num(2) * &p_ + 1) + 1;
            let denominator = &c__ * &factor;
            if denominator.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let n_minus_q = &n - &q_;
            let trinomial = &a__ * x_.pow(&q_) + &c__ * x_.pow(Atom::num(2) * &n - &q_);
            let direct =
                &capital_b__ * x_.pow(&m_ - &n + 1) * trinomial.pow(&p_ + 1) / &denominator;
            let simp_payload = &a__ * &capital_b__ * (&m_ + &p_ * &q_ - &n + &q_ + 1)
                - &capital_a__ * &c__ * &factor * x_.pow(&n_minus_q);
            let recursive_integrand =
                x_.pow(&m_ - &n + &q_) * rubi_simp(&simp_payload, x_) * trinomial.pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) - rubi_star(Atom::num(1) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_1998(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_a__,
        capital_b__,
        a__,
        b__,
        c__,
        j_,
        m_,
        n_,
        p_,
        q_,
        r_,
        x_
    );
    rules.push(rubi_rule!(
        order: 1998,
        source: "Int[x_^m_.*(A_+B_.*x_^r_.)*(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^j_.)^p_.,x_Symbol] :=
          A*x^(m-q+1)*(a*x^q+b*x^n+c*x^(2*n-q))^(p+1)/(a*(m+p*q+1)) +
          1/(a*(m+p*q+1)) \\[Star]
            Int[x^(m+n-q)*
              Simp[a*B*(m+p*q+1)-A*b*(m+p*q+(n-q)*(p+1)+1)-A*c*(m+p*q+2*(n-q)*(p+1)+1)*x^(n-q),x]*
              (a*x^q+b*x^n+c*x^(2*n-q))^p,x] /;
        FreeQ[{a,b,c,A,B},x] && EqQ[r,n-q] && EqQ[j,2*n-q] && Not[IntegerQ[p]] && NeQ[b^2-4*a*c,0] && IGtQ[n,0] &&
          RationalQ[m,p,q] && (GeQ[p,-1] && LtQ[p,0] || EqQ[m+p*q+(n-q)*(2*p+1)+1,0]) && LeQ[m+p*q,-(n-q)] && NeQ[m+p*q+1,0]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [m_, capital_a__, capital_b__, r_, a__, q_, b__, n_, c__, j_, p_, x_],
        optional: [m_, capital_b__, r_, a__, q_, b__, n_, c__, j_, p_],
        when: {
            let factor2 = &m_ + &p_ * &q_ + (&n_ - &q_) * (Atom::num(2) * &p_ + 1) + 1;

            freeq!([a__, b__, c__, capital_a__, capital_b__], x_)
                && eqq!(r_, &n_ - &q_)
                && eqq!(j_, Atom::num(2) * &n_ - &q_)
                && !integerq!(p_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && igtq!(n_, 0)
                && rationalq!([m_, p_, q_])
                && ((geq!(p_, -1) && ltq!(p_, 0)) || eqq!(factor2, 0))
                && leq!(&m_ + &p_ * &q_, Atom::num(-1) * (&n_ - &q_))
                && neq!(&m_ + &p_ * &q_ + 1, 0)
        },
        rhs: {
            let factor1 = &m_ + &p_ * &q_ + 1;
            let denominator = &a__ * &factor1;
            if denominator.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let n_minus_q = &n_ - &q_;
            let trinomial = &a__ * x_.pow(&q_)
                + &b__ * x_.pow(&n_)
                + &c__ * x_.pow(Atom::num(2) * &n_ - &q_);
            let direct =
                &capital_a__ * x_.pow(&m_ - &q_ + 1) * trinomial.pow(&p_ + 1) / &denominator;
            let simp_payload = &a__ * &capital_b__ * &factor1
                - &capital_a__ * &b__ * (&m_ + &p_ * &q_ + (&n_ - &q_) * (&p_ + 1) + 1)
                - &capital_a__
                    * &c__
                    * (&m_ + &p_ * &q_ + Atom::num(2) * (&n_ - &q_) * (&p_ + 1) + 1)
                    * x_.pow(&n_minus_q);
            let recursive_integrand =
                x_.pow(&m_ + &n_ - &q_) * rubi_simp(&simp_payload, x_) * trinomial.pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_1999(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_a__, capital_b__, a__, c__, j_, m_, p_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 1999,
        source: "Int[x_^m_.*(A_+B_.*x_^r_.)*(a_.*x_^q_.+c_.*x_^j_.)^p_.,x_Symbol] :=
          With[{n=q+r},
          A*x^(m-q+1)*(a*x^q+c*x^(2*n-q))^(p+1)/(a*(m+p*q+1)) +
          1/(a*(m+p*q+1)) \\[Star]
            Int[x^(m+n-q)*Simp[a*B*(m+p*q+1)-A*c*(m+p*q+2*(n-q)*(p+1)+1)*x^(n-q),x]*(a*x^q+c*x^(2*n-q))^p,x] /;
         EqQ[j,2*n-q] && IGtQ[n,0] && (GeQ[p,-1] && LtQ[p,0] || EqQ[m+p*q+(n-q)*(2*p+1)+1,0]) && LeQ[m+p*q,-(n-q)] && NeQ[m+p*q+1,0]] /;
        FreeQ[{a,c,A,B},x] && Not[IntegerQ[p]] && RationalQ[m,p,q]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [m_, capital_a__, capital_b__, r_, a__, q_, c__, j_, p_, x_],
        optional: [m_, capital_b__, r_, a__, q_, c__, j_, p_],
        when: {
            let n = &q_ + &r_;
            let factor2 = &m_ + &p_ * &q_ + (&n - &q_) * (Atom::num(2) * &p_ + 1) + 1;

            freeq!([a__, c__, capital_a__, capital_b__], x_)
                && !integerq!(p_)
                && rationalq!([m_, p_, q_])
                && eqq!(j_, Atom::num(2) * &n - &q_)
                && igtq!(n, 0)
                && ((geq!(p_, -1) && ltq!(p_, 0)) || eqq!(factor2, 0))
                && leq!(&m_ + &p_ * &q_, Atom::num(-1) * (&n - &q_))
                && neq!(&m_ + &p_ * &q_ + 1, 0)
        },
        rhs: {
            let n = &q_ + &r_;
            let factor1 = &m_ + &p_ * &q_ + 1;
            let denominator = &a__ * &factor1;
            if denominator.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let n_minus_q = &n - &q_;
            let trinomial = &a__ * x_.pow(&q_) + &c__ * x_.pow(Atom::num(2) * &n - &q_);
            let direct =
                &capital_a__ * x_.pow(&m_ - &q_ + 1) * trinomial.pow(&p_ + 1) / &denominator;
            let simp_payload = &a__ * &capital_b__ * &factor1
                - &capital_a__
                    * &c__
                    * (&m_ + &p_ * &q_ + Atom::num(2) * (&n - &q_) * (&p_ + 1) + 1)
                    * x_.pow(&n_minus_q);
            let recursive_integrand =
                x_.pow(&m_ + &n - &q_) * rubi_simp(&simp_payload, x_) * trinomial.pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_2000(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        capital_a__,
        capital_b__,
        a__,
        b__,
        c__,
        j_,
        m_,
        n_,
        q_,
        r_,
        x_
    );
    rules.push(rubi_rule!(
        order: 2000,
        source: "Int[x_^m_.*(A_+B_.*x_^j_.)/Sqrt[a_.*x_^q_.+b_.*x_^n_.+c_.*x_^r_.],x_Symbol] :=
          x^(q/2)*Sqrt[a+b*x^(n-q)+c*x^(2*(n-q))]/Sqrt[a*x^q+b*x^n+c*x^(2*n-q)] \\[Star]
            Int[x^(m-q/2)*(A+B*x^(n-q))/Sqrt[a+b*x^(n-q)+c*x^(2*(n-q))],x] /;
        FreeQ[{a,b,c,A,B,m,n,q},x] && EqQ[j,n-q] && EqQ[r,2*n-q] && PosQ[n-q] &&
        \t(EqQ[m,1/2] || EqQ[m,-1/2]) && EqQ[n,3] && EqQ[q,1]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: x_.pow(m_)
            * (capital_a__ + capital_b__ * x_.pow(j_))
            / (a__ * x_.pow(q_) + b__ * x_.pow(n_) + c__ * x_.pow(r_)).sqrt(),
        with: [m_, capital_a__, capital_b__, j_, a__, q_, b__, n_, c__, r_, x_],
        optional: [m_, capital_b__, j_, a__, q_, b__, n_, c__, r_],
        when: {
            freeq!([a__, b__, c__, capital_a__, capital_b__, m_, n_, q_], x_)
                && eqq!(j_, &n_ - &q_)
                && eqq!(r_, Atom::num(2) * &n_ - &q_)
                && posq!(&n_ - &q_)
                && (eqq!(m_, Atom::num(1) / Atom::num(2))
                    || eqq!(m_, -Atom::num(1) / Atom::num(2)))
                && eqq!(n_, 3)
                && eqq!(q_, 1)
        },
        rhs: {
            let n_minus_q = &n_ - &q_;
            let trinomial = &a__ * x_.pow(&q_)
                + &b__ * x_.pow(&n_)
                + &c__ * x_.pow(Atom::num(2) * &n_ - &q_);
            let shifted_trinomial = &a__
                + &b__ * x_.pow(&n_minus_q)
                + &c__ * x_.pow(Atom::num(2) * &n_minus_q);
            let direct_denominator = trinomial.sqrt();
            let recursive_denominator = shifted_trinomial.sqrt();
            if direct_denominator.is_zero() || recursive_denominator.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let recursive_integrand = x_.pow(&m_ - &q_ / 2)
                * (&capital_a__ + &capital_b__ * x_.pow(&n_minus_q))
                / recursive_denominator;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(x_.pow(&q_ / 2) * shifted_trinomial.sqrt() / direct_denominator, recursive)
        },
    ));
}

fn push_rules_rule_2001(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        capital_a__,
        capital_b__,
        a__,
        b__,
        c__,
        j_,
        k_,
        m_,
        n_,
        p_,
        q_,
        x_
    );
    rules.push(rubi_rule!(
        order: 2001,
        source: "Int[x_^m_.*(A_+B_.*x_^q_)*(a_.*x_^j_.+b_.*x_^k_.+c_.*x_^n_.)^p_,x_Symbol] :=
          (a*x^j+b*x^k+c*x^n)^p/(x^(j*p)*(a+b*x^(k-j)+c*x^(2*(k-j)))^p) \\[Star]
            Int[x^(m+j*p)*(A+B*x^(k-j))*(a+b*x^(k-j)+c*x^(2*(k-j)))^p,x] /;
        FreeQ[{a,b,c,A,B,j,k,m,p},x] && EqQ[q,k-j] && EqQ[n,2*k-j] && Not[IntegerQ[p]] && PosQ[k-j]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: x_.pow(m_)
            * (capital_a__ + capital_b__ * x_.pow(q_))
            * (a__ * x_.pow(j_) + b__ * x_.pow(k_) + c__ * x_.pow(n_)).pow(p_),
        with: [m_, capital_a__, capital_b__, q_, a__, j_, b__, k_, c__, n_, p_, x_],
        optional: [m_, capital_b__, a__, j_, b__, k_, c__, n_],
        when: {
            freeq!([a__, b__, c__, capital_a__, capital_b__, j_, k_, m_, p_], x_)
                && eqq!(q_, &k_ - &j_)
                && eqq!(n_, Atom::num(2) * &k_ - &j_)
                && !integerq!(p_)
                && posq!(&k_ - &j_)
        },
        rhs: {
            let k_minus_j = &k_ - &j_;
            let trinomial = &a__ * x_.pow(&j_)
                + &b__ * x_.pow(&k_)
                + &c__ * x_.pow(Atom::num(2) * &k_ - &j_);
            let shifted_trinomial = &a__
                + &b__ * x_.pow(&k_minus_j)
                + &c__ * x_.pow(Atom::num(2) * &k_minus_j);
            let denominator = x_.pow(&j_ * &p_) * shifted_trinomial.pow(&p_);
            if denominator.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let recursive_integrand = x_.pow(&m_ + &j_ * &p_)
                * (&capital_a__ + &capital_b__ * x_.pow(&k_minus_j))
                * shifted_trinomial.pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(trinomial.pow(&p_), recursive / denominator)
        },
    ));
}

fn push_rules_rule_2002(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        capital_a__,
        capital_b__,
        a__,
        b__,
        c__,
        j_,
        m_,
        n_,
        p_,
        q_,
        r_,
        u__
    );
    rules.push(rubi_rule!(
        order: 2002,
        source: "Int[u_^m_.*(A_+B_.*u_^j_.)*(a_.*u_^q_.+b_.*u_^n_.+c_.*u_^r_.)^p_.,x_Symbol] :=
          1/Coefficient[u,x,1] \\[Star] Subst[Int[x^m*(A+B*x^(n-q))*(a*x^q+b*x^n+c*x^(2*n-q))^p,x],x,u] /;
        FreeQ[{a,b,c,A,B,m,n,p,q},x] && EqQ[j,n-q] && EqQ[r,2*n-q] && LinearQ[u,x] && NeQ[u,x]",
        desc: "Integration by substitution",
        refs: [],
        pattern: u__.pow(m_)
            * (capital_a__ + capital_b__ * u__.pow(j_))
            * (a__ * u__.pow(q_) + b__ * u__.pow(n_) + c__ * u__.pow(r_)).pow(p_),
        with: [u__, m_, capital_a__, capital_b__, j_, a__, q_, b__, n_, c__, r_, p_, x_],
        optional: [m_, capital_b__, j_, a__, q_, b__, n_, c__, r_, p_],
        when: {
            freeq!([a__, b__, c__, capital_a__, capital_b__, m_, n_, p_, q_], x_)
                && eqq!(j_, &n_ - &q_)
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
                * (&capital_a__ + &capital_b__ * sub_atom.pow(&n_ - &q_))
                * (&a__ * sub_atom.pow(&q_)
                    + &b__ * sub_atom.pow(&n_)
                    + &c__ * sub_atom.pow(Atom::num(2) * &n_ - &q_))
                .pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);

            rubi_star(Atom::num(1) / coefficient, rubi_subst(&transformed, sub, u__))
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
    let j_ = symbols.j_;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let q_ = symbols.q_;
    let r_ = symbols.r_;
    let x_ = symbols.x_;
    x_.pow(m_)
        * (capital_a__ + capital_b__ * x_.pow(r_))
        * (a__ * x_.pow(q_) + b__ * x_.pow(n_) + c__ * x_.pow(j_)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let c__ = symbols.c__;
    let capital_a__ = symbols.capital_a__;
    let capital_b__ = symbols.capital_b__;
    let j_ = symbols.j_;
    let m_ = symbols.m_;
    let p_ = symbols.p_;
    let q_ = symbols.q_;
    let r_ = symbols.r_;
    let x_ = symbols.x_;
    x_.pow(m_)
        * (capital_a__ + capital_b__ * x_.pow(r_))
        * (a__ * x_.pow(q_) + c__ * x_.pow(j_)).pow(p_)
}
