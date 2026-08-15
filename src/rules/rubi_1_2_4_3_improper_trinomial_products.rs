use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_1979(rules);
    push_rules_rule_1980(rules);
    push_rules_rule_1981(rules);
    push_rules_rule_1982(rules);
    push_rules_rule_1983(rules);
    push_rules_rule_1984(rules);
    push_rules_rule_1985(rules);
    push_rules_rule_1986(rules);
}

fn push_rules_rule_1979(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_a__,
        capital_b__,
        a__,
        b__,
        c__,
        j_,
        n_,
        p_,
        q_,
        r_,
        x_
    );
    rules.push(rubi_rule!(
        order: 1979,
        source: "Int[(A_+B_.*x_^r_.)*(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^j_.)^p_.,x_Symbol] :=
          Int[x^(p*q)*(A+B*x^(n-q))*(a+b*x^(n-q)+c*x^(2*(n-q)))^p,x] /;
        FreeQ[{a,b,c,A,B,n,q},x] && EqQ[r,n-q] && EqQ[j,2*n-q] && IntegerQ[p] && PosQ[n-q]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [capital_a__, capital_b__, r_, a__, q_, b__, n_, c__, j_, p_, x_],
        optional: [capital_b__, r_, a__, q_, b__, n_, c__, j_, p_],
        when: {
            freeq!([a__, b__, c__, capital_a__, capital_b__, n_, q_], x_)
                && eqq!(r_, &n_ - &q_)
                && eqq!(j_, Atom::num(2) * &n_ - &q_)
                && integerq!(p_)
                && posq!(&n_ - &q_)
        },
        rhs: {
            let n_minus_q = &n_ - &q_;
            let integrand = x_.pow(&p_ * &q_)
                * (&capital_a__ + &capital_b__ * x_.pow(&n_minus_q))
                * (&a__
                    + &b__ * x_.pow(&n_minus_q)
                    + &c__ * x_.pow(Atom::num(2) * &n_minus_q))
                .pow(&p_);

            rubi_rhs_int(&integrand, x_)
        },
    ));
}

fn push_rules_rule_1980(rules: &mut Vec<RubiRule>) {
    rubi_symb!(capital_a__, capital_b__, a__, b__, c__, j_, n_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 1980,
        source: "Int[(A_+B_.*x_^j_.)/Sqrt[a_.*x_^q_.+b_.*x_^n_.+c_.*x_^r_.],x_Symbol] :=
          x^(q/2)*Sqrt[a+b*x^(n-q)+c*x^(2*(n-q))]/Sqrt[a*x^q+b*x^n+c*x^(2*n-q)] \\[Star]
            Int[(A+B*x^(n-q))/(x^(q/2)*Sqrt[a+b*x^(n-q)+c*x^(2*(n-q))]),x] /;
        FreeQ[{a,b,c,A,B,n,q},x] && EqQ[j,n-q] && EqQ[r,2*n-q] && PosQ[n-q] && EqQ[n,3] && EqQ[q,2]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: (capital_a__ + capital_b__ * x_.pow(j_))
            / (a__ * x_.pow(q_) + b__ * x_.pow(n_) + c__ * x_.pow(r_)).sqrt(),
        with: [capital_a__, capital_b__, j_, a__, q_, b__, n_, c__, r_, x_],
        optional: [capital_b__, j_, a__, q_, b__, n_, c__, r_],
        when: {
            freeq!([a__, b__, c__, capital_a__, capital_b__, n_, q_], x_)
                && eqq!(j_, &n_ - &q_)
                && eqq!(r_, Atom::num(2) * &n_ - &q_)
                && posq!(&n_ - &q_)
                && eqq!(n_, 3)
                && eqq!(q_, 2)
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
            let recursive_denominator = x_.pow(&q_ / 2) * shifted_trinomial.sqrt();
            if direct_denominator.is_zero() || recursive_denominator.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let recursive_integrand =
                (&capital_a__ + &capital_b__ * x_.pow(&n_minus_q)) / recursive_denominator;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(x_.pow(&q_ / 2) * shifted_trinomial.sqrt() / direct_denominator, recursive)
        },
    ));
}

fn push_rules_rule_1981(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_a__,
        capital_b__,
        a__,
        b__,
        c__,
        j_,
        n_,
        p_,
        q_,
        r_,
        x_
    );
    rules.push(rubi_rule!(
        order: 1981,
        source: "Int[(A_+B_.*x_^r_.)*(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^j_.)^p_,x_Symbol] :=
          x*(b*B*(n-q)*p+A*c*(p*q+(n-q)*(2*p+1)+1)+B*c*(p*(2*n-q)+1)*x^(n-q))*(a*x^q+b*x^n+c*x^(2*n-q))^p/
            (c*(p*(2*n-q)+1)*(p*q+(n-q)*(2*p+1)+1)) +
          (n-q)*p/(c*(p*(2*n-q)+1)*(p*q+(n-q)*(2*p+1)+1)) \\[Star]
            Int[x^q*
              (2*a*A*c*(p*q+(n-q)*(2*p+1)+1)-a*b*B*(p*q+1)+(2*a*B*c*(p*(2*n-q)+1)+A*b*c*(p*q+(n-q)*(2*p+1)+1)-b^2*B*(p*q+(n-q)*p+1))*x^(n-q))*
              (a*x^q+b*x^n+c*x^(2*n-q))^(p-1),x] /;
        FreeQ[{a,b,c,A,B,n,q},x] && EqQ[r,n-q] && EqQ[j,2*n-q] && Not[IntegerQ[p]] && NeQ[b^2-4*a*c,0] && GtQ[p,0] &&
          NeQ[p*(2*n-q)+1,0] && NeQ[p*q+(n-q)*(2*p+1)+1,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [capital_a__, capital_b__, r_, a__, q_, b__, n_, c__, j_, p_, x_],
        optional: [capital_b__, r_, a__, q_, b__, n_, c__, j_],
        when: {
            freeq!([a__, b__, c__, capital_a__, capital_b__, n_, q_], x_)
                && eqq!(r_, &n_ - &q_)
                && eqq!(j_, Atom::num(2) * &n_ - &q_)
                && !integerq!(p_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && gtq!(p_, 0)
                && neq!(&p_ * (Atom::num(2) * &n_ - &q_) + 1, 0)
                && neq!(&p_ * &q_ + (&n_ - &q_) * (Atom::num(2) * &p_ + 1) + 1, 0)
        },
        rhs: {
            let factor1 = &p_ * (Atom::num(2) * &n_ - &q_) + 1;
            let factor2 = &p_ * &q_ + (&n_ - &q_) * (Atom::num(2) * &p_ + 1) + 1;
            let denominator = &c__ * &factor1 * &factor2;
            if denominator.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let n_minus_q = &n_ - &q_;
            let trinomial = &a__ * x_.pow(&q_)
                + &b__ * x_.pow(&n_)
                + &c__ * x_.pow(Atom::num(2) * &n_ - &q_);
            let direct = x_
                * (&b__ * &capital_b__ * (&n_ - &q_) * &p_
                    + &capital_a__ * &c__ * &factor2
                    + &capital_b__ * &c__ * &factor1 * x_.pow(&n_minus_q))
                * trinomial.pow(&p_)
                / &denominator;
            let payload = Atom::num(2) * &a__ * &capital_a__ * &c__ * &factor2
                - &a__ * &b__ * &capital_b__ * (&p_ * &q_ + 1)
                + (Atom::num(2) * &a__ * &capital_b__ * &c__ * &factor1
                    + &capital_a__ * &b__ * &c__ * &factor2
                    - b__.pow(2) * &capital_b__ * (&p_ * &q_ + (&n_ - &q_) * &p_ + 1))
                    * x_.pow(&n_minus_q);
            let recursive_integrand =
                x_.pow(&q_) * payload * trinomial.pow(&p_ - 1);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) + rubi_star((&n_ - &q_) * &p_ / denominator, recursive)
        },
    ));
}

fn push_rules_rule_1982(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_a__, capital_b__, a__, c__, j_, p_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 1982,
        source: "Int[(A_+B_.*x_^r_.)*(a_.*x_^q_.+c_.*x_^j_.)^p_,x_Symbol] :=
          With[{n=q+r},
          x*(A*(p*q+(n-q)*(2*p+1)+1)+B*(p*(2*n-q)+1)*x^(n-q))*(a*x^q+c*x^(2*n-q))^p/((p*(2*n-q)+1)*(p*q+(n-q)*(2*p+1)+1)) +
          (n-q)*p/((p*(2*n-q)+1)*(p*q+(n-q)*(2*p+1)+1)) \\[Star]
            Int[x^q*(2*a*A*(p*q+(n-q)*(2*p+1)+1)+(2*a*B*(p*(2*n-q)+1))*x^(n-q))*(a*x^q+c*x^(2*n-q))^(p-1),x] /;
         EqQ[j,2*n-q] && NeQ[p*(2*n-q)+1,0] && NeQ[p*q+(n-q)*(2*p+1)+1,0]] /;
        FreeQ[{a,c,A,B,q},x] && Not[IntegerQ[p]] && GtQ[p,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [capital_a__, capital_b__, r_, a__, q_, c__, j_, p_, x_],
        optional: [capital_b__, r_, a__, q_, c__, j_],
        when: {
            let n = &q_ + &r_;

            freeq!([a__, c__, capital_a__, capital_b__, q_], x_)
                && !integerq!(p_)
                && gtq!(p_, 0)
                && eqq!(j_, Atom::num(2) * &n - &q_)
                && neq!(&p_ * (Atom::num(2) * &n - &q_) + 1, 0)
                && neq!(&p_ * &q_ + (&n - &q_) * (Atom::num(2) * &p_ + 1) + 1, 0)
        },
        rhs: {
            let n = &q_ + &r_;
            let factor1 = &p_ * (Atom::num(2) * &n - &q_) + 1;
            let factor2 = &p_ * &q_ + (&n - &q_) * (Atom::num(2) * &p_ + 1) + 1;
            let denominator = &factor1 * &factor2;
            if denominator.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let n_minus_q = &n - &q_;
            let trinomial = &a__ * x_.pow(&q_) + &c__ * x_.pow(Atom::num(2) * &n - &q_);
            let direct = x_
                * (&capital_a__ * &factor2 + &capital_b__ * &factor1 * x_.pow(&n_minus_q))
                * trinomial.pow(&p_)
                / &denominator;
            let payload = Atom::num(2) * &a__ * &capital_a__ * &factor2
                + Atom::num(2) * &a__ * &capital_b__ * &factor1 * x_.pow(&n_minus_q);
            let recursive_integrand =
                x_.pow(&q_) * payload * trinomial.pow(&p_ - 1);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) + rubi_star((&n - &q_) * &p_ / denominator, recursive)
        },
    ));
}

fn push_rules_rule_1983(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        capital_a__,
        capital_b__,
        a__,
        b__,
        c__,
        j_,
        n_,
        p_,
        q_,
        r_,
        x_
    );
    rules.push(rubi_rule!(
        order: 1983,
        source: "Int[(A_+B_.*x_^r_.)*(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^j_.)^p_,x_Symbol] :=
          -x^(-q+1)*(A*b^2-a*b*B-2*a*A*c+(A*b-2*a*B)*c*x^(n-q))*(a*x^q+b*x^n+c*x^(2*n-q))^(p+1)/(a*(n-q)*(p+1)*(b^2-4*a*c)) +
          1/(a*(n-q)*(p+1)*(b^2-4*a*c)) \\[Star]
            Int[x^(-q)*
              ((A*b^2*(p*q+(n-q)*(p+1)+1)-a*b*B*(p*q+1)-2*a*A*c*(p*q+2*(n-q)*(p+1)+1)+(p*q+(n-q)*(2*p+3)+1)*(A*b-2*a*B)*c*x^(n-q))*
              (a*x^q+b*x^n+c*x^(2*n-q))^(p+1)),x] /;
        FreeQ[{a,b,c,A,B,n,q},x] && EqQ[r,n-q] && EqQ[j,2*n-q] && Not[IntegerQ[p]] && NeQ[b^2-4*a*c,0] && LtQ[p,-1]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [capital_a__, capital_b__, r_, a__, q_, b__, n_, c__, j_, p_, x_],
        optional: [capital_b__, r_, a__, q_, b__, n_, c__, j_],
        when: {
            freeq!([a__, b__, c__, capital_a__, capital_b__, n_, q_], x_)
                && eqq!(r_, &n_ - &q_)
                && eqq!(j_, Atom::num(2) * &n_ - &q_)
                && !integerq!(p_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && ltq!(p_, -1)
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
            let direct = Atom::num(-1) * x_.pow(-&q_ + 1)
                * (&capital_a__ * b__.pow(2)
                    - &a__ * &b__ * &capital_b__
                    - Atom::num(2) * &a__ * &capital_a__ * &c__
                    + (&capital_a__ * &b__ - Atom::num(2) * &a__ * &capital_b__)
                        * &c__
                        * x_.pow(&n_minus_q))
                * trinomial.pow(&p_ + 1)
                / &denominator;
            let payload = &capital_a__ * b__.pow(2) * (&p_ * &q_ + (&n_ - &q_) * (&p_ + 1) + 1)
                - &a__ * &b__ * &capital_b__ * (&p_ * &q_ + 1)
                - Atom::num(2)
                    * &a__
                    * &capital_a__
                    * &c__
                    * (&p_ * &q_ + Atom::num(2) * (&n_ - &q_) * (&p_ + 1) + 1)
                + (&p_ * &q_ + (&n_ - &q_) * (Atom::num(2) * &p_ + 3) + 1)
                    * (&capital_a__ * &b__ - Atom::num(2) * &a__ * &capital_b__)
                    * &c__
                    * x_.pow(&n_minus_q);
            let recursive_integrand = x_.pow(-&q_) * payload * trinomial.pow(&p_ + 1);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_1984(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; capital_a__, capital_b__, a__, c__, j_, p_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 1984,
        source: "Int[(A_+B_.*x_^r_.)*(a_.*x_^q_.+c_.*x_^j_.)^p_,x_Symbol] :=
          With[{n=q+r},
          -x^(-q+1)*(a*A*c+a*B*c*x^(n-q))*(a*x^q+c*x^(2*n-q))^(p+1)/(a*(n-q)*(p+1)*(2*a*c)) +
          1/(a*(n-q)*(p+1)*(2*a*c)) \\[Star]
            Int[x^(-q)*((a*A*c*(p*q+2*(n-q)*(p+1)+1)+a*B*c*(p*q+(n-q)*(2*p+3)+1)*x^(n-q))*(a*x^q+c*x^(2*n-q))^(p+1)),x] /;
         EqQ[j,2*n-q]] /;
        FreeQ[{a,c,A,B,q},x] && Not[IntegerQ[p]] && LtQ[p,-1]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [capital_a__, capital_b__, r_, a__, q_, c__, j_, p_, x_],
        optional: [capital_b__, r_, a__, q_, c__, j_],
        when: {
            let n = &q_ + &r_;

            freeq!([a__, c__, capital_a__, capital_b__, q_], x_)
                && !integerq!(p_)
                && ltq!(p_, -1)
                && eqq!(j_, Atom::num(2) * &n - &q_)
        },
        rhs: {
            let n = &q_ + &r_;
            let denominator = &a__ * (&n - &q_) * (&p_ + 1) * (Atom::num(2) * &a__ * &c__);
            if denominator.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let n_minus_q = &n - &q_;
            let trinomial = &a__ * x_.pow(&q_) + &c__ * x_.pow(Atom::num(2) * &n - &q_);
            let direct = Atom::num(-1) * x_.pow(-&q_ + 1)
                * (&a__ * &capital_a__ * &c__ + &a__ * &capital_b__ * &c__ * x_.pow(&n_minus_q))
                * trinomial.pow(&p_ + 1)
                / &denominator;
            let payload = &a__
                * &capital_a__
                * &c__
                * (&p_ * &q_ + Atom::num(2) * (&n - &q_) * (&p_ + 1) + 1)
                + &a__
                    * &capital_b__
                    * &c__
                    * (&p_ * &q_ + (&n - &q_) * (Atom::num(2) * &p_ + 3) + 1)
                    * x_.pow(&n_minus_q);
            let recursive_integrand = x_.pow(-&q_) * payload * trinomial.pow(&p_ + 1);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_1985(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        capital_a__,
        capital_b__,
        a__,
        b__,
        c__,
        j_,
        n_,
        p_,
        q_,
        r_,
        x_
    );
    rules.push(rubi_rule!(
        order: 1985,
        source: "Int[(A_+B_.*x_^j_.)*(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^r_.)^p_.,x_Symbol] :=
          Unintegrable[(A+B*x^(n-q))*(a*x^q+b*x^n+c*x^(2*n-q))^p,x] /;
        FreeQ[{a,b,c,A,B,n,p,q},x] && EqQ[j,n-q] && EqQ[r,2*n-q]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern: (capital_a__ + capital_b__ * x_.pow(j_))
            * (a__ * x_.pow(q_) + b__ * x_.pow(n_) + c__ * x_.pow(r_)).pow(p_),
        with: [capital_a__, capital_b__, j_, a__, q_, b__, n_, c__, r_, p_, x_],
        optional: [capital_b__, j_, a__, q_, b__, n_, c__, r_, p_],
        when: {
            let integrand = (&capital_a__ + &capital_b__ * x_.pow(&n_ - &q_))
                * (&a__ * x_.pow(&q_)
                    + &b__ * x_.pow(&n_)
                    + &c__ * x_.pow(Atom::num(2) * &n_ - &q_))
                .pow(&p_);
            freeq!([a__, b__, c__, capital_a__, capital_b__, n_, p_, q_], x_)
                && eqq!(j_, &n_ - &q_)
                && eqq!(r_, Atom::num(2) * &n_ - &q_)
                && !rubi_sum_q(&rubi_expand_integrand(&integrand, x_))
        },
        rhs: {
            let integrand = (&capital_a__ + &capital_b__ * x_.pow(&n_ - &q_))
                * (&a__ * x_.pow(&q_)
                    + &b__ * x_.pow(&n_)
                    + &c__ * x_.pow(Atom::num(2) * &n_ - &q_))
                .pow(&p_);

            rubi_unintegrable(integrand, x_)
        },
    ));
}

fn push_rules_rule_1986(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        capital_a__,
        capital_b__,
        a__,
        b__,
        c__,
        j_,
        n_,
        p_,
        q_,
        r_,
        u__
    );
    rules.push(rubi_rule!(
        order: 1986,
        source: "Int[(A_+B_.*u_^j_.)*(a_.*u_^q_.+b_.*u_^n_.+c_.*u_^r_.)^p_.,x_Symbol] :=
          1/Coefficient[u,x,1] \\[Star] Subst[Int[(A+B*x^(n-q))*(a*x^q+b*x^n+c*x^(2*n-q))^p,x],x,u] /;
        FreeQ[{a,b,c,A,B,n,p,q},x] && EqQ[j,n-q] && EqQ[r,2*n-q] && LinearQ[u,x] && NeQ[u,x]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (capital_a__ + capital_b__ * u__.pow(j_))
            * (a__ * u__.pow(q_) + b__ * u__.pow(n_) + c__ * u__.pow(r_)).pow(p_),
        with: [capital_a__, capital_b__, u__, j_, a__, q_, b__, n_, c__, r_, p_, x_],
        optional: [capital_b__, j_, a__, q_, b__, n_, c__, r_, p_],
        when: {
            freeq!([a__, b__, c__, capital_a__, capital_b__, n_, p_, q_], x_)
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
            let transformed_integrand = (&capital_a__ + &capital_b__ * sub_atom.pow(&n_ - &q_))
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
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let q_ = symbols.q_;
    let r_ = symbols.r_;
    let x_ = symbols.x_;
    (capital_a__ + capital_b__ * x_.pow(r_))
        * (a__ * x_.pow(q_) + b__ * x_.pow(n_) + c__ * x_.pow(j_)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let c__ = symbols.c__;
    let capital_a__ = symbols.capital_a__;
    let capital_b__ = symbols.capital_b__;
    let j_ = symbols.j_;
    let p_ = symbols.p_;
    let q_ = symbols.q_;
    let r_ = symbols.r_;
    let x_ = symbols.x_;
    (capital_a__ + capital_b__ * x_.pow(r_)) * (a__ * x_.pow(q_) + c__ * x_.pow(j_)).pow(p_)
}
