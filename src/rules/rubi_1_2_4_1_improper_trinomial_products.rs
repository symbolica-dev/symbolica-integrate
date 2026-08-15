use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_1949(rules);
    push_rules_rule_1950(rules);
    push_rules_rule_1951(rules);
    push_rules_rule_1952(rules);
    push_rules_rule_1953(rules);
    push_rules_rule_1954(rules);
    push_rules_rule_1955(rules);
    push_rules_rule_1956(rules);
    push_rules_rule_1957(rules);
}

fn push_rules_rule_1949(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, n_, p_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 1949,
        source: "Int[(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^r_.)^p_,x_Symbol] :=
          Int[x^(p*q)*(a+b*x^(n-q)+c*x^(2*(n-q)))^p,x] /;
        FreeQ[{a,b,c,n,q},x] && EqQ[r,2*n-q] && PosQ[n-q] && IntegerQ[p]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, q_, b__, n_, c__, r_, p_, x_],
        optional: [a__, q_, b__, n_, c__, r_],
        when: {
            freeq!([a__, b__, c__, n_, q_], x_)
                && eqq!(r_, Atom::num(2) * &n_ - &q_)
                && posq!(&n_ - &q_)
                && integerq!(p_)
        },
        rhs: {
            let n_minus_q = &n_ - &q_;
            let integrand = x_.pow(&p_ * &q_)
                * (&a__
                    + &b__ * x_.pow(&n_minus_q)
                    + &c__ * x_.pow(Atom::num(2) * &n_minus_q))
                .pow(&p_);

            rubi_rhs_int(&integrand, x_)
        },
    ));
}

fn push_rules_rule_1950(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, n_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 1950,
        source: "Int[Sqrt[a_.*x_^q_.+b_.*x_^n_.+c_.*x_^r_.],x_Symbol] :=
          Sqrt[a*x^q+b*x^n+c*x^(2*n-q)]/(x^(q/2)*Sqrt[a+b*x^(n-q)+c*x^(2*(n-q))]) \\[Star]
            Int[x^(q/2)*Sqrt[a+b*x^(n-q)+c*x^(2*(n-q))],x] /;
        FreeQ[{a,b,c,n,q},x] && EqQ[r,2*n-q] && PosQ[n-q]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: (a__ * x_.pow(q_) + b__ * x_.pow(n_) + c__ * x_.pow(r_)).sqrt(),
        with: [a__, q_, b__, n_, c__, r_, x_],
        optional: [a__, q_, b__, n_, c__, r_],
        when: {
            freeq!([a__, b__, c__, n_, q_], x_)
                && eqq!(r_, Atom::num(2) * &n_ - &q_)
                && posq!(&n_ - &q_)
        },
        rhs: {
            let n_minus_q = &n_ - &q_;
            let trinomial = &a__ * x_.pow(&q_) + &b__ * x_.pow(&n_)
                + &c__ * x_.pow(Atom::num(2) * &n_ - &q_);
            let shifted_trinomial = &a__
                + &b__ * x_.pow(&n_minus_q)
                + &c__ * x_.pow(Atom::num(2) * &n_minus_q);
            let denominator = x_.pow(&q_ / 2) * shifted_trinomial.sqrt();
            if denominator.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let recursive_integrand = x_.pow(&q_ / 2) * shifted_trinomial.sqrt();
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(trinomial.sqrt(), recursive / denominator)
        },
    ));
}

fn push_rules_rule_1951(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, n_, r_, x_);
    rules.push(rubi_rule!(
        order: 1951,
        source: "Int[1/Sqrt[a_.*x_^2+b_.*x_^n_.+c_.*x_^r_.],x_Symbol] :=
          -2/(n-2) \\[Star] Subst[Int[1/(4*a-x^2),x],x,x*(2*a+b*x^(n-2))/Sqrt[a*x^2+b*x^n+c*x^r]] /;
        FreeQ[{a,b,c,n,r},x] && EqQ[r,2*n-2] && PosQ[n-2] && NeQ[b^2-4*a*c,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: Atom::num(1) / (a__ * x_.pow(2) + b__ * x_.pow(n_) + c__ * x_.pow(r_)).sqrt(),
        with: [a__, b__, n_, c__, r_, x_],
        optional: [a__, b__, n_, c__, r_],
        when: {
            freeq!([a__, b__, c__, n_, r_], x_)
                && eqq!(r_, Atom::num(2) * &n_ - 2)
                && posq!(&n_ - 2)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
        },
        rhs: {
            let denominator = &n_ - 2;
            if denominator.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let sub_atom = Atom::var(sub);
            let trinomial = &a__ * x_.pow(2) + &b__ * x_.pow(&n_) + &c__ * x_.pow(&r_);
            let substitution =
                x_ * (Atom::num(2) * &a__ + &b__ * x_.pow(&n_ - 2)) / trinomial.sqrt();
            let transformed = rubi_rhs_int(&(Atom::num(1) / (Atom::num(4) * &a__ - sub_atom.pow(2))), sub);

            rubi_star(Atom::num(-2), rubi_subst(&transformed, sub, substitution) / denominator)
        },
    ));
}

fn push_rules_rule_1952(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, n_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 1952,
        source: "Int[1/Sqrt[a_.*x_^q_.+b_.*x_^n_.+c_.*x_^r_.],x_Symbol] :=
          x^(q/2)*Sqrt[a+b*x^(n-q)+c*x^(2*(n-q))]/Sqrt[a*x^q+b*x^n+c*x^(2*n-q)] \\[Star]
            Int[1/(x^(q/2)*Sqrt[a+b*x^(n-q)+c*x^(2*(n-q))]),x] /;
        FreeQ[{a,b,c,n,q},x] && EqQ[r,2*n-q] && PosQ[n-q]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: Atom::num(1) / (a__ * x_.pow(q_) + b__ * x_.pow(n_) + c__ * x_.pow(r_)).sqrt(),
        with: [a__, q_, b__, n_, c__, r_, x_],
        optional: [a__, q_, b__, n_, c__, r_],
        when: {
            freeq!([a__, b__, c__, n_, q_], x_)
                && eqq!(r_, Atom::num(2) * &n_ - &q_)
                && posq!(&n_ - &q_)
        },
        rhs: {
            let n_minus_q = &n_ - &q_;
            let trinomial = &a__ * x_.pow(&q_) + &b__ * x_.pow(&n_)
                + &c__ * x_.pow(Atom::num(2) * &n_ - &q_);
            let shifted_trinomial = &a__
                + &b__ * x_.pow(&n_minus_q)
                + &c__ * x_.pow(Atom::num(2) * &n_minus_q);
            let recursive_integrand =
                Atom::num(1) / (x_.pow(&q_ / 2) * shifted_trinomial.sqrt());
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(x_.pow(&q_ / 2) * shifted_trinomial.sqrt() / trinomial.sqrt(), recursive)
        },
    ));
}

fn push_rules_rule_1953(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, n_, p_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 1953,
        source: "Int[(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^r_.)^p_,x_Symbol] :=
          x*(a*x^q+b*x^n+c*x^(2*n-q))^p/(p*(2*n-q)+1) +
          (n-q)*p/(p*(2*n-q)+1) \\[Star]
            Int[x^q*(2*a+b*x^(n-q))*(a*x^q+b*x^n+c*x^(2*n-q))^(p-1),x] /;
        FreeQ[{a,b,c,n,q},x] && EqQ[r,2*n-q] && PosQ[n-q] && Not[IntegerQ[p]] && NeQ[b^2-4*a*c,0] && GtQ[p,0] && NeQ[p*(2*n-q)+1,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, q_, b__, n_, c__, r_, p_, x_],
        optional: [a__, q_, b__, n_, c__, r_],
        when: {
            freeq!([a__, b__, c__, n_, q_], x_)
                && eqq!(r_, Atom::num(2) * &n_ - &q_)
                && posq!(&n_ - &q_)
                && !integerq!(p_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && gtq!(p_, 0)
                && neq!(&p_ * (Atom::num(2) * &n_ - &q_) + 1, 0)
        },
        rhs: {
            let denominator = &p_ * (Atom::num(2) * &n_ - &q_) + 1;
            if denominator.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let n_minus_q = &n_ - &q_;
            let trinomial = &a__ * x_.pow(&q_) + &b__ * x_.pow(&n_)
                + &c__ * x_.pow(Atom::num(2) * &n_ - &q_);
            let direct = x_ * trinomial.pow(&p_) / &denominator;
            let recursive_integrand = x_.pow(&q_)
                * (Atom::num(2) * &a__ + &b__ * x_.pow(&n_minus_q))
                * trinomial.pow(&p_ - 1);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) + rubi_star((&n_ - &q_) * &p_ / denominator, recursive)
        },
    ));
}

fn push_rules_rule_1954(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, n_, p_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 1954,
        source: "Int[(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^r_.)^p_,x_Symbol] :=
          -x^(-q+1)*(b^2-2*a*c+b*c*x^(n-q))*(a*x^q+b*x^n+c*x^(2*n-q))^(p+1)/(a*(n-q)*(p+1)*(b^2-4*a*c)) +
          1/(a*(n-q)*(p+1)*(b^2-4*a*c)) \\[Star]
            Int[x^(-q)*((p*q+1)*(b^2-2*a*c)+(n-q)*(p+1)*(b^2-4*a*c)+b*c*(p*q+(n-q)*(2*p+3)+1)*x^(n-q))*(a*x^q+b*x^n+c*x^(2*n-q))^(p+1),x] /;
        FreeQ[{a,b,c,n,q},x] && EqQ[r,2*n-q] && PosQ[n-q] && Not[IntegerQ[p]] && NeQ[b^2-4*a*c,0] && LtQ[p,-1]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, q_, b__, n_, c__, r_, p_, x_],
        optional: [a__, q_, b__, n_, c__, r_],
        when: {
            freeq!([a__, b__, c__, n_, q_], x_)
                && eqq!(r_, Atom::num(2) * &n_ - &q_)
                && posq!(&n_ - &q_)
                && !integerq!(p_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && ltq!(p_, -1)
        },
        rhs: {
            let discriminant = b__.pow(2) - Atom::num(4) * &a__ * &c__;
            let direct_denominator = &a__ * (&n_ - &q_) * (&p_ + 1) * &discriminant;
            if direct_denominator.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let n_minus_q = &n_ - &q_;
            let trinomial = &a__ * x_.pow(&q_) + &b__ * x_.pow(&n_)
                + &c__ * x_.pow(Atom::num(2) * &n_ - &q_);
            let direct = Atom::num(-1) * x_.pow(-&q_ + 1)
                * (b__.pow(2) - Atom::num(2) * &a__ * &c__ + &b__ * &c__ * x_.pow(&n_minus_q))
                * trinomial.pow(&p_ + 1)
                / &direct_denominator;
            let payload =
                (&p_ * &q_ + 1) * (b__.pow(2) - Atom::num(2) * &a__ * &c__)
                    + (&n_ - &q_) * (&p_ + 1) * &discriminant
                    + &b__
                        * &c__
                        * (&p_ * &q_ + (&n_ - &q_) * (Atom::num(2) * &p_ + 3) + 1)
                        * x_.pow(&n_minus_q);
            let recursive_integrand = x_.pow(-&q_) * payload * trinomial.pow(&p_ + 1);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / &direct_denominator, recursive)
        },
    ));
}

fn push_rules_rule_1955(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, n_, p_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 1955,
        source: "Int[(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^r_.)^p_,x_Symbol] :=
          (a*x^q+b*x^n+c*x^(2*n-q))^p/(x^(p*q)*(a+b*x^(n-q)+c*x^(2*(n-q)))^p) \\[Star]
            Int[x^(p*q)*(a+b*x^(n-q)+c*x^(2*(n-q)))^p,x] /;
        FreeQ[{a,b,c,n,p,q},x] && EqQ[r,2*n-q] && PosQ[n-q] && Not[IntegerQ[p]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, q_, b__, n_, c__, r_, p_, x_],
        optional: [a__, q_, b__, n_, c__, r_],
        when: {
            freeq!([a__, b__, c__, n_, p_, q_], x_)
                && eqq!(r_, Atom::num(2) * &n_ - &q_)
                && posq!(&n_ - &q_)
                && !integerq!(p_)
        },
        rhs: {
            let n_minus_q = &n_ - &q_;
            let trinomial = &a__ * x_.pow(&q_) + &b__ * x_.pow(&n_)
                + &c__ * x_.pow(Atom::num(2) * &n_ - &q_);
            let shifted_trinomial = &a__
                + &b__ * x_.pow(&n_minus_q)
                + &c__ * x_.pow(Atom::num(2) * &n_minus_q);
            let denominator = x_.pow(&p_ * &q_) * shifted_trinomial.pow(&p_);
            if denominator.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let recursive_integrand = x_.pow(&p_ * &q_) * shifted_trinomial.pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(trinomial.pow(&p_), recursive / denominator)
        },
    ));
}

fn push_rules_rule_1956(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, n_, p_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 1956,
        source: "Int[(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^r_.)^p_,x_Symbol] :=
          Unintegrable[(a*x^q+b*x^n+c*x^(2*n-q))^p,x] /;
        FreeQ[{a,b,c,n,p,q},x] && EqQ[r,2*n-q]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, q_, b__, n_, c__, r_, p_, x_],
        optional: [a__, q_, b__, n_, c__, r_],
        when: {
            freeq!([a__, b__, c__, n_, p_, q_], x_)
                && eqq!(r_, Atom::num(2) * &n_ - &q_)
        },
        rhs: {
            let integrand = (&a__ * x_.pow(&q_)
                + &b__ * x_.pow(&n_)
                + &c__ * x_.pow(Atom::num(2) * &n_ - &q_))
            .pow(&p_);

            rubi_unintegrable(integrand, x_)
        },
    ));
}

fn push_rules_rule_1957(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, n_, p_, q_, r_, u__);
    rules.push(rubi_rule!(
        order: 1957,
        source: "Int[(a_.*u_^q_.+b_.*u_^n_.+c_.*u_^r_.)^p_,x_Symbol] :=
          1/Coefficient[u,x,1] \\[Star] Subst[Int[(a*x^q+b*x^n+c*x^(2*n-q))^p,x],x,u] /;
        FreeQ[{a,b,c,n,p,q},x] && EqQ[r,2*n-q] && LinearQ[u,x] && NeQ[u,x]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (a__ * u__.pow(q_) + b__ * u__.pow(n_) + c__ * u__.pow(r_)).pow(p_),
        with: [a__, u__, q_, b__, n_, c__, r_, p_, x_],
        optional: [a__, q_, b__, n_, c__, r_],
        when: {
            freeq!([a__, b__, c__, n_, p_, q_], x_)
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
            let transformed_integrand =
                (&a__ * sub_atom.pow(&q_) + &b__ * sub_atom.pow(&n_)
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
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let q_ = symbols.q_;
    let r_ = symbols.r_;
    let x_ = symbols.x_;
    (a__ * x_.pow(q_) + b__ * x_.pow(n_) + c__ * x_.pow(r_)).pow(p_)
}
