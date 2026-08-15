use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_1906(rules);
    push_rules_rule_1907(rules);
    push_rules_rule_1908(rules);
    push_rules_rule_1909(rules);
    push_rules_rule_1910(rules);
    push_rules_rule_1911(rules);
    push_rules_rule_1912(rules);
    push_rules_rule_1913(rules);
    push_rules_rule_1914(rules);
    push_rules_rule_1915(rules);
    push_rules_rule_1916(rules);
    push_rules_rule_1917(rules);
    push_rules_rule_1918(rules);
}

fn push_rules_rule_1906(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, j_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 1906,
        source: "Int[(a_.*x_^j_.+b_.*x_^n_.)^p_,x_Symbol] :=
          (a*x^j+b*x^n)^(p+1)/(b*(n-j)*(p+1)*x^(n-1)) /;
        FreeQ[{a,b,j,n,p},x] && Not[IntegerQ[p]] && NeQ[n,j] && EqQ[j*p-n+j+1,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, j_, n_, p_, x_],
        optional: [a__, b__, j_, n_],
        when: {
            freeq!([a__, b__, j_, n_, p_], x_)
                && !integerq!(p_)
                && neq!(n_, j_)
                && eqq!(&j_ * &p_ - &n_ + &j_ + Atom::num(1), 0)
        },
        rhs: {
            let denominator = &b__ * (&n_ - &j_) * (&p_ + Atom::num(1)) * x_.pow(&n_ - Atom::num(1));
            if denominator.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            rubi_simp(&((&a__ * x_.pow(&j_) + &b__ * x_.pow(&n_)).pow(&p_ + Atom::num(1)) / denominator), x_)
        },
    ));
}

fn push_rules_rule_1907(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, j_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 1907,
        source: "Int[(a_.*x_^j_.+b_.*x_^n_.)^p_,x_Symbol] :=
          -(a*x^j+b*x^n)^(p+1)/(a*(n-j)*(p+1)*x^(j-1)) +
          (n*p+n-j+1)/(a*(n-j)*(p+1)) \\[Star] Int[(a*x^j+b*x^n)^(p+1)/x^j,x] /;
        FreeQ[{a,b,j,n},x] && Not[IntegerQ[p]] && NeQ[n,j] && ILtQ[Simplify[(n*p+n-j+1)/(n-j)],0] && LtQ[p,-1]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, j_, n_, p_, x_],
        optional: [a__, b__, j_, n_],
        when: {
            if !(freeq!([a__, b__, j_, n_], x_)
                && !integerq!(p_)
                && neq!(n_, j_))
            {
                return ConditionResult::False;
            }

            let quotient = ((&n_ * &p_ + &n_ - &j_ + Atom::num(1)) / (&n_ - &j_))
                .together();
            iltq!(quotient, 0) && ltq!(p_, -1)
        },
        rhs: {
            let base = &a__ * x_.pow(&j_) + &b__ * x_.pow(&n_);
            let denominator = &a__ * (&n_ - &j_) * (&p_ + Atom::num(1));
            if denominator.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let recursive_integrand = base.pow(&p_ + Atom::num(1)) / x_.pow(&j_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(-base.pow(&p_ + Atom::num(1)) / (&denominator * x_.pow(&j_ - Atom::num(1)))), x_)
                    + rubi_star(&n_ * &p_ + &n_ - &j_ + Atom::num(1), recursive / denominator)
        },
    ));
}

fn push_rules_rule_1908(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, j_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 1908,
        source: "Int[(a_.*x_^j_.+b_.*x_^n_.)^p_,x_Symbol] :=
          (a*x^j+b*x^n)^(p+1)/(a*(j*p+1)*x^(j-1)) -
          b*(n*p+n-j+1)/(a*(j*p+1)) \\[Star] Int[x^(n-j)*(a*x^j+b*x^n)^p,x] /;
        FreeQ[{a,b,j,n,p},x] && Not[IntegerQ[p]] && NeQ[n,j] && ILtQ[Simplify[(n*p+n-j+1)/(n-j)],0] && NeQ[j*p+1,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, j_, n_, p_, x_],
        optional: [a__, b__, j_, n_],
        when: {
            if !(freeq!([a__, b__, j_, n_, p_], x_)
                && !integerq!(p_)
                && neq!(n_, j_))
            {
                return ConditionResult::False;
            }

            let quotient = ((&n_ * &p_ + &n_ - &j_ + Atom::num(1)) / (&n_ - &j_))
                .together();
            iltq!(quotient, 0) && neq!(&j_ * &p_ + Atom::num(1), 0)
        },
        rhs: {
            let base = &a__ * x_.pow(&j_) + &b__ * x_.pow(&n_);
            let denominator = &a__ * (&j_ * &p_ + Atom::num(1));
            if denominator.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let recursive_integrand = x_.pow(&n_ - &j_) * base.pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(base.pow(&p_ + Atom::num(1)) / (&denominator * x_.pow(&j_ - Atom::num(1)))), x_)
                    - rubi_star(&b__ * (&n_ * &p_ + &n_ - &j_ + Atom::num(1)) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_1909(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, j_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 1909,
        source: "Int[(a_.*x_^j_.+b_.*x_^n_.)^p_,x_Symbol] :=
          x*(a*x^j+b*x^n)^p/(j*p+1) -
          b*(n-j)*p/(j*p+1) \\[Star] Int[x^n*(a*x^j+b*x^n)^(p-1),x] /;
        FreeQ[{a,b},x] && Not[IntegerQ[p]] && LtQ[0,j,n] && GtQ[p,0] && LtQ[j*p+1,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, j_, n_, p_, x_],
        optional: [a__, b__, j_, n_],
        when: {
            freeq!([a__, b__], x_)
                && !integerq!(p_)
                && gtq!(j_, 0)
                && ltq!(j_, n_)
                && gtq!(p_, 0)
                && ltq!(&j_ * &p_ + Atom::num(1), 0)
        },
        rhs: {
            let base = &a__ * x_.pow(&j_) + &b__ * x_.pow(&n_);
            let denominator = &j_ * &p_ + Atom::num(1);
            if denominator.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let recursive_integrand = x_.pow(&n_) * base.pow(&p_ - Atom::num(1));
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(x_ * base.pow(&p_) / &denominator), x_)
                    - rubi_star(&b__ * (&n_ - &j_) * &p_ / denominator, recursive)
        },
    ));
}

fn push_rules_rule_1910(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, j_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 1910,
        source: "Int[(a_.*x_^j_.+b_.*x_^n_.)^p_,x_Symbol] :=
          x*(a*x^j+b*x^n)^p/(n*p+1) +
          a*(n-j)*p/(n*p+1) \\[Star] Int[x^j*(a*x^j+b*x^n)^(p-1),x] /;
        FreeQ[{a,b},x] && Not[IntegerQ[p]] && LtQ[0,j,n] && GtQ[p,0] && NeQ[n*p+1,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, j_, n_, p_, x_],
        optional: [a__, b__, j_, n_],
        when: {
            freeq!([a__, b__], x_)
                && !integerq!(p_)
                && gtq!(j_, 0)
                && ltq!(j_, n_)
                && gtq!(p_, 0)
                && neq!(&n_ * &p_ + Atom::num(1), 0)
        },
        rhs: {
            let base = &a__ * x_.pow(&j_) + &b__ * x_.pow(&n_);
            let denominator = &n_ * &p_ + Atom::num(1);
            if denominator.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let recursive_integrand = x_.pow(&j_) * base.pow(&p_ - Atom::num(1));
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(x_ * base.pow(&p_) / &denominator), x_)
                    + rubi_star(&a__ * (&n_ - &j_) * &p_ / denominator, recursive)
        },
    ));
}

fn push_rules_rule_1911(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, j_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 1911,
        source: "Int[(a_.*x_^j_.+b_.*x_^n_.)^p_,x_Symbol] :=
          (a*x^j+b*x^n)^(p+1)/(b*(n-j)*(p+1)*x^(n-1)) -
          (j*p-n+j+1)/(b*(n-j)*(p+1)) \\[Star] Int[(a*x^j+b*x^n)^(p+1)/x^n,x] /;
        FreeQ[{a,b},x] && Not[IntegerQ[p]] && LtQ[0,j,n] && LtQ[p,-1] && GtQ[j*p+1,n-j]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, j_, n_, p_, x_],
        optional: [a__, b__, j_, n_],
        when: {
            freeq!([a__, b__], x_)
                && !integerq!(p_)
                && gtq!(j_, 0)
                && ltq!(j_, n_)
                && ltq!(p_, -1)
                && gtq!(&j_ * &p_ + Atom::num(1), &n_ - &j_)
        },
        rhs: {
            let base = &a__ * x_.pow(&j_) + &b__ * x_.pow(&n_);
            let denominator = &b__
                * (&n_ - &j_)
                * (&p_ + Atom::num(1))
                * x_.pow(&n_ - Atom::num(1));
            if denominator.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let recursive_integrand = base.pow(&p_ + Atom::num(1)) / x_.pow(&n_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(base.pow(&p_ + Atom::num(1)) / &denominator), x_)
                    - rubi_star(&j_ * &p_ - &n_ + &j_ + Atom::num(1), recursive
                        / (&b__ * (&n_ - &j_) * (&p_ + Atom::num(1))))
        },
    ));
}

fn push_rules_rule_1912(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, j_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 1912,
        source: "Int[(a_.*x_^j_.+b_.*x_^n_.)^p_,x_Symbol] :=
          -(a*x^j+b*x^n)^(p+1)/(a*(n-j)*(p+1)*x^(j-1)) +
          (n*p+n-j+1)/(a*(n-j)*(p+1)) \\[Star] Int[(a*x^j+b*x^n)^(p+1)/x^j,x] /;
        FreeQ[{a,b},x] && Not[IntegerQ[p]] && LtQ[0,j,n] && LtQ[p,-1]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, j_, n_, p_, x_],
        optional: [a__, b__, j_, n_],
        when: {
            freeq!([a__, b__], x_)
                && !integerq!(p_)
                && gtq!(j_, 0)
                && ltq!(j_, n_)
                && ltq!(p_, -1)
        },
        rhs: {
            let base = &a__ * x_.pow(&j_) + &b__ * x_.pow(&n_);
            let denominator = &a__ * (&n_ - &j_) * (&p_ + Atom::num(1));
            if denominator.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let recursive_integrand = base.pow(&p_ + Atom::num(1)) / x_.pow(&j_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(-base.pow(&p_ + Atom::num(1)) / (&denominator * x_.pow(&j_ - Atom::num(1)))), x_)
                    + rubi_star(&n_ * &p_ + &n_ - &j_ + Atom::num(1), recursive / denominator)
        },
    ));
}

fn push_rules_rule_1913(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, j_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 1913,
        source: "Int[(a_.*x_^j_.+b_.*x_^n_.)^p_,x_Symbol] :=
          x*(a*x^j+b*x^n)^p/(p*(n-j)) + a \\[Star] Int[x^j*(a*x^j+b*x^n)^(p-1),x] /;
        FreeQ[{a,b,j,n},x] && IGtQ[p+1/2,0] && NeQ[n,j] && EqQ[Simplify[j*p+1],0]",
        desc: "Generalized binomial recurrence 1b",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, j_, n_, p_, x_],
        optional: [a__, b__, j_, n_],
        when: {
            let balance = (&j_ * &p_ + Atom::num(1)).together();
            freeq!([a__, b__, j_, n_], x_)
                && igtq!(&p_ + Atom::num(1) / Atom::num(2), 0)
                && neq!(n_, j_)
                && eqq!(balance, 0)
        },
        rhs: {
            let base = &a__ * x_.pow(&j_) + &b__ * x_.pow(&n_);
            let denominator = &p_ * (&n_ - &j_);
            if denominator.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let recursive_integrand = x_.pow(&j_) * base.pow(&p_ - Atom::num(1));
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(x_ * base.pow(&p_) / denominator), x_) + rubi_star(a__, recursive)
        },
    ));
}

fn push_rules_rule_1914(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, n_, x_);
    rules.push(rubi_rule!(
        order: 1914,
        source: "Int[1/Sqrt[a_.*x_^2+b_.*x_^n_.],x_Symbol] :=
          2/(2-n) \\[Star] Subst[Int[1/(1-a*x^2),x],x,x/Sqrt[a*x^2+b*x^n]] /;
        FreeQ[{a,b,n},x] && NeQ[n,2]",
        desc: "Integration by substitution",
        refs: ["G&R 2.261.1, CRC 237a, A&S 3.3.33", "CRC 238"],
        pattern: Atom::num(1) / (a__ * x_.pow(2) + b__ * x_.pow(n_)).sqrt(),
        with: [a__, b__, n_, x_],
        optional: [a__, b__, n_],
        when: { freeq!([a__, b__, n_], x_) && neq!(n_, 2) },
        rhs: {
            let base = &a__ * x_.pow(2) + &b__ * x_.pow(&n_);
            let denominator = Atom::num(2) - &n_;
            if denominator.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub_symbol = sub_guard.symbol();
            let sub_atom = Atom::var(sub_symbol);
            let transformed_integrand = Atom::num(1) / (Atom::num(1) - &a__ * sub_atom.pow(2));
            let transformed = rubi_rhs_int(&transformed_integrand, sub_symbol);
            let replacement = x_ / base.sqrt();

            rubi_star(Atom::num(2), substitute_symbol(&transformed, sub_symbol, replacement) / denominator)
        },
    ));
}

fn push_rules_rule_1915(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, j_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 1915,
        source: "Int[(a_.*x_^j_.+b_.*x_^n_.)^p_,x_Symbol] :=
          -(a*x^j+b*x^n)^(p+1)/(a*(n-j)*(p+1)*x^(j-1)) +
          (n*p+n-j+1)/(a*(n-j)*(p+1)) \\[Star] Int[(a*x^j+b*x^n)^(p+1)/x^j,x] /;
        FreeQ[{a,b,j,n},x] && ILtQ[p+1/2,0] && NeQ[n,j] && EqQ[Simplify[j*p+1],0]",
        desc: "Generalized binomial recurrence 2b",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, j_, n_, p_, x_],
        optional: [a__, b__, j_, n_],
        when: {
            let balance = (&j_ * &p_ + Atom::num(1)).together();
            freeq!([a__, b__, j_, n_], x_)
                && iltq!(&p_ + Atom::num(1) / Atom::num(2), 0)
                && neq!(n_, j_)
                && eqq!(balance, 0)
        },
        rhs: {
            let base = &a__ * x_.pow(&j_) + &b__ * x_.pow(&n_);
            let denominator = &a__ * (&n_ - &j_) * (&p_ + Atom::num(1));
            if denominator.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let recursive_integrand = base.pow(&p_ + Atom::num(1)) / x_.pow(&j_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(-base.pow(&p_ + Atom::num(1)) / (&denominator * x_.pow(&j_ - Atom::num(1)))), x_)
                    + rubi_star(&n_ * &p_ + &n_ - &j_ + Atom::num(1), recursive / denominator)
        },
    ));
}

fn push_rules_rule_1916(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, j_, n_, x_);
    rules.push(rubi_rule!(
        order: 1916,
        source: "Int[1/Sqrt[a_.*x_^j_.+b_.*x_^n_.],x_Symbol] :=
          -2*Sqrt[a*x^j+b*x^n]/(b*(n-2)*x^(n-1)) -
          a*(2*n-j-2)/(b*(n-2)) \\[Star] Int[1/(x^(n-j)*Sqrt[a*x^j+b*x^n]),x] /;
        FreeQ[{a,b},x] && LtQ[2*(n-1),j,n]",
        desc: "Generalized binomial recurrence 3a with m=0 and p=-12",
        refs: [],
        pattern: Atom::num(1) / (a__ * x_.pow(j_) + b__ * x_.pow(n_)).sqrt(),
        with: [a__, b__, j_, n_, x_],
        optional: [a__, b__, j_, n_],
        when: {
            freeq!([a__, b__], x_)
                && ltq!(Atom::num(2) * (&n_ - Atom::num(1)), j_)
                && ltq!(j_, n_)
        },
        rhs: {
            let base = &a__ * x_.pow(&j_) + &b__ * x_.pow(&n_);
            let denominator = &b__ * (&n_ - Atom::num(2));
            let recursive_integrand =
                Atom::num(1) / (x_.pow(&n_ - &j_) * &base.sqrt());
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let direct = rubi_simp(
                &(-Atom::num(2) * base.sqrt()
                    / (&denominator * x_.pow(&n_ - Atom::num(1)))),
                x_,
            );
            let remainder = rubi_star(
                &a__ * (Atom::num(2) * &n_ - &j_ - Atom::num(2)) / denominator,
                recursive,
            );
            rubi_simp(&(direct), x_) - remainder
        },
    ));
}

fn push_rules_rule_1917(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, j_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 1917,
        source: "Int[(a_.*x_^j_.+b_.*x_^n_.)^p_,x_Symbol] :=
          (a*x^j+b*x^n)^FracPart[p]/(x^(j*FracPart[p])*(a+b*x^(n-j))^FracPart[p]) \\[Star] Int[x^(j*p)*(a+b*x^(n-j))^p,x] /;
        FreeQ[{a,b,j,n,p},x] && Not[IntegerQ[p]] && NeQ[n,j] && PosQ[n-j]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, j_, n_, p_, x_],
        optional: [a__, b__, j_, n_],
        when: {
            freeq!([a__, b__, j_, n_, p_], x_)
                && !integerq!(p_)
                && neq!(n_, j_)
                && posq!(&n_ - &j_)
        },
        rhs: {
            let frac = rubi_frac_part(&p_);
            let base = &a__ * x_.pow(&j_) + &b__ * x_.pow(&n_);
            let normalized_base = &a__ + &b__ * x_.pow(&n_ - &j_);
            let multiplier =
                base.pow(&frac) / (x_.pow(&j_ * &frac) * normalized_base.pow(&frac));
            let recursive_integrand = x_.pow(&j_ * &p_) * normalized_base.pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(multiplier, recursive)
        },
    ));
}

fn push_rules_rule_1918(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, j_, n_, p_, u_);
    rules.push(rubi_rule!(
        order: 1918,
        source: "Int[(a_.*u_^j_.+b_.*u_^n_.)^p_,x_Symbol] :=
          1/Coefficient[u,x,1] \\[Star] Subst[Int[(a*x^j+b*x^n)^p,x],x,u] /;
        FreeQ[{a,b,j,n,p},x] && LinearQ[u,x] && NeQ[u,x]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (a__ * u_.pow(j_) + b__ * u_.pow(n_)).pow(p_),
        with: [a__, b__, u_, j_, n_, p_, x_],
        optional: [a__, b__, j_, n_],
        x_dep: [u_],
        x_free: [a__, b__, j_, n_, p_],
        when: {
            freeq!([a__, b__, j_, n_, p_], x_)
                && rubi_linear_q(&u_, x_)
                && neq!(u_, x_)
        },
        rhs: {
            let (_constant, slope) = linear_coefficients(&u_, x_).rubi_rhs();
            if slope.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub_symbol = sub_guard.symbol();
            let sub_atom = Atom::var(sub_symbol);
            let transformed_integrand =
                (&a__ * sub_atom.pow(&j_) + &b__ * sub_atom.pow(&n_)).pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, sub_symbol);

            rubi_star(Atom::num(1) / slope, substitute_symbol(&transformed, sub_symbol, &u_))
        },
    ));
}

// Generated shared pattern builders.

#[inline(never)]
fn rubi_shared_pattern_0(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let j_ = symbols.j_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (a__ * x_.pow(j_) + b__ * x_.pow(n_)).pow(p_)
}
