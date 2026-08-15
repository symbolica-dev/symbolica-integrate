use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_1919(rules);
    push_rules_rule_1920(rules);
    push_rules_rule_1921(rules);
    push_rules_rule_1922(rules);
    push_rules_rule_1923(rules);
    push_rules_rule_1924(rules);
    push_rules_rule_1925(rules);
    push_rules_rule_1926(rules);
    push_rules_rule_1927(rules);
    push_rules_rule_1928(rules);
    push_rules_rule_1929(rules);
    push_rules_rule_1930(rules);
    push_rules_rule_1931(rules);
    push_rules_rule_1932(rules);
    push_rules_rule_1933(rules);
    push_rules_rule_1934(rules);
    push_rules_rule_1935(rules);
    push_rules_rule_1936(rules);
    push_rules_rule_1937(rules);
    push_rules_rule_1938(rules);
    push_rules_rule_1939(rules);
}

fn push_rules_rule_1919(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, j_, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 1919,
        source: "Int[x_^m_.*(a_.*x_^j_.+b_.*x_^n_)^p_,x_Symbol] :=
          1/n \\[Star] Subst[Int[(a*x^Simplify[j/n]+b*x)^p,x],x,x^n] /;
        FreeQ[{a,b,j,m,n,p},x] && Not[IntegerQ[p]] && NeQ[n,j] && IntegerQ[Simplify[j/n]] && EqQ[Simplify[m-n+1],0]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, j_, m_, n_, p_, x_],
        optional: [a__, b__, j_, m_],
        when: {
            let j_over_n = (&j_ / &n_).together();
            let balance = (&m_ - &n_ + Atom::num(1)).together();
            freeq!([a__, b__, j_, m_, n_, p_], x_)
                && !integerq!(p_)
                && neq!(n_, j_)
                && integerq!(j_over_n)
                && eqq!(balance, 0)
        },
        rhs: {
            if n_.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub_symbol = sub_guard.symbol();
            let sub_atom = Atom::var(sub_symbol);
            let j_over_n = (&j_ / &n_).together();
            let transformed_integrand = (&a__ * sub_atom.pow(j_over_n) + &b__ * &sub_atom).pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, sub_symbol);

            rubi_star(Atom::num(1) / &n_, substitute_symbol(&transformed, sub_symbol, x_.pow(&n_)))
        },
    ));
}

fn push_rules_rule_1920(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, j_, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 1920,
        source: "Int[(c_.*x_)^m_.*(a_.*x_^j_.+b_.*x_^n_.)^p_,x_Symbol] :=
          -c^(j-1)*(c*x)^(m-j+1)*(a*x^j+b*x^n)^(p+1)/(a*(n-j)*(p+1)) /;
        FreeQ[{a,b,c,j,m,n,p},x] && Not[IntegerQ[p]] && NeQ[n,j] && EqQ[m+n*p+n-j+1,0] && (IntegerQ[j] || GtQ[c,0])",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, j_, m_, n_, p_, x_],
        optional: [a__, b__, c__, j_, m_, n_],
        when: {
            freeq!([a__, b__, c__, j_, m_, n_, p_], x_)
                && !integerq!(p_)
                && neq!(n_, j_)
                && eqq!(&m_ + &n_ * &p_ + &n_ - &j_ + Atom::num(1), 0)
                && (integerq!(j_) || gtq!(c__, 0))
        },
        rhs: {
            let base = &a__ * x_.pow(&j_) + &b__ * x_.pow(&n_);
            let denominator = &a__ * (&n_ - &j_) * (&p_ + Atom::num(1));
            if denominator.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            rubi_simp(&(-c__.pow(&j_ - Atom::num(1))
                    * (&c__ * x_).pow(&m_ - &j_ + Atom::num(1))
                    * base.pow(&p_ + Atom::num(1))
                    / denominator), x_)
        },
    ));
}

fn push_rules_rule_1921(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, j_, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 1921,
        source: "Int[(c_.*x_)^m_.*(a_.*x_^j_.+b_.*x_^n_.)^p_,x_Symbol] :=
          -c^(j-1)*(c*x)^(m-j+1)*(a*x^j+b*x^n)^(p+1)/(a*(n-j)*(p+1)) +
          c^j*(m+n*p+n-j+1)/(a*(n-j)*(p+1)) \\[Star] Int[(c*x)^(m-j)*(a*x^j+b*x^n)^(p+1),x] /;
        FreeQ[{a,b,c,j,m,n},x] && Not[IntegerQ[p]] && NeQ[n,j] && ILtQ[Simplify[(m+n*p+n-j+1)/(n-j)],0] && LtQ[p,-1] && (IntegerQ[j] || GtQ[c,0])",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, j_, m_, n_, p_, x_],
        optional: [a__, b__, c__, j_, m_, n_],
        when: {
            if !(freeq!([a__, b__, c__, j_, m_, n_], x_)
                && !integerq!(p_)
                && neq!(n_, j_))
            {
                return ConditionResult::False;
            }

            let quotient = ((&m_ + &n_ * &p_ + &n_ - &j_ + Atom::num(1)) / (&n_ - &j_))
                .together();
            iltq!(quotient, 0)
                && ltq!(p_, -1)
                && (integerq!(j_) || gtq!(c__, 0))
        },
        rhs: {
            let base = &a__ * x_.pow(&j_) + &b__ * x_.pow(&n_);
            let denominator = &a__ * (&n_ - &j_) * (&p_ + Atom::num(1));
            if denominator.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let recursive_integrand =
                (&c__ * x_).pow(&m_ - &j_) * base.pow(&p_ + Atom::num(1));
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(-c__.pow(&j_ - Atom::num(1))
                    * (&c__ * x_).pow(&m_ - &j_ + Atom::num(1))
                    * base.pow(&p_ + Atom::num(1))
                    / &denominator), x_)
                    + rubi_star(c__.pow(&j_) * (&m_ + &n_ * &p_ + &n_ - &j_ + Atom::num(1)) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_1922(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, j_, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 1922,
        source: "Int[(c_.*x_)^m_.*(a_.*x_^j_.+b_.*x_^n_.)^p_,x_Symbol] :=
          c^(j-1)*(c*x)^(m-j+1)*(a*x^j+b*x^n)^(p+1)/(a*(m+j*p+1)) -
          b*(m+n*p+n-j+1)/(a*c^(n-j)*(m+j*p+1)) \\[Star] Int[(c*x)^(m+n-j)*(a*x^j+b*x^n)^p,x] /;
        FreeQ[{a,b,c,j,m,n,p},x] && Not[IntegerQ[p]] && NeQ[n,j] && ILtQ[Simplify[(m+n*p+n-j+1)/(n-j)],0] && NeQ[m+j*p+1,0] && (IntegersQ[j,n] || GtQ[c,0])",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, j_, m_, n_, p_, x_],
        optional: [a__, b__, c__, j_, m_, n_],
        when: {
            if !(freeq!([a__, b__, c__, j_, m_, n_, p_], x_)
                && !integerq!(p_)
                && neq!(n_, j_))
            {
                return ConditionResult::False;
            }

            let quotient = ((&m_ + &n_ * &p_ + &n_ - &j_ + Atom::num(1)) / (&n_ - &j_))
                .together();
            iltq!(quotient, 0)
                && neq!(&m_ + &j_ * &p_ + Atom::num(1), 0)
                && (integerq!(j_) && integerq!(n_) || gtq!(c__, 0))
        },
        rhs: {
            let base = &a__ * x_.pow(&j_) + &b__ * x_.pow(&n_);
            let denominator = &a__ * (&m_ + &j_ * &p_ + Atom::num(1));
            if denominator.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let recursive_integrand =
                (&c__ * x_).pow(&m_ + &n_ - &j_) * base.pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(c__.pow(&j_ - Atom::num(1))
                    * (&c__ * x_).pow(&m_ - &j_ + Atom::num(1))
                    * base.pow(&p_ + Atom::num(1))
                    / &denominator), x_)
                    - rubi_star(&b__ * (&m_ + &n_ * &p_ + &n_ - &j_ + Atom::num(1)) / (&a__ * c__.pow(&n_ - &j_) * (&m_ + &j_ * &p_ + Atom::num(1))), recursive)
        },
    ));
}

fn push_rules_rule_1923(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, j_, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 1923,
        source: "Int[(c_*x_)^m_.*(a_.*x_^j_.+b_.*x_^n_.)^p_,x_Symbol] :=
          c^IntPart[m]*(c*x)^FracPart[m]/x^FracPart[m] \\[Star] Int[x^m*(a*x^j+b*x^n)^p,x] /;
        FreeQ[{a,b,c,j,m,n,p},x] && Not[IntegerQ[p]] && NeQ[n,j] && ILtQ[Simplify[(m+n*p+n-j+1)/(n-j)],0]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, j_, m_, n_, p_, x_],
        optional: [a__, b__, j_, m_, n_],
        when: {
            if !(freeq!([a__, b__, c__, j_, m_, n_, p_], x_)
                && !integerq!(p_)
                && neq!(n_, j_))
            {
                return ConditionResult::False;
            }

            let quotient = ((&m_ + &n_ * &p_ + &n_ - &j_ + Atom::num(1)) / (&n_ - &j_))
                .together();
            iltq!(quotient, 0)
        },
        rhs: {
            let base = &a__ * x_.pow(&j_) + &b__ * x_.pow(&n_);
            let frac = rubi_frac_part(&m_);
            let multiplier = c__.pow(rubi_int_part(&m_)) * (&c__ * x_).pow(&frac)
                / x_.pow(&frac);
            let recursive_integrand = x_.pow(&m_) * base.pow(&p_);
            let original = (&c__ * x_).pow(&m_) * base.pow(&p_);
            if recursive_integrand == original {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(multiplier, recursive)
        },
    ));
}

fn push_rules_rule_1924(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, j_, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 1924,
        source: "Int[x_^m_.*(a_.*x_^j_.+b_.*x_^n_)^p_,x_Symbol] :=
          1/n \\[Star] Subst[Int[x^(Simplify[(m+1)/n]-1)*(a*x^Simplify[j/n]+b*x)^p,x],x,x^n] /;
        FreeQ[{a,b,j,m,n,p},x] && Not[IntegerQ[p]] && NeQ[n,j] && IntegerQ[Simplify[j/n]] && IntegerQ[Simplify[(m+1)/n]] && NeQ[n^2,1]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, j_, m_, n_, p_, x_],
        optional: [a__, b__, j_, m_],
        when: {
            let j_over_n = (&j_ / &n_).together();
            let m1_over_n = ((&m_ + Atom::num(1)) / &n_).together();
            freeq!([a__, b__, j_, m_, n_, p_], x_)
                && !integerq!(p_)
                && neq!(n_, j_)
                && integerq!(j_over_n)
                && integerq!(m1_over_n)
                && neq!(n_.pow(2), 1)
        },
        rhs: {
            if n_.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub_symbol = sub_guard.symbol();
            let sub_atom = Atom::var(sub_symbol);
            let j_over_n = (&j_ / &n_).together();
            let m1_over_n = ((&m_ + Atom::num(1)) / &n_).together();
            let transformed_integrand = sub_atom.pow(m1_over_n - Atom::num(1))
                * (&a__ * sub_atom.pow(j_over_n) + &b__ * &sub_atom).pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, sub_symbol);

            rubi_star(Atom::num(1) / &n_, substitute_symbol(&transformed, sub_symbol, x_.pow(&n_)))
        },
    ));
}

fn push_rules_rule_1925(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, j_, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 1925,
        source: "Int[(c_*x_)^m_.*(a_.*x_^j_.+b_.*x_^n_)^p_,x_Symbol] :=
          c^IntPart[m]*(c*x)^FracPart[m]/x^FracPart[m] \\[Star] Int[x^m*(a*x^j+b*x^n)^p,x] /;
        FreeQ[{a,b,c,j,m,n,p},x] && Not[IntegerQ[p]] && NeQ[n,j] && IntegerQ[Simplify[j/n]] && IntegerQ[Simplify[(m+1)/n]] && NeQ[n^2,1]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, j_, m_, n_, p_, x_],
        optional: [a__, b__, j_, m_],
        when: {
            let j_over_n = (&j_ / &n_).together();
            let m1_over_n = ((&m_ + Atom::num(1)) / &n_).together();
            freeq!([a__, b__, c__, j_, m_, n_, p_], x_)
                && !integerq!(p_)
                && neq!(n_, j_)
                && integerq!(j_over_n)
                && integerq!(m1_over_n)
                && neq!(n_.pow(2), 1)
        },
        rhs: {
            let base = &a__ * x_.pow(&j_) + &b__ * x_.pow(&n_);
            let frac = rubi_frac_part(&m_);
            let multiplier = c__.pow(rubi_int_part(&m_)) * (&c__ * x_).pow(&frac)
                / x_.pow(&frac);
            let recursive_integrand = x_.pow(&m_) * base.pow(&p_);
            let original = (&c__ * x_).pow(&m_) * base.pow(&p_);
            if recursive_integrand == original {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(multiplier, recursive)
        },
    ));
}

fn push_rules_rule_1926(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, j_, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 1926,
        source: "Int[(c_.*x_)^m_*(a_.*x_^j_.+b_.*x_^n_.)^p_,x_Symbol] :=
          (c*x)^(m+1)*(a*x^j+b*x^n)^p/(c*(m+j*p+1)) -
          b*p*(n-j)/(c^n*(m+j*p+1)) \\[Star] Int[(c*x)^(m+n)*(a*x^j+b*x^n)^(p-1),x] /;
        FreeQ[{a,b,c},x] && Not[IntegerQ[p]] && LtQ[0,j,n] && (IntegersQ[j,n] || GtQ[c,0]) && GtQ[p,0] && LtQ[m+j*p+1,0]",
        desc: "Generalized binomial recurrence 1a",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, j_, m_, n_, p_, x_],
        optional: [a__, b__, c__, j_, n_],
        when: {
            freeq!([a__, b__, c__], x_)
                && !integerq!(p_)
                && gtq!(j_, 0)
                && ltq!(j_, n_)
                && (integerq!(j_) && integerq!(n_) || gtq!(c__, 0))
                && gtq!(p_, 0)
                && ltq!(&m_ + &j_ * &p_ + Atom::num(1), 0)
        },
        rhs: {
            let base = &a__ * x_.pow(&j_) + &b__ * x_.pow(&n_);
            let denominator = &c__ * (&m_ + &j_ * &p_ + Atom::num(1));
            let recursive_integrand =
                (&c__ * x_).pow(&m_ + &n_) * base.pow(&p_ - Atom::num(1));
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let direct = rubi_simp(
                &((&c__ * x_).pow(&m_ + Atom::num(1)) * base.pow(&p_)
                    / &denominator),
                x_,
            );
            let remainder = rubi_star(
                &b__ * &p_ * (&n_ - &j_)
                    / (c__.pow(&n_) * (&m_ + &j_ * &p_ + Atom::num(1))),
                recursive,
            );
            rubi_simp(&(direct), x_) - remainder
        },
    ));
}

fn push_rules_rule_1927(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, j_, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 1927,
        source: "Int[(c_.*x_)^m_.*(a_.*x_^j_.+b_.*x_^n_.)^p_,x_Symbol] :=
          (c*x)^(m+1)*(a*x^j+b*x^n)^p/(c*(m+n*p+1)) +
          a*(n-j)*p/(c^j*(m+n*p+1)) \\[Star] Int[(c*x)^(m+j)*(a*x^j+b*x^n)^(p-1),x] /;
        FreeQ[{a,b,c,m},x] && Not[IntegerQ[p]] && LtQ[0,j,n] && (IntegersQ[j,n] || GtQ[c,0]) && GtQ[p,0] && NeQ[m+n*p+1,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, j_, m_, n_, p_, x_],
        optional: [a__, b__, c__, j_, m_, n_],
        when: {
            freeq!([a__, b__, c__, m_], x_)
                && !integerq!(p_)
                && gtq!(j_, 0)
                && ltq!(j_, n_)
                && (integerq!(j_) && integerq!(n_) || gtq!(c__, 0))
                && gtq!(p_, 0)
                && neq!(&m_ + &n_ * &p_ + Atom::num(1), 0)
        },
        rhs: {
            let base = &a__ * x_.pow(&j_) + &b__ * x_.pow(&n_);
            let denominator = &m_ + &n_ * &p_ + Atom::num(1);
            if denominator.is_zero() || c__.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let recursive_integrand =
                (&c__ * x_).pow(&m_ + &j_) * base.pow(&p_ - Atom::num(1));
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&((&c__ * x_).pow(&m_ + Atom::num(1)) * base.pow(&p_)
                    / (&c__ * &denominator)), x_)
                    + rubi_star(&a__ * (&n_ - &j_) * &p_ / (c__.pow(&j_) * denominator), recursive)
        },
    ));
}

fn push_rules_rule_1928(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, j_, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 1928,
        source: "Int[(c_.*x_)^m_.*(a_.*x_^j_.+b_.*x_^n_.)^p_,x_Symbol] :=
          c^(n-1)*(c*x)^(m-n+1)*(a*x^j+b*x^n)^(p+1)/(b*(n-j)*(p+1)) -
          c^n*(m+j*p-n+j+1)/(b*(n-j)*(p+1)) \\[Star] Int[(c*x)^(m-n)*(a*x^j+b*x^n)^(p+1),x] /;
        FreeQ[{a,b,c},x] && Not[IntegerQ[p]] && LtQ[0,j,n] && (IntegersQ[j,n] || GtQ[c,0]) && LtQ[p,-1] && GtQ[m+j*p+1,n-j]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, j_, m_, n_, p_, x_],
        optional: [a__, b__, c__, j_, m_, n_],
        when: {
            freeq!([a__, b__, c__], x_)
                && !integerq!(p_)
                && gtq!(j_, 0)
                && ltq!(j_, n_)
                && (integerq!(j_) && integerq!(n_) || gtq!(c__, 0))
                && ltq!(p_, -1)
                && gtq!(&m_ + &j_ * &p_ + Atom::num(1), &n_ - &j_)
        },
        rhs: {
            let base = &a__ * x_.pow(&j_) + &b__ * x_.pow(&n_);
            let denominator = &b__ * (&n_ - &j_) * (&p_ + Atom::num(1));
            if denominator.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let recursive_integrand =
                (&c__ * x_).pow(&m_ - &n_) * base.pow(&p_ + Atom::num(1));
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(c__.pow(&n_ - Atom::num(1))
                    * (&c__ * x_).pow(&m_ - &n_ + Atom::num(1))
                    * base.pow(&p_ + Atom::num(1))
                    / &denominator), x_)
                    - rubi_star(c__.pow(&n_) * (&m_ + &j_ * &p_ - &n_ + &j_ + Atom::num(1)) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_1929(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, j_, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 1929,
        source: "Int[(c_.*x_)^m_.*(a_.*x_^j_.+b_.*x_^n_.)^p_,x_Symbol] :=
          -c^(j-1)*(c*x)^(m-j+1)*(a*x^j+b*x^n)^(p+1)/(a*(n-j)*(p+1)) +
          c^j*(m+n*p+n-j+1)/(a*(n-j)*(p+1)) \\[Star] Int[(c*x)^(m-j)*(a*x^j+b*x^n)^(p+1),x] /;
        FreeQ[{a,b,c,m},x] && Not[IntegerQ[p]] && LtQ[0,j,n] && (IntegersQ[j,n] || GtQ[c,0]) && LtQ[p,-1]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, j_, m_, n_, p_, x_],
        optional: [a__, b__, c__, j_, m_, n_],
        when: {
            freeq!([a__, b__, c__, m_], x_)
                && !integerq!(p_)
                && gtq!(j_, 0)
                && ltq!(j_, n_)
                && (integerq!(j_) && integerq!(n_) || gtq!(c__, 0))
                && ltq!(p_, -1)
        },
        rhs: {
            let base = &a__ * x_.pow(&j_) + &b__ * x_.pow(&n_);
            let denominator = &a__ * (&n_ - &j_) * (&p_ + Atom::num(1));
            if denominator.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let recursive_integrand =
                (&c__ * x_).pow(&m_ - &j_) * base.pow(&p_ + Atom::num(1));
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(-c__.pow(&j_ - Atom::num(1))
                    * (&c__ * x_).pow(&m_ - &j_ + Atom::num(1))
                    * base.pow(&p_ + Atom::num(1))
                    / &denominator), x_)
                    + rubi_star(c__.pow(&j_) * (&m_ + &n_ * &p_ + &n_ - &j_ + Atom::num(1)) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_1930(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, j_, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 1930,
        source: "Int[(c_.*x_)^m_.*(a_.*x_^j_.+b_.*x_^n_.)^p_,x_Symbol] :=
          c^(n-1)*(c*x)^(m-n+1)*(a*x^j+b*x^n)^(p+1)/(b*(m+n*p+1)) -
          a*c^(n-j)*(m+j*p-n+j+1)/(b*(m+n*p+1)) \\[Star] Int[(c*x)^(m-(n-j))*(a*x^j+b*x^n)^p,x] /;
        FreeQ[{a,b,c,m,p},x] && Not[IntegerQ[p]] && LtQ[0,j,n] && (IntegersQ[j,n] || GtQ[c,0]) && GtQ[m+j*p-n+j+1,0] && NeQ[m+n*p+1,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, j_, m_, n_, p_, x_],
        optional: [a__, b__, c__, j_, m_, n_],
        when: {
            freeq!([a__, b__, c__, m_, p_], x_)
                && !integerq!(p_)
                && gtq!(j_, 0)
                && ltq!(j_, n_)
                && (integerq!(j_) && integerq!(n_) || gtq!(c__, 0))
                && gtq!(&m_ + &j_ * &p_ + Atom::num(1) - &n_ + &j_, 0)
                && neq!(&m_ + &n_ * &p_ + Atom::num(1), 0)
        },
        rhs: {
            let base = &a__ * x_.pow(&j_) + &b__ * x_.pow(&n_);
            let denominator = &b__ * (&m_ + &n_ * &p_ + Atom::num(1));
            if denominator.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let recursive_integrand =
                (&c__ * x_).pow(&m_ - (&n_ - &j_)) * base.pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(c__.pow(&n_ - Atom::num(1))
                    * (&c__ * x_).pow(&m_ - &n_ + Atom::num(1))
                    * base.pow(&p_ + Atom::num(1))
                    / &denominator), x_)
                    - rubi_star(&a__ * c__.pow(&n_ - &j_) * (&m_ + &j_ * &p_ - &n_ + &j_ + Atom::num(1)) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_1931(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, j_, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 1931,
        source: "Int[(c_.*x_)^m_.*(a_.*x_^j_.+b_.*x_^n_.)^p_,x_Symbol] :=
          c^(j-1)*(c*x)^(m-j+1)*(a*x^j+b*x^n)^(p+1)/(a*(m+j*p+1)) -
          b*(m+n*p+n-j+1)/(a*c^(n-j)*(m+j*p+1)) \\[Star] Int[(c*x)^(m+n-j)*(a*x^j+b*x^n)^p,x] /;
        FreeQ[{a,b,c,m,p},x] && Not[IntegerQ[p]] && LtQ[0,j,n] && (IntegersQ[j,n] || GtQ[c,0]) && LtQ[m+j*p+1,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, j_, m_, n_, p_, x_],
        optional: [a__, b__, c__, j_, m_, n_],
        when: {
            freeq!([a__, b__, c__, m_, p_], x_)
                && !integerq!(p_)
                && gtq!(j_, 0)
                && ltq!(j_, n_)
                && (integerq!(j_) && integerq!(n_) || gtq!(c__, 0))
                && ltq!(&m_ + &j_ * &p_ + Atom::num(1), 0)
        },
        rhs: {
            let base = &a__ * x_.pow(&j_) + &b__ * x_.pow(&n_);
            let denominator = &a__ * (&m_ + &j_ * &p_ + Atom::num(1));
            if denominator.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let recursive_integrand =
                (&c__ * x_).pow(&m_ + &n_ - &j_) * base.pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(c__.pow(&j_ - Atom::num(1))
                    * (&c__ * x_).pow(&m_ - &j_ + Atom::num(1))
                    * base.pow(&p_ + Atom::num(1))
                    / &denominator), x_)
                    - rubi_star(&b__ * (&m_ + &n_ * &p_ + &n_ - &j_ + Atom::num(1)) / (&a__ * c__.pow(&n_ - &j_) * (&m_ + &j_ * &p_ + Atom::num(1))), recursive)
        },
    ));
}

fn push_rules_rule_1932(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, j_, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 1932,
        source: "Int[x_^m_.*(a_.*x_^j_.+b_.*x_^n_)^p_,x_Symbol] :=
          1/(m+1) \\[Star] Subst[Int[(a*x^Simplify[j/(m+1)]+b*x^Simplify[n/(m+1)])^p,x],x,x^(m+1)] /;
        FreeQ[{a,b,j,m,n,p},x] && Not[IntegerQ[p]] && NeQ[n,j] && IntegerQ[Simplify[j/n]] && NeQ[m,-1] && IntegerQ[Simplify[n/(m+1)]] && Not[IntegerQ[n]]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, j_, m_, n_, p_, x_],
        optional: [a__, b__, j_, m_],
        when: {
            freeq!([a__, b__, j_, m_, n_, p_], x_)
                && !integerq!(p_)
                && neq!(n_, j_)
                && {
                    let j_over_n = (&j_ / &n_).together();
                    integerq!(j_over_n)
                        && neq!(m_, -1)
                        && {
                            let n_over_m1 = (&n_ / (&m_ + Atom::num(1))).together();
                            integerq!(n_over_m1) && !integerq!(n_)
                        }
                }
        },
        rhs: {
            let m1 = &m_ + Atom::num(1);
            if m1.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub_symbol = sub_guard.symbol();
            let sub_atom = Atom::var(sub_symbol);
            let j_over_m1 = (&j_ / &m1).together();
            let n_over_m1 = (&n_ / &m1).together();
            let transformed_integrand =
                (&a__ * sub_atom.pow(j_over_m1) + &b__ * sub_atom.pow(n_over_m1)).pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, sub_symbol);

            rubi_star(Atom::num(1) / (&m_ + Atom::num(1)), substitute_symbol(&transformed, sub_symbol, x_.pow(m1)))
        },
    ));
}

fn push_rules_rule_1933(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, j_, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 1933,
        source: "Int[(c_*x_)^m_.*(a_.*x_^j_.+b_.*x_^n_)^p_,x_Symbol] :=
          c^IntPart[m]*(c*x)^FracPart[m]/x^FracPart[m] \\[Star] Int[x^m*(a*x^j+b*x^n)^p,x] /;
        FreeQ[{a,b,c,j,m,n,p},x] && Not[IntegerQ[p]] && NeQ[n,j] && IntegerQ[Simplify[j/n]] && NeQ[m,-1] && IntegerQ[Simplify[n/(m+1)]] && Not[IntegerQ[n]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, j_, m_, n_, p_, x_],
        optional: [a__, b__, j_, m_],
        when: {
            freeq!([a__, b__, c__, j_, m_, n_, p_], x_)
                && !integerq!(p_)
                && neq!(n_, j_)
                && {
                    let j_over_n = (&j_ / &n_).together();
                    integerq!(j_over_n)
                        && neq!(m_, -1)
                        && {
                            let n_over_m1 = (&n_ / (&m_ + Atom::num(1))).together();
                            integerq!(n_over_m1) && !integerq!(n_)
                        }
                }
        },
        rhs: {
            let base = &a__ * x_.pow(&j_) + &b__ * x_.pow(&n_);
            let frac = rubi_frac_part(&m_);
            let multiplier = c__.pow(rubi_int_part(&m_)) * (&c__ * x_).pow(&frac)
                / x_.pow(&frac);
            let recursive_integrand = x_.pow(&m_) * base.pow(&p_);
            let original = (&c__ * x_).pow(&m_) * base.pow(&p_);
            if recursive_integrand == original {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(multiplier, recursive)
        },
    ));
}

fn push_rules_rule_1934(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, j_, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 1934,
        source: "Int[(c_.*x_)^m_.*(a_.*x_^j_.+b_.*x_^n_.)^p_,x_Symbol] :=
          (c*x)^(m+1)*(a*x^j+b*x^n)^p/(c*p*(n-j)) + a/c^j \\[Star] Int[(c*x)^(m+j)*(a*x^j+b*x^n)^(p-1),x] /;
        FreeQ[{a,b,c,j,m,n},x] && IGtQ[p+1/2,0] && NeQ[n,j] && EqQ[Simplify[m+j*p+1],0] && (IntegerQ[j] || GtQ[c,0])",
        desc: "Generalized binomial recurrence 1b",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, j_, m_, n_, p_, x_],
        optional: [a__, b__, c__, j_, m_, n_],
        when: {
            freeq!([a__, b__, c__, j_, m_, n_], x_)
                && igtq!(&p_ + Atom::num(1) / Atom::num(2), 0)
                && neq!(n_, j_)
                && eqq!(&m_ + &j_ * &p_ + Atom::num(1), 0)
                && (integerq!(j_) || gtq!(c__, 0))
        },
        rhs: {
            let base = &a__ * x_.pow(&j_) + &b__ * x_.pow(&n_);
            let denominator = &c__ * &p_ * (&n_ - &j_);
            if denominator.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let recursive_integrand =
                (&c__ * x_).pow(&m_ + &j_) * base.pow(&p_ - Atom::num(1));
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&((&c__ * x_).pow(&m_ + Atom::num(1)) * base.pow(&p_) / denominator), x_)
                    + rubi_star(a__, recursive / c__.pow(&j_))
        },
    ));
}

fn push_rules_rule_1935(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, j_, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 1935,
        source: "Int[x_^m_./Sqrt[a_.*x_^j_.+b_.*x_^n_.],x_Symbol] :=
          -2/(n-j) \\[Star] Subst[Int[1/(1-a*x^2),x],x,x^(j/2)/Sqrt[a*x^j+b*x^n]] /;
        FreeQ[{a,b,j,n},x] && EqQ[m,j/2-1] && NeQ[n,j]",
        desc: "Integration by substitution",
        refs: [],
        pattern: x_.pow(m_) / (a__ * x_.pow(j_) + b__ * x_.pow(n_)).sqrt(),
        with: [a__, b__, j_, m_, n_, x_],
        optional: [a__, b__, j_, m_, n_],
        when: {
            freeq!([a__, b__, j_, n_], x_)
                && eqq!(m_, &j_ / Atom::num(2) - Atom::num(1))
                && neq!(n_, j_)
        },
        rhs: {
            let denominator = &n_ - &j_;
            if denominator.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub_symbol = sub_guard.symbol();
            let sub_atom = Atom::var(sub_symbol);
            let base = &a__ * x_.pow(&j_) + &b__ * x_.pow(&n_);
            let transformed_integrand = Atom::num(1) / (Atom::num(1) - &a__ * sub_atom.pow(2));
            let transformed = rubi_rhs_int(&transformed_integrand, sub_symbol);
            let substitution = x_.pow(&j_ / Atom::num(2)) / base.sqrt();

            rubi_star(-Atom::num(2), substitute_symbol(&transformed, sub_symbol, substitution) / denominator)
        },
    ));
}

fn push_rules_rule_1936(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, j_, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 1936,
        source: "Int[(c_.*x_)^m_.*(a_.*x_^j_.+b_.*x_^n_.)^p_,x_Symbol] :=
          -c^(j-1)*(c*x)^(m-j+1)*(a*x^j+b*x^n)^(p+1)/(a*(n-j)*(p+1)) +
          c^j*(m+n*p+n-j+1)/(a*(n-j)*(p+1)) \\[Star] Int[(c*x)^(m-j)*(a*x^j+b*x^n)^(p+1),x] /;
        FreeQ[{a,b,c,j,m,n},x] && ILtQ[p+1/2,0] && NeQ[n,j] && EqQ[Simplify[m+j*p+1],0] && (IntegerQ[j] || GtQ[c,0])",
        desc: "Generalized binomial recurrence 2b",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, j_, m_, n_, p_, x_],
        optional: [a__, b__, c__, j_, m_, n_],
        when: {
            freeq!([a__, b__, c__, j_, m_, n_], x_)
                && iltq!(&p_ + Atom::num(1) / Atom::num(2), 0)
                && neq!(n_, j_)
                && eqq!(&m_ + &j_ * &p_ + Atom::num(1), 0)
                && (integerq!(j_) || gtq!(c__, 0))
        },
        rhs: {
            let base = &a__ * x_.pow(&j_) + &b__ * x_.pow(&n_);
            let denominator = &a__ * (&n_ - &j_) * (&p_ + Atom::num(1));
            if denominator.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let recursive_integrand =
                (&c__ * x_).pow(&m_ - &j_) * base.pow(&p_ + Atom::num(1));
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(-c__.pow(&j_ - Atom::num(1))
                    * (&c__ * x_).pow(&m_ - &j_ + Atom::num(1))
                    * base.pow(&p_ + Atom::num(1))
                    / &denominator), x_)
                    + rubi_star(c__.pow(&j_) * (&m_ + &n_ * &p_ + &n_ - &j_ + Atom::num(1)) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_1937(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, j_, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 1937,
        source: "Int[(c_*x_)^m_.*(a_.*x_^j_.+b_.*x_^n_)^p_,x_Symbol] :=
          c^IntPart[m]*(c*x)^FracPart[m]/x^FracPart[m] \\[Star] Int[x^m*(a*x^j+b*x^n)^p,x] /;
        FreeQ[{a,b,c,j,m,n,p},x] && IntegerQ[p+1/2] && NeQ[n,j] && EqQ[Simplify[m+j*p+1],0]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, j_, m_, n_, p_, x_],
        optional: [a__, b__, j_, m_],
        when: {
            freeq!([a__, b__, c__, j_, m_, n_, p_], x_)
                && integerq!(&p_ + Atom::num(1) / Atom::num(2))
                && neq!(n_, j_)
                && eqq!(&m_ + &j_ * &p_ + Atom::num(1), 0)
        },
        rhs: {
            let base = &a__ * x_.pow(&j_) + &b__ * x_.pow(&n_);
            let frac = rubi_frac_part(&m_);
            let multiplier = c__.pow(rubi_int_part(&m_)) * (&c__ * x_).pow(&frac)
                / x_.pow(&frac);
            let recursive_integrand = x_.pow(&m_) * base.pow(&p_);
            let original = (&c__ * x_).pow(&m_) * base.pow(&p_);
            if recursive_integrand == original {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(multiplier, recursive)
        },
    ));
}

fn push_rules_rule_1938(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, j_, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 1938,
        source: "Int[(c_.*x_)^m_.*(a_.*x_^j_.+b_.*x_^n_.)^p_,x_Symbol] :=
          c^IntPart[m]*(c*x)^FracPart[m]*(a*x^j+b*x^n)^FracPart[p]/
            (x^(FracPart[m]+j*FracPart[p])*(a+b*x^(n-j))^FracPart[p]) \\[Star]
            Int[x^(m+j*p)*(a+b*x^(n-j))^p,x] /;
        FreeQ[{a,b,c,j,m,n,p},x] && Not[IntegerQ[p]] && NeQ[n,j] && PosQ[n-j]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, j_, m_, n_, p_, x_],
        optional: [a__, b__, c__, j_, m_, n_],
        when: {
            freeq!([a__, b__, c__, j_, m_, n_, p_], x_)
                && !integerq!(p_)
                && neq!(n_, j_)
                && posq!(&n_ - &j_)
        },
        rhs: {
            let base = &a__ * x_.pow(&j_) + &b__ * x_.pow(&n_);
            let normalized_base = &a__ + &b__ * x_.pow(&n_ - &j_);
            let frac_m = rubi_frac_part(&m_);
            let frac_p = rubi_frac_part(&p_);
            let recursive_integrand = x_.pow(&m_ + &j_ * &p_) * normalized_base.pow(&p_);
            let original = (&c__ * x_).pow(&m_) * base.pow(&p_);
            if recursive_integrand == original {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(c__.pow(rubi_int_part(&m_)) * (&c__ * x_).pow(&frac_m) * base.pow(&frac_p) / (x_.pow(&frac_m + &j_ * &frac_p) * normalized_base.pow(frac_p)), recursive)
        },
    ));
}

fn push_rules_rule_1939(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, j_, m_, n_, p_, u_, v_);
    rules.push(rubi_rule!(
        order: 1939,
        source: "Int[u_^m_.*(a_.*v_^j_.+b_.*v_^n_.)^p_.,x_Symbol] :=
          u^m/(Coefficient[v,x,1]*v^m) \\[Star] Subst[Int[x^m*(a*x^j+b*x^n)^p,x],x,v] /;
        FreeQ[{a,b,j,m,n,p},x] && LinearPairQ[u,v,x]",
        desc: "Integration by substitution and piecewise constant extraction",
        refs: [],
        pattern: u_.pow(m_) * (a__ * v_.pow(j_) + b__ * v_.pow(n_)).pow(p_),
        with: [a__, b__, u_, v_, j_, m_, n_, p_, x_],
        optional: [a__, b__, j_, m_, n_, p_],
        when: { freeq!([a__, b__, j_, m_, n_, p_], x_) && rubi_linear_pair_q(&u_, &v_, x_) },
        rhs: {
            let (_v0, v1) = linear_coefficients(&v_, x_).rubi_rhs();
            let denominator = &v1 * v_.pow(&m_);
            if denominator.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand =
                sub_atom.pow(&m_) * (&a__ * sub_atom.pow(&j_) + &b__ * sub_atom.pow(&n_)).pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);

            rubi_star(u_.pow(&m_), substitute_symbol(&transformed, sub, &v_) / denominator)
        },
    ));
}

// Generated shared pattern builders.

#[inline(never)]
fn rubi_shared_pattern_0(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let j_ = symbols.j_;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (c__ * x_).pow(m_) * (a__ * x_.pow(j_) + b__ * x_.pow(n_)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let j_ = symbols.j_;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    x_.pow(m_) * (a__ * x_.pow(j_) + b__ * x_.pow(n_)).pow(p_)
}
