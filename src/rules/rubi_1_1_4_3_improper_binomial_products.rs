use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_1940(rules);
    push_rules_rule_1941(rules);
    push_rules_rule_1942(rules);
    push_rules_rule_1943(rules);
    push_rules_rule_1944(rules);
    push_rules_rule_1945(rules);
    push_rules_rule_1946(rules);
    push_rules_rule_1947(rules);
    push_rules_rule_1948(rules);
}

fn push_rules_rule_1940(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, j_, k_, m_, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1940,
        source: "Int[x_^m_.*(a_.*x_^j_+b_.*x_^k_.)^p_*(c_+d_.*x_^n_)^q_.,x_Symbol] :=
          1/n \\[Star] Subst[Int[x^(Simplify[(m+1)/n]-1)*(a*x^Simplify[j/n]+b*x^Simplify[k/n])^p*(c+d*x)^q,x],x,x^n] /;
        FreeQ[{a,b,c,d,j,k,m,n,p,q},x] && Not[IntegerQ[p]] && NeQ[k,j] && IntegerQ[Simplify[j/n]] && IntegerQ[Simplify[k/n]] &&
          IntegerQ[Simplify[(m+1)/n]] && NeQ[n^2,1]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, j_, k_, m_, n_, p_, q_, x_],
        optional: [a__, b__, d__, k_, m_, q_],
        when: {
            let j_over_n = (&j_ / &n_).together();
            let k_over_n = (&k_ / &n_).together();
            let m1_over_n = ((&m_ + Atom::num(1)) / &n_).together();
            freeq!([a__, b__, c__, d__, j_, k_, m_, n_, p_, q_], x_)
                && !integerq!(p_)
                && neq!(k_, j_)
                && integerq!(j_over_n)
                && integerq!(k_over_n)
                && integerq!(m1_over_n)
                && neq!(n_.pow(2), 1)
        },
        rhs: {
            if n_.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let j_over_n = (&j_ / &n_).together();
            let k_over_n = (&k_ / &n_).together();
            let m1_over_n = ((&m_ + Atom::num(1)) / &n_).together();
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub_symbol = sub_guard.symbol();
            let sub_atom = Atom::var(sub_symbol);
            let transformed_integrand = sub_atom.pow(m1_over_n - Atom::num(1))
                * (&a__ * sub_atom.pow(j_over_n) + &b__ * sub_atom.pow(k_over_n)).pow(&p_)
                * (&c__ + &d__ * sub_atom).pow(&q_);
            let transformed = rubi_rhs_int(&transformed_integrand, sub_symbol);

            rubi_star(Atom::num(1) / &n_, substitute_symbol(&transformed, sub_symbol, x_.pow(&n_)))
        },
    ));
}

fn push_rules_rule_1941(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, j_, k_, m_, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1941,
        source: "Int[(e_*x_)^m_.*(a_.*x_^j_+b_.*x_^k_.)^p_*(c_+d_.*x_^n_.)^q_.,x_Symbol] :=
          e^IntPart[m]*(e*x)^FracPart[m]/x^FracPart[m] \\[Star] Int[x^m*(a*x^j+b*x^k)^p*(c+d*x^n)^q,x] /;
        FreeQ[{a,b,c,d,e,j,k,m,n,p,q},x] && Not[IntegerQ[p]] && NeQ[k,j] && IntegerQ[Simplify[j/n]] && IntegerQ[Simplify[k/n]] &&
          IntegerQ[Simplify[(m+1)/n]] && NeQ[n^2,1]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, e__, j_, k_, m_, n_, p_, q_, x_],
        optional: [a__, b__, d__, k_, m_, n_, q_],
        when: {
            let j_over_n = (&j_ / &n_).together();
            let k_over_n = (&k_ / &n_).together();
            let m1_over_n = ((&m_ + Atom::num(1)) / &n_).together();
            freeq!([a__, b__, c__, d__, e__, j_, k_, m_, n_, p_, q_], x_)
                && !integerq!(p_)
                && neq!(k_, j_)
                && integerq!(j_over_n)
                && integerq!(k_over_n)
                && integerq!(m1_over_n)
                && neq!(n_.pow(2), 1)
        },
        rhs: {
            let base = &a__ * x_.pow(&j_) + &b__ * x_.pow(&k_);
            let second = &c__ + &d__ * x_.pow(&n_);
            let frac = rubi_frac_part(&m_);
            let multiplier = e__.pow(rubi_int_part(&m_)) * (&e__ * x_).pow(&frac)
                / x_.pow(&frac);
            let recursive_integrand = x_.pow(&m_) * base.pow(&p_) * second.pow(&q_);
            let original = (&e__ * x_).pow(&m_) * base.pow(&p_) * second.pow(&q_);
            if recursive_integrand == original {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(multiplier, recursive)
        },
    ));
}

fn push_rules_rule_1942(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, j_, jn_, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 1942,
        source: "Int[(e_.*x_)^m_.*(a_.*x_^j_.+b_.*x_^jn_.)^p_*(c_+d_.*x_^n_.),x_Symbol] :=
          c*e^(j-1)*(e*x)^(m-j+1)*(a*x^j+b*x^(j+n))^(p+1)/(a*(m+j*p+1)) /;
        FreeQ[{a,b,c,d,e,j,m,n,p},x] && EqQ[jn,j+n] && Not[IntegerQ[p]] && NeQ[b*c-a*d,0] && EqQ[a*d*(m+j*p+1)-b*c*(m+n+p*(j+n)+1),0] &&
          (GtQ[e,0] || IntegersQ[j]) && NeQ[m+j*p+1,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, e__, j_, jn_, m_, n_, p_, x_],
        optional: [e__, m_, a__, j_, b__, jn_, d__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, j_, m_, n_, p_], x_)
                && eqq!(jn_, &j_ + &n_)
                && !integerq!(p_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(
                    &a__ * &d__ * (&m_ + &j_ * &p_ + Atom::num(1))
                        - &b__ * &c__ * (&m_ + &n_ + &p_ * (&j_ + &n_) + Atom::num(1)),
                    0
                )
                && (gtq!(e__, 0) || integerq!(j_))
                && neq!(&m_ + &j_ * &p_ + Atom::num(1), 0)
        },
        rhs: {
            let denominator = &a__ * (&m_ + &j_ * &p_ + Atom::num(1));
            if denominator.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let base = &a__ * x_.pow(&j_) + &b__ * x_.pow(&j_ + &n_);

            rubi_simp(&(&c__ * e__.pow(&j_ - Atom::num(1))
                    * (&e__ * x_).pow(&m_ - &j_ + Atom::num(1))
                    * base.pow(&p_ + Atom::num(1))
                    / denominator), x_)
        },
    ));
}

fn push_rules_rule_1943(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, j_, jn_, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 1943,
        source: "Int[(e_.*x_)^m_.*(a_.*x_^j_.+b_.*x_^jn_.)^p_*(c_+d_.*x_^n_.),x_Symbol] :=
          -e^(j-1)*(b*c-a*d)*(e*x)^(m-j+1)*(a*x^j+b*x^(j+n))^(p+1)/(a*b*n*(p+1)) -
          e^j*(a*d*(m+j*p+1)-b*c*(m+n+p*(j+n)+1))/(a*b*n*(p+1)) \\[Star] Int[(e*x)^(m-j)*(a*x^j+b*x^(j+n))^(p+1),x] /;
        FreeQ[{a,b,c,d,e,j,m,n},x] && EqQ[jn,j+n] && Not[IntegerQ[p]] && NeQ[b*c-a*d,0] && LtQ[p,-1] && GtQ[j,0] && LeQ[j,m] &&
          (GtQ[e,0] || IntegerQ[j])",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, e__, j_, jn_, m_, n_, p_, x_],
        optional: [e__, m_, a__, j_, b__, jn_, d__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, j_, m_, n_], x_)
                && eqq!(jn_, &j_ + &n_)
                && !integerq!(p_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && ltq!(p_, -1)
                && gtq!(j_, 0)
                && leq!(j_, m_)
                && (gtq!(e__, 0) || integerq!(j_))
        },
        rhs: {
            let denominator = &a__ * &b__ * &n_ * (&p_ + Atom::num(1));
            if denominator.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let base = &a__ * x_.pow(&j_) + &b__ * x_.pow(&j_ + &n_);
            let balance = &a__ * &d__ * (&m_ + &j_ * &p_ + Atom::num(1))
                - &b__ * &c__ * (&m_ + &n_ + &p_ * (&j_ + &n_) + Atom::num(1));
            let recursive_integrand =
                (&e__ * x_).pow(&m_ - &j_) * base.pow(&p_ + Atom::num(1));
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(-e__.pow(&j_ - Atom::num(1))
                    * (&b__ * &c__ - &a__ * &d__)
                    * (&e__ * x_).pow(&m_ - &j_ + Atom::num(1))
                    * base.pow(&p_ + Atom::num(1))
                    / &denominator), x_)
                    - rubi_star(e__.pow(&j_) * balance / denominator, recursive)
        },
    ));
}

fn push_rules_rule_1944(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, j_, jn_, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 1944,
        source: "Int[(e_.*x_)^m_.*(a_.*x_^j_.+b_.*x_^jn_.)^p_*(c_+d_.*x_^n_.),x_Symbol] :=
          c*e^(j-1)*(e*x)^(m-j+1)*(a*x^j+b*x^(j+n))^(p+1)/(a*(m+j*p+1)) +
          (a*d*(m+j*p+1)-b*c*(m+n+p*(j+n)+1))/(a*e^n*(m+j*p+1)) \\[Star] Int[(e*x)^(m+n)*(a*x^j+b*x^(j+n))^p,x] /;
        FreeQ[{a,b,c,d,e,j,p},x] && EqQ[jn,j+n] && Not[IntegerQ[p]] && NeQ[b*c-a*d,0] && GtQ[n,0] &&
          (LtQ[m+j*p,-1] || IntegersQ[m-1/2,p-1/2] && LtQ[p,0] && LtQ[m,-n*p-1]) &&
          (GtQ[e,0] || IntegersQ[j,n]) && NeQ[m+j*p+1,0] && NeQ[m-n+j*p+1,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, e__, j_, jn_, m_, n_, p_, x_],
        optional: [e__, m_, a__, j_, b__, jn_, d__, n_],
        when: {
            let shifted_m = &m_ - Atom::num(1) / Atom::num(2);
            let shifted_p = &p_ - Atom::num(1) / Atom::num(2);
            let lower_m_bound = -&n_ * &p_ - Atom::num(1);
            freeq!([a__, b__, c__, d__, e__, j_, p_], x_)
                && eqq!(jn_, &j_ + &n_)
                && !integerq!(p_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && gtq!(n_, 0)
                && (ltq!(&m_ + &j_ * &p_, -1)
                    || integers_q(&[shifted_m.expand(), shifted_p.expand()])
                        && ltq!(p_, 0)
                        && ltq!(m_, lower_m_bound))
                && (gtq!(e__, 0) || integerq!(j_) && integerq!(n_))
                && neq!(&m_ + &j_ * &p_ + Atom::num(1), 0)
                && neq!(&m_ - &n_ + &j_ * &p_ + Atom::num(1), 0)
        },
        rhs: {
            let denominator = &a__ * e__.pow(&n_) * (&m_ + &j_ * &p_ + Atom::num(1));
            if denominator.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let base = &a__ * x_.pow(&j_) + &b__ * x_.pow(&j_ + &n_);
            let balance = &a__ * &d__ * (&m_ + &j_ * &p_ + Atom::num(1))
                - &b__ * &c__ * (&m_ + &n_ + &p_ * (&j_ + &n_) + Atom::num(1));
            let recursive_integrand =
                (&e__ * x_).pow(&m_ + &n_) * base.pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(&c__ * e__.pow(&j_ - Atom::num(1))
                    * (&e__ * x_).pow(&m_ - &j_ + Atom::num(1))
                    * base.pow(&p_ + Atom::num(1))
                    / (&a__ * (&m_ + &j_ * &p_ + Atom::num(1)))), x_)
                    + rubi_star(balance, recursive / denominator)
        },
    ));
}

fn push_rules_rule_1945(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, j_, jn_, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 1945,
        source: "Int[(e_.*x_)^m_.*(a_.*x_^j_.+b_.*x_^jn_.)^p_*(c_+d_.*x_^n_.),x_Symbol] :=
          d*e^(j-1)*(e*x)^(m-j+1)*(a*x^j+b*x^(j+n))^(p+1)/(b*(m+n+p*(j+n)+1)) -
          (a*d*(m+j*p+1)-b*c*(m+n+p*(j+n)+1))/(b*(m+n+p*(j+n)+1)) \\[Star] Int[(e*x)^m*(a*x^j+b*x^(j+n))^p,x] /;
        FreeQ[{a,b,c,d,e,j,m,n,p},x] && EqQ[jn,j+n] && Not[IntegerQ[p]] && NeQ[b*c-a*d,0] && NeQ[m+n+p*(j+n)+1,0] && (GtQ[e,0] || IntegerQ[j])",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, e__, j_, jn_, m_, n_, p_, x_],
        optional: [e__, m_, a__, j_, b__, jn_, d__, n_],
        when: {
            let denominator_factor = &m_ + &n_ + &p_ * (&j_ + &n_) + Atom::num(1);
            freeq!([a__, b__, c__, d__, e__, j_, m_, n_, p_], x_)
                && eqq!(jn_, &j_ + &n_)
                && !integerq!(p_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && neq!(denominator_factor, 0)
                && (gtq!(e__, 0) || integerq!(j_))
        },
        rhs: {
            let denominator = &b__ * (&m_ + &n_ + &p_ * (&j_ + &n_) + Atom::num(1));
            if denominator.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let base = &a__ * x_.pow(&j_) + &b__ * x_.pow(&j_ + &n_);
            let balance = &a__ * &d__ * (&m_ + &j_ * &p_ + Atom::num(1))
                - &b__ * &c__ * (&m_ + &n_ + &p_ * (&j_ + &n_) + Atom::num(1));
            let recursive_integrand = (&e__ * x_).pow(&m_) * base.pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(&d__ * e__.pow(&j_ - Atom::num(1))
                    * (&e__ * x_).pow(&m_ - &j_ + Atom::num(1))
                    * base.pow(&p_ + Atom::num(1))
                    / &denominator), x_)
                    - rubi_star(balance, recursive / denominator)
        },
    ));
}

fn push_rules_rule_1946(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, j_, k_, m_, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1946,
        source: "Int[x_^m_.*(a_.*x_^j_+b_.*x_^k_.)^p_*(c_+d_.*x_^n_.)^q_.,x_Symbol] :=
          1/(m+1) \\[Star] Subst[Int[(a*x^Simplify[j/(m+1)]+b*x^Simplify[k/(m+1)])^p*(c+d*x^Simplify[n/(m+1)])^q,x],x,x^(m+1)] /;
        FreeQ[{a,b,c,d,j,k,m,n,p,q},x] && Not[IntegerQ[p]] && NeQ[k,j] && IntegerQ[Simplify[j/n]] && IntegerQ[Simplify[k/n]] &&
          NeQ[m,-1] && IntegerQ[Simplify[n/(m+1)]] && Not[IntegerQ[n]]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, j_, k_, m_, n_, p_, q_, x_],
        optional: [a__, b__, d__, k_, m_, n_, q_],
        when: {
            if !(freeq!([a__, b__, c__, d__, j_, k_, m_, n_, p_, q_], x_)
                && !integerq!(p_)
                && neq!(k_, j_))
            {
                return false.into();
            }

            let j_over_n = (&j_ / &n_).together();
            let k_over_n = (&k_ / &n_).together();
            if !(integerq!(j_over_n)
                && integerq!(k_over_n)
                && neq!(m_, -Atom::num(1)))
            {
                return false.into();
            }

            let n_over_m1 = (&n_ / (&m_ + Atom::num(1))).together();
            integerq!(n_over_m1) && !integerq!(n_)
        },
        rhs: {
            let m1 = &m_ + Atom::num(1);
            if m1.is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let j_over_m1 = (&j_ / &m1).together();
            let k_over_m1 = (&k_ / &m1).together();
            let n_over_m1 = (&n_ / &m1).together();
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub_symbol = sub_guard.symbol();
            let sub_atom = Atom::var(sub_symbol);
            let transformed_integrand = (&a__ * sub_atom.pow(j_over_m1)
                + &b__ * sub_atom.pow(k_over_m1))
            .pow(&p_)
                * (&c__ + &d__ * sub_atom.pow(n_over_m1)).pow(&q_);
            let transformed = rubi_rhs_int(&transformed_integrand, sub_symbol);

            rubi_star(Atom::num(1) / &m1, substitute_symbol(&transformed, sub_symbol, x_.pow(&m1)))
        },
    ));
}

fn push_rules_rule_1947(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, j_, k_, m_, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1947,
        source: "Int[(e_*x_)^m_.*(a_.*x_^j_+b_.*x_^k_.)^p_*(c_+d_.*x_^n_.)^q_.,x_Symbol] :=
          e^IntPart[m]*(e*x)^FracPart[m]/x^FracPart[m] \\[Star] Int[x^m*(a*x^j+b*x^k)^p*(c+d*x^n)^q,x] /;
        FreeQ[{a,b,c,d,e,j,k,m,n,p,q},x] && Not[IntegerQ[p]] && NeQ[k,j] && IntegerQ[Simplify[j/n]] && IntegerQ[Simplify[k/n]] &&
          NeQ[m,-1] && IntegerQ[Simplify[n/(m+1)]] && Not[IntegerQ[n]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, e__, j_, k_, m_, n_, p_, q_, x_],
        optional: [a__, b__, d__, k_, m_, n_, q_],
        when: {
            let j_over_n = (&j_ / &n_).together();
            let k_over_n = (&k_ / &n_).together();
            let n_over_m1 = (&n_ / (&m_ + Atom::num(1))).together();
            freeq!([a__, b__, c__, d__, e__, j_, k_, m_, n_, p_, q_], x_)
                && !integerq!(p_)
                && neq!(k_, j_)
                && integerq!(j_over_n)
                && integerq!(k_over_n)
                && neq!(m_, -Atom::num(1))
                && integerq!(n_over_m1)
                && !integerq!(n_)
        },
        rhs: {
            let base = &a__ * x_.pow(&j_) + &b__ * x_.pow(&k_);
            let second = &c__ + &d__ * x_.pow(&n_);
            let frac = rubi_frac_part(&m_);
            let multiplier = e__.pow(rubi_int_part(&m_)) * (&e__ * x_).pow(&frac)
                / x_.pow(&frac);
            let recursive_integrand = x_.pow(&m_) * base.pow(&p_) * second.pow(&q_);
            let original = (&e__ * x_).pow(&m_) * base.pow(&p_) * second.pow(&q_);
            if recursive_integrand == original {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(multiplier, recursive)
        },
    ));
}

fn push_rules_rule_1948(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, j_, jn_, m_, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1948,
        source: "Int[(e_.*x_)^m_.*(a_.*x_^j_.+b_.*x_^jn_.)^p_*(c_+d_.*x_^n_.)^q_.,x_Symbol] :=
          e^IntPart[m]*(e*x)^FracPart[m]*(a*x^j+b*x^(j+n))^FracPart[p]/
            (x^(FracPart[m]+j*FracPart[p])*(a+b*x^n)^FracPart[p]) \\[Star]
            Int[x^(m+j*p)*(a+b*x^n)^p*(c+d*x^n)^q,x] /;
        FreeQ[{a,b,c,d,e,j,m,n,p,q},x] && EqQ[jn,j+n] && Not[IntegerQ[p]] && NeQ[b*c-a*d,0] && Not[EqQ[n,1] && EqQ[j,1]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: (e__ * x_).pow(m_)
            * (a__ * x_.pow(j_) + b__ * x_.pow(jn_)).pow(p_)
            * (c__ + d__ * x_.pow(n_)).pow(q_),
        with: [a__, b__, c__, d__, e__, j_, jn_, m_, n_, p_, q_, x_],
        optional: [e__, m_, a__, j_, b__, jn_, d__, n_, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__, j_, m_, n_, p_, q_], x_)
                && eqq!(jn_, &j_ + &n_)
                && !integerq!(p_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && !(eqq!(n_, 1) && eqq!(j_, 1))
        },
        rhs: {
            let frac_m = rubi_frac_part(&m_);
            let frac_p = rubi_frac_part(&p_);
            let shifted_base = &a__ * x_.pow(&j_) + &b__ * x_.pow(&j_ + &n_);
            let normalized_base = &a__ + &b__ * x_.pow(&n_);
            let multiplier = e__.pow(rubi_int_part(&m_))
                * (&e__ * x_).pow(&frac_m)
                * shifted_base.pow(&frac_p)
                / (x_.pow(&frac_m + &j_ * &frac_p) * normalized_base.pow(&frac_p));
            let recursive_integrand = x_.pow(&m_ + &j_ * &p_)
                * normalized_base.pow(&p_)
                * (&c__ + &d__ * x_.pow(&n_)).pow(&q_);
            let original =
                (&e__ * x_).pow(&m_) * shifted_base.pow(&p_) * (&c__ + &d__ * x_.pow(&n_)).pow(&q_);
            if recursive_integrand == original {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(multiplier, recursive)
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
    let e__ = symbols.e__;
    let j_ = symbols.j_;
    let jn_ = symbols.jn_;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (e__ * x_).pow(m_) * (a__ * x_.pow(j_) + b__ * x_.pow(jn_)).pow(p_) * (c__ + d__ * x_.pow(n_))
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let j_ = symbols.j_;
    let k_ = symbols.k_;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let q_ = symbols.q_;
    let x_ = symbols.x_;
    (e__ * x_).pow(m_)
        * (a__ * x_.pow(j_) + b__ * x_.pow(k_)).pow(p_)
        * (c__ + d__ * x_.pow(n_)).pow(q_)
}

#[inline(never)]
fn rubi_shared_pattern_2(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let j_ = symbols.j_;
    let k_ = symbols.k_;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let q_ = symbols.q_;
    let x_ = symbols.x_;
    x_.pow(m_) * (a__ * x_.pow(j_) + b__ * x_.pow(k_)).pow(p_) * (c__ + d__ * x_.pow(n_)).pow(q_)
}
