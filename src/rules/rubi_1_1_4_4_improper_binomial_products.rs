use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_2440(rules);
    push_rules_rule_2441(rules);
    push_rules_rule_2442(rules);
    push_rules_rule_2443(rules);
    push_rules_rule_2444(rules);
    push_rules_rule_2445(rules);
    push_rules_rule_2446(rules);
    push_rules_rule_2447(rules);
    push_rules_rule_2448(rules);
    push_rules_rule_2449(rules);
    push_rules_rule_2450(rules);
}

fn push_rules_rule_2440(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, j_, n_, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2440,
        source: "Int[Pq_*(a_.*x_^j_.+b_.*x_^n_)^p_,x_Symbol] :=
          With[{d=Denominator[n]},
          d \\[Star] Subst[Int[x^(d-1)*ReplaceAll[SubstFor[x^n,Pq,x],x->x^(d*n)]*(a*x^(d*j)+b*x^(d*n))^p,x],x,x^(1/d)]] /;
        FreeQ[{a,b,j,n,p},x] && PolyQ[Pq,x^n] && Not[IntegerQ[p]] && NeQ[n,j] && RationalQ[j,n] && IntegerQ[j/n] && LtQ[-1,n,1]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, j_, n_, p_, pq__, x_],
        optional: [a__, j_, b__],
        when: {
            freeq!([a__, b__, j_, n_, p_], x_)
                && rubi_poly_q_power(&pq__, x_, &n_)
                && !integerq!(p_)
                && neq!(n_, j_)
                && rationalq!([j_, n_])
                && integerq!(rubi_simplify(&(&j_ / &n_)))
                && gtq!(n_, -1)
                && ltq!(n_, 1)
        },
        rhs: {
            let d = rational_denominator(&n_).unwrap();
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub_symbol = sub_guard.symbol();
            let sub_atom = Atom::var(sub_symbol);
            let subst_for = rubi_subst_for(&pq__, x_.pow(&n_), sub_symbol);
            let transformed_px =
                substitute_symbol(&subst_for, sub_symbol, sub_atom.pow(Atom::num(d) * &n_));
            let transformed_integrand = sub_atom.pow(d - 1)
                * transformed_px
                * (&a__ * sub_atom.pow(Atom::num(d) * &j_)
                    + &b__ * sub_atom.pow(Atom::num(d) * &n_))
                .pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, sub_symbol);
            let substituted = rubi_subst(
                &transformed,
                sub_symbol,
                x_.pow(Atom::num(1) / Atom::num(d)),
            );

            rubi_star(Atom::num(d), substituted)
        },
    ));
}

fn push_rules_rule_2441(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, j_, m_, n_, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2441,
        source: "Int[x_^m_.*Pq_*(a_.*x_^j_.+b_.*x_^n_)^p_,x_Symbol] :=
          1/n \\[Star] Subst[Int[x^(Simplify[(m+1)/n]-1)*SubstFor[x^n,Pq,x]*(a*x^Simplify[j/n]+b*x)^p,x],x,x^n] /;
        FreeQ[{a,b,j,m,n,p},x] && PolyQ[Pq,x^n] && Not[IntegerQ[p]] && NeQ[n,j] && IntegerQ[Simplify[j/n]] && IntegerQ[Simplify[(m+1)/n]]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, j_, m_, n_, p_, pq__, x_],
        optional: [m_, a__, j_, b__],
        when: {
            freeq!([a__, b__, j_, m_, n_, p_], x_)
                && rubi_poly_q_power(&pq__, x_, &n_)
                && !integerq!(p_)
                && neq!(n_, j_)
                && integerq!(rubi_simplify(&(&j_ / &n_)))
                && integerq!(rubi_simplify(&((&m_ + Atom::num(1)) / &n_)))
        },
        rhs: {
            let m1_over_n = rubi_simplify(&((&m_ + Atom::num(1)) / &n_));
            let j_over_n = rubi_simplify(&(&j_ / &n_));
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub_symbol = sub_guard.symbol();
            let sub_atom = Atom::var(sub_symbol);
            let transformed_px = rubi_subst_for(&pq__, x_.pow(&n_), sub_symbol);
            let transformed_integrand = sub_atom.pow(m1_over_n - Atom::num(1))
                * transformed_px
                * (&a__ * sub_atom.pow(j_over_n) + &b__ * &sub_atom).pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, sub_symbol);
            let substituted = rubi_subst(&transformed, sub_symbol, x_.pow(&n_));

            rubi_star(Atom::num(1) / &n_, substituted)
        },
    ));
}

fn push_rules_rule_2442(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, j_, m_, n_, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2442,
        source: "Int[(c_*x_)^m_.*Pq_*(a_.*x_^j_.+b_.*x_^n_)^p_,x_Symbol] :=
          c^(Sign[m]*Quotient[m,Sign[m]])*(c*x)^Mod[m,Sign[m]]/x^Mod[m,Sign[m]] \\[Star] Int[x^m*Pq*(a*x^j+b*x^n)^p,x] /;
        FreeQ[{a,b,c,j,n,p},x] && PolyQ[Pq,x^n] && Not[IntegerQ[p]] && NeQ[n,j] && IntegerQ[Simplify[j/n]] &&
          IntegerQ[Simplify[(m+1)/n]] && RationalQ[m] && GtQ[m^2,1]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, j_, m_, n_, p_, pq__, x_],
        optional: [m_, a__, j_, b__],
        when: {
            freeq!([a__, b__, c__, j_, n_, p_], x_)
                && rubi_poly_q_power(&pq__, x_, &n_)
                && !integerq!(p_)
                && neq!(n_, j_)
                && integerq!(rubi_simplify(&(&j_ / &n_)))
                && integerq!(rubi_simplify(&((&m_ + Atom::num(1)) / &n_)))
                && rationalq!(m_)
                && gtq!(m_.pow(2), 1)
        },
        rhs: {
            let quotient_part = rubi_signed_quotient_part(&m_).unwrap();
            let mod_part = rubi_signed_mod_part(&m_).unwrap();
            let base = &a__ * x_.pow(&j_) + &b__ * x_.pow(&n_);
            let recursive_integrand = x_.pow(&m_) * &pq__ * base.pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let multiplier = c__.pow(quotient_part) * (&c__ * x_).pow(&mod_part)
                / x_.pow(mod_part);

            rubi_star(multiplier, recursive)
        },
    ));
}

fn push_rules_rule_2443(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, j_, m_, n_, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2443,
        source: "Int[(c_*x_)^m_.*Pq_*(a_.*x_^j_.+b_.*x_^n_)^p_,x_Symbol] :=
          (c*x)^m/x^m \\[Star] Int[x^m*Pq*(a*x^j+b*x^n)^p,x] /;
        FreeQ[{a,b,c,j,m,n,p},x] && PolyQ[Pq,x^n] && Not[IntegerQ[p]] && NeQ[n,j] && IntegerQ[Simplify[j/n]] && IntegerQ[Simplify[(m+1)/n]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, j_, m_, n_, p_, pq__, x_],
        optional: [m_, a__, j_, b__],
        when: {
            freeq!([a__, b__, c__, j_, m_, n_, p_], x_)
                && rubi_poly_q_power(&pq__, x_, &n_)
                && !integerq!(p_)
                && neq!(n_, j_)
                && integerq!(rubi_simplify(&(&j_ / &n_)))
                && integerq!(rubi_simplify(&((&m_ + Atom::num(1)) / &n_)))
        },
        rhs: {
            let base = &a__ * x_.pow(&j_) + &b__ * x_.pow(&n_);
            let recursive_integrand = x_.pow(&m_) * &pq__ * base.pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let multiplier = (&c__ * x_).pow(&m_) / x_.pow(&m_);

            rubi_star(multiplier, recursive)
        },
    ));
}

fn push_rules_rule_2444(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, j_, m_, n_, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2444,
        source: "Int[x_^m_.*Pq_*(a_.*x_^j_.+b_.*x_^n_)^p_,x_Symbol] :=
          With[{g=GCD[m+1,n]},
          1/g \\[Star] Subst[Int[x^((m+1)/g-1)*ReplaceAll[Pq,x->x^(1/g)]*(a*x^(j/g)+b*x^(n/g))^p,x],x,x^g] /;
         NeQ[g,1]] /;
        FreeQ[{a,b,p},x] && PolyQ[Pq,x^n] && Not[IntegerQ[p]] && IGtQ[j,0] && IGtQ[n,0] && IGtQ[j/n,0] && IntegerQ[m]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, j_, m_, n_, p_, pq__, x_],
        optional: [m_, a__, j_, b__],
        when: {
            freeq!([a__, b__, p_], x_)
                && rubi_poly_q_power(&pq__, x_, &n_)
                && !integerq!(p_)
                && igtq!(j_, 0)
                && igtq!(n_, 0)
                && igtq!(rubi_simplify(&(&j_ / &n_)), 0)
                && integerq!(m_)
                && neq!(
                    Atom::num(integer_gcd(
                        integer_i64(&(&m_ + Atom::num(1))).unwrap(),
                        integer_i64(&n_).unwrap(),
                    )),
                    1
                )
        },
        rhs: {
            let m1_i = integer_i64(&(&m_ + Atom::num(1))).unwrap();
            let n_i = integer_i64(&n_).unwrap();
            let g = integer_gcd(m1_i, n_i);
            let g_atom = Atom::num(g);
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub_symbol = sub_guard.symbol();
            let sub_atom = Atom::var(sub_symbol);
            let transformed_px = substitute_symbol(&pq__, x_, sub_atom.pow(Atom::num(1) / &g_atom));
            let transformed_integrand = sub_atom.pow(Atom::num(m1_i / g - 1))
                * transformed_px
                * (&a__ * sub_atom.pow(&j_ / &g_atom) + &b__ * sub_atom.pow(&n_ / &g_atom)).pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, sub_symbol);
            let substituted = rubi_subst(&transformed, sub_symbol, x_.pow(g));

            rubi_star(Atom::num(1) / &g_atom, substituted)
        },
    ));
}

fn push_rules_rule_2445(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, j_, m_, n_, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2445,
        source: "Int[(c_.*x_)^m_.*Pq_*(a_.*x_^j_.+b_.*x_^n_)^p_,x_Symbol] :=
          With[{q=Expon[Pq,x]},
            With[{Pqq=Coeff[Pq,x,q]},
            Pqq*(c*x)^(m+q-n+1)*(a*x^j+b*x^n)^(p+1)/(b*c^(q-n+1)*(m+q+n*p+1)) +
            Int[(c*x)^m*ExpandToSum[Pq-Pqq*x^q-a*Pqq*(m+q-n+1)*x^(q-n)/(b*(m+q+n*p+1)),x]*(a*x^j+b*x^n)^p,x]] /;
          GtQ[q,n-1] && NeQ[m+q+n*p+1,0] && (IntegerQ[2*p] || IntegerQ[p+(q+1)/(2*n)])] /;
        FreeQ[{a,b,c,m,p},x] && PolyQ[Pq,x] && Not[IntegerQ[p]] && IGtQ[j,0] && IGtQ[n,0] && LtQ[j,n]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, j_, m_, n_, p_, pq__, x_],
        optional: [c__, m_, a__, j_, b__],
        when: {
            freeq!([a__, b__, c__, m_, p_], x_)
                && rubi_poly_q(&pq__, x_)
                && !integerq!(p_)
                && igtq!(j_, 0)
                && igtq!(n_, 0)
                && ltq!(j_, n_)
                && {
                    let q = Atom::num(rubi_expon(&pq__, x_).unwrap());
                    gtq!(&q, &n_ - Atom::num(1))
                        && neq!(&m_ + &q + &n_ * &p_ + Atom::num(1), 0)
                        && (integerq!(Atom::num(2) * &p_)
                            || integerq!(&p_ + (&q + Atom::num(1)) / (Atom::num(2) * &n_)))
                }
        },
        rhs: {
            let q_i = rubi_expon(&pq__, x_).unwrap();
            let q = Atom::num(q_i);
            let pqq = rubi_coeff(&pq__, x_, q_i).unwrap();
            let denominator_factor = &m_ + &q + &n_ * &p_ + Atom::num(1);
            let direct_denominator = &b__ * c__.pow(&q - &n_ + Atom::num(1)) * &denominator_factor;
            let base = &a__ * x_.pow(&j_) + &b__ * x_.pow(&n_);
            let direct = &pqq
                * (&c__ * x_).pow(&m_ + &q - &n_ + Atom::num(1))
                * base.pow(&p_ + Atom::num(1))
                / direct_denominator;
            let payload = &pq__
                - &pqq * x_.pow(&q)
                - &a__ * &pqq * (&m_ + &q - &n_ + Atom::num(1)) * x_.pow(&q - &n_)
                    / (&b__ * &denominator_factor);
            let expanded_to_sum = rubi_expand_to_sum(&payload, x_);
            let recursive_integrand =
                (&c__ * x_).pow(&m_) * expanded_to_sum * base.pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            recursive + rubi_simp(&direct, x_)
        },
    ));
}

fn push_rules_rule_2446(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, j_, m_, n_, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2446,
        source: "Int[x_^m_.*Pq_*(a_.*x_^j_.+b_.*x_^n_)^p_,x_Symbol] :=
          1/(m+1) \\[Star] Subst[
            Int[ReplaceAll[SubstFor[x^n,Pq,x],x->x^Simplify[n/(m+1)]]*(a*x^Simplify[j/(m+1)]+b*x^Simplify[n/(m+1)])^p,x],x,x^(m+1)] /;
        FreeQ[{a,b,j,m,n,p},x] && PolyQ[Pq,x^n] && Not[IntegerQ[p]] && NeQ[n,j] && IntegerQ[Simplify[j/n]] &&
          IntegerQ[Simplify[n/(m+1)]] && Not[IntegerQ[n]]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, j_, m_, n_, p_, pq__, x_],
        optional: [m_, a__, j_, b__],
        when: {
            freeq!([a__, b__, j_, m_, n_, p_], x_)
                && rubi_poly_q_power(&pq__, x_, &n_)
                && !integerq!(p_)
                && neq!(n_, j_)
                && integerq!(rubi_simplify(&(&j_ / &n_)))
                && integerq!(rubi_simplify(&(&n_ / (&m_ + Atom::num(1)))))
                && !integerq!(n_)
        },
        rhs: {
            let m1 = &m_ + Atom::num(1);
            let j_over_m1 = rubi_simplify(&(&j_ / &m1));
            let n_over_m1 = rubi_simplify(&(&n_ / &m1));
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub_symbol = sub_guard.symbol();
            let sub_atom = Atom::var(sub_symbol);
            let subst_for = rubi_subst_for(&pq__, x_.pow(&n_), sub_symbol);
            let transformed_px =
                substitute_symbol(&subst_for, sub_symbol, sub_atom.pow(&n_over_m1));
            let transformed_integrand = transformed_px
                * (&a__ * sub_atom.pow(j_over_m1) + &b__ * sub_atom.pow(n_over_m1)).pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, sub_symbol);
            let substituted = rubi_subst(&transformed, sub_symbol, x_.pow(&m1));

            rubi_star(Atom::num(1) / &m1, substituted)
        },
    ));
}

fn push_rules_rule_2447(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, j_, m_, n_, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2447,
        source: "Int[(c_*x_)^m_*Pq_*(a_.*x_^j_.+b_.*x_^n_)^p_,x_Symbol] :=
          c^(Sign[m]*Quotient[m,Sign[m]])*(c*x)^Mod[m,Sign[m]]/x^Mod[m,Sign[m]] \\[Star] Int[x^m*Pq*(a*x^j+b*x^n)^p,x] /;
        FreeQ[{a,b,c,j,n,p},x] && PolyQ[Pq,x^n] && Not[IntegerQ[p]] && NeQ[n,j] && IntegerQ[Simplify[j/n]] &&
          IntegerQ[Simplify[n/(m+1)]] && Not[IntegerQ[n]] && GtQ[m^2,1]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, j_, m_, n_, p_, pq__, x_],
        optional: [a__, j_, b__],
        when: {
            freeq!([a__, b__, c__, j_, n_, p_], x_)
                && rubi_poly_q_power(&pq__, x_, &n_)
                && !integerq!(p_)
                && neq!(n_, j_)
                && integerq!(rubi_simplify(&(&j_ / &n_)))
                && integerq!(rubi_simplify(&(&n_ / (&m_ + Atom::num(1)))))
                && !integerq!(n_)
                && gtq!(m_.pow(2), 1)
        },
        rhs: {
            let quotient_part = rubi_signed_quotient_part(&m_).unwrap();
            let mod_part = rubi_signed_mod_part(&m_).unwrap();
            let base = &a__ * x_.pow(&j_) + &b__ * x_.pow(&n_);
            let recursive_integrand = x_.pow(&m_) * &pq__ * base.pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let multiplier = c__.pow(quotient_part) * (&c__ * x_).pow(&mod_part)
                / x_.pow(mod_part);

            rubi_star(multiplier, recursive)
        },
    ));
}

fn push_rules_rule_2448(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, j_, m_, n_, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2448,
        source: "Int[(c_*x_)^m_*Pq_*(a_.*x_^j_.+b_.*x_^n_)^p_,x_Symbol] :=
          (c*x)^m/x^m \\[Star] Int[x^m*Pq*(a*x^j+b*x^n)^p,x] /;
        FreeQ[{a,b,c,j,m,n,p},x] && PolyQ[Pq,x^n] && Not[IntegerQ[p]] && NeQ[n,j] && IntegerQ[Simplify[j/n]] &&
          IntegerQ[Simplify[n/(m+1)]] && Not[IntegerQ[n]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, j_, m_, n_, p_, pq__, x_],
        optional: [a__, j_, b__],
        when: {
            freeq!([a__, b__, c__, j_, m_, n_, p_], x_)
                && rubi_poly_q_power(&pq__, x_, &n_)
                && !integerq!(p_)
                && neq!(n_, j_)
                && integerq!(rubi_simplify(&(&j_ / &n_)))
                && integerq!(rubi_simplify(&(&n_ / (&m_ + Atom::num(1)))))
                && !integerq!(n_)
        },
        rhs: {
            let base = &a__ * x_.pow(&j_) + &b__ * x_.pow(&n_);
            let recursive_integrand = x_.pow(&m_) * &pq__ * base.pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let multiplier = (&c__ * x_).pow(&m_) / x_.pow(&m_);

            rubi_star(multiplier, recursive)
        },
    ));
}

fn push_rules_rule_2449(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, j_, m_, n_, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2449,
        source: "Int[(c_.*x_)^m_.*Pq_*(a_.*x_^j_.+b_.*x_^n_)^p_,x_Symbol] :=
          Int[ExpandIntegrand[(c*x)^m*Pq*(a*x^j+b*x^n)^p,x],x] /;
        FreeQ[{a,b,c,j,m,n,p},x] && (PolyQ[Pq,x] || PolyQ[Pq,x^n]) && Not[IntegerQ[p]] && NeQ[n,j]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, j_, m_, n_, p_, pq__, x_],
        optional: [c__, m_, a__, j_, b__],
        when: {
            freeq!([a__, b__, c__, j_, m_, n_, p_], x_)
                && (rubi_poly_q(&pq__, x_) || rubi_poly_q_power(&pq__, x_, &n_))
                && !integerq!(p_)
                && neq!(n_, j_)
        },
        rhs: {
            let payload = (&c__ * x_).pow(&m_)
                * &pq__
                * (&a__ * x_.pow(&j_) + &b__ * x_.pow(&n_)).pow(&p_);
            let expanded = rubi_expand_integrand(&payload, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_2450(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, j_, n_, p_, pq__, x_);
    rules.push(rubi_rule!(
        order: 2450,
        source: "Int[Pq_*(a_.*x_^j_.+b_.*x_^n_)^p_,x_Symbol] :=
          Int[ExpandIntegrand[Pq*(a*x^j+b*x^n)^p,x],x] /;
        FreeQ[{a,b,j,n,p},x] && (PolyQ[Pq,x] || PolyQ[Pq,x^n]) && Not[IntegerQ[p]] && NeQ[n,j]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, j_, n_, p_, pq__, x_],
        optional: [a__, j_, b__],
        when: {
            freeq!([a__, b__, j_, n_, p_], x_)
                && (rubi_poly_q(&pq__, x_) || rubi_poly_q_power(&pq__, x_, &n_))
                && !integerq!(p_)
                && neq!(n_, j_)
        },
        rhs: {
            let payload = &pq__ * (&a__ * x_.pow(&j_) + &b__ * x_.pow(&n_)).pow(&p_);
            let expanded = rubi_expand_integrand(&payload, x_);
            rubi_rhs_int(&expanded, x_)
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
    let pq__ = symbols.pq__;
    let x_ = symbols.x_;
    (c__ * x_).pow(m_) * pq__ * (a__ * x_.pow(j_) + b__ * x_.pow(n_)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let j_ = symbols.j_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let pq__ = symbols.pq__;
    let x_ = symbols.x_;
    pq__ * (a__ * x_.pow(j_) + b__ * x_.pow(n_)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_2(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let j_ = symbols.j_;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let pq__ = symbols.pq__;
    let x_ = symbols.x_;
    x_.pow(m_) * pq__ * (a__ * x_.pow(j_) + b__ * x_.pow(n_)).pow(p_)
}
