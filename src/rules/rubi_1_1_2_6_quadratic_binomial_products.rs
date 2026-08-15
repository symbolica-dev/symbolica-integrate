use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_435(rules);
    push_rules_rule_436(rules);
    push_rules_rule_437(rules);
    push_rules_rule_438(rules);
    push_rules_rule_439(rules);
    push_rules_rule_440(rules);
    push_rules_rule_441(rules);
    push_rules_rule_442(rules);
    push_rules_rule_443(rules);
    push_rules_rule_444(rules);
    push_rules_rule_445(rules);
    push_rules_rule_446(rules);
    push_rules_rule_447(rules);
    push_rules_rule_448(rules);
    push_rules_rule_449(rules);
    push_rules_rule_450(rules);
}

fn push_rules_rule_435(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, p_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 435,
        source: "Int[x_^m_.*(a_.+b_.*x_^2)^p_.*(c_.+d_.*x_^2)^q_.*(e_.+f_.*x_^2)^r_.,x_Symbol] :=
          1/2 \\[Star] Subst[Int[x^((m-1)/2)*(a+b*x)^p*(c+d*x)^q*(e+f*x)^r,x],x,x^2] /;
        FreeQ[{a,b,c,d,e,f,p,q,r},x] && IntegerQ[(m-1)/2]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern: x_.pow(m_)
            * (a__ + b__ * x_.pow(2)).pow(p_)
            * (c__ + d__ * x_.pow(2)).pow(q_)
            * (e__ + f__ * x_.pow(2)).pow(r_),
        with: [a__, b__, c__, d__, e__, f__, m_, p_, q_, r_, x_],
        optional: [a__, b__, c__, d__, e__, f__, m_, p_, q_, r_],
        x_free: [a__, b__, c__, d__, e__, f__, p_, q_, r_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, p_, q_, r_], x_)
                && integerq!((&m_ - 1) / 2)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = sub_atom.pow((&m_ - 1) / 2)
                * (&a__ + &b__ * &sub_atom).pow(&p_)
                * (&c__ + &d__ * &sub_atom).pow(&q_)
                * (&e__ + &f__ * &sub_atom).pow(&r_);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);
            let substituted = rubi_subst(&transformed, sub, x_.pow(2));
            rubi_star(Atom::num(1) / 2, substituted)
        },
    ));
}

fn push_rules_rule_436(rules: &mut Vec<RubiRule>) {
    rubi_symb!(b__, c__, d__, e__, f__, g__, m_, p_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 436,
        source: "Int[(g_.*x_)^m_.*(b_.*x_^2.)^p_.*(c_.+d_.*x_^2)^q_.*(e_.+f_.*x_^2)^r_.,x_Symbol] :=
          (g*x)^m*(b*x^2)^p/x^(m+2*p) \\[Star] Int[x^(m+2*p)*(c+d*x^2)^q*(e+f*x^2)^r,x] /;
        FreeQ[{b,c,d,e,f,g,m,p,q,r},x]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern: (g__ * x_).pow(m_)
            * (b__ * x_.pow(2)).pow(p_)
            * (c__ + d__ * x_.pow(2)).pow(q_)
            * (e__ + f__ * x_.pow(2)).pow(r_),
        with: [b__, c__, d__, e__, f__, g__, m_, p_, q_, r_, x_],
        optional: [b__, c__, d__, e__, f__, g__, m_, p_, q_, r_],
        x_free: [b__, c__, d__, e__, f__, g__, m_, p_, q_, r_],
        when: { freeq!([b__, c__, d__, e__, f__, g__, m_, p_, q_, r_], x_) },
        rhs: {
            let exponent = &m_ + Atom::num(2) * &p_;
            let prefactor = (&g__ * x_).pow(&m_)
                * (&b__ * x_.pow(2)).pow(&p_)
                / x_.pow(&exponent);
            let primitive = rubi_rhs_int(
                &(x_.pow(exponent)
                    * (&c__ + &d__ * x_.pow(2)).pow(&q_)
                    * (&e__ + &f__ * x_.pow(2)).pow(&r_)),
                x_,
            );
            rubi_star(prefactor, primitive)
        },
    ));
}

fn push_rules_rule_438(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, p_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 438,
        source: "Int[(g_.*x_)^m_*(a_+b_.*x_^2)^p_*(c_+d_.*x_^2)^q_*(e_+f_.*x_^2)^r_,x_Symbol] :=
          With[{k=Denominator[m]},
          k/g \\[Star] Subst[Int[x^(k*(m+1)-1)*(a+b*x^(k*2)/g^2)^p*(c+d*x^(k*2)/g^2)^q*(e+f*x^(k*2)/g^2)^r,x],x,(g*x)^(1/k)]] /;
        FreeQ[{a,b,c,d,e,f,g,p,q,r},x] && FractionQ[m]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, p_, q_, r_, x_],
        optional: [b__, d__, f__, g__],
        x_free: [a__, b__, c__, d__, e__, f__, g__, p_, q_, r_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, p_, q_, r_], x_)
                && fractionq!(m_)
        },
        rhs: {
            let k = Atom::num(rubi_denominator(&m_).rubi_rhs());
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let scaled_power = sub_atom.pow(Atom::num(2) * &k) / g__.pow(2);
            let transformed_integrand = sub_atom.pow(&k * (&m_ + 1) - 1)
                * (&a__ + &b__ * &scaled_power).pow(&p_)
                * (&c__ + &d__ * &scaled_power).pow(&q_)
                * (&e__ + &f__ * scaled_power).pow(&r_);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);
            let replacement = (&g__ * x_).pow(Atom::num(1) / &k);
            let substituted = rubi_subst(&transformed, sub, replacement);
            rubi_star(&k / &g__, substituted)
        },
    ));
}

fn push_rules_rule_437(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, p_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 437,
        source: "Int[(g_.*x_)^m_.*(a_+b_.*x_^2)^p_.*(c_+d_.*x_^2)^q_.*(e_+f_.*x_^2)^r_.,x_Symbol] :=
          Int[ExpandIntegrand[(g*x)^m*(a+b*x^2)^p*(c+d*x^2)^q*(e+f*x^2)^r,x],x] /;
        FreeQ[{a,b,c,d,e,f,g,m},x] && IGtQ[p,-2] && IGtQ[q,0] && IGtQ[r,0]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, p_, q_, r_, x_],
        optional: [b__, d__, f__, g__, m_, p_, q_, r_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, m_], x_)
                && igtq!(p_, -2)
                && igtq!(q_, 0)
                && igtq!(r_, 0)
        },
        rhs: {
            let integrand = (g__ * x_).pow(&m_)
                * (a__ + b__ * x_.pow(2)).pow(&p_)
                * (c__ + d__ * x_.pow(2)).pow(&q_)
                * (e__ + f__ * x_.pow(2)).pow(&r_);
            let expanded = rubi_expand_integrand(&integrand, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_439(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 439,
        source: "Int[(g_.*x_)^m_.*(a_+b_.*x_^2)^p_*(c_+d_.*x_^2)^q_.*(e_+f_.*x_^2),x_Symbol] :=
          -(b*e-a*f)*(g*x)^(m+1)*(a+b*x^2)^(p+1)*(c+d*x^2)^q/(2*a*b*g*(p+1)) +
          1/(2*a*b*(p+1)) \\[Star] Int[(g*x)^m*(a+b*x^2)^(p+1)*(c+d*x^2)^(q-1)*
            Simp[c*(2*b*e*(p+1)+(b*e-a*f)*(m+1))+d*(2*b*e*(p+1)+(b*e-a*f)*(m+2*q+1))*x^2,x],x] /;
        FreeQ[{a,b,c,d,e,f,g,m},x] && LtQ[p,-1] && GtQ[q,0] && Not[EqQ[q,1] && SimplerQ[b*c-a*d,b*e-a*f]]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, p_, q_, x_],
        optional: [b__, d__, f__, g__, m_, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, m_], x_)
                && ltq!(p_, -1)
                && gtq!(q_, 0)
                && !(eqq!(q_, 1)
                    && simplerq!(&b__ * &c__ - &a__ * &d__, &b__ * &e__ - &a__ * &f__))
        },
        rhs: {
            let quadratic_a = &a__ + &b__ * x_.pow(2);
            let quadratic_c = &c__ + &d__ * x_.pow(2);
            let shifted_p = &p_ + Atom::num(1);
            let cross = &b__ * &e__ - &a__ * &f__;
            let denominator = Atom::num(2) * &a__ * &b__ * &shifted_p;

            let direct = rubi_simp(
                &(-&cross * (&g__ * x_).pow(&m_ + Atom::num(1))
                    * quadratic_a.pow(&shifted_p)
                    * quadratic_c.pow(&q_)
                    / (&g__ * &denominator)),
                x_,
            );
            let payload = rubi_simp(
                &(&c__
                    * (Atom::num(2) * &b__ * &e__ * &shifted_p
                        + &cross * (&m_ + Atom::num(1)))
                    + &d__
                        * (Atom::num(2) * &b__ * &e__ * &shifted_p
                            + &cross * (&m_ + Atom::num(2) * &q_ + Atom::num(1)))
                        * x_.pow(2)),
                x_,
            );
            let recursive_integrand = (&g__ * x_).pow(&m_)
                * quadratic_a.pow(shifted_p)
                * quadratic_c.pow(&q_ - Atom::num(1))
                * payload;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_442(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 442,
        source: "Int[(g_.*x_)^m_*(a_+b_.*x_^2)^p_.*(c_+d_.*x_^2)^q_.*(e_+f_.*x_^2),x_Symbol] :=
          e*(g*x)^(m+1)*(a+b*x^2)^(p+1)*(c+d*x^2)^q/(a*g*(m+1)) -
          1/(a*g^2*(m+1)) \\[Star] Int[(g*x)^(m+2)*(a+b*x^2)^p*(c+d*x^2)^(q-1)*
            Simp[c*(b*e-a*f)*(m+1)+e*2*(b*c*(p+1)+a*d*q)+d*((b*e-a*f)*(m+1)+b*e*2*(p+q+1))*x^2,x],x] /;
        FreeQ[{a,b,c,d,e,f,g,p},x] && GtQ[q,0] && LtQ[m,-1] && Not[EqQ[q,1] && SimplerQ[e+f*x^2,c+d*x^2]]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, p_, q_, x_],
        optional: [b__, d__, f__, g__, p_, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, p_], x_)
                && gtq!(q_, 0)
                && ltq!(m_, -1)
                && !(eqq!(q_, 1)
                    && simplerq!(
                        &e__ + &f__ * x_.pow(2),
                        &c__ + &d__ * x_.pow(2)
                    ))
        },
        rhs: {
            let first_base = &a__ + &b__ * x_.pow(2);
            let second_base = &c__ + &d__ * x_.pow(2);
            let shifted_m = &m_ + Atom::num(1);
            let cross = &b__ * &e__ - &a__ * &f__;
            let direct = rubi_simp(
                &(&e__
                    * (&g__ * x_).pow(&shifted_m)
                    * first_base.pow(&p_ + Atom::num(1))
                    * second_base.pow(&q_)
                    / (&a__ * &g__ * &shifted_m)),
                x_,
            );
            let payload = rubi_simp(
                &(&c__ * &cross * &shifted_m
                    + Atom::num(2)
                        * &e__
                        * (&b__ * &c__ * (&p_ + Atom::num(1)) + &a__ * &d__ * &q_)
                    + &d__
                        * (&cross * &shifted_m
                            + Atom::num(2)
                                * &b__
                                * &e__
                                * (&p_ + &q_ + Atom::num(1)))
                        * x_.pow(2)),
                x_,
            );
            let recursive_integrand = (&g__ * x_).pow(&m_ + Atom::num(2))
                * first_base.pow(&p_)
                * second_base.pow(&q_ - Atom::num(1))
                * payload;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            rubi_simp(&(direct), x_)
                    - rubi_star(Atom::num(1) / (&a__ * g__.pow(2) * &shifted_m), recursive)
        },
    ));
}

fn push_rules_rule_443(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 443,
        source: "Int[(g_.*x_)^m_.*(a_+b_.*x_^2)^p_.*(c_+d_.*x_^2)^q_.*(e_+f_.*x_^2),x_Symbol] :=
          f*(g*x)^(m+1)*(a+b*x^2)^(p+1)*(c+d*x^2)^q/(b*g*(m+2*(p+q+1)+1)) +
          1/(b*(m+2*(p+q+1)+1)) \\[Star] Int[(g*x)^m*(a+b*x^2)^p*(c+d*x^2)^(q-1)*
            Simp[c*((b*e-a*f)*(m+1)+b*e*2*(p+q+1))+(d*(b*e-a*f)*(m+1)+f*2*q*(b*c-a*d)+b*e*d*2*(p+q+1))*x^2,x],x] /;
        FreeQ[{a,b,c,d,e,f,g,m,p},x] && GtQ[q,0] && Not[EqQ[q,1] && SimplerQ[e+f*x^2,c+d*x^2]]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, p_, q_, x_],
        optional: [b__, d__, f__, g__, m_, p_, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, m_, p_], x_)
                && gtq!(q_, 0)
                && !(eqq!(q_, 1)
                    && simplerq!(
                        &e__ + &f__ * x_.pow(2),
                        &c__ + &d__ * x_.pow(2)
                    ))
        },
        rhs: {
            let first_base = &a__ + &b__ * x_.pow(2);
            let second_base = &c__ + &d__ * x_.pow(2);
            let cross = &b__ * &e__ - &a__ * &f__;
            let balance = &m_ + Atom::num(2) * (&p_ + &q_ + Atom::num(1)) + Atom::num(1);
            let direct = rubi_simp(
                &(&f__ * (&g__ * x_).pow(&m_ + Atom::num(1))
                    * first_base.pow(&p_ + Atom::num(1))
                    * second_base.pow(&q_)
                    / (&b__ * &g__ * &balance)),
                x_,
            );
            let payload = rubi_simp(
                &(&c__
                    * (&cross * (&m_ + Atom::num(1))
                        + Atom::num(2) * &b__ * &e__ * (&p_ + &q_ + Atom::num(1)))
                    + (&d__ * &cross * (&m_ + Atom::num(1))
                        + Atom::num(2) * &f__ * &q_ * (&b__ * &c__ - &a__ * &d__)
                        + Atom::num(2) * &b__ * &e__ * &d__ * (&p_ + &q_ + Atom::num(1)))
                        * x_.pow(2)),
                x_,
            );
            let recursive_integrand = (&g__ * x_).pow(&m_)
                * first_base.pow(&p_)
                * second_base.pow(&q_ - Atom::num(1))
                * payload;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / (&b__ * &balance), recursive)
        },
    ));
}

fn push_rules_rule_440(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 440,
        source: "Int[(g_.*x_)^m_.*(a_+b_.*x_^2)^p_*(c_+d_.*x_^2)^q_*(e_+f_.*x_^2),x_Symbol] :=
          g*(b*e-a*f)*(g*x)^(m-1)*(a+b*x^2)^(p+1)*(c+d*x^2)^(q+1)/(2*b*(b*c-a*d)*(p+1)) -
          g^2/(2*b*(b*c-a*d)*(p+1)) \\[Star] Int[(g*x)^(m-2)*(a+b*x^2)^(p+1)*(c+d*x^2)^q*
            Simp[c*(b*e-a*f)*(m-1)+(d*(b*e-a*f)*(m+2*q+1)-b*2*(c*f-d*e)*(p+1))*x^2,x],x] /;
        FreeQ[{a,b,c,d,e,f,g,q},x] && LtQ[p,-1] && GtQ[m,1]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, p_, q_, x_],
        optional: [b__, d__, f__, g__, m_],
        x_free: [a__, b__, c__, d__, e__, f__, g__, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, q_], x_)
                && ltq!(p_, -1)
                && gtq!(m_, 1)
        },
        rhs: {
            let first_base = &a__ + &b__ * x_.pow(2);
            let second_base = &c__ + &d__ * x_.pow(2);
            let determinant = &b__ * &c__ - &a__ * &d__;
            let cross = &b__ * &e__ - &a__ * &f__;
            let denominator = Atom::num(2) * &b__ * &determinant * (&p_ + 1);
            let direct = &g__
                * &cross
                * (&g__ * x_).pow(&m_ - 1)
                * first_base.pow(&p_ + 1)
                * second_base.pow(&q_ + 1)
                / &denominator;
            let payload = rubi_simp(
                &(&c__ * &cross * (&m_ - 1)
                    + (&d__ * &cross * (&m_ + Atom::num(2) * &q_ + 1)
                        - Atom::num(2)
                            * &b__
                            * (&c__ * &f__ - &d__ * &e__)
                            * (&p_ + 1))
                        * x_.pow(2)),
                x_,
            );
            let primitive = rubi_rhs_int(
                &((&g__ * x_).pow(&m_ - 2)
                    * first_base.pow(&p_ + 1)
                    * second_base.pow(&q_)
                    * payload),
                x_,
            );
            rubi_simp(&(direct), x_) - rubi_star(g__.pow(2) / denominator, primitive)
        },
    ));
}

fn push_rules_rule_441(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 441,
        source: "Int[(g_.*x_)^m_.*(a_+b_.*x_^2)^p_*(c_+d_.*x_^2)^q_*(e_+f_.*x_^2),x_Symbol] :=
          -(b*e-a*f)*(g*x)^(m+1)*(a+b*x^2)^(p+1)*(c+d*x^2)^(q+1)/(a*g*2*(b*c-a*d)*(p+1)) +
          1/(a*2*(b*c-a*d)*(p+1)) \\[Star] Int[(g*x)^m*(a+b*x^2)^(p+1)*(c+d*x^2)^q*
            Simp[c*(b*e-a*f)*(m+1)+e*2*(b*c-a*d)*(p+1)+d*(b*e-a*f)*(m+2*(p+q+2)+1)*x^2,x],x] /;
        FreeQ[{a,b,c,d,e,f,g,m,q},x] && LtQ[p,-1]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, p_, q_, x_],
        optional: [b__, d__, f__, g__, m_],
        x_free: [a__, b__, c__, d__, e__, f__, g__, m_, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, m_, q_], x_)
                && ltq!(p_, -1)
        },
        rhs: {
            let first_base = &a__ + &b__ * x_.pow(2);
            let second_base = &c__ + &d__ * x_.pow(2);
            let determinant = &b__ * &c__ - &a__ * &d__;
            let cross = &b__ * &e__ - &a__ * &f__;
            let denominator = Atom::num(2) * &a__ * &determinant * (&p_ + 1);
            let direct = -&cross
                * (&g__ * x_).pow(&m_ + 1)
                * first_base.pow(&p_ + 1)
                * second_base.pow(&q_ + 1)
                / (&g__ * &denominator);
            let payload = rubi_simp(
                &(&c__ * &cross * (&m_ + 1)
                    + Atom::num(2) * &e__ * &determinant * (&p_ + 1)
                    + &d__
                        * &cross
                        * (&m_ + Atom::num(2) * (&p_ + &q_ + 2) + 1)
                        * x_.pow(2)),
                x_,
            );
            let primitive = rubi_rhs_int(
                &((&g__ * x_).pow(&m_)
                    * first_base.pow(&p_ + 1)
                    * second_base.pow(&q_)
                    * payload),
                x_,
            );
            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / denominator, primitive)
        },
    ));
}

fn push_rules_rule_444(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 444,
        source: "Int[(g_.*x_)^m_.*(a_+b_.*x_^2)^p_.*(c_+d_.*x_^2)^q_.*(e_+f_.*x_^2),x_Symbol] :=
          f*g*(g*x)^(m-1)*(a+b*x^2)^(p+1)*(c+d*x^2)^(q+1)/(b*d*(m+2*(p+q+1)+1)) -
          g^2/(b*d*(m+2*(p+q+1)+1)) \\[Star] Int[(g*x)^(m-2)*(a+b*x^2)^p*(c+d*x^2)^q*
            Simp[a*f*c*(m-1)+(a*f*d*(m+2*q+1)+b*(f*c*(m+2*p+1)-e*d*(m+2*(p+q+1)+1)))*x^2,x],x] /;
        FreeQ[{a,b,c,d,e,f,g,p,q},x] && GtQ[m,1]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, p_, q_, x_],
        optional: [b__, d__, f__, g__, m_, p_, q_],
        x_free: [a__, b__, c__, d__, e__, f__, g__, p_, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, p_, q_], x_) && gtq!(m_, 1)
        },
        rhs: {
            let first_base = &a__ + &b__ * x_.pow(2);
            let second_base = &c__ + &d__ * x_.pow(2);
            let balance = &m_ + Atom::num(2) * (&p_ + &q_ + 1) + 1;
            let direct = &f__
                * &g__
                * (&g__ * x_).pow(&m_ - 1)
                * first_base.pow(&p_ + 1)
                * second_base.pow(&q_ + 1)
                / (&b__ * &d__ * &balance);
            let payload = rubi_simp(
                &(&a__ * &f__ * &c__ * (&m_ - 1)
                    + (&a__ * &f__ * &d__ * (&m_ + Atom::num(2) * &q_ + 1)
                        + &b__
                            * (&f__ * &c__ * (&m_ + Atom::num(2) * &p_ + 1)
                                - &e__ * &d__ * &balance))
                        * x_.pow(2)),
                x_,
            );
            let primitive = rubi_rhs_int(
                &((&g__ * x_).pow(&m_ - 2)
                    * first_base.pow(&p_)
                    * second_base.pow(&q_)
                    * payload),
                x_,
            );
            rubi_simp(&(direct), x_)
                    - rubi_star(g__.pow(2) / (&b__ * &d__ * balance), primitive)
        },
    ));
}

fn push_rules_rule_445(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 445,
        source: "Int[(g_.*x_)^m_*(a_+b_.*x_^2)^p_.*(c_+d_.*x_^2)^q_.*(e_+f_.*x_^2),x_Symbol] :=
          e*(g*x)^(m+1)*(a+b*x^2)^(p+1)*(c+d*x^2)^(q+1)/(a*c*g*(m+1)) +
          1/(a*c*g^2*(m+1)) \\[Star] Int[(g*x)^(m+2)*(a+b*x^2)^p*(c+d*x^2)^q*
            Simp[a*f*c*(m+1)-e*(b*c+a*d)*(m+2+1)-e*2*(b*c*p+a*d*q)-b*e*d*(m+2*(p+q+2)+1)*x^2,x],x] /;
        FreeQ[{a,b,c,d,e,f,g,p,q},x] && LtQ[m,-1]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, p_, q_, x_],
        optional: [b__, d__, f__, g__, p_, q_],
        x_free: [a__, b__, c__, d__, e__, f__, g__, p_, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, p_, q_], x_) && ltq!(m_, -1)
        },
        rhs: {
            let first_base = &a__ + &b__ * x_.pow(2);
            let second_base = &c__ + &d__ * x_.pow(2);
            let shifted_m = &m_ + 1;
            let direct = &e__
                * (&g__ * x_).pow(&shifted_m)
                * first_base.pow(&p_ + 1)
                * second_base.pow(&q_ + 1)
                / (&a__ * &c__ * &g__ * &shifted_m);
            let payload = rubi_simp(
                &(&a__ * &f__ * &c__ * &shifted_m
                    - &e__ * (&b__ * &c__ + &a__ * &d__) * (&m_ + 2 + 1)
                    - Atom::num(2)
                        * &e__
                        * (&b__ * &c__ * &p_ + &a__ * &d__ * &q_)
                    - &b__
                        * &e__
                        * &d__
                        * (&m_ + Atom::num(2) * (&p_ + &q_ + 2) + 1)
                        * x_.pow(2)),
                x_,
            );
            let primitive = rubi_rhs_int(
                &((&g__ * x_).pow(&m_ + 2)
                    * first_base.pow(&p_)
                    * second_base.pow(&q_)
                    * payload),
                x_,
            );
            rubi_simp(&(direct), x_)
                    + rubi_star(Atom::num(1) / (&a__ * &c__ * g__.pow(2) * shifted_m), primitive)
        },
    ));
}

fn push_rules_rule_446(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, g__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 446,
        source: "Int[(g_.*x_)^m_.*(a_+b_.*x_^2)^p_*(e_+f_.*x_^2)/(c_+d_.*x_^2),x_Symbol] :=
          Int[ExpandIntegrand[(g*x)^m*(a+b*x^2)^p*(e+f*x^2)/(c+d*x^2),x],x] /;
        FreeQ[{a,b,c,d,e,f,g,m,p},x]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern: (g__ * x_).pow(m_)
            * (a__ + b__ * x_.pow(2)).pow(p_)
            * (e__ + f__ * x_.pow(2))
            / (c__ + d__ * x_.pow(2)),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, p_, x_],
        optional: [b__, d__, f__, g__, m_],
        x_free: [a__, b__, c__, d__, e__, f__, g__, m_, p_],
        when: { freeq!([a__, b__, c__, d__, e__, f__, g__, m_, p_], x_) },
        rhs: {
            let integrand = (&g__ * x_).pow(&m_)
                * (&a__ + &b__ * x_.pow(2)).pow(&p_)
                * (&e__ + &f__ * x_.pow(2))
                / (&c__ + &d__ * x_.pow(2));
            let expanded = rubi_expand_integrand(&integrand, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_447(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 447,
        source: "Int[(g_.*x_)^m_.*(a_+b_.*x_^2)^p_.*(c_+d_.*x_^2)^q_.*(e_+f_.*x_^2),x_Symbol] :=
          e \\[Star] Int[(g*x)^m*(a+b*x^2)^p*(c+d*x^2)^q,x] +
          f/e^2 \\[Star] Int[(g*x)^(m+2)*(a+b*x^2)^p*(c+d*x^2)^q,x] /;
        FreeQ[{a,b,c,d,e,f,g,m,p,q},x]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, p_, q_, x_],
        optional: [b__, d__, f__, g__, m_, p_, q_],
        x_free: [a__, b__, c__, d__, e__, f__, g__, m_, p_, q_],
        when: { freeq!([a__, b__, c__, d__, e__, f__, g__, m_, p_, q_], x_) },
        rhs: {
            let common = (&a__ + &b__ * x_.pow(2)).pow(&p_)
                * (&c__ + &d__ * x_.pow(2)).pow(&q_);
            let first = rubi_rhs_int(&((&g__ * x_).pow(&m_) * &common), x_);
            let second = rubi_rhs_int(&((&g__ * x_).pow(&m_ + 2) * common), x_);
            rubi_star(&e__, first)
                    + rubi_star(&f__ / e__.pow(2), second)
        },
    ));
}

fn push_rules_rule_448(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, p_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 448,
        source: "Int[(g_.*x_)^m_.*(a_+b_.*x_^2)^p_.*(c_+d_.*x_^2)^q_.*(e_+f_.*x_^2)^r_.,x_Symbol] :=
          e \\[Star] Int[(g*x)^m*(a+b*x^2)^p*(c+d*x^2)^q*(e+f*x^2)^(r-1),x] +
          f/e^2 \\[Star] Int[(g*x)^(m+2)*(a+b*x^2)^p*(c+d*x^2)^q*(e+f*x^2)^(r-1),x] /;
        FreeQ[{a,b,c,d,e,f,g,m,p,q},x] && IGtQ[r,0]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, p_, q_, r_, x_],
        optional: [b__, d__, f__, g__, m_, p_, q_, r_],
        x_free: [a__, b__, c__, d__, e__, f__, g__, m_, p_, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, m_, p_, q_], x_)
                && igtq!(r_, 0)
        },
        rhs: {
            let common = (&a__ + &b__ * x_.pow(2)).pow(&p_)
                * (&c__ + &d__ * x_.pow(2)).pow(&q_)
                * (&e__ + &f__ * x_.pow(2)).pow(&r_ - 1);
            let first = rubi_rhs_int(&((&g__ * x_).pow(&m_) * &common), x_);
            let second = rubi_rhs_int(&((&g__ * x_).pow(&m_ + 2) * common), x_);
            rubi_star(&e__, first)
                    + rubi_star(&f__ / e__.pow(2), second)
        },
    ));
}

fn push_rules_rule_449(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 449,
        source: "Int[(g_.*x_)^m_.*(a_+b_.*x_^2)^p_*(c_+d_.*x_^2)^q_*(e_+f_.*x_^2),x_Symbol] :=
          e \\[Star] Int[(g*x)^m*(a+b*x^2)^p*(c+d*x^2)^q,x] +
          f*(g*x)^m/x^m \\[Star] Int[x^(m+2)*(a+b*x^2)^p*(c+d*x^2)^q,x] /;
        FreeQ[{a,b,c,d,e,f,g,m,p,q},x]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, p_, q_, x_],
        optional: [b__, d__, f__, g__, m_],
        x_free: [a__, b__, c__, d__, e__, f__, g__, m_, p_, q_],
        when: { freeq!([a__, b__, c__, d__, e__, f__, g__, m_, p_, q_], x_) },
        rhs: {
            let common = (&a__ + &b__ * x_.pow(2)).pow(&p_)
                * (&c__ + &d__ * x_.pow(2)).pow(&q_);
            let first = rubi_rhs_int(&((&g__ * x_).pow(&m_) * &common), x_);
            let second = rubi_rhs_int(&(x_.pow(&m_ + 2) * common), x_);
            let second_prefactor = &f__ * (&g__ * x_).pow(&m_) / x_.pow(&m_);
            rubi_star(e__, first)
                    + rubi_star(second_prefactor, second)
        },
    ));
}

fn push_rules_rule_450(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, p_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 450,
        source: "Int[(g_.*x_)^m_.*(a_.+b_.*x_^2)^p_.*(c_.+d_.*x_^2)^q_.*(e_.+f_.*x_^2)^r_.,x_Symbol] :=
          Unintegrable[(g*x)^m*(a+b*x^2)^p*(c+d*x^2)^q*(e+f*x^2)^r,x] /;
        FreeQ[{a,b,c,d,e,f,g,m,p,q,r},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, p_, q_, r_, x_],
        optional: [a__, b__, c__, d__, e__, f__, g__, m_, p_, q_, r_],
        x_free: [a__, b__, c__, d__, e__, f__, g__, m_, p_, q_, r_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, m_, p_, q_, r_], x_)
        },
        rhs: {
            let integrand = (&g__ * x_).pow(&m_)
                * (&a__ + &b__ * x_.pow(2)).pow(&p_)
                * (&c__ + &d__ * x_.pow(2)).pow(&q_)
                * (&e__ + &f__ * x_.pow(2)).pow(&r_);
            rubi_unintegrable(integrand, x_)
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
    let f__ = symbols.f__;
    let g__ = symbols.g__;
    let m_ = symbols.m_;
    let p_ = symbols.p_;
    let q_ = symbols.q_;
    let x_ = symbols.x_;
    (g__ * x_).pow(m_)
        * (a__ + b__ * x_.pow(2)).pow(p_)
        * (c__ + d__ * x_.pow(2)).pow(q_)
        * (e__ + f__ * x_.pow(2))
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let g__ = symbols.g__;
    let m_ = symbols.m_;
    let p_ = symbols.p_;
    let q_ = symbols.q_;
    let r_ = symbols.r_;
    let x_ = symbols.x_;
    (g__ * x_).pow(m_)
        * (a__ + b__ * x_.pow(2)).pow(p_)
        * (c__ + d__ * x_.pow(2)).pow(q_)
        * (e__ + f__ * x_.pow(2)).pow(r_)
}
