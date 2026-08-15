use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_1037(rules);
    push_rules_rule_1038(rules);
    push_rules_rule_1039(rules);
    push_rules_rule_1040(rules);
    push_rules_rule_1041(rules);
    push_rules_rule_1042(rules);
    push_rules_rule_1043(rules);
    push_rules_rule_1044(rules);
    push_rules_rule_1045(rules);
    push_rules_rule_1046(rules);
    push_rules_rule_1047(rules);
    push_rules_rule_1048(rules);
    push_rules_rule_1049(rules);
    push_rules_rule_1050(rules);
    push_rules_rule_1051(rules);
    push_rules_rule_1052(rules);
    push_rules_rule_1053(rules);
    push_rules_rule_1054(rules);
    push_rules_rule_1055(rules);
    push_rules_rule_1056(rules);
    push_rules_rule_1057(rules);
    push_rules_rule_1058(rules);
    push_rules_rule_1059(rules);
    push_rules_rule_1060(rules);
    push_rules_rule_1061(rules);
    push_rules_rule_1062(rules);
    push_rules_rule_1063(rules);
    push_rules_rule_1064(rules);
    push_rules_rule_1065(rules);
    push_rules_rule_1066(rules);
    push_rules_rule_1067(rules);
    push_rules_rule_1068(rules);
    push_rules_rule_1069(rules);
    push_rules_rule_1070(rules);
    push_rules_rule_1071(rules);
    push_rules_rule_1072(rules);
    push_rules_rule_1073(rules);
    push_rules_rule_1074(rules);
    push_rules_rule_1075(rules);
    push_rules_rule_1076(rules);
}

fn push_rules_rule_1037(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; b__, c__, d__, e__, f__, g__, m_, n_, p_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 1037,
        source: "Int[(g_.*x_)^m_.*(b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_.*(e_+f_.*x_^n_)^r_.,x_Symbol] :=
          g^m/(n*b^(Simplify[(m+1)/n]-1)) \\[Star] Subst[Int[(b*x)^(p+Simplify[(m+1)/n]-1)*(c+d*x)^q*(e+f*x)^r,x],x,x^n] /;
        FreeQ[{b,c,d,e,f,g,m,n,p,q,r},x] && (IntegerQ[m] || GtQ[g,0]) && IntegerQ[Simplify[(m+1)/n]]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [b__, c__, d__, e__, f__, g__, m_, n_, p_, q_, r_, x_],
        optional: [g__, m_, b__, d__, f__, q_, r_],
        when: {
            let k = rubi_simplify(&((&m_ + Atom::num(1)) / &n_));
            freeq!([b__, c__, d__, e__, f__, g__, m_, n_, p_, q_, r_], x_)
                && (integerq!(m_) || gtq!(g__, 0))
                && integerq!(k)
        },
        rhs: {
            let k = rubi_simplify(&((&m_ + Atom::num(1)) / &n_));
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = (&b__ * &sub_atom).pow(&p_ + &k - Atom::num(1))
                * (&c__ + &d__ * &sub_atom).pow(&q_)
                * (&e__ + &f__ * &sub_atom).pow(&r_);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);
            let substituted = rubi_subst(&transformed, sub, x_.pow(&n_));

            rubi_star(g__.pow(&m_) / (&n_ * b__.pow(&k - Atom::num(1))), substituted)
        },
    ));
}

fn push_rules_rule_1038(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; b__, c__, d__, e__, f__, g__, m_, n_, p_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 1038,
        source: "Int[(g_.*x_)^m_.*(b_.*x_^n_.)^p_*(c_+d_.*x_^n_)^q_.*(e_+f_.*x_^n_)^r_.,x_Symbol] :=
          g^m*b^IntPart[p]*(b*x^n)^FracPart[p]/x^(n*FracPart[p]) \\[Star] Int[x^(m+n*p)*(c+d*x^n)^q*(e+f*x^n)^r,x] /;
        FreeQ[{b,c,d,e,f,g,m,n,p,q,r},x] && (IntegerQ[m] || GtQ[g,0]) && Not[IntegerQ[Simplify[(m+1)/n]]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [b__, c__, d__, e__, f__, g__, m_, n_, p_, q_, r_, x_],
        optional: [g__, m_, b__, n_, d__, f__, q_, r_],
        when: {
            let k = rubi_simplify(&((&m_ + Atom::num(1)) / &n_));
            freeq!([b__, c__, d__, e__, f__, g__, m_, n_, p_, q_, r_], x_)
                && (integerq!(m_) || gtq!(g__, 0))
                && !integerq!(k)
        },
        rhs: {
            let frac_p = rubi_frac_part(&p_);
            let recursive_integrand = x_.pow(&m_ + &n_ * &p_)
                * (&c__ + &d__ * x_.pow(&n_)).pow(&q_)
                * (&e__ + &f__ * x_.pow(&n_)).pow(&r_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(g__.pow(&m_)
                    * b__.pow(rubi_int_part(&p_))
                    * (&b__ * x_.pow(&n_)).pow(&frac_p)
                    / x_.pow(&n_ * frac_p), recursive)
        },
    ));
}

fn push_rules_rule_1039(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; b__, c__, d__, e__, f__, g__, m_, n_, p_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 1039,
        source: "Int[(g_*x_)^m_*(b_.*x_^n_.)^p_*(c_+d_.*x_^n_)^q_.*(e_+f_.*x_^n_)^r_.,x_Symbol] :=
          g^IntPart[m]*(g*x)^FracPart[m]/x^FracPart[m] \\[Star] Int[x^m*(b*x^n)^p*(c+d*x^n)^q*(e+f*x^n)^r,x] /;
        FreeQ[{b,c,d,e,f,g,m,n,p,q,r},x] && Not[IntegerQ[m]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [b__, c__, d__, e__, f__, g__, m_, n_, p_, q_, r_, x_],
        optional: [b__, n_, d__, f__, q_, r_],
        when: { freeq!([b__, c__, d__, e__, f__, g__, m_, n_, p_, q_, r_], x_) && !integerq!(m_) },
        rhs: {
            let frac_m = rubi_frac_part(&m_);
            let recursive_integrand = x_.pow(&m_)
                * (&b__ * x_.pow(&n_)).pow(&p_)
                * (&c__ + &d__ * x_.pow(&n_)).pow(&q_)
                * (&e__ + &f__ * x_.pow(&n_)).pow(&r_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(g__.pow(rubi_int_part(&m_)) * (&g__ * x_).pow(&frac_m)
                    / x_.pow(frac_m), recursive)
        },
    ));
}

fn push_rules_rule_1040(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 1040,
        source: "Int[(g_.*x_)^m_.*(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_)^q_.*(e_+f_.*x_^n_)^r_.,x_Symbol] :=
          Int[ExpandIntegrand[(g*x)^m*(a+b*x^n)^p*(c+d*x^n)^q*(e+f*x^n)^r,x],x] /;
        FreeQ[{a,b,c,d,e,f,g,m,n},x] && IGtQ[p,-2] && IGtQ[q,0] && IGtQ[r,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, q_, r_, x_],
        optional: [g__, m_, b__, d__, f__, p_, q_, r_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, m_, n_], x_)
                && igtq!(p_, -2)
                && igtq!(q_, 0)
                && igtq!(r_, 0)
        },
        rhs: {
            let integrand = (&g__ * x_).pow(&m_)
                * (&a__ + &b__ * x_.pow(&n_)).pow(&p_)
                * (&c__ + &d__ * x_.pow(&n_)).pow(&q_)
                * (&e__ + &f__ * x_.pow(&n_)).pow(&r_);
            let expanded = rubi_expand_integrand(&integrand, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_1041(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, p_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 1041,
        source: "Int[x_^m_.*(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_)^q_.*(e_+f_.*x_^n_)^r_.,x_Symbol] :=
          1/n \\[Star] Subst[Int[(a+b*x)^p*(c+d*x)^q*(e+f*x)^r,x],x,x^n] /;
        FreeQ[{a,b,c,d,e,f,m,n,p,q,r},x] && EqQ[m-n+1,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [a__, b__, c__, d__, e__, f__, m_, n_, p_, q_, r_, x_],
        optional: [m_, b__, d__, f__, p_, q_, r_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_, p_, q_, r_], x_)
                && eqq!(&m_ - &n_ + Atom::num(1), 0)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand =
                (&a__ + &b__ * &sub_atom).pow(&p_) * (&c__ + &d__ * &sub_atom).pow(&q_) * (&e__ + &f__ * &sub_atom).pow(&r_);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);
            let substituted = rubi_subst(&transformed, sub, x_.pow(&n_));

            rubi_star(Atom::num(1) / n_, substituted)
        },
    ));
}

fn push_rules_rule_1042(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, p_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 1042,
        source: "Int[x_^m_.*(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_)^q_.*(e_+f_.*x_^n_)^r_.,x_Symbol] :=
          Int[x^(m+n*(p+q+r))*(b+a*x^(-n))^p*(d+c*x^(-n))^q*(f+e*x^(-n))^r,x] /;
        FreeQ[{a,b,c,d,e,f,m,n},x] && IntegersQ[p,q,r] && NegQ[n]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [a__, b__, c__, d__, e__, f__, m_, n_, p_, q_, r_, x_],
        optional: [m_, b__, d__, f__, p_, q_, r_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_], x_)
                && integersq!([p_, q_, r_])
                && negq!(n_)
        },
        rhs: {
            let recursive_integrand = x_.pow(&m_ + &n_ * (&p_ + &q_ + &r_))
                * (&b__ + &a__ * x_.pow(-&n_)).pow(&p_)
                * (&d__ + &c__ * x_.pow(-&n_)).pow(&q_)
                * (&f__ + &e__ * x_.pow(-&n_)).pow(&r_);
            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_1043(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, p_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 1043,
        source: "Int[x_^m_.*(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_)^q_.*(e_+f_.*x_^n_)^r_.,x_Symbol] :=
          1/n \\[Star] Subst[Int[x^(Simplify[(m+1)/n]-1)*(a+b*x)^p*(c+d*x)^q*(e+f*x)^r,x],x,x^n] /;
        FreeQ[{a,b,c,d,e,f,m,n,p,q,r},x] && IntegerQ[Simplify[(m+1)/n]]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [a__, b__, c__, d__, e__, f__, m_, n_, p_, q_, r_, x_],
        optional: [m_, b__, d__, f__, p_, q_, r_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_, p_, q_, r_], x_)
                && integerq!(rubi_simplify(&((&m_ + Atom::num(1)) / &n_)))
        },
        rhs: {
            let k = rubi_simplify(&((&m_ + Atom::num(1)) / &n_));
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = sub_atom.pow(&k - Atom::num(1))
                * (&a__ + &b__ * &sub_atom).pow(&p_)
                * (&c__ + &d__ * &sub_atom).pow(&q_)
                * (&e__ + &f__ * &sub_atom).pow(&r_);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);
            let substituted = rubi_subst(&transformed, sub, x_.pow(&n_));

            rubi_star(Atom::num(1) / n_, substituted)
        },
    ));
}

fn push_rules_rule_1044(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 1044,
        source: "Int[(g_*x_)^m_.*(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_)^q_.*(e_+f_.*x_^n_)^r_.,x_Symbol] :=
          g^IntPart[m]*(g*x)^FracPart[m]/x^FracPart[m] \\[Star] Int[x^m*(a+b*x^n)^p*(c+d*x^n)^q*(e+f*x^n)^r,x] /;
        FreeQ[{a,b,c,d,e,f,g,m,n,p,q,r},x] && IntegerQ[Simplify[(m+1)/n]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, q_, r_, x_],
        optional: [m_, b__, d__, f__, p_, q_, r_],
        when: {
            let k = rubi_simplify(&((&m_ + Atom::num(1)) / &n_));
            freeq!([a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, q_, r_], x_)
                && integerq!(k)
        },
        rhs: {
            let frac_m = rubi_frac_part(&m_);
            let recursive_integrand = x_.pow(&m_)
                * (&a__ + &b__ * x_.pow(&n_)).pow(&p_)
                * (&c__ + &d__ * x_.pow(&n_)).pow(&q_)
                * (&e__ + &f__ * x_.pow(&n_)).pow(&r_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(g__.pow(rubi_int_part(&m_)) * (&g__ * x_).pow(&frac_m)
                    / x_.pow(frac_m), recursive)
        },
    ));
}

fn push_rules_rule_1045(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, p_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 1045,
        source: "Int[x_^m_.*(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_)^q_.*(e_+f_.*x_^n_)^r_.,x_Symbol] :=
          With[{k=GCD[m+1,n]},
          1/k \\[Star] Subst[Int[x^((m+1)/k-1)*(a+b*x^(n/k))^p*(c+d*x^(n/k))^q*(e+f*x^(n/k))^r,x],x,x^k] /;
         k!=1] /;
        FreeQ[{a,b,c,d,e,f,p,q,r},x] && IGtQ[n,0] && IntegerQ[m]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [a__, b__, c__, d__, e__, f__, m_, n_, p_, q_, r_, x_],
        optional: [m_, b__, d__, f__, p_, q_, r_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, p_, q_, r_], x_)
                && igtq!(n_, 0)
                && integerq!(m_)
                && rubi_gcd(&(&m_ + Atom::num(1)), &n_).is_some_and(|k| k != 1)
        },
        rhs: {
            let k = Atom::num(rubi_gcd(&(&m_ + Atom::num(1)), &n_).rubi_rhs());
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = sub_atom.pow((&m_ + Atom::num(1)) / &k - Atom::num(1))
                * (&a__ + &b__ * sub_atom.pow(&n_ / &k)).pow(&p_)
                * (&c__ + &d__ * sub_atom.pow(&n_ / &k)).pow(&q_)
                * (&e__ + &f__ * sub_atom.pow(&n_ / &k)).pow(&r_);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);
            let substituted = rubi_subst(&transformed, sub, x_.pow(&k));

            rubi_star(Atom::num(1) / k, substituted)
        },
    ));
}

fn push_rules_rule_1046(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 1046,
        source: "Int[(g_.*x_)^m_*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_*(e_+f_.*x_^n_)^r_,x_Symbol] :=
          With[{k=Denominator[m]},
          k/g \\[Star] Subst[Int[x^(k*(m+1)-1)*(a+b*x^(k*n)/g^n)^p*(c+d*x^(k*n)/g^n)^q*(e+f*x^(k*n)/g^n)^r,x],x,(g*x)^(1/k)]] /;
        FreeQ[{a,b,c,d,e,f,g,p,q,r},x] && IGtQ[n,0] && FractionQ[m]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, q_, r_, x_],
        optional: [g__, b__, d__, f__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, p_, q_, r_], x_)
                && igtq!(n_, 0)
                && fractionq!(m_)
        },
        rhs: {
            let k_i = rational_denominator(&m_).rubi_rhs();
            let k = Atom::num(k_i);
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = sub_atom.pow(&k * (&m_ + Atom::num(1)) - Atom::num(1))
                * (&a__ + &b__ * sub_atom.pow(&k * &n_) / g__.pow(&n_)).pow(&p_)
                * (&c__ + &d__ * sub_atom.pow(&k * &n_) / g__.pow(&n_)).pow(&q_)
                * (&e__ + &f__ * sub_atom.pow(&k * &n_) / g__.pow(&n_)).pow(&r_);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);
            let replacement = (&g__ * x_).pow(Atom::num(1) / &k);
            let substituted = rubi_subst(&transformed, sub, replacement);

            rubi_star(&k / g__, substituted)
        },
    ));
}

fn push_rules_rule_1047(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1047,
        source: "Int[(g_.*x_)^m_.*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_.*(e_+f_.*x_^n_),x_Symbol] :=
          -(b*e-a*f)*(g*x)^(m+1)*(a+b*x^n)^(p+1)*(c+d*x^n)^q/(a*b*g*n*(p+1)) +
          1/(a*b*n*(p+1)) \\[Star] Int[(g*x)^m*(a+b*x^n)^(p+1)*(c+d*x^n)^(q-1)*
            Simp[c*(b*e*n*(p+1)+(b*e-a*f)*(m+1))+d*(b*e*n*(p+1)+(b*e-a*f)*(m+n*q+1))*x^n,x],x] /;
        FreeQ[{a,b,c,d,e,f,g,m},x] && IGtQ[n,0] && LtQ[p,-1] && GtQ[q,0] && Not[EqQ[q,1] && SimplerQ[b*c-a*d,b*e-a*f]]",
        desc: "Binomial product recurrence 1",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, q_, x_],
        optional: [g__, m_, b__, d__, f__, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, m_], x_)
                && igtq!(n_, 0)
                && ltq!(p_, -1)
                && gtq!(q_, 0)
                && !(eqq!(q_, 1) && simplerq!(&b__ * &c__ - &a__ * &d__, &b__ * &e__ - &a__ * &f__))
        },
        rhs: {
            let first_base = &a__ + &b__ * x_.pow(&n_);
            let second_base = &c__ + &d__ * x_.pow(&n_);
            let be_af = &b__ * &e__ - &a__ * &f__;
            let direct = -&be_af
                * (&g__ * x_).pow(&m_ + Atom::num(1))
                * first_base.pow(&p_ + Atom::num(1))
                * second_base.pow(&q_)
                / (&a__ * &b__ * &g__ * &n_ * (&p_ + Atom::num(1)));
            let payload = &c__ * (&b__ * &e__ * &n_ * (&p_ + Atom::num(1)) + &be_af * (&m_ + Atom::num(1)))
                + &d__
                    * (&b__ * &e__ * &n_ * (&p_ + Atom::num(1))
                        + &be_af * (&m_ + &n_ * &q_ + Atom::num(1)))
                    * x_.pow(&n_);
            let recursive_integrand = (&g__ * x_).pow(&m_)
                * first_base.pow(&p_ + Atom::num(1))
                * second_base.pow(&q_ - Atom::num(1))
                * simp!(payload, x_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_)
                    + rubi_star(Atom::num(1) / (&a__ * &b__ * &n_ * (&p_ + Atom::num(1))), recursive)
        },
    ));
}

fn push_rules_rule_1048(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1048,
        source: "Int[(g_.*x_)^m_.*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_*(e_+f_.*x_^n_),x_Symbol] :=
          g^(n-1)*(b*e-a*f)*(g*x)^(m-n+1)*(a+b*x^n)^(p+1)*(c+d*x^n)^(q+1)/(b*n*(b*c-a*d)*(p+1)) -
          g^n/(b*n*(b*c-a*d)*(p+1)) \\[Star] Int[(g*x)^(m-n)*(a+b*x^n)^(p+1)*(c+d*x^n)^q*
            Simp[c*(b*e-a*f)*(m-n+1)+(d*(b*e-a*f)*(m+n*q+1)-b*n*(c*f-d*e)*(p+1))*x^n,x],x] /;
        FreeQ[{a,b,c,d,e,f,g,q},x] && IGtQ[n,0] && LtQ[p,-1] && GtQ[m-n+1,0]",
        desc: "Binomial product recurrence 3a",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, q_, x_],
        optional: [g__, m_, b__, d__, f__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, q_], x_)
                && igtq!(n_, 0)
                && ltq!(p_, -1)
                && gtq!(&m_ - &n_ + Atom::num(1), 0)
        },
        rhs: {
            let first_base = &a__ + &b__ * x_.pow(&n_);
            let second_base = &c__ + &d__ * x_.pow(&n_);
            let det = &b__ * &c__ - &a__ * &d__;
            let be_af = &b__ * &e__ - &a__ * &f__;
            let denominator = &b__ * &n_ * &det * (&p_ + Atom::num(1));
            let direct = g__.pow(&n_ - Atom::num(1))
                * &be_af
                * (&g__ * x_).pow(&m_ - &n_ + Atom::num(1))
                * first_base.pow(&p_ + Atom::num(1))
                * second_base.pow(&q_ + Atom::num(1))
                / &denominator;
            let payload = &c__ * &be_af * (&m_ - &n_ + Atom::num(1))
                + (&d__ * &be_af * (&m_ + &n_ * &q_ + Atom::num(1))
                    - &b__ * &n_ * (&c__ * &f__ - &d__ * &e__) * (&p_ + Atom::num(1)))
                    * x_.pow(&n_);
            let recursive_integrand = (&g__ * x_).pow(&m_ - &n_)
                * first_base.pow(&p_ + Atom::num(1))
                * second_base.pow(&q_)
                * simp!(payload, x_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) - rubi_star(g__.pow(&n_) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_1049(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1049,
        source: "Int[(g_.*x_)^m_.*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_*(e_+f_.*x_^n_),x_Symbol] :=
          -(b*e-a*f)*(g*x)^(m+1)*(a+b*x^n)^(p+1)*(c+d*x^n)^(q+1)/(a*g*n*(b*c-a*d)*(p+1)) +
          1/(a*n*(b*c-a*d)*(p+1)) \\[Star] Int[(g*x)^m*(a+b*x^n)^(p+1)*(c+d*x^n)^q*
            Simp[c*(b*e-a*f)*(m+1)+e*n*(b*c-a*d)*(p+1)+d*(b*e-a*f)*(m+n*(p+q+2)+1)*x^n,x],x] /;
        FreeQ[{a,b,c,d,e,f,g,m,q},x] && IGtQ[n,0] && LtQ[p,-1]",
        desc: "Binomial product recurrence 3b",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, q_, x_],
        optional: [g__, m_, b__, d__, f__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, m_, q_], x_)
                && igtq!(n_, 0)
                && ltq!(p_, -1)
        },
        rhs: {
            let first_base = &a__ + &b__ * x_.pow(&n_);
            let second_base = &c__ + &d__ * x_.pow(&n_);
            let det = &b__ * &c__ - &a__ * &d__;
            let be_af = &b__ * &e__ - &a__ * &f__;
            let denominator = &a__ * &n_ * &det * (&p_ + Atom::num(1));
            let direct = -&be_af
                * (&g__ * x_).pow(&m_ + Atom::num(1))
                * first_base.pow(&p_ + Atom::num(1))
                * second_base.pow(&q_ + Atom::num(1))
                / (&g__ * &denominator);
            let payload = &c__ * &be_af * (&m_ + Atom::num(1))
                + &e__ * &n_ * &det * (&p_ + Atom::num(1))
                + &d__ * &be_af * (&m_ + &n_ * (&p_ + &q_ + Atom::num(2)) + Atom::num(1)) * x_.pow(&n_);
            let recursive_integrand = (&g__ * x_).pow(&m_)
                * first_base.pow(&p_ + Atom::num(1))
                * second_base.pow(&q_)
                * simp!(payload, x_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_1050(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1050,
        source: "Int[(g_.*x_)^m_*(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_)^q_.*(e_+f_.*x_^n_),x_Symbol] :=
          e*(g*x)^(m+1)*(a+b*x^n)^(p+1)*(c+d*x^n)^q/(a*g*(m+1)) -
          1/(a*g^n*(m+1)) \\[Star] Int[(g*x)^(m+n)*(a+b*x^n)^p*(c+d*x^n)^(q-1)*
            Simp[c*(b*e-a*f)*(m+1)+e*n*(b*c*(p+1)+a*d*q)+d*((b*e-a*f)*(m+1)+b*e*n*(p+q+1))*x^n,x],x] /;
        FreeQ[{a,b,c,d,e,f,g,p},x] && IGtQ[n,0] && GtQ[q,0] && LtQ[m,-1] && Not[EqQ[q,1] && SimplerQ[e+f*x^n,c+d*x^n]]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, q_, x_],
        optional: [g__, b__, d__, f__, p_, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, p_], x_)
                && igtq!(n_, 0)
                && gtq!(q_, 0)
                && ltq!(m_, -1)
                && !(eqq!(q_, 1)
                    && simplerq!(&e__ + &f__ * x_.pow(&n_), &c__ + &d__ * x_.pow(&n_)))
        },
        rhs: {
            let first_base = &a__ + &b__ * x_.pow(&n_);
            let second_base = &c__ + &d__ * x_.pow(&n_);
            let be_af = &b__ * &e__ - &a__ * &f__;
            let direct = &e__
                * (&g__ * x_).pow(&m_ + Atom::num(1))
                * first_base.pow(&p_ + Atom::num(1))
                * second_base.pow(&q_)
                / (&a__ * &g__ * (&m_ + Atom::num(1)));
            let payload = &c__ * &be_af * (&m_ + Atom::num(1))
                + &e__ * &n_ * (&b__ * &c__ * (&p_ + Atom::num(1)) + &a__ * &d__ * &q_)
                + &d__
                    * (&be_af * (&m_ + Atom::num(1)) + &b__ * &e__ * &n_ * (&p_ + &q_ + Atom::num(1)))
                    * x_.pow(&n_);
            let recursive_integrand = (&g__ * x_).pow(&m_ + &n_)
                * first_base.pow(&p_)
                * second_base.pow(&q_ - Atom::num(1))
                * simp!(payload, x_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_)
                    - rubi_star(Atom::num(1) / (&a__ * g__.pow(&n_) * (&m_ + Atom::num(1))), recursive)
        },
    ));
}

fn push_rules_rule_1051(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1051,
        source: "Int[(g_.*x_)^m_.*(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_)^q_.*(e_+f_.*x_^n_),x_Symbol] :=
          f*(g*x)^(m+1)*(a+b*x^n)^(p+1)*(c+d*x^n)^q/(b*g*(m+n*(p+q+1)+1)) +
          1/(b*(m+n*(p+q+1)+1)) \\[Star] Int[(g*x)^m*(a+b*x^n)^p*(c+d*x^n)^(q-1)*
            Simp[c*((b*e-a*f)*(m+1)+b*e*n*(p+q+1))+(d*(b*e-a*f)*(m+1)+f*n*q*(b*c-a*d)+b*e*d*n*(p+q+1))*x^n,x],x] /;
        FreeQ[{a,b,c,d,e,f,g,m,p},x] && IGtQ[n,0] && GtQ[q,0] && Not[EqQ[q,1] && SimplerQ[e+f*x^n,c+d*x^n]]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, q_, x_],
        optional: [g__, m_, b__, d__, f__, p_, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, m_, p_], x_)
                && igtq!(n_, 0)
                && gtq!(q_, 0)
                && !(eqq!(q_, 1)
                    && simplerq!(&e__ + &f__ * x_.pow(&n_), &c__ + &d__ * x_.pow(&n_)))
        },
        rhs: {
            let first_base = &a__ + &b__ * x_.pow(&n_);
            let second_base = &c__ + &d__ * x_.pow(&n_);
            let be_af = &b__ * &e__ - &a__ * &f__;
            let denominator = &m_ + &n_ * (&p_ + &q_ + Atom::num(1)) + Atom::num(1);
            let direct = &f__
                * (&g__ * x_).pow(&m_ + Atom::num(1))
                * first_base.pow(&p_ + Atom::num(1))
                * second_base.pow(&q_)
                / (&b__ * &g__ * &denominator);
            let payload = &c__ * (&be_af * (&m_ + Atom::num(1)) + &b__ * &e__ * &n_ * (&p_ + &q_ + Atom::num(1)))
                + (&d__ * &be_af * (&m_ + Atom::num(1))
                    + &f__ * &n_ * &q_ * (&b__ * &c__ - &a__ * &d__)
                    + &b__ * &e__ * &d__ * &n_ * (&p_ + &q_ + Atom::num(1)))
                    * x_.pow(&n_);
            let recursive_integrand = (&g__ * x_).pow(&m_)
                * first_base.pow(&p_)
                * second_base.pow(&q_ - Atom::num(1))
                * simp!(payload, x_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / (&b__ * denominator), recursive)
        },
    ));
}

fn push_rules_rule_1052(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1052,
        source: "Int[(g_.*x_)^m_.*(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_)^q_.*(e_+f_.*x_^n_),x_Symbol] :=
          f*g^(n-1)*(g*x)^(m-n+1)*(a+b*x^n)^(p+1)*(c+d*x^n)^(q+1)/(b*d*(m+n*(p+q+1)+1)) -
          g^n/(b*d*(m+n*(p+q+1)+1)) \\[Star] Int[(g*x)^(m-n)*(a+b*x^n)^p*(c+d*x^n)^q*
            Simp[a*f*c*(m-n+1)+(a*f*d*(m+n*q+1)+b*(f*c*(m+n*p+1)-e*d*(m+n*(p+q+1)+1)))*x^n,x],x] /;
        FreeQ[{a,b,c,d,e,f,g,p,q},x] && IGtQ[n,0] && GtQ[m,n-1]",
        desc: "Binomial product recurrence 4a",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, q_, x_],
        optional: [g__, m_, b__, d__, f__, p_, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, p_, q_], x_)
                && igtq!(n_, 0)
                && gtq!(m_, &n_ - Atom::num(1))
        },
        rhs: {
            let first_base = &a__ + &b__ * x_.pow(&n_);
            let second_base = &c__ + &d__ * x_.pow(&n_);
            let denominator = &m_ + &n_ * (&p_ + &q_ + Atom::num(1)) + Atom::num(1);
            let direct = &f__
                * g__.pow(&n_ - Atom::num(1))
                * (&g__ * x_).pow(&m_ - &n_ + Atom::num(1))
                * first_base.pow(&p_ + Atom::num(1))
                * second_base.pow(&q_ + Atom::num(1))
                / (&b__ * &d__ * &denominator);
            let payload = &a__ * &f__ * &c__ * (&m_ - &n_ + Atom::num(1))
                + (&a__ * &f__ * &d__ * (&m_ + &n_ * &q_ + Atom::num(1))
                    + &b__
                        * (&f__ * &c__ * (&m_ + &n_ * &p_ + Atom::num(1))
                            - &e__ * &d__ * (&m_ + &n_ * (&p_ + &q_ + Atom::num(1)) + Atom::num(1))))
                    * x_.pow(&n_);
            let recursive_integrand = (&g__ * x_).pow(&m_ - &n_)
                * first_base.pow(&p_)
                * second_base.pow(&q_)
                * simp!(payload, x_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_)
                    - rubi_star(g__.pow(&n_) / (&b__ * &d__ * denominator), recursive)
        },
    ));
}

fn push_rules_rule_1053(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1053,
        source: "Int[(g_.*x_)^m_*(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_)^q_.*(e_+f_.*x_^n_),x_Symbol] :=
          e*(g*x)^(m+1)*(a+b*x^n)^(p+1)*(c+d*x^n)^(q+1)/(a*c*g*(m+1)) +
          1/(a*c*g^n*(m+1)) \\[Star] Int[(g*x)^(m+n)*(a+b*x^n)^p*(c+d*x^n)^q*
            Simp[a*f*c*(m+1)-e*(b*c+a*d)*(m+n+1)-e*n*(b*c*p+a*d*q)-b*e*d*(m+n*(p+q+2)+1)*x^n,x],x] /;
        FreeQ[{a,b,c,d,e,f,g,p,q},x] && IGtQ[n,0] && LtQ[m,-1]",
        desc: "Binomial product recurrence 4b",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, q_, x_],
        optional: [g__, b__, d__, f__, p_, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, p_, q_], x_)
                && igtq!(n_, 0)
                && ltq!(m_, -1)
        },
        rhs: {
            let first_base = &a__ + &b__ * x_.pow(&n_);
            let second_base = &c__ + &d__ * x_.pow(&n_);
            let direct = &e__
                * (&g__ * x_).pow(&m_ + Atom::num(1))
                * first_base.pow(&p_ + Atom::num(1))
                * second_base.pow(&q_ + Atom::num(1))
                / (&a__ * &c__ * &g__ * (&m_ + Atom::num(1)));
            let payload = &a__ * &f__ * &c__ * (&m_ + Atom::num(1))
                - &e__ * (&b__ * &c__ + &a__ * &d__) * (&m_ + &n_ + Atom::num(1))
                - &e__ * &n_ * (&b__ * &c__ * &p_ + &a__ * &d__ * &q_)
                - &b__ * &e__ * &d__ * (&m_ + &n_ * (&p_ + &q_ + Atom::num(2)) + Atom::num(1)) * x_.pow(&n_);
            let recursive_integrand = (&g__ * x_).pow(&m_ + &n_)
                * first_base.pow(&p_)
                * second_base.pow(&q_)
                * simp!(payload, x_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_)
                    + rubi_star(Atom::num(1)
                            / (&a__ * &c__ * g__.pow(&n_) * (&m_ + Atom::num(1))), recursive)
        },
    ));
}

fn push_rules_rule_1054(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 1054,
        source: "Int[(g_.*x_)^m_.*(a_+b_.*x_^n_)^p_*(e_+f_.*x_^n_)/(c_+d_.*x_^n_),x_Symbol] :=
          Int[ExpandIntegrand[(g*x)^m*(a+b*x^n)^p*(e+f*x^n)/(c+d*x^n),x],x] /;
        FreeQ[{a,b,c,d,e,f,g,m,p},x] && IGtQ[n,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_],
        optional: [g__, m_, b__, d__, f__],
        when: { freeq!([a__, b__, c__, d__, e__, f__, g__, m_, p_], x_) && igtq!(n_, 0) },
        rhs: {
            let integrand = (&g__ * x_).pow(&m_)
                * (&a__ + &b__ * x_.pow(&n_)).pow(&p_)
                * (&e__ + &f__ * x_.pow(&n_))
                / (&c__ + &d__ * x_.pow(&n_));
            let expanded = rubi_expand_integrand(&integrand, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_1055(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1055,
        source: "Int[(g_.*x_)^m_.*(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_)^q_.*(e_+f_.*x_^n_),x_Symbol] :=
          e \\[Star] Int[(g*x)^m*(a+b*x^n)^p*(c+d*x^n)^q,x] +
          f/e^n \\[Star] Int[(g*x)^(m+n)*(a+b*x^n)^p*(c+d*x^n)^q,x] /;
        FreeQ[{a,b,c,d,e,f,g,m,p,q},x] && IGtQ[n,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, q_, x_],
        optional: [g__, m_, b__, d__, f__, p_, q_],
        when: { freeq!([a__, b__, c__, d__, e__, f__, g__, m_, p_, q_], x_) && igtq!(n_, 0) },
        rhs: {
            let first_integrand =
                (&g__ * x_).pow(&m_) * (&a__ + &b__ * x_.pow(&n_)).pow(&p_) * (&c__ + &d__ * x_.pow(&n_)).pow(&q_);
            let second_integrand = (&g__ * x_).pow(&m_ + &n_)
                * (&a__ + &b__ * x_.pow(&n_)).pow(&p_)
                * (&c__ + &d__ * x_.pow(&n_)).pow(&q_);
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(&e__, first)
                    + rubi_star(&f__ / e__.pow(&n_), second)
        },
    ));
}

fn push_rules_rule_1056(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 1056,
        source: "Int[(g_.*x_)^m_.*(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_)^q_.*(e_+f_.*x_^n_)^r_.,x_Symbol] :=
          e \\[Star] Int[(g*x)^m*(a+b*x^n)^p*(c+d*x^n)^q*(e+f*x^n)^(r-1),x] +
          f/e^n \\[Star] Int[(g*x)^(m+n)*(a+b*x^n)^p*(c+d*x^n)^q*(e+f*x^n)^(r-1),x] /;
        FreeQ[{a,b,c,d,e,f,g,m,p,q},x] && IGtQ[n,0] && IGtQ[r,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, q_, r_, x_],
        optional: [g__, m_, b__, d__, f__, p_, q_, r_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, m_, p_, q_], x_)
                && igtq!(n_, 0)
                && igtq!(r_, 0)
        },
        rhs: {
            let first_integrand = (&g__ * x_).pow(&m_)
                * (&a__ + &b__ * x_.pow(&n_)).pow(&p_)
                * (&c__ + &d__ * x_.pow(&n_)).pow(&q_)
                * (&e__ + &f__ * x_.pow(&n_)).pow(&r_ - Atom::num(1));
            let second_integrand = (&g__ * x_).pow(&m_ + &n_)
                * (&a__ + &b__ * x_.pow(&n_)).pow(&p_)
                * (&c__ + &d__ * x_.pow(&n_)).pow(&q_)
                * (&e__ + &f__ * x_.pow(&n_)).pow(&r_ - Atom::num(1));
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(&e__, first)
                    + rubi_star(&f__ / e__.pow(&n_), second)
        },
    ));
}

fn push_rules_rule_1057(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, p_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 1057,
        source: "Int[x_^m_.*(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_)^q_.*(e_+f_.*x_^n_)^r_.,x_Symbol] :=
          -Subst[Int[(a+b*x^(-n))^p*(c+d*x^(-n))^q*(e+f*x^(-n))^r/x^(m+2),x],x,1/x] /;
        FreeQ[{a,b,c,d,e,f,p,q,r},x] && ILtQ[n,0] && IntegerQ[m]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [a__, b__, c__, d__, e__, f__, m_, n_, p_, q_, r_, x_],
        optional: [m_, b__, d__, f__, p_, q_, r_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, p_, q_, r_], x_)
                && iltq!(n_, 0)
                && integerq!(m_)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = (&a__ + &b__ * sub_atom.pow(-&n_)).pow(&p_)
                * (&c__ + &d__ * sub_atom.pow(-&n_)).pow(&q_)
                * (&e__ + &f__ * sub_atom.pow(-&n_)).pow(&r_)
                / sub_atom.pow(&m_ + Atom::num(2));
            let transformed = rubi_rhs_int(&transformed_integrand, sub);

            -rubi_subst(
                &transformed,
                sub,
                Atom::num(1) / x_,
            )
        },
    ));
}

fn push_rules_rule_1058(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 1058,
        source: "Int[(g_.*x_)^m_*(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_)^q_.*(e_+f_.*x_^n_)^r_.,x_Symbol] :=
          With[{k=Denominator[m]},
          -k/g \\[Star] Subst[Int[(a+b*g^(-n)*x^(-k*n))^p*(c+d*g^(-n)*x^(-k*n))^q*(e+f*g^(-n)*x^(-k*n))^r/x^(k*(m+1)+1),x],x,1/(g*x)^(1/k)]] /;
        FreeQ[{a,b,c,d,e,f,g,p,q,r},x] && ILtQ[n,0] && FractionQ[m]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, q_, r_, x_],
        optional: [g__, b__, d__, f__, p_, q_, r_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, p_, q_, r_], x_)
                && iltq!(n_, 0)
                && fractionq!(m_)
        },
        rhs: {
            let k_i = rational_denominator(&m_).rubi_rhs();
            let k = Atom::num(k_i);
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_power = (-&k * &n_).expand();
            let transformed_integrand = (&a__ + &b__ * g__.pow(-&n_) * sub_atom.pow(&transformed_power)).pow(&p_)
                * (&c__ + &d__ * g__.pow(-&n_) * sub_atom.pow(&transformed_power)).pow(&q_)
                * (&e__ + &f__ * g__.pow(-&n_) * sub_atom.pow(&transformed_power)).pow(&r_)
                / sub_atom.pow(&k * (&m_ + Atom::num(1)) + Atom::num(1));
            let transformed = rubi_rhs_int(&transformed_integrand, sub);
            let replacement = Atom::num(1) / (&g__ * x_).pow(Atom::num(1) / &k);
            let substituted = rubi_subst(&transformed, sub, replacement);

            rubi_star(-&k / g__, substituted)
        },
    ));
}

fn push_rules_rule_1059(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 1059,
        source: "Int[(g_.*x_)^m_*(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_)^q_.*(e_+f_.*x_^n_)^r_.,x_Symbol] :=
          -(g*x)^m*(x^(-1))^m \\[Star] Subst[Int[(a+b*x^(-n))^p*(c+d*x^(-n))^q*(e+f*x^(-n))^r/x^(m+2),x],x,1/x] /;
        FreeQ[{a,b,c,d,e,f,g,m,p,q,r},x] && ILtQ[n,0] && Not[RationalQ[m]]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, q_, r_, x_],
        optional: [g__, b__, d__, f__, p_, q_, r_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, m_, p_, q_, r_], x_)
                && iltq!(n_, 0)
                && !rationalq!(m_)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = (&a__ + &b__ * sub_atom.pow(-&n_)).pow(&p_)
                * (&c__ + &d__ * sub_atom.pow(-&n_)).pow(&q_)
                * (&e__ + &f__ * sub_atom.pow(-&n_)).pow(&r_)
                / sub_atom.pow(&m_ + Atom::num(2));
            let transformed = rubi_rhs_int(&transformed_integrand, sub);
            let substituted = rubi_subst(&transformed, sub, Atom::num(1) / x_);

            rubi_star(-(&g__ * x_).pow(&m_) * x_.pow(-Atom::num(1)).pow(&m_), substituted)
        },
    ));
}

fn push_rules_rule_1060(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, p_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 1060,
        source: "Int[x_^m_.*(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_)^q_.*(e_+f_.*x_^n_)^r_.,x_Symbol] :=
          With[{k=Denominator[n]},
          k \\[Star] Subst[Int[x^(k*(m+1)-1)*(a+b*x^(k*n))^p*(c+d*x^(k*n))^q*(e+f*x^(k*n))^r,x],x,x^(1/k)]] /;
        FreeQ[{a,b,c,d,e,f,m,p,q,r},x] && FractionQ[n]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [a__, b__, c__, d__, e__, f__, m_, n_, p_, q_, r_, x_],
        optional: [m_, b__, d__, f__, p_, q_, r_],
        when: { freeq!([a__, b__, c__, d__, e__, f__, m_, p_, q_, r_], x_) && fractionq!(n_) },
        rhs: {
            let k_i = rational_denominator(&n_).rubi_rhs();
            let k = Atom::num(k_i);
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = sub_atom.pow(&k * (&m_ + Atom::num(1)) - Atom::num(1))
                * (&a__ + &b__ * sub_atom.pow(&k * &n_)).pow(&p_)
                * (&c__ + &d__ * sub_atom.pow(&k * &n_)).pow(&q_)
                * (&e__ + &f__ * sub_atom.pow(&k * &n_)).pow(&r_);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);
            let replacement = x_.pow(Atom::num(1) / &k);
            let substituted = rubi_subst(&transformed, sub, replacement);

            rubi_star(k, substituted)
        },
    ));
}

fn push_rules_rule_1061(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 1061,
        source: "Int[(g_*x_)^m_*(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_)^q_.*(e_+f_.*x_^n_)^r_.,x_Symbol] :=
          g^IntPart[m]*(g*x)^FracPart[m]/x^FracPart[m] \\[Star] Int[x^m*(a+b*x^n)^p*(c+d*x^n)^q*(e+f*x^n)^r,x] /;
        FreeQ[{a,b,c,d,e,f,g,m,p,q,r},x] && FractionQ[n]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, q_, r_, x_],
        optional: [b__, d__, f__, p_, q_, r_],
        when: { freeq!([a__, b__, c__, d__, e__, f__, g__, m_, p_, q_, r_], x_) && fractionq!(n_) },
        rhs: {
            let frac_m = rubi_frac_part(&m_);
            let recursive_integrand = x_.pow(&m_)
                * (&a__ + &b__ * x_.pow(&n_)).pow(&p_)
                * (&c__ + &d__ * x_.pow(&n_)).pow(&q_)
                * (&e__ + &f__ * x_.pow(&n_)).pow(&r_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(g__.pow(rubi_int_part(&m_)) * (&g__ * x_).pow(&frac_m)
                    / x_.pow(frac_m), recursive)
        },
    ));
}

fn push_rules_rule_1062(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, n_, p_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 1062,
        source: "Int[x_^m_.*(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_)^q_.*(e_+f_.*x_^n_)^r_.,x_Symbol] :=
          1/(m+1) \\[Star] Subst[Int[(a+b*x^Simplify[n/(m+1)])^p*(c+d*x^Simplify[n/(m+1)])^q*(e+f*x^Simplify[n/(m+1)])^r,x],x,x^(m+1)] /;
        FreeQ[{a,b,c,d,e,f,m,n,p,q,r},x] && IntegerQ[Simplify[n/(m+1)]]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [a__, b__, c__, d__, e__, f__, m_, n_, p_, q_, r_, x_],
        optional: [m_, b__, d__, f__, p_, q_, r_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_, p_, q_, r_], x_)
                && integerq!(rubi_simplify(&(&n_ / (&m_ + Atom::num(1)))))
        },
        rhs: {
            let k = rubi_simplify(&(&n_ / (&m_ + Atom::num(1))));
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = (&a__ + &b__ * sub_atom.pow(&k)).pow(&p_)
                * (&c__ + &d__ * sub_atom.pow(&k)).pow(&q_)
                * (&e__ + &f__ * sub_atom.pow(&k)).pow(&r_);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);
            let substituted = rubi_subst(
                &transformed,
                sub,
                x_.pow(&m_ + Atom::num(1)),
            );

            rubi_star(Atom::num(1) / (&m_ + Atom::num(1)), substituted)
        },
    ));
}

fn push_rules_rule_1063(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 1063,
        source: "Int[(g_*x_)^m_.*(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_)^q_.*(e_+f_.*x_^n_)^r_.,x_Symbol] :=
          g^IntPart[m]*(g*x)^FracPart[m]/x^FracPart[m] \\[Star] Int[x^m*(a+b*x^n)^p*(c+d*x^n)^q*(e+f*x^n)^r,x] /;
        FreeQ[{a,b,c,d,e,f,g,m,n,p,q,r},x] && IntegerQ[Simplify[n/(m+1)]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, q_, r_, x_],
        optional: [m_, b__, d__, f__, p_, q_, r_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, q_, r_], x_)
                && integerq!(rubi_simplify(&(&n_ / (&m_ + Atom::num(1)))))
        },
        rhs: {
            let frac_m = rubi_frac_part(&m_);
            let recursive_integrand = x_.pow(&m_)
                * (&a__ + &b__ * x_.pow(&n_)).pow(&p_)
                * (&c__ + &d__ * x_.pow(&n_)).pow(&q_)
                * (&e__ + &f__ * x_.pow(&n_)).pow(&r_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(g__.pow(rubi_int_part(&m_)) * (&g__ * x_).pow(&frac_m)
                    / x_.pow(frac_m), recursive)
        },
    ));
}

fn push_rules_rule_1064(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1064,
        source: "Int[(g_.*x_)^m_.*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_.*(e_+f_.*x_^n_),x_Symbol] :=
          -(b*e-a*f)*(g*x)^(m+1)*(a+b*x^n)^(p+1)*(c+d*x^n)^q/(a*b*g*n*(p+1)) +
          1/(a*b*n*(p+1)) \\[Star] Int[(g*x)^m*(a+b*x^n)^(p+1)*(c+d*x^n)^(q-1)*
            Simp[c*(b*e*n*(p+1)+(b*e-a*f)*(m+1))+d*(b*e*n*(p+1)+(b*e-a*f)*(m+n*q+1))*x^n,x],x] /;
        FreeQ[{a,b,c,d,e,f,g,m,n},x] && LtQ[p,-1] && GtQ[q,0] && Not[EqQ[q,1] && SimplerQ[b*c-a*d,b*e-a*f]]",
        desc: "Binomial product recurrence 1",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, q_, x_],
        optional: [g__, m_, b__, d__, f__, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, m_, n_], x_)
                && ltq!(p_, -1)
                && gtq!(q_, 0)
                && !(eqq!(q_, 1) && simplerq!(&b__ * &c__ - &a__ * &d__, &b__ * &e__ - &a__ * &f__))
        },
        rhs: {
            let first_base = &a__ + &b__ * x_.pow(&n_);
            let second_base = &c__ + &d__ * x_.pow(&n_);
            let be_af = &b__ * &e__ - &a__ * &f__;
            let direct = -&be_af
                * (&g__ * x_).pow(&m_ + Atom::num(1))
                * first_base.pow(&p_ + Atom::num(1))
                * second_base.pow(&q_)
                / (&a__ * &b__ * &g__ * &n_ * (&p_ + Atom::num(1)));
            let payload = &c__
                * (&b__ * &e__ * &n_ * (&p_ + Atom::num(1)) + &be_af * (&m_ + Atom::num(1)))
                + &d__
                    * (&b__ * &e__ * &n_ * (&p_ + Atom::num(1))
                        + &be_af * (&m_ + &n_ * &q_ + Atom::num(1)))
                    * x_.pow(&n_);
            let recursive_integrand = (&g__ * x_).pow(&m_)
                * first_base.pow(&p_ + Atom::num(1))
                * second_base.pow(&q_ - Atom::num(1))
                * simp!(payload, x_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_)
                    + rubi_star(Atom::num(1) / (&a__ * &b__ * &n_ * (&p_ + Atom::num(1))), recursive)
        },
    ));
}

fn push_rules_rule_1065(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1065,
        source: "Int[(g_.*x_)^m_.*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_*(e_+f_.*x_^n_),x_Symbol] :=
          -(b*e-a*f)*(g*x)^(m+1)*(a+b*x^n)^(p+1)*(c+d*x^n)^(q+1)/(a*g*n*(b*c-a*d)*(p+1)) +
          1/(a*n*(b*c-a*d)*(p+1)) \\[Star] Int[(g*x)^m*(a+b*x^n)^(p+1)*(c+d*x^n)^q*
            Simp[c*(b*e-a*f)*(m+1)+e*n*(b*c-a*d)*(p+1)+d*(b*e-a*f)*(m+n*(p+q+2)+1)*x^n,x],x] /;
        FreeQ[{a,b,c,d,e,f,g,m,n,q},x] && LtQ[p,-1]",
        desc: "Binomial product recurrence 3b",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, q_, x_],
        optional: [g__, m_, b__, d__, f__],
        when: { freeq!([a__, b__, c__, d__, e__, f__, g__, m_, n_, q_], x_) && ltq!(p_, -1) },
        rhs: {
            let first_base = &a__ + &b__ * x_.pow(&n_);
            let second_base = &c__ + &d__ * x_.pow(&n_);
            let be_af = &b__ * &e__ - &a__ * &f__;
            let bc_ad = &b__ * &c__ - &a__ * &d__;
            let direct = -&be_af
                * (&g__ * x_).pow(&m_ + Atom::num(1))
                * first_base.pow(&p_ + Atom::num(1))
                * second_base.pow(&q_ + Atom::num(1))
                / (&a__ * &g__ * &n_ * &bc_ad * (&p_ + Atom::num(1)));
            let payload = &c__ * &be_af * (&m_ + Atom::num(1))
                + &e__ * &n_ * &bc_ad * (&p_ + Atom::num(1))
                + &d__ * &be_af * (&m_ + &n_ * (&p_ + &q_ + Atom::num(2)) + Atom::num(1)) * x_.pow(&n_);
            let recursive_integrand = (&g__ * x_).pow(&m_)
                * first_base.pow(&p_ + Atom::num(1))
                * second_base.pow(&q_)
                * simp!(payload, x_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_)
                    + rubi_star(Atom::num(1) / (&a__ * &n_ * bc_ad * (&p_ + Atom::num(1))), recursive)
        },
    ));
}

fn push_rules_rule_1066(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1066,
        source: "Int[(g_.*x_)^m_.*(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_)^q_.*(e_+f_.*x_^n_),x_Symbol] :=
          f*(g*x)^(m+1)*(a+b*x^n)^(p+1)*(c+d*x^n)^q/(b*g*(m+n*(p+q+1)+1)) +
          1/(b*(m+n*(p+q+1)+1)) \\[Star] Int[(g*x)^m*(a+b*x^n)^p*(c+d*x^n)^(q-1)*
            Simp[c*((b*e-a*f)*(m+1)+b*e*n*(p+q+1))+(d*(b*e-a*f)*(m+1)+f*n*q*(b*c-a*d)+b*e*d*n*(p+q+1))*x^n,x],x] /;
        FreeQ[{a,b,c,d,e,f,g,m,n,p},x] && GtQ[q,0] && Not[EqQ[q,1] && SimplerQ[e+f*x^n,c+d*x^n]]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, q_, x_],
        optional: [g__, m_, b__, d__, f__, p_, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, m_, n_, p_], x_)
                && gtq!(q_, 0)
                && !(eqq!(q_, 1)
                    && simplerq!(&e__ + &f__ * x_.pow(&n_), &c__ + &d__ * x_.pow(&n_)))
        },
        rhs: {
            let first_base = &a__ + &b__ * x_.pow(&n_);
            let second_base = &c__ + &d__ * x_.pow(&n_);
            let be_af = &b__ * &e__ - &a__ * &f__;
            let bc_ad = &b__ * &c__ - &a__ * &d__;
            let denominator = &m_ + &n_ * (&p_ + &q_ + Atom::num(1)) + Atom::num(1);
            let direct = &f__
                * (&g__ * x_).pow(&m_ + Atom::num(1))
                * first_base.pow(&p_ + Atom::num(1))
                * second_base.pow(&q_)
                / (&b__ * &g__ * &denominator);
            let payload = &c__ * (&be_af * (&m_ + Atom::num(1)) + &b__ * &e__ * &n_ * (&p_ + &q_ + Atom::num(1)))
                + (&d__ * &be_af * (&m_ + Atom::num(1))
                    + &f__ * &n_ * &q_ * &bc_ad
                    + &b__ * &e__ * &d__ * &n_ * (&p_ + &q_ + Atom::num(1)))
                    * x_.pow(&n_);
            let recursive_integrand = (&g__ * x_).pow(&m_)
                * first_base.pow(&p_)
                * second_base.pow(&q_ - Atom::num(1))
                * simp!(payload, x_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / (&b__ * denominator), recursive)
        },
    ));
}

fn push_rules_rule_1067(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 1067,
        source: "Int[(g_.*x_)^m_.*(a_+b_.*x_^n_)^p_*(e_+f_.*x_^n_)/(c_+d_.*x_^n_),x_Symbol] :=
          Int[ExpandIntegrand[(g*x)^m*(a+b*x^n)^p*(e+f*x^n)/(c+d*x^n),x],x] /;
        FreeQ[{a,b,c,d,e,f,g,m,n,p},x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, x_],
        optional: [g__, m_, b__, d__, f__],
        when: { freeq!([a__, b__, c__, d__, e__, f__, g__, m_, n_, p_], x_) },
        rhs: {
            let integrand = (&g__ * x_).pow(&m_)
                * (&a__ + &b__ * x_.pow(&n_)).pow(&p_)
                * (&e__ + &f__ * x_.pow(&n_))
                / (&c__ + &d__ * x_.pow(&n_));
            let expanded = rubi_expand_integrand(&integrand, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_1068(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1068,
        source: "Int[(g_.*x_)^m_.*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_*(e_+f_.*x_^n_),x_Symbol] :=
          e \\[Star] Int[(g*x)^m*(a+b*x^n)^p*(c+d*x^n)^q,x] +
          f*(g*x)^m/x^m \\[Star] Int[x^(m+n)*(a+b*x^n)^p*(c+d*x^n)^q,x] /;
        FreeQ[{a,b,c,d,e,f,g,m,n,p,q},x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, q_, x_],
        optional: [g__, m_, b__, d__, f__],
        when: { freeq!([a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, q_], x_) },
        rhs: {
            let first_integrand =
                (&g__ * x_).pow(&m_) * (&a__ + &b__ * x_.pow(&n_)).pow(&p_) * (&c__ + &d__ * x_.pow(&n_)).pow(&q_);
            let second_integrand = x_.pow(&m_ + &n_)
                * (&a__ + &b__ * x_.pow(&n_)).pow(&p_)
                * (&c__ + &d__ * x_.pow(&n_)).pow(&q_);
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(e__, first)
                    + rubi_star(&f__ * (&g__ * x_).pow(&m_) / x_.pow(&m_), second)
        },
    ));
}

fn push_rules_rule_1069(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, mn_, n_, p_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 1069,
        source: "Int[x_^m_.*(a_+b_.*x_^n_.)^p_.*(c_+d_.*x_^mn_.)^q_.*(e_+f_.*x_^n_.)^r_.,x_Symbol] :=
          Int[x^(m-n*q)*(a+b*x^n)^p*(d+c*x^n)^q*(e+f*x^n)^r,x] /;
        FreeQ[{a,b,c,d,e,f,m,n,p,r},x] && EqQ[mn,-n] && IntegerQ[q]",
        desc: "Algebraic normalization",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [a__, b__, c__, d__, e__, f__, m_, n_, mn_, p_, q_, r_, x_],
        optional: [m_, b__, n_, p_, d__, mn_, q_, f__, r_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_, p_, r_], x_)
                && eqq!(mn_, -&n_)
                && integerq!(q_)
        },
        rhs: {
            let recursive_integrand = x_.pow(&m_ - &n_ * &q_)
                * (&a__ + &b__ * x_.pow(&n_)).pow(&p_)
                * (&d__ + &c__ * x_.pow(&n_)).pow(&q_)
                * (&e__ + &f__ * x_.pow(&n_)).pow(&r_);
            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_1070(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, mn_, n_, p_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 1070,
        source: "Int[x_^m_.*(a_.+b_.*x_^n_.)^p_.*(c_+d_.*x_^mn_.)^q_.*(e_+f_.*x_^n_.)^r_.,x_Symbol] :=
          Int[x^(m+n*(p+r))*(b+a*x^(-n))^p*(c+d*x^(-n))^q*(f+e*x^(-n))^r,x] /;
        FreeQ[{a,b,c,d,e,f,m,n,q},x] && EqQ[mn,-n] && IntegerQ[p] && IntegerQ[r]",
        desc: "Algebraic normalization",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [a__, b__, c__, d__, e__, f__, m_, n_, mn_, p_, q_, r_, x_],
        optional: [m_, a__, b__, n_, p_, d__, mn_, q_, f__, r_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_, q_], x_)
                && eqq!(mn_, -&n_)
                && integerq!(p_)
                && integerq!(r_)
        },
        rhs: {
            let recursive_integrand = x_.pow(&m_ + &n_ * (&p_ + &r_))
                * (&b__ + &a__ * x_.pow(-&n_)).pow(&p_)
                * (&c__ + &d__ * x_.pow(-&n_)).pow(&q_)
                * (&f__ + &e__ * x_.pow(-&n_)).pow(&r_);
            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_1071(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, mn_, n_, p_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 1071,
        source: "Int[x_^m_.*(a_.+b_.*x_^n_.)^p_.*(c_+d_.*x_^mn_.)^q_*(e_+f_.*x_^n_.)^r_.,x_Symbol] :=
          x^(n*FracPart[q])*(c+d*x^(-n))^FracPart[q]/(d+c*x^n)^FracPart[q] \\[Star] Int[x^(m-n*q)*(a+b*x^n)^p*(d+c*x^n)^q*(e+f*x^n)^r,x] /;
        FreeQ[{a,b,c,d,e,f,m,n,p,q,r},x] && EqQ[mn,-n] && Not[IntegerQ[q]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [a__, b__, c__, d__, e__, f__, m_, n_, mn_, p_, q_, r_, x_],
        optional: [m_, a__, b__, n_, p_, d__, mn_, f__, r_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, n_, p_, q_, r_], x_)
                && eqq!(mn_, -&n_)
                && !integerq!(q_)
        },
        rhs: {
            let frac_q = rubi_frac_part(&q_);
            let recursive_integrand = x_.pow(&m_ - &n_ * &q_)
                * (&a__ + &b__ * x_.pow(&n_)).pow(&p_)
                * (&d__ + &c__ * x_.pow(&n_)).pow(&q_)
                * (&e__ + &f__ * x_.pow(&n_)).pow(&r_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(x_.pow(&n_ * &frac_q)
                    * (&c__ + &d__ * x_.pow(-&n_)).pow(&frac_q)
                    / (&d__ + &c__ * x_.pow(&n_)).pow(frac_q), recursive)
        },
    ));
}

fn push_rules_rule_1072(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        a__, b__, c__, d__, e__, f__, g__, m_, mn_, n_, p_, q_, r_, x_
    );
    rules.push(rubi_rule!(
        order: 1072,
        source: "Int[(g_*x_)^m_*(a_+b_.*x_^n_.)^p_.*(c_+d_.*x_^mn_.)^q_.*(e_+f_.*x_^n_.)^r_.,x_Symbol] :=
          g^IntPart[m]*(g*x)^FracPart[m]/x^FracPart[m] \\[Star] Int[x^m*(a+b*x^n)^p*(c+d*x^(-n))^q*(e+f*x^n)^r,x] /;
        FreeQ[{a,b,c,d,e,f,g,m,n,p,q,r},x] && EqQ[mn,-n]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: (g__ * x_).pow(m_)
            * (a__ + b__ * x_.pow(n_)).pow(p_)
            * (c__ + d__ * x_.pow(mn_)).pow(q_)
            * (e__ + f__ * x_.pow(n_)).pow(r_),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, n_, mn_, p_, q_, r_, x_],
        optional: [b__, n_, p_, d__, mn_, q_, f__, r_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, q_, r_], x_)
                && eqq!(mn_, -&n_)
        },
        rhs: {
            let frac_m = rubi_frac_part(&m_);
            let recursive_integrand = x_.pow(&m_)
                * (&a__ + &b__ * x_.pow(&n_)).pow(&p_)
                * (&c__ + &d__ * x_.pow(-&n_)).pow(&q_)
                * (&e__ + &f__ * x_.pow(&n_)).pow(&r_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(g__.pow(rubi_int_part(&m_)) * (&g__ * x_).pow(&frac_m)
                    / x_.pow(frac_m), recursive)
        },
    ));
}

fn push_rules_rule_1073(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 1073,
        source: "Int[(g_.*x_)^m_.*(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_)^q_.*(e_+f_.*x_^n_)^r_.,x_Symbol] :=
          Unintegrable[(g*x)^m*(a+b*x^n)^p*(c+d*x^n)^q*(e+f*x^n)^r,x] /;
        FreeQ[{a,b,c,d,e,f,g,m,n,p,q,r},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, q_, r_, x_],
        optional: [g__, m_, b__, d__, f__, p_, q_, r_],
        when: { freeq!([a__, b__, c__, d__, e__, f__, g__, m_, n_, p_, q_, r_], x_) },
        rhs: {
            let integrand = (&g__ * x_).pow(&m_)
                * (&a__ + &b__ * x_.pow(&n_)).pow(&p_)
                * (&c__ + &d__ * x_.pow(&n_)).pow(&q_)
                * (&e__ + &f__ * x_.pow(&n_)).pow(&r_);
            rubi_unintegrable(integrand, x_)
        },
    ));
}

fn push_rules_rule_1074(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, f__, m_, n_, p_, q_, r_, u_, v_);
    rules.push(rubi_rule!(
        order: 1074,
        source: "Int[u_^m_.*(a_.+b_.*v_^n_)^p_.*(c_.+d_.*v_^n_)^q_.*(e_+f_.*v_^n_)^r_.,x_Symbol] :=
          u^m/(Coefficient[v,x,1]*v^m) \\[Star] Subst[Int[x^m*(a+b*x^n)^p*(c+d*x^n)^q*(e+f*x^n)^r,x],x,v] /;
        FreeQ[{a,b,c,d,e,f,m,n,p,q,r},x] && LinearPairQ[u,v,x]",
        desc: "Integration by substitution and piecewise constant extraction",
        refs: [],
        pattern: u_.pow(m_)
            * (a__ + b__ * v_.pow(n_)).pow(p_)
            * (c__ + d__ * v_.pow(n_)).pow(q_)
            * (e__ + f__ * v_.pow(n_)).pow(r_),
        with: [u_, a__, b__, c__, d__, e__, f__, v_, m_, n_, p_, q_, r_, x_],
        optional: [m_, a__, b__, p_, c__, d__, q_, f__, r_],
        when: { freeq!([a__, b__, c__, d__, e__, f__, m_, n_, p_, q_, r_], x_) && rubi_linear_pair_q(&u_, &v_, x_) },
        rhs: {
            let v1 = rubi_coefficient(&v_, x_, 1).rubi_rhs();

            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = sub_atom.pow(&m_)
                * (&a__ + &b__ * sub_atom.pow(&n_)).pow(&p_)
                * (&c__ + &d__ * sub_atom.pow(&n_)).pow(&q_)
                * (&e__ + &f__ * sub_atom.pow(&n_)).pow(&r_);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);
            let substituted = rubi_subst(&transformed, sub, &v_);

            rubi_star(u_.pow(&m_) / (&v1 * v_.pow(&m_)), substituted)
        },
    ));
}

fn push_rules_rule_1075(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        a__, b__, c__, d__, e1__, e2__, f1__, f2__, g__, m_, n_, n2_, p_, q_, r_, x_
    );
    rules.push(rubi_rule!(
        order: 1075,
        source: "Int[(g_.*x_)^m_.*(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_)^q_.*(e1_+f1_.*x_^n2_.)^r_.*(e2_+f2_.*x_^n2_.)^r_.,x_Symbol] :=
          Int[(g*x)^m*(a+b*x^n)^p*(c+d*x^n)^q*(e1*e2+f1*f2*x^n)^r,x] /;
        FreeQ[{a,b,c,d,e1,f1,e2,f2,g,m,n,p,q,r},x] && EqQ[n2,n/2] && EqQ[e2*f1+e1*f2,0] && (IntegerQ[r] || GtQ[e1,0] && GtQ[e2,0])",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, e1__, f1__, e2__, f2__, g__, m_, n_, n2_, p_, q_, r_, x_],
        optional: [g__, m_, b__, d__, f1__, f2__, n2_, p_, q_, r_],
        when: {
            freeq!([a__, b__, c__, d__, e1__, f1__, e2__, f2__, g__, m_, n_, p_, q_, r_], x_)
                && eqq!(n2_, &n_ / Atom::num(2))
                && eqq!(&e2__ * &f1__ + &e1__ * &f2__, 0)
                && (integerq!(r_) || gtq!(e1__, 0) && gtq!(e2__, 0))
        },
        rhs: {
            let recursive_integrand = (&g__ * x_).pow(&m_)
                * (&a__ + &b__ * x_.pow(&n_)).pow(&p_)
                * (&c__ + &d__ * x_.pow(&n_)).pow(&q_)
                * (&e1__ * &e2__ + &f1__ * &f2__ * x_.pow(&n_)).pow(&r_);
            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_1076(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        a__, b__, c__, d__, e1__, e2__, f1__, f2__, g__, m_, n_, n2_, p_, q_, r_, x_
    );
    rules.push(rubi_rule!(
        order: 1076,
        source: "Int[(g_.*x_)^m_.*(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_)^q_.*(e1_+f1_.*x_^n2_.)^r_.*(e2_+f2_.*x_^n2_.)^r_.,x_Symbol] :=
          (e1+f1*x^(n/2))^FracPart[r]*(e2+f2*x^(n/2))^FracPart[r]/(e1*e2+f1*f2*x^n)^FracPart[r] \\[Star]
            Int[(g*x)^m*(a+b*x^n)^p*(c+d*x^n)^q*(e1*e2+f1*f2*x^n)^r,x] /;
        FreeQ[{a,b,c,d,e1,f1,e2,f2,g,m,n,p,q,r},x] && EqQ[n2,n/2] && EqQ[e2*f1+e1*f2,0]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, e1__, f1__, e2__, f2__, g__, m_, n_, n2_, p_, q_, r_, x_],
        optional: [g__, m_, b__, d__, f1__, f2__, n2_, p_, q_, r_],
        when: {
            freeq!([a__, b__, c__, d__, e1__, f1__, e2__, f2__, g__, m_, n_, p_, q_, r_], x_)
                && eqq!(n2_, &n_ / Atom::num(2))
                && eqq!(&e2__ * &f1__ + &e1__ * &f2__, 0)
        },
        rhs: {
            let frac_r = rubi_frac_part(&r_);
            let recursive_integrand = (&g__ * x_).pow(&m_)
                * (&a__ + &b__ * x_.pow(&n_)).pow(&p_)
                * (&c__ + &d__ * x_.pow(&n_)).pow(&q_)
                * (&e1__ * &e2__ + &f1__ * &f2__ * x_.pow(&n_)).pow(&r_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star((&e1__ + &f1__ * x_.pow(&n_ / Atom::num(2))).pow(&frac_r)
                    * (&e2__ + &f2__ * x_.pow(&n_ / Atom::num(2))).pow(&frac_r)
                    / (&e1__ * &e2__ + &f1__ * &f2__ * x_.pow(&n_)).pow(frac_r), recursive)
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
    let e1__ = symbols.e1__;
    let e2__ = symbols.e2__;
    let f1__ = symbols.f1__;
    let f2__ = symbols.f2__;
    let g__ = symbols.g__;
    let m_ = symbols.m_;
    let n2_ = symbols.n2_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let q_ = symbols.q_;
    let r_ = symbols.r_;
    let x_ = symbols.x_;
    (g__ * x_).pow(m_)
        * (a__ + b__ * x_.pow(n_)).pow(p_)
        * (c__ + d__ * x_.pow(n_)).pow(q_)
        * (e1__ + f1__ * x_.pow(n2_)).pow(r_)
        * (e2__ + f2__ * x_.pow(n2_)).pow(r_)
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
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let q_ = symbols.q_;
    let x_ = symbols.x_;
    (g__ * x_).pow(m_)
        * (a__ + b__ * x_.pow(n_)).pow(p_)
        * (c__ + d__ * x_.pow(n_)).pow(q_)
        * (e__ + f__ * x_.pow(n_))
}

#[inline(never)]
fn rubi_shared_pattern_2(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let g__ = symbols.g__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let q_ = symbols.q_;
    let r_ = symbols.r_;
    let x_ = symbols.x_;
    (g__ * x_).pow(m_)
        * (a__ + b__ * x_.pow(n_)).pow(p_)
        * (c__ + d__ * x_.pow(n_)).pow(q_)
        * (e__ + f__ * x_.pow(n_)).pow(r_)
}

#[inline(never)]
fn rubi_shared_pattern_3(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let g__ = symbols.g__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (g__ * x_).pow(m_) * (a__ + b__ * x_.pow(n_)).pow(p_) * (e__ + f__ * x_.pow(n_))
        / (c__ + d__ * x_.pow(n_))
}

#[inline(never)]
fn rubi_shared_pattern_4(symbols: &RubiSymbols) -> Atom {
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let g__ = symbols.g__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let q_ = symbols.q_;
    let r_ = symbols.r_;
    let x_ = symbols.x_;
    (g__ * x_).pow(m_)
        * (b__ * x_.pow(n_)).pow(p_)
        * (c__ + d__ * x_.pow(n_)).pow(q_)
        * (e__ + f__ * x_.pow(n_)).pow(r_)
}

#[inline(never)]
fn rubi_shared_pattern_5(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let mn_ = symbols.mn_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let q_ = symbols.q_;
    let r_ = symbols.r_;
    let x_ = symbols.x_;
    x_.pow(m_)
        * (a__ + b__ * x_.pow(n_)).pow(p_)
        * (c__ + d__ * x_.pow(mn_)).pow(q_)
        * (e__ + f__ * x_.pow(n_)).pow(r_)
}

#[inline(never)]
fn rubi_shared_pattern_6(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let q_ = symbols.q_;
    let r_ = symbols.r_;
    let x_ = symbols.x_;
    x_.pow(m_)
        * (a__ + b__ * x_.pow(n_)).pow(p_)
        * (c__ + d__ * x_.pow(n_)).pow(q_)
        * (e__ + f__ * x_.pow(n_)).pow(r_)
}
