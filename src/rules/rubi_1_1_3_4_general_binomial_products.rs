use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_943(rules);
    push_rules_rule_944(rules);
    push_rules_rule_945(rules);
    push_rules_rule_946(rules);
    push_rules_rule_947(rules);
    push_rules_rule_948(rules);
    push_rules_rule_949(rules);
    push_rules_rule_950(rules);
    push_rules_rule_951(rules);
    push_rules_rule_952(rules);
    push_rules_rule_953(rules);
    push_rules_rule_954(rules);
    push_rules_rule_955(rules);
    push_rules_rule_956(rules);
    push_rules_rule_957(rules);
    push_rules_rule_958(rules);
    push_rules_rule_959(rules);
    push_rules_rule_960(rules);
    push_rules_rule_961(rules);
    push_rules_rule_962(rules);
    push_rules_rule_963(rules);
    push_rules_rule_964(rules);
    push_rules_rule_965(rules);
    push_rules_rule_966(rules);
    push_rules_rule_967(rules);
    push_rules_rule_968(rules);
    push_rules_rule_969(rules);
    push_rules_rule_970(rules);
    push_rules_rule_971(rules);
    push_rules_rule_972(rules);
    push_rules_rule_973(rules);
    push_rules_rule_974(rules);
    push_rules_rule_975(rules);
    push_rules_rule_976(rules);
    push_rules_rule_977(rules);
    push_rules_rule_978(rules);
    push_rules_rule_979(rules);
    push_rules_rule_980(rules);
    push_rules_rule_981(rules);
    push_rules_rule_982(rules);
    push_rules_rule_983(rules);
    push_rules_rule_984(rules);
    push_rules_rule_985(rules);
    push_rules_rule_986(rules);
    push_rules_rule_987(rules);
    push_rules_rule_988(rules);
    push_rules_rule_989(rules);
    push_rules_rule_990(rules);
    push_rules_rule_991(rules);
    push_rules_rule_992(rules);
    push_rules_rule_993(rules);
    push_rules_rule_994(rules);
    push_rules_rule_995(rules);
    push_rules_rule_996(rules);
    push_rules_rule_997(rules);
    push_rules_rule_998(rules);
    push_rules_rule_999(rules);
    push_rules_rule_1000(rules);
    push_rules_rule_1001(rules);
    push_rules_rule_1002(rules);
    push_rules_rule_1003(rules);
    push_rules_rule_1004(rules);
    push_rules_rule_1005(rules);
    push_rules_rule_1006(rules);
    push_rules_rule_1007(rules);
    push_rules_rule_1008(rules);
    push_rules_rule_1009(rules);
    push_rules_rule_1010(rules);
    push_rules_rule_1011(rules);
    push_rules_rule_1012(rules);
    push_rules_rule_1013(rules);
    push_rules_rule_1015(rules);
    push_rules_rule_1014(rules);
    push_rules_rule_1016(rules);
    push_rules_rule_1017(rules);
    push_rules_rule_1018(rules);
    push_rules_rule_2036(rules);
    push_rules_rule_2037(rules);
    push_rules_rule_2038(rules);
    push_rules_rule_2039(rules);
}

fn push_rules_rule_943(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; b__, c__, d__, e__, m_, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 943,
        source: "Int[(e_.*x_)^m_.*(b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_.,x_Symbol] :=
          e^m/(n*b^(Simplify[(m+1)/n]-1)) \\[Star] Subst[Int[(b*x)^(p+Simplify[(m+1)/n]-1)*(c+d*x)^q,x],x,x^n] /;
        FreeQ[{b,c,d,e,m,n,p,q},x] && (IntegerQ[m] || GtQ[e,0]) && IntegerQ[Simplify[(m+1)/n]]",
        desc: "Algebraic expansion and integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [b__, c__, d__, e__, m_, n_, p_, q_, x_],
        optional: [b__, d__, e__, m_, q_],
        when: {
            let k = rubi_simplify(&((&m_ + Atom::num(1)) / &n_));
            freeq!([b__, c__, d__, e__, m_, n_, p_, q_], x_)
                && (integerq!(m_) || gtq!(e__, 0))
                && integerq!(&k)
        },
        rhs: {
            let k = rubi_simplify(&((&m_ + Atom::num(1)) / &n_));
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand =
                (&b__ * &sub_atom).pow(&p_ + &k - Atom::num(1)) * (&c__ + &d__ * &sub_atom).pow(&q_);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);
            let substituted = rubi_subst(&transformed, sub, x_.pow(&n_));

            rubi_star(e__.pow(&m_), substituted / (&n_ * b__.pow(&k - Atom::num(1))))
        },
    ));
}

fn push_rules_rule_944(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; b__, c__, d__, e__, m_, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 944,
        source: "Int[(e_.*x_)^m_.*(b_.*x_^n_.)^p_*(c_+d_.*x_^n_)^q_.,x_Symbol] :=
          e^m*b^IntPart[p]*(b*x^n)^FracPart[p]/x^(n*FracPart[p]) \\[Star] Int[x^(m+n*p)*(c+d*x^n)^q,x] /;
        FreeQ[{b,c,d,e,m,n,p,q},x] && (IntegerQ[m] || GtQ[e,0]) && Not[IntegerQ[Simplify[(m+1)/n]]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [b__, c__, d__, e__, m_, n_, p_, q_, x_],
        optional: [b__, d__, e__, m_, n_, q_],
        when: {
            let k = rubi_simplify(&((&m_ + Atom::num(1)) / &n_));
            freeq!([b__, c__, d__, e__, m_, n_, p_, q_], x_)
                && (integerq!(m_) || gtq!(e__, 0))
                && !integerq!(&k)
        },
        rhs: {
            let frac_p = rubi_frac_part(&p_);
            let recursive_integrand =
                x_.pow(&m_ + &n_ * &p_) * (&c__ + &d__ * x_.pow(&n_)).pow(&q_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(e__.pow(&m_) * b__.pow(rubi_int_part(&p_)) * (&b__ * x_.pow(&n_)).pow(&frac_p) / x_.pow(&n_ * frac_p), recursive)
        },
    ));
}

fn push_rules_rule_945(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; b__, c__, d__, e__, m_, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 945,
        source: "Int[(e_*x_)^m_*(b_.*x_^n_.)^p_*(c_+d_.*x_^n_)^q_.,x_Symbol] :=
          e^IntPart[m]*(e*x)^FracPart[m]/x^FracPart[m] \\[Star] Int[x^m*(b*x^n)^p*(c+d*x^n)^q,x] /;
        FreeQ[{b,c,d,e,m,n,p,q},x] && Not[IntegerQ[m]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [b__, c__, d__, e__, m_, n_, p_, q_, x_],
        optional: [b__, d__, n_, q_],
        when: { freeq!([b__, c__, d__, e__, m_, n_, p_, q_], x_) && !integerq!(m_) },
        rhs: {
            let frac_m = rubi_frac_part(&m_);
            let recursive_integrand = x_.pow(&m_)
                * (&b__ * x_.pow(&n_)).pow(&p_)
                * (&c__ + &d__ * x_.pow(&n_)).pow(&q_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(e__.pow(rubi_int_part(&m_)) * (&e__ * x_).pow(&frac_m) / x_.pow(frac_m), recursive)
        },
    ));
}

fn push_rules_rule_946(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, q_, x_);
    let rule = rubi_rule!(
        order: 946,
        source: "Int[x_^m_.*(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_)^q_.,x_Symbol] :=
          1/n \\[Star] Subst[Int[(a+b*x)^p*(c+d*x)^q,x],x,x^n] /;
        FreeQ[{a,b,c,d,m,n,p,q},x] && NeQ[b*c-a*d,0] && EqQ[m-n+1,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [a__, b__, c__, d__, m_, n_, p_, q_, x_],
        optional: [b__, d__, m_, p_, q_],
        when: {
            freeq!([a__, b__, c__, d__, m_, n_, p_, q_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(&m_ - &n_ + Atom::num(1), 0)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand =
                (&a__ + &b__ * &sub_atom).pow(&p_) * (&c__ + &d__ * &sub_atom).pow(&q_);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);
            let substituted = rubi_subst(&transformed, sub, x_.pow(&n_));
            rubi_star(Atom::num(1) / &n_, substituted)
        },
    );
    rules.push(rule.with_explicit_variable_power_factor());
}

fn push_rules_rule_947(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, q_, x_);
    let rule = rubi_rule!(
        order: 947,
        source: "Int[x_^m_.*(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_)^q_.,x_Symbol] :=
          Int[x^(m+n*(p+q))*(b+a*x^(-n))^p*(d+c*x^(-n))^q,x] /;
        FreeQ[{a,b,c,d,m,n},x] && NeQ[b*c-a*d,0] && IntegersQ[p,q] && NegQ[n]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [a__, b__, c__, d__, m_, n_, p_, q_, x_],
        optional: [b__, d__, m_, p_, q_],
        when: {
            freeq!([a__, b__, c__, d__, m_, n_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && integersq!([p_, q_])
                && negq!(n_)
        },
        rhs: {
            let transformed_integrand = x_.pow(&m_ + &n_ * (&p_ + &q_))
                * (&b__ + &a__ * x_.pow(-&n_)).pow(&p_)
                * (&d__ + &c__ * x_.pow(-&n_)).pow(&q_);
            rubi_rhs_int(&transformed_integrand, x_)
        },
    );
    rules.push(rule.with_explicit_variable_power_factor());
}

fn push_rules_rule_948(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, q_, x_);
    let rule = rubi_rule!(
        order: 948,
        source: "Int[x_^m_.*(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_)^q_.,x_Symbol] :=
          1/n \\[Star] Subst[Int[x^(Simplify[(m+1)/n]-1)*(a+b*x)^p*(c+d*x)^q,x],x,x^n] /;
        FreeQ[{a,b,c,d,m,n,p,q},x] && NeQ[b*c-a*d,0] && IntegerQ[Simplify[(m+1)/n]]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [a__, b__, c__, d__, m_, n_, p_, q_, x_],
        optional: [b__, d__, m_, p_, q_],
        when: {
            let k = rubi_simplify(&((&m_ + Atom::num(1)) / &n_));
            freeq!([a__, b__, c__, d__, m_, n_, p_, q_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && integerq!(&k)
        },
        rhs: {
            let k = rubi_simplify(&((&m_ + Atom::num(1)) / &n_));
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = sub_atom.pow(&k - Atom::num(1))
                * (&a__ + &b__ * &sub_atom).pow(&p_)
                * (&c__ + &d__ * &sub_atom).pow(&q_);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);
            let substituted = rubi_subst(&transformed, sub, x_.pow(&n_));
            rubi_star(Atom::num(1) / &n_, substituted)
        },
    );
    rules.push(rule.with_explicit_variable_power_factor());
}

fn push_rules_rule_949(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 949,
        source: "Int[(e_*x_)^m_.*(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_)^q_.,x_Symbol] :=
          e^IntPart[m]*(e*x)^FracPart[m]/x^FracPart[m] \\[Star] Int[x^m*(a+b*x^n)^p*(c+d*x^n)^q,x] /;
        FreeQ[{a,b,c,d,e,m,n,p,q},x] && NeQ[b*c-a*d,0] && IntegerQ[Simplify[(m+1)/n]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, p_, q_, x_],
        optional: [b__, d__, m_, p_, q_],
        when: {
            let k = rubi_simplify(&((&m_ + Atom::num(1)) / &n_));
            freeq!([a__, b__, c__, d__, e__, m_, n_, p_, q_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && integerq!(&k)
        },
        rhs: {
            let frac_m = rubi_frac_part(&m_);
            let recursive_integrand = x_.pow(&m_)
                * (&a__ + &b__ * x_.pow(&n_)).pow(&p_)
                * (&c__ + &d__ * x_.pow(&n_)).pow(&q_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(e__.pow(rubi_int_part(&m_)) * (&e__ * x_).pow(&frac_m) / x_.pow(frac_m), recursive)
        },
    ));
}

fn push_rules_rule_950(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 950,
        source: "Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_)^q_.,x_Symbol] :=
          Int[ExpandIntegrand[(e*x)^m*(a+b*x^n)^p*(c+d*x^n)^q,x],x] /;
        FreeQ[{a,b,c,d,e,m,n},x] && NeQ[b*c-a*d,0] && IGtQ[p,0] && IGtQ[q,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, p_, q_, x_],
        optional: [b__, d__, e__, m_, p_, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && igtq!(p_, 0)
                && igtq!(q_, 0)
        },
        rhs: {
            let integrand = (&e__ * x_).pow(&m_)
                * (&a__ + &b__ * x_.pow(&n_)).pow(&p_)
                * (&c__ + &d__ * x_.pow(&n_)).pow(&q_);
            let expanded = rubi_expand_integrand(&integrand, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_951(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 951,
        source: "Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_),x_Symbol] :=
          c*(e*x)^(m+1)*(a+b*x^n)^(p+1)/(a*e*(m+1)) /;
        FreeQ[{a,b,c,d,e,m,n,p},x] && NeQ[b*c-a*d,0] && EqQ[a*d*(m+1)-b*c*(m+n*(p+1)+1),0] && NeQ[m,-1]",
        desc: "Trinomial recurrence 2b with c=0 and a d (m+1)-b c (m+n (p+1)+1)\\[Equal]0",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, p_, x_],
        optional: [b__, d__, e__, m_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_, p_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(
                    &a__ * &d__ * (&m_ + Atom::num(1))
                        - &b__ * &c__ * (&m_ + &n_ * (&p_ + Atom::num(1)) + Atom::num(1)),
                    0
                )
                && neq!(m_, -1)
        },
        rhs: {
            rubi_simp(
                &(&c__ * (&e__ * x_).pow(&m_ + Atom::num(1))
                    * (&a__ + &b__ * x_.pow(&n_)).pow(&p_ + Atom::num(1))
                    / (&a__ * &e__ * (&m_ + Atom::num(1)))),
                x_,
            )
        },
    ));
}

fn push_rules_rule_952(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a1__, a2__, b1__, b2__, c__, d__, e__, m_, n_, non2_, p_, x_);
    rules.push(rubi_rule!(
        order: 952,
        source: "Int[(e_.*x_)^m_.*(a1_+b1_.*x_^non2_.)^p_.*(a2_+b2_.*x_^non2_.)^p_.*(c_+d_.*x_^n_),x_Symbol] :=
          c*(e*x)^(m+1)*(a1+b1*x^(n/2))^(p+1)*(a2+b2*x^(n/2))^(p+1)/(a1*a2*e*(m+1)) /;
        FreeQ[{a1,b1,a2,b2,c,d,e,m,n,p},x] && EqQ[non2,n/2] && EqQ[a2*b1+a1*b2,0] && EqQ[a1*a2*d*(m+1)-b1*b2*c*(m+n*(p+1)+1),0] && NeQ[m,-1]",
        desc: "Trinomial recurrence 2b with c=0 and a d (m+1)-b c (m+n (p+1)+1)\\[Equal]0",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a1__, b1__, a2__, b2__, c__, d__, e__, m_, n_, non2_, p_, x_],
        optional: [b1__, b2__, d__, e__, m_, non2_, p_],
        when: {
            freeq!([a1__, b1__, a2__, b2__, c__, d__, e__, m_, n_, p_], x_)
                && eqq!(non2_, &n_ / Atom::num(2))
                && eqq!(&a2__ * &b1__ + &a1__ * &b2__, 0)
                && eqq!(
                    &a1__ * &a2__ * &d__ * (&m_ + Atom::num(1))
                        - &b1__ * &b2__ * &c__ * (&m_ + &n_ * (&p_ + Atom::num(1)) + Atom::num(1)),
                    0
                )
                && neq!(m_, -1)
        },
        rhs: {
            rubi_simp(
                &(&c__ * (&e__ * x_).pow(&m_ + Atom::num(1))
                    * (&a1__ + &b1__ * x_.pow(&n_ / Atom::num(2))).pow(&p_ + Atom::num(1))
                    * (&a2__ + &b2__ * x_.pow(&n_ / Atom::num(2))).pow(&p_ + Atom::num(1))
                    / (&a1__ * &a2__ * &e__ * (&m_ + Atom::num(1)))),
                x_,
            )
        },
    ));
}

fn push_rules_rule_953(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 953,
        source: "Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_),x_Symbol] :=
          c*(e*x)^(m+1)*(a+b*x^n)^(p+1)/(a*e*(m+1)) + d/e^n \\[Star] Int[(e*x)^(m+n)*(a+b*x^n)^p,x] /;
        FreeQ[{a,b,c,d,e,m,n,p},x] && NeQ[b*c-a*d,0] && EqQ[m+n*(p+1)+1,0] && (IntegerQ[n] || GtQ[e,0]) &&
          (GtQ[n,0] && LtQ[m,-1] || LtQ[n,0] && GtQ[m+n,-1])",
        desc: "Trinomial recurrence 3b with c=0",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, p_, x_],
        optional: [b__, d__, e__, m_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_, p_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(&m_ + &n_ * (&p_ + Atom::num(1)) + Atom::num(1), 0)
                && (integerq!(n_) || gtq!(e__, 0))
                && (gtq!(n_, 0) && ltq!(m_, -1) || ltq!(n_, 0) && gtq!(&m_ + &n_, -1))
        },
        rhs: {
            let first = &c__ * (&e__ * x_).pow(&m_ + Atom::num(1))
                * (&a__ + &b__ * x_.pow(&n_)).pow(&p_ + Atom::num(1))
                / (&a__ * &e__ * (&m_ + Atom::num(1)));
            let recursive_integrand =
                (&e__ * x_).pow(&m_ + &n_) * (&a__ + &b__ * x_.pow(&n_)).pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            rubi_simp(&first, x_)
                    + rubi_star(d__, recursive / e__.pow(&n_))
        },
    ));
}

fn push_rules_rule_954(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 954,
        source: "Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_),x_Symbol] :=
          (b*c-a*d)*(e*x)^(m+1)*(a+b*x^n)^(p+1)/(a*b*e*(m+1)) + d/b \\[Star] Int[(e*x)^m*(a+b*x^n)^(p+1),x] /;
        FreeQ[{a,b,c,d,e,m,n,p},x] && NeQ[b*c-a*d,0] && EqQ[m+n*(p+1)+1,0] && NeQ[m,-1]",
        desc: "Trinomial recurrence 2b with c=0",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, p_, x_],
        optional: [b__, d__, e__, m_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_, p_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(&m_ + &n_ * (&p_ + Atom::num(1)) + Atom::num(1), 0)
                && neq!(m_, -1)
        },
        rhs: {
            let first = (&b__ * &c__ - &a__ * &d__)
                * (&e__ * x_).pow(&m_ + Atom::num(1))
                * (&a__ + &b__ * x_.pow(&n_)).pow(&p_ + Atom::num(1))
                / (&a__ * &b__ * &e__ * (&m_ + Atom::num(1)));
            let recursive_integrand =
                (&e__ * x_).pow(&m_) * (&a__ + &b__ * x_.pow(&n_)).pow(&p_ + Atom::num(1));
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            rubi_simp(&first, x_) + rubi_star(d__, recursive / &b__)
        },
    ));
}

fn push_rules_rule_955(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 955,
        source: "Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_),x_Symbol] :=
          c*(e*x)^(m+1)*(a+b*x^n)^(p+1)/(a*e*(m+1)) +
          (a*d*(m+1)-b*c*(m+n*(p+1)+1))/(a*e^n*(m+1)) \\[Star] Int[(e*x)^(m+n)*(a+b*x^n)^p,x] /;
        FreeQ[{a,b,c,d,e,p},x] && NeQ[b*c-a*d,0] && (IntegerQ[n] || GtQ[e,0]) &&
          (GtQ[n,0] && LtQ[m,-1] || LtQ[n,0] && GtQ[m+n,-1]) && Not[ILtQ[p,-1]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, p_, x_],
        optional: [b__, d__, e__, m_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, p_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && (integerq!(n_) || gtq!(e__, 0))
                && (gtq!(n_, 0) && ltq!(m_, -1) || ltq!(n_, 0) && gtq!(&m_ + &n_, -1))
                && !iltq!(p_, -1)
        },
        rhs: {
            let first = &c__ * (&e__ * x_).pow(&m_ + Atom::num(1))
                * (&a__ + &b__ * x_.pow(&n_)).pow(&p_ + Atom::num(1))
                / (&a__ * &e__ * (&m_ + Atom::num(1)));
            let coefficient = (&a__ * &d__ * (&m_ + Atom::num(1))
                - &b__ * &c__ * (&m_ + &n_ * (&p_ + Atom::num(1)) + Atom::num(1)))
                / (&a__ * e__.pow(&n_) * (&m_ + Atom::num(1)));
            let recursive_integrand =
                (&e__ * x_).pow(&m_ + &n_) * (&a__ + &b__ * x_.pow(&n_)).pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            rubi_simp(&first, x_) + rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_956(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a1__, a2__, b1__, b2__, c__, d__, e__, m_, n_, non2_, p_, x_);
    rules.push(rubi_rule!(
        order: 956,
        source: "Int[(e_.*x_)^m_.*(a1_+b1_.*x_^non2_.)^p_.*(a2_+b2_.*x_^non2_.)^p_.*(c_+d_.*x_^n_),x_Symbol] :=
          c*(e*x)^(m+1)*(a1+b1*x^(n/2))^(p+1)*(a2+b2*x^(n/2))^(p+1)/(a1*a2*e*(m+1)) +
          (a1*a2*d*(m+1)-b1*b2*c*(m+n*(p+1)+1))/(a1*a2*e^n*(m+1)) \\[Star] Int[(e*x)^(m+n)*(a1+b1*x^(n/2))^p*(a2+b2*x^(n/2))^p,x] /;
        FreeQ[{a1,b1,a2,b2,c,d,e,p},x] && EqQ[non2,n/2] && EqQ[a2*b1+a1*b2,0] && (IntegerQ[n] || GtQ[e,0]) &&
          (GtQ[n,0] && LtQ[m,-1] || LtQ[n,0] && GtQ[m+n,-1]) && Not[ILtQ[p,-1]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a1__, b1__, a2__, b2__, c__, d__, e__, m_, n_, non2_, p_, x_],
        optional: [b1__, b2__, d__, e__, m_, non2_, p_],
        when: {
            freeq!([a1__, b1__, a2__, b2__, c__, d__, e__, p_], x_)
                && eqq!(non2_, &n_ / Atom::num(2))
                && eqq!(&a2__ * &b1__ + &a1__ * &b2__, 0)
                && (integerq!(n_) || gtq!(e__, 0))
                && (gtq!(n_, 0) && ltq!(m_, -1) || ltq!(n_, 0) && gtq!(&m_ + &n_, -1))
                && !iltq!(p_, -1)
        },
        rhs: {
            let first_base = &a1__ + &b1__ * x_.pow(&n_ / Atom::num(2));
            let second_base = &a2__ + &b2__ * x_.pow(&n_ / Atom::num(2));
            let first = &c__ * (&e__ * x_).pow(&m_ + Atom::num(1))
                * first_base.pow(&p_ + Atom::num(1))
                * second_base.pow(&p_ + Atom::num(1))
                / (&a1__ * &a2__ * &e__ * (&m_ + Atom::num(1)));
            let coefficient = (&a1__ * &a2__ * &d__ * (&m_ + Atom::num(1))
                - &b1__ * &b2__ * &c__ * (&m_ + &n_ * (&p_ + Atom::num(1)) + Atom::num(1)))
                / (&a1__ * &a2__ * e__.pow(&n_) * (&m_ + Atom::num(1)));
            let recursive_integrand =
                (&e__ * x_).pow(&m_ + &n_) * first_base.pow(&p_) * second_base.pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            rubi_simp(&first, x_) + rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_957(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 957,
        source: "Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_),x_Symbol] :=
          -(b*c-a*d)*(e*x)^(m+1)*(a+b*x^n)^(p+1)/(a*b*e*n*(p+1)) -
          (a*d*(m+1)-b*c*(m+n*(p+1)+1))/(a*b*n*(p+1)) \\[Star] Int[(e*x)^m*(a+b*x^n)^(p+1),x] /;
        FreeQ[{a,b,c,d,e,m,n},x] && NeQ[b*c-a*d,0] && LtQ[p,-1] &&
          (Not[IntegerQ[p+1/2]] && NeQ[p,-5/4] || Not[RationalQ[m]] || IGtQ[n,0] && ILtQ[p+1/2,0] && LeQ[-1,m,-n*(p+1)])",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, p_, x_],
        optional: [b__, d__, e__, m_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && ltq!(p_, -1)
                && ((!integerq!(&p_ + Atom::num(1) / Atom::num(2)) && neq!(p_, -Atom::num(5) / Atom::num(4)))
                    || !rationalq!(m_)
                    || igtq!(n_, 0)
                        && iltq!(&p_ + Atom::num(1) / Atom::num(2), 0)
                        && leq!(Atom::num(-1), m_, -&n_ * (&p_ + Atom::num(1))))
        },
        rhs: {
            let det = &b__ * &c__ - &a__ * &d__;
            let base = &a__ + &b__ * x_.pow(&n_);
            let direct = -&det * (&e__ * x_).pow(&m_ + Atom::num(1)) * base.pow(&p_ + Atom::num(1))
                / (&a__ * &b__ * &e__ * &n_ * (&p_ + Atom::num(1)));
            let coefficient = (&a__ * &d__ * (&m_ + Atom::num(1))
                - &b__ * &c__ * (&m_ + &n_ * (&p_ + Atom::num(1)) + Atom::num(1)))
                / (&a__ * &b__ * &n_ * (&p_ + Atom::num(1)));
            let recursive_integrand = (&e__ * x_).pow(&m_) * base.pow(&p_ + Atom::num(1));
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            rubi_simp(&direct, x_) - rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_958(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a1__, a2__, b1__, b2__, c__, d__, e__, m_, n_, non2_, p_, x_);
    rules.push(rubi_rule!(
        order: 958,
        source: "Int[(e_.*x_)^m_.*(a1_+b1_.*x_^non2_.)^p_.*(a2_+b2_.*x_^non2_.)^p_.*(c_+d_.*x_^n_),x_Symbol] :=
          -(b1*b2*c-a1*a2*d)*(e*x)^(m+1)*(a1+b1*x^(n/2))^(p+1)*(a2+b2*x^(n/2))^(p+1)/(a1*a2*b1*b2*e*n*(p+1)) -
          (a1*a2*d*(m+1)-b1*b2*c*(m+n*(p+1)+1))/(a1*a2*b1*b2*n*(p+1)) \\[Star] Int[(e*x)^m*(a1+b1*x^(n/2))^(p+1)*(a2+b2*x^(n/2))^(p+1),x] /;
        FreeQ[{a1,b1,a2,b2,c,d,e,m,n},x] && EqQ[non2,n/2] && EqQ[a2*b1+a1*b2,0] && LtQ[p,-1] &&
          (Not[IntegerQ[p+1/2]] && NeQ[p,-5/4] || Not[RationalQ[m]] || IGtQ[n,0] && ILtQ[p+1/2,0] && LeQ[-1,m,-n*(p+1)])",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a1__, b1__, a2__, b2__, c__, d__, e__, m_, n_, non2_, p_, x_],
        optional: [b1__, b2__, d__, e__, m_, non2_, p_],
        when: {
            freeq!([a1__, b1__, a2__, b2__, c__, d__, e__, m_, n_], x_)
                && eqq!(non2_, &n_ / Atom::num(2))
                && eqq!(&a2__ * &b1__ + &a1__ * &b2__, 0)
                && ltq!(p_, -1)
                && ((!integerq!(&p_ + Atom::num(1) / Atom::num(2)) && neq!(p_, -Atom::num(5) / Atom::num(4)))
                    || !rationalq!(m_)
                    || igtq!(n_, 0)
                        && iltq!(&p_ + Atom::num(1) / Atom::num(2), 0)
                        && leq!(Atom::num(-1), m_, -&n_ * (&p_ + Atom::num(1))))
        },
        rhs: {
            let first_base = &a1__ + &b1__ * x_.pow(&n_ / Atom::num(2));
            let second_base = &a2__ + &b2__ * x_.pow(&n_ / Atom::num(2));
            let det = &b1__ * &b2__ * &c__ - &a1__ * &a2__ * &d__;
            let direct = -&det * (&e__ * x_).pow(&m_ + Atom::num(1))
                * first_base.pow(&p_ + Atom::num(1))
                * second_base.pow(&p_ + Atom::num(1))
                / (&a1__ * &a2__ * &b1__ * &b2__ * &e__ * &n_ * (&p_ + Atom::num(1)));
            let coefficient = (&a1__ * &a2__ * &d__ * (&m_ + Atom::num(1))
                - &b1__ * &b2__ * &c__ * (&m_ + &n_ * (&p_ + Atom::num(1)) + Atom::num(1)))
                / (&a1__ * &a2__ * &b1__ * &b2__ * &n_ * (&p_ + Atom::num(1)));
            let recursive_integrand = (&e__ * x_).pow(&m_)
                * first_base.pow(&p_ + Atom::num(1))
                * second_base.pow(&p_ + Atom::num(1));
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            rubi_simp(&direct, x_) - rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_959(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 959,
        source: "Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_),x_Symbol] :=
          d*(e*x)^(m+1)*(a+b*x^n)^(p+1)/(b*e*(m+n*(p+1)+1)) -
          (a*d*(m+1)-b*c*(m+n*(p+1)+1))/(b*(m+n*(p+1)+1)) \\[Star] Int[(e*x)^m*(a+b*x^n)^p,x] /;
        FreeQ[{a,b,c,d,e,m,n,p},x] && NeQ[b*c-a*d,0] && NeQ[m+n*(p+1)+1,0]",
        desc: "Trinomial recurrence 2b with c=0 composed with binomial recurrence 1b",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, p_, x_],
        optional: [b__, d__, e__, m_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_, p_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && neq!(&m_ + &n_ * (&p_ + Atom::num(1)) + Atom::num(1), 0)
        },
        rhs: {
            let denominator = &m_ + &n_ * (&p_ + Atom::num(1)) + Atom::num(1);
            let base = &a__ + &b__ * x_.pow(&n_);
            let direct = &d__ * (&e__ * x_).pow(&m_ + Atom::num(1)) * base.pow(&p_ + Atom::num(1))
                / (&b__ * &e__ * &denominator);
            let coefficient = (&a__ * &d__ * (&m_ + Atom::num(1))
                - &b__ * &c__ * &denominator)
                / (&b__ * &denominator);
            let recursive_integrand = (&e__ * x_).pow(&m_) * base.pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            rubi_simp(&direct, x_) - rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_960(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a1__, a2__, b1__, b2__, c__, d__, e__, m_, n_, non2_, p_, x_);
    rules.push(rubi_rule!(
        order: 960,
        source: "Int[(e_.*x_)^m_.*(a1_+b1_.*x_^non2_.)^p_.*(a2_+b2_.*x_^non2_.)^p_.*(c_+d_.*x_^n_),x_Symbol] :=
          d*(e*x)^(m+1)*(a1+b1*x^(n/2))^(p+1)*(a2+b2*x^(n/2))^(p+1)/(b1*b2*e*(m+n*(p+1)+1)) -
          (a1*a2*d*(m+1)-b1*b2*c*(m+n*(p+1)+1))/(b1*b2*(m+n*(p+1)+1)) \\[Star] Int[(e*x)^m*(a1+b1*x^(n/2))^p*(a2+b2*x^(n/2))^p,x] /;
        FreeQ[{a1,b1,a2,b2,c,d,e,m,n,p},x] && EqQ[non2,n/2] && EqQ[a2*b1+a1*b2,0] && NeQ[m+n*(p+1)+1,0]",
        desc: "Trinomial recurrence 2b with c=0 composed with binomial recurrence 1b",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a1__, b1__, a2__, b2__, c__, d__, e__, m_, n_, non2_, p_, x_],
        optional: [b1__, b2__, d__, e__, m_, non2_, p_],
        when: {
            freeq!([a1__, b1__, a2__, b2__, c__, d__, e__, m_, n_, p_], x_)
                && eqq!(non2_, &n_ / Atom::num(2))
                && eqq!(&a2__ * &b1__ + &a1__ * &b2__, 0)
                && neq!(&m_ + &n_ * (&p_ + Atom::num(1)) + Atom::num(1), 0)
        },
        rhs: {
            let denominator = &m_ + &n_ * (&p_ + Atom::num(1)) + Atom::num(1);
            let first_base = &a1__ + &b1__ * x_.pow(&n_ / Atom::num(2));
            let second_base = &a2__ + &b2__ * x_.pow(&n_ / Atom::num(2));
            let direct = &d__ * (&e__ * x_).pow(&m_ + Atom::num(1))
                * first_base.pow(&p_ + Atom::num(1))
                * second_base.pow(&p_ + Atom::num(1))
                / (&b1__ * &b2__ * &e__ * &denominator);
            let coefficient = (&a1__ * &a2__ * &d__ * (&m_ + Atom::num(1))
                - &b1__ * &b2__ * &c__ * &denominator)
                / (&b1__ * &b2__ * &denominator);
            let recursive_integrand = (&e__ * x_).pow(&m_) * first_base.pow(&p_) * second_base.pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            rubi_simp(&direct, x_) - rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_961(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 961,
        source: "Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_/(c_+d_.*x_^n_),x_Symbol] :=
          Int[ExpandIntegrand[(e*x)^m*(a+b*x^n)^p/(c+d*x^n),x],x] /;
        FreeQ[{a,b,c,d,e,m},x] && NeQ[b*c-a*d,0] && IGtQ[n,0] && IGtQ[p,0] && (IntegerQ[m] || IGtQ[2*(m+1),0] || Not[RationalQ[m]])",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (e__ * x_).pow(m_) * (a__ + b__ * x_.pow(n_)).pow(p_) / (c__ + d__ * x_.pow(n_)),
        with: [a__, b__, c__, d__, e__, m_, n_, p_, x_],
        optional: [b__, d__, e__, m_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && igtq!(n_, 0)
                && igtq!(p_, 0)
                && (integerq!(m_)
                    || igtq!(Atom::num(2) * (&m_ + Atom::num(1)), 0)
                    || !rationalq!(m_))
        },
        rhs: {
            let integrand = (&e__ * x_).pow(&m_)
                * (&a__ + &b__ * x_.pow(&n_)).pow(&p_)
                / (&c__ + &d__ * x_.pow(&n_));
            let expanded = rubi_expand_integrand(&integrand, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_962(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 962,
        source: "Int[(e_.*x_)^m_*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^2,x_Symbol] :=
          c^2*(e*x)^(m+1)*(a+b*x^n)^(p+1)/(a*e*(m+1)) -
          1/(a*e^n*(m+1)) \\[Star] Int[(e*x)^(m+n)*(a+b*x^n)^p*Simp[b*c^2*n*(p+1)+c*(b*c-2*a*d)*(m+1)-a*(m+1)*d^2*x^n,x],x] /;
        FreeQ[{a,b,c,d,e,p},x] && NeQ[b*c-a*d,0] && IGtQ[n,0] && LtQ[m,-1] && GtQ[n,0]",
        desc: "?",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, p_, x_],
        optional: [b__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__, p_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && igtq!(n_, 0)
                && ltq!(m_, -1)
                && gtq!(n_, 0)
        },
        rhs: {
            let base = &a__ + &b__ * x_.pow(&n_);
            let direct =
                c__.pow(2) * (&e__ * x_).pow(&m_ + Atom::num(1)) * base.pow(&p_ + Atom::num(1))
                    / (&a__ * &e__ * (&m_ + Atom::num(1)));
            let payload = simp!(
                &b__ * c__.pow(2) * &n_ * (&p_ + Atom::num(1))
                    + &c__ * (&b__ * &c__ - Atom::num(2) * &a__ * &d__) * (&m_ + Atom::num(1))
                    - &a__ * (&m_ + Atom::num(1)) * d__.pow(2) * x_.pow(&n_),
                x_
            );
            let recursive_integrand =
                (&e__ * x_).pow(&m_ + &n_) * base.pow(&p_) * payload;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&direct, x_)
                    - rubi_star(Atom::num(1) / (&a__ * e__.pow(&n_) * (&m_ + Atom::num(1))), recursive)
        },
    ));
}

fn push_rules_rule_963(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 963,
        source: "Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^2,x_Symbol] :=
          -(b*c-a*d)^2*(e*x)^(m+1)*(a+b*x^n)^(p+1)/(a*b^2*e*n*(p+1)) +
          1/(a*b^2*n*(p+1)) \\[Star] Int[(e*x)^m*(a+b*x^n)^(p+1)*Simp[(b*c-a*d)^2*(m+1)+b^2*c^2*n*(p+1)+a*b*d^2*n*(p+1)*x^n,x],x] /;
        FreeQ[{a,b,c,d,e,m,n},x] && NeQ[b*c-a*d,0] && IGtQ[n,0] && LtQ[p,-1]",
        desc: "?",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, p_, x_],
        optional: [b__, d__, e__, m_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && igtq!(n_, 0)
                && ltq!(p_, -1)
        },
        rhs: {
            let det = &b__ * &c__ - &a__ * &d__;
            let base = &a__ + &b__ * x_.pow(&n_);
            let direct = -det.pow(2)
                * (&e__ * x_).pow(&m_ + Atom::num(1))
                * base.pow(&p_ + Atom::num(1))
                / (&a__ * b__.pow(2) * &e__ * &n_ * (&p_ + Atom::num(1)));
            let payload = simp!(
                det.pow(2) * (&m_ + Atom::num(1))
                    + b__.pow(2) * c__.pow(2) * &n_ * (&p_ + Atom::num(1))
                    + &a__ * &b__ * d__.pow(2) * &n_ * (&p_ + Atom::num(1)) * x_.pow(&n_),
                x_
            );
            let recursive_integrand =
                (&e__ * x_).pow(&m_) * base.pow(&p_ + Atom::num(1)) * payload;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&direct, x_)
                    + rubi_star(Atom::num(1) / (&a__ * b__.pow(2) * &n_ * (&p_ + Atom::num(1))), recursive)
        },
    ));
}

fn push_rules_rule_964(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 964,
        source: "Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^2,x_Symbol] :=
          d^2*(e*x)^(m+n+1)*(a+b*x^n)^(p+1)/(b*e^(n+1)*(m+n*(p+2)+1)) +
          1/(b*(m+n*(p+2)+1)) \\[Star] Int[(e*x)^m*(a+b*x^n)^p*Simp[b*c^2*(m+n*(p+2)+1)-d*(a*d*(m+n+1)-2*b*c*(m+n*(p+2)+1))*x^n,x],x] /;
        FreeQ[{a,b,c,d,e,m,n,p},x] && NeQ[b*c-a*d,0] && IGtQ[n,0] && NeQ[m+n*(p+2)+1,0]",
        desc: "?",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, p_, x_],
        optional: [b__, d__, e__, m_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_, p_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && igtq!(n_, 0)
                && neq!(&m_ + &n_ * (&p_ + Atom::num(2)) + Atom::num(1), 0)
        },
        rhs: {
            let base = &a__ + &b__ * x_.pow(&n_);
            let denominator = &m_ + &n_ * (&p_ + Atom::num(2)) + Atom::num(1);
            let direct = d__.pow(2)
                * (&e__ * x_).pow(&m_ + &n_ + Atom::num(1))
                * base.pow(&p_ + Atom::num(1))
                / (&b__ * e__.pow(&n_ + Atom::num(1)) * &denominator);
            let payload = simp!(
                &b__ * c__.pow(2) * &denominator
                    + &d__
                        * ((Atom::num(2) * &b__ * &c__ - &a__ * &d__) * (&m_ + &n_ + Atom::num(1))
                            + Atom::num(2) * &b__ * &c__ * &n_ * (&p_ + Atom::num(1)))
                        * x_.pow(&n_),
                x_
            );
            let recursive_integrand =
                (&e__ * x_).pow(&m_) * base.pow(&p_) * payload;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&direct, x_)
                    + rubi_star(Atom::num(1) / (&b__ * denominator), recursive)
        },
    ));
}

fn push_rules_rule_965(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 965,
        source: "Int[x_^m_.*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
          With[{k=GCD[m+1,n]},
          1/k \\[Star] Subst[Int[x^((m+1)/k-1)*(a+b*x^(n/k))^p*(c+d*x^(n/k))^q,x],x,x^k] /;
         k!=1] /;
        FreeQ[{a,b,c,d,p,q},x] && NeQ[b*c-a*d,0] && IGtQ[n,0] && IntegerQ[m]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [a__, b__, c__, d__, m_, n_, p_, q_, x_],
        optional: [b__, d__, m_],
        when: {
            freeq!([a__, b__, c__, d__, p_, q_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
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
                * (&c__ + &d__ * sub_atom.pow(&n_ / &k)).pow(&q_);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);
            let substituted = rubi_subst(&transformed, sub, x_.pow(&k));
            rubi_star(Atom::num(1) / k, substituted)
        },
    ));
}

fn push_rules_rule_966(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 966,
        source: "Int[(e_.*x_)^m_*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
          With[{k=Denominator[m]},
          k/e \\[Star] Subst[Int[x^(k*(m+1)-1)*(a+b*x^(k*n)/e^n)^p*(c+d*x^(k*n)/e^n)^q,x],x,(e*x)^(1/k)]] /;
        FreeQ[{a,b,c,d,e,p,q},x] && NeQ[b*c-a*d,0] && IGtQ[n,0] && FractionQ[m] && IntegerQ[p]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, p_, q_, x_],
        optional: [b__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__, p_, q_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && igtq!(n_, 0)
                && fractionq!(m_)
                && integerq!(p_)
        },
        rhs: {
            let k_i = rational_denominator(&m_).rubi_rhs();
            let k = Atom::num(k_i);
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = sub_atom.pow(&k * (&m_ + Atom::num(1)) - Atom::num(1))
                * (&a__ + &b__ * sub_atom.pow(&k * &n_) / e__.pow(&n_)).pow(&p_)
                * (&c__ + &d__ * sub_atom.pow(&k * &n_) / e__.pow(&n_)).pow(&q_);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);
            let replacement = (&e__ * x_).pow(Atom::num(1) / &k);
            let substituted = rubi_subst(&transformed, sub, replacement);
            rubi_star(k, substituted / &e__)
        },
    ));
}

fn push_rules_rule_967(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 967,
        source: "Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
          e^(n-1)*(e*x)^(m-n+1)*(a+b*x^n)^(p+1)*(c+d*x^n)^q/(b*n*(p+1)) -
          e^n/(b*n*(p+1)) \\[Star] Int[(e*x)^(m-n)*(a+b*x^n)^(p+1)*(c+d*x^n)^(q-1)*Simp[c*(m-n+1)+d*(m+n*(q-1)+1)*x^n,x],x] /;
        FreeQ[{a,b,c,d,e},x] && NeQ[b*c-a*d,0] && IGtQ[n,0] && LtQ[p,-1] && GtQ[q,0] && GtQ[m-n+1,0] && IntBinomialQ[a,b,c,d,e,m,n,p,q,x]",
        desc: "Binomial product recurrence 3a with A=c, B=d and q=q-1",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, p_, q_, x_],
        optional: [b__, d__, e__, m_],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && igtq!(n_, 0)
                && ltq!(p_, -1)
                && gtq!(q_, 0)
                && gtq!(&m_ - &n_ + Atom::num(1), 0)
                && rubi_int_binomial_scaled_q(
                    &a__, &b__, &c__, &d__, &e__, &m_, &n_, &p_, &q_, x_,
                )
        },
        rhs: {
            let first_base = &a__ + &b__ * x_.pow(&n_);
            let second_base = &c__ + &d__ * x_.pow(&n_);
            let direct = e__.pow(&n_ - Atom::num(1))
                * (&e__ * x_).pow(&m_ - &n_ + Atom::num(1))
                * first_base.pow(&p_ + Atom::num(1))
                * second_base.pow(&q_)
                / (&b__ * &n_ * (&p_ + Atom::num(1)));
            let payload = simp!(
                &c__ * (&m_ - &n_ + Atom::num(1))
                    + &d__ * (&m_ + &n_ * (&q_ - Atom::num(1)) + Atom::num(1)) * x_.pow(&n_),
                x_
            );
            let recursive_integrand = (&e__ * x_).pow(&m_ - &n_)
                * first_base.pow(&p_ + Atom::num(1))
                * second_base.pow(&q_ - Atom::num(1))
                * payload;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&direct, x_)
                    - rubi_star(e__.pow(&n_), recursive / (&b__ * &n_ * (&p_ + Atom::num(1))))
        },
    ));
}

fn push_rules_rule_968(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 968,
        source: "Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
          -(c*b-a*d)*(e*x)^(m+1)*(a+b*x^n)^(p+1)*(c+d*x^n)^(q-1)/(a*b*e*n*(p+1)) +
          1/(a*b*n*(p+1)) \\[Star] Int[(e*x)^m*(a+b*x^n)^(p+1)*(c+d*x^n)^(q-2)*
            Simp[c*(c*b*n*(p+1)+(c*b-a*d)*(m+1))+d*(c*b*n*(p+1)+(c*b-a*d)*(m+n*(q-1)+1))*x^n,x],x] /;
        FreeQ[{a,b,c,d,e,m},x] && NeQ[b*c-a*d,0] && IGtQ[n,0] && LtQ[p,-1] && GtQ[q,1] && IntBinomialQ[a,b,c,d,e,m,n,p,q,x]",
        desc: "Binomial product recurrence 1 with A=c, B=d and q=q-1",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, p_, q_, x_],
        optional: [b__, d__, e__, m_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && igtq!(n_, 0)
                && ltq!(p_, -1)
                && gtq!(q_, 1)
                && rubi_int_binomial_scaled_q(
                    &a__, &b__, &c__, &d__, &e__, &m_, &n_, &p_, &q_, x_,
                )
        },
        rhs: {
            let first_base = &a__ + &b__ * x_.pow(&n_);
            let second_base = &c__ + &d__ * x_.pow(&n_);
            let cb_ad = &c__ * &b__ - &a__ * &d__;
            let direct = -&cb_ad
                * (&e__ * x_).pow(&m_ + Atom::num(1))
                * first_base.pow(&p_ + Atom::num(1))
                * second_base.pow(&q_ - Atom::num(1))
                / (&a__ * &b__ * &e__ * &n_ * (&p_ + Atom::num(1)));
            let payload = simp!(
                &c__ * (&c__ * &b__ * &n_ * (&p_ + Atom::num(1)) + &cb_ad * (&m_ + Atom::num(1)))
                    + &d__
                        * (&c__ * &b__ * &n_ * (&p_ + Atom::num(1))
                            + &cb_ad * (&m_ + &n_ * (&q_ - Atom::num(1)) + Atom::num(1)))
                        * x_.pow(&n_),
                x_
            );
            let recursive_integrand = (&e__ * x_).pow(&m_)
                * first_base.pow(&p_ + Atom::num(1))
                * second_base.pow(&q_ - Atom::num(2))
                * payload;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&direct, x_)
                    + rubi_star(Atom::num(1) / (&a__ * &b__ * &n_ * (&p_ + Atom::num(1))), recursive)
        },
    ));
}

fn push_rules_rule_969(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 969,
        source: "Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
          -(e*x)^(m+1)*(a+b*x^n)^(p+1)*(c+d*x^n)^q/(a*e*n*(p+1)) +
          1/(a*n*(p+1)) \\[Star] Int[(e*x)^m*(a+b*x^n)^(p+1)*(c+d*x^n)^(q-1)*Simp[c*(m+n*(p+1)+1)+d*(m+n*(p+q+1)+1)*x^n,x],x] /;
        FreeQ[{a,b,c,d,e,m},x] && NeQ[b*c-a*d,0] && IGtQ[n,0] && LtQ[p,-1] && LtQ[0,q,1] && IntBinomialQ[a,b,c,d,e,m,n,p,q,x]",
        desc: "Binomial product recurrence 3b with A=c, B=d and q=q-1",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, p_, q_, x_],
        optional: [b__, d__, e__, m_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && igtq!(n_, 0)
                && ltq!(p_, -1)
                && ltq!(0, q_, 1)
                && rubi_int_binomial_scaled_q(
                    &a__, &b__, &c__, &d__, &e__, &m_, &n_, &p_, &q_, x_,
                )
        },
        rhs: {
            let first_base = &a__ + &b__ * x_.pow(&n_);
            let second_base = &c__ + &d__ * x_.pow(&n_);
            let direct = -(&e__ * x_).pow(&m_ + Atom::num(1))
                * first_base.pow(&p_ + Atom::num(1))
                * second_base.pow(&q_)
                / (&a__ * &e__ * &n_ * (&p_ + Atom::num(1)));
            let payload = simp!(
                &c__ * (&m_ + &n_ * (&p_ + Atom::num(1)) + Atom::num(1))
                    + &d__ * (&m_ + &n_ * (&p_ + &q_ + Atom::num(1)) + Atom::num(1)) * x_.pow(&n_),
                x_
            );
            let recursive_integrand = (&e__ * x_).pow(&m_)
                * first_base.pow(&p_ + Atom::num(1))
                * second_base.pow(&q_ - Atom::num(1))
                * payload;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&direct, x_)
                    + rubi_star(Atom::num(1) / (&a__ * &n_ * (&p_ + Atom::num(1))), recursive)
        },
    ));
}

fn push_rules_rule_970(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 970,
        source: "Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
          -a*e^(2*n-1)*(e*x)^(m-2*n+1)*(a+b*x^n)^(p+1)*(c+d*x^n)^(q+1)/(b*n*(b*c-a*d)*(p+1)) +
          e^(2*n)/(b*n*(b*c-a*d)*(p+1)) \\[Star] Int[(e*x)^(m-2*n)*(a+b*x^n)^(p+1)*(c+d*x^n)^q*
            Simp[a*c*(m-2*n+1)+(a*d*(m-n+n*q+1)+b*c*n*(p+1))*x^n,x],x] /;
        FreeQ[{a,b,c,d,e,q},x] && NeQ[b*c-a*d,0] && IGtQ[n,0] && LtQ[p,-1] && GtQ[m-n+1,n] && IntBinomialQ[a,b,c,d,e,m,n,p,q,x]",
        desc: "Binomial product recurrence 3a with A=0, B=1 and m=m-n",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, p_, q_, x_],
        optional: [b__, d__, e__, m_],
        when: {
            freeq!([a__, b__, c__, d__, e__, q_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && igtq!(n_, 0)
                && ltq!(p_, -1)
                && gtq!(&m_ - &n_ + Atom::num(1), n_)
                && rubi_int_binomial_scaled_q(
                    &a__, &b__, &c__, &d__, &e__, &m_, &n_, &p_, &q_, x_,
                )
        },
        rhs: {
            let det = &b__ * &c__ - &a__ * &d__;
            let first_base = &a__ + &b__ * x_.pow(&n_);
            let second_base = &c__ + &d__ * x_.pow(&n_);
            let direct = -&a__
                * e__.pow(Atom::num(2) * &n_ - Atom::num(1))
                * (&e__ * x_).pow(&m_ - Atom::num(2) * &n_ + Atom::num(1))
                * first_base.pow(&p_ + Atom::num(1))
                * second_base.pow(&q_ + Atom::num(1))
                / (&b__ * &n_ * &det * (&p_ + Atom::num(1)));
            let payload = simp!(
                &a__ * &c__ * (&m_ - Atom::num(2) * &n_ + Atom::num(1))
                    + (&a__ * &d__ * (&m_ - &n_ + &n_ * &q_ + Atom::num(1))
                        + &b__ * &c__ * &n_ * (&p_ + Atom::num(1)))
                        * x_.pow(&n_),
                x_
            );
            let recursive_integrand = (&e__ * x_).pow(&m_ - Atom::num(2) * &n_)
                * first_base.pow(&p_ + Atom::num(1))
                * second_base.pow(&q_)
                * payload;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&direct, x_)
                    + rubi_star(e__.pow(Atom::num(2) * &n_), recursive
                            / (&b__ * &n_ * det * (&p_ + Atom::num(1))))
        },
    ));
}

fn push_rules_rule_971(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 971,
        source: "Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
          e^(n-1)*(e*x)^(m-n+1)*(a+b*x^n)^(p+1)*(c+d*x^n)^(q+1)/(n*(b*c-a*d)*(p+1)) -
          e^n/(n*(b*c-a*d)*(p+1)) \\[Star] Int[(e*x)^(m-n)*(a+b*x^n)^(p+1)*(c+d*x^n)^q*Simp[c*(m-n+1)+d*(m+n*(p+q+1)+1)*x^n,x],x] /;
        FreeQ[{a,b,c,d,e,q},x] && NeQ[b*c-a*d,0] && IGtQ[n,0] && LtQ[p,-1] && GeQ[n,m-n+1] && GtQ[m-n+1,0] && IntBinomialQ[a,b,c,d,e,m,n,p,q,x]",
        desc: "Binomial product recurrence 3b with A=0, B=1 and m=m-n",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, p_, q_, x_],
        optional: [b__, d__, e__, m_],
        when: {
            freeq!([a__, b__, c__, d__, e__, q_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && igtq!(n_, 0)
                && ltq!(p_, -1)
                && geq!(n_, &m_ - &n_ + Atom::num(1))
                && gtq!(&m_ - &n_ + Atom::num(1), 0)
                && rubi_int_binomial_scaled_q(
                    &a__, &b__, &c__, &d__, &e__, &m_, &n_, &p_, &q_, x_,
                )
        },
        rhs: {
            let det = &b__ * &c__ - &a__ * &d__;
            let first_base = &a__ + &b__ * x_.pow(&n_);
            let second_base = &c__ + &d__ * x_.pow(&n_);
            let direct = e__.pow(&n_ - Atom::num(1))
                * (&e__ * x_).pow(&m_ - &n_ + Atom::num(1))
                * first_base.pow(&p_ + Atom::num(1))
                * second_base.pow(&q_ + Atom::num(1))
                / (&n_ * &det * (&p_ + Atom::num(1)));
            let payload = simp!(
                &c__ * (&m_ - &n_ + Atom::num(1))
                    + &d__ * (&m_ + &n_ * (&p_ + &q_ + Atom::num(1)) + Atom::num(1)) * x_.pow(&n_),
                x_
            );
            let recursive_integrand = (&e__ * x_).pow(&m_ - &n_)
                * first_base.pow(&p_ + Atom::num(1))
                * second_base.pow(&q_)
                * payload;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&direct, x_)
                    - rubi_star(e__.pow(&n_), recursive / (&n_ * det * (&p_ + Atom::num(1))))
        },
    ));
}

fn push_rules_rule_972(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 972,
        source: "Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
          -b*(e*x)^(m+1)*(a+b*x^n)^(p+1)*(c+d*x^n)^(q+1)/(a*e*n*(b*c-a*d)*(p+1)) +
          1/(a*n*(b*c-a*d)*(p+1)) \\[Star]
            Int[(e*x)^m*(a+b*x^n)^(p+1)*(c+d*x^n)^q*Simp[c*b*(m+1)+n*(b*c-a*d)*(p+1)+d*b*(m+n*(p+q+2)+1)*x^n,x],x] /;
        FreeQ[{a,b,c,d,e,m,q},x] && NeQ[b*c-a*d,0] && IGtQ[n,0] && LtQ[p,-1] && IntBinomialQ[a,b,c,d,e,m,n,p,q,x]",
        desc: "Binomial product recurrence 3b with A=1 and B=0",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, p_, q_, x_],
        optional: [b__, d__, e__, m_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, q_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && igtq!(n_, 0)
                && ltq!(p_, -1)
                && rubi_int_binomial_scaled_q(
                    &a__, &b__, &c__, &d__, &e__, &m_, &n_, &p_, &q_, x_,
                )
        },
        rhs: {
            let det = &b__ * &c__ - &a__ * &d__;
            let first_base = &a__ + &b__ * x_.pow(&n_);
            let second_base = &c__ + &d__ * x_.pow(&n_);
            let direct = -&b__
                * (&e__ * x_).pow(&m_ + Atom::num(1))
                * first_base.pow(&p_ + Atom::num(1))
                * second_base.pow(&q_ + Atom::num(1))
                / (&a__ * &e__ * &n_ * &det * (&p_ + Atom::num(1)));
            let payload = simp!(
                &c__ * &b__ * (&m_ + Atom::num(1))
                    + &n_ * &det * (&p_ + Atom::num(1))
                    + &d__ * &b__ * (&m_ + &n_ * (&p_ + &q_ + Atom::num(2)) + Atom::num(1)) * x_.pow(&n_),
                x_
            );
            let recursive_integrand = (&e__ * x_).pow(&m_)
                * first_base.pow(&p_ + Atom::num(1))
                * second_base.pow(&q_)
                * payload;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&direct, x_)
                    + rubi_star(Atom::num(1) / (&a__ * &n_ * det * (&p_ + Atom::num(1))), recursive)
        },
    ));
}

fn push_rules_rule_973(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 973,
        source: "Int[(e_.*x_)^m_*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
          (e*x)^(m+1)*(a+b*x^n)^p*(c+d*x^n)^q/(e*(m+1)) -
          n/(e^n*(m+1)) \\[Star] Int[(e*x)^(m+n)*(a+b*x^n)^(p-1)*(c+d*x^n)^(q-1)*Simp[b*c*p+a*d*q+b*d*(p+q)*x^n,x],x] /;
        FreeQ[{a,b,c,d,e},x] && NeQ[b*c-a*d,0] && IGtQ[n,0] && GtQ[q,0] && LtQ[m,-1] && GtQ[p,0] && IntBinomialQ[a,b,c,d,e,m,n,p,q,x]",
        desc: "Binomial product recurrence 2a with A=a, B=b and p=p-1",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, p_, q_, x_],
        optional: [b__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && igtq!(n_, 0)
                && gtq!(q_, 0)
                && ltq!(m_, -1)
                && gtq!(p_, 0)
                && rubi_int_binomial_scaled_q(
                    &a__, &b__, &c__, &d__, &e__, &m_, &n_, &p_, &q_, x_,
                )
        },
        rhs: {
            let first_base = &a__ + &b__ * x_.pow(&n_);
            let second_base = &c__ + &d__ * x_.pow(&n_);
            let direct = (&e__ * x_).pow(&m_ + Atom::num(1))
                * first_base.pow(&p_)
                * second_base.pow(&q_)
                / (&e__ * (&m_ + Atom::num(1)));
            let payload = simp!(
                &b__ * &c__ * &p_ + &a__ * &d__ * &q_ + &b__ * &d__ * (&p_ + &q_) * x_.pow(&n_),
                x_
            );
            let recursive_integrand = (&e__ * x_).pow(&m_ + &n_)
                * first_base.pow(&p_ - Atom::num(1))
                * second_base.pow(&q_ - Atom::num(1))
                * payload;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&direct, x_)
                    - rubi_star(&n_, recursive / (e__.pow(&n_) * (&m_ + Atom::num(1))))
        },
    ));
}

fn push_rules_rule_974(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 974,
        source: "Int[(e_.*x_)^m_*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
          c*(e*x)^(m+1)*(a+b*x^n)^(p+1)*(c+d*x^n)^(q-1)/(a*e*(m+1)) -
          1/(a*e^n*(m+1)) \\[Star] Int[(e*x)^(m+n)*(a+b*x^n)^p*(c+d*x^n)^(q-2)*
            Simp[c*(c*b-a*d)*(m+1)+c*n*(b*c*(p+1)+a*d*(q-1))+d*((c*b-a*d)*(m+1)+c*b*n*(p+q))*x^n,x],x] /;
        FreeQ[{a,b,c,d,e,p},x] && NeQ[b*c-a*d,0] && IGtQ[n,0] && GtQ[q,1] && LtQ[m,-1] && IntBinomialQ[a,b,c,d,e,m,n,p,q,x]",
        desc: "Binomial product recurrence 2a with A=c, B=d and q=q-1",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, p_, q_, x_],
        optional: [b__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__, p_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && igtq!(n_, 0)
                && gtq!(q_, 1)
                && ltq!(m_, -1)
                && rubi_int_binomial_scaled_q(
                    &a__, &b__, &c__, &d__, &e__, &m_, &n_, &p_, &q_, x_,
                )
        },
        rhs: {
            let first_base = &a__ + &b__ * x_.pow(&n_);
            let second_base = &c__ + &d__ * x_.pow(&n_);
            let direct = &c__
                * (&e__ * x_).pow(&m_ + Atom::num(1))
                * first_base.pow(&p_ + Atom::num(1))
                * second_base.pow(&q_ - Atom::num(1))
                / (&a__ * &e__ * (&m_ + Atom::num(1)));
            let payload = simp!(
                &c__ * (&c__ * &b__ - &a__ * &d__) * (&m_ + Atom::num(1))
                    + &c__ * &n_ * (&b__ * &c__ * (&p_ + Atom::num(1)) + &a__ * &d__ * (&q_ - Atom::num(1)))
                    + &d__ * ((&c__ * &b__ - &a__ * &d__) * (&m_ + Atom::num(1)) + &c__ * &b__ * &n_ * (&p_ + &q_))
                        * x_.pow(&n_),
                x_
            );
            let recursive_integrand = (&e__ * x_).pow(&m_ + &n_)
                * first_base.pow(&p_)
                * second_base.pow(&q_ - Atom::num(2))
                * payload;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&direct, x_)
                    - rubi_star(Atom::num(1) / (&a__ * e__.pow(&n_) * (&m_ + Atom::num(1))), recursive)
        },
    ));
}

fn push_rules_rule_975(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 975,
        source: "Int[(e_.*x_)^m_*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
          (e*x)^(m+1)*(a+b*x^n)^(p+1)*(c+d*x^n)^q/(a*e*(m+1)) -
          1/(a*e^n*(m+1)) \\[Star] Int[(e*x)^(m+n)*(a+b*x^n)^p*(c+d*x^n)^(q-1)*
            Simp[c*b*(m+1)+n*(b*c*(p+1)+a*d*q)+d*(b*(m+1)+b*n*(p+q+1))*x^n,x],x] /;
        FreeQ[{a,b,c,d,e,p},x] && NeQ[b*c-a*d,0] && IGtQ[n,0] && LtQ[0,q,1] && LtQ[m,-1] && IntBinomialQ[a,b,c,d,e,m,n,p,q,x]",
        desc: "Binomial product recurrence 4b with A=c, B=d and q=q-1",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, p_, q_, x_],
        optional: [b__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__, p_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && igtq!(n_, 0)
                && ltq!(0, q_, 1)
                && ltq!(m_, -1)
                && rubi_int_binomial_scaled_q(
                    &a__, &b__, &c__, &d__, &e__, &m_, &n_, &p_, &q_, x_,
                )
        },
        rhs: {
            let first_base = &a__ + &b__ * x_.pow(&n_);
            let second_base = &c__ + &d__ * x_.pow(&n_);
            let direct = (&e__ * x_).pow(&m_ + Atom::num(1))
                * first_base.pow(&p_ + Atom::num(1))
                * second_base.pow(&q_)
                / (&a__ * &e__ * (&m_ + Atom::num(1)));
            let payload = simp!(
                &c__ * &b__ * (&m_ + Atom::num(1))
                    + &n_ * (&b__ * &c__ * (&p_ + Atom::num(1)) + &a__ * &d__ * &q_)
                    + &d__ * (&b__ * (&m_ + Atom::num(1)) + &b__ * &n_ * (&p_ + &q_ + Atom::num(1)))
                        * x_.pow(&n_),
                x_
            );
            let recursive_integrand = (&e__ * x_).pow(&m_ + &n_)
                * first_base.pow(&p_)
                * second_base.pow(&q_ - Atom::num(1))
                * payload;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&direct, x_)
                    - rubi_star(Atom::num(1) / (&a__ * e__.pow(&n_) * (&m_ + Atom::num(1))), recursive)
        },
    ));
}

fn push_rules_rule_976(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 976,
        source: "Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
          (e*x)^(m+1)*(a+b*x^n)^p*(c+d*x^n)^q/(e*(m+n*(p+q)+1)) +
          n/(m+n*(p+q)+1) \\[Star] Int[(e*x)^m*(a+b*x^n)^(p-1)*(c+d*x^n)^(q-1)*Simp[a*c*(p+q)+(q*(b*c-a*d)+a*d*(p+q))*x^n,x],x] /;
        FreeQ[{a,b,c,d,e,m},x] && NeQ[b*c-a*d,0] && IGtQ[n,0] && GtQ[q,0] && GtQ[p,0] && IntBinomialQ[a,b,c,d,e,m,n,p,q,x]",
        desc: "Binomial product recurrence 2b with A=a, B=b and p=p-1",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, p_, q_, x_],
        optional: [b__, d__, e__, m_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && igtq!(n_, 0)
                && gtq!(q_, 0)
                && gtq!(p_, 0)
                && rubi_int_binomial_scaled_q(
                    &a__, &b__, &c__, &d__, &e__, &m_, &n_, &p_, &q_, x_,
                )
        },
        rhs: {
            let det = &b__ * &c__ - &a__ * &d__;
            let first_base = &a__ + &b__ * x_.pow(&n_);
            let second_base = &c__ + &d__ * x_.pow(&n_);
            let denominator = &m_ + &n_ * (&p_ + &q_) + Atom::num(1);
            let direct = (&e__ * x_).pow(&m_ + Atom::num(1))
                * first_base.pow(&p_)
                * second_base.pow(&q_)
                / (&e__ * &denominator);
            let payload = simp!(
                &a__ * &c__ * (&p_ + &q_) + (&q_ * &det + &a__ * &d__ * (&p_ + &q_)) * x_.pow(&n_),
                x_
            );
            let recursive_integrand = (&e__ * x_).pow(&m_)
                * first_base.pow(&p_ - Atom::num(1))
                * second_base.pow(&q_ - Atom::num(1))
                * payload;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&direct, x_)
                    + rubi_star(n_, recursive / denominator)
        },
    ));
}

fn push_rules_rule_977(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 977,
        source: "Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
          d*(e*x)^(m+1)*(a+b*x^n)^(p+1)*(c+d*x^n)^(q-1)/(b*e*(m+n*(p+q)+1)) +
          1/(b*(m+n*(p+q)+1)) \\[Star] Int[(e*x)^m*(a+b*x^n)^p*(c+d*x^n)^(q-2)*
            Simp[c*((c*b-a*d)*(m+1)+c*b*n*(p+q))+(d*(c*b-a*d)*(m+1)+d*n*(q-1)*(b*c-a*d)+c*b*d*n*(p+q))*x^n,x],x] /;
        FreeQ[{a,b,c,d,e,m,p},x] && NeQ[b*c-a*d,0] && IGtQ[n,0] && GtQ[q,1] && IntBinomialQ[a,b,c,d,e,m,n,p,q,x]",
        desc: "Binomial product recurrence 2b with A=c, B=d and q=q-1",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, p_, q_, x_],
        optional: [b__, d__, e__, m_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, p_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && igtq!(n_, 0)
                && gtq!(q_, 1)
                && rubi_int_binomial_scaled_q(
                    &a__, &b__, &c__, &d__, &e__, &m_, &n_, &p_, &q_, x_,
                )
        },
        rhs: {
            let det = &b__ * &c__ - &a__ * &d__;
            let reverse_det = &c__ * &b__ - &a__ * &d__;
            let first_base = &a__ + &b__ * x_.pow(&n_);
            let second_base = &c__ + &d__ * x_.pow(&n_);
            let denominator = &m_ + &n_ * (&p_ + &q_) + Atom::num(1);
            let direct = &d__
                * (&e__ * x_).pow(&m_ + Atom::num(1))
                * first_base.pow(&p_ + Atom::num(1))
                * second_base.pow(&q_ - Atom::num(1))
                / (&b__ * &e__ * &denominator);
            let payload = simp!(
                &c__ * (&reverse_det * (&m_ + Atom::num(1)) + &c__ * &b__ * &n_ * (&p_ + &q_))
                    + (&d__ * &reverse_det * (&m_ + Atom::num(1))
                        + &d__ * &n_ * (&q_ - Atom::num(1)) * &det
                        + &c__ * &b__ * &d__ * &n_ * (&p_ + &q_))
                        * x_.pow(&n_),
                x_
            );
            let recursive_integrand = (&e__ * x_).pow(&m_)
                * first_base.pow(&p_)
                * second_base.pow(&q_ - Atom::num(2))
                * payload;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&direct, x_)
                    + rubi_star(Atom::num(1) / (&b__ * denominator), recursive)
        },
    ));
}

fn push_rules_rule_978(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 978,
        source: "Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
          e^(n-1)*(e*x)^(m-n+1)*(a+b*x^n)^(p+1)*(c+d*x^n)^q/(b*(m+n*(p+q)+1)) -
          e^n/(b*(m+n*(p+q)+1)) \\[Star]
            Int[(e*x)^(m-n)*(a+b*x^n)^p*(c+d*x^n)^(q-1)*Simp[a*c*(m-n+1)+(a*d*(m-n+1)-n*q*(b*c-a*d))*x^n,x],x] /;
        FreeQ[{a,b,c,d,e,p},x] && NeQ[b*c-a*d,0] && IGtQ[n,0] && GtQ[q,0] && GtQ[m-n+1,0] && IntBinomialQ[a,b,c,d,e,m,n,p,q,x]",
        desc: "Binomial product recurrence 4a with A=c, B=d and q=q-1",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, p_, q_, x_],
        optional: [b__, d__, e__, m_],
        when: {
            freeq!([a__, b__, c__, d__, e__, p_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && igtq!(n_, 0)
                && gtq!(q_, 0)
                && gtq!(&m_ - &n_ + Atom::num(1), 0)
                && rubi_int_binomial_scaled_q(
                    &a__, &b__, &c__, &d__, &e__, &m_, &n_, &p_, &q_, x_,
                )
        },
        rhs: {
            let det = &b__ * &c__ - &a__ * &d__;
            let first_base = &a__ + &b__ * x_.pow(&n_);
            let second_base = &c__ + &d__ * x_.pow(&n_);
            let denominator = &m_ + &n_ * (&p_ + &q_) + Atom::num(1);
            let direct = e__.pow(&n_ - Atom::num(1))
                * (&e__ * x_).pow(&m_ - &n_ + Atom::num(1))
                * first_base.pow(&p_ + Atom::num(1))
                * second_base.pow(&q_)
                / (&b__ * &denominator);
            let payload = simp!(
                &a__ * &c__ * (&m_ - &n_ + Atom::num(1))
                    + (&a__ * &d__ * (&m_ - &n_ + Atom::num(1)) - &n_ * &q_ * &det) * x_.pow(&n_),
                x_
            );
            let recursive_integrand = (&e__ * x_).pow(&m_ - &n_)
                * first_base.pow(&p_)
                * second_base.pow(&q_ - Atom::num(1))
                * payload;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&direct, x_)
                    - rubi_star(e__.pow(&n_), recursive / (&b__ * denominator))
        },
    ));
}

fn push_rules_rule_979(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 979,
        source: "Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
          e^(2*n-1)*(e*x)^(m-2*n+1)*(a+b*x^n)^(p+1)*(c+d*x^n)^(q+1)/(b*d*(m+n*(p+q)+1)) -
          e^(2*n)/(b*d*(m+n*(p+q)+1)) \\[Star]
            Int[(e*x)^(m-2*n)*(a+b*x^n)^p*(c+d*x^n)^q*Simp[a*c*(m-2*n+1)+(a*d*(m+n*(q-1)+1)+b*c*(m+n*(p-1)+1))*x^n,x],x] /;
        FreeQ[{a,b,c,d,e,p,q},x] && NeQ[b*c-a*d,0] && IGtQ[n,0] && GtQ[m-n+1,n] && IntBinomialQ[a,b,c,d,e,m,n,p,q,x]",
        desc: "Binomial product recurrence 4a with A=0, B=1 and m=m-n",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, p_, q_, x_],
        optional: [b__, d__, e__, m_],
        when: {
            freeq!([a__, b__, c__, d__, e__, p_, q_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && igtq!(n_, 0)
                && gtq!(&m_ - &n_ + Atom::num(1), n_)
                && rubi_int_binomial_scaled_q(
                    &a__, &b__, &c__, &d__, &e__, &m_, &n_, &p_, &q_, x_,
                )
        },
        rhs: {
            let first_base = &a__ + &b__ * x_.pow(&n_);
            let second_base = &c__ + &d__ * x_.pow(&n_);
            let denominator = &m_ + &n_ * (&p_ + &q_) + Atom::num(1);
            let direct = e__.pow(Atom::num(2) * &n_ - Atom::num(1))
                * (&e__ * x_).pow(&m_ - Atom::num(2) * &n_ + Atom::num(1))
                * first_base.pow(&p_ + Atom::num(1))
                * second_base.pow(&q_ + Atom::num(1))
                / (&b__ * &d__ * &denominator);
            let payload = simp!(
                &a__ * &c__ * (&m_ - Atom::num(2) * &n_ + Atom::num(1))
                    + (&a__ * &d__ * (&m_ + &n_ * (&q_ - Atom::num(1)) + Atom::num(1))
                        + &b__ * &c__ * (&m_ + &n_ * (&p_ - Atom::num(1)) + Atom::num(1)))
                        * x_.pow(&n_),
                x_
            );
            let recursive_integrand = (&e__ * x_).pow(&m_ - Atom::num(2) * &n_)
                * first_base.pow(&p_)
                * second_base.pow(&q_)
                * payload;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&direct, x_)
                    - rubi_star(e__.pow(Atom::num(2) * &n_), recursive
                            / (&b__ * &d__ * denominator))
        },
    ));
}

fn push_rules_rule_980(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 980,
        source: "Int[(e_.*x_)^m_*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
          (e*x)^(m+1)*(a+b*x^n)^(p+1)*(c+d*x^n)^(q+1)/(a*c*e*(m+1)) -
          1/(a*c*e^n*(m+1)) \\[Star]
            Int[(e*x)^(m+n)*(a+b*x^n)^p*(c+d*x^n)^q*Simp[(b*c+a*d)*(m+n+1)+n*(b*c*p+a*d*q)+b*d*(m+n*(p+q+2)+1)*x^n,x],x] /;
        FreeQ[{a,b,c,d,e,p,q},x] && NeQ[b*c-a*d,0] && IGtQ[n,0] && LtQ[m,-1] && IntBinomialQ[a,b,c,d,e,m,n,p,q,x]",
        desc: "Binomial product recurrence 4b with A=1 and B=0",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, p_, q_, x_],
        optional: [b__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__, p_, q_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && igtq!(n_, 0)
                && ltq!(m_, -1)
                && rubi_int_binomial_scaled_q(
                    &a__, &b__, &c__, &d__, &e__, &m_, &n_, &p_, &q_, x_,
                )
        },
        rhs: {
            let first_base = &a__ + &b__ * x_.pow(&n_);
            let second_base = &c__ + &d__ * x_.pow(&n_);
            let direct = (&e__ * x_).pow(&m_ + Atom::num(1))
                * first_base.pow(&p_ + Atom::num(1))
                * second_base.pow(&q_ + Atom::num(1))
                / (&a__ * &c__ * &e__ * (&m_ + Atom::num(1)));
            let payload = simp!(
                (&b__ * &c__ + &a__ * &d__) * (&m_ + &n_ + Atom::num(1))
                    + &n_ * (&b__ * &c__ * &p_ + &a__ * &d__ * &q_)
                    + &b__ * &d__ * (&m_ + &n_ * (&p_ + &q_ + Atom::num(2)) + Atom::num(1))
                        * x_.pow(&n_),
                x_
            );
            let recursive_integrand = (&e__ * x_).pow(&m_ + &n_)
                * first_base.pow(&p_)
                * second_base.pow(&q_)
                * payload;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&direct, x_)
                    - rubi_star(Atom::num(1) / (&a__ * &c__ * e__.pow(&n_) * (&m_ + Atom::num(1))), recursive)
        },
    ));
}

fn push_rules_rule_981(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 981,
        source: "Int[(e_.*x_)^m_./((a_+b_.*x_^n_)*(c_+d_.*x_^n_)),x_Symbol] :=
          -a*e^n/(b*c-a*d) \\[Star] Int[(e*x)^(m-n)/(a+b*x^n),x] + c*e^n/(b*c-a*d) \\[Star] Int[(e*x)^(m-n)/(c+d*x^n),x] /;
        FreeQ[{a,b,c,d,e,m},x] && NeQ[b*c-a*d,0] && IGtQ[n,0] && LeQ[n,m,2*n-1]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, x_],
        optional: [b__, d__, e__, m_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && igtq!(n_, 0)
                && leq!(n_, m_, Atom::num(2) * &n_ - Atom::num(1))
        },
        rhs: {
            let det = &b__ * &c__ - &a__ * &d__;
            let first_base = &a__ + &b__ * x_.pow(&n_);
            let second_base = &c__ + &d__ * x_.pow(&n_);
            let first_integrand = (&e__ * x_).pow(&m_ - &n_) / first_base;
            let second_integrand = (&e__ * x_).pow(&m_ - &n_) / second_base;
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(-&a__ * e__.pow(&n_) / &det, first)
                    + rubi_star(&c__ * e__.pow(&n_) / det, second)
        },
    ));
}

fn push_rules_rule_982(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 982,
        source: "Int[(e_.*x_)^m_./((a_+b_.*x_^n_)*(c_+d_.*x_^n_)),x_Symbol] :=
          b/(b*c-a*d) \\[Star] Int[(e*x)^m/(a+b*x^n),x] - d/(b*c-a*d) \\[Star] Int[(e*x)^m/(c+d*x^n),x] /;
        FreeQ[{a,b,c,d,e,m},x] && NeQ[b*c-a*d,0] && IGtQ[n,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, x_],
        optional: [b__, d__, e__, m_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && igtq!(n_, 0)
        },
        rhs: {
            let det = &b__ * &c__ - &a__ * &d__;
            let first_base = &a__ + &b__ * x_.pow(&n_);
            let second_base = &c__ + &d__ * x_.pow(&n_);
            let first_integrand = (&e__ * x_).pow(&m_) / first_base;
            let second_integrand = (&e__ * x_).pow(&m_) / second_base;
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(b__, first / &det)
                    - rubi_star(d__, second / det)
        },
    ));
}

fn push_rules_rule_983(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, n_, q_, x_);
    rules.push(rubi_rule!(
        order: 983,
        source: "Int[(e_.*x_)^m_*(c_+d_.*x_^n_)^q_./(a_+b_.*x_^n_),x_Symbol] :=
          e^n/b \\[Star] Int[(e*x)^(m-n)*(c+d*x^n)^q,x] - a*e^n/b \\[Star] Int[(e*x)^(m-n)*(c+d*x^n)^q/(a+b*x^n),x] /;
        FreeQ[{a,b,c,d,e,m,q},x] && NeQ[b*c-a*d,0] && IGtQ[n,0] && LeQ[n,m,2*n-1] && IntBinomialQ[a,b,c,d,e,m,n,-1,q,x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (e__ * x_).pow(m_) * (c__ + d__ * x_.pow(n_)).pow(q_) / (a__ + b__ * x_.pow(n_)),
        with: [a__, b__, c__, d__, e__, m_, n_, q_, x_],
        optional: [b__, d__, e__, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, q_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && igtq!(n_, 0)
                && leq!(n_, m_, Atom::num(2) * &n_ - Atom::num(1))
                && rubi_int_binomial_scaled_q(
                    &a__,
                    &b__,
                    &c__,
                    &d__,
                    &e__,
                    &m_,
                    &n_,
                    &(-Atom::num(1)),
                    &q_,
                    x_,
                )
        },
        rhs: {
            let first_base = &a__ + &b__ * x_.pow(&n_);
            let second_base = &c__ + &d__ * x_.pow(&n_);
            let first_integrand = (&e__ * x_).pow(&m_ - &n_) * second_base.pow(&q_);
            let second_integrand = (&e__ * x_).pow(&m_ - &n_) * second_base.pow(&q_) / first_base;
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(e__.pow(&n_), first / &b__)
                    - rubi_star(&a__ * e__.pow(&n_) / b__, second)
        },
    ));
}

fn push_rules_rule_984(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 984,
        source: "Int[x_*(a_+b_.*x_^n_)^p_/(c_+d_.*x_^n_),x_Symbol] :=
          b/d \\[Star] Int[x*(a+b*x^n)^(p-1),x] - (b*c-a*d)/d \\[Star] Int[x*(a+b*x^n)^(p-1)/(c+d*x^n),x] /;
        FreeQ[{a,b,c,d},x] && NeQ[b*c-a*d,0] && IGtQ[n,0] && GtQ[p,0] && IntBinomialQ[a,b,c,d,1,1,n,p,-1,x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [a__, b__, c__, d__, n_, p_, x_],
        optional: [b__, d__],
        when: {
            let one = Atom::num(1);
            let minus_one = -Atom::num(1);
            freeq!([a__, b__, c__, d__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && igtq!(n_, 0)
                && gtq!(p_, 0)
                && rubi_int_binomial_scaled_q(
                    &a__, &b__, &c__, &d__, &one, &one, &n_, &p_, &minus_one, x_,
                )
        },
        rhs: {
            let det = &b__ * &c__ - &a__ * &d__;
            let first_base = &a__ + &b__ * x_.pow(&n_);
            let second_base = &c__ + &d__ * x_.pow(&n_);
            let first_integrand = x_ * first_base.pow(&p_ - Atom::num(1));
            let second_integrand = x_ * first_base.pow(&p_ - Atom::num(1)) / second_base;
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(b__, first / &d__)
                    - rubi_star(det, second / d__)
        },
    ));
}

fn push_rules_rule_985(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 985,
        source: "Int[x_*(a_+b_.*x_^n_)^p_/(c_+d_.*x_^n_),x_Symbol] :=
          b/(b*c-a*d) \\[Star] Int[x*(a+b*x^n)^(p-1),x] - d/(b*c-a*d) \\[Star] Int[x*(a+b*x^n)^(p+1)/(c+d*x^n),x] /;
        FreeQ[{a,b,c,d},x] && NeQ[b*c-a*d,0] && IGtQ[n,0] && LtQ[p,-1] && IntBinomialQ[a,b,c,d,1,1,n,p,-1,x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [a__, b__, c__, d__, n_, p_, x_],
        optional: [b__, d__],
        when: {
            let one = Atom::num(1);
            let minus_one = -Atom::num(1);
            freeq!([a__, b__, c__, d__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && igtq!(n_, 0)
                && ltq!(p_, -1)
                && rubi_int_binomial_scaled_q(
                    &a__, &b__, &c__, &d__, &one, &one, &n_, &p_, &minus_one, x_,
                )
        },
        rhs: {
            let det = &b__ * &c__ - &a__ * &d__;
            let first_base = &a__ + &b__ * x_.pow(&n_);
            let second_base = &c__ + &d__ * x_.pow(&n_);
            let first_integrand = x_ * first_base.pow(&p_ - Atom::num(1));
            let second_integrand = x_ * first_base.pow(&p_ + Atom::num(1)) / second_base;
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(b__, first / &det)
                    - rubi_star(d__, second / det)
        },
    ));
}

fn push_rules_rule_986(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 986,
        source: "Int[x_/((a_+b_.*x_^3)*Sqrt[c_+d_.*x_^3]),x_Symbol] :=
          With[{q=Rt[d/c,3]},
          q*ArcTanh[Sqrt[c+d*x^3]/Rt[c,2]]/(9*2^(2/3)*b*Rt[c,2]) +
          q*ArcTan[Sqrt[c+d*x^3]/(Sqrt[3]*Rt[c,2])]/(3*2^(2/3)*Sqrt[3]*b*Rt[c,2]) -
          q*ArcTan[Sqrt[3]*Rt[c,2]*(1+2^(1/3)*q*x)/Sqrt[c+d*x^3]]/(3*2^(2/3)*Sqrt[3]*b*Rt[c,2]) -
          q*ArcTanh[Rt[c,2]*(1-2^(1/3)*q*x)/Sqrt[c+d*x^3]]/(3*2^(2/3)*b*Rt[c,2])] /;
        FreeQ[{a,b,c,d},x] && NeQ[b*c-a*d,0] && EqQ[4*b*c-a*d,0] && PosQ[c]",
        desc: "Algebraic expansion",
        refs: ["Goursat pseudo-elliptic integral"],
        pattern:  rubi_shared_pattern_10(symbols),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(Atom::num(4) * &b__ * &c__ - &a__ * &d__, 0)
                && posq!(c__)
        },
        rhs: {
            let q = rubi_rt(&(&d__ / &c__), 3);
            let rt_c = rubi_rt(&c__, 2);
            let sqrt_three = Atom::num(3).sqrt();
            let two_one_third = rubi_rt(&Atom::num(2), 3);
            let two_two_thirds = two_one_third.pow(2);
            let radical = (&c__ + &d__ * x_.pow(3)).sqrt();
            let first_arg = &radical / &rt_c;
            let second_arg = &radical / (&sqrt_three * &rt_c);
            let third_arg =
                &sqrt_three * &rt_c * (Atom::num(1) + &two_one_third * &q * x_) / &radical;
            let fourth_arg = &rt_c * (Atom::num(1) - &two_one_third * &q * x_) / radical;

            rubi_simp(
                    &(&q * first_arg.atanh()
                        / (Atom::num(9) * &two_two_thirds * &b__ * &rt_c)),
                    x_,
                ) + rubi_simp(
                    &(&q * second_arg.atan()
                        / (Atom::num(3)
                            * &two_two_thirds
                            * &sqrt_three
                            * &b__
                            * &rt_c)),
                    x_,
                ) - rubi_simp(
                    &(&q * third_arg.atan()
                        / (Atom::num(3)
                            * &two_two_thirds
                            * &sqrt_three
                            * &b__
                            * &rt_c)),
                    x_,
                ) - rubi_simp(
                    &(q * fourth_arg.atanh()
                        / (Atom::num(3) * two_two_thirds * b__ * rt_c)),
                    x_,
                )
        },
    ));
}

fn push_rules_rule_987(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 987,
        source: "Int[x_/((a_+b_.*x_^3)*Sqrt[c_+d_.*x_^3]),x_Symbol] :=
          With[{q=Rt[d/c,3]},
          -q*ArcTan[Sqrt[c+d*x^3]/Rt[-c,2]]/(9*2^(2/3)*b*Rt[-c,2]) -
          q*ArcTanh[Sqrt[c+d*x^3]/(Sqrt[3]*Rt[-c,2])]/(3*2^(2/3)*Sqrt[3]*b*Rt[-c,2]) -
          q*ArcTanh[Sqrt[3]*Rt[-c,2]*(1+2^(1/3)*q*x)/Sqrt[c+d*x^3]]/(3*2^(2/3)*Sqrt[3]*b*Rt[-c,2]) -
          q*ArcTan[Rt[-c,2]*(1-2^(1/3)*q*x)/Sqrt[c+d*x^3]]/(3*2^(2/3)*b*Rt[-c,2])] /;
        FreeQ[{a,b,c,d},x] && NeQ[b*c-a*d,0] && EqQ[4*b*c-a*d,0] && NegQ[c]",
        desc: "Algebraic expansion",
        refs: ["Goursat pseudo-elliptic integral"],
        pattern:  rubi_shared_pattern_10(symbols),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(Atom::num(4) * &b__ * &c__ - &a__ * &d__, 0)
                && negq!(c__)
        },
        rhs: {
            let q = rubi_rt(&(&d__ / &c__), 3);
            let rt_neg_c = rubi_rt(&(-&c__), 2);
            let sqrt_three = Atom::num(3).sqrt();
            let two_one_third = rubi_rt(&Atom::num(2), 3);
            let two_two_thirds = two_one_third.pow(2);
            let radical = (&c__ + &d__ * x_.pow(3)).sqrt();
            let first_arg = &radical / &rt_neg_c;
            let second_arg = &radical / (&sqrt_three * &rt_neg_c);
            let third_arg = &sqrt_three * &rt_neg_c * (Atom::num(1) + &two_one_third * &q * x_)
                / &radical;
            let fourth_arg = &rt_neg_c * (Atom::num(1) - &two_one_third * &q * x_) / radical;

            rubi_simp(
                    &(-&q * first_arg.atan()
                        / (Atom::num(9) * &two_two_thirds * &b__ * &rt_neg_c)),
                    x_,
                ) - rubi_simp(
                    &(&q * second_arg.atanh()
                        / (Atom::num(3)
                            * &two_two_thirds
                            * &sqrt_three
                            * &b__
                            * &rt_neg_c)),
                    x_,
                ) - rubi_simp(
                    &(&q * third_arg.atanh()
                        / (Atom::num(3)
                            * &two_two_thirds
                            * &sqrt_three
                            * &b__
                            * &rt_neg_c)),
                    x_,
                ) - rubi_simp(
                    &(q * fourth_arg.atan()
                        / (Atom::num(3) * two_two_thirds * b__ * rt_neg_c)),
                    x_,
                )
        },
    ));
}

fn push_rules_rule_988(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 988,
        source: "Int[x_/((a_+b_.*x_^3)*Sqrt[c_+d_.*x_^3]),x_Symbol] :=
          With[{q=Rt[d/c,3]},
          d*q/(4*b) \\[Star] Int[x^2/((8*c-d*x^3)*Sqrt[c+d*x^3]),x] -
          q^2/(12*b) \\[Star] Int[(1+q*x)/((2-q*x)*Sqrt[c+d*x^3]),x] +
          1/(12*b*c) \\[Star] Int[(2*c*q^2-2*d*x-d*q*x^2)/((4+2*q*x+q^2*x^2)*Sqrt[c+d*x^3]),x]] /;
        FreeQ[{a,b,c,d},x] && NeQ[b*c-a*d,0] && EqQ[8*b*c+a*d,0]",
        desc: "Algebraic expansion",
        refs: ["Goursat pseudo-elliptic integral"],
        pattern:  rubi_shared_pattern_10(symbols),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(Atom::num(8) * &b__ * &c__ + &a__ * &d__, 0)
        },
        rhs: {
            let q = rubi_rt(&(&d__ / &c__), 3);
            let radical = (&c__ + &d__ * x_.pow(3)).sqrt();
            let first_integrand =
                x_.pow(2) / ((Atom::num(8) * &c__ - &d__ * x_.pow(3)) * &radical);
            let second_integrand =
                (Atom::num(1) + &q * x_) / ((Atom::num(2) - &q * x_) * &radical);
            let third_integrand = (Atom::num(2) * &c__ * q.pow(2)
                - Atom::num(2) * &d__ * x_
                - &d__ * &q * x_.pow(2))
                / ((Atom::num(4) + Atom::num(2) * &q * x_ + q.pow(2) * x_.pow(2))
                    * radical);
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);
            let third = rubi_rhs_int(&third_integrand, x_);

            rubi_star(&d__ * &q / (Atom::num(4) * &b__), first)
                    - rubi_star(q.pow(2), second / (Atom::num(12) * &b__))
                    + rubi_star(Atom::num(1) / (Atom::num(12) * &b__ * &c__), third)
        },
    ));
}

fn push_rules_rule_989(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 989,
        source: "Int[x_/((c_+d_.*x_^3)*Sqrt[a_+b_.*x_^3]),x_Symbol] :=
          With[{q=Rt[b/a,3],r=Simplify[(b*c-10*a*d)/(6*a*d)]},
          -q*(2-r)*ArcTan[(1-r)*Sqrt[a+b*x^3]/(Sqrt[2]*Rt[a,2]*r^(3/2))]/(3*Sqrt[2]*Rt[a,2]*d*r^(3/2)) -
          q*(2-r)*ArcTan[Rt[a,2]*Sqrt[r]*(1+r)*(1+q*x)/(Sqrt[2]*Sqrt[a+b*x^3])]/(2*Sqrt[2]*Rt[a,2]*d*r^(3/2)) -
          q*(2-r)*ArcTanh[Rt[a,2]*(1-r)*Sqrt[r]*(1+q*x)/(Sqrt[2]*Sqrt[a+b*x^3])]/(6*Sqrt[2]*Rt[a,2]*d*Sqrt[r]) -
          q*(2-r)*ArcTanh[Rt[a,2]*Sqrt[r]*(1+r-2*q*x)/(Sqrt[2]*Sqrt[a+b*x^3])]/(3*Sqrt[2]*Rt[a,2]*d*Sqrt[r])] /;
        FreeQ[{a,b,c,d},x] && NeQ[b*c-a*d,0] && EqQ[b^2*c^2-20*a*b*c*d-8*a^2*d^2,0] && PosQ[a]",
        desc: "Apply the direct antiderivative formula.",
        refs: ["Goursat pseudo-elliptic integral"],
        pattern:  rubi_shared_pattern_11(symbols),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(
                    b__.pow(2) * c__.pow(2) - Atom::num(20) * &a__ * &b__ * &c__ * &d__ - Atom::num(8) * a__.pow(2) * d__.pow(2),
                    0
                )
                && posq!(a__)
        },
        rhs: {
            let q = rubi_rt(&(&b__ / &a__), 3);
            let r = rubi_simplify(
                &((&b__ * &c__ - Atom::num(10) * &a__ * &d__)
                    / (Atom::num(6) * &a__ * &d__)),
            );
            let rt_a = rubi_rt(&a__, 2);
            let sqrt_two = Atom::num(2).sqrt();
            let sqrt_r = r.sqrt();
            let r_three_halves = r.pow(Atom::num(3) / Atom::num(2));
            let radical = (&a__ + &b__ * x_.pow(3)).sqrt();
            let common = &q * (Atom::num(2) - &r);
            let first_arg = (Atom::num(1) - &r) * &radical / (&sqrt_two * &rt_a * &r_three_halves);
            let second_arg =
                &rt_a * &sqrt_r * (Atom::num(1) + &r) * (Atom::num(1) + &q * x_) / (&sqrt_two * &radical);
            let third_arg = &rt_a * (Atom::num(1) - &r) * &sqrt_r * (Atom::num(1) + &q * x_)
                / (&sqrt_two * &radical);
            let fourth_arg =
                &rt_a * &sqrt_r * (Atom::num(1) + &r - Atom::num(2) * &q * x_) / (&sqrt_two * radical);

            rubi_simp(
                    &(-&common * first_arg.atan()
                        / (Atom::num(3) * &sqrt_two * &rt_a * &d__ * &r_three_halves)),
                    x_,
                ) - rubi_simp(
                    &(&common * second_arg.atan()
                        / (Atom::num(2) * &sqrt_two * &rt_a * &d__ * &r_three_halves)),
                    x_,
                ) - rubi_simp(
                    &(&common * third_arg.atanh()
                        / (Atom::num(6) * &sqrt_two * &rt_a * &d__ * &sqrt_r)),
                    x_,
                ) - rubi_simp(
                    &(common * fourth_arg.atanh()
                        / (Atom::num(3) * sqrt_two * rt_a * d__ * sqrt_r)),
                    x_,
                )
        },
    ));
}

fn push_rules_rule_990(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 990,
        source: "Int[x_/((c_+d_.*x_^3)*Sqrt[a_+b_.*x_^3]),x_Symbol] :=
          With[{q=Rt[b/a,3],r=Simplify[(b*c-10*a*d)/(6*a*d)]},
          q*(2-r)*ArcTanh[(1-r)*Sqrt[a+b*x^3]/(Sqrt[2]*Rt[-a,2]*r^(3/2))]/(3*Sqrt[2]*Rt[-a,2]*d*r^(3/2)) -
          q*(2-r)*ArcTanh[Rt[-a,2]*Sqrt[r]*(1+r)*(1+q*x)/(Sqrt[2]*Sqrt[a+b*x^3])]/(2*Sqrt[2]*Rt[-a,2]*d*r^(3/2)) -
          q*(2-r)*ArcTan[Rt[-a,2]*(1-r)*Sqrt[r]*(1+q*x)/(Sqrt[2]*Sqrt[a+b*x^3])]/(6*Sqrt[2]*Rt[-a,2]*d*Sqrt[r]) -
          q*(2-r)*ArcTan[Rt[-a,2]*Sqrt[r]*(1+r-2*q*x)/(Sqrt[2]*Sqrt[a+b*x^3])]/(3*Sqrt[2]*Rt[-a,2]*d*Sqrt[r])] /;
        FreeQ[{a,b,c,d},x] && NeQ[b*c-a*d,0] && EqQ[b^2*c^2-20*a*b*c*d-8*a^2*d^2,0] && NegQ[a]",
        desc: "Apply the direct antiderivative formula.",
        refs: ["Goursat pseudo-elliptic integral"],
        pattern:  rubi_shared_pattern_11(symbols),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(
                    b__.pow(2) * c__.pow(2) - Atom::num(20) * &a__ * &b__ * &c__ * &d__ - Atom::num(8) * a__.pow(2) * d__.pow(2),
                    0
                )
                && negq!(a__)
        },
        rhs: {
            let q = rubi_rt(&(&b__ / &a__), 3);
            let r = rubi_simplify(
                &((&b__ * &c__ - Atom::num(10) * &a__ * &d__)
                    / (Atom::num(6) * &a__ * &d__)),
            );
            let rt_neg_a = rubi_rt(&(-&a__), 2);
            let sqrt_two = Atom::num(2).sqrt();
            let sqrt_r = r.sqrt();
            let r_three_halves = r.pow(Atom::num(3) / Atom::num(2));
            let radical = (&a__ + &b__ * x_.pow(3)).sqrt();
            let common = &q * (Atom::num(2) - &r);
            let first_arg = (Atom::num(1) - &r) * &radical / (&sqrt_two * &rt_neg_a * &r_three_halves);
            let second_arg = &rt_neg_a * &sqrt_r * (Atom::num(1) + &r) * (Atom::num(1) + &q * x_)
                / (&sqrt_two * &radical);
            let third_arg =
                &rt_neg_a * (Atom::num(1) - &r) * &sqrt_r * (Atom::num(1) + &q * x_)
                    / (&sqrt_two * &radical);
            let fourth_arg =
                &rt_neg_a * &sqrt_r * (Atom::num(1) + &r - Atom::num(2) * &q * x_) / (&sqrt_two * radical);

            rubi_simp(
                    &(&common * first_arg.atanh()
                        / (Atom::num(3)
                            * &sqrt_two
                            * &rt_neg_a
                            * &d__
                            * &r_three_halves)),
                    x_,
                ) - rubi_simp(
                    &(&common * second_arg.atanh()
                        / (Atom::num(2)
                            * &sqrt_two
                            * &rt_neg_a
                            * &d__
                            * &r_three_halves)),
                    x_,
                ) - rubi_simp(
                    &(&common * third_arg.atan()
                        / (Atom::num(6) * &sqrt_two * &rt_neg_a * &d__ * &sqrt_r)),
                    x_,
                ) - rubi_simp(
                    &(common * fourth_arg.atan()
                        / (Atom::num(3) * sqrt_two * rt_neg_a * d__ * sqrt_r)),
                    x_,
                )
        },
    ));
}

fn push_rules_rule_991(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 991,
        source: "Int[x_/((a_+b_.*x_^3)^(1/3)*(c_+d_.*x_^3)),x_Symbol] :=
          With[{q=Rt[b/a,3]},
          -q^2/(3*d) \\[Star] Int[1/((1-q*x)*(a+b*x^3)^(1/3)),x] +
          q/d \\[Star] Subst[Int[1/(1+2*a*x^3),x],x,(1+q*x)/(a+b*x^3)^(1/3)]] /;
        FreeQ[{a,b,c,d},x] && NeQ[b*c-a*d,0] && EqQ[b*c+a*d,0]",
        desc: "Algebraic expansion and integration by substitution",
        refs: [],
        pattern: x_ / ((a__ + b__ * x_.pow(3)).pow(Atom::num(1) / Atom::num(3)) * (c__ + d__ * x_.pow(3))),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(&b__ * &c__ + &a__ * &d__, 0)
        },
        rhs: {
            let q = rubi_rt(&(&b__ / &a__), 3);
            let base = &a__ + &b__ * x_.pow(3);
            let radical = base.pow(Atom::num(1) / Atom::num(3));
            let recursive_integrand =
                Atom::num(1) / ((Atom::num(1) - &q * x_) * &radical);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = Atom::num(1) / (Atom::num(1) + Atom::num(2) * &a__ * sub_atom.pow(3));
            let transformed = rubi_rhs_int(&transformed_integrand, sub);
            let replacement = (Atom::num(1) + &q * x_) / radical;
            let substituted = rubi_subst(&transformed, sub, replacement);

            rubi_star(-q.pow(2), recursive / (Atom::num(3) * &d__))
                    + rubi_star(q, substituted / d__)
        },
    ));
}

fn push_rules_rule_992(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 992,
        source: "Int[x_/((a_+b_.*x_^3)^(2/3)*(c_+d_.*x_^3)),x_Symbol] :=
          With[{q=Rt[(b*c-a*d)/c,3]},
          -ArcTan[(1+(2*q*x)/(a+b*x^3)^(1/3))/Sqrt[3]]/(Sqrt[3]*c*q^2) + Log[c+d*x^3]/(6*c*q^2) - Log[q*x-(a+b*x^3)^(1/3)]/(2*c*q^2)] /;
        FreeQ[{a,b,c,d},x] && NeQ[b*c-a*d,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: x_ / ((a__ + b__ * x_.pow(3)).pow(Atom::num(2) / Atom::num(3)) * (c__ + d__ * x_.pow(3))),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
        },
        rhs: {
            let q = rubi_rt(&((&b__ * &c__ - &a__ * &d__) / &c__), 3);
            let q_squared = q.pow(2);
            let base = &a__ + &b__ * x_.pow(3);
            let radical = base.pow(Atom::num(1) / Atom::num(3));
            let sqrt_three = Atom::num(3).sqrt();
            let atan_arg = (Atom::num(1) + Atom::num(2) * &q * x_ / &radical) / &sqrt_three;

            rubi_simp(
                    &(-atan_arg.atan() / (&sqrt_three * &c__ * &q_squared)),
                    x_,
                ) - rubi_simp(
                    &((&q * x_ - &radical).log()
                        / (Atom::num(2) * &c__ * &q_squared)),
                    x_,
                ) + rubi_simp(
                    &((&c__ + &d__ * x_.pow(3)).log()
                        / (Atom::num(6) * &c__ * q_squared)),
                    x_,
                )
        },
    ));
}

fn push_rules_rule_993(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 993,
        source: "Int[x_^2/((a_+b_.*x_^4)*Sqrt[c_+d_.*x_^4]),x_Symbol] :=
          With[{r=Numerator[Rt[-a/b,2]], s=Denominator[Rt[-a/b,2]]},
          s/(2*b) \\[Star] Int[1/((r+s*x^2)*Sqrt[c+d*x^4]),x] - s/(2*b) \\[Star] Int[1/((r-s*x^2)*Sqrt[c+d*x^4]),x]] /;
        FreeQ[{a,b,c,d},x] && NeQ[b*c-a*d,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: x_.pow(2) / ((a__ + b__ * x_.pow(4)) * (c__ + d__ * x_.pow(4)).sqrt()),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
        },
        rhs: {
            let root = rubi_rt(&(-&a__ / &b__), 2);
            let r = rubi_numerator(&root);
            let s = rubi_denominator_atom(&root);
            let radical = (&c__ + &d__ * x_.pow(4)).sqrt();
            let first_integrand = Atom::num(1) / ((&r + &s * x_.pow(2)) * &radical);
            let second_integrand = Atom::num(1) / ((&r - &s * x_.pow(2)) * radical);
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(&s, first / (Atom::num(2) * &b__))
                    - rubi_star(s, second / (Atom::num(2) * b__))
        },
    ));
}

fn push_rules_rule_994(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 994,
        source: "Int[x_^2*Sqrt[c_+d_.*x_^4]/(a_+b_.*x_^4),x_Symbol] :=
          d/b \\[Star] Int[x^2/Sqrt[c+d*x^4],x] + (b*c-a*d)/b \\[Star] Int[x^2/((a+b*x^4)*Sqrt[c+d*x^4]),x] /;
        FreeQ[{a,b,c,d},x] && NeQ[b*c-a*d,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: x_.pow(2) * (c__ + d__ * x_.pow(4)).sqrt() / (a__ + b__ * x_.pow(4)),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
        },
        rhs: {
            let det = &b__ * &c__ - &a__ * &d__;
            let first_base = &a__ + &b__ * x_.pow(4);
            let second_base = &c__ + &d__ * x_.pow(4);
            let first_integrand = x_.pow(2) / second_base.sqrt();
            let second_integrand = x_.pow(2) / (first_base * second_base.sqrt());
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(d__, first / &b__)
                    + rubi_star(det, second / b__)
        },
    ));
}

fn push_rules_rule_995(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 995,
        source: "Int[x_^4/(Sqrt[a_+b_.*x_^4]*Sqrt[c_+d_.*x_^4]),x_Symbol] :=
          1/b \\[Star] Int[Sqrt[a+b*x^4]/Sqrt[c+d*x^4],x] - a/b \\[Star] Int[1/(Sqrt[a+b*x^4]*Sqrt[c+d*x^4]),x] /;
        FreeQ[{a,b,c,d},x] && NeQ[b*c-a*d,0]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern: x_.pow(4) / ((a__ + b__ * x_.pow(4)).sqrt() * (c__ + d__ * x_.pow(4)).sqrt()),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
        },
        rhs: {
            let first_base = &a__ + &b__ * x_.pow(4);
            let second_base = &c__ + &d__ * x_.pow(4);
            let first_integrand = first_base.sqrt() / second_base.sqrt();
            let second_integrand = Atom::num(1) / (first_base.sqrt() * second_base.sqrt());
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(Atom::num(1) / &b__, first)
                    - rubi_star(a__, second / b__)
        },
    ));
}

fn push_rules_rule_996(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 996,
        source: "Int[x_^m_.*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_.,x_Symbol] :=
          With[{k=Denominator[p]},
          k*a^(p+(m+1)/n)/n \\[Star]
            Subst[Int[x^(k*(m+1)/n-1)*(c-(b*c-a*d)*x^k)^q/(1-b*x^k)^(p+q+(m+1)/n+1),x],x,x^(n/k)/(a+b*x^n)^(1/k)]] /;
        FreeQ[{a,b,c,d},x] && IGtQ[n,0] && RationalQ[m,p] && IntegersQ[p+(m+1)/n,q] && LtQ[-1,p,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [a__, b__, c__, d__, m_, n_, p_, q_, x_],
        optional: [b__, d__, m_, q_],
        when: {
            let exponent_sum = &p_ + (&m_ + Atom::num(1)) / &n_;
            freeq!([a__, b__, c__, d__], x_)
                && igtq!(n_, 0)
                && rationalq!([m_, p_])
                && integersq!([exponent_sum, q_])
                && ltq!(-1, p_, 0)
        },
        rhs: {
            let k_i64 = rubi_denominator(&p_).rubi_rhs();
            let k = Atom::num(k_i64);
            let exponent_sum = &p_ + (&m_ + Atom::num(1)) / &n_;
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = sub_atom.pow(&k * (&m_ + Atom::num(1)) / &n_ - Atom::num(1))
                * (&c__ - (&b__ * &c__ - &a__ * &d__) * sub_atom.pow(&k)).pow(&q_)
                / (Atom::num(1) - &b__ * sub_atom.pow(&k)).pow(&p_ + &q_ + (&m_ + Atom::num(1)) / &n_ + Atom::num(1));
            let transformed = rubi_rhs_int(&transformed_integrand, sub);
            let replacement =
                x_.pow(&n_ / &k) / (&a__ + &b__ * x_.pow(&n_)).pow(Atom::num(1) / &k);
            let substituted = rubi_subst(&transformed, sub, replacement);

            rubi_star(k * a__.pow(exponent_sum) / n_, substituted)
        },
    ));
}

fn push_rules_rule_997(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 997,
        source: "Int[x_^m_.*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
          -Subst[Int[(a+b*x^(-n))^p*(c+d*x^(-n))^q/x^(m+2),x],x,1/x] /;
        FreeQ[{a,b,c,d,p,q},x] && NeQ[b*c-a*d,0] && ILtQ[n,0] && IntegerQ[m]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [a__, b__, c__, d__, m_, n_, p_, q_, x_],
        optional: [b__, d__, m_],
        when: {
            freeq!([a__, b__, c__, d__, p_, q_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && iltq!(n_, 0)
                && integerq!(m_)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = (&a__ + &b__ * sub_atom.pow(-&n_)).pow(&p_)
                * (&c__ + &d__ * sub_atom.pow(-&n_)).pow(&q_)
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

fn push_rules_rule_998(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 998,
        source: "Int[(e_.*x_)^m_*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
          With[{g=Denominator[m]},
          -g/e \\[Star] Subst[Int[(a+b*e^(-n)*x^(-g*n))^p*(c+d*e^(-n)*x^(-g*n))^q/x^(g*(m+1)+1),x],x,1/(e*x)^(1/g)]] /;
        FreeQ[{a,b,c,d,e,p,q},x] && ILtQ[n,0] && FractionQ[m]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, p_, q_, x_],
        optional: [b__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__, p_, q_], x_)
                && iltq!(n_, 0)
                && fractionq!(m_)
        },
        rhs: {
            let g_i64 = rubi_denominator(&m_).rubi_rhs();
            let g = Atom::num(g_i64);
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_power = (-&g * &n_).expand();
            let transformed_integrand = (&a__ + &b__ * e__.pow(-&n_) * sub_atom.pow(&transformed_power)).pow(&p_)
                * (&c__ + &d__ * e__.pow(-&n_) * sub_atom.pow(&transformed_power)).pow(&q_)
                / sub_atom.pow(&g * (&m_ + Atom::num(1)) + Atom::num(1));
            let transformed = rubi_rhs_int(&transformed_integrand, sub);
            let replacement = Atom::num(1) / (&e__ * x_).pow(Atom::num(1) / &g);
            let substituted = rubi_subst(&transformed, sub, replacement);

            rubi_star(-&g, substituted / e__)
        },
    ));
}

fn push_rules_rule_999(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 999,
        source: "Int[(e_.*x_)^m_*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
          -(e*x)^m*(x^(-1))^m \\[Star] Subst[Int[(a+b*x^(-n))^p*(c+d*x^(-n))^q/x^(m+2),x],x,1/x] /;
        FreeQ[{a,b,c,d,e,m,p,q},x] && NeQ[b*c-a*d,0] && ILtQ[n,0] && Not[RationalQ[m]]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, p_, q_, x_],
        optional: [b__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, p_, q_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && iltq!(n_, 0)
                && !rationalq!(m_)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = (&a__ + &b__ * sub_atom.pow(-&n_)).pow(&p_)
                * (&c__ + &d__ * sub_atom.pow(-&n_)).pow(&q_)
                / sub_atom.pow(&m_ + Atom::num(2));
            let transformed = rubi_rhs_int(&transformed_integrand, sub);
            let substituted = rubi_subst(&transformed, sub, Atom::num(1) / x_);

            rubi_star(-(&e__ * x_).pow(&m_) * x_.pow(-Atom::num(1)).pow(&m_), substituted)
        },
    ));
}

fn push_rules_rule_1000(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1000,
        source: "Int[x_^m_.*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
          With[{g=Denominator[n]},
          g \\[Star] Subst[Int[x^(g*(m+1)-1)*(a+b*x^(g*n))^p*(c+d*x^(g*n))^q,x],x,x^(1/g)]] /;
        FreeQ[{a,b,c,d,m,p,q},x] && NeQ[b*c-a*d,0] && FractionQ[n]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [a__, b__, c__, d__, m_, n_, p_, q_, x_],
        optional: [b__, d__, m_],
        when: {
            freeq!([a__, b__, c__, d__, m_, p_, q_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && fractionq!(n_)
        },
        rhs: {
            let g_i64 = rubi_denominator(&n_).rubi_rhs();
            let g = Atom::num(g_i64);
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_power = (&g * &n_).expand();
            let transformed_integrand = sub_atom.pow(&g * (&m_ + Atom::num(1)) - Atom::num(1))
                * (&a__ + &b__ * sub_atom.pow(&transformed_power)).pow(&p_)
                * (&c__ + &d__ * sub_atom.pow(&transformed_power)).pow(&q_);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);
            let substituted = rubi_subst(
                &transformed,
                sub,
                x_.pow(Atom::num(1) / &g),
            );

            rubi_star(g, substituted)
        },
    ));
}

fn push_rules_rule_1001(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1001,
        source: "Int[(e_*x_)^m_*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
          e^IntPart[m]*(e*x)^FracPart[m]/x^FracPart[m] \\[Star] Int[x^m*(a+b*x^n)^p*(c+d*x^n)^q,x] /;
        FreeQ[{a,b,c,d,e,m,p,q},x] && NeQ[b*c-a*d,0] && FractionQ[n]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, p_, q_, x_],
        optional: [b__, d__],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, p_, q_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && fractionq!(n_)
        },
        rhs: {
            let frac_m = rubi_frac_part(&m_);
            let recursive_integrand = x_.pow(&m_)
                * (&a__ + &b__ * x_.pow(&n_)).pow(&p_)
                * (&c__ + &d__ * x_.pow(&n_)).pow(&q_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(e__.pow(rubi_int_part(&m_)) * (&e__ * x_).pow(&frac_m) / x_.pow(frac_m), recursive)
        },
    ));
}

fn push_rules_rule_1002(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1002,
        source: "Int[x_^m_.*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
          1/(m+1) \\[Star] Subst[Int[(a+b*x^Simplify[n/(m+1)])^p*(c+d*x^Simplify[n/(m+1)])^q,x],x,x^(m+1)] /;
        FreeQ[{a,b,c,d,m,n,p,q},x] && NeQ[b*c-a*d,0] && IntegerQ[Simplify[n/(m+1)]] && Not[IntegerQ[n]]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [a__, b__, c__, d__, m_, n_, p_, q_, x_],
        optional: [b__, d__, m_],
        when: {
            freeq!([a__, b__, c__, d__, m_, n_, p_, q_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && rubi_simplified_quotient(&n_, &(&m_ + Atom::num(1)))
                    .is_some_and(|quotient| integerq!(quotient))
                && !integerq!(n_)
        },
        rhs: {
            let quotient = rubi_simplified_quotient(&n_, &(&m_ + Atom::num(1))).rubi_rhs();

            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = (&a__ + &b__ * sub_atom.pow(&quotient)).pow(&p_)
                * (&c__ + &d__ * sub_atom.pow(quotient)).pow(&q_);
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

fn push_rules_rule_1003(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1003,
        source: "Int[(e_*x_)^m_.*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
          e^IntPart[m]*(e*x)^FracPart[m]/x^FracPart[m] \\[Star] Int[x^m*(a+b*x^n)^p*(c+d*x^n)^q,x] /;
        FreeQ[{a,b,c,d,e,m,n,p,q},x] && NeQ[b*c-a*d,0] && IntegerQ[Simplify[n/(m+1)]] && Not[IntegerQ[n]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, p_, q_, x_],
        optional: [b__, d__, m_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_, p_, q_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && rubi_simplified_quotient(&n_, &(&m_ + Atom::num(1)))
                    .is_some_and(|quotient| integerq!(quotient))
                && !integerq!(n_)
        },
        rhs: {
            let frac_m = rubi_frac_part(&m_);
            let recursive_integrand = x_.pow(&m_)
                * (&a__ + &b__ * x_.pow(&n_)).pow(&p_)
                * (&c__ + &d__ * x_.pow(&n_)).pow(&q_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(e__.pow(rubi_int_part(&m_)) * (&e__ * x_).pow(&frac_m) / x_.pow(frac_m), recursive)
        },
    ));
}

fn push_rules_rule_1004(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1004,
        source: "Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
          -(c*b-a*d)*(e*x)^(m+1)*(a+b*x^n)^(p+1)*(c+d*x^n)^(q-1)/(a*b*e*n*(p+1)) +
          1/(a*b*n*(p+1)) \\[Star] Int[(e*x)^m*(a+b*x^n)^(p+1)*(c+d*x^n)^(q-2)*
            Simp[c*(c*b*n*(p+1)+(c*b-a*d)*(m+1))+d*(c*b*n*(p+1)+(c*b-a*d)*(m+n*(q-1)+1))*x^n,x],x] /;
        FreeQ[{a,b,c,d,e,m,n},x] && NeQ[b*c-a*d,0] && LtQ[p,-1] && GtQ[q,1] && IntBinomialQ[a,b,c,d,e,m,n,p,q,x]",
        desc: "Binomial product recurrence 1 with A=c, B=d and q=q-1",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, p_, q_, x_],
        optional: [b__, d__, e__, m_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && ltq!(p_, -1)
                && gtq!(q_, 1)
                && rubi_int_binomial_scaled_q(
                    &a__, &b__, &c__, &d__, &e__, &m_, &n_, &p_, &q_, x_,
                )
        },
        rhs: {
            let reverse_det = &c__ * &b__ - &a__ * &d__;
            let first_base = &a__ + &b__ * x_.pow(&n_);
            let second_base = &c__ + &d__ * x_.pow(&n_);
            let direct = -&reverse_det
                * (&e__ * x_).pow(&m_ + Atom::num(1))
                * first_base.pow(&p_ + Atom::num(1))
                * second_base.pow(&q_ - Atom::num(1))
                / (&a__ * &b__ * &e__ * &n_ * (&p_ + Atom::num(1)));
            let payload = simp!(
                &c__ * (&c__ * &b__ * &n_ * (&p_ + Atom::num(1)) + &reverse_det * (&m_ + Atom::num(1)))
                    + &d__ * (&c__ * &b__ * &n_ * (&p_ + Atom::num(1))
                        + &reverse_det * (&m_ + &n_ * (&q_ - Atom::num(1)) + Atom::num(1)))
                        * x_.pow(&n_),
                x_
            );
            let recursive_integrand = (&e__ * x_).pow(&m_)
                * first_base.pow(&p_ + Atom::num(1))
                * second_base.pow(&q_ - Atom::num(2))
                * payload;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&direct, x_)
                    + rubi_star(Atom::num(1) / (&a__ * &b__ * &n_ * (&p_ + Atom::num(1))), recursive)
        },
    ));
}

fn push_rules_rule_1005(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1005,
        source: "Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
          -(e*x)^(m+1)*(a+b*x^n)^(p+1)*(c+d*x^n)^q/(a*e*n*(p+1)) +
          1/(a*n*(p+1)) \\[Star] Int[(e*x)^m*(a+b*x^n)^(p+1)*(c+d*x^n)^(q-1)*Simp[c*(m+n*(p+1)+1)+d*(m+n*(p+q+1)+1)*x^n,x],x] /;
        FreeQ[{a,b,c,d,e,m,n},x] && NeQ[b*c-a*d,0] && LtQ[p,-1] && LtQ[0,q,1] && IntBinomialQ[a,b,c,d,e,m,n,p,q,x]",
        desc: "Binomial product recurrence 3b with A=c, B=d and q=q-1",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, p_, q_, x_],
        optional: [b__, d__, e__, m_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && ltq!(p_, -1)
                && ltq!(0, q_, 1)
                && rubi_int_binomial_scaled_q(
                    &a__, &b__, &c__, &d__, &e__, &m_, &n_, &p_, &q_, x_,
                )
        },
        rhs: {
            let first_base = &a__ + &b__ * x_.pow(&n_);
            let second_base = &c__ + &d__ * x_.pow(&n_);
            let direct = -(&e__ * x_).pow(&m_ + Atom::num(1))
                * first_base.pow(&p_ + Atom::num(1))
                * second_base.pow(&q_)
                / (&a__ * &e__ * &n_ * (&p_ + Atom::num(1)));
            let payload = simp!(
                &c__ * (&m_ + &n_ * (&p_ + Atom::num(1)) + Atom::num(1))
                    + &d__ * (&m_ + &n_ * (&p_ + &q_ + Atom::num(1)) + Atom::num(1)) * x_.pow(&n_),
                x_
            );
            let recursive_integrand = (&e__ * x_).pow(&m_)
                * first_base.pow(&p_ + Atom::num(1))
                * second_base.pow(&q_ - Atom::num(1))
                * payload;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&direct, x_)
                    + rubi_star(Atom::num(1) / (&a__ * &n_ * (&p_ + Atom::num(1))), recursive)
        },
    ));
}

fn push_rules_rule_1006(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1006,
        source: "Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
          -b*(e*x)^(m+1)*(a+b*x^n)^(p+1)*(c+d*x^n)^(q+1)/(a*e*n*(b*c-a*d)*(p+1)) +
          1/(a*n*(b*c-a*d)*(p+1)) \\[Star]
            Int[(e*x)^m*(a+b*x^n)^(p+1)*(c+d*x^n)^q*Simp[c*b*(m+1)+n*(b*c-a*d)*(p+1)+d*b*(m+n*(p+q+2)+1)*x^n,x],x] /;
        FreeQ[{a,b,c,d,e,m,n,q},x] && NeQ[b*c-a*d,0] && LtQ[p,-1] && IntBinomialQ[a,b,c,d,e,m,n,p,q,x]",
        desc: "Binomial product recurrence 3b with A=1 and B=0",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, p_, q_, x_],
        optional: [b__, d__, e__, m_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_, q_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && ltq!(p_, -1)
                && rubi_int_binomial_scaled_q(
                    &a__, &b__, &c__, &d__, &e__, &m_, &n_, &p_, &q_, x_,
                )
        },
        rhs: {
            let det = &b__ * &c__ - &a__ * &d__;
            let first_base = &a__ + &b__ * x_.pow(&n_);
            let second_base = &c__ + &d__ * x_.pow(&n_);
            let direct = -&b__
                * (&e__ * x_).pow(&m_ + Atom::num(1))
                * first_base.pow(&p_ + Atom::num(1))
                * second_base.pow(&q_ + Atom::num(1))
                / (&a__ * &e__ * &n_ * &det * (&p_ + Atom::num(1)));
            let payload = simp!(
                &c__ * &b__ * (&m_ + Atom::num(1))
                    + &n_ * &det * (&p_ + Atom::num(1))
                    + &d__ * &b__ * (&m_ + &n_ * (&p_ + &q_ + Atom::num(2)) + Atom::num(1)) * x_.pow(&n_),
                x_
            );
            let recursive_integrand = (&e__ * x_).pow(&m_)
                * first_base.pow(&p_ + Atom::num(1))
                * second_base.pow(&q_)
                * payload;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&direct, x_)
                    + rubi_star(Atom::num(1) / (&a__ * &n_ * det * (&p_ + Atom::num(1))), recursive)
        },
    ));
}

fn push_rules_rule_1007(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1007,
        source: "Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
          (e*x)^(m+1)*(a+b*x^n)^p*(c+d*x^n)^q/(e*(m+n*(p+q)+1)) +
          n/(m+n*(p+q)+1) \\[Star] Int[(e*x)^m*(a+b*x^n)^(p-1)*(c+d*x^n)^(q-1)*Simp[a*c*(p+q)+(q*(b*c-a*d)+a*d*(p+q))*x^n,x],x] /;
        FreeQ[{a,b,c,d,e,m,n},x] && NeQ[b*c-a*d,0] && GtQ[q,0] && GtQ[p,0] && IntBinomialQ[a,b,c,d,e,m,n,p,q,x]",
        desc: "Binomial product recurrence 2b with A=a, B=b and p=p-1",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, p_, q_, x_],
        optional: [b__, d__, e__, m_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && gtq!(q_, 0)
                && gtq!(p_, 0)
                && rubi_int_binomial_scaled_q(
                    &a__, &b__, &c__, &d__, &e__, &m_, &n_, &p_, &q_, x_,
                )
        },
        rhs: {
            let det = &b__ * &c__ - &a__ * &d__;
            let first_base = &a__ + &b__ * x_.pow(&n_);
            let second_base = &c__ + &d__ * x_.pow(&n_);
            let denominator = &m_ + &n_ * (&p_ + &q_) + Atom::num(1);
            let direct = (&e__ * x_).pow(&m_ + Atom::num(1))
                * first_base.pow(&p_)
                * second_base.pow(&q_)
                / (&e__ * &denominator);
            let payload = simp!(
                &a__ * &c__ * (&p_ + &q_) + (&q_ * &det + &a__ * &d__ * (&p_ + &q_)) * x_.pow(&n_),
                x_
            );
            let recursive_integrand = (&e__ * x_).pow(&m_)
                * first_base.pow(&p_ - Atom::num(1))
                * second_base.pow(&q_ - Atom::num(1))
                * payload;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&direct, x_)
                    + rubi_star(n_, recursive / denominator)
        },
    ));
}

fn push_rules_rule_1008(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1008,
        source: "Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
          d*(e*x)^(m+1)*(a+b*x^n)^(p+1)*(c+d*x^n)^(q-1)/(b*e*(m+n*(p+q)+1)) +
          1/(b*(m+n*(p+q)+1)) \\[Star] Int[(e*x)^m*(a+b*x^n)^p*(c+d*x^n)^(q-2)*
            Simp[c*((c*b-a*d)*(m+1)+c*b*n*(p+q))+(d*(c*b-a*d)*(m+1)+d*n*(q-1)*(b*c-a*d)+c*b*d*n*(p+q))*x^n,x],x] /;
        FreeQ[{a,b,c,d,e,m,n,p},x] && NeQ[b*c-a*d,0] && GtQ[q,1] && IntBinomialQ[a,b,c,d,e,m,n,p,q,x]",
        desc: "Binomial product recurrence 2b with A=c, B=d and q=q-1",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, p_, q_, x_],
        optional: [b__, d__, e__, m_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_, p_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && gtq!(q_, 1)
                && rubi_int_binomial_scaled_q(
                    &a__, &b__, &c__, &d__, &e__, &m_, &n_, &p_, &q_, x_,
                )
        },
        rhs: {
            let det = &b__ * &c__ - &a__ * &d__;
            let reverse_det = &c__ * &b__ - &a__ * &d__;
            let first_base = &a__ + &b__ * x_.pow(&n_);
            let second_base = &c__ + &d__ * x_.pow(&n_);
            let denominator = &m_ + &n_ * (&p_ + &q_) + Atom::num(1);
            let direct = &d__
                * (&e__ * x_).pow(&m_ + Atom::num(1))
                * first_base.pow(&p_ + Atom::num(1))
                * second_base.pow(&q_ - Atom::num(1))
                / (&b__ * &e__ * &denominator);
            let payload = simp!(
                &c__ * (&reverse_det * (&m_ + Atom::num(1)) + &c__ * &b__ * &n_ * (&p_ + &q_))
                    + (&d__ * &reverse_det * (&m_ + Atom::num(1))
                        + &d__ * &n_ * (&q_ - Atom::num(1)) * &det
                        + &c__ * &b__ * &d__ * &n_ * (&p_ + &q_))
                        * x_.pow(&n_),
                x_
            );
            let recursive_integrand = (&e__ * x_).pow(&m_)
                * first_base.pow(&p_)
                * second_base.pow(&q_ - Atom::num(2))
                * payload;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&direct, x_)
                    + rubi_star(Atom::num(1) / (&b__ * denominator), recursive)
        },
    ));
}

fn push_rules_rule_1009(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 1009,
        source: "Int[x_^m_/((a_+b_.*x_^n_)*(c_+d_.*x_^n_)),x_Symbol] :=
          -a/(b*c-a*d) \\[Star] Int[x^(m-n)/(a+b*x^n),x] + c/(b*c-a*d) \\[Star] Int[x^(m-n)/(c+d*x^n),x] /;
        FreeQ[{a,b,c,d,m,n},x] && NeQ[b*c-a*d,0] && (EqQ[m,n] || EqQ[m,2*n-1])",
        desc: "Algebraic expansion",
        refs: [],
        pattern: x_.pow(m_) / ((a__ + b__ * x_.pow(n_)) * (c__ + d__ * x_.pow(n_))),
        with: [a__, b__, c__, d__, m_, n_, x_],
        optional: [b__, d__],
        when: {
            freeq!([a__, b__, c__, d__, m_, n_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && (eqq!(m_, n_) || eqq!(m_, Atom::num(2) * &n_ - Atom::num(1)))
        },
        rhs: {
            let det = &b__ * &c__ - &a__ * &d__;
            let first_integrand = x_.pow(&m_ - &n_) / (&a__ + &b__ * x_.pow(&n_));
            let second_integrand = x_.pow(&m_ - &n_) / (&c__ + &d__ * x_.pow(&n_));
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(-&a__, first / &det)
                    + rubi_star(c__, second / det)
        },
    ));
}

fn push_rules_rule_1010(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 1010,
        source: "Int[(e_.*x_)^m_./((a_+b_.*x_^n_)*(c_+d_.*x_^n_)),x_Symbol] :=
          b/(b*c-a*d) \\[Star] Int[(e*x)^m/(a+b*x^n),x] - d/(b*c-a*d) \\[Star] Int[(e*x)^m/(c+d*x^n),x] /;
        FreeQ[{a,b,c,d,e,n,m},x] && NeQ[b*c-a*d,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, x_],
        optional: [b__, d__, e__, m_],
        when: {
            freeq!([a__, b__, c__, d__, e__, n_, m_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
        },
        rhs: {
            let det = &b__ * &c__ - &a__ * &d__;
            let first_integrand = (&e__ * x_).pow(&m_) / (&a__ + &b__ * x_.pow(&n_));
            let second_integrand = (&e__ * x_).pow(&m_) / (&c__ + &d__ * x_.pow(&n_));
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(b__, first / &det)
                    - rubi_star(d__, second / det)
        },
    ));
}

fn push_rules_rule_1011(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1011,
        source: "Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
          Int[ExpandIntegrand[(e*x)^m*(a+b*x^n)^p*(c+d*x^n)^q,x],x] /;
        FreeQ[{a,b,c,d,e,m},x] && NeQ[b*c-a*d,0] && IGtQ[p,-2] && (IGtQ[q,-2] || EqQ[q,-3] && IntegerQ[(m-1)/2])",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, p_, q_, x_],
        optional: [b__, d__, e__, m_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && igtq!(p_, -2)
                && (igtq!(q_, -2) || eqq!(q_, -3) && integerq!((&m_ - Atom::num(1)) / Atom::num(2)))
        },
        rhs: {
            let integrand = (&e__ * x_).pow(&m_)
                * (&a__ + &b__ * x_.pow(&n_)).pow(&p_)
                * (&c__ + &d__ * x_.pow(&n_)).pow(&q_);
            let expanded = rubi_expand_integrand(&integrand, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_1012(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1012,
        source: "Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
          a^p*c^q*(e*x)^(m+1)/(e*(m+1))*AppellF1[(m+1)/n,-p,-q,1+(m+1)/n,-b*x^n/a,-d*x^n/c] /;
        FreeQ[{a,b,c,d,e,m,n,p,q},x] && NeQ[b*c-a*d,0] && NeQ[m,-1] && NeQ[m,n-1] &&
          (IntegerQ[p] || GtQ[a,0]) && (IntegerQ[q] || GtQ[c,0])",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, p_, q_, x_],
        optional: [b__, d__, e__, m_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_, p_, q_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && neq!(m_, -1)
                && neq!(m_, &n_ - Atom::num(1))
                && (integerq!(p_) || gtq!(a__, 0))
                && (integerq!(q_) || gtq!(c__, 0))
        },
        rhs: {
            let quotient = (&m_ + Atom::num(1)) / &n_;
            let monomial = x_.pow(&n_);

            rubi_simp(
                &(a__.pow(&p_)
                    * c__.pow(&q_)
                    * (&e__ * x_).pow(&m_ + Atom::num(1))
                    * rubi_appell_f1(
                        &quotient,
                        -&p_,
                        -&q_,
                        Atom::num(1) + &quotient,
                        -&b__ * &monomial / &a__,
                        -&d__ * monomial / &c__,
                    )
                    / (&e__ * (&m_ + Atom::num(1)))),
                x_,
            )
        },
    ));
}

fn push_rules_rule_1013(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1013,
        source: "Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
          a^IntPart[p]*(a+b*x^n)^FracPart[p]/(1+b*x^n/a)^FracPart[p] \\[Star] Int[(e*x)^m*(1+b*x^n/a)^p*(c+d*x^n)^q,x] /;
        FreeQ[{a,b,c,d,e,m,n,p,q},x] && NeQ[b*c-a*d,0] && NeQ[m,-1] && NeQ[m,n-1] && Not[IntegerQ[p] || GtQ[a,0]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, m_, n_, p_, q_, x_],
        optional: [b__, d__, e__, m_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_, p_, q_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && neq!(m_, -1)
                && neq!(m_, &n_ - Atom::num(1))
                && !(integerq!(p_) || gtq!(a__, 0))
        },
        rhs: {
            let monomial = x_.pow(&n_);
            let frac_p = rubi_frac_part(&p_);
            let recursive_integrand = (&e__ * x_).pow(&m_)
                * (Atom::num(1) + &b__ * &monomial / &a__).pow(&p_)
                * (&c__ + &d__ * monomial).pow(&q_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(a__.pow(rubi_int_part(&p_)) * (&a__ + &b__ * x_.pow(&n_)).pow(&frac_p) / (Atom::num(1) + &b__ * x_.pow(&n_) / &a__).pow(frac_p), recursive)
        },
    ));
}

fn push_rules_rule_1015(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, n_, p_, q_, v__, x_);
    let rule = rubi_rule!(
        order: 1015,
        source: "Int[x_^m_.*(a_.+b_.*v_^n_)^p_.*(c_.+d_.*v_^n_)^q_.,x_Symbol] :=
          1/Coefficient[v,x,1]^(m+1) \\[Star] Subst[Int[SimplifyIntegrand[(x-Coefficient[v,x,0])^m*(a+b*x^n)^p*(c+d*x^n)^q,x],x],x,v] /;
        FreeQ[{a,b,c,d,n,p,q},x] && LinearQ[v,x] && IntegerQ[m] && NeQ[v,x]",
        desc: "Integration by substitution",
        refs: [],
        pattern: x_.pow(m_) * (a__ + b__ * v__.pow(n_)).pow(p_) * (c__ + d__ * v__.pow(n_)).pow(q_),
        with: [a__, b__, c__, d__, v__, m_, n_, p_, q_, x_],
        optional: [a__, b__, c__, d__, m_, p_, q_],
        x_dep: [v__],
        x_free: [a__, b__, c__, d__, n_, p_, q_],
        x_linear: [v__],
        when: {
            freeq!([a__, b__, c__, d__, n_, p_, q_], x_)
                && rubi_linear_q(&v__, x_)
                && integerq!(m_)
                && neq!(v__, x_)
        },
        rhs: {
            let constant = rubi_coefficient(&v__, x_, 0).rubi_rhs();
            let slope = rubi_coefficient(&v__, x_, 1).rubi_rhs();

            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = rubi_simplify_integrand(
                &((&sub_atom - constant).pow(&m_)
                * (&a__ + &b__ * sub_atom.pow(&n_)).pow(&p_)
                    * (&c__ + &d__ * sub_atom.pow(&n_)).pow(&q_)),
                sub,
            );
            let transformed = rubi_rhs_int(&transformed_integrand, sub);
            let substituted = rubi_subst(&transformed, sub, v__);

            rubi_star(Atom::num(1) / slope.pow(&m_ + Atom::num(1)), substituted)
        },
    );
    rules.push(rule.with_explicit_variable_power_factor());
}

fn push_rules_rule_1014(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, n_, p_, q_, u__, v__);
    let rule = rubi_rule!(
        order: 1014,
        source: "Int[u_^m_.*(a_.+b_.*v_^n_)^p_.*(c_.+d_.*v_^n_)^q_.,x_Symbol] :=
          u^m/(Coefficient[v,x,1]*v^m) \\[Star] Subst[Int[x^m*(a+b*x^n)^p*(c+d*x^n)^q,x],x,v] /;
        FreeQ[{a,b,c,d,m,n,p,q},x] && LinearPairQ[u,v,x]",
        desc: "Integration by substitution and piecewise constant extraction",
        refs: [],
        pattern: u__.pow(m_) * (a__ + b__ * v__.pow(n_)).pow(p_) * (c__ + d__ * v__.pow(n_)).pow(q_),
        with: [a__, b__, c__, d__, u__, v__, m_, n_, p_, q_, x_],
        optional: [a__, b__, c__, d__, m_, p_, q_],
        x_dep: [u__, v__],
        x_free: [a__, b__, c__, d__, m_, n_, p_, q_],
        x_linear: [u__, v__],
        when: {
            freeq!([a__, b__, c__, d__, m_, n_, p_, q_], x_)
                && rubi_linear_pair_q(&u__, &v__, x_)
        },
        rhs: {
            let slope = rubi_coefficient(&v__, x_, 1).rubi_rhs();

            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = sub_atom.pow(&m_)
                * (&a__ + &b__ * sub_atom.pow(&n_)).pow(&p_)
                * (&c__ + &d__ * sub_atom.pow(&n_)).pow(&q_);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);
            let substituted = rubi_subst(&transformed, sub, &v__);

            rubi_star(u__.pow(&m_), substituted / (&slope * v__.pow(&m_)))
        },
    );
    rules.push(rule.with_proportional_affine_factor_pair());
}

fn push_rules_rule_1016(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, mn_, n_, p_, q_, x_);
    let rule = rubi_rule!(
        order: 1016,
        source: "Int[x_^m_.*(a_+b_.*x_^n_.)^p_.*(c_+d_.*x_^mn_.)^q_.,x_Symbol] :=
          Int[x^(m-n*q)*(a+b*x^n)^p*(d+c*x^n)^q,x] /;
        FreeQ[{a,b,c,d,m,n,p},x] && EqQ[mn,-n] && IntegerQ[q] && (PosQ[n] || Not[IntegerQ[p]])",
        desc: "Algebraic normalization",
        refs: [],
        pattern: x_.pow(m_) * (a__ + b__ * x_.pow(n_)).pow(p_) * (c__ + d__ * x_.pow(mn_)).pow(q_),
        with: [a__, b__, c__, d__, m_, n_, mn_, p_, q_, x_],
        optional: [b__, d__, m_, n_, mn_, p_, q_],
        x_free: [a__, b__, c__, d__, m_, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, m_, n_, p_], x_)
                && eqq!(mn_, -&n_)
                && integerq!(q_)
                && (posq!(n_) || !integerq!(p_))
        },
        rhs: {
            let recursive_integrand = x_.pow(&m_ - &n_ * &q_)
                * (&a__ + &b__ * x_.pow(&n_)).pow(&p_)
                * (&d__ + &c__ * x_.pow(&n_)).pow(&q_);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    );
    rules.push(rule.with_negated_binomial_exponent_pair());
}

fn push_rules_rule_1017(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, mn_, n_, p_, q_, x_);
    let rule = rubi_rule!(
        order: 1017,
        source: "Int[x_^m_.*(a_+b_.*x_^n_.)^p_*(c_+d_.*x_^mn_.)^q_,x_Symbol] :=
          x^(n*FracPart[q])*(c+d*x^(-n))^FracPart[q]/(d+c*x^n)^FracPart[q] \\[Star] Int[x^(m-n*q)*(a+b*x^n)^p*(d+c*x^n)^q,x] /;
        FreeQ[{a,b,c,d,m,n,p,q},x] && EqQ[mn,-n] && Not[IntegerQ[q]] && Not[IntegerQ[p]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern: x_.pow(m_) * (c__ + d__ * x_.pow(mn_)).pow(q_) * (a__ + b__ * x_.pow(n_)).pow(p_),
        with: [a__, b__, c__, d__, m_, n_, mn_, p_, q_, x_],
        optional: [b__, d__, m_, n_, mn_],
        when: {
            freeq!([a__, b__, c__, d__, m_, n_, p_, q_], x_)
                && eqq!(mn_, -&n_)
                && !integerq!(q_)
                && !integerq!(p_)
        },
        rhs: {
            let frac_q = rubi_frac_part(&q_);
            let recursive_integrand = x_.pow(&m_ - &n_ * &q_)
                * (&a__ + &b__ * x_.pow(&n_)).pow(&p_)
                * (&d__ + &c__ * x_.pow(&n_)).pow(&q_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(x_.pow(&n_ * &frac_q) * (&c__ + &d__ * x_.pow(-&n_)).pow(&frac_q) / (&d__ + &c__ * x_.pow(&n_)).pow(frac_q), recursive)
        },
    );
    rules.push(rule.with_negated_binomial_exponent_pair());
}

fn push_rules_rule_1018(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, mn_, n_, p_, q_, x_);
    let rule = rubi_rule!(
        order: 1018,
        source: "Int[(e_*x_)^m_*(a_+b_.*x_^n_.)^p_.*(c_+d_.*x_^mn_.)^q_.,x_Symbol] :=
          e^IntPart[m]*(e*x)^FracPart[m]/x^FracPart[m] \\[Star] Int[x^m*(a+b*x^n)^p*(c+d*x^(-n))^q,x] /;
        FreeQ[{a,b,c,d,e,m,n,p,q},x] && EqQ[mn,-n]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern: (e__ * x_).pow(m_) * (c__ + d__ * x_.pow(mn_)).pow(q_) * (a__ + b__ * x_.pow(n_)).pow(p_),
        with: [a__, b__, c__, d__, e__, m_, n_, mn_, p_, q_, x_],
        optional: [b__, d__, n_, mn_, p_, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, n_, p_, q_], x_)
                && eqq!(mn_, -&n_)
        },
        rhs: {
            let frac_m = rubi_frac_part(&m_);
            let recursive_integrand = x_.pow(&m_)
                * (&a__ + &b__ * x_.pow(&n_)).pow(&p_)
                * (&c__ + &d__ * x_.pow(-&n_)).pow(&q_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star(e__.pow(rubi_int_part(&m_)) * (&e__ * x_).pow(&frac_m) / x_.pow(frac_m), recursive)
        },
    );
    rules.push(rule.with_negated_binomial_exponent_pair());
}

fn push_rules_rule_2036(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a1__, a2__, b1__, b2__, c__, d__, n_, non2_, p_, q_, u_, x_);
    rules.push(rubi_rule!(
        order: 2036,
        source: "Int[u_.*(a1_+b1_.*x_^non2_.)^p_.*(a2_+b2_.*x_^non2_.)^p_.*(c_+d_.*x_^n_.)^q_.,x_Symbol] :=
          Int[u*(a1*a2+b1*b2*x^n)^p*(c+d*x^n)^q,x] /;
        FreeQ[{a1,b1,a2,b2,c,d,n,p,q},x] && EqQ[non2,n/2] && EqQ[a2*b1+a1*b2,0] && (IntegerQ[p] || GtQ[a1,0] && GtQ[a2,0])",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [u_, a1__, b1__, a2__, b2__, c__, d__, non2_, n_, p_, q_, x_],
        optional: [u_, b1__, b2__, d__, non2_, n_, p_, q_],
        when: {
            freeq!([a1__, b1__, a2__, b2__, c__, d__, n_, p_, q_], x_)
                && eqq!(non2_, &n_ / Atom::num(2))
                && eqq!(&a2__ * &b1__ + &a1__ * &b2__, 0)
                && (integerq!(p_) || gtq!(a1__, 0) && gtq!(a2__, 0))
        },
        rhs: {
            let recursive_integrand = &u_
                * (&a1__ * &a2__ + &b1__ * &b2__ * x_.pow(&n_)).pow(&p_)
                * (&c__ + &d__ * x_.pow(&n_)).pow(&q_);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_2037(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        a1__, a2__, b1__, b2__, c__, d__, e__, n_, n2_, non2_, p_, q_, u_, x_
    );
    rules.push(rubi_rule!(
        order: 2037,
        source: "Int[u_.*(a1_+b1_.*x_^non2_.)^p_.*(a2_+b2_.*x_^non2_.)^p_.*(c_+d_.*x_^n_.+e_.*x_^n2_.)^q_.,x_Symbol] :=
          Int[u*(a1*a2+b1*b2*x^n)^p*(c+d*x^n+e*x^(2*n))^q,x] /;
        FreeQ[{a1,b1,a2,b2,c,d,e,n,p,q},x] && EqQ[non2,n/2] && EqQ[n2,2*n] && EqQ[a2*b1+a1*b2,0] && (IntegerQ[p] || GtQ[a1,0] && GtQ[a2,0])",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [u_, a1__, b1__, a2__, b2__, c__, d__, e__, non2_, n_, n2_, p_, q_, x_],
        optional: [u_, b1__, b2__, d__, e__, non2_, n_, n2_, p_, q_],
        when: {
            freeq!([a1__, b1__, a2__, b2__, c__, d__, e__, n_, p_, q_], x_)
                && eqq!(non2_, &n_ / Atom::num(2))
                && eqq!(n2_, Atom::num(2) * &n_)
                && eqq!(&a2__ * &b1__ + &a1__ * &b2__, 0)
                && (integerq!(p_) || gtq!(a1__, 0) && gtq!(a2__, 0))
        },
        rhs: {
            let monomial = x_.pow(&n_);
            let recursive_integrand = &u_
                * (&a1__ * &a2__ + &b1__ * &b2__ * &monomial).pow(&p_)
                * (&c__ + &d__ * &monomial + &e__ * x_.pow(Atom::num(2) * &n_)).pow(&q_);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_2038(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a1__, a2__, b1__, b2__, c__, d__, n_, non2_, p_, q_, u_, x_);
    rules.push(rubi_rule!(
        order: 2038,
        source: "Int[u_.*(a1_+b1_.*x_^non2_.)^p_*(a2_+b2_.*x_^non2_.)^p_*(c_+d_.*x_^n_.)^q_.,x_Symbol] :=
          (a1+b1*x^(n/2))^FracPart[p]*(a2+b2*x^(n/2))^FracPart[p]/(a1*a2+b1*b2*x^n)^FracPart[p] \\[Star]
            Int[u*(a1*a2+b1*b2*x^n)^p*(c+d*x^n)^q,x] /;
        FreeQ[{a1,b1,a2,b2,c,d,n,p,q},x] && EqQ[non2,n/2] && EqQ[a2*b1+a1*b2,0] && Not[EqQ[n,2] && IGtQ[q,0]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [u_, a1__, b1__, a2__, b2__, c__, d__, non2_, n_, p_, q_, x_],
        optional: [u_, b1__, b2__, d__, non2_, n_, q_],
        when: {
            freeq!([a1__, b1__, a2__, b2__, c__, d__, n_, p_, q_], x_)
                && eqq!(non2_, &n_ / Atom::num(2))
                && eqq!(&a2__ * &b1__ + &a1__ * &b2__, 0)
                && !(eqq!(n_, 2) && igtq!(q_, 0))
        },
        rhs: {
            let frac_p = rubi_frac_part(&p_);
            let half_power = x_.pow(&n_ / Atom::num(2));
            let combined = &a1__ * &a2__ + &b1__ * &b2__ * x_.pow(&n_);
            let recursive_integrand =
                &u_ * combined.pow(&p_) * (&c__ + &d__ * x_.pow(&n_)).pow(&q_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star((&a1__ + &b1__ * &half_power).pow(&frac_p) * (&a2__ + &b2__ * half_power).pow(&frac_p) / combined.pow(frac_p), recursive)
        },
    ));
}

fn push_rules_rule_2039(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        a1__, a2__, b1__, b2__, c__, d__, e__, n_, n2_, non2_, p_, q_, u_, x_
    );
    rules.push(rubi_rule!(
        order: 2039,
        source: "Int[u_.*(a1_+b1_.*x_^non2_.)^p_.*(a2_+b2_.*x_^non2_.)^p_.*(c_+d_.*x_^n_.+e_.*x_^n2_.)^q_.,x_Symbol] :=
          (a1+b1*x^(n/2))^FracPart[p]*(a2+b2*x^(n/2))^FracPart[p]/(a1*a2+b1*b2*x^n)^FracPart[p] \\[Star]
            Int[u*(a1*a2+b1*b2*x^n)^p*(c+d*x^n+e*x^(2*n))^q,x] /;
        FreeQ[{a1,b1,a2,b2,c,d,e,n,p,q},x] && EqQ[non2,n/2] && EqQ[n2,2*n] && EqQ[a2*b1+a1*b2,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [u_, a1__, b1__, a2__, b2__, c__, d__, e__, non2_, n_, n2_, p_, q_, x_],
        optional: [u_, b1__, b2__, d__, e__, non2_, n_, n2_, p_, q_],
        when: {
            freeq!([a1__, b1__, a2__, b2__, c__, d__, e__, n_, p_, q_], x_)
                && eqq!(non2_, &n_ / Atom::num(2))
                && eqq!(n2_, Atom::num(2) * &n_)
                && eqq!(&a2__ * &b1__ + &a1__ * &b2__, 0)
        },
        rhs: {
            let monomial = x_.pow(&n_);
            let frac_p = rubi_frac_part(&p_);
            let half_power = x_.pow(&n_ / Atom::num(2));
            let combined = &a1__ * &a2__ + &b1__ * &b2__ * &monomial;
            let recursive_integrand =
                &u_ * combined.pow(&p_) * (&c__ + &d__ * &monomial + &e__ * x_.pow(Atom::num(2) * &n_)).pow(&q_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_star((&a1__ + &b1__ * &half_power).pow(&frac_p) * (&a2__ + &b2__ * half_power).pow(&frac_p) / combined.pow(frac_p), recursive)
        },
    ));
}

// Generated shared pattern builders.

#[inline(never)]
fn rubi_shared_pattern_0(symbols: &RubiSymbols) -> Atom {
    let a1__ = symbols.a1__;
    let a2__ = symbols.a2__;
    let b1__ = symbols.b1__;
    let b2__ = symbols.b2__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let non2_ = symbols.non2_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (e__ * x_).pow(m_)
        * (a1__ + b1__ * x_.pow(non2_)).pow(p_)
        * (a2__ + b2__ * x_.pow(non2_)).pow(p_)
        * (c__ + d__ * x_.pow(n_))
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (e__ * x_).pow(m_) * (a__ + b__ * x_.pow(n_)).pow(p_) * (c__ + d__ * x_.pow(n_))
}

#[inline(never)]
fn rubi_shared_pattern_2(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (e__ * x_).pow(m_) * (a__ + b__ * x_.pow(n_)).pow(p_) * (c__ + d__ * x_.pow(n_)).pow(2)
}

#[inline(never)]
fn rubi_shared_pattern_3(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let q_ = symbols.q_;
    let x_ = symbols.x_;
    (e__ * x_).pow(m_) * (a__ + b__ * x_.pow(n_)).pow(p_) * (c__ + d__ * x_.pow(n_)).pow(q_)
}

#[inline(never)]
fn rubi_shared_pattern_4(symbols: &RubiSymbols) -> Atom {
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let q_ = symbols.q_;
    let x_ = symbols.x_;
    (e__ * x_).pow(m_) * (b__ * x_.pow(n_)).pow(p_) * (c__ + d__ * x_.pow(n_)).pow(q_)
}

#[inline(never)]
fn rubi_shared_pattern_5(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    (e__ * x_).pow(m_) / ((a__ + b__ * x_.pow(n_)) * (c__ + d__ * x_.pow(n_)))
}

#[inline(never)]
fn rubi_shared_pattern_6(symbols: &RubiSymbols) -> Atom {
    let a1__ = symbols.a1__;
    let a2__ = symbols.a2__;
    let b1__ = symbols.b1__;
    let b2__ = symbols.b2__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let n_ = symbols.n_;
    let non2_ = symbols.non2_;
    let p_ = symbols.p_;
    let q_ = symbols.q_;
    let u_ = symbols.u_;
    let x_ = symbols.x_;
    u_ * (a1__ + b1__ * x_.pow(non2_)).pow(p_)
        * (a2__ + b2__ * x_.pow(non2_)).pow(p_)
        * (c__ + d__ * x_.pow(n_)).pow(q_)
}

#[inline(never)]
fn rubi_shared_pattern_7(symbols: &RubiSymbols) -> Atom {
    let a1__ = symbols.a1__;
    let a2__ = symbols.a2__;
    let b1__ = symbols.b1__;
    let b2__ = symbols.b2__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let n2_ = symbols.n2_;
    let n_ = symbols.n_;
    let non2_ = symbols.non2_;
    let p_ = symbols.p_;
    let q_ = symbols.q_;
    let u_ = symbols.u_;
    let x_ = symbols.x_;
    u_ * (a1__ + b1__ * x_.pow(non2_)).pow(p_)
        * (a2__ + b2__ * x_.pow(non2_)).pow(p_)
        * (c__ + d__ * x_.pow(n_) + e__ * x_.pow(n2_)).pow(q_)
}

#[inline(never)]
fn rubi_shared_pattern_8(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    x_ * (a__ + b__ * x_.pow(n_)).pow(p_) / (c__ + d__ * x_.pow(n_))
}

#[inline(never)]
fn rubi_shared_pattern_9(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let q_ = symbols.q_;
    let x_ = symbols.x_;
    x_.pow(m_) * (a__ + b__ * x_.pow(n_)).pow(p_) * (c__ + d__ * x_.pow(n_)).pow(q_)
}

#[inline(never)]
fn rubi_shared_pattern_10(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let x_ = symbols.x_;
    x_ / ((a__ + b__ * x_.pow(3)) * (c__ + d__ * x_.pow(3)).sqrt())
}

#[inline(never)]
fn rubi_shared_pattern_11(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let x_ = symbols.x_;
    x_ / ((c__ + d__ * x_.pow(3)) * (a__ + b__ * x_.pow(3)).sqrt())
}
