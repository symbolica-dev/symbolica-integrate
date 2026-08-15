use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_791(rules);
    push_rules_rule_792(rules);
    push_rules_rule_793(rules);
    push_rules_rule_794(rules);
    push_rules_rule_795(rules);
    push_rules_rule_796(rules);
    push_rules_rule_797(rules);
    push_rules_rule_798(rules);
    push_rules_rule_799(rules);
    push_rules_rule_800(rules);
    push_rules_rule_801(rules);
    push_rules_rule_802(rules);
    push_rules_rule_803(rules);
    push_rules_rule_804(rules);
    push_rules_rule_805(rules);
    push_rules_rule_806(rules);
    push_rules_rule_807(rules);
    push_rules_rule_808(rules);
    push_rules_rule_809(rules);
    push_rules_rule_810(rules);
    push_rules_rule_811(rules);
    push_rules_rule_812(rules);
    push_rules_rule_813(rules);
    push_rules_rule_814(rules);
    push_rules_rule_815(rules);
    push_rules_rule_816(rules);
    push_rules_rule_817(rules);
    push_rules_rule_818(rules);
    push_rules_rule_819(rules);
    push_rules_rule_820(rules);
    push_rules_rule_821(rules);
    push_rules_rule_822(rules);
    push_rules_rule_823(rules);
    push_rules_rule_824(rules);
    push_rules_rule_825(rules);
    push_rules_rule_826(rules);
    push_rules_rule_827(rules);
    push_rules_rule_828(rules);
    push_rules_rule_829(rules);
    push_rules_rule_830(rules);
    push_rules_rule_831(rules);
    push_rules_rule_832(rules);
    push_rules_rule_833(rules);
    push_rules_rule_834(rules);
    push_rules_rule_835(rules);
    push_rules_rule_836(rules);
    push_rules_rule_837(rules);
    push_rules_rule_838(rules);
    push_rules_rule_839(rules);
    push_rules_rule_840(rules);
    push_rules_rule_841(rules);
    push_rules_rule_842(rules);
    push_rules_rule_843(rules);
    push_rules_rule_844(rules);
    push_rules_rule_845(rules);
    push_rules_rule_846(rules);
    push_rules_rule_847(rules);
    push_rules_rule_848(rules);
    push_rules_rule_849(rules);
    push_rules_rule_850(rules);
    push_rules_rule_851(rules);
    push_rules_rule_852(rules);
    push_rules_rule_853(rules);
    push_rules_rule_854(rules);
    push_rules_rule_855(rules);
    push_rules_rule_856(rules);
    push_rules_rule_857(rules);
    push_rules_rule_858(rules);
    push_rules_rule_859(rules);
    push_rules_rule_860(rules);
    push_rules_rule_861(rules);
    push_rules_rule_862(rules);
    push_rules_rule_863(rules);
    push_rules_rule_864(rules);
    push_rules_rule_865(rules);
    push_rules_rule_866(rules);
    push_rules_rule_867(rules);
    push_rules_rule_868(rules);
    push_rules_rule_869(rules);
    push_rules_rule_870(rules);
    push_rules_rule_871(rules);
    push_rules_rule_872(rules);
    push_rules_rule_873(rules);
    push_rules_rule_874(rules);
    push_rules_rule_875(rules);
    push_rules_rule_876(rules);
    push_rules_rule_877(rules);
    push_rules_rule_880(rules);
    push_rules_rule_881(rules);
    push_rules_rule_882(rules);
    push_rules_rule_883(rules);
    push_rules_rule_884(rules);
    push_rules_rule_878(rules);
    push_rules_rule_879(rules);
    push_rules_rule_885(rules);
    push_rules_rule_886(rules);
    push_rules_rule_887(rules);
    push_rules_rule_888(rules);
    push_rules_rule_889(rules);
    push_rules_rule_890(rules);
    push_rules_rule_891(rules);
    push_rules_rule_892(rules);
    push_rules_rule_893(rules);
    push_rules_rule_894(rules);
    push_rules_rule_896(rules);
    push_rules_rule_895(rules);
}

fn push_rules_rule_791(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a1__, b1__, c__, a2__, m_, n_, p_, x_, b2__);
    rules.push(rubi_rule!(
        order: 791,
        source: "Int[(c_.*x_)^m_.*(a1_+b1_.*x_^n_)^p_*(a2_+b2_.*x_^n_)^p_,x_Symbol] :=
          Int[(c*x)^m*(a1*a2+b1*b2*x^(2*n))^p,x] /;
        FreeQ[{a1,b1,a2,b2,c,m,n,p},x] && EqQ[a2*b1+a1*b2,0] && (IntegerQ[p] || GtQ[a1,0] && GtQ[a2,0])",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a1__, b1__, c__, a2__, b2__, m_, n_, p_, x_],
        optional: [b1__, c__, b2__, m_],
        when: {
            freeq!([a1__, b1__, c__, a2__, b2__, m_, n_, p_], x_)
                && eqq!(&a2__ * &b1__ + &a1__ * &b2__, 0)
                && (integerq!(p_) || gtq!(a1__, 0) && gtq!(a2__, 0))
        },
        rhs: {
            let transformed_integrand =
                (&c__ * x_).pow(&m_) * (&a1__ * &a2__ + &b1__ * &b2__ * x_.pow(Atom::num(2) * &n_)).pow(&p_);

            rubi_rhs_int(&transformed_integrand, x_)
        },
    ));
}

fn push_rules_rule_792(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 792,
        source: "Int[x_^m_./(a_+b_.*x_^n_),x_Symbol] :=
          Log[RemoveContent[a+b*x^n,x]]/(b*n) /;
        FreeQ[{a,b,m,n},x] && EqQ[m,n-1]",
        desc: "Integration by substitution and reciprocal rule for integration",
        refs: [],
        pattern: x_.pow(m_) * (a__ + b__ * x_.pow(n_)).pow(-1),
        with: [a__, b__, m_, n_, x_],
        optional: [b__, m_],
        when: {
            freeq!([a__, b__, m_, n_], x_)
                && eqq!(m_, &n_ - Atom::num(1))
        },
        rhs: {
            let content_removed = rubi_remove_content(&(&a__ + &b__ * x_.pow(&n_)), x_);
            rubi_simp(&(content_removed.log() / (&b__ * &n_)), x_)
        },
    ));
}

fn push_rules_rule_793(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 793,
        source: "Int[x_^m_.*(a_+b_.*x_^n_)^p_,x_Symbol] :=
          (a+b*x^n)^(p+1)/(b*n*(p+1)) /;
        FreeQ[{a,b,m,n,p},x] && EqQ[m,n-1] && NeQ[p,-1]",
        desc: "Integration by substitution and power rule for integration",
        refs: ["G&R 2.110.4, CRC 88a with m=n-1"],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [a__, b__, m_, n_, p_, x_],
        optional: [b__, m_],
        when: {
            freeq!([a__, b__, m_, n_, p_], x_)
                && eqq!(m_, &n_ - Atom::num(1))
                && neq!(p_, -1)
        },
        rhs: {
            let raised = &p_ + Atom::num(1);
            rubi_simp(&((&a__ + &b__ * x_.pow(&n_)).pow(&raised)
                    / (&b__ * &n_ * raised)), x_)
        },
    ));
}

fn push_rules_rule_794(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a1__, b1__, a2__, m_, n_, p_, x_, b2__);
    rules.push(rubi_rule!(
        order: 794,
        source: "Int[x_^m_.*(a1_+b1_.*x_^n_.)^p_*(a2_+b2_.*x_^n_.)^p_,x_Symbol] :=
          (a1+b1*x^n)^(p+1)*(a2+b2*x^n)^(p+1)/(2*b1*b2*n*(p+1)) /;
        FreeQ[{a1,b1,a2,b2,m,n,p},x] && EqQ[a2*b1+a1*b2,0] && EqQ[m,2*n-1] && NeQ[p,-1]",
        desc: "Integration by substitution and power rule for integration",
        refs: ["G&R 2.110.4, CRC 88a with m=n-1"],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [a1__, b1__, a2__, b2__, m_, n_, p_, x_],
        optional: [b1__, b2__, m_, n_],
        when: {
            freeq!([a1__, b1__, a2__, b2__, m_, n_, p_], x_)
                && eqq!(&a2__ * &b1__ + &a1__ * &b2__, 0)
                && eqq!(m_, Atom::num(2) * &n_ - Atom::num(1))
                && neq!(p_, -1)
        },
        rhs: {
            let raised = &p_ + Atom::num(1);
            let monomial = x_.pow(&n_);
            rubi_simp(&((&a1__ + &b1__ * &monomial).pow(&raised)
                    * (&a2__ + &b2__ * monomial).pow(&raised)
                    / (Atom::num(2) * &b1__ * &b2__ * &n_ * raised)), x_)
        },
    ));
}

fn push_rules_rule_795(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 795,
        source: "Int[x_^m_.*(a_+b_.*x_^n_)^p_,x_Symbol] :=
          Int[x^(m+n*p)*(b+a*x^(-n))^p,x] /;
        FreeQ[{a,b,m,n},x] && IntegerQ[p] && NegQ[n]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [a__, b__, m_, n_, p_, x_],
        optional: [b__, m_],
        when: {
            freeq!([a__, b__, m_, n_], x_)
                && integerq!(p_)
                && negq!(n_)
        },
        rhs: {
            let transformed_integrand =
                x_.pow(&m_ + &n_ * &p_) * (&b__ + &a__ / x_.pow(&n_)).pow(&p_);

            rubi_rhs_int(&transformed_integrand, x_)
        },
    ));
}

fn push_rules_rule_796(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 796,
        source: "Int[(c_.*x_)^m_.*(a_+b_.*x_^n_)^p_,x_Symbol] :=
          (c*x)^(m+1)*(a+b*x^n)^(p+1)/(a*c*(m+1)) /;
        FreeQ[{a,b,c,m,n,p},x] && EqQ[(m+1)/n+p+1,0] && NeQ[m,-1]",
        desc: "Binomial recurrence 3b with m+n p+n+1\\[Equal]0",
        refs: ["G&R 2.110.6, CRC 88c with m+n p+n+1\\[Equal]0"],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, m_, n_, p_, x_],
        optional: [b__, c__, m_],
        when: {
            freeq!([a__, b__, c__, m_, n_, p_], x_)
                && eqq!((&m_ + Atom::num(1)) / &n_ + &p_ + Atom::num(1), 0)
                && neq!(m_, -1)
        },
        rhs: {
            let raised_m = &m_ + Atom::num(1);
            rubi_simp(&((&c__ * x_).pow(&raised_m)
                    * (&a__ + &b__ * x_.pow(&n_)).pow(&p_ + Atom::num(1))
                    / (&a__ * &c__ * raised_m)), x_)
        },
    ));
}

fn push_rules_rule_797(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a1__, b1__, c__, a2__, m_, n_, p_, x_, b2__);
    rules.push(rubi_rule!(
        order: 797,
        source: "Int[(c_.*x_)^m_.*(a1_+b1_.*x_^n_)^p_*(a2_+b2_.*x_^n_)^p_,x_Symbol] :=
          (c*x)^(m+1)*(a1+b1*x^n)^(p+1)*(a2+b2*x^n)^(p+1)/(a1*a2*c*(m+1)) /;
        FreeQ[{a1,b1,a2,b2,c,m,n,p},x] && EqQ[a2*b1+a1*b2,0] && EqQ[(m+1)/(2*n)+p+1,0] && NeQ[m,-1]",
        desc: "Binomial recurrence 3b with m+n p+n+1\\[Equal]0",
        refs: ["G&R 2.110.6, CRC 88c with m+n p+n+1\\[Equal]0"],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a1__, b1__, c__, a2__, b2__, m_, n_, p_, x_],
        optional: [b1__, c__, b2__, m_],
        when: {
            freeq!([a1__, b1__, c__, a2__, b2__, m_, n_, p_], x_)
                && eqq!(&a2__ * &b1__ + &a1__ * &b2__, 0)
                && eqq!((&m_ + Atom::num(1)) / (Atom::num(2) * &n_) + &p_ + Atom::num(1), 0)
                && neq!(m_, -1)
        },
        rhs: {
            let raised_m = &m_ + Atom::num(1);
            let monomial = x_.pow(&n_);
            rubi_simp(&((&c__ * x_).pow(&raised_m)
                    * (&a1__ + &b1__ * &monomial).pow(&p_ + Atom::num(1))
                    * (&a2__ + &b2__ * monomial).pow(&p_ + Atom::num(1))
                    / (&a1__ * &a2__ * &c__ * raised_m)), x_)
        },
    ));
}

fn push_rules_rule_798(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 798,
        source: "Int[x_^m_.*(a_+b_.*x_^n_)^p_,x_Symbol] :=
          1/n \\[Star] Subst[Int[x^(Simplify[(m+1)/n]-1)*(a+b*x)^p,x],x,x^n] /;
        FreeQ[{a,b,m,n,p},x] && IntegerQ[Simplify[(m+1)/n]]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [a__, b__, m_, n_, p_, x_],
        optional: [b__, m_],
        when: {
            let quotient = rubi_simplify(&((&m_ + Atom::num(1)) / &n_));
            freeq!([a__, b__, m_, n_, p_], x_)
                && integerq!(quotient)
        },
        rhs: {
            let quotient = rubi_simplify(&((&m_ + Atom::num(1)) / &n_));
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand =
                sub_atom.pow(&quotient - Atom::num(1)) * (&a__ + &b__ * &sub_atom).pow(&p_);
            let primitive = rubi_rhs_int(&transformed_integrand, sub);
            let substituted = rubi_subst(&primitive, sub, x_.pow(&n_));

            rubi_star(Atom::num(1) / &n_, substituted)
        },
    ));
}

fn push_rules_rule_799(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a1__, b1__, a2__, m_, n_, p_, x_, b2__);
    rules.push(rubi_rule!(
        order: 799,
        source: "Int[x_^m_.*(a1_+b1_.*x_^n_)^p_*(a2_+b2_.*x_^n_)^p_,x_Symbol] :=
          1/n \\[Star] Subst[Int[x^(Simplify[(m+1)/n]-1)*(a1+b1*x)^p*(a2+b2*x)^p,x],x,x^n] /;
        FreeQ[{a1,b1,a2,b2,m,n,p},x] && EqQ[a2*b1+a1*b2,0] && IntegerQ[Simplify[(m+1)/(2*n)]]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [a1__, b1__, a2__, b2__, m_, n_, p_, x_],
        optional: [b1__, b2__, m_],
        when: {
            let two_n = Atom::num(2) * &n_;
            let quotient = rubi_simplify(&((&m_ + Atom::num(1)) / two_n));
            freeq!([a1__, b1__, a2__, b2__, m_, n_, p_], x_)
                && eqq!(&a2__ * &b1__ + &a1__ * &b2__, 0)
                && integerq!(quotient)
        },
        rhs: {
            let quotient = rubi_simplify(&((&m_ + Atom::num(1)) / &n_));
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = sub_atom.pow(&quotient - Atom::num(1))
                * (&a1__ + &b1__ * &sub_atom).pow(&p_)
                * (&a2__ + &b2__ * sub_atom).pow(&p_);
            let primitive = rubi_rhs_int(&transformed_integrand, sub);
            let substituted = rubi_subst(&primitive, sub, x_.pow(&n_));

            rubi_star(Atom::num(1) / &n_, substituted)
        },
    ));
}

fn push_rules_rule_800(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 800,
        source: "Int[(c_*x_)^m_*(a_+b_.*x_^n_)^p_,x_Symbol] :=
          c^IntPart[m]*(c*x)^FracPart[m]/x^FracPart[m] \\[Star] Int[x^m*(a+b*x^n)^p,x] /;
        FreeQ[{a,b,c,m,n,p},x] && IntegerQ[Simplify[(m+1)/n]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, m_, n_, p_, x_],
        optional: [b__],
        when: {
            let quotient = rubi_simplify(&((&m_ + Atom::num(1)) / &n_));
            freeq!([a__, b__, c__, m_, n_, p_], x_)
                && integerq!(quotient)
        },
        rhs: {
            let int_m = rubi_int_part(&m_);
            let frac_m = rubi_frac_part(&m_);
            let unscaled_integrand =
                x_.pow(&m_) * (&a__ + &b__ * x_.pow(&n_)).pow(&p_);
            let recursive = rubi_rhs_int(&unscaled_integrand, x_);
            let multiplier = c__.pow(int_m) * (&c__ * x_).pow(&frac_m)
                / x_.pow(frac_m);

            rubi_star(multiplier, recursive)
        },
    ));
}

fn push_rules_rule_801(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a1__, b1__, c__, a2__, m_, n_, p_, x_, b2__);
    rules.push(rubi_rule!(
        order: 801,
        source: "Int[(c_*x_)^m_*(a1_+b1_.*x_^n_)^p_*(a2_+b2_.*x_^n_)^p_,x_Symbol] :=
          c^IntPart[m]*(c*x)^FracPart[m]/x^FracPart[m] \\[Star] Int[x^m*(a1+b1*x^n)^p*(a2+b2*x^n)^p,x] /;
        FreeQ[{a1,b1,a2,b2,c,m,n,p},x] && EqQ[a2*b1+a1*b2,0] && IntegerQ[Simplify[(m+1)/(2*n)]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a1__, b1__, c__, a2__, b2__, m_, n_, p_, x_],
        optional: [b1__, b2__],
        when: {
            let two_n = Atom::num(2) * &n_;
            let quotient = rubi_simplify(&((&m_ + Atom::num(1)) / two_n));
            freeq!([a1__, b1__, c__, a2__, b2__, m_, n_, p_], x_)
                && eqq!(&a2__ * &b1__ + &a1__ * &b2__, 0)
                && integerq!(quotient)
        },
        rhs: {
            let int_m = rubi_int_part(&m_);
            let frac_m = rubi_frac_part(&m_);
            let monomial = x_.pow(&n_);
            let unscaled_integrand = x_.pow(&m_)
                * (&a1__ + &b1__ * &monomial).pow(&p_)
                * (&a2__ + &b2__ * monomial).pow(&p_);
            let recursive = rubi_rhs_int(&unscaled_integrand, x_);
            let multiplier = c__.pow(int_m) * (&c__ * x_).pow(&frac_m)
                / x_.pow(frac_m);

            rubi_star(multiplier, recursive)
        },
    ));
}

fn push_rules_rule_802(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 802,
        source: "Int[(c_.*x_)^m_.*(a_+b_.*x_^n_)^p_.,x_Symbol] :=
          Int[ExpandIntegrand[(c*x)^m*(a+b*x^n)^p,x],x] /;
        FreeQ[{a,b,c,m,n},x] && IGtQ[p,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, m_, n_, p_, x_],
        optional: [b__, c__, m_, p_],
        when: { freeq!([a__, b__, c__, m_, n_], x_) && igtq!(p_, 0) },
        rhs: {
            let transformed = (&c__ * x_).pow(&m_) * (&a__ + &b__ * x_.pow(&n_)).pow(&p_);
            let expanded = rubi_expand_integrand(&transformed, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_803(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 803,
        source: "Int[x_^m_*(a_+b_.*x_^n_)^p_,x_Symbol] :=
          x^(m+1)*(a+b*x^n)^(p+1)/(a*(m+1)) -
          b*(m+n*(p+1)+1)/(a*(m+1)) \\[Star] Int[x^(m+n)*(a+b*x^n)^p,x] /;
        FreeQ[{a,b,m,n,p},x] && ILtQ[Simplify[(m+1)/n+p+1],0] && NeQ[m,-1]",
        desc: "Binomial recurrence 3b",
        refs: ["G&R 2.110.6, CRC 88c"],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [a__, b__, m_, n_, p_, x_],
        optional: [b__],
        when: {
            let quotient = (&m_ + Atom::num(1)) / &n_;
            let balance = rubi_simplify(&(quotient + &p_ + Atom::num(1)));
            freeq!([a__, b__, m_, n_, p_], x_)
                && iltq!(balance, 0)
                && neq!(m_, -1)
        },
        rhs: {
            let m1 = &m_ + Atom::num(1);
            let denominator = &a__ * &m1;
            let binomial = &a__ + &b__ * x_.pow(&n_);
            let direct = x_.pow(&m1) * binomial.pow(&p_ + Atom::num(1)) / &denominator;
            let recurrence_factor = &b__
                * (&m_ + &n_ * (&p_ + Atom::num(1)) + Atom::num(1))
                / denominator;
            let recursive_integrand = x_.pow(&m_ + &n_) * binomial.pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) - rubi_star(recurrence_factor, recursive)
        },
    ));
}

fn push_rules_rule_804(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a1__, b1__, a2__, m_, n_, p_, x_, b2__);
    rules.push(rubi_rule!(
        order: 804,
        source: "Int[x_^m_*(a1_+b1_.*x_^n_)^p_*(a2_+b2_.*x_^n_)^p_,x_Symbol] :=
          x^(m+1)*(a1+b1*x^n)^(p+1)*(a2+b2*x^n)^(p+1)/(a1*a2*(m+1)) -
          b1*b2*(m+2*n*(p+1)+1)/(a1*a2*(m+1)) \\[Star] Int[x^(m+2*n)*(a1+b1*x^n)^p*(a2+b2*x^n)^p,x] /;
        FreeQ[{a1,b1,a2,b2,m,n,p},x] && EqQ[a2*b1+a1*b2,0] && ILtQ[Simplify[(m+1)/(2*n)+p+1],0] && NeQ[m,-1]",
        desc: "Binomial recurrence 3b",
        refs: ["G&R 2.110.6, CRC 88c"],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [a1__, b1__, a2__, b2__, m_, n_, p_, x_],
        optional: [b1__, b2__],
        when: {
            let two_n = Atom::num(2) * &n_;
            let quotient = (&m_ + Atom::num(1)) / &two_n;
            let balance = rubi_simplify(&(quotient + &p_ + Atom::num(1)));
            freeq!([a1__, b1__, a2__, b2__, m_, n_, p_], x_)
                && eqq!(&a2__ * &b1__ + &a1__ * &b2__, 0)
                && iltq!(balance, 0)
                && neq!(m_, -1)
        },
        rhs: {
            let m1 = &m_ + Atom::num(1);
            let denominator = &a1__ * &a2__ * &m1;
            let monomial = x_.pow(&n_);
            let first = &a1__ + &b1__ * &monomial;
            let second = &a2__ + &b2__ * monomial;
            let direct = x_.pow(&m1)
                * first.pow(&p_ + Atom::num(1))
                * second.pow(&p_ + Atom::num(1))
                / &denominator;
            let recurrence_factor = &b1__
                * &b2__
                * (&m_ + Atom::num(2) * &n_ * (&p_ + Atom::num(1)) + Atom::num(1))
                / denominator;
            let recursive_monomial = x_.pow(&m_ + Atom::num(2) * &n_);
            let recursive_integrand =
                recursive_monomial * first.pow(&p_) * second.pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) - rubi_star(recurrence_factor, recursive)
        },
    ));
}

fn push_rules_rule_805(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 805,
        source: "Int[(c_.*x_)^m_.*(a_+b_.*x_^n_)^p_,x_Symbol] :=
          -(c*x)^(m+1)*(a+b*x^n)^(p+1)/(a*c*n*(p+1)) +
          (m+n*(p+1)+1)/(a*n*(p+1)) \\[Star] Int[(c*x)^m*(a+b*x^n)^(p+1),x] /;
        FreeQ[{a,b,c,m,n,p},x] && ILtQ[Simplify[(m+1)/n+p+1],0] && NeQ[p,-1]",
        desc: "Integration by parts",
        refs: ["G&R 2.110.2, CRC 88d"],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, m_, n_, p_, x_],
        optional: [b__, c__, m_],
        when: {
            let quotient = (&m_ + Atom::num(1)) / &n_;
            let balance = rubi_simplify(&(quotient + &p_ + Atom::num(1)));
            freeq!([a__, b__, c__, m_, n_, p_], x_)
                && iltq!(balance, 0)
                && neq!(p_, -1)
        },
        rhs: {
            let p1 = &p_ + Atom::num(1);
            let scaled = &c__ * x_;
            let binomial = &a__ + &b__ * x_.pow(&n_);
            let direct = -scaled.pow(&m_ + Atom::num(1)) * binomial.pow(&p1)
                / (&a__ * &c__ * &n_ * &p1);
            let recurrence_factor = (&m_ + &n_ * &p1 + Atom::num(1))
                / (&a__ * &n_ * &p1);
            let recursive_integrand = scaled.pow(&m_) * binomial.pow(&p1);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) + rubi_star(recurrence_factor, recursive)
        },
    ));
}

fn push_rules_rule_806(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a1__, b1__, c__, a2__, m_, n_, p_, x_, b2__);
    rules.push(rubi_rule!(
        order: 806,
        source: "Int[(c_.*x_)^m_.*(a1_+b1_.*x_^n_)^p_*(a2_+b2_.*x_^n_)^p_,x_Symbol] :=
          -(c*x)^(m+1)*(a1+b1*x^n)^(p+1)*(a2+b2*x^n)^(p+1)/(2*a1*a2*c*n*(p+1)) +
          (m+2*n*(p+1)+1)/(2*a1*a2*n*(p+1)) \\[Star] Int[(c*x)^m*(a1+b1*x^n)^(p+1)*(a2+b2*x^n)^(p+1),x] /;
        FreeQ[{a1,b1,a2,b2,c,m,n,p},x] && EqQ[a2*b1+a1*b2,0] && ILtQ[Simplify[(m+1)/(2*n)+p+1],0] && NeQ[p,-1]",
        desc: "Integration by parts",
        refs: ["G&R 2.110.2, CRC 88d"],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a1__, b1__, c__, a2__, b2__, m_, n_, p_, x_],
        optional: [b1__, c__, b2__, m_],
        when: {
            let two_n = Atom::num(2) * &n_;
            let quotient = (&m_ + Atom::num(1)) / &two_n;
            let balance = rubi_simplify(&(quotient + &p_ + Atom::num(1)));
            freeq!([a1__, b1__, c__, a2__, b2__, m_, n_, p_], x_)
                && eqq!(&a2__ * &b1__ + &a1__ * &b2__, 0)
                && iltq!(balance, 0)
                && neq!(p_, -1)
        },
        rhs: {
            let p1 = &p_ + Atom::num(1);
            let scaled = &c__ * x_;
            let monomial = x_.pow(&n_);
            let first = &a1__ + &b1__ * &monomial;
            let second = &a2__ + &b2__ * monomial;
            let direct = -scaled.pow(&m_ + Atom::num(1))
                * first.pow(&p1)
                * second.pow(&p1)
                / (Atom::num(2) * &a1__ * &a2__ * &c__ * &n_ * &p1);
            let recurrence_factor = (&m_ + Atom::num(2) * &n_ * &p1 + Atom::num(1))
                / (Atom::num(2) * &a1__ * &a2__ * &n_ * &p1);
            let recursive_integrand = scaled.pow(&m_) * first.pow(&p1) * second.pow(&p1);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) + rubi_star(recurrence_factor, recursive)
        },
    ));
}

fn push_rules_rule_807(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 807,
        source: "Int[x_^m_.*(a_+b_.*x_^n_)^p_,x_Symbol] :=
          With[{k=GCD[m+1,n]},
          1/k \\[Star] Subst[Int[x^((m+1)/k-1)*(a+b*x^(n/k))^p,x],x,x^k] /;
         k!=1] /;
        FreeQ[{a,b,p},x] && IGtQ[n,0] && IntegerQ[m]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [a__, b__, m_, n_, p_, x_],
        optional: [b__, m_],
        when: {
            freeq!([a__, b__, p_], x_)
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
                * (&a__ + &b__ * sub_atom.pow(&n_ / &k)).pow(&p_);
            let primitive = rubi_rhs_int(&transformed_integrand, sub);
            let substituted = rubi_subst(&primitive, sub, x_.pow(&k));

            rubi_star(Atom::num(1) / k, substituted)
        },
    ));
}

fn push_rules_rule_808(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a1__, b1__, a2__, m_, n_, p_, x_, b2__);
    rules.push(rubi_rule!(
        order: 808,
        source: "Int[x_^m_.*(a1_+b1_.*x_^n_)^p_*(a2_+b2_.*x_^n_)^p_,x_Symbol] :=
          With[{k=GCD[m+1,2*n]},
          1/k \\[Star] Subst[Int[x^((m+1)/k-1)*(a1+b1*x^(n/k))^p*(a2+b2*x^(n/k))^p,x],x,x^k] /;
         k!=1] /;
        FreeQ[{a1,b1,a2,b2,p},x] && EqQ[a2*b1+a1*b2,0] && IGtQ[2*n,0] && IntegerQ[m]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [a1__, b1__, a2__, b2__, m_, n_, p_, x_],
        optional: [b1__, b2__, m_],
        when: {
            freeq!([a1__, b1__, a2__, b2__, p_], x_)
                && eqq!(&a2__ * &b1__ + &a1__ * &b2__, 0)
                && igtq!(Atom::num(2) * &n_, 0)
                && integerq!(m_)
                && rubi_gcd(&(&m_ + Atom::num(1)), &(Atom::num(2) * &n_))
                    .is_some_and(|k| k != 1)
        },
        rhs: {
            let k = Atom::num(rubi_gcd(
                &(&m_ + Atom::num(1)),
                &(Atom::num(2) * &n_),
            ).rubi_rhs());
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_monomial = sub_atom.pow(&n_ / &k);
            let transformed_integrand = sub_atom.pow((&m_ + Atom::num(1)) / &k - Atom::num(1))
                * (&a1__ + &b1__ * &transformed_monomial).pow(&p_)
                * (&a2__ + &b2__ * transformed_monomial).pow(&p_);
            let primitive = rubi_rhs_int(&transformed_integrand, sub);
            let substituted = rubi_subst(&primitive, sub, x_.pow(&k));

            rubi_star(Atom::num(1) / k, substituted)
        },
    ));
}

fn push_rules_rule_809(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 809,
        source: "Int[(c_.*x_)^m_.*(a_+b_.*x_^n_)^p_,x_Symbol] :=
          (c*x)^(m+1)*(a+b*x^n)^p/(c*(m+1)) -
          b*n*p/(c^n*(m+1)) \\[Star] Int[(c*x)^(m+n)*(a+b*x^n)^(p-1),x] /;
        FreeQ[{a,b,c},x] && IGtQ[n,0] && GtQ[p,0] && LtQ[m,-1] && Not[ILtQ[(m+n*p+n+1)/n,0]] &&
          IntBinomialQ[a,b,c,n,m,p,x]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, m_, n_, p_, x_],
        optional: [b__, c__, m_],
        when: {
            freeq!([a__, b__, c__], x_)
                && igtq!(n_, 0)
                && gtq!(p_, 0)
                && ltq!(m_, -1)
                && !iltq!((&m_ + &n_ * &p_ + &n_ + Atom::num(1)) / &n_, 0)
                && rubi_int_binomial_q(&a__, &b__, &c__, &n_, &m_, &p_, x_)
        },
        rhs: {
            let m1 = &m_ + Atom::num(1);
            let scaled = &c__ * x_;
            let binomial = &a__ + &b__ * x_.pow(&n_);
            let direct = scaled.pow(&m1) * binomial.pow(&p_) / (&c__ * &m1);
            let recurrence_factor = &b__ * &n_ * &p_ / (c__.pow(&n_) * &m1);
            let recursive_integrand =
                scaled.pow(&m_ + &n_) * binomial.pow(&p_ - Atom::num(1));
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) - rubi_star(recurrence_factor, recursive)
        },
    ));
}

fn push_rules_rule_810(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a1__, b1__, c__, a2__, m_, n_, p_, x_, b2__);
    rules.push(rubi_rule!(
        order: 810,
        source: "Int[(c_.*x_)^m_.*(a1_+b1_.*x_^n_)^p_*(a2_+b2_.*x_^n_)^p_,x_Symbol] :=
          (c*x)^(m+1)*(a1+b1*x^n)^p*(a2+b2*x^n)^p/(c*(m+1)) -
          2*b1*b2*n*p/(c^(2*n)*(m+1)) \\[Star] Int[(c*x)^(m+2*n)*(a1+b1*x^n)^(p-1)*(a2+b2*x^n)^(p-1),x] /;
        FreeQ[{a1,b1,a2,b2,c,m},x] && EqQ[a2*b1+a1*b2,0] && IGtQ[2*n,0] && GtQ[p,0] && LtQ[m,-1] && NeQ[m+2*n*p+1,0] &&
          IntBinomialQ[a1*a2,b1*b2,c,2*n,m,p,x]",
        desc: "Integration by parts",
        refs: ["G&R 2.110.3"],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a1__, b1__, c__, a2__, b2__, m_, n_, p_, x_],
        optional: [b1__, c__, b2__, m_],
        when: {
            freeq!([a1__, b1__, a2__, b2__, c__, m_], x_)
                && eqq!(&a2__ * &b1__ + &a1__ * &b2__, 0)
                && igtq!(Atom::num(2) * &n_, 0)
                && gtq!(p_, 0)
                && ltq!(m_, -1)
                && neq!(&m_ + Atom::num(2) * &n_ * &p_ + Atom::num(1), 0)
                && rubi_int_binomial_q(
                    &(&a1__ * &a2__),
                    &(&b1__ * &b2__),
                    &c__,
                    &(Atom::num(2) * &n_),
                    &m_,
                    &p_,
                    x_
                )
        },
        rhs: {
            let m1 = &m_ + Atom::num(1);
            let scaled = &c__ * x_;
            let monomial = x_.pow(&n_);
            let first = &a1__ + &b1__ * &monomial;
            let second = &a2__ + &b2__ * monomial;
            let direct = scaled.pow(&m1) * first.pow(&p_) * second.pow(&p_)
                / (&c__ * &m1);
            let recurrence_factor = Atom::num(2) * &b1__ * &b2__ * &n_ * &p_
                / (c__.pow(Atom::num(2) * &n_) * &m1);
            let recursive_integrand = scaled.pow(&m_ + Atom::num(2) * &n_)
                * first.pow(&p_ - Atom::num(1))
                * second.pow(&p_ - Atom::num(1));
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) - rubi_star(recurrence_factor, recursive)
        },
    ));
}

fn push_rules_rule_811(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 811,
        source: "Int[(c_.*x_)^m_.*(a_+b_.*x_^n_)^p_,x_Symbol] :=
          (c*x)^(m+1)*(a+b*x^n)^p/(c*(m+n*p+1)) +
          a*n*p/(m+n*p+1) \\[Star] Int[(c*x)^m*(a+b*x^n)^(p-1),x] /;
        FreeQ[{a,b,c,m},x] && IGtQ[n,0] && GtQ[p,0] && NeQ[m+n*p+1,0] && IntBinomialQ[a,b,c,n,m,p,x]",
        desc: "Inverted integration by parts",
        refs: ["G&R 2.110.1, CRC 88b"],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, m_, n_, p_, x_],
        optional: [b__, c__, m_],
        when: {
            freeq!([a__, b__, c__, m_], x_)
                && igtq!(n_, 0)
                && gtq!(p_, 0)
                && neq!(&m_ + &n_ * &p_ + Atom::num(1), 0)
                && rubi_int_binomial_q(&a__, &b__, &c__, &n_, &m_, &p_, x_)
        },
        rhs: {
            let denominator = &m_ + &n_ * &p_ + Atom::num(1);
            let scaled = &c__ * x_;
            let binomial = &a__ + &b__ * x_.pow(&n_);
            let direct = scaled.pow(&m_ + Atom::num(1)) * binomial.pow(&p_)
                / (&c__ * &denominator);
            let recurrence_factor = &a__ * &n_ * &p_ / &denominator;
            let recursive_integrand = scaled.pow(&m_) * binomial.pow(&p_ - Atom::num(1));
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) + rubi_star(recurrence_factor, recursive)
        },
    ));
}

fn push_rules_rule_812(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a1__, b1__, c__, a2__, m_, n_, p_, x_, b2__);
    rules.push(rubi_rule!(
        order: 812,
        source: "Int[(c_.*x_)^m_.*(a1_+b1_.*x_^n_)^p_*(a2_+b2_.*x_^n_)^p_,x_Symbol] :=
          (c*x)^(m+1)*(a1+b1*x^n)^p*(a2+b2*x^n)^p/(c*(m+2*n*p+1)) +
          2*a1*a2*n*p/(m+2*n*p+1) \\[Star] Int[(c*x)^m*(a1+b1*x^n)^(p-1)*(a2+b2*x^n)^(p-1),x] /;
        FreeQ[{a1,b1,a2,b2,c,m},x] && EqQ[a2*b1+a1*b2,0] && IGtQ[2*n,0] && GtQ[p,0] && NeQ[m+2*n*p+1,0] && IntBinomialQ[a1*a2,b1*b2,c,2*n,m,p,x]",
        desc: "Inverted integration by parts",
        refs: ["G&R 2.110.1, CRC 88b"],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a1__, b1__, c__, a2__, b2__, m_, n_, p_, x_],
        optional: [b1__, c__, b2__, m_],
        when: {
            freeq!([a1__, b1__, a2__, b2__, c__, m_], x_)
                && eqq!(&a2__ * &b1__ + &a1__ * &b2__, 0)
                && igtq!(Atom::num(2) * &n_, 0)
                && gtq!(p_, 0)
                && neq!(&m_ + Atom::num(2) * &n_ * &p_ + Atom::num(1), 0)
                && rubi_int_binomial_q(
                    &(&a1__ * &a2__),
                    &(&b1__ * &b2__),
                    &c__,
                    &(Atom::num(2) * &n_),
                    &m_,
                    &p_,
                    x_
                )
        },
        rhs: {
            let denominator = &m_ + Atom::num(2) * &n_ * &p_ + Atom::num(1);
            let scaled = &c__ * x_;
            let monomial = x_.pow(&n_);
            let first = &a1__ + &b1__ * &monomial;
            let second = &a2__ + &b2__ * monomial;
            let direct = scaled.pow(&m_ + Atom::num(1)) * first.pow(&p_) * second.pow(&p_)
                / (&c__ * &denominator);
            let recurrence_factor = Atom::num(2) * &a1__ * &a2__ * &n_ * &p_ / &denominator;
            let recursive_integrand =
                scaled.pow(&m_) * first.pow(&p_ - Atom::num(1)) * second.pow(&p_ - Atom::num(1));
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) + rubi_star(recurrence_factor, recursive)
        },
    ));
}

fn push_rules_rule_813(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, x_);
    rules.push(rubi_rule!(
        order: 813,
        source: "Int[x_^2/(a_+b_.*x_^4)^(5/4),x_Symbol] :=
          x*(1+a/(b*x^4))^(1/4)/(b*(a+b*x^4)^(1/4)) \\[Star] Int[1/(x^3*(1+a/(b*x^4))^(5/4)),x] /;
        FreeQ[{a,b},x] && PosQ[b/a]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [a__, b__, x_],
        optional: [b__],
        when: { freeq!([a__, b__], x_) && posq!((&b__ / &a__).expand()) },
        rhs: {
            let base = &a__ + &b__ * x_.pow(4);
            let normalized_base = Atom::num(1) + &a__ / (&b__ * x_.pow(4));
            let recursive_integrand =
                Atom::num(1) / (x_.pow(3) * normalized_base.pow((5, 4)));
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let multiplier = x_ * normalized_base.pow((1, 4))
                / (&b__ * base.pow((1, 4)));

            rubi_star(multiplier, recursive)
        },
    ));
}

fn push_rules_rule_815(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, x_);
    rules.push(rubi_rule!(
        order: 815,
        source: "Int[x_^m_/(a_+b_.*x_^4)^(5/4),x_Symbol] :=
          x^(m-3)/(b*(m-4)*(a+b*x^4)^(1/4)) - a*(m-3)/(b*(m-4)) \\[Star] Int[x^(m-4)/(a+b*x^4)^(5/4),x] /;
        FreeQ[{a,b},x] && PosQ[b/a] && IGtQ[(m-2)/4,0]",
        desc: "Inverted integration by parts",
        refs: ["G&R 2.110.5, CRC 88a"],
        pattern:  rubi_shared_pattern_10(symbols),
        with: [a__, b__, m_, x_],
        optional: [b__],
        when: {
            freeq!([a__, b__], x_)
                && posq!((&b__ / &a__).expand())
                && igtq!(((&m_ - Atom::num(2)) / Atom::num(4)).expand(), 0)
        },
        rhs: {
            let denominator_factor = &m_ - Atom::num(4);
            let base = &a__ + &b__ * x_.pow(4);
            let direct = x_.pow(&m_ - Atom::num(3))
                / (&b__ * &denominator_factor * base.pow((1, 4)));
            let recurrence_factor =
                &a__ * (&m_ - Atom::num(3)) / (&b__ * &denominator_factor);
            let recursive_integrand =
                x_.pow(&m_ - Atom::num(4)) / base.pow((5, 4));
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) - rubi_star(recurrence_factor, recursive)
        },
    ));
}

fn push_rules_rule_816(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, x_);
    rules.push(rubi_rule!(
        order: 816,
        source: "Int[x_^m_/(a_+b_.*x_^4)^(5/4),x_Symbol] :=
          x^(m+1)/(a*(m+1)*(a+b*x^4)^(1/4)) - b*m/(a*(m+1)) \\[Star] Int[x^(m+4)/(a+b*x^4)^(5/4),x] /;
        FreeQ[{a,b},x] && PosQ[b/a] && ILtQ[(m-2)/4,0]",
        desc: "Integration by parts",
        refs: ["G&R 2.110.6, CRC 88c"],
        pattern:  rubi_shared_pattern_10(symbols),
        with: [a__, b__, m_, x_],
        optional: [b__],
        when: {
            freeq!([a__, b__], x_)
                && posq!((&b__ / &a__).expand())
                && iltq!(((&m_ - Atom::num(2)) / Atom::num(4)).expand(), 0)
        },
        rhs: {
            let denominator_factor = &m_ + Atom::num(1);
            let base = &a__ + &b__ * x_.pow(4);
            let direct = x_.pow(&m_ + Atom::num(1))
                / (&a__ * &denominator_factor * base.pow((1, 4)));
            let recurrence_factor = &b__ * &m_ / (&a__ * &denominator_factor);
            let recursive_integrand =
                x_.pow(&m_ + Atom::num(4)) / base.pow((5, 4));
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) - rubi_star(recurrence_factor, recursive)
        },
    ));
}

fn push_rules_rule_814(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, x_);
    rules.push(rubi_rule!(
        order: 814,
        source: "Int[x_^2/(a_+b_.*x_^4)^(5/4),x_Symbol] :=
          -1/(b*x*(a+b*x^4)^(1/4)) - 1/b \\[Star] Int[1/(x^2*(a+b*x^4)^(1/4)),x] /;
        FreeQ[{a,b},x] && NegQ[b/a]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [a__, b__, x_],
        optional: [b__],
        when: { freeq!([a__, b__], x_) && negq!((&b__ / &a__).expand()) },
        rhs: {
            let base = &a__ + &b__ * x_.pow(4);
            let recursive_integrand = Atom::num(1) / (x_.pow(2) * base.pow((1, 4)));
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(-Atom::num(1) / (&b__ * x_ * base.pow((1, 4)))), x_)
                    - rubi_star(Atom::num(1) / &b__, recursive)
        },
    ));
}

fn push_rules_rule_817(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 817,
        source: "Int[(c_.*x_)^m_.*(a_+b_.*x_^n_)^p_,x_Symbol] :=
          c^(n-1)*(c*x)^(m-n+1)*(a+b*x^n)^(p+1)/(b*n*(p+1)) -
          c^n*(m-n+1)/(b*n*(p+1)) \\[Star] Int[(c*x)^(m-n)*(a+b*x^n)^(p+1),x] /;
        FreeQ[{a,b,c},x] && IGtQ[n,0] && LtQ[p,-1] && GtQ[m+1,n] && Not[ILtQ[(m+n*(p+1)+1)/n,0]] && IntBinomialQ[a,b,c,n,m,p,x]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, m_, n_, p_, x_],
        optional: [b__, c__, m_],
        when: {
            freeq!([a__, b__, c__], x_)
                && igtq!(n_, 0)
                && ltq!(p_, -1)
                && gtq!(&m_ + Atom::num(1), n_)
                && !iltq!((&m_ + &n_ * (&p_ + Atom::num(1)) + Atom::num(1)) / &n_, 0)
                && rubi_int_binomial_q(&a__, &b__, &c__, &n_, &m_, &p_, x_)
        },
        rhs: {
            let p1 = &p_ + Atom::num(1);
            let denominator = &b__ * &n_ * &p1;
            let scaled = &c__ * x_;
            let binomial = &a__ + &b__ * x_.pow(&n_);
            let direct = c__.pow(&n_ - Atom::num(1))
                * scaled.pow(&m_ - &n_ + Atom::num(1))
                * binomial.pow(&p1)
                / &denominator;
            let recurrence_factor =
                c__.pow(&n_) * (&m_ - &n_ + Atom::num(1)) / &denominator;
            let recursive_integrand =
                scaled.pow(&m_ - &n_) * binomial.pow(&p1);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) - rubi_star(recurrence_factor, recursive)
        },
    ));
}

fn push_rules_rule_818(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a1__, b1__, c__, a2__, m_, n_, p_, x_, b2__);
    rules.push(rubi_rule!(
        order: 818,
        source: "Int[(c_.*x_)^m_.*(a1_+b1_.*x_^n_)^p_*(a2_+b2_.*x_^n_)^p_,x_Symbol] :=
          c^(2*n-1)*(c*x)^(m-2*n+1)*(a1+b1*x^n)^(p+1)*(a2+b2*x^n)^(p+1)/(2*b1*b2*n*(p+1)) -
          c^(2*n)*(m-2*n+1)/(2*b1*b2*n*(p+1)) \\[Star] Int[(c*x)^(m-2*n)*(a1+b1*x^n)^(p+1)*(a2+b2*x^n)^(p+1),x] /;
        FreeQ[{a1,b1,a2,b2,c},x] && EqQ[a2*b1+a1*b2,0] && IGtQ[2*n,0] && LtQ[p,-1] && m+1>2*n &&
          Not[ILtQ[(m+2*n*(p+1)+1)/(2*n),0]] && IntBinomialQ[a1*a2,b1*b2,c,2*n,m,p,x]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a1__, b1__, c__, a2__, b2__, m_, n_, p_, x_],
        optional: [b1__, c__, b2__, m_],
        when: {
            freeq!([a1__, b1__, a2__, b2__, c__], x_)
                && eqq!(&a2__ * &b1__ + &a1__ * &b2__, 0)
                && igtq!(Atom::num(2) * &n_, 0)
                && ltq!(p_, -1)
                && is_number_greater_than_atom(
                    &(&m_ + Atom::num(1)),
                    &(Atom::num(2) * &n_)
                )
                && !iltq!(
                    (&m_ + Atom::num(2) * &n_ * (&p_ + Atom::num(1)) + Atom::num(1))
                        / (Atom::num(2) * &n_),
                    0
                )
                && rubi_int_binomial_q(
                    &(&a1__ * &a2__),
                    &(&b1__ * &b2__),
                    &c__,
                    &(Atom::num(2) * &n_),
                    &m_,
                    &p_,
                    x_
                )
        },
        rhs: {
            let p1 = &p_ + Atom::num(1);
            let denominator = Atom::num(2) * &b1__ * &b2__ * &n_ * &p1;
            let scaled = &c__ * x_;
            let monomial = x_.pow(&n_);
            let first = &a1__ + &b1__ * &monomial;
            let second = &a2__ + &b2__ * monomial;
            let direct = c__.pow(Atom::num(2) * &n_ - Atom::num(1))
                * scaled.pow(&m_ - Atom::num(2) * &n_ + Atom::num(1))
                * first.pow(&p1)
                * second.pow(&p1)
                / &denominator;
            let recurrence_factor = c__.pow(Atom::num(2) * &n_)
                * (&m_ - Atom::num(2) * &n_ + Atom::num(1))
                / &denominator;
            let recursive_integrand = scaled.pow(&m_ - Atom::num(2) * &n_)
                * first.pow(&p1)
                * second.pow(&p1);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) - rubi_star(recurrence_factor, recursive)
        },
    ));
}

fn push_rules_rule_819(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 819,
        source: "Int[(c_.*x_)^m_.*(a_+b_.*x_^n_)^p_,x_Symbol] :=
          -(c*x)^(m+1)*(a+b*x^n)^(p+1)/(a*c*n*(p+1)) +
          (m+n*(p+1)+1)/(a*n*(p+1)) \\[Star] Int[(c*x)^m*(a+b*x^n)^(p+1),x] /;
        FreeQ[{a,b,c,m},x] && IGtQ[n,0] && LtQ[p,-1] && IntBinomialQ[a,b,c,n,m,p,x]",
        desc: "Integration by parts",
        refs: ["G&R 2.110.2, CRC 88d"],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, m_, n_, p_, x_],
        optional: [b__, c__, m_],
        when: {
            freeq!([a__, b__, c__, m_], x_)
                && igtq!(n_, 0)
                && ltq!(p_, -1)
                && rubi_int_binomial_q(&a__, &b__, &c__, &n_, &m_, &p_, x_)
        },
        rhs: {
            let p1 = &p_ + Atom::num(1);
            let scaled = &c__ * x_;
            let binomial = &a__ + &b__ * x_.pow(&n_);
            let direct = -scaled.pow(&m_ + Atom::num(1)) * binomial.pow(&p1)
                / (&a__ * &c__ * &n_ * &p1);
            let recurrence_factor =
                (&m_ + &n_ * &p1 + Atom::num(1)) / (&a__ * &n_ * &p1);
            let recursive_integrand = scaled.pow(&m_) * binomial.pow(&p1);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) + rubi_star(recurrence_factor, recursive)
        },
    ));
}

fn push_rules_rule_820(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a1__, b1__, c__, a2__, m_, n_, p_, x_, b2__);
    rules.push(rubi_rule!(
        order: 820,
        source: "Int[(c_.*x_)^m_.*(a1_+b1_.*x_^n_)^p_*(a2_+b2_.*x_^n_)^p_,x_Symbol] :=
          -(c*x)^(m+1)*(a1+b1*x^n)^(p+1)*(a2+b2*x^n)^(p+1)/(2*a1*a2*c*n*(p+1)) +
          (m+2*n*(p+1)+1)/(2*a1*a2*n*(p+1)) \\[Star] Int[(c*x)^m*(a1+b1*x^n)^(p+1)*(a2+b2*x^n)^(p+1),x] /;
        FreeQ[{a1,b1,a2,b2,c,m},x] && EqQ[a2*b1+a1*b2,0] && IGtQ[2*n,0] && LtQ[p,-1] && IntBinomialQ[a1*a2,b1*b2,c,2*n,m,p,x]",
        desc: "Integration by parts",
        refs: ["G&R 2.110.2, CRC 88d"],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a1__, b1__, c__, a2__, b2__, m_, n_, p_, x_],
        optional: [b1__, c__, b2__, m_],
        when: {
            freeq!([a1__, b1__, a2__, b2__, c__, m_], x_)
                && eqq!(&a2__ * &b1__ + &a1__ * &b2__, 0)
                && igtq!(Atom::num(2) * &n_, 0)
                && ltq!(p_, -1)
                && rubi_int_binomial_q(
                    &(&a1__ * &a2__),
                    &(&b1__ * &b2__),
                    &c__,
                    &(Atom::num(2) * &n_),
                    &m_,
                    &p_,
                    x_
                )
        },
        rhs: {
            let p1 = &p_ + Atom::num(1);
            let scaled = &c__ * x_;
            let monomial = x_.pow(&n_);
            let first = &a1__ + &b1__ * &monomial;
            let second = &a2__ + &b2__ * monomial;
            let direct = -scaled.pow(&m_ + Atom::num(1))
                * first.pow(&p1)
                * second.pow(&p1)
                / (Atom::num(2) * &a1__ * &a2__ * &c__ * &n_ * &p1);
            let recurrence_factor =
                (&m_ + Atom::num(2) * &n_ * &p1 + Atom::num(1))
                    / (Atom::num(2) * &a1__ * &a2__ * &n_ * &p1);
            let recursive_integrand = scaled.pow(&m_) * first.pow(&p1) * second.pow(&p1);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) + rubi_star(recurrence_factor, recursive)
        },
    ));
}

fn push_rules_rule_821(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, x_);
    rules.push(rubi_rule!(
        order: 821,
        source: "Int[x_/(a_+b_.*x_^3),x_Symbol] :=
          -1/(3*Rt[a,3]*Rt[b,3]) \\[Star] Int[1/(Rt[a,3]+Rt[b,3]*x),x] +
          1/(3*Rt[a,3]*Rt[b,3]) \\[Star] Int[(Rt[a,3]+Rt[b,3]*x)/(Rt[a,3]^2-Rt[a,3]*Rt[b,3]*x+Rt[b,3]^2*x^2),x] /;
        FreeQ[{a,b},x]",
        desc: "Algebraic expansion",
        refs: ["G&R 2.126.2, CRC 75"],
        pattern: x_ / (a__ + b__ * x_.pow(3)),
        with: [a__, b__, x_],
        optional: [b__],
        when: { freeq!([a__, b__], x_) },
        rhs: {
            let rt_a = rubi_rt(&a__, 3);
            let rt_b = rubi_rt(&b__, 3);
            let denominator = Atom::num(3) * &rt_a * &rt_b;
            let linear_integrand = Atom::num(1) / (&rt_a + &rt_b * x_);
            let quadratic_denominator =
                rt_a.pow(2) - &rt_a * &rt_b * x_ + rt_b.pow(2) * x_.pow(2);
            let quadratic_numerator = &rt_a + &rt_b * x_;
            let quadratic_integrand = &quadratic_numerator / &quadratic_denominator;
            let linear = rubi_rhs_int(&linear_integrand, x_);
            let quadratic = rubi_rhs_int(&quadratic_integrand, x_);

            rubi_star(-Atom::num(1) / &denominator, linear)
                    + rubi_star(Atom::num(1) / denominator, quadratic)
        },
    ));
}

fn push_rules_rule_822(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 822,
        source: "Int[x_^m_./(a_+b_.*x_^n_),x_Symbol] :=
          Module[{r=Numerator[Rt[a/b,n]], s=Denominator[Rt[a/b,n]], k, u},
          u=Int[(r*Cos[(2*k-1)*m*Pi/n]-s*Cos[(2*k-1)*(m+1)*Pi/n]*x)/(r^2-2*r*s*Cos[(2*k-1)*Pi/n]*x+s^2*x^2),x];
          -(-r)^(m+1)/(a*n*s^m) \\[Star] Int[1/(r+s*x),x] + 2*r^(m+1)/(a*n*s^m) \\[Star] Sum[u,{k,1,(n-1)/2}]] /;
        FreeQ[{a,b},x] && IGtQ[(n-1)/2,0] && IGtQ[m,0] && LtQ[m,n-1] && PosQ[a/b]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern:  rubi_shared_pattern_11(symbols),
        with: [a__, b__, m_, n_, x_],
        optional: [b__, m_],
        when: {
            freeq!([a__, b__], x_)
                && igtq!((&n_ - Atom::num(1)) / Atom::num(2), 0)
                && igtq!(m_, 0)
                && ltq!(m_, &n_ - Atom::num(1))
                && posq!((&a__ / &b__).expand())
        },
        rhs: {
            let n_i64 = integer_i64(&n_).rubi_rhs();
            let root = rubi_rt(&(&a__ / &b__), n_i64);
            let r = rubi_numerator(&root);
            let s = rubi_denominator_atom(&root);
            let denominator = &a__ * &n_ * s.pow(&m_);
            let linear_integrand = Atom::num(1) / (&r + x_);
            let linear = rubi_rhs_int(&linear_integrand, x_);
            let pi = Atom::var(Symbol::PI);
            let mut sum = Atom::num(0);
            for k in 1..=((n_i64 - 1) / 2) {
                let odd = Atom::num(2 * k - 1);
                let numerator = &r * (&odd * &m_ * &pi / &n_).cos()
                    - &s
                        * (&odd * (&m_ + Atom::num(1)) * &pi / &n_).cos()
                        * x_;
                let quadratic_denominator = r.pow(2)
                    - Atom::num(2) * &r * &s * (odd * &pi / &n_).cos() * x_
                    + s.pow(2) * x_.pow(2);
                sum += rubi_rhs_int(&(numerator / quadratic_denominator), x_);
            }
            let first_coefficient = -(-&r).pow(&m_ + Atom::num(1)) / &denominator;
            let second_coefficient =
                Atom::num(2) * r.pow(&m_ + Atom::num(1)) / denominator;
            rubi_star(first_coefficient, linear)
                    + rubi_star(second_coefficient, sum)
        },
    ));
}

fn push_rules_rule_823(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 823,
        source: "Int[x_^m_./(a_+b_.*x_^n_),x_Symbol] :=
          Module[{r=Numerator[Rt[-a/b,n]], s=Denominator[Rt[-a/b,n]], k, u},
          u=Int[(r*Cos[(2*k-1)*m*Pi/n]+s*Cos[(2*k-1)*(m+1)*Pi/n]*x)/(r^2+2*r*s*Cos[(2*k-1)*Pi/n]*x+s^2*x^2),x];
          r^(m+1)/(a*n*s^m) \\[Star] Int[1/(r-s*x),x] - 2*(-r)^(m+1)/(a*n*s^m) \\[Star] Sum[u,{k,1,(n-1)/2}]] /;
        FreeQ[{a,b},x] && IGtQ[(n-1)/2,0] && IGtQ[m,0] && LtQ[m,n-1] && NegQ[a/b]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern:  rubi_shared_pattern_11(symbols),
        with: [a__, b__, m_, n_, x_],
        optional: [b__, m_],
        when: {
            freeq!([a__, b__], x_)
                && igtq!((&n_ - Atom::num(1)) / Atom::num(2), 0)
                && igtq!(m_, 0)
                && ltq!(m_, &n_ - Atom::num(1))
                && negq!((&a__ / &b__).expand())
        },
        rhs: {
            let n_i64 = integer_i64(&n_).rubi_rhs();
            let root = rubi_rt(&(-&a__ / &b__), n_i64);
            let r = rubi_numerator(&root);
            let s = rubi_denominator_atom(&root);
            let denominator = &a__ * &n_ * s.pow(&m_);
            let linear_integrand = Atom::num(1) / (&r - x_);
            let linear = rubi_rhs_int(&linear_integrand, x_);
            let pi = Atom::var(Symbol::PI);
            let mut sum = Atom::num(0);
            for k in 1..=((n_i64 - 1) / 2) {
                let odd = Atom::num(2 * k - 1);
                let numerator = &r * (&odd * &m_ * &pi / &n_).cos()
                    + &s
                        * (&odd * (&m_ + Atom::num(1)) * &pi / &n_).cos()
                        * x_;
                let quadratic_denominator = r.pow(2)
                    + Atom::num(2) * &r * &s * (odd * &pi / &n_).cos() * x_
                    + s.pow(2) * x_.pow(2);
                sum += rubi_rhs_int(&(numerator / quadratic_denominator), x_);
            }
            let first_coefficient = r.pow(&m_ + Atom::num(1)) / &denominator;
            let second_coefficient =
                -Atom::num(2) * (-&r).pow(&m_ + Atom::num(1)) / denominator;
            rubi_star(first_coefficient, linear)
                    + rubi_star(second_coefficient, sum)
        },
    ));
}

fn push_rules_rule_824(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 824,
        source: "Int[x_^m_./(a_+b_.*x_^n_),x_Symbol] :=
          Module[{r=Numerator[Rt[a/b,n]], s=Denominator[Rt[a/b,n]], k, u},
          u=Int[(r*Cos[(2*k-1)*m*Pi/n]-s*Cos[(2*k-1)*(m+1)*Pi/n]*x)/(r^2-2*r*s*Cos[(2*k-1)*Pi/n]*x+s^2*x^2),x] +
            Int[(r*Cos[(2*k-1)*m*Pi/n]+s*Cos[(2*k-1)*(m+1)*Pi/n]*x)/(r^2+2*r*s*Cos[(2*k-1)*Pi/n]*x+s^2*x^2),x];
          2*(-1)^(m/2)*r^(m+2)/(a*n*s^m) \\[Star] Int[1/(r^2+s^2*x^2),x] + 2*r^(m+1)/(a*n*s^m) \\[Star] Sum[u,{k,1,(n-2)/4}]] /;
         FreeQ[{a,b},x] && IGtQ[(n-2)/4,0] && IGtQ[m,0] && LtQ[m,n-1] && PosQ[a/b]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern:  rubi_shared_pattern_11(symbols),
        with: [a__, b__, m_, n_, x_],
        optional: [b__, m_],
        when: {
            freeq!([a__, b__], x_)
                && igtq!((&n_ - Atom::num(2)) / Atom::num(4), 0)
                && igtq!(m_, 0)
                && ltq!(m_, &n_ - Atom::num(1))
                && posq!((&a__ / &b__).expand())
        },
        rhs: {
            let n_i64 = integer_i64(&n_).rubi_rhs();
            let root = rubi_rt(&(&a__ / &b__), n_i64);
            let r = rubi_numerator(&root);
            let s = rubi_denominator_atom(&root);
            let r2 = r.pow(2);
            let s2 = s.pow(2);
            let denominator = &a__ * &n_ * s.pow(&m_);
            let base_integrand = Atom::num(1) / (&r2 + &s2 * x_.pow(2));
            let base = rubi_rhs_int(&base_integrand, x_);
            let pi = Atom::var(Symbol::PI);
            let mut sum = Atom::num(0);
            for k in 1..=((n_i64 - 2) / 4) {
                let odd = Atom::num(2 * k - 1);
                let cosine = (&odd * &pi / &n_).cos();
                let first_numerator = &r * (&odd * &m_ * &pi / &n_).cos()
                    - &s
                        * (&odd * (&m_ + Atom::num(1)) * &pi / &n_).cos()
                        * x_;
                let first_denominator = &r2
                    - Atom::num(2) * &r * &s * &cosine * x_
                    + &s2 * x_.pow(2);
                let first = rubi_rhs_int(&(first_numerator / first_denominator), x_);
                let second_numerator = &r * (&odd * &m_ * &pi / &n_).cos()
                    + &s * (odd * (&m_ + Atom::num(1)) * &pi / &n_).cos() * x_;
                let second_denominator = &r2
                    + Atom::num(2) * &r * &s * cosine * x_
                    + &s2 * x_.pow(2);
                let second = rubi_rhs_int(&(second_numerator / second_denominator), x_);
                sum += first + second;
            }
            let first_coefficient = Atom::num(2)
                * Atom::num(-1).pow(&m_ / Atom::num(2))
                * r.pow(&m_ + Atom::num(2))
                / &denominator;
            let second_coefficient =
                Atom::num(2) * r.pow(&m_ + Atom::num(1)) / denominator;
            rubi_star(first_coefficient, base)
                    + rubi_star(second_coefficient, sum)
        },
    ));
}

fn push_rules_rule_825(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 825,
        source: "Int[x_^m_./(a_+b_.*x_^n_),x_Symbol] :=
          Module[{r=Numerator[Rt[-a/b,n]], s=Denominator[Rt[-a/b,n]], k, u},
          u=Int[(r*Cos[2*k*m*Pi/n]-s*Cos[2*k*(m+1)*Pi/n]*x)/(r^2-2*r*s*Cos[2*k*Pi/n]*x+s^2*x^2),x] +
            Int[(r*Cos[2*k*m*Pi/n]+s*Cos[2*k*(m+1)*Pi/n]*x)/(r^2+2*r*s*Cos[2*k*Pi/n]*x+s^2*x^2),x];
          2*r^(m+2)/(a*n*s^m) \\[Star] Int[1/(r^2-s^2*x^2),x] + 2*r^(m+1)/(a*n*s^m) \\[Star] Sum[u,{k,1,(n-2)/4}]] /;
         FreeQ[{a,b},x] && IGtQ[(n-2)/4,0] && IGtQ[m,0] && LtQ[m,n-1] && NegQ[a/b]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern:  rubi_shared_pattern_11(symbols),
        with: [a__, b__, m_, n_, x_],
        optional: [b__, m_],
        when: {
            freeq!([a__, b__], x_)
                && igtq!((&n_ - Atom::num(2)) / Atom::num(4), 0)
                && igtq!(m_, 0)
                && ltq!(m_, &n_ - Atom::num(1))
                && negq!((&a__ / &b__).expand())
        },
        rhs: {
            let n_i64 = integer_i64(&n_).rubi_rhs();
            let root = rubi_rt(&(-&a__ / &b__), n_i64);
            let r = rubi_numerator(&root);
            let s = rubi_denominator_atom(&root);
            let r2 = r.pow(2);
            let s2 = s.pow(2);
            let denominator = &a__ * &n_ * s.pow(&m_);
            let base_integrand = Atom::num(1) / (&r2 - &s2 * x_.pow(2));
            let base = rubi_rhs_int(&base_integrand, x_);
            let pi = Atom::var(Symbol::PI);
            let mut sum = Atom::num(0);
            for k in 1..=((n_i64 - 2) / 4) {
                let even = Atom::num(2 * k);
                let cosine = (&even * &pi / &n_).cos();
                let first_numerator = &r * (&even * &m_ * &pi / &n_).cos()
                    - &s
                        * (&even * (&m_ + Atom::num(1)) * &pi / &n_).cos()
                        * x_;
                let first_denominator = &r2
                    - Atom::num(2) * &r * &s * &cosine * x_
                    + &s2 * x_.pow(2);
                let first = rubi_rhs_int(&(first_numerator / first_denominator), x_);
                let second_numerator = &r * (&even * &m_ * &pi / &n_).cos()
                    + &s * (even * (&m_ + Atom::num(1)) * &pi / &n_).cos() * x_;
                let second_denominator = &r2
                    + Atom::num(2) * &r * &s * cosine * x_
                    + &s2 * x_.pow(2);
                let second = rubi_rhs_int(&(second_numerator / second_denominator), x_);
                sum += first + second;
            }
            let first_coefficient =
                Atom::num(2) * r.pow(&m_ + Atom::num(2)) / &denominator;
            let second_coefficient =
                Atom::num(2) * r.pow(&m_ + Atom::num(1)) / denominator;
            rubi_star(first_coefficient, base)
                    + rubi_star(second_coefficient, sum)
        },
    ));
}

fn push_rules_rule_826(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, x_);
    rules.push(rubi_rule!(
        order: 826,
        source: "Int[x_^2/(a_+b_.*x_^4),x_Symbol] :=
          With[{r=Numerator[Rt[a/b,2]], s=Denominator[Rt[a/b,2]]},
          1/(2*s) \\[Star] Int[(r+s*x^2)/(a+b*x^4),x] -
          1/(2*s) \\[Star] Int[(r-s*x^2)/(a+b*x^4),x]] /;
        FreeQ[{a,b},x] && (GtQ[a/b,0] || PosQ[a/b] && AtomQ[SplitProduct[SumBaseQ,a]] && AtomQ[SplitProduct[SumBaseQ,b]])",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, b__, x_],
        optional: [b__],
        when: {
            let ratio = (&a__ / &b__).expand();
            freeq!([a__, b__], x_)
                && (gtq!(ratio, 0)
                    || posq!(ratio)
                        && rubi_atomq_split_product_sum_base(&a__)
                        && rubi_atomq_split_product_sum_base(&b__))
        },
        rhs: {
            let root = rubi_rt(&(&a__ / &b__), 2);
            let r = rubi_numerator(&root);
            let s = rubi_denominator_atom(&root);
            let denominator = &a__ + &b__ * x_.pow(4);
            let first_integrand = (&r + &s * x_.pow(2)) / &denominator;
            let second_integrand = (&r - &s * x_.pow(2)) / denominator;
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);
            let coefficient = Atom::num(1) / (Atom::num(2) * &s);

            rubi_star(&coefficient, first) - rubi_star(coefficient, second)
        },
    ));
}

fn push_rules_rule_827(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, x_);
    rules.push(rubi_rule!(
        order: 827,
        source: "Int[x_^2/(a_+b_.*x_^4),x_Symbol] :=
          With[{r=Numerator[Rt[-a/b,2]], s=Denominator[Rt[-a/b,2]]},
          s/(2*b) \\[Star] Int[1/(r+s*x^2),x] -
          s/(2*b) \\[Star] Int[1/(r-s*x^2),x]] /;
        FreeQ[{a,b},x] && Not[GtQ[a/b,0]]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, b__, x_],
        optional: [b__],
        when: { freeq!([a__, b__], x_) && !gtq!((&a__ / &b__).expand(), 0) },
        rhs: {
            let root = rubi_rt(&(-&a__ / &b__), 2);
            let r = rubi_numerator(&root);
            let s = rubi_denominator_atom(&root);
            let first_integrand = Atom::num(1) / (&r + &s * x_.pow(2));
            let second_integrand = Atom::num(1) / (&r - &s * x_.pow(2));
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);
            let coefficient = &s / (Atom::num(2) * &b__);

            rubi_star(&coefficient, first) - rubi_star(coefficient, second)
        },
    ));
}

fn push_rules_rule_828(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 828,
        source: "Int[x_^m_./(a_+b_.*x_^n_),x_Symbol] :=
          With[{r=Numerator[Rt[a/b,4]], s=Denominator[Rt[a/b,4]]},
          s^3/(2*Sqrt[2]*b*r) \\[Star] Int[x^(m-n/4)/(r^2-Sqrt[2]*r*s*x^(n/4)+s^2*x^(n/2)),x] -
          s^3/(2*Sqrt[2]*b*r) \\[Star] Int[x^(m-n/4)/(r^2+Sqrt[2]*r*s*x^(n/4)+s^2*x^(n/2)),x]] /;
        FreeQ[{a,b},x] && IGtQ[n/4,0] && IGtQ[m,0] && LtQ[m,n-1] && GtQ[a/b,0]",
        desc: "Algebraic expansion",
        refs: ["G&R 2.132.3.1', CRC 81'"],
        pattern:  rubi_shared_pattern_11(symbols),
        with: [a__, b__, m_, n_, x_],
        optional: [b__, m_],
        when: {
            freeq!([a__, b__], x_)
                && igtq!(&n_ / Atom::num(4), 0)
                && igtq!(m_, 0)
                && ltq!(m_, &n_ - Atom::num(1))
                && gtq!((&a__ / &b__).expand(), 0)
        },
        rhs: {
            let root = rubi_rt(&(&a__ / &b__), 4);
            let r = rubi_numerator(&root);
            let s = rubi_denominator_atom(&root);
            let sqrt_two = Atom::num(2).sqrt();
            let exponent = &m_ - &n_ / Atom::num(4);
            let x_n_over_4 = x_.pow(&n_ / Atom::num(4));
            let x_n_over_2 = x_.pow(&n_ / Atom::num(2));
            let first_denominator = r.pow(2) - &sqrt_two * &r * &s * &x_n_over_4
                + s.pow(2) * &x_n_over_2;
            let second_denominator = r.pow(2)
                + &sqrt_two * &r * &s * &x_n_over_4
                + s.pow(2) * &x_n_over_2;
            let first_integrand = x_.pow(&exponent) / &first_denominator;
            let second_integrand = x_.pow(&exponent) / &second_denominator;
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);
            let coefficient = s.pow(3) / (Atom::num(2) * sqrt_two * &b__ * &r);

            rubi_star(&coefficient, first) - rubi_star(coefficient, second)
        },
    ));
}

fn push_rules_rule_829(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 829,
        source: "Int[x_^m_/(a_+b_.*x_^n_),x_Symbol] :=
          With[{r=Numerator[Rt[-a/b,2]], s=Denominator[Rt[-a/b,2]]},
          r/(2*a) \\[Star] Int[x^m/(r+s*x^(n/2)),x] +
          r/(2*a) \\[Star] Int[x^m/(r-s*x^(n/2)),x]] /;
        FreeQ[{a,b},x] && IGtQ[n/4,0] && IGtQ[m,0] && LtQ[m,n/2] && Not[GtQ[a/b,0]]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern:  rubi_shared_pattern_11(symbols),
        with: [a__, b__, m_, n_, x_],
        optional: [b__],
        when: {
            freeq!([a__, b__], x_)
                && igtq!(&n_ / Atom::num(4), 0)
                && igtq!(m_, 0)
                && ltq!(m_, &n_ / Atom::num(2))
                && !gtq!((&a__ / &b__).expand(), 0)
        },
        rhs: {
            let root = rubi_rt(&(-&a__ / &b__), 2);
            let r = rubi_numerator(&root);
            let s = rubi_denominator_atom(&root);
            let x_n_over_2 = x_.pow(&n_ / Atom::num(2));
            let first_integrand = x_.pow(&m_) / (&r + &s * &x_n_over_2);
            let second_integrand = x_.pow(&m_) / (&r - &s * &x_n_over_2);
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);
            let coefficient = &r / (Atom::num(2) * &a__);

            rubi_star(&coefficient, first) + rubi_star(coefficient, second)
        },
    ));
}

fn push_rules_rule_830(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 830,
        source: "Int[x_^m_/(a_+b_.*x_^n_),x_Symbol] :=
          With[{r=Numerator[Rt[-a/b,2]], s=Denominator[Rt[-a/b,2]]},
          s/(2*b) \\[Star] Int[x^(m-n/2)/(r+s*x^(n/2)),x] -
          s/(2*b) \\[Star] Int[x^(m-n/2)/(r-s*x^(n/2)),x]] /;
        FreeQ[{a,b},x] && IGtQ[n/4,0] && IGtQ[m,0] && LeQ[n/2,m] && LtQ[m,n] && Not[GtQ[a/b,0]]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern:  rubi_shared_pattern_11(symbols),
        with: [a__, b__, m_, n_, x_],
        optional: [b__],
        when: {
            freeq!([a__, b__], x_)
                && igtq!(&n_ / Atom::num(4), 0)
                && igtq!(m_, 0)
                && leq!(&n_ / Atom::num(2), m_)
                && ltq!(m_, n_)
                && !gtq!((&a__ / &b__).expand(), 0)
        },
        rhs: {
            let root = rubi_rt(&(-&a__ / &b__), 2);
            let r = rubi_numerator(&root);
            let s = rubi_denominator_atom(&root);
            let reduced_m = &m_ - &n_ / Atom::num(2);
            let x_n_over_2 = x_.pow(&n_ / Atom::num(2));
            let first_integrand = x_.pow(&reduced_m) / (&r + &s * &x_n_over_2);
            let second_integrand = x_.pow(&reduced_m) / (&r - &s * &x_n_over_2);
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);
            let coefficient = &s / (Atom::num(2) * &b__);

            rubi_star(&coefficient, first) - rubi_star(coefficient, second)
        },
    ));
}

fn push_rules_rule_831(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 831,
        source: "Int[x_^m_/(a_+b_.*x_^n_),x_Symbol] :=
          Int[PolynomialDivide[x^m,(a+b*x^n),x],x] /;
        FreeQ[{a,b},x] && IGtQ[m,0] && IGtQ[n,0] && GtQ[m,2*n-1]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_11(symbols),
        with: [a__, b__, m_, n_, x_],
        optional: [b__],
        when: {
            freeq!([a__, b__], x_)
                && igtq!(m_, 0)
                && igtq!(n_, 0)
                && gtq!(m_, Atom::num(2) * &n_ - Atom::num(1))
        },
        rhs: {
            let numerator = x_.pow(&m_);
            let denominator = &a__ + &b__ * x_.pow(&n_);
            let divided = rubi_polynomial_divide(&numerator, &denominator, x_).rubi_rhs();
            rubi_rhs_int(&divided, x_)
        },
    ));
}

fn push_rules_rule_832(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, x_);
    rules.push(rubi_rule!(
        order: 832,
        source: "Int[x_/Sqrt[a_+b_.*x_^3],x_Symbol] :=
          With[{r=Numer[Rt[b/a,3]], s=Denom[Rt[b/a,3]]},
          -(1-Sqrt[3])*s/r \\[Star] Int[1/Sqrt[a+b*x^3],x] + 1/r \\[Star] Int[((1-Sqrt[3])*s+r*x)/Sqrt[a+b*x^3],x]] /;
        FreeQ[{a,b},x] && PosQ[a]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_12(symbols),
        with: [a__, b__, x_],
        optional: [b__],
        when: { freeq!([a__, b__], x_) && posq!(a__) },
        rhs: {
            let rt = rubi_rt(&(&b__ / &a__), 3);
            let r = rubi_numerator(&rt);
            let s = rubi_denominator_atom(&rt);
            let sqrt_three = Atom::num(3).sqrt();
            let base = &a__ + &b__ * x_.pow(3);
            let first_integrand = Atom::num(1) / base.sqrt();
            let second_integrand =
                ((Atom::num(1) - &sqrt_three) * &s + &r * x_) / base.sqrt();
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);
            let first_coefficient = -(Atom::num(1) - &sqrt_three) * &s / &r;
            let second_coefficient = Atom::num(1) / r;

            rubi_star(first_coefficient, first)
                    + rubi_star(second_coefficient, second)
        },
    ));
}

fn push_rules_rule_833(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, x_);
    rules.push(rubi_rule!(
        order: 833,
        source: "Int[x_/Sqrt[a_+b_.*x_^3],x_Symbol] :=
          With[{r=Numer[Rt[b/a,3]], s=Denom[Rt[b/a,3]]},
          -(1+Sqrt[3])*s/r \\[Star] Int[1/Sqrt[a+b*x^3],x] + 1/r \\[Star] Int[((1+Sqrt[3])*s+r*x)/Sqrt[a+b*x^3],x]] /;
        FreeQ[{a,b},x] && NegQ[a]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_12(symbols),
        with: [a__, b__, x_],
        optional: [b__],
        when: { freeq!([a__, b__], x_) && negq!(a__) },
        rhs: {
            let rt = rubi_rt(&(&b__ / &a__), 3);
            let r = rubi_numerator(&rt);
            let s = rubi_denominator_atom(&rt);
            let sqrt_three = Atom::num(3).sqrt();
            let base = &a__ + &b__ * x_.pow(3);
            let first_integrand = Atom::num(1) / base.sqrt();
            let second_integrand =
                ((Atom::num(1) + &sqrt_three) * &s + &r * x_) / base.sqrt();
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);
            let first_coefficient = -(Atom::num(1) + &sqrt_three) * &s / &r;
            let second_coefficient = Atom::num(1) / r;

            rubi_star(first_coefficient, first)
                    + rubi_star(second_coefficient, second)
        },
    ));
}

fn push_rules_rule_834(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, x_);
    rules.push(rubi_rule!(
        order: 834,
        source: "Int[x_^2/Sqrt[a_+b_.*x_^4],x_Symbol] :=
          With[{q=Rt[b/a,2]},
          1/q \\[Star] Int[1/Sqrt[a+b*x^4],x] - 1/q \\[Star] Int[(1-q*x^2)/Sqrt[a+b*x^4],x]] /;
        FreeQ[{a,b},x] && PosQ[b/a]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [a__, b__, x_],
        optional: [b__],
        when: { freeq!([a__, b__], x_) && posq!((&b__ / &a__).expand()) },
        rhs: {
            let q = rubi_rt(&(&b__ / &a__), 2);
            let base = &a__ + &b__ * x_.pow(4);
            let first_integrand = Atom::num(1) / base.sqrt();
            let second_integrand = (Atom::num(1) - &q * x_.pow(2)) / base.sqrt();
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);
            let coefficient = Atom::num(1) / q;

            rubi_star(&coefficient, first) - rubi_star(coefficient, second)
        },
    ));
}

fn push_rules_rule_835(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, x_);
    rules.push(rubi_rule!(
        order: 835,
        source: "Int[x_^2/Sqrt[a_+b_.*x_^4],x_Symbol] :=
          With[{q=Rt[-b/a,2]},
          1/q \\[Star] Int[1/Sqrt[a+b*x^4],x] - 1/q \\[Star] Int[(1-q*x^2)/Sqrt[a+b*x^4],x]] /;
        FreeQ[{a,b},x] && LtQ[a,0] && GtQ[b,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [a__, b__, x_],
        optional: [b__],
        when: { freeq!([a__, b__], x_) && ltq!(a__, 0) && gtq!(b__, 0) },
        rhs: {
            let q = rubi_rt(&(-&b__ / &a__), 2);
            let base = &a__ + &b__ * x_.pow(4);
            let first_integrand = Atom::num(1) / base.sqrt();
            let second_integrand = (Atom::num(1) - &q * x_.pow(2)) / base.sqrt();
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);
            let coefficient = Atom::num(1) / q;

            rubi_star(&coefficient, first) - rubi_star(coefficient, second)
        },
    ));
}

fn push_rules_rule_836(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, x_);
    rules.push(rubi_rule!(
        order: 836,
        source: "Int[x_^2/Sqrt[a_+b_.*x_^4],x_Symbol] :=
          With[{q=Rt[-b/a,2]},
          -1/q \\[Star] Int[1/Sqrt[a+b*x^4],x] + 1/q \\[Star] Int[(1+q*x^2)/Sqrt[a+b*x^4],x]] /;
        FreeQ[{a,b},x] && NegQ[b/a]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [a__, b__, x_],
        optional: [b__],
        when: { freeq!([a__, b__], x_) && negq!((&b__ / &a__).expand()) },
        rhs: {
            let q = rubi_rt(&(-&b__ / &a__), 2);
            let base = &a__ + &b__ * x_.pow(4);
            let first_integrand = Atom::num(1) / base.sqrt();
            let second_integrand = (Atom::num(1) + &q * x_.pow(2)) / base.sqrt();
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);
            let coefficient = Atom::num(1) / q;

            rubi_star(-(&coefficient), first) + rubi_star(coefficient, second)
        },
    ));
}

fn push_rules_rule_837(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, x_);
    rules.push(rubi_rule!(
        order: 837,
        source: "Int[x_^4/Sqrt[a_+b_.*x_^6],x_Symbol] :=
          With[{r=Numer[Rt[b/a,3]], s=Denom[Rt[b/a,3]]},
          (Sqrt[3]-1)*s^2/(2*r^2) \\[Star] Int[1/Sqrt[a+b*x^6],x] - 1/(2*r^2) \\[Star] Int[((Sqrt[3]-1)*s^2-2*r^2*x^4)/Sqrt[a+b*x^6],x]] /;
        FreeQ[{a,b},x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: x_.pow(4) / (a__ + b__ * x_.pow(6)).sqrt(),
        with: [a__, b__, x_],
        optional: [b__],
        when: { freeq!([a__, b__], x_) },
        rhs: {
            let rt = rubi_rt(&(&b__ / &a__), 3);
            let r = rubi_numerator(&rt);
            let s = rubi_denominator_atom(&rt);
            let sqrt_three = Atom::num(3).sqrt();
            let base = &a__ + &b__ * x_.pow(6);
            let first_integrand = Atom::num(1) / base.sqrt();
            let second_integrand =
                ((&sqrt_three - Atom::num(1)) * s.pow(2)
                    - Atom::num(2) * r.pow(2) * x_.pow(4))
                    / base.sqrt();
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);
            let first_coefficient =
                (&sqrt_three - Atom::num(1)) * s.pow(2) / (Atom::num(2) * r.pow(2));
            let second_coefficient = Atom::num(1) / (Atom::num(2) * r.pow(2));

            rubi_star(first_coefficient, first)
                    - rubi_star(second_coefficient, second)
        },
    ));
}

fn push_rules_rule_838(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, x_);
    rules.push(rubi_rule!(
        order: 838,
        source: "Int[x_^2/Sqrt[a_+b_.*x_^8],x_Symbol] :=
          1/(2*Rt[b/a,4]) \\[Star] Int[(1+Rt[b/a,4]*x^2)/Sqrt[a+b*x^8],x] -
          1/(2*Rt[b/a,4]) \\[Star] Int[(1-Rt[b/a,4]*x^2)/Sqrt[a+b*x^8],x] /;
        FreeQ[{a,b},x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: x_.pow(2) / (a__ + b__ * x_.pow(8)).sqrt(),
        with: [a__, b__, x_],
        optional: [b__],
        when: { freeq!([a__, b__], x_) },
        rhs: {
            let q = rubi_rt(&(&b__ / &a__), 4);
            let base = &a__ + &b__ * x_.pow(8);
            let first_integrand = (Atom::num(1) + &q * x_.pow(2)) / base.sqrt();
            let second_integrand = (Atom::num(1) - &q * x_.pow(2)) / base.sqrt();
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);
            let coefficient = Atom::num(1) / (Atom::num(2) * q);

            rubi_star(&coefficient, first) - rubi_star(coefficient, second)
        },
    ));
}

fn push_rules_rule_839(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, x_);
    rules.push(rubi_rule!(
        order: 839,
        source: "Int[x_^2/(a_+b_.*x_^4)^(1/4),x_Symbol] :=
          x^3/(2*(a+b*x^4)^(1/4)) - a/2 \\[Star] Int[x^2/(a+b*x^4)^(5/4),x] /;
        FreeQ[{a,b},x] && PosQ[b/a]",
        desc: "Binomial recurrence 1b",
        refs: ["G&R 2.110.1, CRC 88b"],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [a__, b__, x_],
        optional: [b__],
        when: { freeq!([a__, b__], x_) && posq!((&b__ / &a__).expand()) },
        rhs: {
            let base = &a__ + &b__ * x_.pow(4);
            let recursive_integrand = x_.pow(2) / base.pow((5, 4));
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(x_.pow(3) / (Atom::num(2) * base.pow((1, 4)))), x_)
                    - rubi_star(&a__ / Atom::num(2), recursive)
        },
    ));
}

fn push_rules_rule_840(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, x_);
    rules.push(rubi_rule!(
        order: 840,
        source: "Int[x_^2/(a_+b_.*x_^4)^(1/4),x_Symbol] :=
          (a+b*x^4)^(3/4)/(2*b*x) + a/(2*b) \\[Star] Int[1/(x^2*(a+b*x^4)^(1/4)),x] /;
        FreeQ[{a,b},x] && NegQ[b/a]",
        desc: "Binomial recurrence 3a",
        refs: ["G&R 2.110.5, CRC 88a"],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [a__, b__, x_],
        optional: [b__],
        when: { freeq!([a__, b__], x_) && negq!((&b__ / &a__).expand()) },
        rhs: {
            let base = &a__ + &b__ * x_.pow(4);
            let recursive_integrand = Atom::num(1) / (x_.pow(2) * base.pow((1, 4)));
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(base.pow((3, 4)) / (Atom::num(2) * &b__ * x_)), x_)
                    + rubi_star(&a__ / (Atom::num(2) * &b__), recursive)
        },
    ));
}

fn push_rules_rule_841(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, x_);
    rules.push(rubi_rule!(
        order: 841,
        source: "Int[1/(x_^2*(a_+b_.*x_^4)^(1/4)),x_Symbol] :=
          -1/(x*(a+b*x^4)^(1/4)) - b \\[Star] Int[x^2/(a+b*x^4)^(5/4),x] /;
        FreeQ[{a,b},x] && PosQ[b/a]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, x_],
        optional: [b__],
        when: { freeq!([a__, b__], x_) && posq!((&b__ / &a__).expand()) },
        rhs: {
            let base = &a__ + &b__ * x_.pow(4);
            let recursive_integrand = x_.pow(2) / base.pow((5, 4));
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(-Atom::num(1) / (x_ * base.pow((1, 4)))), x_)
                    - rubi_star(b__, recursive)
        },
    ));
}

fn push_rules_rule_842(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, x_);
    rules.push(rubi_rule!(
        order: 842,
        source: "Int[1/(x_^2*(a_+b_.*x_^4)^(1/4)),x_Symbol] :=
          x*(1+a/(b*x^4))^(1/4)/(a+b*x^4)^(1/4) \\[Star] Int[1/(x^3*(1+a/(b*x^4))^(1/4)),x] /;
        FreeQ[{a,b},x] && NegQ[b/a]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, x_],
        optional: [b__],
        when: { freeq!([a__, b__], x_) && negq!((&b__ / &a__).expand()) },
        rhs: {
            let base = &a__ + &b__ * x_.pow(4);
            let normalized_base = Atom::num(1) + &a__ / (&b__ * x_.pow(4));
            let recursive_integrand =
                Atom::num(1) / (x_.pow(3) * normalized_base.pow((1, 4)));
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let coefficient =
                x_ * normalized_base.pow((1, 4)) / base.pow((1, 4));

            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_843(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 843,
        source: "Int[(c_.*x_)^m_*(a_+b_.*x_^n_)^p_,x_Symbol] :=
          c^(n-1)*(c*x)^(m-n+1)*(a+b*x^n)^(p+1)/(b*(m+n*p+1)) -
          a*c^n*(m-n+1)/(b*(m+n*p+1)) \\[Star] Int[(c*x)^(m-n)*(a+b*x^n)^p,x] /;
        FreeQ[{a,b,c,p},x] && IGtQ[n,0] && GtQ[m,n-1] && NeQ[m+n*p+1,0] && IntBinomialQ[a,b,c,n,m,p,x]",
        desc: "Inverted integration by parts",
        refs: ["G&R 2.110.5, CRC 88a"],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, m_, n_, p_, x_],
        optional: [b__, c__],
        when: {
            freeq!([a__, b__, c__, p_], x_)
                && igtq!(n_, 0)
                && gtq!(m_, &n_ - Atom::num(1))
                && neq!(&m_ + &n_ * &p_ + Atom::num(1), 0)
                && rubi_int_binomial_q(&a__, &b__, &c__, &n_, &m_, &p_, x_)
        },
        rhs: {
            let denominator = &b__ * (&m_ + &n_ * &p_ + Atom::num(1));
            let scaled = &c__ * x_;
            let base = &a__ + &b__ * x_.pow(&n_);
            let direct = c__.pow(&n_ - Atom::num(1))
                * scaled.pow(&m_ - &n_ + Atom::num(1))
                * base.pow(&p_ + Atom::num(1))
                / &denominator;
            let recurrence_factor =
                &a__ * c__.pow(&n_) * (&m_ - &n_ + Atom::num(1)) / &denominator;
            let recursive_integrand = scaled.pow(&m_ - &n_) * base.pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) - rubi_star(recurrence_factor, recursive)
        },
    ));
}

fn push_rules_rule_844(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 844,
        source: "Int[(c_.*x_)^m_*(a_+b_.*x_^n_)^p_,x_Symbol] :=
          c^(n-1)*(c*x)^(m-n+1)*(a+b*x^n)^(p+1)/(b*(m+n*p+1)) -
          a*c^n*(m-n+1)/(b*(m+n*p+1)) \\[Star] Int[(c*x)^(m-n)*(a+b*x^n)^p,x] /;
        FreeQ[{a,b,c,m,p},x] && IGtQ[n,0] && SumSimplerQ[m,-n] && NeQ[m+n*p+1,0] && ILtQ[Simplify[(m+1)/n+p],0]",
        desc: "Inverted integration by parts",
        refs: ["G&R 2.110.5, CRC 88a"],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, m_, n_, p_, x_],
        optional: [b__, c__],
        when: {
            freeq!([a__, b__, c__, m_, p_], x_)
                && igtq!(n_, 0)
                && rubi_sum_simpler_q(&m_, &(-&n_))
                && neq!(&m_ + &n_ * &p_ + Atom::num(1), 0)
                && iltq!(rubi_simplify(&((&m_ + Atom::num(1)) / &n_ + &p_)), 0)
        },
        rhs: {
            let denominator = &b__ * (&m_ + &n_ * &p_ + Atom::num(1));
            let scaled = &c__ * x_;
            let base = &a__ + &b__ * x_.pow(&n_);
            let direct = c__.pow(&n_ - Atom::num(1))
                * scaled.pow(&m_ - &n_ + Atom::num(1))
                * base.pow(&p_ + Atom::num(1))
                / &denominator;
            let recurrence_factor =
                &a__ * c__.pow(&n_) * (&m_ - &n_ + Atom::num(1)) / &denominator;
            let recursive_integrand = scaled.pow(&m_ - &n_) * base.pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) - rubi_star(recurrence_factor, recursive)
        },
    ));
}

fn push_rules_rule_845(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a1__, b1__, c__, a2__, m_, n_, p_, x_, b2__);
    rules.push(rubi_rule!(
        order: 845,
        source: "Int[(c_.*x_)^m_*(a1_+b1_.*x_^n_)^p_*(a2_+b2_.*x_^n_)^p_,x_Symbol] :=
          c^(2*n-1)*(c*x)^(m-2*n+1)*(a1+b1*x^n)^(p+1)*(a2+b2*x^n)^(p+1)/(b1*b2*(m+2*n*p+1)) -
          a1*a2*c^(2*n)*(m-2*n+1)/(b1*b2*(m+2*n*p+1)) \\[Star] Int[(c*x)^(m-2*n)*(a1+b1*x^n)^p*(a2+b2*x^n)^p,x] /;
        FreeQ[{a1,b1,a2,b2,c,p},x] && EqQ[a2*b1+a1*b2,0] && IGtQ[2*n,0] && GtQ[m,2*n-1] && NeQ[m+2*n*p+1,0] &&
          IntBinomialQ[a1*a2,b1*b2,c,2*n,m,p,x]",
        desc: "Inverted integration by parts",
        refs: ["G&R 2.110.5, CRC 88a"],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a1__, b1__, c__, a2__, b2__, m_, n_, p_, x_],
        optional: [b1__, c__, b2__],
        when: {
            freeq!([a1__, b1__, a2__, b2__, c__, p_], x_)
                && eqq!(&a2__ * &b1__ + &a1__ * &b2__, 0)
                && igtq!(Atom::num(2) * &n_, 0)
                && gtq!(m_, Atom::num(2) * &n_ - Atom::num(1))
                && neq!(&m_ + Atom::num(2) * &n_ * &p_ + Atom::num(1), 0)
                && rubi_int_binomial_q(
                    &(&a1__ * &a2__),
                    &(&b1__ * &b2__),
                    &c__,
                    &(Atom::num(2) * &n_),
                    &m_,
                    &p_,
                    x_
                )
        },
        rhs: {
            let denominator =
                &b1__ * &b2__ * (&m_ + Atom::num(2) * &n_ * &p_ + Atom::num(1));
            let scaled = &c__ * x_;
            let monomial = x_.pow(&n_);
            let first = &a1__ + &b1__ * &monomial;
            let second = &a2__ + &b2__ * monomial;
            let direct = c__.pow(Atom::num(2) * &n_ - Atom::num(1))
                * scaled.pow(&m_ - Atom::num(2) * &n_ + Atom::num(1))
                * first.pow(&p_ + Atom::num(1))
                * second.pow(&p_ + Atom::num(1))
                / &denominator;
            let recurrence_factor = &a1__
                * &a2__
                * c__.pow(Atom::num(2) * &n_)
                * (&m_ - Atom::num(2) * &n_ + Atom::num(1))
                / &denominator;
            let recursive_integrand = scaled.pow(&m_ - Atom::num(2) * &n_)
                * first.pow(&p_)
                * second.pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) - rubi_star(recurrence_factor, recursive)
        },
    ));
}

fn push_rules_rule_846(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a1__, b1__, c__, a2__, m_, n_, p_, x_, b2__);
    rules.push(rubi_rule!(
        order: 846,
        source: "Int[(c_.*x_)^m_*(a1_+b1_.*x_^n_)^p_*(a2_+b2_.*x_^n_)^p_,x_Symbol] :=
          c^(2*n-1)*(c*x)^(m-2*n+1)*(a1+b1*x^n)^(p+1)*(a2+b2*x^n)^(p+1)/(b1*b2*(m+2*n*p+1)) -
          a1*a2*c^(2*n)*(m-2*n+1)/(b1*b2*(m+2*n*p+1)) \\[Star] Int[(c*x)^(m-2*n)*(a1+b1*x^n)^p*(a2+b2*x^n)^p,x] /;
        FreeQ[{a1,b1,a2,b2,c,m,p},x] && EqQ[a2*b1+a1*b2,0] && IGtQ[2*n,0] && SumSimplerQ[m,-2*n] && NeQ[m+2*n*p+1,0] &&
          ILtQ[Simplify[(m+1)/(2*n)+p],0]",
        desc: "Inverted integration by parts",
        refs: ["G&R 2.110.5, CRC 88a"],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a1__, b1__, c__, a2__, b2__, m_, n_, p_, x_],
        optional: [b1__, c__, b2__],
        when: {
            freeq!([a1__, b1__, a2__, b2__, c__, m_, p_], x_)
                && eqq!(&a2__ * &b1__ + &a1__ * &b2__, 0)
                && igtq!(Atom::num(2) * &n_, 0)
                && rubi_sum_simpler_q(&m_, &(-Atom::num(2) * &n_))
                && neq!(&m_ + Atom::num(2) * &n_ * &p_ + Atom::num(1), 0)
                && iltq!(
                    rubi_simplify(
                        &((&m_ + Atom::num(1)) / (Atom::num(2) * &n_) + &p_)
                    ),
                    0
                )
        },
        rhs: {
            let denominator =
                &b1__ * &b2__ * (&m_ + Atom::num(2) * &n_ * &p_ + Atom::num(1));
            let scaled = &c__ * x_;
            let monomial = x_.pow(&n_);
            let first = &a1__ + &b1__ * &monomial;
            let second = &a2__ + &b2__ * monomial;
            let direct = c__.pow(Atom::num(2) * &n_ - Atom::num(1))
                * scaled.pow(&m_ - Atom::num(2) * &n_ + Atom::num(1))
                * first.pow(&p_ + Atom::num(1))
                * second.pow(&p_ + Atom::num(1))
                / &denominator;
            let recurrence_factor = &a1__
                * &a2__
                * c__.pow(Atom::num(2) * &n_)
                * (&m_ - Atom::num(2) * &n_ + Atom::num(1))
                / &denominator;
            let recursive_integrand = scaled.pow(&m_ - Atom::num(2) * &n_)
                * first.pow(&p_)
                * second.pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) - rubi_star(recurrence_factor, recursive)
        },
    ));
}

fn push_rules_rule_847(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 847,
        source: "Int[(c_.*x_)^m_*(a_+b_.*x_^n_)^p_,x_Symbol] :=
          (c*x)^(m+1)*(a+b*x^n)^(p+1)/(a*c*(m+1)) -
          b*(m+n*(p+1)+1)/(a*c^n*(m+1)) \\[Star] Int[(c*x)^(m+n)*(a+b*x^n)^p,x] /;
        FreeQ[{a,b,c,p},x] && IGtQ[n,0] && LtQ[m,-1] && IntBinomialQ[a,b,c,n,m,p,x]",
        desc: "Integration by parts",
        refs: ["G&R 2.110.6, CRC 88c"],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, m_, n_, p_, x_],
        optional: [b__, c__],
        when: {
            freeq!([a__, b__, c__, p_], x_)
                && igtq!(n_, 0)
                && ltq!(m_, -1)
                && rubi_int_binomial_q(&a__, &b__, &c__, &n_, &m_, &p_, x_)
        },
        rhs: {
            let m1 = &m_ + Atom::num(1);
            let scaled = &c__ * x_;
            let base = &a__ + &b__ * x_.pow(&n_);
            let direct = scaled.pow(&m1) * base.pow(&p_ + Atom::num(1))
                / (&a__ * &c__ * &m1);
            let recurrence_factor = &b__
                * (&m_ + &n_ * (&p_ + Atom::num(1)) + Atom::num(1))
                / (&a__ * c__.pow(&n_) * &m1);
            let recursive_integrand = scaled.pow(&m_ + &n_) * base.pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) - rubi_star(recurrence_factor, recursive)
        },
    ));
}

fn push_rules_rule_848(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 848,
        source: "Int[(c_.*x_)^m_*(a_+b_.*x_^n_)^p_,x_Symbol] :=
          (c*x)^(m+1)*(a+b*x^n)^(p+1)/(a*c*(m+1)) -
          b*(m+n*(p+1)+1)/(a*c^n*(m+1)) \\[Star] Int[(c*x)^(m+n)*(a+b*x^n)^p,x] /;
        FreeQ[{a,b,c,m,p},x] && IGtQ[n,0] && SumSimplerQ[m,n] && ILtQ[Simplify[(m+1)/n+p],0]",
        desc: "Integration by parts",
        refs: ["G&R 2.110.6, CRC 88c"],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, m_, n_, p_, x_],
        optional: [b__, c__],
        when: {
            freeq!([a__, b__, c__, m_, p_], x_)
                && igtq!(n_, 0)
                && rubi_sum_simpler_q(&m_, &n_)
                && iltq!(rubi_simplify(&((&m_ + Atom::num(1)) / &n_ + &p_)), 0)
        },
        rhs: {
            let m1 = &m_ + Atom::num(1);
            let scaled = &c__ * x_;
            let base = &a__ + &b__ * x_.pow(&n_);
            let direct = scaled.pow(&m1) * base.pow(&p_ + Atom::num(1))
                / (&a__ * &c__ * &m1);
            let recurrence_factor = &b__
                * (&m_ + &n_ * (&p_ + Atom::num(1)) + Atom::num(1))
                / (&a__ * c__.pow(&n_) * &m1);
            let recursive_integrand = scaled.pow(&m_ + &n_) * base.pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) - rubi_star(recurrence_factor, recursive)
        },
    ));
}

fn push_rules_rule_849(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a1__, b1__, c__, a2__, m_, n_, p_, x_, b2__);
    rules.push(rubi_rule!(
        order: 849,
        source: "Int[(c_.*x_)^m_*(a1_+b1_.*x_^n_)^p_*(a2_+b2_.*x_^n_)^p_,x_Symbol] :=
          (c*x)^(m+1)*(a1+b1*x^n)^(p+1)*(a2+b2*x^n)^(p+1)/(a1*a2*c*(m+1)) -
          b1*b2*(m+2*n*(p+1)+1)/(a1*a2*c^(2*n)*(m+1)) \\[Star] Int[(c*x)^(m+2*n)*(a1+b1*x^n)^p*(a2+b2*x^n)^p,x] /;
        FreeQ[{a1,b1,a2,b2,c,p},x] && EqQ[a2*b1+a1*b2,0] && IGtQ[2*n,0] && LtQ[m,-1] && IntBinomialQ[a1*a2,b1*b2,c,2*n,m,p,x]",
        desc: "Integration by parts",
        refs: ["G&R 2.110.6, CRC 88c"],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a1__, b1__, c__, a2__, b2__, m_, n_, p_, x_],
        optional: [b1__, c__, b2__],
        when: {
            freeq!([a1__, b1__, a2__, b2__, c__, p_], x_)
                && eqq!(&a2__ * &b1__ + &a1__ * &b2__, 0)
                && igtq!(Atom::num(2) * &n_, 0)
                && ltq!(m_, -1)
                && rubi_int_binomial_q(
                    &(&a1__ * &a2__),
                    &(&b1__ * &b2__),
                    &c__,
                    &(Atom::num(2) * &n_),
                    &m_,
                    &p_,
                    x_,
                )
        },
        rhs: {
            let m1 = &m_ + Atom::num(1);
            let scaled = &c__ * x_;
            let monomial = x_.pow(&n_);
            let first = &a1__ + &b1__ * &monomial;
            let second = &a2__ + &b2__ * monomial;
            let direct = scaled.pow(&m1)
                * first.pow(&p_ + Atom::num(1))
                * second.pow(&p_ + Atom::num(1))
                / (&a1__ * &a2__ * &c__ * &m1);
            let recurrence_factor = &b1__
                * &b2__
                * (&m_ + Atom::num(2) * &n_ * (&p_ + Atom::num(1)) + Atom::num(1))
                / (&a1__ * &a2__ * c__.pow(Atom::num(2) * &n_) * &m1);
            let recursive_integrand = scaled.pow(&m_ + Atom::num(2) * &n_)
                * first.pow(&p_)
                * second.pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) - rubi_star(recurrence_factor, recursive)
        },
    ));
}

fn push_rules_rule_850(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a1__, b1__, c__, a2__, m_, n_, p_, x_, b2__);
    rules.push(rubi_rule!(
        order: 850,
        source: "Int[(c_.*x_)^m_*(a1_+b1_.*x_^n_)^p_*(a2_+b2_.*x_^n_)^p_,x_Symbol] :=
          (c*x)^(m+1)*(a1+b1*x^n)^(p+1)*(a2+b2*x^n)^(p+1)/(a1*a2*c*(m+1)) -
          b1*b2*(m+2*n*(p+1)+1)/(a1*a2*c^(2*n)*(m+1)) \\[Star] Int[(c*x)^(m+2*n)*(a1+b1*x^n)^p*(a2+b2*x^n)^p,x] /;
        FreeQ[{a1,b1,a2,b2,c,m,p},x] && EqQ[a2*b1+a1*b2,0] && IGtQ[2*n,0] && SumSimplerQ[m,2*n] && ILtQ[Simplify[(m+1)/(2*n)+p],0]",
        desc: "Integration by parts",
        refs: ["G&R 2.110.6, CRC 88c"],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a1__, b1__, c__, a2__, b2__, m_, n_, p_, x_],
        optional: [b1__, c__, b2__],
        when: {
            freeq!([a1__, b1__, a2__, b2__, c__, m_, p_], x_)
                && eqq!(&a2__ * &b1__ + &a1__ * &b2__, 0)
                && igtq!(Atom::num(2) * &n_, 0)
                && rubi_sum_simpler_q(&m_, &(Atom::num(2) * &n_))
                && iltq!(
                    rubi_simplify(
                        &((&m_ + Atom::num(1)) / (Atom::num(2) * &n_) + &p_)
                    ),
                    0
                )
        },
        rhs: {
            let m1 = &m_ + Atom::num(1);
            let scaled = &c__ * x_;
            let monomial = x_.pow(&n_);
            let first = &a1__ + &b1__ * &monomial;
            let second = &a2__ + &b2__ * monomial;
            let direct = scaled.pow(&m1)
                * first.pow(&p_ + Atom::num(1))
                * second.pow(&p_ + Atom::num(1))
                / (&a1__ * &a2__ * &c__ * &m1);
            let recurrence_factor = &b1__
                * &b2__
                * (&m_ + Atom::num(2) * &n_ * (&p_ + Atom::num(1)) + Atom::num(1))
                / (&a1__ * &a2__ * c__.pow(Atom::num(2) * &n_) * &m1);
            let recursive_integrand = scaled.pow(&m_ + Atom::num(2) * &n_)
                * first.pow(&p_)
                * second.pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) - rubi_star(recurrence_factor, recursive)
        },
    ));
}

fn push_rules_rule_851(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 851,
        source: "Int[(c_.*x_)^m_*(a_+b_.*x_^n_)^p_,x_Symbol] :=
          With[{k=Denominator[m]},
          k/c \\[Star] Subst[Int[x^(k*(m+1)-1)*(a+b*x^(k*n)/c^n)^p,x],x,(c*x)^(1/k)]] /;
        FreeQ[{a,b,c,p},x] && IGtQ[n,0] && FractionQ[m] && IntBinomialQ[a,b,c,n,m,p,x]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, m_, n_, p_, x_],
        optional: [b__, c__],
        when: {
            freeq!([a__, b__, c__, p_], x_)
                && igtq!(n_, 0)
                && fractionq!(m_)
                && rubi_int_binomial_q(&a__, &b__, &c__, &n_, &m_, &p_, x_)
        },
        rhs: {
            let k = Atom::num(rubi_denominator(&m_).rubi_rhs());
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = sub_atom.pow(&k * (&m_ + Atom::num(1)) - Atom::num(1))
                * (&a__ + &b__ * sub_atom.pow(&k * &n_) / c__.pow(&n_)).pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);
            let substituted = rubi_subst(
                &transformed,
                sub,
                (&c__ * x_).pow(Atom::num(1) / &k),
            );

            rubi_star(&k / &c__, substituted)
        },
    ));
}

fn push_rules_rule_852(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a1__, b1__, c__, a2__, m_, n_, p_, x_, b2__);
    rules.push(rubi_rule!(
        order: 852,
        source: "Int[(c_.*x_)^m_*(a1_+b1_.*x_^n_)^p_*(a2_+b2_.*x_^n_)^p_,x_Symbol] :=
          With[{k=Denominator[m]},
          k/c \\[Star] Subst[Int[x^(k*(m+1)-1)*(a1+b1*x^(k*n)/c^n)^p*(a2+b2*x^(k*n)/c^n)^p,x],x,(c*x)^(1/k)]] /;
        FreeQ[{a1,b1,a2,b2,c,p},x] && EqQ[a2*b1+a1*b2,0] && IGtQ[2*n,0] && FractionQ[m] && IntBinomialQ[a1*a2,b1*b2,c,2*n,m,p,x]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a1__, b1__, c__, a2__, b2__, m_, n_, p_, x_],
        optional: [b1__, c__, b2__],
        when: {
            freeq!([a1__, b1__, a2__, b2__, c__, p_], x_)
                && eqq!(&a2__ * &b1__ + &a1__ * &b2__, 0)
                && igtq!(Atom::num(2) * &n_, 0)
                && fractionq!(m_)
                && rubi_int_binomial_q(
                    &(&a1__ * &a2__),
                    &(&b1__ * &b2__),
                    &c__,
                    &(Atom::num(2) * &n_),
                    &m_,
                    &p_,
                    x_,
                )
        },
        rhs: {
            let k = Atom::num(rubi_denominator(&m_).rubi_rhs());
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_power = &k * &n_;
            let transformed_integrand = sub_atom.pow(&k * (&m_ + Atom::num(1)) - Atom::num(1))
                * (&a1__ + &b1__ * sub_atom.pow(&transformed_power) / c__.pow(&n_)).pow(&p_)
                * (&a2__ + &b2__ * sub_atom.pow(transformed_power) / c__.pow(&n_)).pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);
            let substituted = rubi_subst(
                &transformed,
                sub,
                (&c__ * x_).pow(Atom::num(1) / &k),
            );

            rubi_star(&k / &c__, substituted)
        },
    ));
}

fn push_rules_rule_853(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, x_);
    rules.push(rubi_rule!(
        order: 853,
        source: "Int[x_/(a_+b_.*x_^3)^(2/3),x_Symbol] :=
          With[{q=Rt[b,3]},
          -ArcTan[(1+2*q*x/(a+b*x^3)^(1/3))/Sqrt[3]]/(Sqrt[3]*q^2) - Log[q*x-(a+b*x^3)^(1/3)]/(2*q^2)] /;
        FreeQ[{a,b},x]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: x_ / (a__ + b__ * x_.pow(3)).pow((2, 3)),
        with: [a__, b__, x_],
        optional: [b__],
        when: { freeq!([a__, b__], x_) },
        rhs: {
            let q = rubi_rt(&b__, 3);
            let base = &a__ + &b__ * x_.pow(3);
            let sqrt_three = Atom::num(3).sqrt();
            let q_squared = q.pow(2);
            let radical = base.pow((1, 3));
            let atan_argument =
                (Atom::num(1) + Atom::num(2) * &q * x_ / &radical) / &sqrt_three;
            let first = -atan_argument.atan() / (&sqrt_three * &q_squared);
            let second = (&q * x_ - radical).log() / (Atom::num(2) * q_squared);
            rubi_simp(&first, x_) - rubi_simp(&second, x_)
        },
    ));
}

fn push_rules_rule_854(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 854,
        source: "Int[x_^m_.*(a_+b_.*x_^n_)^p_,x_Symbol] :=
          a^(p+(m+1)/n) \\[Star] Subst[Int[x^m/(1-b*x^n)^(p+(m+1)/n+1),x],x,x/(a+b*x^n)^(1/n)] /;
        FreeQ[{a,b},x] && IGtQ[n,0] && LtQ[-1,p,0] && NeQ[p,-1/2] && IntegersQ[m,p+(m+1)/n]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [a__, b__, m_, n_, p_, x_],
        optional: [b__, m_],
        when: {
            let exponent_sum = &p_ + (&m_ + Atom::num(1)) / &n_;
            freeq!([a__, b__], x_)
                && igtq!(n_, 0)
                && ltq!(-1, p_, 0)
                && neq!(p_, -Atom::num(1) / Atom::num(2))
                && integersq!([m_, exponent_sum])
        },
        rhs: {
            let exponent_sum = &p_ + (&m_ + Atom::num(1)) / &n_;
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = sub_atom.pow(&m_)
                / (Atom::num(1) - &b__ * sub_atom.pow(&n_)).pow(&exponent_sum + Atom::num(1));
            let transformed = rubi_rhs_int(&transformed_integrand, sub);

            let base = &a__ + &b__ * x_.pow(&n_);
            let replacement = x_ / base.pow(Atom::num(1) / &n_);
            let substituted = rubi_subst(&transformed, sub, replacement);

            rubi_star(a__.pow(exponent_sum), substituted)
        },
    ));
}

fn push_rules_rule_855(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a1__, b1__, a2__, m_, n_, p_, x_, b2__);
    rules.push(rubi_rule!(
        order: 855,
        source: "Int[x_^m_.*(a1_+b1_.*x_^n_)^p_*(a2_+b2_.*x_^n_)^p_,x_Symbol] :=
          (a1*a2)^(p+(m+1)/(2*n)) \\[Star]
            Subst[Int[x^m/((1-b1*x^n)^(p+(m+1)/(2*n)+1)*(1-b2*x^n)^(p+(m+1)/(2*n)+1)),x],x,
              x/((a1+b1*x^n)^(1/(2*n))*(a2+b2*x^n)^(1/(2*n)))] /;
        FreeQ[{a1,b1,a2,b2},x] && EqQ[a2*b1+a1*b2,0] && IGtQ[2*n,0] && LtQ[-1,p,0] && NeQ[p,-1/2] && IntegersQ[m,p+(m+1)/(2*n)]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [a1__, b1__, a2__, b2__, m_, n_, p_, x_],
        optional: [b1__, b2__, m_],
        when: {
            let exponent_sum = &p_ + (&m_ + Atom::num(1)) / (Atom::num(2) * &n_);
            freeq!([a1__, b1__, a2__, b2__], x_)
                && eqq!(&a2__ * &b1__ + &a1__ * &b2__, 0)
                && igtq!(Atom::num(2) * &n_, 0)
                && ltq!(-1, p_, 0)
                && neq!(p_, -Atom::num(1) / Atom::num(2))
                && integersq!([m_, exponent_sum])
        },
        rhs: {
            let exponent_sum = &p_ + (&m_ + Atom::num(1)) / (Atom::num(2) * &n_);
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = sub_atom.pow(&m_)
                / ((Atom::num(1) - &b1__ * sub_atom.pow(&n_)).pow(&exponent_sum + Atom::num(1))
                    * (Atom::num(1) - &b2__ * sub_atom.pow(&n_)).pow(&exponent_sum + Atom::num(1)));
            let transformed = rubi_rhs_int(&transformed_integrand, sub);

            let monomial = x_.pow(&n_);
            let first = &a1__ + &b1__ * &monomial;
            let second = &a2__ + &b2__ * monomial;
            let replacement =
                x_ / (first.pow(Atom::num(1) / (Atom::num(2) * &n_)) * second.pow(Atom::num(1) / (Atom::num(2) * &n_)));
            let substituted = rubi_subst(&transformed, sub, replacement);

            rubi_star((&a1__ * &a2__).pow(exponent_sum), substituted)
        },
    ));
}

fn push_rules_rule_856(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 856,
        source: "Int[x_^m_.*(a_+b_.*x_^n_)^p_,x_Symbol] :=
          (a/(a+b*x^n))^(p+(m+1)/n)*(a+b*x^n)^(p+(m+1)/n) \\[Star] Subst[Int[x^m/(1-b*x^n)^(p+(m+1)/n+1),x],x,x/(a+b*x^n)^(1/n)] /;
        FreeQ[{a,b},x] && IGtQ[n,0] && LtQ[-1,p,0] && NeQ[p,-1/2] && IntegerQ[m] && LtQ[Denominator[p+(m+1)/n],Denominator[p]]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [a__, b__, m_, n_, p_, x_],
        optional: [b__, m_],
        when: {
            let exponent_sum = &p_ + (&m_ + Atom::num(1)) / &n_;
            freeq!([a__, b__], x_)
                && igtq!(n_, 0)
                && ltq!(-1, p_, 0)
                && neq!(p_, -Atom::num(1) / Atom::num(2))
                && integerq!(m_)
                && ltq!(
                    Atom::num(denominator!(exponent_sum)),
                    Atom::num(denominator!(p_))
                )
        },
        rhs: {
            let exponent_sum = &p_ + (&m_ + Atom::num(1)) / &n_;
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = sub_atom.pow(&m_)
                / (Atom::num(1) - &b__ * sub_atom.pow(&n_)).pow(&exponent_sum + Atom::num(1));
            let transformed = rubi_rhs_int(&transformed_integrand, sub);

            let base = &a__ + &b__ * x_.pow(&n_);
            let replacement = x_ / base.pow(Atom::num(1) / &n_);
            let substituted = rubi_subst(&transformed, sub, replacement);
            let coefficient = (&a__ / &base).pow(&exponent_sum) * base.pow(&exponent_sum);

            rubi_star(coefficient, substituted)
        },
    ));
}

fn push_rules_rule_857(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a1__, b1__, a2__, m_, n_, p_, x_, b2__);
    rules.push(rubi_rule!(
        order: 857,
        source: "Int[x_^m_.*(a1_+b1_.*x_^n_)^p_*(a2_+b2_.*x_^n_)^p_,x_Symbol] :=
          (a1/(a1+b1*x^n))^(p+(m+1)/(2*n))*(a1+b1*x^n)^(p+(m+1)/(2*n))*(a2/(a2+b2*x^n))^(p+(m+1)/(2*n))*(a2+b2*x^n)^(p+(m+1)/(2*n)) \\[Star]
            Subst[Int[x^m/((1-b1*x^n)^(p+(m+1)/(2*n)+1)*(1-b2*x^n)^(p+(m+1)/(2*n)+1)),x],x,
              x/((a1+b1*x^n)^(1/(2*n))*(a2+b2*x^n)^(1/(2*n)))] /;
        FreeQ[{a1,b1,a2,b2},x] && EqQ[a2*b1+a1*b2,0] && IGtQ[2*n,0] && LtQ[-1,p,0] && NeQ[p,-1/2] &&
          IntegerQ[m] && LtQ[Denominator[p+(m+1)/(2*n)],Denominator[p]]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [a1__, b1__, a2__, b2__, m_, n_, p_, x_],
        optional: [b1__, b2__, m_],
        when: {
            let exponent_sum = &p_ + (&m_ + Atom::num(1)) / (Atom::num(2) * &n_);
            freeq!([a1__, b1__, a2__, b2__], x_)
                && eqq!(&a2__ * &b1__ + &a1__ * &b2__, 0)
                && igtq!(Atom::num(2) * &n_, 0)
                && ltq!(-1, p_, 0)
                && neq!(p_, -Atom::num(1) / Atom::num(2))
                && integerq!(m_)
                && ltq!(
                    Atom::num(denominator!(exponent_sum)),
                    Atom::num(denominator!(p_))
                )
        },
        rhs: {
            let exponent_sum = &p_ + (&m_ + Atom::num(1)) / (Atom::num(2) * &n_);
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = sub_atom.pow(&m_)
                / ((Atom::num(1) - &b1__ * sub_atom.pow(&n_)).pow(&exponent_sum + Atom::num(1))
                    * (Atom::num(1) - &b2__ * sub_atom.pow(&n_)).pow(&exponent_sum + Atom::num(1)));
            let transformed = rubi_rhs_int(&transformed_integrand, sub);

            let monomial = x_.pow(&n_);
            let first = &a1__ + &b1__ * &monomial;
            let second = &a2__ + &b2__ * monomial;
            let replacement =
                x_ / (first.pow(Atom::num(1) / (Atom::num(2) * &n_)) * second.pow(Atom::num(1) / (Atom::num(2) * &n_)));
            let substituted = rubi_subst(&transformed, sub, replacement);
            let coefficient = (&a1__ / &first).pow(&exponent_sum)
                * first.pow(&exponent_sum)
                * (&a2__ / &second).pow(&exponent_sum)
                * second.pow(&exponent_sum);

            rubi_star(coefficient, substituted)
        },
    ));
}

fn push_rules_rule_858(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 858,
        source: "Int[x_^m_.*(a_+b_.*x_^n_)^p_,x_Symbol] :=
          -Subst[Int[(a+b*x^(-n))^p/x^(m+2),x],x,1/x] /;
        FreeQ[{a,b,p},x] && ILtQ[n,0] && IntegerQ[m]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [a__, b__, m_, n_, p_, x_],
        optional: [b__, m_],
        when: { freeq!([a__, b__, p_], x_) && iltq!(n_, 0) && integerq!(m_) },
        rhs: {
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = (&a__ + &b__ * sub_atom.pow(-&n_)).pow(&p_)
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

fn push_rules_rule_859(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a1__, b1__, a2__, m_, n_, p_, x_, b2__);
    rules.push(rubi_rule!(
        order: 859,
        source: "Int[x_^m_.*(a1_+b1_.*x_^n_)^p_*(a2_+b2_.*x_^n_)^p_,x_Symbol] :=
          -Subst[Int[(a1+b1*x^(-n))^p*(a2+b2*x^(-n))^p/x^(m+2),x],x,1/x] /;
        FreeQ[{a1,b1,a2,b2,p},x] && EqQ[a2*b1+a1*b2,0] && ILtQ[2*n,0] && IntegerQ[m]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [a1__, b1__, a2__, b2__, m_, n_, p_, x_],
        optional: [b1__, b2__, m_],
        when: {
            freeq!([a1__, b1__, a2__, b2__, p_], x_)
                && eqq!(&a2__ * &b1__ + &a1__ * &b2__, 0)
                && iltq!(Atom::num(2) * &n_, 0)
                && integerq!(m_)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = (&a1__ + &b1__ * sub_atom.pow(-&n_)).pow(&p_)
                * (&a2__ + &b2__ * sub_atom.pow(-&n_)).pow(&p_)
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

fn push_rules_rule_860(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 860,
        source: "Int[(c_.*x_)^m_*(a_+b_.*x_^n_)^p_,x_Symbol] :=
          With[{k=Denominator[m]},
          -k/c \\[Star] Subst[Int[(a+b*c^(-n)*x^(-k*n))^p/x^(k*(m+1)+1),x],x,1/(c*x)^(1/k)]] /;
        FreeQ[{a,b,c,p},x] && ILtQ[n,0] && FractionQ[m]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, m_, n_, p_, x_],
        optional: [b__, c__],
        when: { freeq!([a__, b__, c__, p_], x_) && iltq!(n_, 0) && fractionq!(m_) },
        rhs: {
            let k = Atom::num(rubi_denominator(&m_).rubi_rhs());
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = (&a__ + &b__ * c__.pow(-&n_) * sub_atom.pow(-&k * &n_)).pow(&p_)
                / sub_atom.pow(&k * (&m_ + Atom::num(1)) + Atom::num(1));
            let transformed = rubi_rhs_int(&transformed_integrand, sub);
            let replacement = Atom::num(1) / (&c__ * x_).pow(Atom::num(1) / &k);
            let substituted = rubi_subst(&transformed, sub, replacement);
            rubi_star(-&k / &c__, substituted)
        },
    ));
}

fn push_rules_rule_861(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a1__, b1__, c__, a2__, m_, n_, p_, x_, b2__);
    rules.push(rubi_rule!(
        order: 861,
        source: "Int[(c_.*x_)^m_*(a1_+b1_.*x_^n_)^p_*(a2_+b2_.*x_^n_)^p_,x_Symbol] :=
          With[{k=Denominator[m]},
          -k/c \\[Star] Subst[Int[(a1+b1*c^(-n)*x^(-k*n))^p*(a2+b2*c^(-n)*x^(-k*n))^p/x^(k*(m+1)+1),x],x,1/(c*x)^(1/k)]] /;
        FreeQ[{a1,b1,a2,b2,c,p},x] && EqQ[a2*b1+a1*b2,0] && ILtQ[2*n,0] && FractionQ[m]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a1__, b1__, c__, a2__, b2__, m_, n_, p_, x_],
        optional: [b1__, c__, b2__],
        when: {
            freeq!([a1__, b1__, a2__, b2__, c__, p_], x_)
                && eqq!(&a2__ * &b1__ + &a1__ * &b2__, 0)
                && iltq!(Atom::num(2) * &n_, 0)
                && fractionq!(m_)
        },
        rhs: {
            let k = Atom::num(rubi_denominator(&m_).rubi_rhs());
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_power = -&k * &n_;
            let transformed_integrand = (&a1__ + &b1__ * c__.pow(-&n_) * sub_atom.pow(&transformed_power)).pow(&p_)
                * (&a2__ + &b2__ * c__.pow(-&n_) * sub_atom.pow(transformed_power)).pow(&p_)
                / sub_atom.pow(&k * (&m_ + Atom::num(1)) + Atom::num(1));
            let transformed = rubi_rhs_int(&transformed_integrand, sub);
            let replacement = Atom::num(1) / (&c__ * x_).pow(Atom::num(1) / &k);
            let substituted = rubi_subst(&transformed, sub, replacement);
            rubi_star(-&k / &c__, substituted)
        },
    ));
}

fn push_rules_rule_862(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 862,
        source: "Int[(c_.*x_)^m_*(a_+b_.*x_^n_)^p_,x_Symbol] :=
          -1/c*(c*x)^(m+1)*(1/x)^(m+1) \\[Star] Subst[Int[(a+b*x^(-n))^p/x^(m+2),x],x,1/x] /;
        FreeQ[{a,b,c,m,p},x] && ILtQ[n,0] && Not[RationalQ[m]]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, m_, n_, p_, x_],
        optional: [b__, c__],
        when: { freeq!([a__, b__, c__, m_, p_], x_) && iltq!(n_, 0) && !rationalq!(m_) },
        rhs: {
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = (&a__ + &b__ * sub_atom.pow(-&n_)).pow(&p_)
                / sub_atom.pow(&m_ + Atom::num(2));
            let transformed = rubi_rhs_int(&transformed_integrand, sub);

            let coefficient = -(&c__ * x_).pow(&m_ + Atom::num(1))
                * (Atom::num(1) / x_).pow(&m_ + Atom::num(1))
                / &c__;
            let substituted = rubi_subst(&transformed, sub, Atom::num(1) / x_);
            rubi_star(coefficient, substituted)
        },
    ));
}

fn push_rules_rule_863(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a1__, b1__, c__, a2__, m_, n_, p_, x_, b2__);
    rules.push(rubi_rule!(
        order: 863,
        source: "Int[(c_.*x_)^m_*(a1_+b1_.*x_^n_)^p_*(a2_+b2_.*x_^n_)^p_,x_Symbol] :=
          -1/c*(c*x)^(m+1)*(1/x)^(m+1) \\[Star] Subst[Int[(a1+b1*x^(-n))^p*(a2+b2*x^(-n))^p/x^(m+2),x],x,1/x] /;
        FreeQ[{a1,b1,a2,b2,c,m,p},x] && EqQ[a2*b1+a1*b2,0] && ILtQ[2*n,0] && Not[RationalQ[m]]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a1__, b1__, c__, a2__, b2__, m_, n_, p_, x_],
        optional: [b1__, c__, b2__],
        when: {
            freeq!([a1__, b1__, a2__, b2__, c__, m_, p_], x_)
                && eqq!(&a2__ * &b1__ + &a1__ * &b2__, 0)
                && iltq!(Atom::num(2) * &n_, 0)
                && !rationalq!(m_)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = (&a1__ + &b1__ * sub_atom.pow(-&n_)).pow(&p_)
                * (&a2__ + &b2__ * sub_atom.pow(-&n_)).pow(&p_)
                / sub_atom.pow(&m_ + Atom::num(2));
            let transformed = rubi_rhs_int(&transformed_integrand, sub);

            let coefficient = -(&c__ * x_).pow(&m_ + Atom::num(1))
                * (Atom::num(1) / x_).pow(&m_ + Atom::num(1))
                / &c__;
            let substituted = rubi_subst(&transformed, sub, Atom::num(1) / x_);
            rubi_star(coefficient, substituted)
        },
    ));
}

fn push_rules_rule_864(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 864,
        source: "Int[x_^m_.*(a_+b_.*x_^n_)^p_,x_Symbol] :=
          With[{k=Denominator[n]},
          k \\[Star] Subst[Int[x^(k*(m+1)-1)*(a+b*x^(k*n))^p,x],x,x^(1/k)]] /;
        FreeQ[{a,b,m,p},x] && FractionQ[n]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [a__, b__, m_, n_, p_, x_],
        optional: [b__, m_],
        when: { freeq!([a__, b__, m_, p_], x_) && fractionq!(n_) },
        rhs: {
            let k = Atom::num(rubi_denominator(&n_).rubi_rhs());
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = sub_atom.pow(&k * (&m_ + Atom::num(1)) - Atom::num(1))
                * (&a__ + &b__ * sub_atom.pow(&k * &n_)).pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);
            let substituted = rubi_subst(&transformed, sub, x_.pow(Atom::num(1) / &k));
            rubi_star(k, substituted)
        },
    ));
}

fn push_rules_rule_865(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a1__, b1__, a2__, m_, n_, p_, x_, b2__);
    rules.push(rubi_rule!(
        order: 865,
        source: "Int[x_^m_.*(a1_+b1_.*x_^n_)^p_*(a2_+b2_.*x_^n_)^p_,x_Symbol] :=
          With[{k=Denominator[2*n]},
          k \\[Star] Subst[Int[x^(k*(m+1)-1)*(a1+b1*x^(k*n))^p*(a2+b2*x^(k*n))^p,x],x,x^(1/k)]] /;
        FreeQ[{a1,b1,a2,b2,m,p},x] && EqQ[a2*b1+a1*b2,0] && FractionQ[2*n]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [a1__, b1__, a2__, b2__, m_, n_, p_, x_],
        optional: [b1__, b2__, m_],
        when: {
            freeq!([a1__, b1__, a2__, b2__, m_, p_], x_)
                && eqq!(&a2__ * &b1__ + &a1__ * &b2__, 0)
                && fractionq!(Atom::num(2) * &n_)
        },
        rhs: {
            let k = Atom::num(rubi_denominator(&(Atom::num(2) * &n_)).rubi_rhs());
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_power = &k * &n_;
            let transformed_integrand = sub_atom.pow(&k * (&m_ + Atom::num(1)) - Atom::num(1))
                * (&a1__ + &b1__ * sub_atom.pow(&transformed_power)).pow(&p_)
                * (&a2__ + &b2__ * sub_atom.pow(transformed_power)).pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);
            let substituted = rubi_subst(&transformed, sub, x_.pow(Atom::num(1) / &k));
            rubi_star(k, substituted)
        },
    ));
}

fn push_rules_rule_866(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 866,
        source: "Int[(c_*x_)^m_*(a_+b_.*x_^n_)^p_,x_Symbol] :=
          c^IntPart[m]*(c*x)^FracPart[m]/x^FracPart[m] \\[Star] Int[x^m*(a+b*x^n)^p,x] /;
        FreeQ[{a,b,c,m,p},x] && FractionQ[n]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, m_, n_, p_, x_],
        optional: [b__],
        when: { freeq!([a__, b__, c__, m_, p_], x_) && fractionq!(n_) },
        rhs: {
            let int_m = rubi_int_part(&m_);
            let frac_m = rubi_frac_part(&m_);
            let unscaled_integrand = x_.pow(&m_) * (&a__ + &b__ * x_.pow(&n_)).pow(&p_);
            let unscaled = rubi_rhs_int(&unscaled_integrand, x_);
            let coefficient = c__.pow(int_m) * (&c__ * x_).pow(&frac_m) / x_.pow(&frac_m);
            rubi_star(coefficient, unscaled)
        },
    ));
}

fn push_rules_rule_867(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a1__, b1__, c__, a2__, m_, n_, p_, x_, b2__);
    rules.push(rubi_rule!(
        order: 867,
        source: "Int[(c_*x_)^m_*(a1_+b1_.*x_^n_)^p_*(a2_+b2_.*x_^n_)^p_,x_Symbol] :=
          c^IntPart[m]*(c*x)^FracPart[m]/x^FracPart[m] \\[Star] Int[x^m*(a1+b1*x^n)^p*(a2+b2*x^n)^p,x] /;
        FreeQ[{a1,b1,a2,b2,c,m,p},x] && EqQ[a2*b1+a1*b2,0] && FractionQ[2*n]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a1__, b1__, c__, a2__, b2__, m_, n_, p_, x_],
        optional: [b1__, b2__],
        when: {
            freeq!([a1__, b1__, a2__, b2__, c__, m_, p_], x_)
                && eqq!(&a2__ * &b1__ + &a1__ * &b2__, 0)
                && fractionq!(Atom::num(2) * &n_)
        },
        rhs: {
            let int_m = rubi_int_part(&m_);
            let frac_m = rubi_frac_part(&m_);
            let monomial = x_.pow(&n_);
            let unscaled_integrand = x_.pow(&m_)
                * (&a1__ + &b1__ * &monomial).pow(&p_)
                * (&a2__ + &b2__ * monomial).pow(&p_);
            let unscaled = rubi_rhs_int(&unscaled_integrand, x_);
            let coefficient = c__.pow(int_m) * (&c__ * x_).pow(&frac_m) / x_.pow(&frac_m);
            rubi_star(coefficient, unscaled)
        },
    ));
}

fn push_rules_rule_868(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 868,
        source: "Int[x_^m_.*(a_+b_.*x_^n_)^p_,x_Symbol] :=
          1/(m+1) \\[Star] Subst[Int[(a+b*x^Simplify[n/(m+1)])^p,x],x,x^(m+1)] /;
        FreeQ[{a,b,m,n,p},x] && IntegerQ[Simplify[n/(m+1)]] && Not[IntegerQ[n]]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [a__, b__, m_, n_, p_, x_],
        optional: [b__, m_],
        when: {
            freeq!([a__, b__, m_, n_, p_], x_)
                && integerq!(rubi_simplify(&(&n_ / (&m_ + Atom::num(1)))))
                && !integerq!(n_)
        },
        rhs: {
            let m1 = &m_ + Atom::num(1);
            let quotient = rubi_simplify(&(&n_ / &m1));
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = (&a__ + &b__ * sub_atom.pow(quotient)).pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);
            let substituted = rubi_subst(&transformed, sub, x_.pow(&m1));
            rubi_star(Atom::num(1) / &m1, substituted)
        },
    ));
}

fn push_rules_rule_869(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a1__, b1__, a2__, m_, n_, p_, x_, b2__);
    rules.push(rubi_rule!(
        order: 869,
        source: "Int[x_^m_.*(a1_+b1_.*x_^n_)^p_*(a2_+b2_.*x_^n_)^p_,x_Symbol] :=
          1/(m+1) \\[Star] Subst[Int[(a1+b1*x^Simplify[n/(m+1)])^p*(a2+b2*x^Simplify[n/(m+1)])^p,x],x,x^(m+1)] /;
        FreeQ[{a1,b1,a2,b2,m,n,p},x] && EqQ[a2*b1+a1*b2,0] && IntegerQ[Simplify[2*n/(m+1)]] && Not[IntegerQ[2*n]]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [a1__, b1__, a2__, b2__, m_, n_, p_, x_],
        optional: [b1__, b2__, m_],
        when: {
            freeq!([a1__, b1__, a2__, b2__, m_, n_, p_], x_)
                && eqq!(&a2__ * &b1__ + &a1__ * &b2__, 0)
                && integerq!(rubi_simplify(
                    &(Atom::num(2) * &n_ / (&m_ + Atom::num(1)))
                ))
                && !integerq!(Atom::num(2) * &n_)
        },
        rhs: {
            let m1 = &m_ + Atom::num(1);
            let quotient = rubi_simplify(&(&n_ / &m1));
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand =
                (&a1__ + &b1__ * sub_atom.pow(&quotient)).pow(&p_) * (&a2__ + &b2__ * sub_atom.pow(quotient)).pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);
            let substituted = rubi_subst(&transformed, sub, x_.pow(&m1));
            rubi_star(Atom::num(1) / &m1, substituted)
        },
    ));
}

fn push_rules_rule_870(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 870,
        source: "Int[(c_*x_)^m_*(a_+b_.*x_^n_)^p_,x_Symbol] :=
          c^IntPart[m]*(c*x)^FracPart[m]/x^FracPart[m] \\[Star] Int[x^m*(a+b*x^n)^p,x] /;
        FreeQ[{a,b,c,m,n,p},x] && IntegerQ[Simplify[n/(m+1)]] && Not[IntegerQ[n]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, m_, n_, p_, x_],
        optional: [b__],
        when: {
            freeq!([a__, b__, c__, m_, n_, p_], x_)
                && integerq!(rubi_simplify(&(&n_ / (&m_ + Atom::num(1)))))
                && !integerq!(n_)
        },
        rhs: {
            let int_m = rubi_int_part(&m_);
            let frac_m = rubi_frac_part(&m_);
            let unscaled_integrand = x_.pow(&m_) * (&a__ + &b__ * x_.pow(&n_)).pow(&p_);
            let unscaled = rubi_rhs_int(&unscaled_integrand, x_);
            let coefficient = c__.pow(int_m) * (&c__ * x_).pow(&frac_m) / x_.pow(&frac_m);
            rubi_star(coefficient, unscaled)
        },
    ));
}

fn push_rules_rule_871(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a1__, b1__, c__, a2__, m_, n_, p_, x_, b2__);
    rules.push(rubi_rule!(
        order: 871,
        source: "Int[(c_*x_)^m_*(a1_+b1_.*x_^n_)^p_*(a2_+b2_.*x_^n_)^p_,x_Symbol] :=
          c^IntPart[m]*(c*x)^FracPart[m]/x^FracPart[m] \\[Star] Int[x^m*(a1+b1*x^n)^p*(a2+b2*x^n)^p,x] /;
        FreeQ[{a1,b1,a2,b2,c,m,n,p},x] && EqQ[a2*b1+a1*b2,0] && IntegerQ[Simplify[2*n/(m+1)]] && Not[IntegerQ[2*n]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a1__, b1__, c__, a2__, b2__, m_, n_, p_, x_],
        optional: [b1__, b2__],
        when: {
            freeq!([a1__, b1__, a2__, b2__, c__, m_, n_, p_], x_)
                && eqq!(&a2__ * &b1__ + &a1__ * &b2__, 0)
                && integerq!(rubi_simplify(
                    &(Atom::num(2) * &n_ / (&m_ + Atom::num(1)))
                ))
                && !integerq!(Atom::num(2) * &n_)
        },
        rhs: {
            let int_m = rubi_int_part(&m_);
            let frac_m = rubi_frac_part(&m_);
            let monomial = x_.pow(&n_);
            let unscaled_integrand = x_.pow(&m_)
                * (&a1__ + &b1__ * &monomial).pow(&p_)
                * (&a2__ + &b2__ * monomial).pow(&p_);
            let unscaled = rubi_rhs_int(&unscaled_integrand, x_);
            let coefficient = c__.pow(int_m) * (&c__ * x_).pow(&frac_m) / x_.pow(&frac_m);
            rubi_star(coefficient, unscaled)
        },
    ));
}

fn push_rules_rule_872(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 872,
        source: "Int[x_^m_.*(a_+b_.*x_^n_)^p_,x_Symbol] :=
          x^(m+1)*(a+b*x^n)^p/(m+1) -
          b*n*p/(m+1) \\[Star] Int[x^(m+n)*(a+b*x^n)^(p-1),x] /;
        FreeQ[{a,b,m,n},x] && EqQ[(m+1)/n+p,0] && GtQ[p,0]",
        desc: "Integration by parts",
        refs: ["G&R 2.110.3"],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [a__, b__, m_, n_, p_, x_],
        optional: [b__, m_],
        when: {
            freeq!([a__, b__, m_, n_], x_)
                && eqq!((&m_ + Atom::num(1)) / &n_ + &p_, 0)
                && gtq!(p_, 0)
        },
        rhs: {
            let denominator = &m_ + Atom::num(1);
            let base = &a__ + &b__ * x_.pow(&n_);
            let direct = x_.pow(&m_ + Atom::num(1)) * base.pow(&p_) / &denominator;
            let recursive_integrand = x_.pow(&m_ + &n_) * base.pow(&p_ - Atom::num(1));
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let recurrence = rubi_simp(&(&(&b__ * &n_ * &p_ / denominator) * &recursive), x_);

            rubi_simp(&direct, x_) - rubi_star(Atom::num(1), recurrence)
        },
    ));
}

fn push_rules_rule_873(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a1__, b1__, a2__, m_, n_, p_, x_, b2__);
    rules.push(rubi_rule!(
        order: 873,
        source: "Int[x_^m_.*(a1_+b1_.*x_^n_)^p_*(a2_+b2_.*x_^n_)^p_,x_Symbol] :=
          x^(m+1)*(a1+b1*x^n)^p*(a2+b2*x^n)^p/(m+1) -
          2*b1*b2*n*p/(m+1) \\[Star] Int[x^(m+2*n)*(a1+b1*x^n)^(p-1)*(a2+b2*x^n)^(p-1),x] /;
        FreeQ[{a1,b1,a2,b2,m,n},x] && EqQ[a2*b1+a1*b2,0] && EqQ[(m+1)/(2*n)+p,0] && GtQ[p,0]",
        desc: "Integration by parts",
        refs: ["G&R 2.110.3"],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [a1__, b1__, a2__, b2__, m_, n_, p_, x_],
        optional: [b1__, b2__, m_],
        when: {
            freeq!([a1__, b1__, a2__, b2__, m_, n_], x_)
                && eqq!(&a2__ * &b1__ + &a1__ * &b2__, 0)
                && eqq!((&m_ + Atom::num(1)) / (Atom::num(2) * &n_) + &p_, 0)
                && gtq!(p_, 0)
        },
        rhs: {
            let denominator = &m_ + Atom::num(1);
            let monomial = x_.pow(&n_);
            let first = &a1__ + &b1__ * &monomial;
            let second = &a2__ + &b2__ * monomial;
            let direct = x_.pow(&m_ + Atom::num(1)) * first.pow(&p_) * second.pow(&p_) / &denominator;
            let recursive_integrand = x_.pow(&m_ + Atom::num(2) * &n_)
                * first.pow(&p_ - Atom::num(1))
                * second.pow(&p_ - Atom::num(1));
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let recurrence = rubi_simp(&(&(Atom::num(2) * &b1__ * &b2__ * &n_ * &p_ / denominator) * &recursive), x_);

            rubi_simp(&direct, x_) - rubi_star(Atom::num(1), recurrence)
        },
    ));
}

fn push_rules_rule_874(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 874,
        source: "Int[(c_*x_)^m_*(a_+b_.*x_^n_)^p_,x_Symbol] :=
          c^IntPart[m]*(c*x)^FracPart[m]/x^FracPart[m] \\[Star] Int[x^m*(a+b*x^n)^p,x] /;
        FreeQ[{a,b,c,m,n},x] && EqQ[(m+1)/n+p,0] && GtQ[p,0]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, m_, n_, p_, x_],
        optional: [b__],
        when: {
            freeq!([a__, b__, c__, m_, n_], x_)
                && eqq!((&m_ + Atom::num(1)) / &n_ + &p_, 0)
                && gtq!(p_, 0)
        },
        rhs: {
            let int_m = rubi_int_part(&m_);
            let frac_m = rubi_frac_part(&m_);
            let unscaled_integrand = x_.pow(&m_) * (&a__ + &b__ * x_.pow(&n_)).pow(&p_);
            let unscaled = rubi_rhs_int(&unscaled_integrand, x_);
            let coefficient = c__.pow(int_m) * (&c__ * x_).pow(&frac_m) / x_.pow(&frac_m);
            rubi_star(coefficient, unscaled)
        },
    ));
}

fn push_rules_rule_875(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a1__, b1__, c__, a2__, m_, n_, p_, x_, b2__);
    rules.push(rubi_rule!(
        order: 875,
        source: "Int[(c_*x_)^m_*(a1_+b1_.*x_^n_)^p_*(a2_+b2_.*x_^n_)^p_,x_Symbol] :=
          c^IntPart[m]*(c*x)^FracPart[m]/x^FracPart[m] \\[Star] Int[x^m*(a1+b1*x^n)^p*(a2+b2*x^n)^p,x] /;
        FreeQ[{a1,b1,a2,b2,c,m,n},x] && EqQ[a2*b1+a1*b2,0] && EqQ[(m+1)/(2*n)+p,0] && GtQ[p,0]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a1__, b1__, c__, a2__, b2__, m_, n_, p_, x_],
        optional: [b1__, b2__],
        when: {
            freeq!([a1__, b1__, a2__, b2__, c__, m_, n_], x_)
                && eqq!(&a2__ * &b1__ + &a1__ * &b2__, 0)
                && eqq!((&m_ + Atom::num(1)) / (Atom::num(2) * &n_) + &p_, 0)
                && gtq!(p_, 0)
        },
        rhs: {
            let int_m = rubi_int_part(&m_);
            let frac_m = rubi_frac_part(&m_);
            let monomial = x_.pow(&n_);
            let unscaled_integrand = x_.pow(&m_)
                * (&a1__ + &b1__ * &monomial).pow(&p_)
                * (&a2__ + &b2__ * monomial).pow(&p_);
            let unscaled = rubi_rhs_int(&unscaled_integrand, x_);
            let coefficient = c__.pow(int_m) * (&c__ * x_).pow(&frac_m) / x_.pow(&frac_m);
            rubi_star(coefficient, unscaled)
        },
    ));
}

fn push_rules_rule_876(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 876,
        source: "Int[(c_.*x_)^m_.*(a_+b_.*x_^n_)^p_,x_Symbol] :=
          (c*x)^(m+1)*(a+b*x^n)^p/(c*(m+n*p+1)) +
          a*n*p/(m+n*p+1) \\[Star] Int[(c*x)^m*(a+b*x^n)^(p-1),x] /;
        FreeQ[{a,b,c,m,n},x] && IntegerQ[p+Simplify[(m+1)/n]] && GtQ[p,0] && NeQ[m+n*p+1,0]",
        desc: "Inverted integration by parts",
        refs: ["G&R 2.110.1, CRC 88b"],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, m_, n_, p_, x_],
        optional: [b__, c__, m_],
        when: {
            freeq!([a__, b__, c__, m_, n_], x_)
                && integerq!(&p_ + rubi_simplify(&((&m_ + Atom::num(1)) / &n_)))
                && gtq!(p_, 0)
                && neq!(&m_ + &n_ * &p_ + Atom::num(1), 0)
        },
        rhs: {
            let denominator = &m_ + &n_ * &p_ + Atom::num(1);
            let scaled = &c__ * x_;
            let base = &a__ + &b__ * x_.pow(&n_);
            let direct = scaled.pow(&m_ + Atom::num(1)) * base.pow(&p_) / (&c__ * &denominator);
            let recursive_integrand = scaled.pow(&m_) * base.pow(&p_ - Atom::num(1));
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let recurrence = rubi_simp(&(&(&a__ * &n_ * &p_ / denominator) * &recursive), x_);

            rubi_simp(&direct, x_) + rubi_star(Atom::num(1), recurrence)
        },
    ));
}

fn push_rules_rule_877(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a1__, b1__, c__, a2__, m_, n_, p_, x_, b2__);
    rules.push(rubi_rule!(
        order: 877,
        source: "Int[(c_.*x_)^m_.*(a1_+b1_.*x_^n_)^p_*(a2_+b2_.*x_^n_)^p_,x_Symbol] :=
          (c*x)^(m+1)*(a1+b1*x^n)^p*(a2+b2*x^n)^p/(c*(m+2*n*p+1)) +
          2*a1*a2*n*p/(m+2*n*p+1) \\[Star] Int[(c*x)^m*(a1+b1*x^n)^(p-1)*(a2+b2*x^n)^(p-1),x] /;
        FreeQ[{a1,b1,a2,b2,c,m,n},x] && EqQ[a2*b1+a1*b2,0] && IntegerQ[p+Simplify[(m+1)/(2*n)]] && GtQ[p,0] && NeQ[m+2*n*p+1,0]",
        desc: "Inverted integration by parts",
        refs: ["G&R 2.110.1, CRC 88b"],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a1__, b1__, c__, a2__, b2__, m_, n_, p_, x_],
        optional: [b1__, c__, b2__, m_],
        when: {
            freeq!([a1__, b1__, a2__, b2__, c__, m_, n_], x_)
                && eqq!(&a2__ * &b1__ + &a1__ * &b2__, 0)
                && integerq!(
                    &p_ + rubi_simplify(
                        &((&m_ + Atom::num(1)) / (Atom::num(2) * &n_))
                    )
                )
                && gtq!(p_, 0)
                && neq!(&m_ + Atom::num(2) * &n_ * &p_ + Atom::num(1), 0)
        },
        rhs: {
            let denominator = &m_ + Atom::num(2) * &n_ * &p_ + Atom::num(1);
            let scaled = &c__ * x_;
            let monomial = x_.pow(&n_);
            let first = &a1__ + &b1__ * &monomial;
            let second = &a2__ + &b2__ * monomial;
            let direct = scaled.pow(&m_ + Atom::num(1)) * first.pow(&p_) * second.pow(&p_)
                / (&c__ * &denominator);
            let recursive_integrand =
                scaled.pow(&m_) * first.pow(&p_ - Atom::num(1)) * second.pow(&p_ - Atom::num(1));
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let recurrence = rubi_simp(&(&(Atom::num(2) * &a1__ * &a2__ * &n_ * &p_ / denominator) * &recursive), x_);

            rubi_simp(&direct, x_) + rubi_star(Atom::num(1), recurrence)
        },
    ));
}

fn push_rules_rule_880(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 880,
        source: "Int[x_^m_.*(a_+b_.*x_^n_)^p_,x_Symbol] :=
          With[{k=Denominator[p]},
          k*a^(p+Simplify[(m+1)/n])/n \\[Star]
            Subst[Int[x^(k*Simplify[(m+1)/n]-1)/(1-b*x^k)^(p+Simplify[(m+1)/n]+1),x],x,x^(n/k)/(a+b*x^n)^(1/k)]] /;
        FreeQ[{a,b,m,n,p},x] && IntegerQ[p+Simplify[(m+1)/n]] && LtQ[-1,p,0]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [a__, b__, m_, n_, p_, x_],
        optional: [b__, m_],
        when: {
            let exponent = rubi_simplify(&((&m_ + Atom::num(1)) / &n_));
            freeq!([a__, b__, m_, n_, p_], x_)
                && integerq!(&p_ + exponent)
                && ltq!(-1, p_, 0)
        },
        rhs: {
            let k = Atom::num(rubi_denominator(&p_).rubi_rhs());
            let exponent = rubi_simplify(&((&m_ + Atom::num(1)) / &n_));
            let exponent_sum = &p_ + &exponent;
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = sub_atom.pow(&k * &exponent - Atom::num(1))
                / (Atom::num(1) - &b__ * sub_atom.pow(&k))
                    .pow(&exponent_sum + Atom::num(1));
            let transformed = rubi_rhs_int(&transformed_integrand, sub);

            let base = &a__ + &b__ * x_.pow(&n_);
            let replacement = x_.pow(&n_ / &k) / base.pow(Atom::num(1) / &k);
            let substituted = rubi_subst(&transformed, sub, replacement);
            let coefficient = &k * a__.pow(exponent_sum) / &n_;

            rubi_star(coefficient, substituted)
        },
    ));
}

fn push_rules_rule_881(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a1__, b1__, a2__, m_, n_, p_, x_, b2__);
    rules.push(rubi_rule!(
        order: 881,
        source: "Int[x_^m_.*(a1_+b1_.*x_^n_)^p_*(a2_+b2_.*x_^n_)^p_,x_Symbol] :=
          With[{k=Denominator[p]},
          k*(a1*a2)^(p+Simplify[(m+1)/(2*n)])/(2*n) \\[Star]
            Subst[Int[x^(k*Simplify[(m+1)/(2*n)]-1)/(1-b1*b2*x^k)^(p+Simplify[(m+1)/(2*n)]+1),x],x,x^(2*n/k)/((a1+b1*x^n)^(1/k)*(a2+b2*x^n)^(1/k))]] /;
        FreeQ[{a1,b1,a2,b2,m,n,p},x] && EqQ[a2*b1+a1*b2,0] && IntegerQ[p+Simplify[(m+1)/(2*n)]] && LtQ[-1,p,0]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [a1__, b1__, a2__, b2__, m_, n_, p_, x_],
        optional: [b1__, b2__, m_],
        when: {
            let exponent = rubi_simplify(&((&m_ + Atom::num(1)) / (Atom::num(2) * &n_)));
            freeq!([a1__, b1__, a2__, b2__, m_, n_, p_], x_)
                && eqq!(&a2__ * &b1__ + &a1__ * &b2__, 0)
                && integerq!(&p_ + exponent)
                && ltq!(-1, p_, 0)
        },
        rhs: {
            let k = Atom::num(rubi_denominator(&p_).rubi_rhs());
            let exponent = rubi_simplify(
                &((&m_ + Atom::num(1)) / (Atom::num(2) * &n_)),
            );
            let exponent_sum = &p_ + &exponent;
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = sub_atom.pow(&k * &exponent - Atom::num(1))
                / (Atom::num(1) - &b1__ * &b2__ * sub_atom.pow(&k))
                    .pow(&exponent_sum + Atom::num(1));
            let transformed = rubi_rhs_int(&transformed_integrand, sub);

            let monomial = x_.pow(&n_);
            let first = &a1__ + &b1__ * &monomial;
            let second = &a2__ + &b2__ * monomial;
            let replacement = x_.pow(Atom::num(2) * &n_ / &k)
                / (first.pow(Atom::num(1) / &k) * second.pow(Atom::num(1) / &k));
            let substituted = rubi_subst(&transformed, sub, replacement);
            let coefficient = &k * (&a1__ * &a2__).pow(exponent_sum)
                / (Atom::num(2) * &n_);

            rubi_star(coefficient, substituted)
        },
    ));
}

fn push_rules_rule_882(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 882,
        source: "Int[x_^m_.*(a_+b_.*x_^n_)^p_,x_Symbol] :=
          a^Simplify[(m+1)/n+p]*x^m*(a+b*x^n)^p*(x^n/(a+b*x^n))^p/(n*x^Simplify[m+n*p]) \\[Star]
            Subst[Int[x^((m+1)/n-1)/(1-b*x)^(Simplify[(m+1)/n+p]+1),x],x,x^n/(a+b*x^n)] /;
        FreeQ[{a,b,m,n,p},x] && IntegerQ[Simplify[(m+1)/n+p]]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [a__, b__, m_, n_, p_, x_],
        optional: [b__, m_],
        when: {
            let exponent_sum = rubi_simplify(&((&m_ + Atom::num(1)) / &n_ + &p_));
            freeq!([a__, b__, m_, n_, p_], x_)
                && integerq!(exponent_sum)
        },
        rhs: {
            let base = &a__ + &b__ * x_.pow(&n_);
            let exponent_sum = rubi_simplify(&((&m_ + Atom::num(1)) / &n_ + &p_));
            let replacement = x_.pow(&n_) / &base;

            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = sub_atom.pow(
                (&m_ + Atom::num(1)) / &n_ - Atom::num(1),
            ) / (Atom::num(1) - &b__ * &sub_atom)
                .pow(&exponent_sum + Atom::num(1));
            let transformed = rubi_rhs_int(&transformed_integrand, sub);
            let substituted = rubi_subst(&transformed, sub, &replacement);

            let coefficient = a__.pow(&exponent_sum)
                * x_.pow(&m_)
                * base.pow(&p_)
                * replacement.pow(&p_)
                / (&n_ * x_.pow(rubi_simplify(&(&m_ + &n_ * &p_))));

            rubi_star(coefficient, substituted)
        },
    ));
}

fn push_rules_rule_883(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 883,
        source: "Int[(c_*x_)^m_*(a_+b_.*x_^n_)^p_,x_Symbol] :=
          c^IntPart[m]*(c*x)^FracPart[m]/x^FracPart[m] \\[Star] Int[x^m*(a+b*x^n)^p,x] /;
        FreeQ[{a,b,c,m,n,p},x] && IntegerQ[Simplify[(m+1)/n+p]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, m_, n_, p_, x_],
        optional: [b__],
        when: {
            let exponent_sum = rubi_simplify(&((&m_ + Atom::num(1)) / &n_ + &p_));
            freeq!([a__, b__, c__, m_, n_, p_], x_) && integerq!(exponent_sum)
        },
        rhs: {
            let int_m = rubi_int_part(&m_);
            let frac_m = rubi_frac_part(&m_);
            let unscaled_integrand = x_.pow(&m_) * (&a__ + &b__ * x_.pow(&n_)).pow(&p_);
            let unscaled = rubi_rhs_int(&unscaled_integrand, x_);
            let coefficient = c__.pow(int_m) * (&c__ * x_).pow(&frac_m)
                / x_.pow(&frac_m);

            rubi_star(coefficient, unscaled)
        },
    ));
}

fn push_rules_rule_884(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a1__, b1__, c__, a2__, m_, n_, p_, x_, b2__);
    rules.push(rubi_rule!(
        order: 884,
        source: "Int[(c_*x_)^m_*(a1_+b1_.*x_^n_)^p_*(a2_+b2_.*x_^n_)^p_,x_Symbol] :=
          c^IntPart[m]*(c*x)^FracPart[m]/x^FracPart[m] \\[Star] Int[x^m*(a1+b1*x^n)^p*(a2+b2*x^n)^p,x] /;
        FreeQ[{a1,b1,a2,b2,c,m,n,p},x] && EqQ[a2*b1+a1*b2,0] && IntegerQ[p+Simplify[(m+1)/(2*n)]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a1__, b1__, c__, a2__, b2__, m_, n_, p_, x_],
        optional: [b1__, b2__],
        when: {
            let exponent = rubi_simplify(&((&m_ + Atom::num(1)) / (Atom::num(2) * &n_)));
            freeq!([a1__, b1__, a2__, b2__, c__, m_, n_, p_], x_)
                && eqq!(&a2__ * &b1__ + &a1__ * &b2__, 0)
                && integerq!(&p_ + exponent)
        },
        rhs: {
            let int_m = rubi_int_part(&m_);
            let frac_m = rubi_frac_part(&m_);
            let monomial = x_.pow(&n_);
            let unscaled_integrand = x_.pow(&m_)
                * (&a1__ + &b1__ * &monomial).pow(&p_)
                * (&a2__ + &b2__ * monomial).pow(&p_);
            let unscaled = rubi_rhs_int(&unscaled_integrand, x_);
            let coefficient = c__.pow(int_m) * (&c__ * x_).pow(&frac_m)
                / x_.pow(&frac_m);

            rubi_star(coefficient, unscaled)
        },
    ));
}

fn push_rules_rule_878(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 878,
        source: "Int[(c_.*x_)^m_.*(a_+b_.*x_^n_)^p_,x_Symbol] :=
          -(c*x)^(m+1)*(a+b*x^n)^(p+1)/(a*c*n*(p+1)) +
          (m+n*(p+1)+1)/(a*n*(p+1)) \\[Star] Int[(c*x)^m*(a+b*x^n)^(p+1),x] /;
        FreeQ[{a,b,c,m,n},x] && IntegerQ[p+Simplify[(m+1)/n]] && LtQ[p,-1]",
        desc: "Integration by parts",
        refs: ["G&R 2.110.2, CRC 88d"],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, m_, n_, p_, x_],
        optional: [b__, c__, m_],
        when: {
            freeq!([a__, b__, c__, m_, n_], x_)
                && integerq!(
                    &p_ + rubi_simplify(&((&m_ + Atom::num(1)) / &n_))
                )
                && ltq!(p_, -1)
        },
        rhs: {
            let p1 = &p_ + Atom::num(1);
            let scaled = &c__ * x_;
            let base = &a__ + &b__ * x_.pow(&n_);
            let direct = -scaled.pow(&m_ + Atom::num(1)) * base.pow(&p1)
                / (&a__ * &c__ * &n_ * &p1);
            let recursive_integrand = scaled.pow(&m_) * base.pow(&p1);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let recurrence_factor = (&m_ + &n_ * &p1 + Atom::num(1))
                / (&a__ * &n_ * &p1);
            let recurrence = rubi_simp(&(&recurrence_factor * &recursive), x_);

            rubi_simp(&direct, x_) + rubi_star(Atom::num(1), recurrence)
        },
    ));
}

fn push_rules_rule_879(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a1__, b1__, c__, a2__, m_, n_, p_, x_, b2__);
    rules.push(rubi_rule!(
        order: 879,
        source: "Int[(c_.*x_)^m_.*(a1_+b1_.*x_^n_)^p_*(a2_+b2_.*x_^n_)^p_,x_Symbol] :=
          -(c*x)^(m+1)*(a1+b1*x^n)^(p+1)*(a2+b2*x^n)^(p+1)/(2*a1*a2*c*n*(p+1)) +
          (m+2*n*(p+1)+1)/(2*a1*a2*n*(p+1)) \\[Star] Int[(c*x)^m*(a1+b1*x^n)^(p+1)*(a2+b2*x^n)^(p+1),x] /;
        FreeQ[{a1,b1,a2,b2,c,m,n},x] && EqQ[a2*b1+a1*b2,0] && IntegerQ[p+Simplify[(m+1)/(2*n)]] && LtQ[p,-1]",
        desc: "Integration by parts",
        refs: ["G&R 2.110.2, CRC 88d"],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a1__, b1__, c__, a2__, b2__, m_, n_, p_, x_],
        optional: [b1__, c__, b2__, m_],
        when: {
            freeq!([a1__, b1__, a2__, b2__, c__, m_, n_], x_)
                && eqq!(&a2__ * &b1__ + &a1__ * &b2__, 0)
                && integerq!(
                    &p_ + rubi_simplify(
                        &((&m_ + Atom::num(1)) / (Atom::num(2) * &n_))
                    )
                )
                && ltq!(p_, -1)
        },
        rhs: {
            let p1 = &p_ + Atom::num(1);
            let scaled = &c__ * x_;
            let monomial = x_.pow(&n_);
            let first = &a1__ + &b1__ * &monomial;
            let second = &a2__ + &b2__ * monomial;
            let direct = -scaled.pow(&m_ + Atom::num(1))
                * first.pow(&p1)
                * second.pow(&p1)
                / (Atom::num(2) * &a1__ * &a2__ * &c__ * &n_ * &p1);
            let recursive_integrand = scaled.pow(&m_) * first.pow(&p1) * second.pow(&p1);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let recurrence_factor = (&m_ + Atom::num(2) * &n_ * &p1 + Atom::num(1))
                / (Atom::num(2) * &a1__ * &a2__ * &n_ * &p1);
            let recurrence = rubi_simp(&(&recurrence_factor * &recursive), x_);

            rubi_simp(&direct, x_) + rubi_star(Atom::num(1), recurrence)
        },
    ));
}

fn push_rules_rule_885(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 885,
        source: "Int[x_^m_./(a_+b_.*x_^n_),x_Symbol] :=
          With[{mn=Simplify[m-n]},
          x^(mn+1)/(b*(mn+1)) -
          a/b \\[Star] Int[x^mn/(a+b*x^n),x]] /;
        FreeQ[{a,b,m,n},x] && FractionQ[Simplify[(m+1)/n]] && SumSimplerQ[m,-n]",
        desc: "Binomial recurrence 3a with p=-1",
        refs: ["CRC 86"],
        pattern:  rubi_shared_pattern_11(symbols),
        with: [a__, b__, m_, n_, x_],
        optional: [b__, m_],
        when: {
            let quotient = rubi_simplify(&((&m_ + Atom::num(1)) / &n_));
            freeq!([a__, b__, m_, n_], x_)
                && fractionq!(quotient)
                && rubi_sum_simpler_q(&m_, &(-&n_))
        },
        rhs: {
            let mn = rubi_simplify(&(&m_ - &n_));
            let base = &a__ + &b__ * x_.pow(&n_);
            let recursive_integrand = x_.pow(&mn) / base;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let direct = x_.pow(&mn + Atom::num(1))
                / (&b__ * (&mn + Atom::num(1)));
            let recurrence = rubi_simp(&(&(&a__ / &b__) * &recursive), x_);

            rubi_simp(&direct, x_) - rubi_star(Atom::num(1), recurrence)
        },
    ));
}

fn push_rules_rule_886(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 886,
        source: "Int[x_^m_/(a_+b_.*x_^n_),x_Symbol] :=
          x^(m+1)/(a*(m+1)) -
          b/a \\[Star] Int[x^Simplify[m+n]/(a+b*x^n),x] /;
        FreeQ[{a,b,m,n},x] && FractionQ[Simplify[(m+1)/n]] && SumSimplerQ[m,n]",
        desc: "Binomial recurrence 3b with p=-1",
        refs: ["CRC 87"],
        pattern:  rubi_shared_pattern_11(symbols),
        with: [a__, b__, m_, n_, x_],
        optional: [b__],
        when: {
            let quotient = rubi_simplify(&((&m_ + Atom::num(1)) / &n_));
            freeq!([a__, b__, m_, n_], x_)
                && fractionq!(quotient)
                && rubi_sum_simpler_q(&m_, &n_)
        },
        rhs: {
            let base = &a__ + &b__ * x_.pow(&n_);
            let recursive_integrand = x_.pow(rubi_simplify(&(&m_ + &n_))) / base;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let direct = x_.pow(&m_ + Atom::num(1))
                / (&a__ * (&m_ + Atom::num(1)));
            let recurrence = rubi_simp(&(&(&b__ / &a__) * &recursive), x_);

            rubi_simp(&direct, x_) - rubi_star(Atom::num(1), recurrence)
        },
    ));
}

fn push_rules_rule_887(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, m_, n_, x_);
    rules.push(rubi_rule!(
        order: 887,
        source: "Int[(c_*x_)^m_/(a_+b_.*x_^n_),x_Symbol] :=
          c^IntPart[m]*(c*x)^FracPart[m]/x^FracPart[m] \\[Star] Int[x^m/(a+b*x^n),x] /;
        FreeQ[{a,b,c,m,n},x] && FractionQ[Simplify[(m+1)/n]] && (SumSimplerQ[m,n] || SumSimplerQ[m,-n])",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: (c__ * x_).pow(m_) / (a__ + b__ * x_.pow(n_)),
        with: [a__, b__, c__, m_, n_, x_],
        optional: [b__],
        when: {
            let quotient = rubi_simplify(&((&m_ + Atom::num(1)) / &n_));
            freeq!([a__, b__, c__, m_, n_], x_)
                && fractionq!(quotient)
                && (rubi_sum_simpler_q(&m_, &n_) || rubi_sum_simpler_q(&m_, &(-&n_)))
        },
        rhs: {
            let int_m = rubi_int_part(&m_);
            let frac_m = rubi_frac_part(&m_);
            let unscaled_integrand = x_.pow(&m_) / (&a__ + &b__ * x_.pow(&n_));
            let unscaled = rubi_rhs_int(&unscaled_integrand, x_);
            let coefficient = c__.pow(int_m) * (&c__ * x_).pow(&frac_m)
                / x_.pow(&frac_m);

            rubi_star(coefficient, unscaled)
        },
    ));
}

fn push_rules_rule_888(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 888,
        source: "Int[(c_.*x_)^m_.*(a_+b_.*x_^n_)^p_,x_Symbol] :=
          a^p*(c*x)^(m+1)/(c*(m+1))*Hypergeometric2F1[-p,(m+1)/n,(m+1)/n+1,-b*x^n/a] /;
        FreeQ[{a,b,c,m,n,p},x] && Not[IGtQ[p,0]] && (ILtQ[p,0] || GtQ[a,0])",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, m_, n_, p_, x_],
        optional: [b__, c__, m_],
        when: {
            freeq!([a__, b__, c__, m_, n_, p_], x_)
                && !igtq!(p_, 0)
                && (iltq!(p_, 0) || gtq!(a__, 0))
        },
        rhs: {
            let scaled = &c__ * x_;
            let second = (&m_ + Atom::num(1)) / &n_;
            rubi_simp(
                &(a__.pow(&p_)
                    * scaled.pow(&m_ + Atom::num(1))
                    * rubi_hypergeometric2f1(
                        -&p_,
                        &second,
                        &second + Atom::num(1),
                        -&b__ * x_.pow(&n_) / &a__,
                    )
                    / (&c__ * (&m_ + Atom::num(1)))),
                x_,
            )
        },
    ));
}

fn push_rules_rule_889(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 889,
        source: "Int[(c_.*x_)^m_.*(a_+b_.*x_^n_)^p_,x_Symbol] :=
          a^IntPart[p]*(a+b*x^n)^FracPart[p]/(1+b*x^n/a)^FracPart[p] \\[Star] Int[(c*x)^m*(1+b*x^n/a)^p,x] /;
        FreeQ[{a,b,c,m,n,p},x] && Not[IGtQ[p,0]] && Not[ILtQ[p,0] || GtQ[a,0]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, m_, n_, p_, x_],
        optional: [b__, c__, m_],
        when: {
            freeq!([a__, b__, c__, m_, n_, p_], x_)
                && !igtq!(p_, 0)
                && !(iltq!(p_, 0) || gtq!(a__, 0))
        },
        rhs: {
            let int_p = rubi_int_part(&p_);
            let frac_p = rubi_frac_part(&p_);
            let base = &a__ + &b__ * x_.pow(&n_);
            let normalized_base = Atom::num(1) + &b__ * x_.pow(&n_) / &a__;
            let recursive_integrand = (&c__ * x_).pow(&m_) * normalized_base.pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let coefficient = a__.pow(int_p) * base.pow(&frac_p)
                / normalized_base.pow(&frac_p);

            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_890(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a1__, b1__, c__, a2__, m_, n_, p_, x_, b2__);
    rules.push(rubi_rule!(
        order: 890,
        source: "Int[(c_.*x_)^m_.*(a1_+b1_.*x_^n_)^p_*(a2_+b2_.*x_^n_)^p_,x_Symbol] :=
          (a1+b1*x^n)^FracPart[p]*(a2+b2*x^n)^FracPart[p]/(a1*a2+b1*b2*x^(2*n))^FracPart[p] \\[Star] Int[(c*x)^m*(a1*a2+b1*b2*x^(2*n))^p,x] /;
        FreeQ[{a1,b1,a2,b2,c,m,n,p},x] && EqQ[a2*b1+a1*b2,0] && Not[IntegerQ[p]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a1__, b1__, c__, a2__, b2__, m_, n_, p_, x_],
        optional: [b1__, c__, b2__, m_],
        when: {
            freeq!([a1__, b1__, a2__, b2__, c__, m_, n_, p_], x_)
                && eqq!(&a2__ * &b1__ + &a1__ * &b2__, 0)
                && !integerq!(p_)
        },
        rhs: {
            let frac_p = rubi_frac_part(&p_);
            let monomial = x_.pow(&n_);
            let first = &a1__ + &b1__ * &monomial;
            let second = &a2__ + &b2__ * &monomial;
            let combined = &a1__ * &a2__ + &b1__ * &b2__ * x_.pow(Atom::num(2) * &n_);
            let recursive_integrand = (&c__ * x_).pow(&m_) * combined.pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let coefficient = first.pow(&frac_p) * second.pow(&frac_p)
                / combined.pow(&frac_p);

            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_891(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 891,
        source: "Int[(d_.*x_)^m_.*(a_+b_.*(c_*x_)^n_)^p_.,x_Symbol] :=
          1/c \\[Star] Subst[Int[(d*x/c)^m*(a+b*x^n)^p,x],x,c*x] /;
        FreeQ[{a,b,c,d,m,n,p},x]",
        desc: "Piecewise constant extraction and integration by substitution",
        refs: [],
        pattern: (d__ * x_).pow(m_) * (a__ + b__ * (c__ * x_).pow(n_)).pow(p_),
        with: [a__, b__, c__, d__, m_, n_, p_, x_],
        optional: [b__, d__, m_, p_],
        when: { freeq!([a__, b__, c__, d__, m_, n_, p_], x_) },
        rhs: {
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = (&d__ * &sub_atom / &c__).pow(&m_)
                * (&a__ + &b__ * sub_atom.pow(&n_)).pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);
            let substituted = rubi_subst(&transformed, sub, &c__ * x_);

            rubi_star(Atom::num(1) / &c__, substituted)
        },
    ));
}

fn push_rules_rule_892(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 892,
        source: "Int[(d_.*x_)^m_.*(a_+b_.*(c_.*x_^q_)^n_)^p_.,x_Symbol] :=
          (d*x)^(m+1)/(d*((c*x^q)^(1/q))^(m+1)) \\[Star] Subst[Int[x^m*(a+b*x^(n*q))^p,x],x,(c*x^q)^(1/q)] /;
        FreeQ[{a,b,c,d,m,n,p,q},x] && IntegerQ[n*q] && NeQ[x,(c*x^q)^(1/q)]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, m_, n_, p_, q_, x_],
        optional: [b__, c__, d__, m_, p_],
        when: {
            let replacement = (&c__ * x_.pow(&q_)).pow(Atom::num(1) / &q_);
            freeq!([a__, b__, c__, d__, m_, n_, p_, q_], x_)
                && integerq!(&n_ * &q_)
                && neq!(x_, replacement)
        },
        rhs: {
            let replacement = (&c__ * x_.pow(&q_)).pow(Atom::num(1) / &q_);
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = sub_atom.pow(&m_)
                * (&a__ + &b__ * sub_atom.pow(&n_ * &q_)).pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);
            let substituted = rubi_subst(&transformed, sub, &replacement);
            let coefficient = (&d__ * x_).pow(&m_ + Atom::num(1))
                / (&d__ * replacement.pow(&m_ + Atom::num(1)));

            rubi_star(coefficient, substituted)
        },
    ));
}

fn push_rules_rule_893(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 893,
        source: "Int[(d_.*x_)^m_.*(a_+b_.*(c_.*x_^q_)^n_)^p_.,x_Symbol] :=
          With[{k=Denominator[n]},
          Subst[Int[(d*x)^m*(a+b*c^n*x^(n*q))^p,x],x^(1/k),(c*x^q)^(1/k)/(c^(1/k)*(x^(1/k))^(q-1))]] /;
        FreeQ[{a,b,c,d,m,p,q},x] && FractionQ[n]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, m_, n_, p_, q_, x_],
        optional: [b__, c__, d__, m_, p_],
        when: { freeq!([a__, b__, c__, d__, m_, p_, q_], x_) && fractionq!(n_) },
        rhs: {
            let k = Atom::num(rubi_denominator(&n_).rubi_rhs());
            let integrand = (&d__ * x_).pow(&m_)
                * (&a__ + &b__ * c__.pow(&n_) * x_.pow(&n_ * &q_)).pow(&p_);
            let monomial_exponent = Atom::num(1) / &k;
            let replacement = (&c__ * x_.pow(&q_)).pow(Atom::num(1) / &k)
                / (c__.pow(Atom::num(1) / &k)
                    * x_
                        .pow(Atom::num(1) / &k)
                        .pow(&q_ - Atom::num(1)));

            rubi_subst_integral_monomial(&integrand, x_, &monomial_exponent, replacement).rubi_rhs()
        },
    ));
}

fn push_rules_rule_894(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 894,
        source: "Int[(d_.*x_)^m_.*(a_+b_.*(c_.*x_^q_)^n_)^p_.,x_Symbol] :=
          Subst[Int[(d*x)^m*(a+b*c^n*x^(n*q))^p,x],x^(n*q),(c*x^q)^n/c^n] /;
        FreeQ[{a,b,c,d,m,n,p,q},x] && Not[RationalQ[n]]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, m_, n_, p_, q_, x_],
        optional: [b__, c__, d__, m_, p_],
        when: { freeq!([a__, b__, c__, d__, m_, n_, p_, q_], x_) && !rationalq!(n_) },
        rhs: {
            let integrand = (&d__ * x_).pow(&m_)
                * (&a__ + &b__ * c__.pow(&n_) * x_.pow(&n_ * &q_)).pow(&p_);
            let monomial_exponent = &n_ * &q_;
            let replacement = (&c__ * x_.pow(&q_)).pow(&n_) / c__.pow(&n_);

            rubi_subst_integral_monomial(&integrand, x_, &monomial_exponent, replacement).rubi_rhs()
        },
    ));
}

fn push_rules_rule_896(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, m_, n_, p_, v__, x_);
    let rule = rubi_rule!(
        order: 896,
        source: "Int[x_^m_.*(a_+b_.*v_^n_)^p_.,x_Symbol] :=
          With[{c=Coefficient[v,x,0],d=Coefficient[v,x,1]},
          1/d^(m+1) \\[Star] Subst[Int[SimplifyIntegrand[(x-c)^m*(a+b*x^n)^p,x],x],x,v] /;
         NeQ[c,0]] /;
        FreeQ[{a,b,n,p},x] && LinearQ[v,x] && IntegerQ[m]",
        desc: "Integration by substitution and piecewise constant extraction",
        refs: [],
        pattern: x_.pow(m_) * (a__ + b__ * v__.pow(n_)).pow(p_),
        with: [a__, b__, v__, m_, n_, p_, x_],
        optional: [b__, m_, p_],
        x_dep: [v__],
        x_free: [a__, b__, m_, n_, p_],
        x_linear: [v__],
        when: {
            let c = rubi_coefficient(&v__, x_, 0);
            freeq!([a__, b__, n_, p_], x_)
                && rubi_linear_q(&v__, x_)
                && integerq!(m_)
                && c.is_some_and(|c| neq!(c, 0))
        },
        rhs: {
            let c = rubi_coefficient(&v__, x_, 0).rubi_rhs();
            let d = rubi_coefficient(&v__, x_, 1).rubi_rhs();

            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = rubi_simplify_integrand(
                &((&sub_atom - c).pow(&m_)
                    * (&a__ + &b__ * sub_atom.pow(&n_)).pow(&p_)),
                sub,
            );
            let transformed = rubi_rhs_int(&transformed_integrand, sub);
            let substituted = rubi_subst(&transformed, sub, &v__);
            let coefficient = Atom::num(1) / d.pow(&m_ + Atom::num(1));

            rubi_star(coefficient, substituted)
        },
    );
    rules.push(rule.with_explicit_variable_power_factor());
}

fn push_rules_rule_895(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, m_, n_, p_, u__, v__);
    let rule = rubi_rule!(
        order: 895,
        source: "Int[u_^m_.*(a_+b_.*v_^n_)^p_.,x_Symbol] :=
          u^m/(Coefficient[v,x,1]*v^m) \\[Star] Subst[Int[x^m*(a+b*x^n)^p,x],x,v] /;
        FreeQ[{a,b,m,n,p},x] && LinearPairQ[u,v,x]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern: u__.pow(m_) * (a__ + b__ * v__.pow(n_)).pow(p_),
        with: [a__, b__, u__, v__, m_, n_, p_, x_],
        optional: [b__, m_, p_],
        x_dep: [u__, v__],
        x_free: [a__, b__, m_, n_, p_],
        x_linear: [u__, v__],
        when: { freeq!([a__, b__, m_, n_, p_], x_) && rubi_linear_pair_q(&u__, &v__, x_) },
        rhs: {
            let slope = rubi_coefficient(&v__, x_, 1).rubi_rhs();

            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = sub_atom.pow(&m_) * (&a__ + &b__ * sub_atom.pow(&n_)).pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);
            let substituted = rubi_subst(&transformed, sub, &v__);
            let coefficient = u__.pow(&m_) / (slope * v__.pow(&m_));

            rubi_star(coefficient, substituted)
        },
    );
    rules.push(rule.with_proportional_affine_factor_pair());
}

// Generated shared pattern builders.

#[inline(never)]
fn rubi_shared_pattern_0(symbols: &RubiSymbols) -> Atom {
    let a1__ = symbols.a1__;
    let a2__ = symbols.a2__;
    let b1__ = symbols.b1__;
    let b2__ = symbols.b2__;
    let c__ = symbols.c__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (c__ * x_).pow(m_) * (a1__ + b1__ * x_.pow(n_)).pow(p_) * (a2__ + b2__ * x_.pow(n_)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (c__ * x_).pow(m_) * (a__ + b__ * x_.pow(n_)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_2(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let q_ = symbols.q_;
    let x_ = symbols.x_;
    (d__ * x_).pow(m_) * (a__ + b__ * (c__ * x_.pow(q_)).pow(n_)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_3(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let x_ = symbols.x_;
    Atom::num(1) / (x_.pow(2) * (a__ + b__ * x_.pow(4)).pow((1, 4)))
}

#[inline(never)]
fn rubi_shared_pattern_4(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let x_ = symbols.x_;
    x_.pow(2) / (a__ + b__ * x_.pow(4))
}

#[inline(never)]
fn rubi_shared_pattern_5(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let x_ = symbols.x_;
    x_.pow(2) / (a__ + b__ * x_.pow(4)).pow((1, 4))
}

#[inline(never)]
fn rubi_shared_pattern_6(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let x_ = symbols.x_;
    x_.pow(2) / (a__ + b__ * x_.pow(4)).pow((5, 4))
}

#[inline(never)]
fn rubi_shared_pattern_7(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let x_ = symbols.x_;
    x_.pow(2) / (a__ + b__ * x_.pow(4)).sqrt()
}

#[inline(never)]
fn rubi_shared_pattern_8(symbols: &RubiSymbols) -> Atom {
    let a1__ = symbols.a1__;
    let a2__ = symbols.a2__;
    let b1__ = symbols.b1__;
    let b2__ = symbols.b2__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    x_.pow(m_) * (a1__ + b1__ * x_.pow(n_)).pow(p_) * (a2__ + b2__ * x_.pow(n_)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_9(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    x_.pow(m_) * (a__ + b__ * x_.pow(n_)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_10(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let m_ = symbols.m_;
    let x_ = symbols.x_;
    x_.pow(m_) / (a__ + b__ * x_.pow(4)).pow((5, 4))
}

#[inline(never)]
fn rubi_shared_pattern_11(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let m_ = symbols.m_;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    x_.pow(m_) / (a__ + b__ * x_.pow(n_))
}

#[inline(never)]
fn rubi_shared_pattern_12(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let x_ = symbols.x_;
    x_ / (a__ + b__ * x_.pow(3)).sqrt()
}
