use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_897(rules);
    push_rules_rule_898(rules);
    push_rules_rule_899(rules);
    push_rules_rule_900(rules);
    push_rules_rule_901(rules);
    push_rules_rule_902(rules);
    push_rules_rule_903(rules);
    push_rules_rule_904(rules);
    push_rules_rule_905(rules);
    push_rules_rule_906(rules);
    push_rules_rule_907(rules);
    push_rules_rule_908(rules);
    push_rules_rule_909(rules);
    push_rules_rule_910(rules);
    push_rules_rule_911(rules);
    push_rules_rule_912(rules);
    push_rules_rule_913(rules);
    push_rules_rule_914(rules);
    push_rules_rule_915(rules);
    push_rules_rule_916(rules);
    push_rules_rule_917(rules);
    push_rules_rule_918(rules);
    push_rules_rule_919(rules);
    push_rules_rule_920(rules);
    push_rules_rule_921(rules);
    push_rules_rule_922(rules);
    push_rules_rule_923(rules);
    push_rules_rule_924(rules);
    push_rules_rule_925(rules);
    push_rules_rule_926(rules);
    push_rules_rule_927(rules);
    push_rules_rule_928(rules);
    push_rules_rule_929(rules);
    push_rules_rule_930(rules);
    push_rules_rule_931(rules);
    push_rules_rule_932(rules);
    push_rules_rule_933(rules);
    push_rules_rule_934(rules);
    push_rules_rule_935(rules);
    push_rules_rule_936(rules);
    push_rules_rule_937(rules);
    push_rules_rule_938(rules);
    push_rules_rule_939(rules);
    push_rules_rule_940(rules);
    push_rules_rule_941(rules);
    push_rules_rule_942(rules);
}

fn push_rules_rule_897(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 897,
        source: "Int[(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_)^q_.,x_Symbol] :=
          Int[ExpandIntegrand[(a+b*x^n)^p*(c+d*x^n)^q,x],x] /;
        FreeQ[{a,b,c,d,n},x] && NeQ[b*c-a*d,0] && IGtQ[p,0] && IGtQ[q,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, n_, p_, q_, x_],
        optional: [b__, d__, p_, q_],
        x_free: [a__, b__, c__, d__, n_, p_, q_],
        when: {
            freeq!([a__, b__, c__, d__, n_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && igtq!(p_, 0)
                && igtq!(q_, 0)
        },
        rhs: {
            let integrand =
                (&a__ + &b__ * x_.pow(&n_)).pow(&p_) * (&c__ + &d__ * x_.pow(&n_)).pow(&q_);
            let expanded = rubi_expand_integrand(&integrand, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_898(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 898,
        source: "Int[(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_)^q_.,x_Symbol] :=
          Int[x^(n*(p+q))*(b+a*x^(-n))^p*(d+c*x^(-n))^q,x] /;
        FreeQ[{a,b,c,d,n},x] && NeQ[b*c-a*d,0] && IntegersQ[p,q] && NegQ[n]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, n_, p_, q_, x_],
        optional: [b__, d__, p_, q_],
        x_free: [a__, b__, c__, d__, n_, p_, q_],
        when: {
            freeq!([a__, b__, c__, d__, n_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && integersq!([p_, q_])
                && negq!(n_)
        },
        rhs: {
            let transformed_integrand = x_.pow(&n_ * (&p_ + &q_))
                * (&b__ + &a__ * x_.pow(-&n_)).pow(&p_)
                * (&d__ + &c__ * x_.pow(-&n_)).pow(&q_);
            rubi_rhs_int(&transformed_integrand, x_)
        },
    ));
}

fn push_rules_rule_899(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 899,
        source: "Int[(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_)^q_.,x_Symbol] :=
          -Subst[Int[(a+b*x^(-n))^p*(c+d*x^(-n))^q/x^2,x],x,1/x] /;
        FreeQ[{a,b,c,d,p,q},x] && NeQ[b*c-a*d,0] && ILtQ[n,0]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, n_, p_, q_, x_],
        optional: [b__, d__, p_, q_],
        x_free: [a__, b__, c__, d__, n_, p_, q_],
        when: {
            freeq!([a__, b__, c__, d__, p_, q_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && iltq!(n_, 0)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = (&a__ + &b__ * sub_atom.pow(-&n_)).pow(&p_)
                * (&c__ + &d__ * sub_atom.pow(-&n_)).pow(&q_)
                / sub_atom.pow(2);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);

            -rubi_subst(
                &transformed,
                sub,
                Atom::num(1) / x_,
            )
        },
    ));
}

fn push_rules_rule_900(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 900,
        source: "Int[(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_)^q_.,x_Symbol] :=
          With[{g=Denominator[n]},
          g \\[Star] Subst[Int[x^(g-1)*(a+b*x^(g*n))^p*(c+d*x^(g*n))^q,x],x,x^(1/g)]] /;
        FreeQ[{a,b,c,d,p,q},x] && NeQ[b*c-a*d,0] && FractionQ[n]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, n_, p_, q_, x_],
        optional: [b__, d__, p_, q_],
        x_free: [a__, b__, c__, d__, n_, p_, q_],
        when: {
            freeq!([a__, b__, c__, d__, p_, q_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && fractionq!(n_)
        },
        rhs: {
            let g = Atom::num(rubi_denominator(&n_).rubi_rhs());
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = sub_atom.pow(&g - Atom::num(1))
                * (&a__ + &b__ * sub_atom.pow(&g * &n_)).pow(&p_)
                * (&c__ + &d__ * sub_atom.pow(&g * &n_)).pow(&q_);
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

fn push_rules_rule_901(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 901,
        source: "Int[1/((a_+b_.*x_^3)^(1/3)*(c_+d_.*x_^3)),x_Symbol] :=
          With[{q=Rt[(b*c-a*d)/c,3]},
          ArcTan[(1+(2*q*x)/(a+b*x^3)^(1/3))/Sqrt[3]]/(Sqrt[3]*c*q) + Log[c+d*x^3]/(6*c*q) - Log[q*x-(a+b*x^3)^(1/3)]/(2*c*q)] /;
        FreeQ[{a,b,c,d},x] && NeQ[b*c-a*d,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: Atom::num(1) / ((a__ + b__ * x_.pow(3)).pow((1, 3)) * (c__ + d__ * x_.pow(3))),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, d__],
        when: { freeq!([a__, b__, c__, d__], x_) && neq!(&b__ * &c__ - &a__ * &d__, 0) },
        rhs: {
            let q = rubi_rt(&((&b__ * &c__ - &a__ * &d__) / &c__), 3);
            let base = &a__ + &b__ * x_.pow(3);
            let radical = base.pow((1, 3));
            let sqrt_three = Atom::num(3).sqrt();

            let first = ((Atom::num(1) + Atom::num(2) * &q * x_ / &radical)
                / &sqrt_three)
                .atan()
                / (&sqrt_three * &c__ * &q);
            let second = (&c__ + &d__ * x_.pow(3)).log()
                / (Atom::num(6) * &c__ * &q);
            let third = (&q * x_ - radical).log()
                / (Atom::num(2) * &c__ * &q);

            rubi_simp(&first, x_) + rubi_simp(&second, x_) - rubi_simp(&third, x_)
        },
    ));
}

fn push_rules_rule_902(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 902,
        source: "Int[(a_+b_.*x_^n_)^p_/(c_+d_.*x_^n_),x_Symbol] :=
          Subst[Int[1/(c-(b*c-a*d)*x^n),x],x,x/(a+b*x^n)^(1/n)] /;
        FreeQ[{a,b,c,d},x] && NeQ[b*c-a*d,0] && EqQ[n*p+1,0] && IntegerQ[n]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, b__, c__, d__, n_, p_, x_],
        optional: [b__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(&n_ * &p_ + Atom::num(1), 0)
                && integerq!(n_)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = Atom::num(1) / (&c__ - (&b__ * &c__ - &a__ * &d__) * sub_atom.pow(&n_));
            let transformed = rubi_rhs_int(&transformed_integrand, sub);

            let replacement = x_ / (&a__ + &b__ * x_.pow(&n_)).pow(Atom::num(1) / &n_);
            rubi_subst(&transformed, sub, replacement)
        },
    ));
}

fn push_rules_rule_903(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 903,
        source: "Int[(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_.,x_Symbol] :=
          -x*(a+b*x^n)^(p+1)*(c+d*x^n)^q/(a*n*(p+1)) -
          c*q/(a*(p+1)) \\[Star] Int[(a+b*x^n)^(p+1)*(c+d*x^n)^(q-1),x] /;
        FreeQ[{a,b,c,d,n,p},x] && NeQ[b*c-a*d,0] && EqQ[n*(p+q+1)+1,0] && GtQ[q,0] && NeQ[p,-1]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, n_, p_, q_, x_],
        optional: [b__, d__, q_],
        x_free: [a__, b__, c__, d__, n_, p_, q_],
        when: {
            freeq!([a__, b__, c__, d__, n_, p_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(&n_ * (&p_ + &q_ + Atom::num(1)) + Atom::num(1), 0)
                && gtq!(q_, 0)
                && neq!(p_, -Atom::num(1))
        },
        rhs: {
            let first_base = &a__ + &b__ * x_.pow(&n_);
            let second_base = &c__ + &d__ * x_.pow(&n_);
            let recursive_integrand =
                first_base.pow(&p_ + Atom::num(1)) * second_base.pow(&q_ - Atom::num(1));
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let direct = Atom::num(-1) * x_ * first_base.pow(&p_ + Atom::num(1)) * second_base.pow(&q_)
                / (&a__ * &n_ * (&p_ + Atom::num(1)));
            let recurrence = rubi_simp(&(&(&c__ * &q_ / (&a__ * (&p_ + Atom::num(1)))) * &recursive), x_);

            rubi_simp(&direct, x_) - rubi_star(Atom::num(1), recurrence)
        },
    ));
}

fn push_rules_rule_904(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 904,
        source: "Int[(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
          a^p*x/(c^(p+1)*(c+d*x^n)^(1/n))*Hypergeometric2F1[1/n,-p,1+1/n,-(b*c-a*d)*x^n/(a*(c+d*x^n))] /;
        FreeQ[{a,b,c,d,n,q},x] && NeQ[b*c-a*d,0] && EqQ[n*(p+q+1)+1,0] && ILtQ[p,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, n_, p_, q_, x_],
        optional: [b__, d__],
        when: {
            freeq!([a__, b__, c__, d__, n_, q_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(&n_ * (&p_ + &q_ + Atom::num(1)) + Atom::num(1), 0)
                && iltq!(p_, 0)
        },
        rhs: {
            let second_base = &c__ + &d__ * x_.pow(&n_);
            rubi_simp(
                &(a__.pow(&p_) * x_
                    * rubi_hypergeometric2f1(
                        Atom::num(1) / &n_,
                        -&p_,
                        Atom::num(1) + Atom::num(1) / &n_,
                        -(&b__ * &c__ - &a__ * &d__) * x_.pow(&n_) / (&a__ * &second_base),
                    )
                    / (c__.pow(&p_ + Atom::num(1)) * second_base.pow(Atom::num(1) / &n_))),
                x_,
            )
        },
    ));
}

fn push_rules_rule_905(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 905,
        source: "Int[(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
          x*(a+b*x^n)^p/(c*(c*(a+b*x^n)/(a*(c+d*x^n)))^p*(c+d*x^n)^(1/n+p))*
            Hypergeometric2F1[1/n,-p,1+1/n,-(b*c-a*d)*x^n/(a*(c+d*x^n))] /;
        FreeQ[{a,b,c,d,n,p,q},x] && NeQ[b*c-a*d,0] && EqQ[n*(p+q+1)+1,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, n_, p_, q_, x_],
        optional: [b__, d__],
        when: {
            freeq!([a__, b__, c__, d__, n_, p_, q_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(&n_ * (&p_ + &q_ + Atom::num(1)) + Atom::num(1), 0)
        },
        rhs: {
            let first_base = &a__ + &b__ * x_.pow(&n_);
            let second_base = &c__ + &d__ * x_.pow(&n_);
            rubi_simp(
                &(x_ * first_base.pow(&p_)
                    * rubi_hypergeometric2f1(
                        Atom::num(1) / &n_,
                        -&p_,
                        Atom::num(1) + Atom::num(1) / &n_,
                        -(&b__ * &c__ - &a__ * &d__) * x_.pow(&n_) / (&a__ * &second_base),
                    )
                    / (&c__
                        * (&c__ * &first_base / (&a__ * &second_base)).pow(&p_)
                        * second_base.pow(Atom::num(1) / &n_ + &p_))),
                x_,
            )
        },
    ));
}

fn push_rules_rule_906(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 906,
        source: "Int[(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
          x*(a+b*x^n)^(p+1)*(c+d*x^n)^(q+1)/(a*c) /;
        FreeQ[{a,b,c,d,n,p,q},x] && NeQ[b*c-a*d,0] && EqQ[n*(p+q+2)+1,0] && EqQ[a*d*(p+1)+b*c*(q+1),0]",
        desc: "Binomial product recurrence 2a with A=1, B=0 and n (p+q+2)+1\\[Equal]0Bold",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, n_, p_, q_, x_],
        optional: [b__, d__],
        when: {
            freeq!([a__, b__, c__, d__, n_, p_, q_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(&n_ * (&p_ + &q_ + Atom::num(2)) + Atom::num(1), 0)
                && eqq!(&a__ * &d__ * (&p_ + Atom::num(1)) + &b__ * &c__ * (&q_ + Atom::num(1)), 0)
        },
        rhs: {
            rubi_simp(
                &(x_
                    * (&a__ + &b__ * x_.pow(&n_)).pow(&p_ + Atom::num(1))
                    * (&c__ + &d__ * x_.pow(&n_)).pow(&q_ + Atom::num(1))
                    / (&a__ * &c__)),
                x_,
            )
        },
    ));
}

fn push_rules_rule_907(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 907,
        source: "Int[(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
          -b*x*(a+b*x^n)^(p+1)*(c+d*x^n)^(q+1)/(a*n*(p+1)*(b*c-a*d)) +
          (b*c+n*(p+1)*(b*c-a*d))/(a*n*(p+1)*(b*c-a*d)) \\[Star] Int[(a+b*x^n)^(p+1)*(c+d*x^n)^q,x] /;
        FreeQ[{a,b,c,d,n,q},x] && NeQ[b*c-a*d,0] && EqQ[n*(p+q+2)+1,0] && (LtQ[p,-1] || Not[LtQ[q,-1]]) && NeQ[p,-1]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, n_, p_, q_, x_],
        optional: [b__, d__],
        when: {
            freeq!([a__, b__, c__, d__, n_, q_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(&n_ * (&p_ + &q_ + Atom::num(2)) + Atom::num(1), 0)
                && (ltq!(p_, -1) || !ltq!(q_, -1))
                && neq!(p_, -Atom::num(1))
        },
        rhs: {
            let bc_ad = &b__ * &c__ - &a__ * &d__;
            let first_base = &a__ + &b__ * x_.pow(&n_);
            let second_base = &c__ + &d__ * x_.pow(&n_);
            let recursive_integrand = first_base.pow(&p_ + Atom::num(1)) * second_base.pow(&q_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let denominator = &a__ * &n_ * (&p_ + Atom::num(1)) * &bc_ad;
            let direct = -&b__ * x_ * first_base.pow(&p_ + Atom::num(1))
                * second_base.pow(&q_ + Atom::num(1))
                / &denominator;
            let recurrence_factor = (&b__ * &c__
                + &n_ * (&p_ + Atom::num(1)) * &bc_ad)
                / denominator;
            let recurrence = rubi_simp(&(&recurrence_factor * &recursive), x_);

            rubi_simp(&direct, x_) + rubi_star(Atom::num(1), recurrence)
        },
    ));
}

fn push_rules_rule_908(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 908,
        source: "Int[(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_),x_Symbol] :=
          c*x*(a+b*x^n)^(p+1)/a /;
        FreeQ[{a,b,c,d,n,p},x] && NeQ[b*c-a*d,0] && EqQ[a*d-b*c*(n*(p+1)+1),0]",
        desc: "Trinomial recurrence 2b with c=0, p=0 and a d-b c (n (p+1)+1)\\[Equal]0",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, n_, p_, x_],
        optional: [b__, d__, p_],
        x_free: [a__, b__, c__, d__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, n_, p_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(&a__ * &d__ - &b__ * &c__ * (&n_ * (&p_ + Atom::num(1)) + Atom::num(1)), 0)
        },
        rhs: {
            rubi_simp(
                &(&c__ * x_
                    * (&a__ + &b__ * x_.pow(&n_)).pow(&p_ + Atom::num(1))
                    / &a__),
                x_,
            )
        },
    ));
}

fn push_rules_rule_909(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a1__, a2__, b1__, b2__, c__, d__, n_, non2_, p_, x_);
    let rule = rubi_rule!(
        order: 909,
        source: "Int[(a1_+b1_.*x_^non2_.)^p_.*(a2_+b2_.*x_^non2_.)^p_.*(c_+d_.*x_^n_),x_Symbol] :=
          c*x*(a1+b1*x^(n/2))^(p+1)*(a2+b2*x^(n/2))^(p+1)/(a1*a2) /;
        FreeQ[{a1,b1,a2,b2,c,d,n,p},x] && EqQ[non2,n/2] && EqQ[a2*b1+a1*b2,0] && EqQ[a1*a2*d-b1*b2*c*(n*(p+1)+1),0]",
        desc: "Trinomial recurrence 2b with c=0, p=0 and a d-b c (n (p+1)+1)\\[Equal]0",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a1__, b1__, a2__, b2__, c__, d__, non2_, n_, p_, x_],
        optional: [b1__, b2__, d__, non2_, p_],
        x_free: [a1__, b1__, a2__, b2__, c__, d__, n_, p_],
        when: {
            freeq!([a1__, b1__, a2__, b2__, c__, d__, n_, p_], x_)
                && eqq!(non2_, &n_ / Atom::num(2))
                && eqq!(&a2__ * &b1__ + &a1__ * &b2__, 0)
                && eqq!(
                    &a1__ * &a2__ * &d__ - &b1__ * &b2__ * &c__ * (&n_ * (&p_ + Atom::num(1)) + Atom::num(1)),
                    0
                )
        },
        rhs: {
            rubi_simp(
                &(&c__ * x_
                    * (&a1__ + &b1__ * x_.pow(&n_ / Atom::num(2))).pow(&p_ + Atom::num(1))
                    * (&a2__ + &b2__ * x_.pow(&n_ / Atom::num(2))).pow(&p_ + Atom::num(1))
                    / (&a1__ * &a2__)),
                x_,
            )
        },
    );
    rules.push(rule.with_opposite_binomial_base_pair());
}

fn push_rules_rule_910(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 910,
        source: "Int[(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_),x_Symbol] :=
          -(b*c-a*d)*x*(a+b*x^n)^(p+1)/(a*b*n*(p+1)) -
          (a*d-b*c*(n*(p+1)+1))/(a*b*n*(p+1)) \\[Star] Int[(a+b*x^n)^(p+1),x] /;
        FreeQ[{a,b,c,d,n,p},x] && NeQ[b*c-a*d,0] && (LtQ[p,-1] || ILtQ[1/n+p,0])",
        desc: "Trinomial recurrence 2b with c=0 and p=0",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, n_, p_, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, n_, p_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && (ltq!(p_, -1) || iltq!(Atom::num(1) / &n_ + &p_, 0))
        },
        rhs: {
            let base = &a__ + &b__ * x_.pow(&n_);
            let recursive_integrand = base.pow(&p_ + Atom::num(1));
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let denominator = &a__ * &b__ * &n_ * (&p_ + Atom::num(1));
            let direct = -(&b__ * &c__ - &a__ * &d__) * x_
                * base.pow(&p_ + Atom::num(1))
                / &denominator;
            let recurrence_factor = (&a__ * &d__
                - &b__ * &c__ * (&n_ * (&p_ + Atom::num(1)) + Atom::num(1)))
                / denominator;
            let recurrence = rubi_simp(&(&recurrence_factor * &recursive), x_);

            rubi_simp(&direct, x_) - rubi_star(Atom::num(1), recurrence)
        },
    ));
}

fn push_rules_rule_911(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a1__, a2__, b1__, b2__, c__, d__, n_, non2_, p_, x_);
    let rule = rubi_rule!(
        order: 911,
        source: "Int[(a1_+b1_.*x_^non2_.)^p_.*(a2_+b2_.*x_^non2_.)^p_.*(c_+d_.*x_^n_),x_Symbol] :=
          -(b1*b2*c-a1*a2*d)*x*(a1+b1*x^(n/2))^(p+1)*(a2+b2*x^(n/2))^(p+1)/(a1*a2*b1*b2*n*(p+1)) -
          (a1*a2*d-b1*b2*c*(n*(p+1)+1))/(a1*a2*b1*b2*n*(p+1)) \\[Star] Int[(a1+b1*x^(n/2))^(p+1)*(a2+b2*x^(n/2))^(p+1),x] /;
        FreeQ[{a1,b1,a2,b2,c,d,n},x] && EqQ[non2,n/2] && EqQ[a2*b1+a1*b2,0] && (LtQ[p,-1] || ILtQ[1/n+p,0])",
        desc: "Trinomial recurrence 2b with c=0 and p=0",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a1__, b1__, a2__, b2__, c__, d__, non2_, n_, p_, x_],
        optional: [b1__, b2__, d__, non2_, p_],
        x_free: [a1__, b1__, a2__, b2__, c__, d__, n_],
        when: {
            freeq!([a1__, b1__, a2__, b2__, c__, d__, n_], x_)
                && eqq!(non2_, &n_ / Atom::num(2))
                && eqq!(&a2__ * &b1__ + &a1__ * &b2__, 0)
                && (ltq!(p_, -1) || iltq!(Atom::num(1) / &n_ + &p_, 0))
        },
        rhs: {
            let first_base = &a1__ + &b1__ * x_.pow(&n_ / Atom::num(2));
            let second_base = &a2__ + &b2__ * x_.pow(&n_ / Atom::num(2));
            let recursive_integrand =
                first_base.pow(&p_ + Atom::num(1)) * second_base.pow(&p_ + Atom::num(1));
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let denominator = &a1__ * &a2__ * &b1__ * &b2__ * &n_
                * (&p_ + Atom::num(1));
            let direct = -(&b1__ * &b2__ * &c__ - &a1__ * &a2__ * &d__)
                * x_
                * first_base.pow(&p_ + Atom::num(1))
                * second_base.pow(&p_ + Atom::num(1))
                / &denominator;
            let recurrence_factor = (&a1__ * &a2__ * &d__
                - &b1__ * &b2__ * &c__
                    * (&n_ * (&p_ + Atom::num(1)) + Atom::num(1)))
                / denominator;
            let recurrence = rubi_simp(&(&recurrence_factor * &recursive), x_);

            rubi_simp(&direct, x_) - rubi_star(Atom::num(1), recurrence)
        },
    );
    rules.push(rule.with_opposite_binomial_base_pair());
}

fn push_rules_rule_912(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 912,
        source: "Int[(c_+d_.*x_^n_)/(a_+b_.*x_^n_),x_Symbol] :=
          c*x/a - (b*c-a*d)/a \\[Star] Int[1/(b+a*x^(-n)),x] /;
        FreeQ[{a,b,c,d,n},x] && NeQ[b*c-a*d,0] && LtQ[n,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (c__ + d__ * x_.pow(n_)) / (a__ + b__ * x_.pow(n_)),
        with: [a__, b__, c__, d__, n_, x_],
        optional: [b__, d__],
        when: {
            freeq!([a__, b__, c__, d__, n_], x_) && neq!(&b__ * &c__ - &a__ * &d__, 0) && ltq!(n_, 0)
        },
        rhs: {
            let recursive_integrand = Atom::num(1) / (&b__ + &a__ * x_.pow(-&n_));
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let direct = &c__ * x_ / &a__;
            let recurrence = rubi_simp(&(&((&b__ * &c__ - &a__ * &d__) / &a__) * &recursive), x_);

            rubi_simp(&direct, x_) - rubi_star(Atom::num(1), recurrence)
        },
    ));
}

fn push_rules_rule_913(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 913,
        source: "Int[(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_),x_Symbol] :=
          d*x*(a+b*x^n)^(p+1)/(b*(n*(p+1)+1)) -
          (a*d-b*c*(n*(p+1)+1))/(b*(n*(p+1)+1)) \\[Star] Int[(a+b*x^n)^p,x] /;
        FreeQ[{a,b,c,d,n,p},x] && NeQ[b*c-a*d,0] && NeQ[n*(p+1)+1,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, n_, p_, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__, n_, p_],
        when: {
            freeq!([a__, b__, c__, d__, n_, p_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && neq!(&n_ * (&p_ + Atom::num(1)) + Atom::num(1), 0)
        },
        rhs: {
            let base = &a__ + &b__ * x_.pow(&n_);
            let recursive_integrand = base.pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let denominator = &b__ * (&n_ * (&p_ + Atom::num(1)) + Atom::num(1));
            let direct = &d__ * x_ * base.pow(&p_ + Atom::num(1))
                / &denominator;
            let recurrence_factor = (&a__ * &d__
                - &b__ * &c__ * (&n_ * (&p_ + Atom::num(1)) + Atom::num(1)))
                / denominator;
            let recurrence = rubi_simp(&(&recurrence_factor * &recursive), x_);

            rubi_simp(&direct, x_) - rubi_star(Atom::num(1), recurrence)
        },
    ));
}

fn push_rules_rule_914(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a1__, a2__, b1__, b2__, c__, d__, n_, non2_, p_, x_);
    let rule = rubi_rule!(
        order: 914,
        source: "Int[(a1_+b1_.*x_^non2_.)^p_.*(a2_+b2_.*x_^non2_.)^p_.*(c_+d_.*x_^n_),x_Symbol] :=
          d*x*(a1+b1*x^(n/2))^(p+1)*(a2+b2*x^(n/2))^(p+1)/(b1*b2*(n*(p+1)+1)) -
          (a1*a2*d-b1*b2*c*(n*(p+1)+1))/(b1*b2*(n*(p+1)+1)) \\[Star] Int[(a1+b1*x^(n/2))^p*(a2+b2*x^(n/2))^p,x] /;
        FreeQ[{a1,b1,a2,b2,c,d,n,p},x] && EqQ[non2,n/2] && EqQ[a2*b1+a1*b2,0] && NeQ[n*(p+1)+1,0]",
        desc: "Trinomial recurrence 2b with c=0 and p=0 composed with binomial recurrence 1b with p=0",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a1__, b1__, a2__, b2__, c__, d__, non2_, n_, p_, x_],
        optional: [b1__, b2__, d__, non2_, p_],
        x_free: [a1__, b1__, a2__, b2__, c__, d__, n_, p_],
        when: {
            freeq!([a1__, b1__, a2__, b2__, c__, d__, n_, p_], x_)
                && eqq!(non2_, &n_ / Atom::num(2))
                && eqq!(&a2__ * &b1__ + &a1__ * &b2__, 0)
                && neq!(&n_ * (&p_ + Atom::num(1)) + Atom::num(1), 0)
        },
        rhs: {
            let first_base = &a1__ + &b1__ * x_.pow(&n_ / Atom::num(2));
            let second_base = &a2__ + &b2__ * x_.pow(&n_ / Atom::num(2));
            let recursive_integrand = first_base.pow(&p_) * second_base.pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let denominator = &b1__ * &b2__
                * (&n_ * (&p_ + Atom::num(1)) + Atom::num(1));
            let direct = &d__ * x_
                * first_base.pow(&p_ + Atom::num(1))
                * second_base.pow(&p_ + Atom::num(1))
                / &denominator;
            let recurrence_factor = (&a1__ * &a2__ * &d__
                - &b1__ * &b2__ * &c__
                    * (&n_ * (&p_ + Atom::num(1)) + Atom::num(1)))
                / denominator;
            let recurrence = rubi_simp(&(&recurrence_factor * &recursive), x_);

            rubi_simp(&direct, x_) - rubi_star(Atom::num(1), recurrence)
        },
    );
    rules.push(rule.with_opposite_binomial_base_pair());
}

fn push_rules_rule_915(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 915,
        source: "Int[(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
          Int[PolynomialDivide[(a+b*x^n)^p,(c+d*x^n)^(-q),x],x] /;
        FreeQ[{a,b,c,d},x] && NeQ[b*c-a*d,0] && IGtQ[n,0] && IGtQ[p,0] && ILtQ[q,0] && GeQ[p,-q]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, n_, p_, q_, x_],
        optional: [b__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && igtq!(n_, 0)
                && igtq!(p_, 0)
                && iltq!(q_, 0)
                && geq!(p_, (-&q_))
        },
        rhs: {
            let numerator = (&a__ + &b__ * x_.pow(&n_)).pow(&p_);
            let denominator = (&c__ + &d__ * x_.pow(&n_)).pow(-&q_);
            let divided = rubi_polynomial_divide(&numerator, &denominator, x_).rubi_rhs();
            rubi_rhs_int(&divided, x_)
        },
    ));
}

fn push_rules_rule_916(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, x_);
    rules.push(rubi_rule!(
        order: 916,
        source: "Int[(a_+b_.*x_^n_)^p_/(c_+d_.*x_^n_),x_Symbol] :=
          b/d \\[Star] Int[(a+b*x^n)^(p-1),x] - (b*c-a*d)/d \\[Star] Int[(a+b*x^n)^(p-1)/(c+d*x^n),x] /;
        FreeQ[{a,b,c,d,p},x] && NeQ[b*c-a*d,0] && EqQ[n*(p-1)+1,0] && IntegerQ[n]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, b__, c__, d__, n_, p_, x_],
        optional: [b__, d__],
        when: {
            freeq!([a__, b__, c__, d__, p_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(&n_ * (&p_ - Atom::num(1)) + Atom::num(1), 0)
                && integerq!(n_)
        },
        rhs: {
            let first_integrand = (&a__ + &b__ * x_.pow(&n_)).pow(&p_ - Atom::num(1));
            let second_integrand =
                &first_integrand / (&c__ + &d__ * x_.pow(&n_));
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);
            let first_term = rubi_simp(&(&(&b__ / &d__) * &first), x_);
            let second_term = rubi_simp(&(&((&b__ * &c__ - &a__ * &d__) / &d__) * &second), x_);

            rubi_star(Atom::num(1), first_term) - rubi_star(Atom::num(1), second_term)
        },
    ));
}

fn push_rules_rule_917(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, n_, x_);
    rules.push(rubi_rule!(
        order: 917,
        source: "Int[1/((a_+b_.*x_^n_)*(c_+d_.*x_^n_)),x_Symbol] :=
          b/(b*c-a*d) \\[Star] Int[1/(a+b*x^n),x] - d/(b*c-a*d) \\[Star] Int[1/(c+d*x^n),x] /;
        FreeQ[{a,b,c,d,n},x] && NeQ[b*c-a*d,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: Atom::num(1) / ((a__ + b__ * x_.pow(n_)) * (c__ + d__ * x_.pow(n_))),
        with: [a__, b__, c__, d__, n_, x_],
        optional: [b__, d__],
        when: { freeq!([a__, b__, c__, d__, n_], x_) && neq!(&b__ * &c__ - &a__ * &d__, 0) },
        rhs: {
            let denominator = &b__ * &c__ - &a__ * &d__;
            let first = rubi_rhs_int(
                &(Atom::num(1) / (&a__ + &b__ * x_.pow(&n_))),
                x_,
            );
            let second = rubi_rhs_int(
                &(Atom::num(1) / (&c__ + &d__ * x_.pow(&n_))),
                x_,
            );
            let first_term = rubi_simp(&(&(&b__ / &denominator) * &first), x_);
            let second_term = rubi_simp(&(&(&d__ / denominator) * &second), x_);

            rubi_star(Atom::num(1), first_term) - rubi_star(Atom::num(1), second_term)
        },
    ));
}

fn push_rules_rule_918(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 918,
        source: "Int[(a_+b_.*x_^2)^(2/3)/(c_+d_.*x_^2),x_Symbol] :=
          b/d \\[Star] Int[1/(a+b*x^2)^(1/3),x] - (b*c-a*d)/d \\[Star] Int[1/((a+b*x^2)^(1/3)*(c+d*x^2)),x] /;
        FreeQ[{a,b,c,d},x] && NeQ[b*c-a*d,0] && EqQ[b*c+3*a*d,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (a__ + b__ * x_.pow(2)).pow((2, 3)) / (c__ + d__ * x_.pow(2)),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(&b__ * &c__ + Atom::num(3) * &a__ * &d__, 0)
        },
        rhs: {
            let base = &a__ + &b__ * x_.pow(2);
            let first_integrand = Atom::num(1) / base.pow(Atom::num(1) / Atom::num(3));
            let second_integrand =
                Atom::num(1) / (base.pow(Atom::num(1) / Atom::num(3)) * (&c__ + &d__ * x_.pow(2)));
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);
            let first_term = rubi_simp(&(&(&b__ / &d__) * &first), x_);
            let second_term = rubi_simp(&(&((&b__ * &c__ - &a__ * &d__) / &d__) * &second), x_);

            rubi_star(Atom::num(1), first_term) - rubi_star(Atom::num(1), second_term)
        },
    ));
}

fn push_rules_rule_919(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, p_, x_);
    rules.push(rubi_rule!(
        order: 919,
        source: "Int[(a_+b_.*x_^2)^p_./(c_+d_.*x_^2),x_Symbol] :=
          b/d \\[Star] Int[(a+b*x^2)^(p-1),x] - (b*c-a*d)/d \\[Star] Int[(a+b*x^2)^(p-1)/(c+d*x^2),x] /;
        FreeQ[{a,b,c,d},x] && NeQ[b*c-a*d,0] && GtQ[p,0] && (EqQ[p,1/2] || EqQ[Denominator[p],4])",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (a__ + b__ * x_.pow(2)).pow(p_) / (c__ + d__ * x_.pow(2)),
        with: [a__, b__, c__, d__, p_, x_],
        optional: [b__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && gtq!(p_, 0)
                && (eqq!(p_, Atom::num(1) / Atom::num(2))
                    || eqq!(rubi_denominator_atom(&p_), 4))
        },
        rhs: {
            let base = &a__ + &b__ * x_.pow(2);
            let first_integrand = base.pow(&p_ - Atom::num(1));
            let second_integrand = &first_integrand / (&c__ + &d__ * x_.pow(2));
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);
            let first_term = rubi_simp(&(&(&b__ / &d__) * &first), x_);
            let second_term = rubi_simp(&(&((&b__ * &c__ - &a__ * &d__) / &d__) * &second), x_);

            rubi_star(Atom::num(1), first_term) - rubi_star(Atom::num(1), second_term)
        },
    ));
}

fn push_rules_rule_920(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 920,
        source: "Int[Sqrt[a_+b_.*x_^4]/(c_+d_.*x_^4),x_Symbol] :=
          a/c \\[Star] Subst[Int[1/(1-4*a*b*x^4),x],x,x/Sqrt[a+b*x^4]] /;
        FreeQ[{a,b,c,d},x] && EqQ[b*c+a*d,0] && PosQ[a*b]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && eqq!(&b__ * &c__ + &a__ * &d__, 0)
                && posq!(&a__ * &b__)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = Atom::num(1) / (Atom::num(1) - Atom::num(4) * &a__ * &b__ * sub_atom.pow(4));
            let transformed = rubi_rhs_int(&transformed_integrand, sub);

            let replacement = x_ / (&a__ + &b__ * x_.pow(4)).sqrt();
            let substituted = rubi_subst(&transformed, sub, replacement);
            rubi_star(&a__ / &c__, substituted)
        },
    ));
}

fn push_rules_rule_921(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 921,
        source: "Int[Sqrt[a_+b_.*x_^4]/(c_+d_.*x_^4),x_Symbol] :=
          With[{q=Rt[-a*b,4]},
          a/(2*c*q)*ArcTan[q*x*(a+q^2*x^2)/(a*Sqrt[a+b*x^4])] + a/(2*c*q)*ArcTanh[q*x*(a-q^2*x^2)/(a*Sqrt[a+b*x^4])]] /;
        FreeQ[{a,b,c,d},x] && EqQ[b*c+a*d,0] && NegQ[a*b]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && eqq!(&b__ * &c__ + &a__ * &d__, 0)
                && negq!(&a__ * &b__)
        },
        rhs: {
            let q = rubi_rt(&(-&a__ * &b__), 4);
            let base = &a__ + &b__ * x_.pow(4);
            let coefficient = &a__ / (Atom::num(2) * &c__ * &q);
            let first = &coefficient
                * (&q * x_ * (&a__ + q.pow(2) * x_.pow(2))
                    / (&a__ * base.sqrt()))
                    .atan();
            let second = coefficient
                * (&q * x_ * (&a__ - q.pow(2) * x_.pow(2))
                    / (&a__ * base.sqrt()))
                    .atanh();

            rubi_simp(&first, x_) + rubi_simp(&second, x_)
        },
    ));
}

fn push_rules_rule_922(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 922,
        source: "Int[Sqrt[a_+b_.*x_^4]/(c_+d_.*x_^4),x_Symbol] :=
          b/d \\[Star] Int[1/Sqrt[a+b*x^4],x] - (b*c-a*d)/d \\[Star] Int[1/(Sqrt[a+b*x^4]*(c+d*x^4)),x] /;
        FreeQ[{a,b,c,d},x] && NeQ[b*c-a*d,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, d__],
        when: { freeq!([a__, b__, c__, d__], x_) && neq!(&b__ * &c__ - &a__ * &d__, 0) },
        rhs: {
            let base = &a__ + &b__ * x_.pow(4);
            let first_integrand = Atom::num(1) / base.sqrt();
            let second_integrand = Atom::num(1) / (base.sqrt() * (&c__ + &d__ * x_.pow(4)));
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);
            let first_term = rubi_simp(&(&(&b__ / &d__) * &first), x_);
            let second_term = rubi_simp(&(&((&b__ * &c__ - &a__ * &d__) / &d__) * &second), x_);

            rubi_star(Atom::num(1), first_term) - rubi_star(Atom::num(1), second_term)
        },
    ));
}

fn push_rules_rule_923(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 923,
        source: "Int[(a_+b_.*x_^4)^(1/4)/(c_+d_.*x_^4),x_Symbol] :=
          Sqrt[a+b*x^4]*Sqrt[a/(a+b*x^4)] \\[Star] Subst[Int[1/(Sqrt[1-b*x^4]*(c-(b*c-a*d)*x^4)),x],x,x/(a+b*x^4)^(1/4)] /;
        FreeQ[{a,b,c,d},x] && NeQ[b*c-a*d,0]",
        desc: "Piecewise constant extraction and integration by substitution",
        refs: [],
        pattern: (a__ + b__ * x_.pow(4)).pow((1, 4)) / (c__ + d__ * x_.pow(4)),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, d__],
        when: { freeq!([a__, b__, c__, d__], x_) && neq!(&b__ * &c__ - &a__ * &d__, 0) },
        rhs: {
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = Atom::num(1)
                / ((Atom::num(1) - &b__ * sub_atom.pow(4)).sqrt()
                    * (&c__ - (&b__ * &c__ - &a__ * &d__) * sub_atom.pow(4)));
            let transformed = rubi_rhs_int(&transformed_integrand, sub);

            let base = &a__ + &b__ * x_.pow(4);
            let replacement = x_ / base.pow(Atom::num(1) / Atom::num(4));
            let substituted = rubi_subst(&transformed, sub, replacement);
            let coefficient = base.sqrt() * (&a__ / &base).sqrt();

            rubi_star(coefficient, substituted)
        },
    ));
}

fn push_rules_rule_924(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 924,
        source: "Int[(a_+b_.*x_^4)^(5/4)/(c_+d_.*x_^4),x_Symbol] :=
          b/d \\[Star] Int[(a+b*x^4)^(1/4),x] - (b*c-a*d)/d \\[Star] Int[(a+b*x^4)^(1/4)/(c+d*x^4),x] /;
        FreeQ[{a,b,c,d},x] && NeQ[b*c-a*d,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (a__ + b__ * x_.pow(4)).pow((5, 4)) / (c__ + d__ * x_.pow(4)),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, d__],
        when: { freeq!([a__, b__, c__, d__], x_) && neq!(&b__ * &c__ - &a__ * &d__, 0) },
        rhs: {
            let base = &a__ + &b__ * x_.pow(4);
            let first_integrand = base.pow(Atom::num(1) / Atom::num(4));
            let second_integrand = &first_integrand / (&c__ + &d__ * x_.pow(4));
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);
            let first_term = rubi_simp(&(&(&b__ / &d__) * &first), x_);
            let second_term = rubi_simp(&(&((&b__ * &c__ - &a__ * &d__) / &d__) * &second), x_);

            rubi_star(Atom::num(1), first_term) - rubi_star(Atom::num(1), second_term)
        },
    ));
}

fn push_rules_rule_925(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 925,
        source: "Int[1/(Sqrt[a_+b_.*x_^4]*(c_+d_.*x_^4)),x_Symbol] :=
          1/(2*c) \\[Star] Int[1/(Sqrt[a+b*x^4]*(1-Rt[-d/c,2]*x^2)),x] + 1/(2*c) \\[Star] Int[1/(Sqrt[a+b*x^4]*(1+Rt[-d/c,2]*x^2)),x] /;
        FreeQ[{a,b,c,d},x] && NeQ[b*c-a*d,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: Atom::num(1) / ((a__ + b__ * x_.pow(4)).sqrt() * (c__ + d__ * x_.pow(4))),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, d__],
        when: { freeq!([a__, b__, c__, d__], x_) && neq!(&b__ * &c__ - &a__ * &d__, 0) },
        rhs: {
            let rt = rubi_rt(&(-&d__ / &c__), 2);
            let base = &a__ + &b__ * x_.pow(4);
            let first_integrand = Atom::num(1) / (base.sqrt() * (Atom::num(1) - &rt * x_.pow(2)));
            let second_integrand = Atom::num(1) / (base.sqrt() * (Atom::num(1) + &rt * x_.pow(2)));
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);
            let coefficient = Atom::num(1) / (Atom::num(2) * &c__);
            let first_term = rubi_simp(&(&coefficient * &first), x_);
            let second_term = rubi_simp(&(&coefficient * &second), x_);

            rubi_star(Atom::num(1), first_term) + rubi_star(Atom::num(1), second_term)
        },
    ));
}

fn push_rules_rule_926(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 926,
        source: "Int[1/((a_+b_.*x_^4)^(3/4)*(c_+d_.*x_^4)),x_Symbol] :=
          b/(b*c-a*d) \\[Star] Int[1/(a+b*x^4)^(3/4),x] - d/(b*c-a*d) \\[Star] Int[(a+b*x^4)^(1/4)/(c+d*x^4),x] /;
        FreeQ[{a,b,c,d},x] && NeQ[b*c-a*d,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: Atom::num(1) / ((a__ + b__ * x_.pow(4)).pow((3, 4)) * (c__ + d__ * x_.pow(4))),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, d__],
        when: { freeq!([a__, b__, c__, d__], x_) && neq!(&b__ * &c__ - &a__ * &d__, 0) },
        rhs: {
            let base = &a__ + &b__ * x_.pow(4);
            let first_integrand = Atom::num(1) / base.pow(Atom::num(3) / Atom::num(4));
            let second_integrand = base.pow(Atom::num(1) / Atom::num(4)) / (&c__ + &d__ * x_.pow(4));
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);
            let denominator = &b__ * &c__ - &a__ * &d__;
            let first_term = rubi_simp(&(&(&b__ / &denominator) * &first), x_);
            let second_term = rubi_simp(&(&(&d__ / denominator) * &second), x_);

            rubi_star(Atom::num(1), first_term) - rubi_star(Atom::num(1), second_term)
        },
    ));
}

fn push_rules_rule_927(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, x_);
    let rule = rubi_rule!(
        order: 927,
        source: "Int[(a_+b_.*x_^3)^(1/3)/(c_+d_.*x_^3),x_Symbol] :=
          With[{q=Rt[b/a,3]},
          9*a/(c*q) \\[Star] Subst[Int[x/((4-a*x^3)*(1+2*a*x^3)),x],x,(1+q*x)/(a+b*x^3)^(1/3)]] /;
        FreeQ[{a,b,c,d},x] && NeQ[b*c-a*d,0] && EqQ[b*c+a*d,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (a__ + b__ * x_.pow(3)).pow((1, 3)) / (c__ + d__ * x_.pow(3)),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(&b__ * &c__ + &a__ * &d__, 0)
        },
        rhs: {
            let q = rubi_rt(&(&b__ / &a__), 3);
            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand =
                &sub_atom / ((Atom::num(4) - &a__ * sub_atom.pow(3)) * (Atom::num(1) + Atom::num(2) * &a__ * sub_atom.pow(3)));
            let transformed = rubi_rhs_int(&transformed_integrand, sub);

            let replacement = (Atom::num(1) + &q * x_) / (&a__ + &b__ * x_.pow(3)).pow(Atom::num(1) / Atom::num(3));
            let substituted = rubi_subst(&transformed, sub, replacement);
            let coefficient = Atom::num(9) * &a__ / (&c__ * q);

            rubi_star(coefficient, substituted)
        },
    );
    rules.push(rule.with_repeated_proper_x_dependent_subexpression());
}

fn push_rules_rule_928(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 928,
        source: "Int[1/((a_+b_.*x_^3)^(2/3)*(c_+d_.*x_^3)),x_Symbol] :=
          b/(b*c-a*d) \\[Star] Int[1/(a+b*x^3)^(2/3),x] - d/(b*c-a*d) \\[Star] Int[(a+b*x^3)^(1/3)/(c+d*x^3),x] /;
        FreeQ[{a,b,c,d},x] && NeQ[b*c-a*d,0] && EqQ[b*c+a*d,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: Atom::num(1) / ((a__ + b__ * x_.pow(3)).pow((2, 3)) * (c__ + d__ * x_.pow(3))),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(&b__ * &c__ + &a__ * &d__, 0)
        },
        rhs: {
            let base = &a__ + &b__ * x_.pow(3);
            let denominator = &b__ * &c__ - &a__ * &d__;
            let first_integrand = Atom::num(1) / base.pow(Atom::num(2) / Atom::num(3));
            let second_integrand = base.pow(Atom::num(1) / Atom::num(3)) / (&c__ + &d__ * x_.pow(3));
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);
            let first_term = rubi_simp(&(&(&b__ / &denominator) * &first), x_);
            let second_term = rubi_simp(&(&(&d__ / denominator) * &second), x_);

            rubi_star(Atom::num(1), first_term) - rubi_star(Atom::num(1), second_term)
        },
    ));
}

fn push_rules_rule_929(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 929,
        source: "Int[(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
          -x*(a+b*x^n)^(p+1)*(c+d*x^n)^q/(a*n*(p+1)) +
          1/(a*n*(p+1)) \\[Star] Int[(a+b*x^n)^(p+1)*(c+d*x^n)^(q-1)*Simp[c*(n*(p+1)+1)+d*(n*(p+q+1)+1)*x^n,x],x] /;
        FreeQ[{a,b,c,d,n},x] && NeQ[b*c-a*d,0] && LtQ[p,-1] && LtQ[0,q,1] && IntBinomialQ[a,b,c,d,n,p,q,x]",
        desc: "Binomial product recurrence 1 with A=1 and B=0",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, n_, p_, q_, x_],
        optional: [b__, d__],
        when: {
            freeq!([a__, b__, c__, d__, n_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && ltq!(p_, -1)
                && ltq!(0, q_, 1)
                && rubi_int_binomial_pair_q(&a__, &b__, &c__, &d__, &n_, &p_, &q_, x_)
        },
        rhs: {
            let first_base = &a__ + &b__ * x_.pow(&n_);
            let second_base = &c__ + &d__ * x_.pow(&n_);
            let denominator = &a__ * &n_ * (&p_ + Atom::num(1));
            let payload = simp!(
                &c__ * (&n_ * (&p_ + Atom::num(1)) + Atom::num(1))
                    + &d__ * (&n_ * (&p_ + &q_ + Atom::num(1)) + Atom::num(1)) * x_.pow(&n_),
                x_
            );
            let recursive_integrand = first_base.pow(&p_ + Atom::num(1))
                * second_base.pow(&q_ - Atom::num(1))
                * payload;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let direct = Atom::num(-1) * x_ * first_base.pow(&p_ + Atom::num(1))
                * second_base.pow(&q_)
                / &denominator;
            let recurrence = rubi_simp(&(&(Atom::num(1) / denominator) * &recursive), x_);

            rubi_simp(&direct, x_) + rubi_star(Atom::num(1), recurrence)
        },
    ));
}

fn push_rules_rule_930(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 930,
        source: "Int[(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
          (a*d-c*b)*x*(a+b*x^n)^(p+1)*(c+d*x^n)^(q-1)/(a*b*n*(p+1)) -
          1/(a*b*n*(p+1)) \\[Star]
            Int[(a+b*x^n)^(p+1)*(c+d*x^n)^(q-2)*Simp[c*(a*d-c*b*(n*(p+1)+1))+d*(a*d*(n*(q-1)+1)-b*c*(n*(p+q)+1))*x^n,x],x] /;
        FreeQ[{a,b,c,d,n},x] && NeQ[b*c-a*d,0] && LtQ[p,-1] && GtQ[q,1] && IntBinomialQ[a,b,c,d,n,p,q,x]",
        desc: "Binomial product recurrence 1 with A=c, B=d and q=q-1",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, n_, p_, q_, x_],
        optional: [b__, d__],
        when: {
            freeq!([a__, b__, c__, d__, n_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && ltq!(p_, -1)
                && gtq!(q_, 1)
                && rubi_int_binomial_pair_q(&a__, &b__, &c__, &d__, &n_, &p_, &q_, x_)
        },
        rhs: {
            let first_base = &a__ + &b__ * x_.pow(&n_);
            let second_base = &c__ + &d__ * x_.pow(&n_);
            let denominator = &a__ * &b__ * &n_ * (&p_ + Atom::num(1));
            let payload = simp!(
                &c__ * (&a__ * &d__ - &c__ * &b__ * (&n_ * (&p_ + Atom::num(1)) + Atom::num(1)))
                    + &d__
                        * (&a__ * &d__ * (&n_ * (&q_ - Atom::num(1)) + Atom::num(1))
                            - &b__ * &c__ * (&n_ * (&p_ + &q_) + Atom::num(1)))
                        * x_.pow(&n_),
                x_
            );
            let recursive_integrand = first_base.pow(&p_ + Atom::num(1))
                * second_base.pow(&q_ - Atom::num(2))
                * payload;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let direct = (&a__ * &d__ - &c__ * &b__)
                * x_
                * first_base.pow(&p_ + Atom::num(1))
                * second_base.pow(&q_ - Atom::num(1))
                / &denominator;
            let recurrence = rubi_simp(&(&(Atom::num(1) / denominator) * &recursive), x_);

            rubi_simp(&direct, x_) - rubi_star(Atom::num(1), recurrence)
        },
    ));
}

fn push_rules_rule_931(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 931,
        source: "Int[(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
          -b*x*(a+b*x^n)^(p+1)*(c+d*x^n)^(q+1)/(a*n*(p+1)*(b*c-a*d)) +
          1/(a*n*(p+1)*(b*c-a*d)) \\[Star]
            Int[(a+b*x^n)^(p+1)*(c+d*x^n)^q*Simp[b*c+n*(p+1)*(b*c-a*d)+d*b*(n*(p+q+2)+1)*x^n,x],x] /;
        FreeQ[{a,b,c,d,n,q},x] && NeQ[b*c-a*d,0] && LtQ[p,-1] && Not[Not[IntegerQ[p]] && IntegerQ[q] && LtQ[q,-1]] &&
          IntBinomialQ[a,b,c,d,n,p,q,x]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, n_, p_, q_, x_],
        optional: [b__, d__],
        when: {
            freeq!([a__, b__, c__, d__, n_, q_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && ltq!(p_, -1)
                && !(!integerq!(p_) && integerq!(q_) && ltq!(q_, -1))
                && rubi_int_binomial_pair_q(&a__, &b__, &c__, &d__, &n_, &p_, &q_, x_)
        },
        rhs: {
            let first_base = &a__ + &b__ * x_.pow(&n_);
            let second_base = &c__ + &d__ * x_.pow(&n_);
            let determinant = &b__ * &c__ - &a__ * &d__;
            let denominator = &a__ * &n_ * (&p_ + Atom::num(1)) * &determinant;
            let payload = simp!(
                &b__ * &c__
                    + &n_ * (&p_ + Atom::num(1)) * &determinant
                    + &d__ * &b__ * (&n_ * (&p_ + &q_ + Atom::num(2)) + Atom::num(1)) * x_.pow(&n_),
                x_
            );
            let recursive_integrand =
                first_base.pow(&p_ + Atom::num(1)) * second_base.pow(&q_) * payload;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let direct = -&b__ * x_ * first_base.pow(&p_ + Atom::num(1))
                * second_base.pow(&q_ + Atom::num(1))
                / &denominator;
            let recurrence = rubi_simp(&(&(Atom::num(1) / denominator) * &recursive), x_);

            rubi_simp(&direct, x_) + rubi_star(Atom::num(1), recurrence)
        },
    ));
}

fn push_rules_rule_932(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 932,
        source: "Int[(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
          Int[ExpandIntegrand[(a+b*x^n)^p*(c+d*x^n)^q,x],x] /;
        FreeQ[{a,b,c,d},x] && NeQ[b*c-a*d,0] && IGtQ[n,0] && IntegersQ[p,q] && GtQ[p+q,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, n_, p_, q_, x_],
        optional: [b__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && igtq!(n_, 0)
                && integersq!([p_, q_])
                && gtq!(&p_ + &q_, 0)
        },
        rhs: {
            let integrand =
                (&a__ + &b__ * x_.pow(&n_)).pow(&p_) * (&c__ + &d__ * x_.pow(&n_)).pow(&q_);
            let expanded = rubi_expand_integrand(&integrand, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_933(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 933,
        source: "Int[(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
          d*x*(a+b*x^n)^(p+1)*(c+d*x^n)^(q-1)/(b*(n*(p+q)+1)) +
          1/(b*(n*(p+q)+1)) \\[Star]
            Int[(a+b*x^n)^p*(c+d*x^n)^(q-2)*Simp[c*(b*c*(n*(p+q)+1)-a*d)+d*(b*c*(n*(p+2*q-1)+1)-a*d*(n*(q-1)+1))*x^n,x],x] /;
        FreeQ[{a,b,c,d,n,p},x] && NeQ[b*c-a*d,0] && GtQ[q,1] && NeQ[n*(p+q)+1,0] && Not[IGtQ[p,1]] && IntBinomialQ[a,b,c,d,n,p,q,x]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, n_, p_, q_, x_],
        optional: [b__, d__],
        when: {
            freeq!([a__, b__, c__, d__, n_, p_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && gtq!(q_, 1)
                && neq!(&n_ * (&p_ + &q_) + Atom::num(1), 0)
                && !igtq!(p_, 1)
                && rubi_int_binomial_pair_q(&a__, &b__, &c__, &d__, &n_, &p_, &q_, x_)
        },
        rhs: {
            let first_base = &a__ + &b__ * x_.pow(&n_);
            let second_base = &c__ + &d__ * x_.pow(&n_);
            let sum_denominator = &n_ * (&p_ + &q_) + Atom::num(1);
            let denominator = &b__ * &sum_denominator;
            let payload = simp!(
                &c__ * (&b__ * &c__ * &sum_denominator - &a__ * &d__)
                    + &d__
                        * (&b__ * &c__ * (&n_ * (&p_ + Atom::num(2) * &q_ - Atom::num(1)) + Atom::num(1))
                            - &a__ * &d__ * (&n_ * (&q_ - Atom::num(1)) + Atom::num(1)))
                        * x_.pow(&n_),
                x_
            );
            let recursive_integrand =
                first_base.pow(&p_) * second_base.pow(&q_ - Atom::num(2)) * payload;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let direct = &d__ * x_ * first_base.pow(&p_ + Atom::num(1))
                * second_base.pow(&q_ - Atom::num(1))
                / &denominator;
            let recurrence = rubi_simp(&(&(Atom::num(1) / denominator) * &recursive), x_);

            rubi_simp(&direct, x_) + rubi_star(Atom::num(1), recurrence)
        },
    ));
}

fn push_rules_rule_934(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 934,
        source: "Int[(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
          x*(a+b*x^n)^p*(c+d*x^n)^q/(n*(p+q)+1) +
          n/(n*(p+q)+1) \\[Star] Int[(a+b*x^n)^(p-1)*(c+d*x^n)^(q-1)*Simp[a*c*(p+q)+(q*(b*c-a*d)+a*d*(p+q))*x^n,x],x] /;
        FreeQ[{a,b,c,d,n},x] && NeQ[b*c-a*d,0] && GtQ[q,0] && GtQ[p,0] && IntBinomialQ[a,b,c,d,n,p,q,x]",
        desc: "Binomial product recurrence 2b with m=0, A=a, B=b and p=p-1",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, n_, p_, q_, x_],
        optional: [b__, d__],
        when: {
            freeq!([a__, b__, c__, d__, n_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && gtq!(q_, 0)
                && gtq!(p_, 0)
                && rubi_int_binomial_pair_q(&a__, &b__, &c__, &d__, &n_, &p_, &q_, x_)
        },
        rhs: {
            let first_base = &a__ + &b__ * x_.pow(&n_);
            let second_base = &c__ + &d__ * x_.pow(&n_);
            let denominator = &n_ * (&p_ + &q_) + Atom::num(1);
            let payload = simp!(
                &a__ * &c__ * (&p_ + &q_)
                    + (&q_ * (&b__ * &c__ - &a__ * &d__) + &a__ * &d__ * (&p_ + &q_)) * x_.pow(&n_),
                x_
            );
            let recursive_integrand = first_base.pow(&p_ - Atom::num(1))
                * second_base.pow(&q_ - Atom::num(1))
                * payload;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let direct = x_ * first_base.pow(&p_) * second_base.pow(&q_)
                / &denominator;
            let recurrence = rubi_simp(&(&(&n_ / denominator) * &recursive), x_);

            rubi_simp(&direct, x_) + rubi_star(Atom::num(1), recurrence)
        },
    ));
}

fn push_rules_rule_935(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 935,
        source: "Int[(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_)^q_,x_Symbol] :=
          Int[ExpandIntegrand[(a+b*x^n)^p*(c+d*x^n)^q,x],x] /;
        FreeQ[{a,b,c,d,n,q},x] && NeQ[b*c-a*d,0] && IGtQ[p,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, n_, p_, q_, x_],
        optional: [b__, d__, p_],
        x_free: [a__, b__, c__, d__, n_, p_, q_],
        when: {
            freeq!([a__, b__, c__, d__, n_, q_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && igtq!(p_, 0)
        },
        rhs: {
            let integrand = (&a__ + &b__ * x_.pow(&n_)).pow(&p_)
                * (&c__ + &d__ * x_.pow(&n_)).pow(&q_);
            let expanded = rubi_expand_integrand(&integrand, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_936(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 936,
        source: "Int[(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
          a^p*c^q*x*AppellF1[1/n,-p,-q,1+1/n,-b*x^n/a,-d*x^n/c] /;
        FreeQ[{a,b,c,d,n,p,q},x] && NeQ[b*c-a*d,0] && NeQ[n,-1] && (IntegerQ[p] || GtQ[a,0]) && (IntegerQ[q] || GtQ[c,0])",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, n_, p_, q_, x_],
        optional: [b__, d__],
        when: {
            freeq!([a__, b__, c__, d__, n_, p_, q_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && neq!(n_, -1)
                && (integerq!(p_) || gtq!(a__, 0))
                && (integerq!(q_) || gtq!(c__, 0))
        },
        rhs: {
            rubi_simp(
                &(a__.pow(&p_)
                    * c__.pow(&q_)
                    * x_
                    * rubi_appell_f1(
                        Atom::num(1) / &n_,
                        -&p_,
                        -&q_,
                        Atom::num(1) + Atom::num(1) / &n_,
                        -&b__ * x_.pow(&n_) / &a__,
                        -&d__ * x_.pow(&n_) / &c__,
                    )),
                x_,
            )
        },
    ));
}

fn push_rules_rule_937(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 937,
        source: "Int[(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
          a^IntPart[p]*(a+b*x^n)^FracPart[p]/(1+b*x^n/a)^FracPart[p] \\[Star] Int[(1+b*x^n/a)^p*(c+d*x^n)^q,x] /;
        FreeQ[{a,b,c,d,n,p,q},x] && NeQ[b*c-a*d,0] && NeQ[n,-1] && Not[IntegerQ[p] || GtQ[a,0]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, n_, p_, q_, x_],
        optional: [b__, d__],
        when: {
            freeq!([a__, b__, c__, d__, n_, p_, q_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && neq!(n_, -1)
                && !(integerq!(p_) || gtq!(a__, 0))
        },
        rhs: {
            let int_p = rubi_int_part(&p_);
            let frac_p = rubi_frac_part(&p_);
            let first_base = &a__ + &b__ * x_.pow(&n_);
            let normalized_first = Atom::num(1) + &b__ * x_.pow(&n_) / &a__;
            let recursive_integrand =
                normalized_first.pow(&p_) * (&c__ + &d__ * x_.pow(&n_)).pow(&q_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let coefficient = a__.pow(int_p) * first_base.pow(&frac_p)
                / normalized_first.pow(frac_p);

            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_938(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, n_, p_, q_, u__);
    let rule = rubi_rule!(
        order: 938,
        source: "Int[(a_.+b_.*u_^n_)^p_.*(c_.+d_.*u_^n_)^q_.,x_Symbol] :=
          1/Coefficient[u,x,1] \\[Star] Subst[Int[(a+b*x^n)^p*(c+d*x^n)^q,x],x,u] /;
        FreeQ[{a,b,c,d,n,p,q},x] && LinearQ[u,x] && NeQ[u,x]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (a__ + b__ * u__.pow(n_)).pow(p_) * (c__ + d__ * u__.pow(n_)).pow(q_),
        with: [a__, b__, c__, d__, u__, n_, p_, q_, x_],
        optional: [a__, b__, c__, d__, p_, q_],
        x_dep: [u__],
        x_free: [a__, b__, c__, d__, n_, p_, q_],
        x_linear: [u__],
        when: {
            freeq!([a__, b__, c__, d__, n_, p_, q_], x_)
                && rubi_linear_q(&u__, x_)
                && neq!(u__, x_)
        },
        rhs: {
            let slope = rubi_coefficient(&u__, x_, 1).rubi_rhs();

            let sub_guard = fresh_substitution_symbol().rubi_rhs();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = (&a__ + &b__ * sub_atom.pow(&n_)).pow(&p_)
                * (&c__ + &d__ * sub_atom.pow(&n_)).pow(&q_);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);
            let substituted = rubi_subst(&transformed, sub, &u__);

            rubi_star(Atom::num(1) / slope, substituted)
        },
    );
    rules.push(rule.with_repeated_proper_x_dependent_subexpression());
}

fn push_rules_rule_939(rules: &mut Vec<RubiRule>) {
    rubi_symb!(p_, q_, v__, u__);
    rules.push(rubi_rule!(
        order: 939,
        source: "Int[u_^p_.*v_^q_.,x_Symbol] :=
          Int[NormalizePseudoBinomial[u,x]^p*NormalizePseudoBinomial[v,x]^q,x] /;
        FreeQ[{p,q},x] && PseudoBinomialPairQ[u,v,x]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: u__.pow(p_) * v__.pow(q_),
        with: [u__, v__, p_, q_, x_],
        optional: [q_, p_],
        x_free: [p_, q_],
        when: { freeq!([p_, q_], x_) && pseudo_binomial_pair_q(&u__, &v__, x_) },
        rhs: {
            let normalized_u = normalize_pseudo_binomial(&u__, x_).rubi_rhs();
            let normalized_v = normalize_pseudo_binomial(&v__, x_).rubi_rhs();
            rubi_rhs_int(
                &(normalized_u.pow(&p_) * normalized_v.pow(&q_)),
                x_,
            )
        },
    ));
}

fn push_rules_rule_940(rules: &mut Vec<RubiRule>) {
    rubi_symb!(m_, p_, q_, v__, u__, x_);
    rules.push(rubi_rule!(
        order: 940,
        source: "Int[x_^m_.*u_^p_.*v_^q_.,x_Symbol] :=
          Int[NormalizePseudoBinomial[x^(m/p)*u,x]^p*NormalizePseudoBinomial[v,x]^q,x] /;
        FreeQ[{p,q},x] && IntegersQ[p,m/p] && PseudoBinomialPairQ[x^(m/p)*u,v,x]",
        desc: "Algebraic normalization",
        refs: [],
        pattern: x_.pow(m_) * u__.pow(p_) * v__.pow(q_),
        with: [m_, u__, v__, p_, q_, x_],
        optional: [m_, q_, p_],
        when: {
            let scaled_u = x_.pow(&m_ / &p_) * &u__;
            freeq!([p_, q_], x_)
                && integersq!([p_, &m_ / &p_])
                && pseudo_binomial_pair_q(&scaled_u, &v__, x_)
        },
        rhs: {
            let scaled_u = x_.pow(&m_ / &p_) * &u__;
            let normalized_u = normalize_pseudo_binomial(&scaled_u, x_).rubi_rhs();
            let normalized_v = normalize_pseudo_binomial(&v__, x_).rubi_rhs();
            rubi_rhs_int(
                &(normalized_u.pow(&p_) * normalized_v.pow(&q_)),
                x_,
            )
        },
    ));
}

fn push_rules_rule_941(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, mn_, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 941,
        source: "Int[(a_+b_.*x_^n_.)^p_.*(c_+d_.*x_^mn_.)^q_.,x_Symbol] :=
          Int[(a+b*x^n)^p*(d+c*x^n)^q/x^(n*q),x] /;
        FreeQ[{a,b,c,d,n,p},x] && EqQ[mn,-n] && IntegerQ[q] && (PosQ[n] || Not[IntegerQ[p]])",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: (a__ + b__ * x_.pow(n_)).pow(p_) * (c__ + d__ * x_.pow(mn_)).pow(q_),
        with: [a__, b__, c__, d__, n_, mn_, p_, q_, x_],
        optional: [b__, d__, n_, mn_, p_, q_],
        x_free: [a__, b__, c__, d__, n_, p_],
        integer: [q_],
        scaled: [(mn_, -1, n_)],
        when: {
            freeq!([a__, b__, c__, d__, n_, p_], x_)
                && eqq!(mn_, -&n_)
                && integerq!(q_)
                && (posq!(n_) || !integerq!(p_))
        },
        rhs: {
            let recursive_integrand = (&a__ + &b__ * x_.pow(&n_)).pow(&p_)
                * (&d__ + &c__ * x_.pow(&n_)).pow(&q_)
                / x_.pow(&n_ * &q_);
            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_942(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, mn_, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 942,
        source: "Int[(a_+b_.*x_^n_.)^p_.*(c_+d_.*x_^mn_.)^q_,x_Symbol] :=
          x^(n*FracPart[q])*(c+d*x^(-n))^FracPart[q]/(d+c*x^n)^FracPart[q] \\[Star] Int[(a+b*x^n)^p*(d+c*x^n)^q/x^(n*q),x] /;
        FreeQ[{a,b,c,d,n,p,q},x] && EqQ[mn,-n] && Not[IntegerQ[q]] && Not[IntegerQ[p]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern: (c__ + d__ * x_.pow(mn_)).pow(q_) * (a__ + b__ * x_.pow(n_)).pow(p_),
        with: [a__, b__, c__, d__, n_, mn_, p_, q_, x_],
        optional: [b__, d__, n_, mn_, p_],
        x_free: [a__, b__, c__, d__, n_, mn_, p_, q_],
        when: {
            freeq!([a__, b__, c__, d__, n_, p_, q_], x_)
                && eqq!(mn_, -&n_)
                && !integerq!(q_)
                && !integerq!(p_)
        },
        rhs: {
            let frac_q = rubi_frac_part(&q_);
            let recursive_integrand = (&a__ + &b__ * x_.pow(&n_)).pow(&p_)
                * (&d__ + &c__ * x_.pow(&n_)).pow(&q_)
                / x_.pow(&n_ * &q_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let coefficient = x_.pow(&n_ * &frac_q)
                * (&c__ + &d__ * x_.pow(-&n_)).pow(&frac_q)
                / (&d__ + &c__ * x_.pow(&n_)).pow(frac_q);

            rubi_star(coefficient, recursive)
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
    let n_ = symbols.n_;
    let non2_ = symbols.non2_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (a1__ + b1__ * x_.pow(non2_)).pow(p_)
        * (a2__ + b2__ * x_.pow(non2_)).pow(p_)
        * (c__ + d__ * x_.pow(n_))
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let x_ = symbols.x_;
    (a__ + b__ * x_.pow(4)).sqrt() / (c__ + d__ * x_.pow(4))
}

#[inline(never)]
fn rubi_shared_pattern_2(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (a__ + b__ * x_.pow(n_)).pow(p_) * (c__ + d__ * x_.pow(n_))
}

#[inline(never)]
fn rubi_shared_pattern_3(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let q_ = symbols.q_;
    let x_ = symbols.x_;
    (a__ + b__ * x_.pow(n_)).pow(p_) * (c__ + d__ * x_.pow(n_)).pow(q_)
}

#[inline(never)]
fn rubi_shared_pattern_4(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (a__ + b__ * x_.pow(n_)).pow(p_) / (c__ + d__ * x_.pow(n_))
}
