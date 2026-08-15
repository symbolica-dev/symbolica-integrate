use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_280(rules);
    push_rules_rule_281(rules);
    push_rules_rule_282(rules);
    push_rules_rule_283(rules);
    push_rules_rule_284(rules);
    push_rules_rule_285(rules);
    push_rules_rule_286(rules);
    push_rules_rule_287(rules);
    push_rules_rule_288(rules);
    push_rules_rule_289(rules);
    push_rules_rule_290(rules);
    push_rules_rule_291(rules);
    push_rules_rule_292(rules);
    push_rules_rule_293(rules);
    push_rules_rule_294(rules);
    push_rules_rule_295(rules);
    push_rules_rule_296(rules);
    push_rules_rule_297(rules);
    push_rules_rule_298(rules);
    push_rules_rule_299(rules);
    push_rules_rule_300(rules);
    push_rules_rule_301(rules);
    push_rules_rule_302(rules);
    push_rules_rule_303(rules);
    push_rules_rule_304(rules);
    push_rules_rule_305(rules);
    push_rules_rule_306(rules);
    push_rules_rule_307(rules);
    push_rules_rule_308(rules);
    push_rules_rule_309(rules);
    push_rules_rule_310(rules);
    push_rules_rule_311(rules);
    push_rules_rule_312(rules);
    push_rules_rule_313(rules);
    push_rules_rule_314(rules);
    push_rules_rule_315(rules);
    push_rules_rule_316(rules);
    push_rules_rule_317(rules);
    push_rules_rule_318(rules);
    push_rules_rule_319(rules);
    push_rules_rule_320(rules);
    push_rules_rule_321(rules);
    push_rules_rule_322(rules);
    push_rules_rule_323(rules);
    push_rules_rule_324(rules);
    push_rules_rule_325(rules);
    push_rules_rule_326(rules);
    push_rules_rule_327(rules);
    push_rules_rule_328(rules);
    push_rules_rule_329(rules);
    push_rules_rule_330(rules);
    push_rules_rule_331(rules);
    push_rules_rule_332(rules);
    push_rules_rule_333(rules);
    push_rules_rule_334(rules);
}

fn push_rules_rule_280(rules: &mut Vec<RubiRule>) {
    rubi_symb!(b__, d__, n_, p_, q_, u__, x_);
    rules.push(rubi_rule!(
        order: 280,
        source: "Int[u_.*(b_.*x_^n_)^p_*(d_.*x_^n_)^q_,x_Symbol] :=
          b^IntPart[p]*d^IntPart[q]*(b*x^n)^FracPart[p]*(d*x^n)^FracPart[q]/x^(n*(FracPart[p]+FracPart[q])) \\[Star] Int[u*x^(n*(p+q)),x] /;
        FreeQ[{b,d,n,p,q},x]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern: u__ * (b__ * x_.pow(n_)).pow(p_) * (d__ * x_.pow(n_)).pow(q_),
        with: [b__, d__, n_, p_, q_, u__, x_],
        optional: [b__, d__, u__],
        x_free: [b__, d__, n_, p_, q_],
        when: { freeq!([b__, d__, n_, p_, q_], x_) },
        rhs: {
            let multiplier = b__.pow(rubi_int_part(&p_))
                * d__.pow(rubi_int_part(&q_))
                * (&b__ * x_.pow(&n_)).pow(rubi_frac_part(&p_))
                * (&d__ * x_.pow(&n_)).pow(rubi_frac_part(&q_))
                / x_.pow(&n_ * (rubi_frac_part(&p_) + rubi_frac_part(&q_)));
            let primitive = rubi_rhs_int(
                &(&u__ * x_.pow(&n_ * (&p_ + &q_))),
                x_,
            );
            rubi_star(multiplier, primitive)
        },
    ));
}

fn push_rules_rule_281(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, q_, u__, x_);
    let rule = rubi_rule!(
        order: 281,
        source: "Int[u_.*(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_)^q_.,x_Symbol] :=
          (b/d)^p \\[Star] Int[u*(c+d*x^n)^(p+q),x] /;
        FreeQ[{a,b,c,d,n,p,q},x] && EqQ[b*c-a*d,0] && IntegerQ[p] && Not[IntegerQ[q] && SimplerQ[a+b*x^n,c+d*x^n]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [a__, b__, c__, d__, n_, p_, q_, u__, x_],
        optional: [b__, d__, p_, q_, u__],
        x_free: [a__, b__, c__, d__, n_, p_, q_],
        when: {
            freeq!([a__, b__, c__, d__, n_, p_, q_], x_)
                && eqq!(&b__ * &c__ - &a__ * &d__, 0)
                && integerq!(p_)
                && !(integerq!(q_)
                    && rubi_simpler_q(
                        &(&a__ + &b__ * x_.pow(&n_)),
                        &(&c__ + &d__ * x_.pow(&n_)),
                    ))
        },
        rhs: {
            let multiplier = (&b__ / &d__).pow(&p_);
            let primitive = rubi_rhs_int(
                &(&u__ * (&c__ + &d__ * x_.pow(&n_)).pow(&p_ + &q_)),
                x_,
            );
            rubi_star(multiplier, primitive)
        },
    );
    rules.push(rule.with_proportional_binomial_base_pair());
}

fn push_rules_rule_282(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, q_, u__, x_);
    rules.push(rubi_rule!(
        order: 282,
        source: "Int[u_.*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
          (b/d)^p \\[Star] Int[u*(c+d*x^n)^(p+q),x] /;
        FreeQ[{a,b,c,d,n,p,q},x] && EqQ[b*c-a*d,0] && GtQ[b/d,0] && Not[SimplerQ[a+b*x^n,c+d*x^n]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [a__, b__, c__, d__, n_, p_, q_, u__, x_],
        optional: [b__, d__, u__],
        x_free: [a__, b__, c__, d__, n_, p_, q_],
        when: {
            freeq!([a__, b__, c__, d__, n_, p_, q_], x_)
                && eqq!(&b__ * &c__ - &a__ * &d__, 0)
                && gtq!(&b__ / &d__, 0)
                && !rubi_simpler_q(
                    &(&a__ + &b__ * x_.pow(&n_)),
                    &(&c__ + &d__ * x_.pow(&n_)),
                )
        },
        rhs: {
            let multiplier = (&b__ / &d__).pow(&p_);
            let primitive = rubi_rhs_int(
                &(&u__ * (&c__ + &d__ * x_.pow(&n_)).pow(&p_ + &q_)),
                x_,
            );
            rubi_star(multiplier, primitive)
        },
    ));
}

fn push_rules_rule_283(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, n_, p_, q_, u__, x_);
    rules.push(rubi_rule!(
        order: 283,
        source: "Int[u_.*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
          (a+b*x^n)^p/(c+d*x^n)^p \\[Star] Int[u*(c+d*x^n)^(p+q),x] /;
        FreeQ[{a,b,c,d,n,p,q},x] && EqQ[b*c-a*d,0] && Not[SimplerQ[a+b*x^n,c+d*x^n]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [a__, b__, c__, d__, n_, p_, q_, u__, x_],
        optional: [b__, d__, u__],
        x_free: [a__, b__, c__, d__, n_, p_, q_],
        when: {
            freeq!([a__, b__, c__, d__, n_, p_, q_], x_)
                && eqq!(&b__ * &c__ - &a__ * &d__, 0)
                && !rubi_simpler_q(
                    &(&a__ + &b__ * x_.pow(&n_)),
                    &(&c__ + &d__ * x_.pow(&n_)),
                )
        },
        rhs: {
            let first_base = &a__ + &b__ * x_.pow(&n_);
            let second_base = &c__ + &d__ * x_.pow(&n_);
            let multiplier = first_base.pow(&p_) / second_base.pow(&p_);
            let primitive = rubi_rhs_int(&(&u__ * second_base.pow(&p_ + &q_)), x_);
            rubi_star(multiplier, primitive)
        },
    ));
}

fn push_rules_rule_284(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, p_, x_);
    rules.push(rubi_rule!(
        order: 284,
        source: "Int[(a_+b_.*x_^2)^p_.*(c_+d_.*x_^2)^p_.,x_Symbol] :=
          Int[(a*c+b*d*x^4)^p,x] /;
        FreeQ[{a,b,c,d,p},x] && EqQ[b*c+a*d,0] && (IntegerQ[p] || GtQ[a,0] && GtQ[c,0])",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, p_, x_],
        optional: [b__, d__, p_],
        x_free: [a__, b__, c__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__, p_], x_)
                && eqq!(&b__ * &c__ + &a__ * &d__, 0)
                && (integerq!(p_) || gtq!(a__, 0) && gtq!(c__, 0))
        },
        rhs: {
            rubi_rhs_int(
                &(&a__ * &c__ + &b__ * &d__ * x_.pow(4)).pow(&p_),
                x_,
            )
        },
    ));
}

fn push_rules_rule_285(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, p_, x_);
    rules.push(rubi_rule!(
        order: 285,
        source: "Int[(a_+b_.*x_^2)^p_*(c_+d_.*x_^2)^p_,x_Symbol] :=
          x*(a+b*x^2)^p*(c+d*x^2)^p/(4*p+1) +
          4*a*c*p/(4*p+1) \\[Star] Int[(a+b*x^2)^(p-1)*(c+d*x^2)^(p-1),x] /;
        FreeQ[{a,b,c,d},x] && EqQ[b*c+a*d,0] && GtQ[p,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, p_, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && eqq!(&b__ * &c__ + &a__ * &d__, 0)
                && gtq!(p_, 0)
        },
        rhs: {
            let first_base = &a__ + &b__ * x_.pow(2);
            let second_base = &c__ + &d__ * x_.pow(2);
            let denominator = Atom::num(4) * &p_ + 1;
            let direct = x_ * first_base.pow(&p_) * second_base.pow(&p_)
                / &denominator;
            let primitive = rubi_rhs_int(
                &(first_base.pow(&p_ - 1) * second_base.pow(&p_ - 1)),
                x_,
            );
            let multiplier = Atom::num(4) * &a__ * &c__ * &p_ / denominator;
            rubi_simp(&(direct), x_) + rubi_star(multiplier, primitive)
        },
    ));
}

fn push_rules_rule_286(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, p_, x_);
    rules.push(rubi_rule!(
        order: 286,
        source: "Int[(a_+b_.*x_^2)^p_*(c_+d_.*x_^2)^p_,x_Symbol] :=
          -x*(a+b*x^2)^(p+1)*(c+d*x^2)^(p+1)/(4*a*c*(p+1)) +
          (4*p+5)/(4*a*c*(p+1)) \\[Star] Int[(a+b*x^2)^(p+1)*(c+d*x^2)^(p+1),x] /;
        FreeQ[{a,b,c,d},x] && EqQ[b*c+a*d,0] && LtQ[p,-1]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, p_, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && eqq!(&b__ * &c__ + &a__ * &d__, 0)
                && ltq!(p_, -1)
        },
        rhs: {
            let first_base = &a__ + &b__ * x_.pow(2);
            let second_base = &c__ + &d__ * x_.pow(2);
            let direct = Atom::num(-1) * x_
                * first_base.pow(&p_ + 1)
                * second_base.pow(&p_ + 1)
                / (Atom::num(4) * &a__ * &c__ * (&p_ + 1));
            let primitive = rubi_rhs_int(
                &(first_base.pow(&p_ + 1) * second_base.pow(&p_ + 1)),
                x_,
            );
            let multiplier = (Atom::num(4) * &p_ + 5)
                / (Atom::num(4) * &a__ * &c__ * (&p_ + 1));
            rubi_simp(&(direct), x_) + rubi_star(multiplier, primitive)
        },
    ));
}

fn push_rules_rule_287(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 287,
        source: "Int[1/(Sqrt[a_+b_.*x_^2]*Sqrt[c_+d_.*x_^2]),x_Symbol] :=
          1/Sqrt[2*a*d]*EllipticF[ArcSin[Sqrt[2*d]*x/Sqrt[c+d*x^2]],1/2] /;
        FreeQ[{a,b,c,d},x] && EqQ[b*c+a*d,0] && GtQ[a,0] && GtQ[d,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && eqq!(&b__ * &c__ + &a__ * &d__, 0)
                && gtq!(a__, 0)
                && gtq!(d__, 0)
        },
        rhs: {
            rubi_simp(&(rubi_elliptic_f(
                    (Atom::num(2) * &d__).sqrt() * x_
                        / (&c__ + &d__ * x_.pow(2)).sqrt(),
                    Atom::num(1) / 2,
                ) / (Atom::num(2) * &a__ * &d__).sqrt()), x_)
        },
    ));
}

fn push_rules_rule_288(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, p_, x_);
    rules.push(rubi_rule!(
        order: 288,
        source: "Int[(a_+b_.*x_^2)^p_*(c_+d_.*x_^2)^p_,x_Symbol] :=
          (c+d*x^2)^FracPart[p]/((-1)^IntPart[p]*(-c-d*x^2)^FracPart[p]) \\[Star] Int[(-a*c-b*d*x^4)^p,x] /;
        FreeQ[{a,b,c,d,p},x] && EqQ[b*c+a*d,0] && GtQ[a,0] && LtQ[c,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, p_, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__, p_], x_)
                && eqq!(&b__ * &c__ + &a__ * &d__, 0)
                && gtq!(a__, 0)
                && ltq!(c__, 0)
        },
        rhs: {
            let multiplier = (&c__ + &d__ * x_.pow(2)).pow(rubi_frac_part(&p_))
                / ((-Atom::num(1)).pow(rubi_int_part(&p_))
                    * (-&c__ - &d__ * x_.pow(2)).pow(rubi_frac_part(&p_)));
            let primitive = rubi_rhs_int(
                &(-&a__ * &c__ - &b__ * &d__ * x_.pow(4)).pow(&p_),
                x_,
            );
            rubi_star(multiplier, primitive)
        },
    ));
}

fn push_rules_rule_289(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, p_, x_);
    rules.push(rubi_rule!(
        order: 289,
        source: "Int[(a_+b_.*x_^2)^p_*(c_+d_.*x_^2)^p_,x_Symbol] :=
          (a+b*x^2)^FracPart[p]*(c+d*x^2)^FracPart[p]/(a*c+b*d*x^4)^FracPart[p] \\[Star] Int[(a*c+b*d*x^4)^p,x] /;
        FreeQ[{a,b,c,d,p},x] && EqQ[b*c+a*d,0] && Not[IntegerQ[p]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, p_, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__, p_], x_)
                && eqq!(&b__ * &c__ + &a__ * &d__, 0)
                && !integerq!(p_)
        },
        rhs: {
            let multiplier = (&a__ + &b__ * x_.pow(2)).pow(rubi_frac_part(&p_))
                * (&c__ + &d__ * x_.pow(2)).pow(rubi_frac_part(&p_))
                / (&a__ * &c__ + &b__ * &d__ * x_.pow(4)).pow(rubi_frac_part(&p_));
            let primitive = rubi_rhs_int(
                &(&a__ * &c__ + &b__ * &d__ * x_.pow(4)).pow(&p_),
                x_,
            );
            rubi_star(multiplier, primitive)
        },
    ));
}

fn push_rules_rule_290(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 290,
        source: "Int[(a_+b_.*x_^2)^p_.*(c_+d_.*x_^2)^q_.,x_Symbol] :=
          Int[ExpandIntegrand[(a+b*x^2)^p*(c+d*x^2)^q,x],x] /;
        FreeQ[{a,b,c,d},x] && NeQ[b*c-a*d,0] && IGtQ[p,0] && IGtQ[q,0]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, p_, q_, x_],
        optional: [b__, d__, p_, q_],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && igtq!(p_, 0)
                && igtq!(q_, 0)
        },
        rhs: {
            let integrand = (&a__ + &b__ * x_.pow(2)).pow(&p_)
                * (&c__ + &d__ * x_.pow(2)).pow(&q_);
            let expanded = rubi_expand_integrand(&integrand, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_291(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 291,
        source: "Int[1/(Sqrt[a_+b_.*x_^2]*(c_+d_.*x_^2)),x_Symbol] :=
          Subst[Int[1/(c-(b*c-a*d)*x^2),x],x,x/Sqrt[a+b*x^2]] /;
        FreeQ[{a,b,c,d},x] && NeQ[b*c-a*d,0]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern: Atom::num(1) / ((a__ + b__ * x_.pow(2)).sqrt() * (c__ + d__ * x_.pow(2))),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let primitive = rubi_rhs_int(
                &(Atom::num(1)
                    / (&c__ - (&b__ * &c__ - &a__ * &d__) * sub_atom.pow(2))),
                sub,
            );
            rubi_subst(
                &primitive,
                sub,
                x_ / (&a__ + &b__ * x_.pow(2)).sqrt(),
            )
        },
    ));
}

fn push_rules_rule_292(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 292,
        source: "Int[(a_+b_.*x_^2)^p_*(c_+d_.*x_^2)^q_.,x_Symbol] :=
          -x*(a+b*x^2)^(p+1)*(c+d*x^2)^q/(2*a*(p+1)) -
          c*q/(a*(p+1)) \\[Star] Int[(a+b*x^2)^(p+1)*(c+d*x^2)^(q-1),x] /;
        FreeQ[{a,b,c,d,p},x] && NeQ[b*c-a*d,0] && EqQ[2*(p+q+1)+1,0] && GtQ[q,0] && NeQ[p,-1]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, p_, q_, x_],
        optional: [b__, d__, q_],
        x_free: [a__, b__, c__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__, p_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(Atom::num(2) * (&p_ + &q_ + 1) + 1, 0)
                && gtq!(q_, 0)
                && neq!(p_, -1)
        },
        rhs: {
            let first_base = &a__ + &b__ * x_.pow(2);
            let second_base = &c__ + &d__ * x_.pow(2);
            let direct = Atom::num(-1) * x_ * first_base.pow(&p_ + 1) * second_base.pow(&q_)
                / (Atom::num(2) * &a__ * (&p_ + 1));
            let primitive = rubi_rhs_int(
                &(first_base.pow(&p_ + 1) * second_base.pow(&q_ - 1)),
                x_,
            );
            let multiplier = -&c__ * &q_ / (&a__ * (&p_ + 1));
            rubi_simp(&(direct), x_) + rubi_star(multiplier, primitive)
        },
    ));
}

fn push_rules_rule_293(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 293,
        source: "Int[(a_+b_.*x_^2)^p_*(c_+d_.*x_^2)^q_,x_Symbol] :=
          a^p*x/(c^(p+1)*Sqrt[c+d*x^2])*Hypergeometric2F1[1/2,-p,3/2,-(b*c-a*d)*x^2/(a*(c+d*x^2))] /;
        FreeQ[{a,b,c,d,q},x] && NeQ[b*c-a*d,0] && EqQ[2*(p+q+1)+1,0] && ILtQ[p,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, p_, q_, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__, q_],
        when: {
            freeq!([a__, b__, c__, d__, q_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(Atom::num(2) * (&p_ + &q_ + 1) + 1, 0)
                && iltq!(p_, 0)
        },
        rhs: {
            rubi_simp(&(a__.pow(&p_) * x_
                    / (c__.pow(&p_ + 1) * (&c__ + &d__ * x_.pow(2)).sqrt())
                    * rubi_hypergeometric2f1(
                        Atom::num(1) / 2,
                        -&p_,
                        Atom::num(3) / 2,
                        -(&b__ * &c__ - &a__ * &d__) * x_.pow(2)
                            / (&a__ * (&c__ + &d__ * x_.pow(2))),
                    )), x_)
        },
    ));
}

fn push_rules_rule_294(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 294,
        source: "Int[(a_+b_.*x_^2)^p_*(c_+d_.*x_^2)^q_,x_Symbol] :=
          x*(a+b*x^2)^p/(c*(c*(a+b*x^2)/(a*(c+d*x^2)))^p*(c+d*x^2)^(1/2+p))*
            Hypergeometric2F1[1/2,-p,3/2,-(b*c-a*d)*x^2/(a*(c+d*x^2))] /;
        FreeQ[{a,b,c,d,p,q},x] && NeQ[b*c-a*d,0] && EqQ[2*(p+q+1)+1,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, p_, q_, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__, p_, q_],
        when: {
            freeq!([a__, b__, c__, d__, p_, q_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(Atom::num(2) * (&p_ + &q_ + 1) + 1, 0)
        },
        rhs: {
            let first_base = &a__ + &b__ * x_.pow(2);
            let second_base = &c__ + &d__ * x_.pow(2);
            rubi_simp(&(x_ * first_base.pow(&p_)
                    / (&c__
                        * (&c__ * &first_base / (&a__ * &second_base)).pow(&p_)
                        * second_base.pow(Atom::num(1) / 2 + &p_))
                    * rubi_hypergeometric2f1(
                        Atom::num(1) / 2,
                        -&p_,
                        Atom::num(3) / 2,
                        -(&b__ * &c__ - &a__ * &d__) * x_.pow(2)
                            / (&a__ * second_base),
                    )), x_)
        },
    ));
}

fn push_rules_rule_295(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 295,
        source: "Int[(a_+b_.*x_^2)^p_*(c_+d_.*x_^2)^q_,x_Symbol] :=
          x*(a+b*x^2)^(p+1)*(c+d*x^2)^(q+1)/(a*c) /;
        FreeQ[{a,b,c,d,p,q},x] && NeQ[b*c-a*d,0] && EqQ[2*(p+q+2)+1,0] && EqQ[a*d*(p+1)+b*c*(q+1),0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, p_, q_, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__, p_, q_],
        when: {
            freeq!([a__, b__, c__, d__, p_, q_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(Atom::num(2) * (&p_ + &q_ + 2) + 1, 0)
                && eqq!(&a__ * &d__ * (&p_ + 1) + &b__ * &c__ * (&q_ + 1), 0)
        },
        rhs: {
            rubi_simp(&(x_
                    * (&a__ + &b__ * x_.pow(2)).pow(&p_ + 1)
                    * (&c__ + &d__ * x_.pow(2)).pow(&q_ + 1)
                    / (&a__ * &c__)), x_)
        },
    ));
}

fn push_rules_rule_296(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 296,
        source: "Int[(a_+b_.*x_^2)^p_*(c_+d_.*x_^2)^q_,x_Symbol] :=
          -b*x*(a+b*x^2)^(p+1)*(c+d*x^2)^(q+1)/(2*a*(p+1)*(b*c-a*d)) +
          (b*c+2*(p+1)*(b*c-a*d))/(2*a*(p+1)*(b*c-a*d)) \\[Star] Int[(a+b*x^2)^(p+1)*(c+d*x^2)^q,x] /;
        FreeQ[{a,b,c,d,q},x] && NeQ[b*c-a*d,0] && EqQ[2*(p+q+2)+1,0] && (LtQ[p,-1] || Not[LtQ[q,-1]]) && NeQ[p,-1]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, p_, q_, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__, q_],
        when: {
            freeq!([a__, b__, c__, d__, q_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(Atom::num(2) * (&p_ + &q_ + 2) + 1, 0)
                && (ltq!(p_, -1) || !ltq!(q_, -1))
                && neq!(p_, -1)
        },
        rhs: {
            let first_base = &a__ + &b__ * x_.pow(2);
            let second_base = &c__ + &d__ * x_.pow(2);
            let determinant = &b__ * &c__ - &a__ * &d__;
            let denominator = Atom::num(2) * &a__ * (&p_ + 1) * &determinant;
            let direct = -&b__
                * x_
                * first_base.pow(&p_ + 1)
                * second_base.pow(&q_ + 1)
                / &denominator;
            let primitive = rubi_rhs_int(
                &(first_base.pow(&p_ + 1) * second_base.pow(&q_)),
                x_,
            );
            let multiplier = (&b__ * &c__ + Atom::num(2) * (&p_ + 1) * determinant)
                / denominator;
            rubi_simp(&(direct), x_) + rubi_star(multiplier, primitive)
        },
    ));
}

fn push_rules_rule_297(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, p_, x_);
    rules.push(rubi_rule!(
        order: 297,
        source: "Int[(a_+b_.*x_^2)^p_.*(c_+d_.*x_^2),x_Symbol] :=
          c*x*(a+b*x^2)^(p+1)/a /;
        FreeQ[{a,b,c,d,p},x] && NeQ[b*c-a*d,0] && EqQ[a*d-b*c*(2*p+3),0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, p_, x_],
        optional: [b__, d__, p_],
        x_free: [a__, b__, c__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__, p_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(&a__ * &d__ - &b__ * &c__ * (Atom::num(2) * &p_ + 3), 0)
        },
        rhs: {
            rubi_simp(&(&c__ * x_ * (&a__ + &b__ * x_.pow(2)).pow(&p_ + 1)
                    / &a__), x_)
        },
    ));
}

fn push_rules_rule_298(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, p_, x_);
    rules.push(rubi_rule!(
        order: 298,
        source: "Int[(a_+b_.*x_^2)^p_*(c_+d_.*x_^2),x_Symbol] :=
          -(b*c-a*d)*x*(a+b*x^2)^(p+1)/(2*a*b*(p+1)) -
          (a*d-b*c*(2*p+3))/(2*a*b*(p+1)) \\[Star] Int[(a+b*x^2)^(p+1),x] /;
        FreeQ[{a,b,c,d,p},x] && NeQ[b*c-a*d,0] && (LtQ[p,-1] || ILtQ[1/2+p,0])",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, p_, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__, p_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && (ltq!(p_, -1) || iltq!(Atom::num(1) / 2 + &p_, 0))
        },
        rhs: {
            let direct = -(&b__ * &c__ - &a__ * &d__)
                * x_
                * (&a__ + &b__ * x_.pow(2)).pow(&p_ + 1)
                / (Atom::num(2) * &a__ * &b__ * (&p_ + 1));
            let primitive = rubi_rhs_int(
                &(&a__ + &b__ * x_.pow(2)).pow(&p_ + 1),
                x_,
            );
            let multiplier = -(&a__ * &d__ - &b__ * &c__ * (Atom::num(2) * &p_ + 3))
                / (Atom::num(2) * &a__ * &b__ * (&p_ + 1));
            rubi_simp(&(direct), x_) + rubi_star(multiplier, primitive)
        },
    ));
}

fn push_rules_rule_299(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, p_, x_);
    rules.push(rubi_rule!(
        order: 299,
        source: "Int[(a_+b_.*x_^2)^p_*(c_+d_.*x_^2),x_Symbol] :=
          d*x*(a+b*x^2)^(p+1)/(b*(2*p+3)) -
          (a*d-b*c*(2*p+3))/(b*(2*p+3)) \\[Star] Int[(a+b*x^2)^p,x] /;
        FreeQ[{a,b,c,d},x] && NeQ[b*c-a*d,0] && NeQ[2*p+3,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, p_, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && neq!(Atom::num(2) * &p_ + 3, 0)
        },
        rhs: {
            let denominator = &b__ * (Atom::num(2) * &p_ + 3);
            let direct = &d__ * x_ * (&a__ + &b__ * x_.pow(2)).pow(&p_ + 1)
                / &denominator;
            let primitive = rubi_rhs_int(
                &(&a__ + &b__ * x_.pow(2)).pow(&p_),
                x_,
            );
            let multiplier = -(&a__ * &d__ - &b__ * &c__ * (Atom::num(2) * &p_ + 3))
                / denominator;
            rubi_simp(&(direct), x_) + rubi_star(multiplier, primitive)
        },
    ));
}

fn push_rules_rule_300(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 300,
        source: "Int[(a_+b_.*x_^2)^p_*(c_+d_.*x_^2)^q_,x_Symbol] :=
          Int[PolynomialDivide[(a+b*x^2)^p,(c+d*x^2)^(-q),x],x] /;
        FreeQ[{a,b,c,d},x] && NeQ[b*c-a*d,0] && IGtQ[p,0] && ILtQ[q,0] && GeQ[p,-q]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, p_, q_, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && igtq!(p_, 0)
                && iltq!(q_, 0)
                && geq!(p_, (-&q_))
        },
        rhs: {
            let divided = rubi_polynomial_divide(
                &(&a__ + &b__ * x_.pow(2)).pow(&p_),
                &(&c__ + &d__ * x_.pow(2)).pow(-&q_),
                x_,
            ).rubi_rhs();
            rubi_rhs_int(&divided, x_)
        },
    ));
}

fn push_rules_rule_301(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, p_, x_);
    rules.push(rubi_rule!(
        order: 301,
        source: "Int[(a_+b_.*x_^2)^p_./(c_+d_.*x_^2),x_Symbol] :=
          b/d \\[Star] Int[(a+b*x^2)^(p-1),x] - (b*c-a*d)/d \\[Star] Int[(a+b*x^2)^(p-1)/(c+d*x^2),x] /;
        FreeQ[{a,b,c,d},x] && NeQ[b*c-a*d,0] && GtQ[p,0] && (EqQ[p,1/2] || EqQ[Denominator[p],4] || EqQ[p,2/3] && EqQ[b*c+3*a*d,0])",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, p_, x_],
        optional: [b__, d__, p_],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && gtq!(p_, 0)
                && (eqq!(p_, Atom::num(1) / 2)
                    || eqq!(rubi_denominator_atom(&p_), 4)
                    || eqq!(p_, Atom::num(2) / 3)
                        && eqq!(&b__ * &c__ + Atom::num(3) * &a__ * &d__, 0))
        },
        rhs: {
            let first_base = &a__ + &b__ * x_.pow(2);
            let second_base = &c__ + &d__ * x_.pow(2);
            let first = rubi_rhs_int(&first_base.pow(&p_ - 1), x_);
            let second = rubi_rhs_int(&(first_base.pow(&p_ - 1) / second_base), x_);
            rubi_star(&b__ / &d__, first)
                    - rubi_star((&b__ * &c__ - &a__ * &d__) / &d__, second)
        },
    ));
}

fn push_rules_rule_302(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, p_, x_);
    rules.push(rubi_rule!(
        order: 302,
        source: "Int[(a_+b_.*x_^2)^p_/(c_+d_.*x_^2),x_Symbol] :=
          b/(b*c-a*d) \\[Star] Int[(a+b*x^2)^p,x] - d/(b*c-a*d) \\[Star] Int[(a+b*x^2)^(p+1)/(c+d*x^2),x] /;
        FreeQ[{a,b,c,d},x] && NeQ[b*c-a*d,0] && LtQ[p,-1] && EqQ[Denominator[p],4] && (EqQ[p,-5/4] || EqQ[p,-7/4])",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, p_, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && ltq!(p_, -1)
                && eqq!(rubi_denominator_atom(&p_), 4)
                && (eqq!(p_, Atom::num(-5) / 4) || eqq!(p_, Atom::num(-7) / 4))
        },
        rhs: {
            let first_base = &a__ + &b__ * x_.pow(2);
            let second_base = &c__ + &d__ * x_.pow(2);
            let determinant = &b__ * &c__ - &a__ * &d__;
            let first = rubi_rhs_int(&first_base.pow(&p_), x_);
            let second = rubi_rhs_int(&(first_base.pow(&p_ + 1) / second_base), x_);
            rubi_star(&b__ / &determinant, first)
                    - rubi_star(&d__ / determinant, second)
        },
    ));
}

fn push_rules_rule_303(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 303,
        source: "Int[1/((a_+b_.*x_^2)*(c_+d_.*x_^2)),x_Symbol] :=
          b/(b*c-a*d) \\[Star] Int[1/(a+b*x^2),x] - d/(b*c-a*d) \\[Star] Int[1/(c+d*x^2),x] /;
        FreeQ[{a,b,c,d},x] && NeQ[b*c-a*d,0]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern: Atom::num(1) / ((a__ + b__ * x_.pow(2)) * (c__ + d__ * x_.pow(2))),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
        },
        rhs: {
            let determinant = &b__ * &c__ - &a__ * &d__;
            let first = rubi_rhs_int(
                &(Atom::num(1) / (&a__ + &b__ * x_.pow(2))),
                x_,
            );
            let second = rubi_rhs_int(
                &(Atom::num(1) / (&c__ + &d__ * x_.pow(2))),
                x_,
            );
            rubi_star(&b__ / &determinant, first)
                    - rubi_star(&d__ / determinant, second)
        },
    ));
}

fn push_rules_rule_304(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 304,
        source: "Int[1/((a_+b_.*x_^2)^(1/3)*(c_+d_.*x_^2)),x_Symbol] :=
          With[{q=Rt[b/a,2]},
          q*ArcTanh[Sqrt[3]/(q*x)]/(2*2^(2/3)*Sqrt[3]*a^(1/3)*d) +
          q*ArcTanh[Sqrt[3]*(a^(1/3)-2^(1/3)*(a+b*x^2)^(1/3))/(a^(1/3)*q*x)]/(2*2^(2/3)*Sqrt[3]*a^(1/3)*d) +
          q*ArcTan[q*x]/(6*2^(2/3)*a^(1/3)*d) -
          q*ArcTan[(a^(1/3)*q*x)/(a^(1/3)+2^(1/3)*(a+b*x^2)^(1/3))]/(2*2^(2/3)*a^(1/3)*d)] /;
        FreeQ[{a,b,c,d},x] && NeQ[b*c-a*d,0] && EqQ[b*c+3*a*d,0] && PosQ[b/a]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(&b__ * &c__ + Atom::num(3) * &a__ * &d__, 0)
                && posq!(&b__ / &a__)
        },
        rhs: {
            let q = rubi_rt(&(&b__ / &a__), 2);
            let base = &a__ + &b__ * x_.pow(2);
            let a_third = a__.pow((1, 3));
            let two_third = Atom::num(2).pow((1, 3));
            let two_two_thirds = Atom::num(2).pow((2, 3));
            let radical = base.pow((1, 3));
            let sqrt_three = Atom::num(3).sqrt();
            rubi_simp(&(&q * (&sqrt_three / (&q * x_)).atanh()
                    / (Atom::num(2) * &two_two_thirds * &sqrt_three * &a_third * &d__)), x_)
                    + rubi_simp(&(&q * (&sqrt_three * (&a_third - &two_third * &radical)
                        / (&a_third * &q * x_))
                        .atanh()
                        / (Atom::num(2) * &two_two_thirds * &sqrt_three * &a_third * &d__)), x_)
                    + rubi_simp(&(&q * (&q * x_).atan()
                        / (Atom::num(6) * &two_two_thirds * &a_third * &d__)), x_)
                    - rubi_simp(&(&q
                        * (&a_third * &q * x_ / (&a_third + &two_third * &radical)).atan()
                        / (Atom::num(2) * two_two_thirds * a_third * d__)), x_)
        },
    ));
}

fn push_rules_rule_305(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 305,
        source: "Int[1/((a_+b_.*x_^2)^(1/3)*(c_+d_.*x_^2)),x_Symbol] :=
          With[{q=Rt[-b/a,2]},
          q*ArcTan[Sqrt[3]/(q*x)]/(2*2^(2/3)*Sqrt[3]*a^(1/3)*d) +
          q*ArcTan[Sqrt[3]*(a^(1/3)-2^(1/3)*(a+b*x^2)^(1/3))/(a^(1/3)*q*x)]/(2*2^(2/3)*Sqrt[3]*a^(1/3)*d) -
          q*ArcTanh[q*x]/(6*2^(2/3)*a^(1/3)*d) +
          q*ArcTanh[(a^(1/3)*q*x)/(a^(1/3)+2^(1/3)*(a+b*x^2)^(1/3))]/(2*2^(2/3)*a^(1/3)*d)] /;
        FreeQ[{a,b,c,d},x] && NeQ[b*c-a*d,0] && EqQ[b*c+3*a*d,0] && NegQ[b/a]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(&b__ * &c__ + Atom::num(3) * &a__ * &d__, 0)
                && negq!(&b__ / &a__)
        },
        rhs: {
            let q = rubi_rt(&(-&b__ / &a__), 2);
            let base = &a__ + &b__ * x_.pow(2);
            let a_third = a__.pow((1, 3));
            let two_third = Atom::num(2).pow((1, 3));
            let two_two_thirds = Atom::num(2).pow((2, 3));
            let radical = base.pow((1, 3));
            let sqrt_three = Atom::num(3).sqrt();
            rubi_simp(&(&q * (&sqrt_three / (&q * x_)).atan()
                    / (Atom::num(2) * &two_two_thirds * &sqrt_three * &a_third * &d__)), x_)
                    + rubi_simp(&(&q * (&sqrt_three * (&a_third - &two_third * &radical)
                        / (&a_third * &q * x_))
                        .atan()
                        / (Atom::num(2) * &two_two_thirds * &sqrt_three * &a_third * &d__)), x_)
                    - rubi_simp(&(&q * (&q * x_).atanh()
                        / (Atom::num(6) * &two_two_thirds * &a_third * &d__)), x_)
                    + rubi_simp(&(&q
                        * (&a_third * &q * x_ / (&a_third + &two_third * &radical)).atanh()
                        / (Atom::num(2) * two_two_thirds * a_third * d__)), x_)
        },
    ));
}

fn push_rules_rule_306(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 306,
        source: "Int[1/((a_+b_.*x_^2)^(1/3)*(c_+d_.*x_^2)),x_Symbol] :=
          With[{q=Rt[b/a,2]},
          q*ArcTan[q*x/3]/(12*Rt[a,3]*d) +
          q*ArcTan[(Rt[a,3]-(a+b*x^2)^(1/3))^2/(3*Rt[a,3]^2*q*x)]/(12*Rt[a,3]*d) -
          q*ArcTanh[(Sqrt[3]*(Rt[a,3]-(a+b*x^2)^(1/3)))/(Rt[a,3]*q*x)]/(4*Sqrt[3]*Rt[a,3]*d)] /;
        FreeQ[{a,b,c,d},x] && NeQ[b*c-a*d,0] && EqQ[b*c-9*a*d,0] && PosQ[b/a]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(&b__ * &c__ - Atom::num(9) * &a__ * &d__, 0)
                && posq!(&b__ / &a__)
        },
        rhs: {
            let q = rubi_rt(&(&b__ / &a__), 2);
            let rt_a = rubi_rt(&a__, 3);
            let radical = (&a__ + &b__ * x_.pow(2)).pow((1, 3));
            let diff = &rt_a - &radical;
            let sqrt_three = Atom::num(3).sqrt();
            rubi_simp(&(&q * (&q * x_ / 3).atan() / (Atom::num(12) * &rt_a * &d__)), x_)
                    + rubi_simp(&(&q
                        * (diff.pow(2) / (Atom::num(3) * rt_a.pow(2) * &q * x_)).atan()
                        / (Atom::num(12) * &rt_a * &d__)), x_)
                    - rubi_simp(&(&q * (&sqrt_three * &diff / (&rt_a * &q * x_)).atanh()
                        / (Atom::num(4) * sqrt_three * rt_a * d__)), x_)
        },
    ));
}

fn push_rules_rule_307(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 307,
        source: "Int[1/((a_+b_.*x_^2)^(1/3)*(c_+d_.*x_^2)),x_Symbol] :=
          With[{q=Rt[-b/a,2]},
          -q*ArcTanh[q*x/3]/(12*Rt[a,3]*d) +
          q*ArcTanh[(Rt[a,3]-(a+b*x^2)^(1/3))^2/(3*Rt[a,3]^2*q*x)]/(12*Rt[a,3]*d) -
          q*ArcTan[(Sqrt[3]*(Rt[a,3]-(a+b*x^2)^(1/3)))/(Rt[a,3]*q*x)]/(4*Sqrt[3]*Rt[a,3]*d)] /;
        FreeQ[{a,b,c,d},x] && NeQ[b*c-a*d,0] && EqQ[b*c-9*a*d,0] && NegQ[b/a]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(&b__ * &c__ - Atom::num(9) * &a__ * &d__, 0)
                && negq!(&b__ / &a__)
        },
        rhs: {
            let q = rubi_rt(&(-&b__ / &a__), 2);
            let rt_a = rubi_rt(&a__, 3);
            let radical = (&a__ + &b__ * x_.pow(2)).pow((1, 3));
            let diff = &rt_a - &radical;
            let sqrt_three = Atom::num(3).sqrt();
            rubi_simp(&(-&q * (&q * x_ / 3).atanh() / (Atom::num(12) * &rt_a * &d__)), x_)
                    + rubi_simp(&(&q
                        * (diff.pow(2) / (Atom::num(3) * rt_a.pow(2) * &q * x_)).atanh()
                        / (Atom::num(12) * &rt_a * &d__)), x_)
                    - rubi_simp(&(&q * (&sqrt_three * &diff / (&rt_a * &q * x_)).atan()
                        / (Atom::num(4) * sqrt_three * rt_a * d__)), x_)
        },
    ));
}

fn push_rules_rule_308(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 308,
        source: "Int[1/((a_+b_.*x_^2)^(1/4)*(c_+d_.*x_^2)),x_Symbol] :=
          With[{q=Rt[b^2/a,4]},
          -b/(2*a*d*q)*ArcTan[(b+q^2*Sqrt[a+b*x^2])/(q^3*x*(a+b*x^2)^(1/4))] -
          b/(2*a*d*q)*ArcTanh[(b-q^2*Sqrt[a+b*x^2])/(q^3*x*(a+b*x^2)^(1/4))]] /;
        FreeQ[{a,b,c,d},x] && EqQ[b*c-2*a*d,0] && PosQ[b^2/a]",
        desc: "Apply the direct antiderivative formula.",
        refs: ["Enestr\\[ODoubleDot]m index number E688 in The Euler Archive"],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && eqq!(&b__ * &c__ - Atom::num(2) * &a__ * &d__, 0)
                && posq!(b__.pow(2) / &a__)
        },
        rhs: {
            let q = rubi_rt(&(b__.pow(2) / &a__), 4);
            let base = &a__ + &b__ * x_.pow(2);
            let radical = base.pow((1, 4));
            let denominator = Atom::num(2) * &a__ * &d__ * &q;
            rubi_simp(&(-&b__
                    * ((&b__ + q.pow(2) * base.sqrt()) / (q.pow(3) * x_ * &radical)).atan()
                    / &denominator), x_)
                    - rubi_simp(&(&b__
                        * ((&b__ - q.pow(2) * base.sqrt()) / (q.pow(3) * x_ * radical)).atanh()
                        / denominator), x_)
        },
    ));
}

fn push_rules_rule_309(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 309,
        source: "Int[1/((a_+b_.*x_^2)^(1/4)*(c_+d_.*x_^2)),x_Symbol] :=
          With[{q=Rt[-b^2/a,4]},
          b/(2*Sqrt[2]*a*d*q)*ArcTan[q*x/(Sqrt[2]*(a+b*x^2)^(1/4))] +
          b/(2*Sqrt[2]*a*d*q)*ArcTanh[q*x/(Sqrt[2]*(a+b*x^2)^(1/4))]] /;
        FreeQ[{a,b,c,d},x] && EqQ[b*c-2*a*d,0] && NegQ[b^2/a]",
        desc: "Integration by substitution",
        refs: ["Enestr\\[ODoubleDot]m index number E688 in The Euler Archive"],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && eqq!(&b__ * &c__ - Atom::num(2) * &a__ * &d__, 0)
                && negq!(b__.pow(2) / &a__)
        },
        rhs: {
            let q = rubi_rt(&(-b__.pow(2) / &a__), 4);
            let base = &a__ + &b__ * x_.pow(2);
            let sqrt_two = Atom::num(2).sqrt();
            let denominator = Atom::num(2) * &sqrt_two * &a__ * &d__ * &q;
            let argument = &q * x_ / (&sqrt_two * base.pow((1, 4)));
            rubi_simp(&(&b__ * &argument.atan() / &denominator), x_)
                    + rubi_simp(&(&b__ * argument.atanh() / denominator), x_)
        },
    ));
}

fn push_rules_rule_310(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 310,
        source: "Int[1/((a_+b_.*x_^2)^(1/4)*(c_+d_.*x_^2)),x_Symbol] :=
          2*Sqrt[-b*x^2/a]/x \\[Star] Subst[Int[x^2/(Sqrt[1-x^4/a]*(b*c-a*d+d*x^4)),x],x,(a+b*x^2)^(1/4)] /;
        FreeQ[{a,b,c,d},x] && NeQ[b*c-a*d,0]",
        desc: "Piecewise constant extraction and integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let primitive = rubi_rhs_int(
                &(sub_atom.pow(2)
                    / ((Atom::num(1) - sub_atom.pow(4) / &a__).sqrt()
                        * (&b__ * &c__ - &a__ * &d__ + &d__ * sub_atom.pow(4)))),
                sub,
            );
            let substituted = rubi_subst(
                &primitive,
                sub,
                (&a__ + &b__ * x_.pow(2)).pow((1, 4)),
            );
            let multiplier = Atom::num(2) * (-&b__ * x_.pow(2) / &a__).sqrt() / x_;
            rubi_star(multiplier, substituted)
        },
    ));
}

fn push_rules_rule_311(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 311,
        source: "Int[1/((a_+b_.*x_^2)^(3/4)*(c_+d_.*x_^2)),x_Symbol] :=
          1/c \\[Star] Int[1/(a+b*x^2)^(3/4),x] - d/c \\[Star] Int[x^2/((a+b*x^2)^(3/4)*(c+d*x^2)),x] /;
        FreeQ[{a,b,c,d},x] && EqQ[b*c-2*a*d,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && eqq!(&b__ * &c__ - Atom::num(2) * &a__ * &d__, 0)
        },
        rhs: {
            let first_base = &a__ + &b__ * x_.pow(2);
            let second_base = &c__ + &d__ * x_.pow(2);
            let first = rubi_rhs_int(&(Atom::num(1) / first_base.pow((3, 4))), x_);
            let second = rubi_rhs_int(
                &(x_.pow(2) / (first_base.pow((3, 4)) * second_base)),
                x_,
            );
            rubi_star(Atom::num(1) / &c__, first)
                    - rubi_star(&d__ / &c__, second)
        },
    ));
}

fn push_rules_rule_312(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 312,
        source: "Int[1/((a_+b_.*x_^2)^(3/4)*(c_+d_.*x_^2)),x_Symbol] :=
          Sqrt[-b*x^2/a]/(2*x) \\[Star] Subst[Int[1/(Sqrt[-b*x/a]*(a+b*x)^(3/4)*(c+d*x)),x],x,x^2] /;
        FreeQ[{a,b,c,d},x] && NeQ[b*c-a*d,0]",
        desc: "Piecewise constant extranction and integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let primitive = rubi_rhs_int(
                &(Atom::num(1)
                    / ((-&b__ * &sub_atom / &a__).sqrt()
                        * (&a__ + &b__ * &sub_atom).pow((3, 4))
                        * (&c__ + &d__ * sub_atom))),
                sub,
            );
            let substituted = rubi_subst(&primitive, sub, x_.pow(2));
            let multiplier = (-&b__ * x_.pow(2) / &a__).sqrt()
                / (Atom::num(2) * x_);
            rubi_star(multiplier, substituted)
        },
    ));
}

fn push_rules_rule_313(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 313,
        source: "Int[Sqrt[a_+b_.*x_^2]/(c_+d_.*x_^2)^(3/2),x_Symbol] :=
          Sqrt[a+b*x^2]/(c*Rt[d/c,2]*Sqrt[c+d*x^2]*Sqrt[c*(a+b*x^2)/(a*(c+d*x^2))])*EllipticE[ArcTan[Rt[d/c,2]*x],1-b*c/(a*d)] /;
        FreeQ[{a,b,c,d},x] && PosQ[b/a] && PosQ[d/c]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: (a__ + b__ * x_.pow(2)).sqrt() / (c__ + d__ * x_.pow(2)).pow((3, 2)),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && posq!(&b__ / &a__)
                && posq!(&d__ / &c__)
        },
        rhs: {
            let rt = rubi_rt(&(&d__ / &c__), 2);
            let first_base = &a__ + &b__ * x_.pow(2);
            let second_base = &c__ + &d__ * x_.pow(2);
            rubi_simp(&(first_base.sqrt()
                    * rubi_elliptic_e(
                        (&rt * x_).atan(),
                        Atom::num(1) - &b__ * &c__ / (&a__ * &d__),
                    )
                    / (&c__
                        * &rt
                        * &second_base.sqrt()
                        * (&c__ * first_base / (&a__ * second_base)).sqrt())), x_)
        },
    ));
}

fn push_rules_rule_314(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 314,
        source: "Int[(a_+b_.*x_^2)^p_*(c_+d_.*x_^2)^q_,x_Symbol] :=
          -x*(a+b*x^2)^(p+1)*(c+d*x^2)^q/(2*a*(p+1)) +
          1/(2*a*(p+1)) \\[Star] Int[(a+b*x^2)^(p+1)*(c+d*x^2)^(q-1)*Simp[c*(2*p+3)+d*(2*(p+q+1)+1)*x^2,x],x] /;
        FreeQ[{a,b,c,d},x] && NeQ[b*c-a*d,0] && LtQ[p,-1] && LtQ[0,q,1] && IntBinomialQ[a,b,c,d,2,p,q,x]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, p_, q_, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && ltq!(p_, -1)
                && ltq!(0, q_, 1)
                && rubi_int_binomial_pair_q(
                    &a__,
                    &b__,
                    &c__,
                    &d__,
                    &Atom::num(2),
                    &p_,
                    &q_,
                    x_,
                )
        },
        rhs: {
            let first_base = &a__ + &b__ * x_.pow(2);
            let second_base = &c__ + &d__ * x_.pow(2);
            let direct = Atom::num(-1) * x_ * first_base.pow(&p_ + 1) * second_base.pow(&q_)
                / (Atom::num(2) * &a__ * (&p_ + 1));
            let payload = rubi_simp(
                &(&c__ * (Atom::num(2) * &p_ + 3)
                    + &d__ * (Atom::num(2) * (&p_ + &q_ + 1) + 1) * x_.pow(2)),
                x_,
            );
            let primitive = rubi_rhs_int(
                &(first_base.pow(&p_ + 1) * second_base.pow(&q_ - 1) * payload),
                x_,
            );
            let multiplier = Atom::num(1) / (Atom::num(2) * &a__ * (&p_ + 1));
            rubi_simp(&(direct), x_) + rubi_star(multiplier, primitive)
        },
    ));
}

fn push_rules_rule_315(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 315,
        source: "Int[(a_+b_.*x_^2)^p_*(c_+d_.*x_^2)^q_,x_Symbol] :=
          (a*d-c*b)*x*(a+b*x^2)^(p+1)*(c+d*x^2)^(q-1)/(2*a*b*(p+1)) -
          1/(2*a*b*(p+1)) \\[Star]
            Int[(a+b*x^2)^(p+1)*(c+d*x^2)^(q-2)*Simp[c*(a*d-c*b*(2*p+3))+d*(a*d*(2*(q-1)+1)-b*c*(2*(p+q)+1))*x^2,x],x] /;
        FreeQ[{a,b,c,d},x] && NeQ[b*c-a*d,0] && LtQ[p,-1] && GtQ[q,1] && IntBinomialQ[a,b,c,d,2,p,q,x]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, p_, q_, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && ltq!(p_, -1)
                && gtq!(q_, 1)
                && rubi_int_binomial_pair_q(
                    &a__,
                    &b__,
                    &c__,
                    &d__,
                    &Atom::num(2),
                    &p_,
                    &q_,
                    x_,
                )
        },
        rhs: {
            let first_base = &a__ + &b__ * x_.pow(2);
            let second_base = &c__ + &d__ * x_.pow(2);
            let direct = (&a__ * &d__ - &c__ * &b__)
                * x_
                * first_base.pow(&p_ + 1)
                * second_base.pow(&q_ - 1)
                / (Atom::num(2) * &a__ * &b__ * (&p_ + 1));
            let payload = rubi_simp(
                &(&c__ * (&a__ * &d__ - &c__ * &b__ * (Atom::num(2) * &p_ + 3))
                    + &d__
                        * (&a__ * &d__ * (Atom::num(2) * (&q_ - 1) + 1)
                            - &b__ * &c__ * (Atom::num(2) * (&p_ + &q_) + 1))
                        * x_.pow(2)),
                x_,
            );
            let primitive = rubi_rhs_int(
                &(first_base.pow(&p_ + 1) * second_base.pow(&q_ - 2) * payload),
                x_,
            );
            let multiplier = -Atom::num(1)
                / (Atom::num(2) * &a__ * &b__ * (&p_ + 1));
            rubi_simp(&(direct), x_) + rubi_star(multiplier, primitive)
        },
    ));
}

fn push_rules_rule_316(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 316,
        source: "Int[(a_+b_.*x_^2)^p_*(c_+d_.*x_^2)^q_,x_Symbol] :=
          -b*x*(a+b*x^2)^(p+1)*(c+d*x^2)^(q+1)/(2*a*(p+1)*(b*c-a*d)) +
          1/(2*a*(p+1)*(b*c-a*d)) \\[Star]
            Int[(a+b*x^2)^(p+1)*(c+d*x^2)^q*Simp[b*c+2*(p+1)*(b*c-a*d)+d*b*(2*(p+q+2)+1)*x^2,x],x] /;
        FreeQ[{a,b,c,d,q},x] && NeQ[b*c-a*d,0] && LtQ[p,-1] && Not[Not[IntegerQ[p]] && IntegerQ[q] && LtQ[q,-1]] &&
          IntBinomialQ[a,b,c,d,2,p,q,x]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, p_, q_, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__, q_],
        when: {
            freeq!([a__, b__, c__, d__, q_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && ltq!(p_, -1)
                && !(!integerq!(p_) && integerq!(q_) && ltq!(q_, -1))
                && rubi_int_binomial_pair_q(
                    &a__,
                    &b__,
                    &c__,
                    &d__,
                    &Atom::num(2),
                    &p_,
                    &q_,
                    x_,
                )
        },
        rhs: {
            let first_base = &a__ + &b__ * x_.pow(2);
            let second_base = &c__ + &d__ * x_.pow(2);
            let determinant = &b__ * &c__ - &a__ * &d__;
            let denominator = Atom::num(2) * &a__ * (&p_ + 1) * &determinant;
            let direct = -&b__
                * x_
                * first_base.pow(&p_ + 1)
                * second_base.pow(&q_ + 1)
                / &denominator;
            let payload = rubi_simp(
                &(&b__ * &c__
                    + Atom::num(2) * (&p_ + 1) * &determinant
                    + &d__
                        * &b__
                        * (Atom::num(2) * (&p_ + &q_ + 2) + 1)
                        * x_.pow(2)),
                x_,
            );
            let primitive = rubi_rhs_int(
                &(first_base.pow(&p_ + 1) * second_base.pow(&q_) * payload),
                x_,
            );
            let multiplier = Atom::num(1) / denominator;
            rubi_simp(&(direct), x_) + rubi_star(multiplier, primitive)
        },
    ));
}

fn push_rules_rule_317(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 317,
        source: "Int[(a_+b_.*x_^2)^p_*(c_+d_.*x_^2)^q_,x_Symbol] :=
          Int[ExpandIntegrand[(a+b*x^2)^p*(c+d*x^2)^q,x],x] /;
        FreeQ[{a,b,c,d},x] && NeQ[b*c-a*d,0] && IntegersQ[p,q] && GtQ[p+q,0]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, p_, q_, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && integersq!([p_, q_])
                && gtq!(&p_ + &q_, 0)
        },
        rhs: {
            let integrand = (&a__ + &b__ * x_.pow(2)).pow(&p_)
                * (&c__ + &d__ * x_.pow(2)).pow(&q_);
            let expanded = rubi_expand_integrand(&integrand, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_318(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 318,
        source: "Int[(a_+b_.*x_^2)^p_*(c_+d_.*x_^2)^q_,x_Symbol] :=
          d*x*(a+b*x^2)^(p+1)*(c+d*x^2)^(q-1)/(b*(2*(p+q)+1)) +
          1/(b*(2*(p+q)+1)) \\[Star]
            Int[(a+b*x^2)^p*(c+d*x^2)^(q-2)*Simp[c*(b*c*(2*(p+q)+1)-a*d)+d*(b*c*(2*(p+2*q-1)+1)-a*d*(2*(q-1)+1))*x^2,x],x] /;
        FreeQ[{a,b,c,d,p},x] && NeQ[b*c-a*d,0] && GtQ[q,1] && NeQ[2*(p+q)+1,0] && Not[IGtQ[p,1]] && IntBinomialQ[a,b,c,d,2,p,q,x]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, p_, q_, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__, p_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && gtq!(q_, 1)
                && neq!(Atom::num(2) * (&p_ + &q_) + 1, 0)
                && !igtq!(p_, 1)
                && rubi_int_binomial_pair_q(
                    &a__,
                    &b__,
                    &c__,
                    &d__,
                    &Atom::num(2),
                    &p_,
                    &q_,
                    x_,
                )
        },
        rhs: {
            let first_base = &a__ + &b__ * x_.pow(2);
            let second_base = &c__ + &d__ * x_.pow(2);
            let denominator = &b__ * (Atom::num(2) * (&p_ + &q_) + 1);
            let direct = &d__
                * x_
                * first_base.pow(&p_ + 1)
                * second_base.pow(&q_ - 1)
                / &denominator;
            let payload = rubi_simp(
                &(&c__
                    * (&b__ * &c__ * (Atom::num(2) * (&p_ + &q_) + 1)
                        - &a__ * &d__)
                    + &d__
                        * (&b__ * &c__ * (Atom::num(2) * (&p_ + Atom::num(2) * &q_ - 1) + 1)
                            - &a__ * &d__ * (Atom::num(2) * (&q_ - 1) + 1))
                        * x_.pow(2)),
                x_,
            );
            let primitive = rubi_rhs_int(
                &(first_base.pow(&p_) * second_base.pow(&q_ - 2) * payload),
                x_,
            );
            let multiplier = Atom::num(1) / denominator;
            rubi_simp(&(direct), x_) + rubi_star(multiplier, primitive)
        },
    ));
}

fn push_rules_rule_319(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 319,
        source: "Int[(a_+b_.*x_^2)^p_*(c_+d_.*x_^2)^q_,x_Symbol] :=
          x*(a+b*x^2)^p*(c+d*x^2)^q/(2*(p+q)+1) +
          2/(2*(p+q)+1) \\[Star] Int[(a+b*x^2)^(p-1)*(c+d*x^2)^(q-1)*Simp[a*c*(p+q)+(q*(b*c-a*d)+a*d*(p+q))*x^2,x],x] /;
        FreeQ[{a,b,c,d},x] && NeQ[b*c-a*d,0] && GtQ[q,0] && GtQ[p,0] && IntBinomialQ[a,b,c,d,2,p,q,x]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, p_, q_, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && gtq!(q_, 0)
                && gtq!(p_, 0)
                && rubi_int_binomial_pair_q(
                    &a__,
                    &b__,
                    &c__,
                    &d__,
                    &Atom::num(2),
                    &p_,
                    &q_,
                    x_,
                )
        },
        rhs: {
            let first_base = &a__ + &b__ * x_.pow(2);
            let second_base = &c__ + &d__ * x_.pow(2);
            let denominator = Atom::num(2) * (&p_ + &q_) + 1;
            let direct = x_ * first_base.pow(&p_) * second_base.pow(&q_)
                / &denominator;
            let payload = rubi_simp(
                &(&a__ * &c__ * (&p_ + &q_)
                    + (&q_ * (&b__ * &c__ - &a__ * &d__)
                        + &a__ * &d__ * (&p_ + &q_))
                        * x_.pow(2)),
                x_,
            );
            let primitive = rubi_rhs_int(
                &(first_base.pow(&p_ - 1) * second_base.pow(&q_ - 1) * payload),
                x_,
            );
            let multiplier = Atom::num(2) / denominator;
            rubi_simp(&(direct), x_) + rubi_star(multiplier, primitive)
        },
    ));
}

fn push_rules_rule_320(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 320,
        source: "Int[1/(Sqrt[a_+b_.*x_^2]*Sqrt[c_+d_.*x_^2]),x_Symbol] :=
          Sqrt[a+b*x^2]/(a*Rt[d/c,2]*Sqrt[c+d*x^2]*Sqrt[c*(a+b*x^2)/(a*(c+d*x^2))])*EllipticF[ArcTan[Rt[d/c,2]*x],1-b*c/(a*d)] /;
        FreeQ[{a,b,c,d},x] && PosQ[d/c] && PosQ[b/a] && Not[SimplerSqrtQ[b/a,d/c]]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && posq!(&d__ / &c__)
                && posq!(&b__ / &a__)
                && !rubi_simpler_sqrt_q(&(&b__ / &a__), &(&d__ / &c__))
        },
        rhs: {
            let rt = rubi_rt(&(&d__ / &c__), 2);
            let first_base = &a__ + &b__ * x_.pow(2);
            let second_base = &c__ + &d__ * x_.pow(2);
            rubi_simp(&(&first_base.sqrt()
                    * rubi_elliptic_f(
                        (&rt * x_).atan(),
                        Atom::num(1) - &b__ * &c__ / (&a__ * &d__),
                    )
                    / (&a__
                        * &rt
                        * &second_base.sqrt()
                        * (&c__ * first_base / (&a__ * second_base)).sqrt())), x_)
        },
    ));
}

fn push_rules_rule_321(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 321,
        source: "Int[1/(Sqrt[a_+b_.*x_^2]*Sqrt[c_+d_.*x_^2]),x_Symbol] :=
          1/(Sqrt[a]*Sqrt[c]*Rt[-d/c,2])*EllipticF[ArcSin[Rt[-d/c,2]*x],b*c/(a*d)] /;
        FreeQ[{a,b,c,d},x] && NegQ[d/c] && GtQ[c,0] && GtQ[a,0] && Not[NegQ[b/a] && SimplerSqrtQ[-b/a,-d/c]]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && negq!(&d__ / &c__)
                && gtq!(c__, 0)
                && gtq!(a__, 0)
                && !(negq!(&b__ / &a__)
                    && rubi_simpler_sqrt_q(&(-&b__ / &a__), &(-&d__ / &c__)))
        },
        rhs: {
            let rt = rubi_rt(&(-&d__ / &c__), 2);
            rubi_simp(&(rubi_elliptic_f(
                    (&rt * x_).asin(),
                    &b__ * &c__ / (&a__ * &d__),
                ) / (a__.sqrt() * c__.sqrt() * rt)), x_)
        },
    ));
}

fn push_rules_rule_322(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 322,
        source: "Int[1/(Sqrt[a_+b_.*x_^2]*Sqrt[c_+d_.*x_^2]),x_Symbol] :=
          -1/(Sqrt[c]*Rt[-d/c,2]*Sqrt[a-b*c/d])*EllipticF[ArcCos[Rt[-d/c,2]*x],b*c/(b*c-a*d)] /;
        FreeQ[{a,b,c,d},x] && NegQ[d/c] && GtQ[c,0] && GtQ[a-b*c/d,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && negq!(&d__ / &c__)
                && gtq!(c__, 0)
                && gtq!(&a__ - &b__ * &c__ / &d__, 0)
        },
        rhs: {
            let rt = rubi_rt(&(-&d__ / &c__), 2);
            rubi_simp(&(-rubi_elliptic_f(
                    (&rt * x_).acos(),
                    &b__ * &c__ / (&b__ * &c__ - &a__ * &d__),
                ) / (c__.sqrt() * rt * (&a__ - &b__ * &c__ / &d__).sqrt())), x_)
        },
    ));
}

fn push_rules_rule_323(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 323,
        source: "Int[1/(Sqrt[a_+b_.*x_^2]*Sqrt[c_+d_.*x_^2]),x_Symbol] :=
          Sqrt[1+d/c*x^2]/Sqrt[c+d*x^2] \\[Star] Int[1/(Sqrt[a+b*x^2]*Sqrt[1+d/c*x^2]),x] /;
        FreeQ[{a,b,c,d},x] && Not[GtQ[c,0]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: { freeq!([a__, b__, c__, d__], x_) && !gtq!(c__, 0) },
        rhs: {
            let normalized = Atom::num(1) + &d__ / &c__ * x_.pow(2);
            let primitive = rubi_rhs_int(
                &(Atom::num(1)
                    / ((&a__ + &b__ * x_.pow(2)).sqrt() * &normalized.sqrt())),
                x_,
            );
            let multiplier = normalized.sqrt() / (&c__ + &d__ * x_.pow(2)).sqrt();
            rubi_star(multiplier, primitive)
        },
    ));
}

fn push_rules_rule_324(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 324,
        source: "Int[Sqrt[a_+b_.*x_^2]/Sqrt[c_+d_.*x_^2],x_Symbol] :=
          a \\[Star] Int[1/(Sqrt[a+b*x^2]*Sqrt[c+d*x^2]),x] + b \\[Star] Int[x^2/(Sqrt[a+b*x^2]*Sqrt[c+d*x^2]),x] /;
        FreeQ[{a,b,c,d},x] && PosQ[d/c] && PosQ[b/a]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && posq!(&d__ / &c__)
                && posq!(&b__ / &a__)
        },
        rhs: {
            let denominator = (&a__ + &b__ * x_.pow(2)).sqrt()
                * (&c__ + &d__ * x_.pow(2)).sqrt();
            let first = rubi_rhs_int(&(Atom::num(1) / &denominator), x_);
            let second = rubi_rhs_int(&(x_.pow(2) / denominator), x_);
            rubi_star(a__, first) + rubi_star(b__, second)
        },
    ));
}

fn push_rules_rule_325(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 325,
        source: "Int[Sqrt[a_+b_.*x_^2]/Sqrt[c_+d_.*x_^2],x_Symbol] :=
          x*Sqrt[a+b*x^2]/Sqrt[c+d*x^2] + Sqrt[-2*a]*x/Sqrt[d*x^2]*EllipticE[ArcSin[Sqrt[2*c]/Sqrt[c+d*x^2]],1/2] /;
        FreeQ[{a,b,c,d},x] && PosQ[d/c] && EqQ[b*c+a*d,0] && LtQ[a,0] && GtQ[c,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && posq!(&d__ / &c__)
                && eqq!(&b__ * &c__ + &a__ * &d__, 0)
                && ltq!(a__, 0)
                && gtq!(c__, 0)
        },
        rhs: {
            let first_base = &a__ + &b__ * x_.pow(2);
            let second_base = &c__ + &d__ * x_.pow(2);
            rubi_simp(&(x_ * first_base.sqrt() / &second_base.sqrt()), x_)
                    + rubi_simp(&((-Atom::num(2) * &a__).sqrt()
                        * x_
                        / (&d__ * x_.pow(2)).sqrt()
                        * rubi_elliptic_e(
                            ((Atom::num(2) * &c__).sqrt() / second_base.sqrt()).asin(),
                            Atom::num(1) / 2,
                        )), x_)
        },
    ));
}

fn push_rules_rule_326(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 326,
        source: "Int[Sqrt[a_+b_.*x_^2]/Sqrt[c_+d_.*x_^2],x_Symbol] :=
          b/d \\[Star] Int[Sqrt[c+d*x^2]/Sqrt[a+b*x^2],x] - (b*c-a*d)/d \\[Star] Int[1/(Sqrt[a+b*x^2]*Sqrt[c+d*x^2]),x] /;
        FreeQ[{a,b,c,d},x] && PosQ[d/c] && NegQ[b/a]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && posq!(&d__ / &c__)
                && negq!(&b__ / &a__)
        },
        rhs: {
            let first_base = &a__ + &b__ * x_.pow(2);
            let second_base = &c__ + &d__ * x_.pow(2);
            let first = rubi_rhs_int(&(&second_base.sqrt() / &first_base.sqrt()), x_);
            let second = rubi_rhs_int(
                &(Atom::num(1) / (first_base.sqrt() * second_base.sqrt())),
                x_,
            );
            rubi_star(&b__ / &d__, first)
                    - rubi_star((&b__ * &c__ - &a__ * &d__) / &d__, second)
        },
    ));
}

fn push_rules_rule_327(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 327,
        source: "Int[Sqrt[a_+b_.*x_^2]/Sqrt[c_+d_.*x_^2],x_Symbol] :=
          Sqrt[a]/(Sqrt[c]*Rt[-d/c,2])*EllipticE[ArcSin[Rt[-d/c,2]*x],b*c/(a*d)] /;
        FreeQ[{a,b,c,d},x] && NegQ[d/c] && GtQ[c,0] && GtQ[a,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && negq!(&d__ / &c__)
                && gtq!(c__, 0)
                && gtq!(a__, 0)
        },
        rhs: {
            let rt = rubi_rt(&(-&d__ / &c__), 2);
            rubi_simp(&(a__.sqrt()
                    * rubi_elliptic_e(
                        (&rt * x_).asin(),
                        &b__ * &c__ / (&a__ * &d__),
                    ) / (c__.sqrt() * rt)), x_)
        },
    ));
}

fn push_rules_rule_328(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 328,
        source: "Int[Sqrt[a_+b_.*x_^2]/Sqrt[c_+d_.*x_^2],x_Symbol] :=
          -Sqrt[a-b*c/d]/(Sqrt[c]*Rt[-d/c,2])*EllipticE[ArcCos[Rt[-d/c,2]*x],b*c/(b*c-a*d)] /;
        FreeQ[{a,b,c,d},x] && NegQ[d/c] && GtQ[c,0] && GtQ[a-b*c/d,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && negq!(&d__ / &c__)
                && gtq!(c__, 0)
                && gtq!(&a__ - &b__ * &c__ / &d__, 0)
        },
        rhs: {
            let rt = rubi_rt(&(-&d__ / &c__), 2);
            rubi_simp(&(-(&a__ - &b__ * &c__ / &d__).sqrt()
                    * rubi_elliptic_e(
                        (&rt * x_).acos(),
                        &b__ * &c__ / (&b__ * &c__ - &a__ * &d__),
                    ) / (c__.sqrt() * rt)), x_)
        },
    ));
}

fn push_rules_rule_329(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 329,
        source: "Int[Sqrt[a_+b_.*x_^2]/Sqrt[c_+d_.*x_^2],x_Symbol] :=
          a*Sqrt[1-b^2*x^4/a^2]/(Sqrt[a+b*x^2]*Sqrt[c+d*x^2]) \\[Star] Int[Sqrt[1+b*x^2/a]/Sqrt[1-b*x^2/a],x] /;
        FreeQ[{a,b,c,d},x] && EqQ[b*c+a*d,0] && Not[LtQ[a*c,0] && GtQ[a*b,0]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && eqq!(&b__ * &c__ + &a__ * &d__, 0)
                && !(ltq!(&a__ * &c__, 0) && gtq!(&a__ * &b__, 0))
        },
        rhs: {
            let first_base = &a__ + &b__ * x_.pow(2);
            let second_base = &c__ + &d__ * x_.pow(2);
            let multiplier = &a__
                * (Atom::num(1) - b__.pow(2) * x_.pow(4) / a__.pow(2)).sqrt()
                / (first_base.sqrt() * second_base.sqrt());
            let primitive = rubi_rhs_int(
                &((Atom::num(1) + &b__ * x_.pow(2) / &a__).sqrt()
                    / (Atom::num(1) - &b__ * x_.pow(2) / &a__).sqrt()),
                x_,
            );
            rubi_star(multiplier, primitive)
        },
    ));
}

fn push_rules_rule_330(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 330,
        source: "Int[Sqrt[a_+b_.*x_^2]/Sqrt[c_+d_.*x_^2],x_Symbol] :=
          Sqrt[a+b*x^2]/Sqrt[1+b/a*x^2] \\[Star] Int[Sqrt[1+b/a*x^2]/Sqrt[c+d*x^2],x] /;
        FreeQ[{a,b,c,d},x] && NegQ[d/c] && GtQ[c,0] && Not[GtQ[a,0]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && negq!(&d__ / &c__)
                && gtq!(c__, 0)
                && !gtq!(a__, 0)
        },
        rhs: {
            let normalized = Atom::num(1) + &b__ / &a__ * x_.pow(2);
            let multiplier = (&a__ + &b__ * x_.pow(2)).sqrt() / &normalized.sqrt();
            let primitive = rubi_rhs_int(
                &(normalized.sqrt() / (&c__ + &d__ * x_.pow(2)).sqrt()),
                x_,
            );
            rubi_star(multiplier, primitive)
        },
    ));
}

fn push_rules_rule_331(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 331,
        source: "Int[Sqrt[a_+b_.*x_^2]/Sqrt[c_+d_.*x_^2],x_Symbol] :=
          Sqrt[1+d/c*x^2]/Sqrt[c+d*x^2] \\[Star] Int[Sqrt[a+b*x^2]/Sqrt[1+d/c*x^2],x] /;
        FreeQ[{a,b,c,d},x] && NegQ[d/c] && Not[GtQ[c,0]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && negq!(&d__ / &c__)
                && !gtq!(c__, 0)
        },
        rhs: {
            let normalized = Atom::num(1) + &d__ / &c__ * x_.pow(2);
            let multiplier = &normalized.sqrt() / (&c__ + &d__ * x_.pow(2)).sqrt();
            let primitive = rubi_rhs_int(
                &((&a__ + &b__ * x_.pow(2)).sqrt() / normalized.sqrt()),
                x_,
            );
            rubi_star(multiplier, primitive)
        },
    ));
}

fn push_rules_rule_332(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 332,
        source: "Int[(a_+b_.*x_^2)^p_.*(c_+d_.*x_^2)^q_,x_Symbol] :=
          Int[ExpandIntegrand[(a+b*x^2)^p*(c+d*x^2)^q,x],x] /;
        FreeQ[{a,b,c,d,q},x] && NeQ[b*c-a*d,0] && IGtQ[p,0]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, p_, q_, x_],
        optional: [b__, d__, p_],
        x_free: [a__, b__, c__, d__, q_],
        when: {
            freeq!([a__, b__, c__, d__, q_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && igtq!(p_, 0)
        },
        rhs: {
            let integrand = (&a__ + &b__ * x_.pow(2)).pow(&p_)
                * (&c__ + &d__ * x_.pow(2)).pow(&q_);
            let expanded = rubi_expand_integrand(&integrand, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_333(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 333,
        source: "Int[(a_+b_.*x_^2)^p_*(c_+d_.*x_^2)^q_,x_Symbol] :=
          a^p*c^q*x*AppellF1[1/2,-p,-q,3/2,-b*x^2/a,-d*x^2/c] /;
        FreeQ[{a,b,c,d,p,q},x] && NeQ[b*c-a*d,0] && (IntegerQ[p] || GtQ[a,0]) && (IntegerQ[q] || GtQ[c,0])",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, p_, q_, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__, p_, q_],
        when: {
            freeq!([a__, b__, c__, d__, p_, q_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && (integerq!(p_) || gtq!(a__, 0))
                && (integerq!(q_) || gtq!(c__, 0))
        },
        rhs: {
            rubi_simp(&(a__.pow(&p_)
                    * c__.pow(&q_)
                    * x_
                    * rubi_appell_f1(
                        Atom::num(1) / 2,
                        -&p_,
                        -&q_,
                        Atom::num(3) / 2,
                        -&b__ * x_.pow(2) / &a__,
                        -&d__ * x_.pow(2) / &c__,
                    )), x_)
        },
    ));
}

fn push_rules_rule_334(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 334,
        source: "Int[(a_+b_.*x_^2)^p_*(c_+d_.*x_^2)^q_,x_Symbol] :=
          a^IntPart[p]*(a+b*x^2)^FracPart[p]/(1+b*x^2/a)^FracPart[p] \\[Star] Int[(1+b*x^2/a)^p*(c+d*x^2)^q,x] /;
        FreeQ[{a,b,c,d,p,q},x] && NeQ[b*c-a*d,0] && Not[IntegerQ[p] || GtQ[a,0]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, p_, q_, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__, p_, q_],
        when: {
            freeq!([a__, b__, c__, d__, p_, q_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && !(integerq!(p_) || gtq!(a__, 0))
        },
        rhs: {
            let first_base = &a__ + &b__ * x_.pow(2);
            let normalized = Atom::num(1) + &b__ * x_.pow(2) / &a__;
            let multiplier = a__.pow(rubi_int_part(&p_))
                * first_base.pow(rubi_frac_part(&p_))
                / normalized.pow(rubi_frac_part(&p_));
            let primitive = rubi_rhs_int(
                &(normalized.pow(&p_) * (&c__ + &d__ * x_.pow(2)).pow(&q_)),
                x_,
            );
            rubi_star(multiplier, primitive)
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
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (a__ + b__ * x_.pow(2)).pow(p_) * (c__ + d__ * x_.pow(2))
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (a__ + b__ * x_.pow(2)).pow(p_) * (c__ + d__ * x_.pow(2)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_2(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let p_ = symbols.p_;
    let q_ = symbols.q_;
    let x_ = symbols.x_;
    (a__ + b__ * x_.pow(2)).pow(p_) * (c__ + d__ * x_.pow(2)).pow(q_)
}

#[inline(never)]
fn rubi_shared_pattern_3(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (a__ + b__ * x_.pow(2)).pow(p_) / (c__ + d__ * x_.pow(2))
}

#[inline(never)]
fn rubi_shared_pattern_4(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let x_ = symbols.x_;
    (a__ + b__ * x_.pow(2)).sqrt() / (c__ + d__ * x_.pow(2)).sqrt()
}

#[inline(never)]
fn rubi_shared_pattern_5(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let x_ = symbols.x_;
    Atom::num(1) / ((a__ + b__ * x_.pow(2)).pow((1, 3)) * (c__ + d__ * x_.pow(2)))
}

#[inline(never)]
fn rubi_shared_pattern_6(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let x_ = symbols.x_;
    Atom::num(1) / ((a__ + b__ * x_.pow(2)).pow((1, 4)) * (c__ + d__ * x_.pow(2)))
}

#[inline(never)]
fn rubi_shared_pattern_7(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let x_ = symbols.x_;
    Atom::num(1) / ((a__ + b__ * x_.pow(2)).pow((3, 4)) * (c__ + d__ * x_.pow(2)))
}

#[inline(never)]
fn rubi_shared_pattern_8(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let x_ = symbols.x_;
    Atom::num(1) / ((a__ + b__ * x_.pow(2)).sqrt() * (c__ + d__ * x_.pow(2)).sqrt())
}

#[inline(never)]
fn rubi_shared_pattern_9(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let q_ = symbols.q_;
    let u__ = symbols.u__;
    let x_ = symbols.x_;
    u__ * (a__ + b__ * x_.pow(n_)).pow(p_) * (c__ + d__ * x_.pow(n_)).pow(q_)
}
