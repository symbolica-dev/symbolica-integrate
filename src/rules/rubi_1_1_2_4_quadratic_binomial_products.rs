use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_335(rules);
    push_rules_rule_336(rules);
    push_rules_rule_337(rules);
    push_rules_rule_338(rules);
    push_rules_rule_339(rules);
    push_rules_rule_340(rules);
    push_rules_rule_341(rules);
    push_rules_rule_342(rules);
    push_rules_rule_343(rules);
    push_rules_rule_344(rules);
    push_rules_rule_345(rules);
    push_rules_rule_346(rules);
    push_rules_rule_347(rules);
    push_rules_rule_348(rules);
    push_rules_rule_349(rules);
    push_rules_rule_350(rules);
    push_rules_rule_351(rules);
    push_rules_rule_352(rules);
    push_rules_rule_353(rules);
    push_rules_rule_354(rules);
    push_rules_rule_355(rules);
    push_rules_rule_356(rules);
    push_rules_rule_357(rules);
    push_rules_rule_358(rules);
    push_rules_rule_359(rules);
    push_rules_rule_360(rules);
    push_rules_rule_361(rules);
    push_rules_rule_362(rules);
    push_rules_rule_363(rules);
    push_rules_rule_364(rules);
    push_rules_rule_365(rules);
    push_rules_rule_366(rules);
    push_rules_rule_367(rules);
    push_rules_rule_368(rules);
    push_rules_rule_369(rules);
    push_rules_rule_370(rules);
    push_rules_rule_371(rules);
    push_rules_rule_372(rules);
    push_rules_rule_373(rules);
    push_rules_rule_374(rules);
    push_rules_rule_375(rules);
    push_rules_rule_376(rules);
    push_rules_rule_377(rules);
    push_rules_rule_378(rules);
    push_rules_rule_379(rules);
    push_rules_rule_380(rules);
    push_rules_rule_381(rules);
    push_rules_rule_382(rules);
    push_rules_rule_383(rules);
    push_rules_rule_384(rules);
    push_rules_rule_385(rules);
    push_rules_rule_386(rules);
    push_rules_rule_387(rules);
    push_rules_rule_388(rules);
    push_rules_rule_389(rules);
    push_rules_rule_390(rules);
    push_rules_rule_391(rules);
    push_rules_rule_392(rules);
    push_rules_rule_393(rules);
    push_rules_rule_394(rules);
    push_rules_rule_395(rules);
}

fn push_rules_rule_335(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 335,
        source: "Int[(e_.*x_)^m_.*(a_+b_.*x_^2)^p_.*(c_+d_.*x_^2)^p_.,x_Symbol] :=
          Int[(e*x)^m*(a*c+b*d*x^4)^p,x] /;
        FreeQ[{a,b,c,d,e,m,p},x] && EqQ[b*c+a*d,0] && (IntegerQ[p] || GtQ[a,0] && GtQ[c,0])",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, e__, m_, p_, x_],
        optional: [b__, d__, e__, m_, p_],
        x_free: [a__, b__, c__, d__, e__, m_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, p_], x_)
                && eqq!(&b__ * &c__ + &a__ * &d__, 0)
                && (integerq!(p_) || gtq!(a__, 0) && gtq!(c__, 0))
        },
        rhs: {
            rubi_rhs_int(
                &((&e__ * x_).pow(&m_)
                    * (&a__ * &c__ + &b__ * &d__ * x_.pow(4)).pow(&p_)),
                x_,
            )
        },
    ));
}

fn push_rules_rule_336(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, p_, x_);
    rules.push(rubi_rule!(
        order: 336,
        source: "Int[x_^3*(a_+b_.*x_^2)^p_*(c_+d_.*x_^2)^p_,x_Symbol] :=
          (a+b*x^2)^(p+1)*(c+d*x^2)^(p+1)/(4*b*d*(p+1)) /;
        FreeQ[{a,b,c,d,p},x] && EqQ[b*c+a*d,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: x_.pow(3) * (a__ + b__ * x_.pow(2)).pow(p_) * (c__ + d__ * x_.pow(2)).pow(p_),
        with: [a__, b__, c__, d__, p_, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__, p_], x_) && eqq!(&b__ * &c__ + &a__ * &d__, 0)
        },
        rhs: {
            rubi_simp(&((&a__ + &b__ * x_.pow(2)).pow(&p_ + 1)
                    * (&c__ + &d__ * x_.pow(2)).pow(&p_ + 1)
                    / (Atom::num(4) * &b__ * &d__ * (&p_ + 1))), x_)
        },
    ));
}

fn push_rules_rule_337(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 337,
        source: "Int[(e_.*x_)^m_.*(a_+b_.*x_^2)^p_*(c_+d_.*x_^2)^p_,x_Symbol] :=
          -(e*x)^(m+1)*(a+b*x^2)^(p+1)*(c+d*x^2)^(p+1)/(4*a*c*e*(p+1)) /;
        FreeQ[{a,b,c,d,e,m,p},x] && EqQ[b*c+a*d,0] && EqQ[m+4*p+5,0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, e__, m_, p_, x_],
        optional: [b__, d__, e__, m_],
        x_free: [a__, b__, c__, d__, e__, m_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, p_], x_)
                && eqq!(&b__ * &c__ + &a__ * &d__, 0)
                && eqq!(&m_ + Atom::num(4) * &p_ + 5, 0)
        },
        rhs: {
            rubi_simp(&(-(&e__ * x_).pow(&m_ + 1)
                    * (&a__ + &b__ * x_.pow(2)).pow(&p_ + 1)
                    * (&c__ + &d__ * x_.pow(2)).pow(&p_ + 1)
                    / (Atom::num(4) * &a__ * &c__ * &e__ * (&p_ + 1))), x_)
        },
    ));
}

fn push_rules_rule_338(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 338,
        source: "Int[x_^m_.*(a_+b_.*x_^2)^p_*(c_+d_.*x_^2)^p_,x_Symbol] :=
          1/2 \\[Star] Subst[Int[x^((m-1)/2)*(a+b*x)^p*(c+d*x)^p,x],x,x^2] /;
        FreeQ[{a,b,c,d,p},x] && EqQ[b*c+a*d,0] && IntegerQ[(m-1)/2]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern: x_.pow(m_) * (a__ + b__ * x_.pow(2)).pow(p_) * (c__ + d__ * x_.pow(2)).pow(p_),
        with: [a__, b__, c__, d__, m_, p_, x_],
        optional: [b__, d__, m_],
        x_free: [a__, b__, c__, d__, p_],
        when: {
            freeq!([a__, b__, c__, d__, p_], x_)
                && eqq!(&b__ * &c__ + &a__ * &d__, 0)
                && integerq!((&m_ - 1) / 2)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let primitive = rubi_rhs_int(
                &(sub_atom.pow((&m_ - 1) / 2)
                    * (&a__ + &b__ * &sub_atom).pow(&p_)
                    * (&c__ + &d__ * &sub_atom).pow(&p_)),
                sub,
            );
            let substituted = rubi_subst(&primitive, sub, x_.pow(2));
            rubi_star(Atom::num(1) / 2, substituted)
        },
    ));
}

fn push_rules_rule_339(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 339,
        source: "Int[(e_.*x_)^m_*(a_+b_.*x_^2)^p_*(c_+d_.*x_^2)^p_,x_Symbol] :=
          (e*x)^(m+1)*(a+b*x^2)^p*(c+d*x^2)^p/(e*(m+1)) -
          4*b*d*p/(e^4*(m+1)) \\[Star] Int[(e*x)^(m+4)*(a+b*x^2)^(p-1)*(c+d*x^2)^(p-1),x] /;
        FreeQ[{a,b,c,d,e,m},x] && EqQ[b*c+a*d,0] && GtQ[p,0] && LtQ[m,-1]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, e__, m_, p_, x_],
        optional: [b__, d__, e__],
        x_free: [a__, b__, c__, d__, e__, m_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_], x_)
                && eqq!(&b__ * &c__ + &a__ * &d__, 0)
                && gtq!(p_, 0)
                && ltq!(m_, -1)
        },
        rhs: {
            let first_base = &a__ + &b__ * x_.pow(2);
            let second_base = &c__ + &d__ * x_.pow(2);
            let direct = (&e__ * x_).pow(&m_ + 1)
                * first_base.pow(&p_)
                * second_base.pow(&p_)
                / (&e__ * (&m_ + 1));
            let primitive = rubi_rhs_int(
                &((&e__ * x_).pow(&m_ + 4)
                    * first_base.pow(&p_ - 1)
                    * second_base.pow(&p_ - 1)),
                x_,
            );
            let multiplier = Atom::num(4) * &b__ * &d__ * &p_ / (e__.pow(4) * (&m_ + 1));
            rubi_simp(&(direct), x_) - rubi_star(multiplier, primitive)
        },
    ));
}

fn push_rules_rule_340(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 340,
        source: "Int[(e_.*x_)^m_.*(a_+b_.*x_^2)^p_*(c_+d_.*x_^2)^p_,x_Symbol] :=
          (e*x)^(m+1)*(a+b*x^2)^p*(c+d*x^2)^p/(e*(m+4*p+1)) +
          4*a*c*p/(m+4*p+1) \\[Star] Int[(e*x)^m*(a+b*x^2)^(p-1)*(c+d*x^2)^(p-1),x] /;
        FreeQ[{a,b,c,d,e,m},x] && EqQ[b*c+a*d,0] && GtQ[p,0] && NeQ[m+4*p+1,0] && IntegerQ[2*m]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, e__, m_, p_, x_],
        optional: [b__, d__, e__, m_],
        x_free: [a__, b__, c__, d__, e__, m_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_], x_)
                && eqq!(&b__ * &c__ + &a__ * &d__, 0)
                && gtq!(p_, 0)
                && neq!(&m_ + Atom::num(4) * &p_ + 1, 0)
                && integerq!(Atom::num(2) * &m_)
        },
        rhs: {
            let first_base = &a__ + &b__ * x_.pow(2);
            let second_base = &c__ + &d__ * x_.pow(2);
            let denominator = &m_ + Atom::num(4) * &p_ + 1;
            let direct = (&e__ * x_).pow(&m_ + 1)
                * first_base.pow(&p_)
                * second_base.pow(&p_)
                / (&e__ * &denominator);
            let primitive = rubi_rhs_int(
                &((&e__ * x_).pow(&m_)
                    * first_base.pow(&p_ - 1)
                    * second_base.pow(&p_ - 1)),
                x_,
            );
            let multiplier = Atom::num(4) * &a__ * &c__ * &p_ / denominator;
            rubi_simp(&(direct), x_) + rubi_star(multiplier, primitive)
        },
    ));
}

fn push_rules_rule_341(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 341,
        source: "Int[(e_.*x_)^m_*(a_+b_.*x_^2)^p_*(c_+d_.*x_^2)^p_,x_Symbol] :=
          e^3*(e*x)^(m-3)*(a+b*x^2)^(p+1)*(c+d*x^2)^(p+1)/(4*b*d*(p+1)) -
          e^4*(m-3)/(4*b*d*(p+1)) \\[Star] Int[(e*x)^(m-4)*(a+b*x^2)^(p+1)*(c+d*x^2)^(p+1),x] /;
        FreeQ[{a,b,c,d,e,m},x] && EqQ[b*c+a*d,0] && LtQ[p,-1] && GtQ[m,3]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, e__, m_, p_, x_],
        optional: [b__, d__, e__],
        x_free: [a__, b__, c__, d__, e__, m_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_], x_)
                && eqq!(&b__ * &c__ + &a__ * &d__, 0)
                && ltq!(p_, -1)
                && gtq!(m_, 3)
        },
        rhs: {
            let first_base = &a__ + &b__ * x_.pow(2);
            let second_base = &c__ + &d__ * x_.pow(2);
            let denominator = Atom::num(4) * &b__ * &d__ * (&p_ + 1);
            let direct = e__.pow(3)
                * (&e__ * x_).pow(&m_ - 3)
                * first_base.pow(&p_ + 1)
                * second_base.pow(&p_ + 1)
                / &denominator;
            let primitive = rubi_rhs_int(
                &((&e__ * x_).pow(&m_ - 4)
                    * first_base.pow(&p_ + 1)
                    * second_base.pow(&p_ + 1)),
                x_,
            );
            let multiplier = e__.pow(4) * (&m_ - 3) / denominator;
            rubi_simp(&(direct), x_) - rubi_star(multiplier, primitive)
        },
    ));
}

fn push_rules_rule_342(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 342,
        source: "Int[(e_.*x_)^m_.*(a_+b_.*x_^2)^p_*(c_+d_.*x_^2)^p_,x_Symbol] :=
          -(e*x)^(m+1)*(a+b*x^2)^(p+1)*(c+d*x^2)^(p+1)/(4*a*c*e*(p+1)) +
          (m+4*p+5)/(4*a*c*(p+1)) \\[Star] Int[(e*x)^m*(a+b*x^2)^(p+1)*(c+d*x^2)^(p+1),x] /;
        FreeQ[{a,b,c,d,e,m},x] && EqQ[b*c+a*d,0] && LtQ[p,-1] && IntegerQ[2*m]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, e__, m_, p_, x_],
        optional: [b__, d__, e__, m_],
        x_free: [a__, b__, c__, d__, e__, m_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_], x_)
                && eqq!(&b__ * &c__ + &a__ * &d__, 0)
                && ltq!(p_, -1)
                && integerq!(Atom::num(2) * &m_)
        },
        rhs: {
            let first_base = &a__ + &b__ * x_.pow(2);
            let second_base = &c__ + &d__ * x_.pow(2);
            let denominator = Atom::num(4) * &a__ * &c__ * (&p_ + 1);
            let direct = -(&e__ * x_).pow(&m_ + 1)
                * first_base.pow(&p_ + 1)
                * second_base.pow(&p_ + 1)
                / (&e__ * &denominator);
            let primitive = rubi_rhs_int(
                &((&e__ * x_).pow(&m_)
                    * first_base.pow(&p_ + 1)
                    * second_base.pow(&p_ + 1)),
                x_,
            );
            let multiplier = (&m_ + Atom::num(4) * &p_ + 5) / denominator;
            rubi_simp(&(direct), x_) + rubi_star(multiplier, primitive)
        },
    ));
}

fn push_rules_rule_343(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 343,
        source: "Int[(e_.*x_)^m_*(a_+b_.*x_^2)^p_*(c_+d_.*x_^2)^p_,x_Symbol] :=
          (e*x)^(m+1)*(a+b*x^2)^(p+1)*(c+d*x^2)^(p+1)/(a*c*e*(m+1)) -
          b*d*(m+4*p+5)/(a*c*e^4*(m+1)) \\[Star] Int[(e*x)^(m+4)*(a+b*x^2)^p*(c+d*x^2)^p,x] /;
        FreeQ[{a,b,c,d,e,p},x] && EqQ[b*c+a*d,0] && LtQ[m,-1]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, e__, m_, p_, x_],
        optional: [b__, d__, e__],
        x_free: [a__, b__, c__, d__, e__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, p_], x_)
                && eqq!(&b__ * &c__ + &a__ * &d__, 0)
                && ltq!(m_, -1)
        },
        rhs: {
            let first_base = &a__ + &b__ * x_.pow(2);
            let second_base = &c__ + &d__ * x_.pow(2);
            let direct = (&e__ * x_).pow(&m_ + 1)
                * first_base.pow(&p_ + 1)
                * second_base.pow(&p_ + 1)
                / (&a__ * &c__ * &e__ * (&m_ + 1));
            let primitive = rubi_rhs_int(
                &((&e__ * x_).pow(&m_ + 4)
                    * first_base.pow(&p_)
                    * second_base.pow(&p_)),
                x_,
            );
            let multiplier = &b__ * &d__ * (&m_ + Atom::num(4) * &p_ + 5)
                / (&a__ * &c__ * e__.pow(4) * (&m_ + 1));
            rubi_simp(&(direct), x_) - rubi_star(multiplier, primitive)
        },
    ));
}

fn push_rules_rule_344(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 344,
        source: "Int[(e_.*x_)^m_.*(a_+b_.*x_^2)^p_*(c_+d_.*x_^2)^p_,x_Symbol] :=
          (a+b*x^2)^FracPart[p]*(c+d*x^2)^FracPart[p]/(a*c+b*d*x^4)^FracPart[p] \\[Star] Int[(e*x)^m*(a*c+b*d*x^4)^p,x] /;
        FreeQ[{a,b,c,d,e,m,p},x] && EqQ[b*c+a*d,0] && Not[IntegerQ[p]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, e__, m_, p_, x_],
        optional: [b__, d__, e__, m_],
        x_free: [a__, b__, c__, d__, e__, m_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, p_], x_)
                && eqq!(&b__ * &c__ + &a__ * &d__, 0)
                && !integerq!(p_)
        },
        rhs: {
            let multiplier = (&a__ + &b__ * x_.pow(2)).pow(rubi_frac_part(&p_))
                * (&c__ + &d__ * x_.pow(2)).pow(rubi_frac_part(&p_))
                / (&a__ * &c__ + &b__ * &d__ * x_.pow(4)).pow(rubi_frac_part(&p_));
            let primitive = rubi_rhs_int(
                &((&e__ * x_).pow(&m_)
                    * (&a__ * &c__ + &b__ * &d__ * x_.pow(4)).pow(&p_)),
                x_,
            );
            rubi_star(multiplier, primitive)
        },
    ));
}

fn push_rules_rule_345(rules: &mut Vec<RubiRule>) {
    rubi_symb!(b__, c__, d__, m_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 345,
        source: "Int[x_^m_.*(b_.*x_^2)^p_*(c_+d_.*x_^2)^q_.,x_Symbol] :=
          1/(2*b^((m-1)/2)) \\[Star] Subst[Int[(b*x)^(p+(m-1)/2)*(c+d*x)^q,x],x,x^2] /;
        FreeQ[{b,c,d,m,p,q},x] && IntegerQ[(m-1)/2]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern: x_.pow(m_) * (b__ * x_.pow(2)).pow(p_) * (c__ + d__ * x_.pow(2)).pow(q_),
        with: [b__, c__, d__, m_, p_, q_, x_],
        optional: [b__, d__, m_, q_],
        x_free: [b__, c__, d__, m_, p_, q_],
        when: {
            freeq!([b__, c__, d__, m_, p_, q_], x_) && integerq!((&m_ - 1) / 2)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let primitive = rubi_rhs_int(
                &((&b__ * &sub_atom).pow(&p_ + (&m_ - 1) / 2)
                    * (&c__ + &d__ * &sub_atom).pow(&q_)),
                sub,
            );
            let substituted = rubi_subst(&primitive, sub, x_.pow(2));
            let multiplier = Atom::num(1) / (Atom::num(2) * b__.pow((&m_ - 1) / 2));
            rubi_star(multiplier, substituted)
        },
    ));
}

fn push_rules_rule_346(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; b__, c__, d__, e__, m_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 346,
        source: "Int[(e_.*x_)^m_.*(b_.*x_^2.)^p_*(c_+d_.*x_^2)^q_.,x_Symbol] :=
          e^m*b^IntPart[p]*(b*x^2)^FracPart[p]/x^(2*FracPart[p]) \\[Star] Int[x^(m+2*p)*(c+d*x^2)^q,x] /;
        FreeQ[{b,c,d,e,m,p,q},x] && (IntegerQ[m] || GtQ[e,0])",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [b__, c__, d__, e__, m_, p_, q_, x_],
        optional: [b__, d__, e__, m_, q_],
        x_free: [b__, c__, d__, e__, m_, p_, q_],
        when: {
            freeq!([b__, c__, d__, e__, m_, p_, q_], x_)
                && (integerq!(m_) || gtq!(e__, 0))
        },
        rhs: {
            let multiplier = e__.pow(&m_)
                * b__.pow(rubi_int_part(&p_))
                * (&b__ * x_.pow(2)).pow(rubi_frac_part(&p_))
                / x_.pow(Atom::num(2) * rubi_frac_part(&p_));
            let primitive = rubi_rhs_int(
                &(x_.pow(&m_ + Atom::num(2) * &p_)
                    * (&c__ + &d__ * x_.pow(2)).pow(&q_)),
                x_,
            );
            rubi_star(multiplier, primitive)
        },
    ));
}

fn push_rules_rule_347(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; b__, c__, d__, e__, m_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 347,
        source: "Int[(e_*x_)^m_*(b_.*x_^2.)^p_*(c_+d_.*x_^2)^q_.,x_Symbol] :=
          e^IntPart[m]*(e*x)^FracPart[m]/x^FracPart[m] \\[Star] Int[x^m*(b*x^2)^p*(c+d*x^2)^q,x] /;
        FreeQ[{b,c,d,e,m,p,q},x] && Not[IntegerQ[m]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [b__, c__, d__, e__, m_, p_, q_, x_],
        optional: [b__, d__, q_],
        x_free: [b__, c__, d__, e__, m_, p_, q_],
        when: {
            freeq!([b__, c__, d__, e__, m_, p_, q_], x_) && !integerq!(m_)
        },
        rhs: {
            let multiplier = e__.pow(rubi_int_part(&m_))
                * (&e__ * x_).pow(rubi_frac_part(&m_))
                / x_.pow(rubi_frac_part(&m_));
            let primitive = rubi_rhs_int(
                &(x_.pow(&m_)
                    * (&b__ * x_.pow(2)).pow(&p_)
                    * (&c__ + &d__ * x_.pow(2)).pow(&q_)),
                x_,
            );
            rubi_star(multiplier, primitive)
        },
    ));
}

fn push_rules_rule_348(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 348,
        source: "Int[x_/((a_+b_.*x_^2)^(1/4)*(c_+d_.*x_^2)),x_Symbol] :=
          -1/(Sqrt[2]*Rt[a,4]*d)*ArcTan[(Rt[a,4]^2-Sqrt[a+b*x^2])/(Sqrt[2]*Rt[a,4]*(a+b*x^2)^(1/4))] -
          1/(Sqrt[2]*Rt[a,4]*d)*ArcTanh[(Rt[a,4]^2+Sqrt[a+b*x^2])/(Sqrt[2]*Rt[a,4]*(a+b*x^2)^(1/4))] /;
        FreeQ[{a,b,c,d},x] && EqQ[b*c-2*a*d,0] && PosQ[a]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern: x_ / ((a__ + b__ * x_.pow(2)).pow((1, 4)) * (c__ + d__ * x_.pow(2))),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && eqq!(&b__ * &c__ - Atom::num(2) * &a__ * &d__, 0)
                && posq!(a__)
        },
        rhs: {
            let sqrt_two = Atom::num(2).sqrt();
            let base = &a__ + &b__ * x_.pow(2);
            let rt = rubi_rt(&a__, 4);
            let denominator = &sqrt_two * &rt * &d__;
            rubi_simp(&(-((&rt.pow(2) - base.sqrt()) / (&sqrt_two * &rt * base.pow((1, 4)))).atan()
                    / &denominator), x_)
                    - rubi_simp(&(((&rt.pow(2) + base.sqrt()) / (&sqrt_two * &rt * base.pow((1, 4)))).atanh()
                        / denominator), x_)
        },
    ));
}

fn push_rules_rule_349(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, x_);
    rules.push(rubi_rule!(
        order: 349,
        source: "Int[x_^m_/((a_+b_.*x_^2)^(1/4)*(c_+d_.*x_^2)),x_Symbol] :=
          Int[ExpandIntegrand[x^m/((a+b*x^2)^(1/4)*(c+d*x^2)),x],x] /;
        FreeQ[{a,b,c,d},x] && EqQ[b*c-2*a*d,0] && IntegerQ[m] && (PosQ[a] || IntegerQ[m/2])",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern: x_.pow(m_) / ((a__ + b__ * x_.pow(2)).pow((1, 4)) * (c__ + d__ * x_.pow(2))),
        with: [a__, b__, c__, d__, m_, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && eqq!(&b__ * &c__ - Atom::num(2) * &a__ * &d__, 0)
                && integerq!(m_)
                && (posq!(a__) || integerq!(&m_ / 2))
        },
        rhs: {
            let integrand = x_.pow(&m_)
                / ((&a__ + &b__ * x_.pow(2)).pow((1, 4))
                    * (&c__ + &d__ * x_.pow(2)));
            let expanded = rubi_expand_integrand(&integrand, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_350(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 350,
        source: "Int[x_^2/((a_+b_.*x_^2)^(3/4)*(c_+d_.*x_^2)),x_Symbol] :=
          -b/(a*d*Rt[b^2/a,4]^3)*ArcTan[(b+Rt[b^2/a,4]^2*Sqrt[a+b*x^2])/(Rt[b^2/a,4]^3*x*(a+b*x^2)^(1/4))] +
          b/(a*d*Rt[b^2/a,4]^3)*ArcTanh[(b-Rt[b^2/a,4]^2*Sqrt[a+b*x^2])/(Rt[b^2/a,4]^3*x*(a+b*x^2)^(1/4))] /;
        FreeQ[{a,b,c,d},x] && EqQ[b*c-2*a*d,0] && PosQ[b^2/a]",
        desc: "Apply the direct antiderivative formula.",
        refs: ["Enestr\\[ODoubleDot]m index number E688 in The Euler Archive"],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && eqq!(&b__ * &c__ - Atom::num(2) * &a__ * &d__, 0)
                && posq!(b__.pow(2) / &a__)
        },
        rhs: {
            let base = &a__ + &b__ * x_.pow(2);
            let rt = rubi_rt(&(b__.pow(2) / &a__), 4);
            let denominator = &a__ * &d__ * rt.pow(3);
            let argument_denominator = rt.pow(3) * x_ * base.pow((1, 4));
            rubi_simp(&(-&b__ * ((&b__ + rt.pow(2) * base.sqrt()) / &argument_denominator).atan()
                    / &denominator), x_)
                    + rubi_simp(&(&b__ * ((&b__ - rt.pow(2) * base.sqrt()) / argument_denominator).atanh()
                        / denominator), x_)
        },
    ));
}

fn push_rules_rule_351(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 351,
        source: "Int[x_^2/((a_+b_.*x_^2)^(3/4)*(c_+d_.*x_^2)),x_Symbol] :=
          -b/(Sqrt[2]*a*d*Rt[-b^2/a,4]^3)*ArcTan[(Rt[-b^2/a,4]*x)/(Sqrt[2]*(a+b*x^2)^(1/4))] +
          b/(Sqrt[2]*a*d*Rt[-b^2/a,4]^3)*ArcTanh[(Rt[-b^2/a,4]*x)/(Sqrt[2]*(a+b*x^2)^(1/4))] /;
        FreeQ[{a,b,c,d},x] && EqQ[b*c-2*a*d,0] && NegQ[b^2/a]",
        desc: "Integration by substitution",
        refs: ["Enestr\\[ODoubleDot]m index number E688 in The Euler Archive"],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && eqq!(&b__ * &c__ - Atom::num(2) * &a__ * &d__, 0)
                && negq!(b__.pow(2) / &a__)
        },
        rhs: {
            let sqrt_two = Atom::num(2).sqrt();
            let base = &a__ + &b__ * x_.pow(2);
            let rt = rubi_rt(&(-b__.pow(2) / &a__), 4);
            let denominator = &sqrt_two * &a__ * &d__ * rt.pow(3);
            let argument = &rt * x_ / (&sqrt_two * base.pow((1, 4)));
            rubi_simp(&(-&b__ * argument.atan() / &denominator), x_) + rubi_simp(&(&b__ * argument.atanh() / denominator), x_)
        },
    ));
}

fn push_rules_rule_352(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, x_);
    rules.push(rubi_rule!(
        order: 352,
        source: "Int[x_^m_/((a_+b_.*x_^2)^(3/4)*(c_+d_.*x_^2)),x_Symbol] :=
          Int[ExpandIntegrand[x^m/((a+b*x^2)^(3/4)*(c+d*x^2)),x],x] /;
        FreeQ[{a,b,c,d},x] && EqQ[b*c-2*a*d,0] && IntegerQ[m] && (PosQ[a] || IntegerQ[m/2])",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern: x_.pow(m_) / ((a__ + b__ * x_.pow(2)).pow((3, 4)) * (c__ + d__ * x_.pow(2))),
        with: [a__, b__, c__, d__, m_, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && eqq!(&b__ * &c__ - Atom::num(2) * &a__ * &d__, 0)
                && integerq!(m_)
                && (posq!(a__) || integerq!(&m_ / 2))
        },
        rhs: {
            let integrand = x_.pow(&m_)
                / ((&a__ + &b__ * x_.pow(2)).pow((3, 4))
                    * (&c__ + &d__ * x_.pow(2)));
            let expanded = rubi_expand_integrand(&integrand, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_353(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, p_, q_, x_);
    let rule = rubi_rule!(
        order: 353,
        source: "Int[x_*(a_+b_.*x_^2)^p_.*(c_+d_.*x_^2)^q_.,x_Symbol] :=
          1/2 \\[Star] Subst[Int[(a+b*x)^p*(c+d*x)^q,x],x,x^2] /;
        FreeQ[{a,b,c,d,p,q},x] && NeQ[b*c-a*d,0]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern: x_ * (a__ + b__ * x_.pow(2)).pow(p_) * (c__ + d__ * x_.pow(2)).pow(q_),
        with: [a__, b__, c__, d__, p_, q_, x_],
        optional: [b__, d__, p_, q_],
        x_free: [a__, b__, c__, d__, p_, q_],
        when: {
            freeq!([a__, b__, c__, d__, p_, q_], x_) && neq!(&b__ * &c__ - &a__ * &d__, 0)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let primitive = rubi_rhs_int(
                &((&a__ + &b__ * &sub_atom).pow(&p_)
                    * (&c__ + &d__ * &sub_atom).pow(&q_)),
                sub,
            );
            let substituted = rubi_subst(&primitive, sub, x_.pow(2));
            rubi_star(Atom::num(1) / 2, substituted)
        },
    );
    rules.push(rule.with_repeated_proper_x_dependent_subexpression());
}

fn push_rules_rule_354(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, p_, q_, x_);
    let rule = rubi_rule!(
        order: 354,
        source: "Int[x_^m_.*(a_+b_.*x_^2)^p_.*(c_+d_.*x_^2)^q_.,x_Symbol] :=
          1/2 \\[Star] Subst[Int[x^((m-1)/2)*(a+b*x)^p*(c+d*x)^q,x],x,x^2] /;
        FreeQ[{a,b,c,d,p,q},x] && NeQ[b*c-a*d,0] && IntegerQ[(m-1)/2]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_10(symbols),
        with: [a__, b__, c__, d__, m_, p_, q_, x_],
        optional: [b__, d__, m_, p_, q_],
        x_free: [a__, b__, c__, d__, p_, q_],
        when: {
            freeq!([a__, b__, c__, d__, p_, q_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && integerq!((&m_ - 1) / 2)
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let primitive = rubi_rhs_int(
                &(sub_atom.pow((&m_ - 1) / 2)
                    * (&a__ + &b__ * &sub_atom).pow(&p_)
                    * (&c__ + &d__ * &sub_atom).pow(&q_)),
                sub,
            );
            let substituted = rubi_subst(&primitive, sub, x_.pow(2));
            rubi_star(Atom::num(1) / 2, substituted)
        },
    );
    rules.push(rule.with_repeated_proper_x_dependent_subexpression());
}

fn push_rules_rule_355(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 355,
        source: "Int[(e_.*x_)^m_.*(a_+b_.*x_^2)^p_.*(c_+d_.*x_^2)^q_.,x_Symbol] :=
          Int[ExpandIntegrand[(e*x)^m*(a+b*x^2)^p*(c+d*x^2)^q,x],x] /;
        FreeQ[{a,b,c,d,e,m},x] && NeQ[b*c-a*d,0] && IGtQ[p,0] && IGtQ[q,0]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, m_, p_, q_, x_],
        optional: [b__, d__, e__, m_, p_, q_],
        x_free: [a__, b__, c__, d__, e__, m_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && igtq!(p_, 0)
                && igtq!(q_, 0)
        },
        rhs: {
            let integrand = (&e__ * x_).pow(&m_)
                * (&a__ + &b__ * x_.pow(2)).pow(&p_)
                * (&c__ + &d__ * x_.pow(2)).pow(&q_);
            let expanded = rubi_expand_integrand(&integrand, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_356(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 356,
        source: "Int[(e_.*x_)^m_.*(a_+b_.*x_^2)^p_.*(c_+d_.*x_^2),x_Symbol] :=
          c*(e*x)^(m+1)*(a+b*x^2)^(p+1)/(a*e*(m+1)) /;
        FreeQ[{a,b,c,d,e,m,p},x] && NeQ[b*c-a*d,0] && EqQ[a*d*(m+1)-b*c*(m+2*p+3),0] && NeQ[m,-1]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, e__, m_, p_, x_],
        optional: [b__, d__, e__, m_, p_],
        x_free: [a__, b__, c__, d__, e__, m_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, p_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(
                    &a__ * &d__ * (&m_ + 1)
                        - &b__ * &c__ * (&m_ + Atom::num(2) * &p_ + 3),
                    0
                )
                && neq!(m_, -1)
        },
        rhs: {
            rubi_simp(&(&c__ * (&e__ * x_).pow(&m_ + 1)
                    * (&a__ + &b__ * x_.pow(2)).pow(&p_ + 1)
                    / (&a__ * &e__ * (&m_ + 1))), x_)
        },
    ));
}

fn push_rules_rule_357(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 357,
        source: "Int[(e_.*x_)^m_.*(a_+b_.*x_^2)^p_*(c_+d_.*x_^2),x_Symbol] :=
          (b*c-a*d)*(e*x)^(m+1)*(a+b*x^2)^(p+1)/(a*b*e*(m+1)) + d/b \\[Star] Int[(e*x)^m*(a+b*x^2)^(p+1),x] /;
        FreeQ[{a,b,c,d,e},x] && NeQ[b*c-a*d,0] && EqQ[m+2*p+3,0] && LtQ[p,-1]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, e__, m_, p_, x_],
        optional: [b__, d__, e__, m_],
        x_free: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(&m_ + Atom::num(2) * &p_ + 3, 0)
                && ltq!(p_, -1)
        },
        rhs: {
            let base = &a__ + &b__ * x_.pow(2);
            let direct = (&b__ * &c__ - &a__ * &d__)
                * (&e__ * x_).pow(&m_ + 1)
                * base.pow(&p_ + 1)
                / (&a__ * &b__ * &e__ * (&m_ + 1));
            let primitive = rubi_rhs_int(
                &((&e__ * x_).pow(&m_) * base.pow(&p_ + 1)),
                x_,
            );
            rubi_simp(&(direct), x_) + rubi_star(&d__ / &b__, primitive)
        },
    ));
}

fn push_rules_rule_358(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 358,
        source: "Int[(e_.*x_)^m_*(a_+b_.*x_^2)^p_.*(c_+d_.*x_^2),x_Symbol] :=
          c*(e*x)^(m+1)*(a+b*x^2)^(p+1)/(a*e*(m+1)) + d/e^2 \\[Star] Int[(e*x)^(m+2)*(a+b*x^2)^p,x] /;
        FreeQ[{a,b,c,d,e,m,p},x] && NeQ[b*c-a*d,0] && EqQ[Simplify[m+2*p+3],0] && NeQ[m,-1]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, e__, m_, p_, x_],
        optional: [b__, d__, e__, p_],
        x_free: [a__, b__, c__, d__, e__, m_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, p_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && eqq!(rubi_simplify(&(&m_ + Atom::num(2) * &p_ + 3)), 0)
                && neq!(m_, -1)
        },
        rhs: {
            let base = &a__ + &b__ * x_.pow(2);
            let direct = &c__ * (&e__ * x_).pow(&m_ + 1) * base.pow(&p_ + 1)
                / (&a__ * &e__ * (&m_ + 1));
            let primitive = rubi_rhs_int(
                &((&e__ * x_).pow(&m_ + 2) * base.pow(&p_)),
                x_,
            );
            rubi_simp(&(direct), x_) + rubi_star(&d__ / e__.pow(2), primitive)
        },
    ));
}

fn push_rules_rule_359(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 359,
        source: "Int[(e_.*x_)^m_.*(a_+b_.*x_^2)^p_.*(c_+d_.*x_^2),x_Symbol] :=
          c*(e*x)^(m+1)*(a+b*x^2)^(p+1)/(a*e*(m+1)) +
          (a*d*(m+1)-b*c*(m+2*p+3))/(a*e^2*(m+1)) \\[Star] Int[(e*x)^(m+2)*(a+b*x^2)^p,x] /;
        FreeQ[{a,b,c,d,e,p},x] && NeQ[b*c-a*d,0] && LtQ[m,-1] && Not[ILtQ[p,-1]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, e__, m_, p_, x_],
        optional: [b__, d__, e__, m_, p_],
        x_free: [a__, b__, c__, d__, e__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, p_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && ltq!(m_, -1)
                && !iltq!(p_, -1)
        },
        rhs: {
            let base = &a__ + &b__ * x_.pow(2);
            let direct = &c__ * (&e__ * x_).pow(&m_ + 1) * base.pow(&p_ + 1)
                / (&a__ * &e__ * (&m_ + 1));
            let primitive = rubi_rhs_int(
                &((&e__ * x_).pow(&m_ + 2) * base.pow(&p_)),
                x_,
            );
            let multiplier = (&a__ * &d__ * (&m_ + 1)
                - &b__ * &c__ * (&m_ + Atom::num(2) * &p_ + 3))
                / (&a__ * e__.pow(2) * (&m_ + 1));
            rubi_simp(&(direct), x_) + rubi_star(multiplier, primitive)
        },
    ));
}

fn push_rules_rule_360(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 360,
        source: "Int[x_^m_*(a_+b_.*x_^2)^p_*(c_+d_.*x_^2),x_Symbol] :=
          (-a)^(m/2-1)*(b*c-a*d)*x*(a+b*x^2)^(p+1)/(2*b^(m/2+1)*(p+1)) +
          1/(2*b^(m/2+1)*(p+1)) \\[Star] Int[(a+b*x^2)^(p+1)*
            ExpandToSum[2*b*(p+1)*x^2*Together[(b^(m/2)*x^(m-2)*(c+d*x^2)-(-a)^(m/2-1)*(b*c-a*d))/(a+b*x^2)]-(-a)^(m/2-1)*(b*c-a*d),x],x] /;
        FreeQ[{a,b,c,d},x] && NeQ[b*c-a*d,0] && LtQ[p,-1] && IGtQ[m/2,0] && (IntegerQ[p] || EqQ[m+2*p+1,0])",
        desc: "???",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [a__, b__, c__, d__, m_, p_, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && ltq!(p_, -1)
                && igtq!(&m_ / 2, 0)
                && (integerq!(p_) || eqq!(&m_ + Atom::num(2) * &p_ + 1, 0))
        },
        rhs: {
            let half_m = &m_ / 2;
            let determinant = &b__ * &c__ - &a__ * &d__;
            let leading = (-&a__).pow(&half_m - 1);
            let base = &a__ + &b__ * x_.pow(2);
            let denominator = Atom::num(2) * b__.pow(&half_m + 1) * (&p_ + 1);
            let direct = &leading * &determinant * x_ * base.pow(&p_ + 1)
                / &denominator;
            let together = rubi_together_simplify(
                &((b__.pow(&half_m)
                    * x_.pow(&m_ - 2)
                    * (&c__ + &d__ * x_.pow(2))
                    - &leading * &determinant)
                    / &base),
            );
            let payload = rubi_expand_to_sum(
                &(Atom::num(2) * &b__ * (&p_ + 1) * x_.pow(2) * together
                    - &leading * &determinant),
                x_,
            );
            let primitive = rubi_rhs_int(&(base.pow(&p_ + 1) * payload), x_);
            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / denominator, primitive)
        },
    ));
}

fn push_rules_rule_361(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 361,
        source: "Int[x_^m_*(a_+b_.*x_^2)^p_*(c_+d_.*x_^2),x_Symbol] :=
          (-a)^(m/2-1)*(b*c-a*d)*x*(a+b*x^2)^(p+1)/(2*b^(m/2+1)*(p+1)) +
          1/(2*b^(m/2+1)*(p+1)) \\[Star] Int[x^m*(a+b*x^2)^(p+1)*
            ExpandToSum[2*b*(p+1)*Together[(b^(m/2)*(c+d*x^2)-(-a)^(m/2-1)*(b*c-a*d)*x^(-m+2))/(a+b*x^2)]-
              (-a)^(m/2-1)*(b*c-a*d)*x^(-m),x],x] /;
        FreeQ[{a,b,c,d},x] && NeQ[b*c-a*d,0] && LtQ[p,-1] && ILtQ[m/2,0] && (IntegerQ[p] || EqQ[m+2*p+1,0])",
        desc: "???",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [a__, b__, c__, d__, m_, p_, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && ltq!(p_, -1)
                && iltq!(&m_ / 2, 0)
                && (integerq!(p_) || eqq!(&m_ + Atom::num(2) * &p_ + 1, 0))
        },
        rhs: {
            let half_m = &m_ / 2;
            let determinant = &b__ * &c__ - &a__ * &d__;
            let leading = (-&a__).pow(&half_m - 1);
            let base = &a__ + &b__ * x_.pow(2);
            let denominator = Atom::num(2) * b__.pow(&half_m + 1) * (&p_ + 1);
            let direct = &leading * &determinant * x_ * base.pow(&p_ + 1)
                / &denominator;
            let together = rubi_together_simplify(
                &((b__.pow(&half_m) * (&c__ + &d__ * x_.pow(2))
                    - &leading * &determinant * x_.pow(-&m_ + 2))
                    / &base),
            );
            let payload = rubi_expand_to_sum(
                &(Atom::num(2) * &b__ * (&p_ + 1) * together
                    - &leading * &determinant / x_.pow(&m_)),
                x_,
            );
            let primitive = rubi_rhs_int(
                &(x_.pow(&m_) * base.pow(&p_ + 1) * payload),
                x_,
            );
            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / denominator, primitive)
        },
    ));
}

fn push_rules_rule_362(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 362,
        source: "Int[(e_.*x_)^m_.*(a_+b_.*x_^2)^p_.*(c_+d_.*x_^2),x_Symbol] :=
          -(b*c-a*d)*(e*x)^(m+1)*(a+b*x^2)^(p+1)/(2*a*b*e*(p+1)) -
          (a*d*(m+1)-b*c*(m+2*p+3))/(2*a*b*(p+1)) \\[Star] Int[(e*x)^m*(a+b*x^2)^(p+1),x] /;
        FreeQ[{a,b,c,d,e,m},x] && NeQ[b*c-a*d,0] && LtQ[p,-1] &&
          (Not[IntegerQ[p+1/2]] && NeQ[p,-5/4] || Not[RationalQ[m]] || ILtQ[p+1/2,0] && LeQ[-1,m,-2*(p+1)])",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, e__, m_, p_, x_],
        optional: [b__, d__, e__, m_, p_],
        x_free: [a__, b__, c__, d__, e__, m_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && ltq!(p_, -1)
                && ((!integerq!(&p_ + Atom::num(1) / 2) && neq!(p_, -Atom::num(5) / 4))
                    || !rationalq!(m_)
                    || iltq!(&p_ + Atom::num(1) / 2, 0)
                        && leq!(Atom::num(-1), m_, -Atom::num(2) * (&p_ + 1)))
        },
        rhs: {
            let determinant = &b__ * &c__ - &a__ * &d__;
            let base = &a__ + &b__ * x_.pow(2);
            let direct = -&determinant
                * (&e__ * x_).pow(&m_ + 1)
                * base.pow(&p_ + 1)
                / (Atom::num(2) * &a__ * &b__ * &e__ * (&p_ + 1));
            let primitive = rubi_rhs_int(
                &((&e__ * x_).pow(&m_) * base.pow(&p_ + 1)),
                x_,
            );
            let multiplier = (&a__ * &d__ * (&m_ + 1)
                - &b__ * &c__ * (&m_ + Atom::num(2) * &p_ + 3))
                / (Atom::num(2) * &a__ * &b__ * (&p_ + 1));
            rubi_simp(&(direct), x_) - rubi_star(multiplier, primitive)
        },
    ));
}

fn push_rules_rule_363(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 363,
        source: "Int[(e_.*x_)^m_.*(a_+b_.*x_^2)^p_.*(c_+d_.*x_^2),x_Symbol] :=
          d*(e*x)^(m+1)*(a+b*x^2)^(p+1)/(b*e*(m+2*p+3)) -
          (a*d*(m+1)-b*c*(m+2*p+3))/(b*(m+2*p+3)) \\[Star] Int[(e*x)^m*(a+b*x^2)^p,x] /;
        FreeQ[{a,b,c,d,e,m,p},x] && NeQ[b*c-a*d,0] && NeQ[m+2*p+3,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, e__, m_, p_, x_],
        optional: [b__, d__, e__, m_, p_],
        x_free: [a__, b__, c__, d__, e__, m_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, p_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && neq!(&m_ + Atom::num(2) * &p_ + 3, 0)
        },
        rhs: {
            let denominator = &m_ + Atom::num(2) * &p_ + 3;
            let base = &a__ + &b__ * x_.pow(2);
            let direct = &d__ * (&e__ * x_).pow(&m_ + 1) * base.pow(&p_ + 1)
                / (&b__ * &e__ * &denominator);
            let primitive = rubi_rhs_int(
                &((&e__ * x_).pow(&m_) * base.pow(&p_)),
                x_,
            );
            let multiplier = (&a__ * &d__ * (&m_ + 1) - &b__ * &c__ * &denominator)
                / (&b__ * &denominator);
            rubi_simp(&(direct), x_) - rubi_star(multiplier, primitive)
        },
    ));
}

fn push_rules_rule_364(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 364,
        source: "Int[(e_.*x_)^m_.*(a_+b_.*x_^2)^p_/(c_+d_.*x_^2),x_Symbol] :=
          Int[ExpandIntegrand[(e*x)^m*(a+b*x^2)^p/(c+d*x^2),x],x] /;
        FreeQ[{a,b,c,d,e,m},x] && NeQ[b*c-a*d,0] && IGtQ[p,0] && (IntegerQ[m] || IGtQ[2*(m+1),0] || Not[RationalQ[m]])",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern: (e__ * x_).pow(m_) * (a__ + b__ * x_.pow(2)).pow(p_) / (c__ + d__ * x_.pow(2)),
        with: [a__, b__, c__, d__, e__, m_, p_, x_],
        optional: [b__, d__, e__, m_],
        x_free: [a__, b__, c__, d__, e__, m_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && igtq!(p_, 0)
                && (integerq!(m_)
                    || igtq!(Atom::num(2) * (&m_ + 1), 0)
                    || !rationalq!(m_))
        },
        rhs: {
            let integrand = (&e__ * x_).pow(&m_)
                * (&a__ + &b__ * x_.pow(2)).pow(&p_)
                / (&c__ + &d__ * x_.pow(2));
            let expanded = rubi_expand_integrand(&integrand, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_365(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 365,
        source: "Int[(e_.*x_)^m_*(a_+b_.*x_^2)^p_*(c_+d_.*x_^2)^2,x_Symbol] :=
          c^2*(e*x)^(m+1)*(a+b*x^2)^(p+1)/(a*e*(m+1)) -
          1/(a*e^2*(m+1)) \\[Star] Int[(e*x)^(m+2)*(a+b*x^2)^p*Simp[2*b*c^2*(p+1)+c*(b*c-2*a*d)*(m+1)-a*d^2*(m+1)*x^2,x],x] /;
        FreeQ[{a,b,c,d,e,p},x] && NeQ[b*c-a*d,0] && LtQ[m,-1]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, e__, m_, p_, x_],
        optional: [b__, d__, e__],
        x_free: [a__, b__, c__, d__, e__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, p_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && ltq!(m_, -1)
        },
        rhs: {
            let base = &a__ + &b__ * x_.pow(2);
            let direct = c__.pow(2)
                * (&e__ * x_).pow(&m_ + 1)
                * base.pow(&p_ + 1)
                / (&a__ * &e__ * (&m_ + 1));
            let payload = simp!(
                Atom::num(2) * &b__ * c__.pow(2) * (&p_ + 1)
                    + &c__ * (&b__ * &c__ - Atom::num(2) * &a__ * &d__) * (&m_ + 1)
                    - &a__ * d__.pow(2) * (&m_ + 1) * x_.pow(2),
                x_
            );
            let primitive = rubi_rhs_int(
                &((&e__ * x_).pow(&m_ + 2) * base.pow(&p_) * payload),
                x_,
            );
            let multiplier = Atom::num(1) / (&a__ * e__.pow(2) * (&m_ + 1));
            rubi_simp(&(direct), x_) - rubi_star(multiplier, primitive)
        },
    ));
}

fn push_rules_rule_366(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 366,
        source: "Int[(e_.*x_)^m_.*(a_+b_.*x_^2)^p_*(c_+d_.*x_^2)^2,x_Symbol] :=
          -(b*c-a*d)^2*(e*x)^(m+1)*(a+b*x^2)^(p+1)/(2*a*b^2*e*(p+1)) +
          1/(2*a*b^2*(p+1)) \\[Star] Int[(e*x)^m*(a+b*x^2)^(p+1)*Simp[(b*c-a*d)^2*(m+1)+2*b^2*c^2*(p+1)+2*a*b*d^2*(p+1)*x^2,x],x] /;
        FreeQ[{a,b,c,d,e,m},x] && NeQ[b*c-a*d,0] && LtQ[p,-1]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, e__, m_, p_, x_],
        optional: [b__, d__, e__, m_],
        x_free: [a__, b__, c__, d__, e__, m_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && ltq!(p_, -1)
        },
        rhs: {
            let determinant = &b__ * &c__ - &a__ * &d__;
            let base = &a__ + &b__ * x_.pow(2);
            let direct = -determinant.pow(2)
                * (&e__ * x_).pow(&m_ + 1)
                * base.pow(&p_ + 1)
                / (Atom::num(2) * &a__ * b__.pow(2) * &e__ * (&p_ + 1));
            let payload = simp!(
                determinant.pow(2) * (&m_ + 1)
                    + Atom::num(2) * b__.pow(2) * c__.pow(2) * (&p_ + 1)
                    + Atom::num(2) * &a__ * &b__ * d__.pow(2) * (&p_ + 1) * x_.pow(2),
                x_
            );
            let primitive = rubi_rhs_int(
                &((&e__ * x_).pow(&m_) * base.pow(&p_ + 1) * payload),
                x_,
            );
            let multiplier = Atom::num(1) / (Atom::num(2) * &a__ * b__.pow(2) * (&p_ + 1));
            rubi_simp(&(direct), x_) + rubi_star(multiplier, primitive)
        },
    ));
}

fn push_rules_rule_367(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 367,
        source: "Int[(e_.*x_)^m_.*(a_+b_.*x_^2)^p_*(c_+d_.*x_^2)^2,x_Symbol] :=
          d^2*(e*x)^(m+3)*(a+b*x^2)^(p+1)/(b*e^3*(m+2*p+5)) +
          1/(b*(m+2*p+5)) \\[Star] Int[(e*x)^m*(a+b*x^2)^p*Simp[b*c^2*(m+2*p+5)-d*(a*d*(m+3)-2*b*c*(m+2*p+5))*x^2,x],x] /;
        FreeQ[{a,b,c,d,e,m,p},x] && NeQ[b*c-a*d,0] && NeQ[m+2*p+5,0]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, e__, m_, p_, x_],
        optional: [b__, d__, e__, m_],
        x_free: [a__, b__, c__, d__, e__, m_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, p_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && neq!(&m_ + Atom::num(2) * &p_ + 5, 0)
        },
        rhs: {
            let denominator = &m_ + Atom::num(2) * &p_ + 5;
            let base = &a__ + &b__ * x_.pow(2);
            let direct = d__.pow(2)
                * (&e__ * x_).pow(&m_ + 3)
                * base.pow(&p_ + 1)
                / (&b__ * e__.pow(3) * &denominator);
            let payload = simp!(
                &b__ * c__.pow(2) * &denominator
                    - &d__
                        * (&a__ * &d__ * (&m_ + 3)
                            - Atom::num(2) * &b__ * &c__ * &denominator)
                        * x_.pow(2),
                x_
            );
            let primitive = rubi_rhs_int(
                &((&e__ * x_).pow(&m_) * base.pow(&p_) * payload),
                x_,
            );
            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / (&b__ * denominator), primitive)
        },
    ));
}

fn push_rules_rule_368(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 368,
        source: "Int[(e_.*x_)^m_*(a_+b_.*x_^2)^p_*(c_+d_.*x_^2)^q_,x_Symbol] :=
          With[{k=Denominator[m]},
          k/e \\[Star] Subst[Int[x^(k*(m+1)-1)*(a+b*x^(k*2)/e^2)^p*(c+d*x^(k*2)/e^2)^q,x],x,(e*x)^(1/k)]] /;
        FreeQ[{a,b,c,d,e,p,q},x] && NeQ[b*c-a*d,0] && FractionQ[m] && IntegerQ[p]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, m_, p_, q_, x_],
        optional: [b__, d__, e__],
        x_free: [a__, b__, c__, d__, e__, p_, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__, p_, q_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && fractionq!(m_)
                && integerq!(p_)
        },
        rhs: {
            let k = Atom::num(rational_denominator(&m_).rubi_rhs());
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = sub_atom.pow(&k * (&m_ + 1) - 1)
                * (&a__ + &b__ * sub_atom.pow(Atom::num(2) * &k) / e__.pow(2)).pow(&p_)
                * (&c__ + &d__ * sub_atom.pow(Atom::num(2) * &k) / e__.pow(2)).pow(&q_);
            let primitive = rubi_rhs_int(&transformed_integrand, sub);
            let substituted = rubi_subst(
                &primitive,
                sub,
                (&e__ * x_).pow(Atom::num(1) / &k),
            );
            rubi_star(&k / &e__, substituted)
        },
    ));
}

fn push_rules_rule_369(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 369,
        source: "Int[(e_.*x_)^m_.*(a_+b_.*x_^2)^p_*(c_+d_.*x_^2)^q_,x_Symbol] :=
          e*(e*x)^(m-1)*(a+b*x^2)^(p+1)*(c+d*x^2)^q/(2*b*(p+1)) -
          e^2/(2*b*(p+1)) \\[Star] Int[(e*x)^(m-2)*(a+b*x^2)^(p+1)*(c+d*x^2)^(q-1)*Simp[c*(m-1)+d*(m+2*q-1)*x^2,x],x] /;
        FreeQ[{a,b,c,d,e},x] && NeQ[b*c-a*d,0] && LtQ[p,-1] && GtQ[q,0] && GtQ[m,1] && IntBinomialQ[a,b,c,d,e,m,2,p,q,x]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, m_, p_, q_, x_],
        optional: [b__, d__, e__, m_],
        x_free: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && ltq!(p_, -1)
                && gtq!(q_, 0)
                && gtq!(m_, 1)
                && rubi_int_binomial_scaled_q(
                    &a__, &b__, &c__, &d__, &e__, &m_, &Atom::num(2), &p_, &q_, x_,
                )
        },
        rhs: {
            let first_base = &a__ + &b__ * x_.pow(2);
            let second_base = &c__ + &d__ * x_.pow(2);
            let direct = &e__
                * (&e__ * x_).pow(&m_ - 1)
                * first_base.pow(&p_ + 1)
                * second_base.pow(&q_)
                / (Atom::num(2) * &b__ * (&p_ + 1));
            let payload = simp!(
                &c__ * (&m_ - 1) + &d__ * (&m_ + Atom::num(2) * &q_ - 1) * x_.pow(2),
                x_
            );
            let primitive = rubi_rhs_int(
                &((&e__ * x_).pow(&m_ - 2)
                    * first_base.pow(&p_ + 1)
                    * second_base.pow(&q_ - 1)
                    * payload),
                x_,
            );
            let multiplier = e__.pow(2) / (Atom::num(2) * &b__ * (&p_ + 1));
            rubi_simp(&(direct), x_) - rubi_star(multiplier, primitive)
        },
    ));
}

fn push_rules_rule_370(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 370,
        source: "Int[(e_.*x_)^m_.*(a_+b_.*x_^2)^p_*(c_+d_.*x_^2)^q_,x_Symbol] :=
          -(b*c-a*d)*(e*x)^(m+1)*(a+b*x^2)^(p+1)*(c+d*x^2)^(q-1)/(a*b*e*2*(p+1)) +
          1/(a*b*2*(p+1)) \\[Star] Int[(e*x)^m*(a+b*x^2)^(p+1)*(c+d*x^2)^(q-2)*
            Simp[c*(b*c*2*(p+1)+(b*c-a*d)*(m+1))+d*(b*c*2*(p+1)+(b*c-a*d)*(m+2*(q-1)+1))*x^2,x],x] /;
        FreeQ[{a,b,c,d,e,m},x] && NeQ[b*c-a*d,0] && LtQ[p,-1] && GtQ[q,1] && IntBinomialQ[a,b,c,d,e,m,2,p,q,x]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, m_, p_, q_, x_],
        optional: [b__, d__, e__, m_],
        x_free: [a__, b__, c__, d__, e__, m_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && ltq!(p_, -1)
                && gtq!(q_, 1)
                && rubi_int_binomial_scaled_q(
                    &a__, &b__, &c__, &d__, &e__, &m_, &Atom::num(2), &p_, &q_, x_,
                )
        },
        rhs: {
            let determinant = &b__ * &c__ - &a__ * &d__;
            let first_base = &a__ + &b__ * x_.pow(2);
            let second_base = &c__ + &d__ * x_.pow(2);
            let denominator = Atom::num(2) * &a__ * &b__ * (&p_ + 1);
            let direct = -&determinant
                * (&e__ * x_).pow(&m_ + 1)
                * first_base.pow(&p_ + 1)
                * second_base.pow(&q_ - 1)
                / (&e__ * &denominator);
            let payload = simp!(
                &c__
                    * (Atom::num(2) * &b__ * &c__ * (&p_ + 1)
                        + &determinant * (&m_ + 1))
                    + &d__
                        * (Atom::num(2) * &b__ * &c__ * (&p_ + 1)
                            + &determinant * (&m_ + Atom::num(2) * (&q_ - 1) + 1))
                        * x_.pow(2),
                x_
            );
            let primitive = rubi_rhs_int(
                &((&e__ * x_).pow(&m_)
                    * first_base.pow(&p_ + 1)
                    * second_base.pow(&q_ - 2)
                    * payload),
                x_,
            );
            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / denominator, primitive)
        },
    ));
}

fn push_rules_rule_371(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 371,
        source: "Int[(e_.*x_)^m_.*(a_+b_.*x_^2)^p_*(c_+d_.*x_^2)^q_,x_Symbol] :=
          -(e*x)^(m+1)*(a+b*x^2)^(p+1)*(c+d*x^2)^q/(a*e*2*(p+1)) +
          1/(a*2*(p+1)) \\[Star] Int[(e*x)^m*(a+b*x^2)^(p+1)*(c+d*x^2)^(q-1)*Simp[c*(m+2*(p+1)+1)+d*(m+2*(p+q+1)+1)*x^2,x],x] /;
        FreeQ[{a,b,c,d,e,m},x] && NeQ[b*c-a*d,0] && LtQ[p,-1] && LtQ[0,q,1] && IntBinomialQ[a,b,c,d,e,m,2,p,q,x]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, m_, p_, q_, x_],
        optional: [b__, d__, e__, m_],
        x_free: [a__, b__, c__, d__, e__, m_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && ltq!(p_, -1)
                && ltq!(0, q_, 1)
                && rubi_int_binomial_scaled_q(
                    &a__, &b__, &c__, &d__, &e__, &m_, &Atom::num(2), &p_, &q_, x_,
                )
        },
        rhs: {
            let first_base = &a__ + &b__ * x_.pow(2);
            let second_base = &c__ + &d__ * x_.pow(2);
            let denominator = Atom::num(2) * &a__ * (&p_ + 1);
            let direct = -(&e__ * x_).pow(&m_ + 1)
                * first_base.pow(&p_ + 1)
                * second_base.pow(&q_)
                / (&e__ * &denominator);
            let payload = simp!(
                &c__ * (&m_ + Atom::num(2) * (&p_ + 1) + 1)
                    + &d__
                        * (&m_ + Atom::num(2) * (&p_ + &q_ + 1) + 1)
                        * x_.pow(2),
                x_
            );
            let primitive = rubi_rhs_int(
                &((&e__ * x_).pow(&m_)
                    * first_base.pow(&p_ + 1)
                    * second_base.pow(&q_ - 1)
                    * payload),
                x_,
            );
            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / denominator, primitive)
        },
    ));
}

fn push_rules_rule_372(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 372,
        source: "Int[(e_.*x_)^m_.*(a_+b_.*x_^2)^p_*(c_+d_.*x_^2)^q_,x_Symbol] :=
          -a*e^3*(e*x)^(m-3)*(a+b*x^2)^(p+1)*(c+d*x^2)^(q+1)/(2*b*(b*c-a*d)*(p+1)) +
          e^4/(2*b*(b*c-a*d)*(p+1)) \\[Star] Int[(e*x)^(m-4)*(a+b*x^2)^(p+1)*(c+d*x^2)^q*
            Simp[a*c*(m-3)+(a*d*(m+2*q-1)+2*b*c*(p+1))*x^2,x],x] /;
        FreeQ[{a,b,c,d,e,q},x] && NeQ[b*c-a*d,0] && LtQ[p,-1] && GtQ[m,3] && IntBinomialQ[a,b,c,d,e,m,2,p,q,x]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, m_, p_, q_, x_],
        optional: [b__, d__, e__, m_],
        x_free: [a__, b__, c__, d__, e__, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__, q_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && ltq!(p_, -1)
                && gtq!(m_, 3)
                && rubi_int_binomial_scaled_q(
                    &a__, &b__, &c__, &d__, &e__, &m_, &Atom::num(2), &p_, &q_, x_,
                )
        },
        rhs: {
            let determinant = &b__ * &c__ - &a__ * &d__;
            let first_base = &a__ + &b__ * x_.pow(2);
            let second_base = &c__ + &d__ * x_.pow(2);
            let denominator = Atom::num(2) * &b__ * &determinant * (&p_ + 1);
            let direct = -&a__
                * e__.pow(3)
                * (&e__ * x_).pow(&m_ - 3)
                * first_base.pow(&p_ + 1)
                * second_base.pow(&q_ + 1)
                / &denominator;
            let payload = simp!(
                &a__ * &c__ * (&m_ - 3)
                    + (&a__ * &d__ * (&m_ + Atom::num(2) * &q_ - 1)
                        + Atom::num(2) * &b__ * &c__ * (&p_ + 1))
                        * x_.pow(2),
                x_
            );
            let primitive = rubi_rhs_int(
                &((&e__ * x_).pow(&m_ - 4)
                    * first_base.pow(&p_ + 1)
                    * second_base.pow(&q_)
                    * payload),
                x_,
            );
            rubi_simp(&(direct), x_) + rubi_star(e__.pow(4) / denominator, primitive)
        },
    ));
}

fn push_rules_rule_373(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 373,
        source: "Int[(e_.*x_)^m_.*(a_+b_.*x_^2)^p_*(c_+d_.*x_^2)^q_,x_Symbol] :=
          e*(e*x)^(m-1)*(a+b*x^2)^(p+1)*(c+d*x^2)^(q+1)/(2*(b*c-a*d)*(p+1)) -
          e^2/(2*(b*c-a*d)*(p+1)) \\[Star] Int[(e*x)^(m-2)*(a+b*x^2)^(p+1)*(c+d*x^2)^q*Simp[c*(m-1)+d*(m+2*p+2*q+3)*x^2,x],x] /;
        FreeQ[{a,b,c,d,e,q},x] && NeQ[b*c-a*d,0] && LtQ[p,-1] && GtQ[m,1] && LeQ[m,3] && IntBinomialQ[a,b,c,d,e,m,2,p,q,x]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, m_, p_, q_, x_],
        optional: [b__, d__, e__, m_],
        x_free: [a__, b__, c__, d__, e__, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__, q_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && ltq!(p_, -1)
                && gtq!(m_, 1)
                && leq!(m_, 3)
                && rubi_int_binomial_scaled_q(
                    &a__, &b__, &c__, &d__, &e__, &m_, &Atom::num(2), &p_, &q_, x_,
                )
        },
        rhs: {
            let determinant = &b__ * &c__ - &a__ * &d__;
            let first_base = &a__ + &b__ * x_.pow(2);
            let second_base = &c__ + &d__ * x_.pow(2);
            let denominator = Atom::num(2) * &determinant * (&p_ + 1);
            let direct = &e__
                * (&e__ * x_).pow(&m_ - 1)
                * first_base.pow(&p_ + 1)
                * second_base.pow(&q_ + 1)
                / &denominator;
            let payload = simp!(
                &c__ * (&m_ - 1)
                    + &d__
                        * (&m_ + Atom::num(2) * &p_ + Atom::num(2) * &q_ + 3)
                        * x_.pow(2),
                x_
            );
            let primitive = rubi_rhs_int(
                &((&e__ * x_).pow(&m_ - 2)
                    * first_base.pow(&p_ + 1)
                    * second_base.pow(&q_)
                    * payload),
                x_,
            );
            rubi_simp(&(direct), x_) - rubi_star(e__.pow(2) / denominator, primitive)
        },
    ));
}

fn push_rules_rule_374(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 374,
        source: "Int[(e_.*x_)^m_.*(a_+b_.*x_^2)^p_*(c_+d_.*x_^2)^q_,x_Symbol] :=
          -b*(e*x)^(m+1)*(a+b*x^2)^(p+1)*(c+d*x^2)^(q+1)/(a*e*2*(b*c-a*d)*(p+1)) +
          1/(a*2*(b*c-a*d)*(p+1)) \\[Star]
            Int[(e*x)^m*(a+b*x^2)^(p+1)*(c+d*x^2)^q*Simp[b*c*(m+1)+2*(b*c-a*d)*(p+1)+d*b*(m+2*(p+q+2)+1)*x^2,x],x] /;
        FreeQ[{a,b,c,d,e,m,q},x] && NeQ[b*c-a*d,0] && LtQ[p,-1] && IntBinomialQ[a,b,c,d,e,m,2,p,q,x]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, m_, p_, q_, x_],
        optional: [b__, d__, e__, m_],
        x_free: [a__, b__, c__, d__, e__, m_, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, q_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && ltq!(p_, -1)
                && rubi_int_binomial_scaled_q(
                    &a__, &b__, &c__, &d__, &e__, &m_, &Atom::num(2), &p_, &q_, x_,
                )
        },
        rhs: {
            let determinant = &b__ * &c__ - &a__ * &d__;
            let first_base = &a__ + &b__ * x_.pow(2);
            let second_base = &c__ + &d__ * x_.pow(2);
            let denominator = Atom::num(2) * &a__ * &determinant * (&p_ + 1);
            let direct = -&b__
                * (&e__ * x_).pow(&m_ + 1)
                * first_base.pow(&p_ + 1)
                * second_base.pow(&q_ + 1)
                / (&e__ * &denominator);
            let payload = simp!(
                &b__ * &c__ * (&m_ + 1)
                    + Atom::num(2) * &determinant * (&p_ + 1)
                    + &b__
                        * &d__
                        * (&m_ + Atom::num(2) * (&p_ + &q_ + 2) + 1)
                        * x_.pow(2),
                x_
            );
            let primitive = rubi_rhs_int(
                &((&e__ * x_).pow(&m_)
                    * first_base.pow(&p_ + 1)
                    * second_base.pow(&q_)
                    * payload),
                x_,
            );
            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / denominator, primitive)
        },
    ));
}

fn push_rules_rule_375(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 375,
        source: "Int[(e_.*x_)^m_*(a_+b_.*x_^2)^p_*(c_+d_.*x_^2)^q_,x_Symbol] :=
          (e*x)^(m+1)*(a+b*x^2)^p*(c+d*x^2)^q/(e*(m+1)) -
          2/(e^2*(m+1)) \\[Star] Int[(e*x)^(m+2)*(a+b*x^2)^(p-1)*(c+d*x^2)^(q-1)*Simp[b*c*p+a*d*q+b*d*(p+q)*x^2,x],x] /;
        FreeQ[{a,b,c,d,e},x] && NeQ[b*c-a*d,0] && GtQ[q,0] && LtQ[m,-1] && GtQ[p,0] && IntBinomialQ[a,b,c,d,e,m,2,p,q,x]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, m_, p_, q_, x_],
        optional: [b__, d__, e__],
        x_free: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && gtq!(q_, 0)
                && ltq!(m_, -1)
                && gtq!(p_, 0)
                && rubi_int_binomial_scaled_q(
                    &a__, &b__, &c__, &d__, &e__, &m_, &Atom::num(2), &p_, &q_, x_,
                )
        },
        rhs: {
            let first_base = &a__ + &b__ * x_.pow(2);
            let second_base = &c__ + &d__ * x_.pow(2);
            let direct = (&e__ * x_).pow(&m_ + 1)
                * first_base.pow(&p_)
                * second_base.pow(&q_)
                / (&e__ * (&m_ + 1));
            let payload = simp!(
                &b__ * &c__ * &p_ + &a__ * &d__ * &q_
                    + &b__ * &d__ * (&p_ + &q_) * x_.pow(2),
                x_
            );
            let primitive = rubi_rhs_int(
                &((&e__ * x_).pow(&m_ + 2)
                    * first_base.pow(&p_ - 1)
                    * second_base.pow(&q_ - 1)
                    * payload),
                x_,
            );
            let multiplier = Atom::num(2) / (e__.pow(2) * (&m_ + 1));
            rubi_simp(&(direct), x_) - rubi_star(multiplier, primitive)
        },
    ));
}

fn push_rules_rule_376(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 376,
        source: "Int[(e_.*x_)^m_*(a_+b_.*x_^2)^p_*(c_+d_.*x_^2)^q_,x_Symbol] :=
          c*(e*x)^(m+1)*(a+b*x^2)^(p+1)*(c+d*x^2)^(q-1)/(a*e*(m+1)) -
          1/(a*e^2*(m+1)) \\[Star] Int[(e*x)^(m+2)*(a+b*x^2)^p*(c+d*x^2)^(q-2)*
            Simp[c*(b*c-a*d)*(m+1)+2*c*(b*c*(p+1)+a*d*(q-1))+d*((b*c-a*d)*(m+1)+2*b*c*(p+q))*x^2,x],x] /;
        FreeQ[{a,b,c,d,e,p},x] && NeQ[b*c-a*d,0] && GtQ[q,1] && LtQ[m,-1] && IntBinomialQ[a,b,c,d,e,m,2,p,q,x]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, m_, p_, q_, x_],
        optional: [b__, d__, e__],
        x_free: [a__, b__, c__, d__, e__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, p_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && gtq!(q_, 1)
                && ltq!(m_, -1)
                && rubi_int_binomial_scaled_q(
                    &a__, &b__, &c__, &d__, &e__, &m_, &Atom::num(2), &p_, &q_, x_,
                )
        },
        rhs: {
            let determinant = &b__ * &c__ - &a__ * &d__;
            let first_base = &a__ + &b__ * x_.pow(2);
            let second_base = &c__ + &d__ * x_.pow(2);
            let direct = &c__
                * (&e__ * x_).pow(&m_ + 1)
                * first_base.pow(&p_ + 1)
                * second_base.pow(&q_ - 1)
                / (&a__ * &e__ * (&m_ + 1));
            let payload = simp!(
                &c__ * &determinant * (&m_ + 1)
                    + Atom::num(2)
                        * &c__
                        * (&b__ * &c__ * (&p_ + 1) + &a__ * &d__ * (&q_ - 1))
                    + &d__
                        * (&determinant * (&m_ + 1)
                            + Atom::num(2) * &b__ * &c__ * (&p_ + &q_))
                        * x_.pow(2),
                x_
            );
            let primitive = rubi_rhs_int(
                &((&e__ * x_).pow(&m_ + 2)
                    * first_base.pow(&p_)
                    * second_base.pow(&q_ - 2)
                    * payload),
                x_,
            );
            let multiplier = Atom::num(1) / (&a__ * e__.pow(2) * (&m_ + 1));
            rubi_simp(&(direct), x_) - rubi_star(multiplier, primitive)
        },
    ));
}

fn push_rules_rule_377(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 377,
        source: "Int[(e_.*x_)^m_*(a_+b_.*x_^2)^p_*(c_+d_.*x_^2)^q_,x_Symbol] :=
          (e*x)^(m+1)*(a+b*x^2)^(p+1)*(c+d*x^2)^q/(a*e*(m+1)) -
          1/(a*e^2*(m+1)) \\[Star] Int[(e*x)^(m+2)*(a+b*x^2)^p*(c+d*x^2)^(q-1)*
            Simp[b*c*(m+1)+2*(b*c*(p+1)+a*d*q)+d*(b*(m+1)+2*b*(p+q+1))*x^2,x],x] /;
        FreeQ[{a,b,c,d,e,p},x] && NeQ[b*c-a*d,0] && LtQ[0,q,1] && LtQ[m,-1] && IntBinomialQ[a,b,c,d,e,m,2,p,q,x]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, m_, p_, q_, x_],
        optional: [b__, d__, e__],
        x_free: [a__, b__, c__, d__, e__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, p_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && ltq!(0, q_, 1)
                && ltq!(m_, -1)
                && rubi_int_binomial_scaled_q(
                    &a__, &b__, &c__, &d__, &e__, &m_, &Atom::num(2), &p_, &q_, x_,
                )
        },
        rhs: {
            let first_base = &a__ + &b__ * x_.pow(2);
            let second_base = &c__ + &d__ * x_.pow(2);
            let direct = (&e__ * x_).pow(&m_ + 1)
                * first_base.pow(&p_ + 1)
                * second_base.pow(&q_)
                / (&a__ * &e__ * (&m_ + 1));
            let payload = simp!(
                &b__ * &c__ * (&m_ + 1)
                    + Atom::num(2) * (&b__ * &c__ * (&p_ + 1) + &a__ * &d__ * &q_)
                    + &d__
                        * (&b__ * (&m_ + 1) + Atom::num(2) * &b__ * (&p_ + &q_ + 1))
                        * x_.pow(2),
                x_
            );
            let primitive = rubi_rhs_int(
                &((&e__ * x_).pow(&m_ + 2)
                    * first_base.pow(&p_)
                    * second_base.pow(&q_ - 1)
                    * payload),
                x_,
            );
            let multiplier = Atom::num(1) / (&a__ * e__.pow(2) * (&m_ + 1));
            rubi_simp(&(direct), x_) - rubi_star(multiplier, primitive)
        },
    ));
}

fn push_rules_rule_378(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 378,
        source: "Int[(e_.*x_)^m_.*(a_+b_.*x_^2)^p_*(c_+d_.*x_^2)^q_,x_Symbol] :=
          (e*x)^(m+1)*(a+b*x^2)^p*(c+d*x^2)^q/(e*(m+2*(p+q)+1)) +
          2/(m+2*(p+q)+1) \\[Star] Int[(e*x)^m*(a+b*x^2)^(p-1)*(c+d*x^2)^(q-1)*Simp[a*c*(p+q)+(q*(b*c-a*d)+a*d*(p+q))*x^2,x],x] /;
        FreeQ[{a,b,c,d,e,m},x] && NeQ[b*c-a*d,0] && GtQ[q,0] && GtQ[p,0] && IntBinomialQ[a,b,c,d,e,m,2,p,q,x]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, m_, p_, q_, x_],
        optional: [b__, d__, e__, m_],
        x_free: [a__, b__, c__, d__, e__, m_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && gtq!(q_, 0)
                && gtq!(p_, 0)
                && rubi_int_binomial_scaled_q(
                    &a__, &b__, &c__, &d__, &e__, &m_, &Atom::num(2), &p_, &q_, x_,
                )
        },
        rhs: {
            let determinant = &b__ * &c__ - &a__ * &d__;
            let first_base = &a__ + &b__ * x_.pow(2);
            let second_base = &c__ + &d__ * x_.pow(2);
            let denominator = &m_ + Atom::num(2) * (&p_ + &q_) + 1;
            let direct = (&e__ * x_).pow(&m_ + 1)
                * first_base.pow(&p_)
                * second_base.pow(&q_)
                / (&e__ * &denominator);
            let payload = simp!(
                &a__ * &c__ * (&p_ + &q_)
                    + (&q_ * &determinant + &a__ * &d__ * (&p_ + &q_))
                        * x_.pow(2),
                x_
            );
            let primitive = rubi_rhs_int(
                &((&e__ * x_).pow(&m_)
                    * first_base.pow(&p_ - 1)
                    * second_base.pow(&q_ - 1)
                    * payload),
                x_,
            );
            rubi_simp(&(direct), x_) + rubi_star(Atom::num(2) / denominator, primitive)
        },
    ));
}

fn push_rules_rule_379(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 379,
        source: "Int[(e_.*x_)^m_.*(a_+b_.*x_^2)^p_*(c_+d_.*x_^2)^q_,x_Symbol] :=
          d*(e*x)^(m+1)*(a+b*x^2)^(p+1)*(c+d*x^2)^(q-1)/(b*e*(m+2*(p+q)+1)) +
          1/(b*(m+2*(p+q)+1)) \\[Star] Int[(e*x)^m*(a+b*x^2)^p*(c+d*x^2)^(q-2)*
            Simp[c*((b*c-a*d)*(m+1)+b*c*2*(p+q))+(d*(b*c-a*d)*(m+1)+d*2*(q-1)*(b*c-a*d)+b*c*d*2*(p+q))*x^2,x],x] /;
        FreeQ[{a,b,c,d,e,m,p},x] && NeQ[b*c-a*d,0] && GtQ[q,1] && IntBinomialQ[a,b,c,d,e,m,2,p,q,x]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, m_, p_, q_, x_],
        optional: [b__, d__, e__, m_],
        x_free: [a__, b__, c__, d__, e__, m_, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, p_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && gtq!(q_, 1)
                && rubi_int_binomial_scaled_q(
                    &a__, &b__, &c__, &d__, &e__, &m_, &Atom::num(2), &p_, &q_, x_,
                )
        },
        rhs: {
            let determinant = &b__ * &c__ - &a__ * &d__;
            let first_base = &a__ + &b__ * x_.pow(2);
            let second_base = &c__ + &d__ * x_.pow(2);
            let denominator = &m_ + Atom::num(2) * (&p_ + &q_) + 1;
            let direct = &d__
                * (&e__ * x_).pow(&m_ + 1)
                * first_base.pow(&p_ + 1)
                * second_base.pow(&q_ - 1)
                / (&b__ * &e__ * &denominator);
            let payload = simp!(
                &c__
                    * (&determinant * (&m_ + 1)
                        + Atom::num(2) * &b__ * &c__ * (&p_ + &q_))
                    + (&d__ * &determinant * (&m_ + 1)
                        + Atom::num(2) * &d__ * (&q_ - 1) * &determinant
                        + Atom::num(2) * &b__ * &c__ * &d__ * (&p_ + &q_))
                        * x_.pow(2),
                x_
            );
            let primitive = rubi_rhs_int(
                &((&e__ * x_).pow(&m_)
                    * first_base.pow(&p_)
                    * second_base.pow(&q_ - 2)
                    * payload),
                x_,
            );
            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / (&b__ * denominator), primitive)
        },
    ));
}

fn push_rules_rule_380(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 380,
        source: "Int[(e_.*x_)^m_.*(a_+b_.*x_^2)^p_*(c_+d_.*x_^2)^q_,x_Symbol] :=
          e*(e*x)^(m-1)*(a+b*x^2)^(p+1)*(c+d*x^2)^q/(b*(m+2*(p+q)+1)) -
          e^2/(b*(m+2*(p+q)+1)) \\[Star]
            Int[(e*x)^(m-2)*(a+b*x^2)^p*(c+d*x^2)^(q-1)*Simp[a*c*(m-1)+(a*d*(m-1)-2*q*(b*c-a*d))*x^2,x],x] /;
        FreeQ[{a,b,c,d,e,p},x] && NeQ[b*c-a*d,0] && GtQ[q,0] && GtQ[m,1] && IntBinomialQ[a,b,c,d,e,m,2,p,q,x]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, m_, p_, q_, x_],
        optional: [b__, d__, e__, m_],
        x_free: [a__, b__, c__, d__, e__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, p_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && gtq!(q_, 0)
                && gtq!(m_, 1)
                && rubi_int_binomial_scaled_q(
                    &a__, &b__, &c__, &d__, &e__, &m_, &Atom::num(2), &p_, &q_, x_,
                )
        },
        rhs: {
            let determinant = &b__ * &c__ - &a__ * &d__;
            let first_base = &a__ + &b__ * x_.pow(2);
            let second_base = &c__ + &d__ * x_.pow(2);
            let denominator = &m_ + Atom::num(2) * (&p_ + &q_) + 1;
            let direct = &e__
                * (&e__ * x_).pow(&m_ - 1)
                * first_base.pow(&p_ + 1)
                * second_base.pow(&q_)
                / (&b__ * &denominator);
            let payload = simp!(
                &a__ * &c__ * (&m_ - 1)
                    + (&a__ * &d__ * (&m_ - 1) - Atom::num(2) * &q_ * &determinant)
                        * x_.pow(2),
                x_
            );
            let primitive = rubi_rhs_int(
                &((&e__ * x_).pow(&m_ - 2)
                    * first_base.pow(&p_)
                    * second_base.pow(&q_ - 1)
                    * payload),
                x_,
            );
            rubi_simp(&(direct), x_) - rubi_star(e__.pow(2) / (&b__ * denominator), primitive)
        },
    ));
}

fn push_rules_rule_381(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 381,
        source: "Int[(e_.*x_)^m_.*(a_+b_.*x_^2)^p_*(c_+d_.*x_^2)^q_,x_Symbol] :=
          e^3*(e*x)^(m-3)*(a+b*x^2)^(p+1)*(c+d*x^2)^(q+1)/(b*d*(m+2*(p+q)+1)) -
          e^4/(b*d*(m+2*(p+q)+1)) \\[Star]
            Int[(e*x)^(m-4)*(a+b*x^2)^p*(c+d*x^2)^q*Simp[a*c*(m-3)+(a*d*(m+2*q-1)+b*c*(m+2*p-1))*x^2,x],x] /;
        FreeQ[{a,b,c,d,e,p,q},x] && NeQ[b*c-a*d,0] && GtQ[m,3] && IntBinomialQ[a,b,c,d,e,m,2,p,q,x]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, m_, p_, q_, x_],
        optional: [b__, d__, e__, m_],
        x_free: [a__, b__, c__, d__, e__, p_, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__, p_, q_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && gtq!(m_, 3)
                && rubi_int_binomial_scaled_q(
                    &a__, &b__, &c__, &d__, &e__, &m_, &Atom::num(2), &p_, &q_, x_,
                )
        },
        rhs: {
            let first_base = &a__ + &b__ * x_.pow(2);
            let second_base = &c__ + &d__ * x_.pow(2);
            let denominator = &m_ + Atom::num(2) * (&p_ + &q_) + 1;
            let direct = e__.pow(3)
                * (&e__ * x_).pow(&m_ - 3)
                * first_base.pow(&p_ + 1)
                * second_base.pow(&q_ + 1)
                / (&b__ * &d__ * &denominator);
            let payload = simp!(
                &a__ * &c__ * (&m_ - 3)
                    + (&a__ * &d__ * (&m_ + Atom::num(2) * &q_ - 1)
                        + &b__ * &c__ * (&m_ + Atom::num(2) * &p_ - 1))
                        * x_.pow(2),
                x_
            );
            let primitive = rubi_rhs_int(
                &((&e__ * x_).pow(&m_ - 4)
                    * first_base.pow(&p_)
                    * second_base.pow(&q_)
                    * payload),
                x_,
            );
            rubi_simp(&(direct), x_) - rubi_star(e__.pow(4) / (&b__ * &d__ * denominator), primitive)
        },
    ));
}

fn push_rules_rule_382(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 382,
        source: "Int[(e_.*x_)^m_*(a_+b_.*x_^2)^p_*(c_+d_.*x_^2)^q_,x_Symbol] :=
          (e*x)^(m+1)*(a+b*x^2)^(p+1)*(c+d*x^2)^(q+1)/(a*c*e*(m+1)) -
          1/(a*c*e^2*(m+1)) \\[Star]
            Int[(e*x)^(m+2)*(a+b*x^2)^p*(c+d*x^2)^q*Simp[(b*c+a*d)*(m+3)+2*(b*c*p+a*d*q)+b*d*(m+2*p+2*q+5)*x^2,x],x] /;
        FreeQ[{a,b,c,d,e,p,q},x] && NeQ[b*c-a*d,0] && LtQ[m,-1] && IntBinomialQ[a,b,c,d,e,m,2,p,q,x]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, m_, p_, q_, x_],
        optional: [b__, d__, e__],
        x_free: [a__, b__, c__, d__, e__, p_, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__, p_, q_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && ltq!(m_, -1)
                && rubi_int_binomial_scaled_q(
                    &a__, &b__, &c__, &d__, &e__, &m_, &Atom::num(2), &p_, &q_, x_,
                )
        },
        rhs: {
            let first_base = &a__ + &b__ * x_.pow(2);
            let second_base = &c__ + &d__ * x_.pow(2);
            let direct = (&e__ * x_).pow(&m_ + 1)
                * first_base.pow(&p_ + 1)
                * second_base.pow(&q_ + 1)
                / (&a__ * &c__ * &e__ * (&m_ + 1));
            let payload = simp!(
                (&b__ * &c__ + &a__ * &d__) * (&m_ + 3)
                    + Atom::num(2) * (&b__ * &c__ * &p_ + &a__ * &d__ * &q_)
                    + &b__
                        * &d__
                        * (&m_ + Atom::num(2) * &p_ + Atom::num(2) * &q_ + 5)
                        * x_.pow(2),
                x_
            );
            let primitive = rubi_rhs_int(
                &((&e__ * x_).pow(&m_ + 2)
                    * first_base.pow(&p_)
                    * second_base.pow(&q_)
                    * payload),
                x_,
            );
            let multiplier = Atom::num(1) / (&a__ * &c__ * e__.pow(2) * (&m_ + 1));
            rubi_simp(&(direct), x_) - rubi_star(multiplier, primitive)
        },
    ));
}

fn push_rules_rule_383(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, x_);
    rules.push(rubi_rule!(
        order: 383,
        source: "Int[(e_.*x_)^m_./((a_+b_.*x_^2)*(c_+d_.*x_^2)),x_Symbol] :=
          -a*e^2/(b*c-a*d) \\[Star] Int[(e*x)^(m-2)/(a+b*x^2),x] + c*e^2/(b*c-a*d) \\[Star] Int[(e*x)^(m-2)/(c+d*x^2),x] /;
        FreeQ[{a,b,c,d,e,m},x] && NeQ[b*c-a*d,0] && LeQ[2,m,3]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [a__, b__, c__, d__, e__, m_, x_],
        optional: [b__, d__, e__, m_],
        x_free: [a__, b__, c__, d__, e__, m_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && leq!(Atom::num(2), m_, Atom::num(3))
        },
        rhs: {
            let determinant = &b__ * &c__ - &a__ * &d__;
            let first = rubi_rhs_int(
                &((&e__ * x_).pow(&m_ - 2) / (&a__ + &b__ * x_.pow(2))),
                x_,
            );
            let second = rubi_rhs_int(
                &((&e__ * x_).pow(&m_ - 2) / (&c__ + &d__ * x_.pow(2))),
                x_,
            );
            rubi_star(-&a__ * e__.pow(2) / &determinant, first)
                    + rubi_star(&c__ * e__.pow(2) / determinant, second)
        },
    ));
}

fn push_rules_rule_384(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, x_);
    rules.push(rubi_rule!(
        order: 384,
        source: "Int[(e_.*x_)^m_./((a_+b_.*x_^2)*(c_+d_.*x_^2)),x_Symbol] :=
          b/(b*c-a*d) \\[Star] Int[(e*x)^m/(a+b*x^2),x] - d/(b*c-a*d) \\[Star] Int[(e*x)^m/(c+d*x^2),x] /;
        FreeQ[{a,b,c,d,e,m},x] && NeQ[b*c-a*d,0]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [a__, b__, c__, d__, e__, m_, x_],
        optional: [b__, d__, e__, m_],
        x_free: [a__, b__, c__, d__, e__, m_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
        },
        rhs: {
            let determinant = &b__ * &c__ - &a__ * &d__;
            let first = rubi_rhs_int(
                &((&e__ * x_).pow(&m_) / (&a__ + &b__ * x_.pow(2))),
                x_,
            );
            let second = rubi_rhs_int(
                &((&e__ * x_).pow(&m_) / (&c__ + &d__ * x_.pow(2))),
                x_,
            );
            rubi_star(&b__ / &determinant, first)
                    - rubi_star(&d__ / determinant, second)
        },
    ));
}

fn push_rules_rule_385(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, q_, x_);
    rules.push(rubi_rule!(
        order: 385,
        source: "Int[(e_.*x_)^m_*(c_+d_.*x_^2)^q_./(a_+b_.*x_^2),x_Symbol] :=
          e^2/b \\[Star] Int[(e*x)^(m-2)*(c+d*x^2)^q,x] - a*e^2/b \\[Star] Int[(e*x)^(m-2)*(c+d*x^2)^q/(a+b*x^2),x] /;
        FreeQ[{a,b,c,d,e,m,q},x] && NeQ[b*c-a*d,0] && LeQ[2,m,3] && IntBinomialQ[a,b,c,d,e,m,2,-1,q,x]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern: (e__ * x_).pow(m_) * (c__ + d__ * x_.pow(2)).pow(q_) / (a__ + b__ * x_.pow(2)),
        with: [a__, b__, c__, d__, e__, m_, q_, x_],
        optional: [b__, d__, e__, q_],
        x_free: [a__, b__, c__, d__, e__, m_, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, q_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && leq!(Atom::num(2), m_, Atom::num(3))
                && rubi_int_binomial_scaled_q(
                    &a__,
                    &b__,
                    &c__,
                    &d__,
                    &e__,
                    &m_,
                    &Atom::num(2),
                    &(-Atom::num(1)),
                    &q_,
                    x_,
                )
        },
        rhs: {
            let second_base = &c__ + &d__ * x_.pow(2);
            let first = rubi_rhs_int(
                &((&e__ * x_).pow(&m_ - 2) * second_base.pow(&q_)),
                x_,
            );
            let second = rubi_rhs_int(
                &((&e__ * x_).pow(&m_ - 2)
                    * second_base.pow(&q_)
                    / (&a__ + &b__ * x_.pow(2))),
                x_,
            );
            rubi_star(e__.pow(2) / &b__, first)
                    - rubi_star(&a__ * e__.pow(2) / &b__, second)
        },
    ));
}

fn push_rules_rule_386(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, p_, x_);
    rules.push(rubi_rule!(
        order: 386,
        source: "Int[x_*(a_+b_.*x_^2)^p_/(c_+d_.*x_^2),x_Symbol] :=
          b/d \\[Star] Int[x*(a+b*x^2)^(p-1),x] - (b*c-a*d)/d \\[Star] Int[x*(a+b*x^2)^(p-1)/(c+d*x^2),x] /;
        FreeQ[{a,b,c,d},x] && NeQ[b*c-a*d,0] && GtQ[p,0] && IntBinomialQ[a,b,c,d,1,1,2,p,-1,x]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [a__, b__, c__, d__, p_, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && gtq!(p_, 0)
                && rubi_int_binomial_scaled_q(
                    &a__,
                    &b__,
                    &c__,
                    &d__,
                    &Atom::num(1),
                    &Atom::num(1),
                    &Atom::num(2),
                    &p_,
                    &(-Atom::num(1)),
                    x_,
                )
        },
        rhs: {
            let first_base = &a__ + &b__ * x_.pow(2);
            let first = rubi_rhs_int(&(x_ * first_base.pow(&p_ - 1)), x_);
            let second = rubi_rhs_int(
                &(x_ * first_base.pow(&p_ - 1) / (&c__ + &d__ * x_.pow(2))),
                x_,
            );
            rubi_star(&b__ / &d__, first)
                    - rubi_star((&b__ * &c__ - &a__ * &d__) / &d__, second)
        },
    ));
}

fn push_rules_rule_387(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, p_, x_);
    rules.push(rubi_rule!(
        order: 387,
        source: "Int[x_*(a_+b_.*x_^2)^p_/(c_+d_.*x_^2),x_Symbol] :=
          b/(b*c-a*d) \\[Star] Int[x*(a+b*x^2)^(p-1),x] - d/(b*c-a*d) \\[Star] Int[x*(a+b*x^2)^(p+1)/(c+d*x^2),x] /;
        FreeQ[{a,b,c,d},x] && NeQ[b*c-a*d,0] && LtQ[p,-1] && IntBinomialQ[a,b,c,d,1,1,2,p,-1,x]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [a__, b__, c__, d__, p_, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && ltq!(p_, -1)
                && rubi_int_binomial_scaled_q(
                    &a__,
                    &b__,
                    &c__,
                    &d__,
                    &Atom::num(1),
                    &Atom::num(1),
                    &Atom::num(2),
                    &p_,
                    &(-Atom::num(1)),
                    x_,
                )
        },
        rhs: {
            let determinant = &b__ * &c__ - &a__ * &d__;
            let first_base = &a__ + &b__ * x_.pow(2);
            let first = rubi_rhs_int(&(x_ * first_base.pow(&p_ - 1)), x_);
            let second = rubi_rhs_int(
                &(x_ * first_base.pow(&p_ + 1) / (&c__ + &d__ * x_.pow(2))),
                x_,
            );
            rubi_star(&b__ / &determinant, first)
                    - rubi_star(&d__ / determinant, second)
        },
    ));
}

fn push_rules_rule_388(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 388,
        source: "Int[x_^2/(Sqrt[a_+b_.*x_^2]*Sqrt[c_+d_.*x_^2]),x_Symbol] :=
          x*Sqrt[a+b*x^2]/(b*Sqrt[c+d*x^2]) - c/b \\[Star] Int[Sqrt[a+b*x^2]/(c+d*x^2)^(3/2),x] /;
        FreeQ[{a,b,c,d},x] && NeQ[b*c-a*d,0] && PosQ[b/a] && PosQ[d/c] && Not[SimplerSqrtQ[b/a,d/c]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && posq!(&b__ / &a__)
                && posq!(&d__ / &c__)
                && !rubi_simpler_sqrt_q(&(&b__ / &a__), &(&d__ / &c__))
        },
        rhs: {
            let first_base = &a__ + &b__ * x_.pow(2);
            let second_base = &c__ + &d__ * x_.pow(2);
            let direct = x_ * &first_base.sqrt() / (&b__ * &second_base.sqrt());
            let primitive = rubi_rhs_int(
                &(first_base.sqrt() / second_base.pow((3, 2))),
                x_,
            );
            rubi_simp(&(direct), x_) - rubi_star(&c__ / &b__, primitive)
        },
    ));
}

fn push_rules_rule_389(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, x_);
    rules.push(rubi_rule!(
        order: 389,
        source: "Int[x_^2/(Sqrt[a_+b_.*x_^2]*Sqrt[c_+d_.*x_^2]),x_Symbol] :=
          1/b \\[Star] Int[Sqrt[a+b*x^2]/Sqrt[c+d*x^2],x] - a/b \\[Star] Int[1/(Sqrt[a+b*x^2]*Sqrt[c+d*x^2]),x] /;
        FreeQ[{a,b,c,d},x] && NeQ[b*c-a*d,0] && Not[SimplerSqrtQ[-b/a,-d/c]]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [a__, b__, c__, d__, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__],
        when: {
            freeq!([a__, b__, c__, d__], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && !rubi_simpler_sqrt_q(&(-&b__ / &a__), &(-&d__ / &c__))
        },
        rhs: {
            let first_base = &a__ + &b__ * x_.pow(2);
            let second_base = &c__ + &d__ * x_.pow(2);
            let first = rubi_rhs_int(&(&first_base.sqrt() / &second_base.sqrt()), x_);
            let second = rubi_rhs_int(&(Atom::num(1) / (first_base.sqrt() * second_base.sqrt())), x_);
            rubi_star(Atom::num(1) / &b__, first)
                    - rubi_star(&a__ / &b__, second)
        },
    ));
}

fn push_rules_rule_390(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, m_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 390,
        source: "Int[x_^m_.*(a_+b_.*x_^2)^p_*(c_+d_.*x_^2)^q_.,x_Symbol] :=
          With[{k=Denominator[p]},
          k*a^(p+(m+1)/2)/2 \\[Star]
            Subst[Int[x^(k*(m+1)/2-1)*(c-(b*c-a*d)*x^k)^q/(1-b*x^k)^(p+q+(m+1)/2+1),x],x,x^(2/k)/(a+b*x^2)^(1/k)]] /;
        FreeQ[{a,b,c,d},x] && RationalQ[m,p] && IntegersQ[p+(m+1)/2,q] && LtQ[-1,p,0]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_10(symbols),
        with: [a__, b__, c__, d__, m_, p_, q_, x_],
        optional: [b__, d__, m_, q_],
        x_free: [a__, b__, c__, d__],
        when: {
            let shift = &p_ + (&m_ + 1) / 2;
            freeq!([a__, b__, c__, d__], x_)
                && rationalq!([m_, p_])
                && integersq!([shift, q_])
                && ltq!(-1, p_, 0)
        },
        rhs: {
            let k = Atom::num(rational_denominator(&p_).rubi_rhs());
            let exponent_sum = &p_ + (&m_ + 1) / 2;
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = sub_atom.pow(&k * (&m_ + 1) / 2 - 1)
                * (&c__ - (&b__ * &c__ - &a__ * &d__) * sub_atom.pow(&k)).pow(&q_)
                / (Atom::num(1) - &b__ * sub_atom.pow(&k))
                    .pow(&p_ + &q_ + (&m_ + 1) / 2 + 1);
            let primitive = rubi_rhs_int(&transformed_integrand, sub);
            let substituted = rubi_subst(
                &primitive,
                sub,
                x_.pow(Atom::num(2) / &k)
                    / (&a__ + &b__ * x_.pow(2)).pow(Atom::num(1) / &k),
            );
            let multiplier = &k * a__.pow(exponent_sum) / 2;
            rubi_star(multiplier, substituted)
        },
    ));
}

fn push_rules_rule_391(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, m_, x_);
    rules.push(rubi_rule!(
        order: 391,
        source: "Int[x_^m_/((a_+b_.*x_^2)*(c_+d_.*x_^2)),x_Symbol] :=
          -a/(b*c-a*d) \\[Star] Int[x^(m-2)/(a+b*x^2),x] + c/(b*c-a*d) \\[Star] Int[x^(m-2)/(c+d*x^2),x] /;
        FreeQ[{a,b,c,d,m},x] && NeQ[b*c-a*d,0] && (EqQ[m,2] || EqQ[m,3])",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern: x_.pow(m_) / ((a__ + b__ * x_.pow(2)) * (c__ + d__ * x_.pow(2))),
        with: [a__, b__, c__, d__, m_, x_],
        optional: [b__, d__],
        x_free: [a__, b__, c__, d__, m_],
        when: {
            freeq!([a__, b__, c__, d__, m_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && (eqq!(m_, 2) || eqq!(m_, 3))
        },
        rhs: {
            let determinant = &b__ * &c__ - &a__ * &d__;
            let first = rubi_rhs_int(
                &(x_.pow(&m_ - 2) / (&a__ + &b__ * x_.pow(2))),
                x_,
            );
            let second = rubi_rhs_int(
                &(x_.pow(&m_ - 2) / (&c__ + &d__ * x_.pow(2))),
                x_,
            );
            rubi_star(-&a__ / &determinant, first)
                    + rubi_star(&c__ / determinant, second)
        },
    ));
}

fn push_rules_rule_392(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 392,
        source: "Int[(e_.*x_)^m_.*(a_+b_.*x_^2)^p_*(c_+d_.*x_^2)^q_,x_Symbol] :=
          Int[ExpandIntegrand[(e*x)^m*(a+b*x^2)^p*(c+d*x^2)^q,x],x] /;
        FreeQ[{a,b,c,d,e,m},x] && NeQ[b*c-a*d,0] && IGtQ[p,-2] && (IGtQ[q,-2] || EqQ[q,-3] && IntegerQ[(m-1)/2])",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, m_, p_, q_, x_],
        optional: [b__, d__, e__, m_],
        x_free: [a__, b__, c__, d__, e__, m_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && igtq!(p_, -2)
                && (igtq!(q_, -2) || eqq!(q_, -3) && integerq!((&m_ - 1) / 2))
        },
        rhs: {
            let integrand = (&e__ * x_).pow(&m_)
                * (&a__ + &b__ * x_.pow(2)).pow(&p_)
                * (&c__ + &d__ * x_.pow(2)).pow(&q_);
            let expanded = rubi_expand_integrand(&integrand, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_393(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 393,
        source: "Int[(e_.*x_)^m_.*(a_+b_.*x_^2)^p_.*(c_+d_.*x_^2)^q_.,x_Symbol] :=
          (e*x)^m/(2*x*(x^2)^(Simplify[(m+1)/2]-1)) \\[Star] Subst[Int[x^(Simplify[(m+1)/2]-1)*(a+b*x)^p*(c+d*x)^q,x],x,x^2] /;
        FreeQ[{a,b,c,d,e,m,p,q},x] && NeQ[b*c-a*d,0] && IntegerQ[Simplify[m+2*p]] && Not[IntegerQ[m]]",
        desc: "Substitute a new variable and integrate the transformed expression.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, m_, p_, q_, x_],
        optional: [b__, d__, e__, m_, p_, q_],
        x_free: [a__, b__, c__, d__, e__, m_, p_, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, p_, q_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && integerq!(rubi_simplify(&(&m_ + Atom::num(2) * &p_)))
                && !integerq!(m_)
        },
        rhs: {
            let simplified_half = rubi_simplify(&((&m_ + 1) / 2));
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let primitive = rubi_rhs_int(
                &(sub_atom.pow(&simplified_half - 1)
                    * (&a__ + &b__ * &sub_atom).pow(&p_)
                    * (&c__ + &d__ * &sub_atom).pow(&q_)),
                sub,
            );
            let substituted = rubi_subst(&primitive, sub, x_.pow(2));
            let multiplier = (&e__ * x_).pow(&m_)
                / (Atom::num(2) * x_ * x_.pow(2).pow(&simplified_half - 1));
            rubi_star(multiplier, substituted)
        },
    ));
}

fn push_rules_rule_394(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 394,
        source: "Int[(e_.*x_)^m_.*(a_+b_.*x_^2)^p_*(c_+d_.*x_^2)^q_,x_Symbol] :=
          a^p*c^q*(e*x)^(m+1)/(e*(m+1))*AppellF1[(m+1)/2,-p,-q,1+(m+1)/2,-b*x^2/a,-d*x^2/c] /;
        FreeQ[{a,b,c,d,e,m,p,q},x] && NeQ[b*c-a*d,0] && NeQ[m,-1] && NeQ[m,1] && (IntegerQ[p] || GtQ[a,0]) && (IntegerQ[q] || GtQ[c,0])",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, m_, p_, q_, x_],
        optional: [b__, d__, e__, m_],
        x_free: [a__, b__, c__, d__, e__, m_, p_, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, p_, q_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && neq!(m_, -1)
                && neq!(m_, 1)
                && (integerq!(p_) || gtq!(a__, 0))
                && (integerq!(q_) || gtq!(c__, 0))
        },
        rhs: {
            let half = (&m_ + 1) / 2;
            rubi_simp(&(a__.pow(&p_)
                    * c__.pow(&q_)
                    * (&e__ * x_).pow(&m_ + 1)
                    * rubi_appell_f1(
                        &half,
                        -&p_,
                        -&q_,
                        Atom::num(1) + &half,
                        -&b__ * x_.pow(2) / &a__,
                        -&d__ * x_.pow(2) / &c__,
                    )
                    / (&e__ * (&m_ + 1))), x_)
        },
    ));
}

fn push_rules_rule_395(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 395,
        source: "Int[(e_.*x_)^m_.*(a_+b_.*x_^2)^p_*(c_+d_.*x_^2)^q_,x_Symbol] :=
          a^IntPart[p]*(a+b*x^2)^FracPart[p]/(1+b*x^2/a)^FracPart[p] \\[Star] Int[(e*x)^m*(1+b*x^2/a)^p*(c+d*x^2)^q,x] /;
        FreeQ[{a,b,c,d,e,m,p,q},x] && NeQ[b*c-a*d,0] && NeQ[m,-1] && NeQ[m,1] && Not[IntegerQ[p] || GtQ[a,0]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, b__, c__, d__, e__, m_, p_, q_, x_],
        optional: [b__, d__, e__, m_],
        x_free: [a__, b__, c__, d__, e__, m_, p_, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__, m_, p_, q_], x_)
                && neq!(&b__ * &c__ - &a__ * &d__, 0)
                && neq!(m_, -1)
                && neq!(m_, 1)
                && !(integerq!(p_) || gtq!(a__, 0))
        },
        rhs: {
            let first_base = &a__ + &b__ * x_.pow(2);
            let normalized = Atom::num(1) + &b__ * x_.pow(2) / &a__;
            let multiplier = a__.pow(rubi_int_part(&p_))
                * first_base.pow(rubi_frac_part(&p_))
                / normalized.pow(rubi_frac_part(&p_));
            let primitive = rubi_rhs_int(
                &((&e__ * x_).pow(&m_)
                    * normalized.pow(&p_)
                    * (&c__ + &d__ * x_.pow(2)).pow(&q_)),
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
    let e__ = symbols.e__;
    let m_ = symbols.m_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (e__ * x_).pow(m_) * (a__ + b__ * x_.pow(2)).pow(p_) * (c__ + d__ * x_.pow(2))
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let m_ = symbols.m_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (e__ * x_).pow(m_) * (a__ + b__ * x_.pow(2)).pow(p_) * (c__ + d__ * x_.pow(2)).pow(2)
}

#[inline(never)]
fn rubi_shared_pattern_2(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let m_ = symbols.m_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (e__ * x_).pow(m_) * (a__ + b__ * x_.pow(2)).pow(p_) * (c__ + d__ * x_.pow(2)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_3(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let m_ = symbols.m_;
    let p_ = symbols.p_;
    let q_ = symbols.q_;
    let x_ = symbols.x_;
    (e__ * x_).pow(m_) * (a__ + b__ * x_.pow(2)).pow(p_) * (c__ + d__ * x_.pow(2)).pow(q_)
}

#[inline(never)]
fn rubi_shared_pattern_4(symbols: &RubiSymbols) -> Atom {
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let m_ = symbols.m_;
    let p_ = symbols.p_;
    let q_ = symbols.q_;
    let x_ = symbols.x_;
    (e__ * x_).pow(m_) * (b__ * x_.pow(2)).pow(p_) * (c__ + d__ * x_.pow(2)).pow(q_)
}

#[inline(never)]
fn rubi_shared_pattern_5(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let m_ = symbols.m_;
    let x_ = symbols.x_;
    (e__ * x_).pow(m_) / ((a__ + b__ * x_.pow(2)) * (c__ + d__ * x_.pow(2)))
}

#[inline(never)]
fn rubi_shared_pattern_6(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    x_ * (a__ + b__ * x_.pow(2)).pow(p_) / (c__ + d__ * x_.pow(2))
}

#[inline(never)]
fn rubi_shared_pattern_7(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let x_ = symbols.x_;
    x_.pow(2) / ((a__ + b__ * x_.pow(2)).pow((3, 4)) * (c__ + d__ * x_.pow(2)))
}

#[inline(never)]
fn rubi_shared_pattern_8(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let x_ = symbols.x_;
    x_.pow(2) / ((a__ + b__ * x_.pow(2)).sqrt() * (c__ + d__ * x_.pow(2)).sqrt())
}

#[inline(never)]
fn rubi_shared_pattern_9(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let m_ = symbols.m_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    x_.pow(m_) * (a__ + b__ * x_.pow(2)).pow(p_) * (c__ + d__ * x_.pow(2))
}

#[inline(never)]
fn rubi_shared_pattern_10(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let m_ = symbols.m_;
    let p_ = symbols.p_;
    let q_ = symbols.q_;
    let x_ = symbols.x_;
    x_.pow(m_) * (a__ + b__ * x_.pow(2)).pow(p_) * (c__ + d__ * x_.pow(2)).pow(q_)
}
