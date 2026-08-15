use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_3721(rules);
    push_rules_rule_3722(rules);
    push_rules_rule_3723(rules);
    push_rules_rule_3724(rules);
}

fn push_rules_rule_3721(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 3721,
        source: "Int[sin[d_.+e_.*x_]^m_*(a_+b_.*cos[d_.+e_.*x_]^p_+c_.*sin[d_.+e_.*x_]^q_)^n_,x_Symbol] :=
          Module[{f=FreeFactors[Cot[d+e*x],x]},
          -f/e \\[Star] Subst[Int[ExpandToSum[c+b*(1+f^2*x^2)^(q/2-p/2)+a*(1+f^2*x^2)^(q/2),x]^n/(1+f^2*x^2)^(m/2+n*q/2+1),x],x,Cot[d+e*x]/f]] /;
        FreeQ[{a,b,c,d,e},x] && IntegerQ[m/2] && IntegerQ[p/2] && IntegerQ[q/2] && IntegerQ[n] && GtQ[p,0] && LeQ[p,q]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, e__, m_, p_, q_, n_, x_],
        optional: [b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && integerq!(&m_ / 2)
                && integerq!(&p_ / 2)
                && integerq!(&q_ / 2)
                && integerq!(n_)
                && gtq!(p_, 0)
                && leq!(p_, q_)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let z = Atom::var(sub);
            let angle = &d__ + &e__ * x_;
            let cot = angle.cot();
            let ff = rubi_free_factors(&cot, x_);
            let base = Atom::num(1) + ff.pow(2) * z.pow(2);
            let expand_to_sum = rubi_expand_to_sum(
                &(&c__ + &b__ * base.pow(&q_ / 2 - &p_ / 2) + &a__ * base.pow(&q_ / 2)),
                sub,
            );
            let transformed = expand_to_sum.pow(&n_) / base.pow(&m_ / 2 + &n_ * &q_ / 2 + 1);
            let primitive = rubi_rhs_int(&transformed, sub);

            rubi_star(-&ff / &e__, rubi_subst(&primitive, sub, cot / &ff))
        },
    ));
}

fn push_rules_rule_3722(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 3722,
        source: "Int[cos[d_.+e_.*x_]^m_*(a_+b_.*sin[d_.+e_.*x_]^p_+c_.*cos[d_.+e_.*x_]^q_)^n_,x_Symbol] :=
          Module[{f=FreeFactors[Tan[d+e*x],x]},
          f/e \\[Star] Subst[Int[ExpandToSum[c+b*(1+f^2*x^2)^(q/2-p/2)+a*(1+f^2*x^2)^(q/2),x]^n/(1+f^2*x^2)^(m/2+n*q/2+1),x],x,Tan[d+e*x]/f]] /;
        FreeQ[{a,b,c,d,e},x] && IntegerQ[m/2] && IntegerQ[p/2] && IntegerQ[q/2] && IntegerQ[n] && GtQ[p,0] && LeQ[p,q]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, e__, m_, p_, q_, n_, x_],
        optional: [b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && integerq!(&m_ / 2)
                && integerq!(&p_ / 2)
                && integerq!(&q_ / 2)
                && integerq!(n_)
                && gtq!(p_, 0)
                && leq!(p_, q_)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let z = Atom::var(sub);
            let angle = &d__ + &e__ * x_;
            let tan = angle.tan();
            let ff = rubi_free_factors(&tan, x_);
            let base = Atom::num(1) + ff.pow(2) * z.pow(2);
            let expand_to_sum = rubi_expand_to_sum(
                &(&c__ + &b__ * base.pow(&q_ / 2 - &p_ / 2) + &a__ * base.pow(&q_ / 2)),
                sub,
            );
            let transformed = expand_to_sum.pow(&n_) / base.pow(&m_ / 2 + &n_ * &q_ / 2 + 1);
            let primitive = rubi_rhs_int(&transformed, sub);

            rubi_star(&ff / &e__, rubi_subst(&primitive, sub, tan / &ff))
        },
    ));
}

fn push_rules_rule_3723(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 3723,
        source: "Int[sin[d_.+e_.*x_]^m_*(a_+b_.*cos[d_.+e_.*x_]^p_+c_.*sin[d_.+e_.*x_]^q_)^n_,x_Symbol] :=
          Module[{f=FreeFactors[Cot[d+e*x],x]},
          -f/e \\[Star] Subst[Int[ExpandToSum[a*(1+f^2*x^2)^(p/2)+b*f^p*x^p+c*(1+f^2*x^2)^(p/2-q/2),x]^n/(1+f^2*x^2)^(m/2+n*p/2+1),x],x,
            Cot[d+e*x]/f]] /;
        FreeQ[{a,b,c,d,e},x] && IntegerQ[m/2] && IntegerQ[p/2] && IntegerQ[q/2] && IntegerQ[n] && LtQ[0,q,p]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, b__, c__, d__, e__, m_, p_, q_, n_, x_],
        optional: [b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && integerq!(&m_ / 2)
                && integerq!(&p_ / 2)
                && integerq!(&q_ / 2)
                && integerq!(n_)
                && ltq!(0, q_, p_)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let z = Atom::var(sub);
            let angle = &d__ + &e__ * x_;
            let cot = angle.cot();
            let ff = rubi_free_factors(&cot, x_);
            let base = Atom::num(1) + ff.pow(2) * z.pow(2);
            let expand_to_sum = rubi_expand_to_sum(
                &(&a__ * base.pow(&p_ / 2)
                    + &b__ * ff.pow(&p_) * z.pow(&p_)
                    + &c__ * base.pow(&p_ / 2 - &q_ / 2)),
                sub,
            );
            let transformed = expand_to_sum.pow(&n_) / base.pow(&m_ / 2 + &n_ * &p_ / 2 + 1);
            let primitive = rubi_rhs_int(&transformed, sub);

            rubi_star(-&ff / &e__, rubi_subst(&primitive, sub, cot / &ff))
        },
    ));
}

fn push_rules_rule_3724(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 3724,
        source: "Int[cos[d_.+e_.*x_]^m_*(a_+b_.*sin[d_.+e_.*x_]^p_+c_.*cos[d_.+e_.*x_]^q_)^n_,x_Symbol] :=
          Module[{f=FreeFactors[Tan[d+e*x],x]},
          f/e \\[Star] Subst[Int[ExpandToSum[a*(1+f^2*x^2)^(p/2)+b*f^p*x^p+c*(1+f^2*x^2)^(p/2-q/2),x]^n/(1+f^2*x^2)^(m/2+n*p/2+1),x],x,
            Tan[d+e*x]/f]] /;
        FreeQ[{a,b,c,d,e},x] && IntegerQ[m/2] && IntegerQ[p/2] && IntegerQ[q/2] && IntegerQ[n] && LtQ[0,q,p]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, e__, m_, p_, q_, n_, x_],
        optional: [b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && integerq!(&m_ / 2)
                && integerq!(&p_ / 2)
                && integerq!(&q_ / 2)
                && integerq!(n_)
                && ltq!(0, q_, p_)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let z = Atom::var(sub);
            let angle = &d__ + &e__ * x_;
            let tan = angle.tan();
            let ff = rubi_free_factors(&tan, x_);
            let base = Atom::num(1) + ff.pow(2) * z.pow(2);
            let expand_to_sum = rubi_expand_to_sum(
                &(&a__ * base.pow(&p_ / 2)
                    + &b__ * ff.pow(&p_) * z.pow(&p_)
                    + &c__ * base.pow(&p_ / 2 - &q_ / 2)),
                sub,
            );
            let transformed = expand_to_sum.pow(&n_) / base.pow(&m_ / 2 + &n_ * &p_ / 2 + 1);
            let primitive = rubi_rhs_int(&transformed, sub);

            rubi_star(&ff / &e__, rubi_subst(&primitive, sub, tan / &ff))
        },
    ));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn downvalues_3721_through_3724_are_registered_once_in_order() {
        let _ = symbol!("x");
        let mut rules = Vec::new();
        push_rules(&mut rules);
        let orders = rules
            .iter()
            .filter_map(|rule| rule.downvalue_order)
            .filter(|order| (3721..=3724).contains(order))
            .collect::<Vec<_>>();
        assert_eq!(orders, (3721..=3724).collect::<Vec<_>>());
    }
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
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let q_ = symbols.q_;
    let x_ = symbols.x_;
    i_cos(d__ + e__ * x_).pow(m_)
        * (a__ + b__ * i_sin(d__ + e__ * x_).pow(p_) + c__ * i_cos(d__ + e__ * x_).pow(q_)).pow(n_)
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
    let q_ = symbols.q_;
    let x_ = symbols.x_;
    i_sin(d__ + e__ * x_).pow(m_)
        * (a__ + b__ * i_cos(d__ + e__ * x_).pow(p_) + c__ * i_sin(d__ + e__ * x_).pow(q_)).pow(n_)
}
