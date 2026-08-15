use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_1381(rules);
    push_rules_rule_1382(rules);
    push_rules_rule_1383(rules);
    push_rules_rule_1386(rules);
    push_rules_rule_1387(rules);
    push_rules_rule_1388(rules);
    push_rules_rule_1395(rules);
    push_rules_rule_1396(rules);
    push_rules_rule_1727(rules);
    push_rules_rule_1728(rules);
    push_rules_rule_1729(rules);
    push_rules_rule_1730(rules);
    push_rules_rule_1731(rules);
    push_rules_rule_1732(rules);
    push_rules_rule_1733(rules);
    push_rules_rule_1734(rules);
    push_rules_rule_1735(rules);
    push_rules_rule_1736(rules);
    push_rules_rule_1737(rules);
    push_rules_rule_1738(rules);
    push_rules_rule_1739(rules);
    push_rules_rule_1740(rules);
    push_rules_rule_1741(rules);
    push_rules_rule_1742(rules);
    push_rules_rule_1743(rules);
    push_rules_rule_1744(rules);
    push_rules_rule_1745(rules);
    push_rules_rule_1746(rules);
    push_rules_rule_1747(rules);
    push_rules_rule_1748(rules);
    push_rules_rule_1749(rules);
    push_rules_rule_1750(rules);
    push_rules_rule_1751(rules);
    push_rules_rule_1752(rules);
    push_rules_rule_1753(rules);
    push_rules_rule_1754(rules);
    push_rules_rule_1755(rules);
    push_rules_rule_1756(rules);
    push_rules_rule_1757(rules);
    push_rules_rule_1758(rules);
    push_rules_rule_1759(rules);
    push_rules_rule_1760(rules);
    push_rules_rule_1761(rules);
    push_rules_rule_1762(rules);
    push_rules_rule_1763(rules);
    push_rules_rule_1764(rules);
    push_rules_rule_1765(rules);
    push_rules_rule_1766(rules);
    push_rules_rule_1767(rules);
    push_rules_rule_1768(rules);
    push_rules_rule_1769(rules);
    push_rules_rule_1770(rules);
    push_rules_rule_1771(rules);
    push_rules_rule_1772(rules);
    push_rules_rule_1773(rules);
    push_rules_rule_1774(rules);
    push_rules_rule_1775(rules);
    push_rules_rule_1776(rules);
    push_rules_rule_1777(rules);
    push_rules_rule_1778(rules);
    push_rules_rule_1779(rules);
    push_rules_rule_1780(rules);
    push_rules_rule_1781(rules);
    push_rules_rule_1782(rules);
    push_rules_rule_1783(rules);
    push_rules_rule_1784(rules);
    push_rules_rule_1785(rules);
    push_rules_rule_1786(rules);
    push_rules_rule_1787(rules);
    push_rules_rule_1788(rules);
    push_rules_rule_1789(rules);
    push_rules_rule_1790(rules);
    push_rules_rule_1791(rules);
}

fn push_rules_rule_1381(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, n2_, p_, q_, u__, x_);
    rules.push(rubi_rule!(
        order: 1381,
        source: "Int[u_.*(d_+e_.*x_^n_)^q_*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
          e^q/c^(q/2) \\[Star] Int[u*(a+b*x^n+c*x^(2*n))^(p+q/2),x] /;
        FreeQ[{a,b,c,d,e,n,p,q},x] && EqQ[n2,2*n] && EqQ[b^2-4*a*c,0] && EqQ[2*c*d-b*e,0] && Not[IntegerQ[p]] && IntegerQ[q/2]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_19(symbols),
        with: [u__, a__, b__, c__, d__, e__, n_, n2_, p_, q_, x_],
        optional: [u__, b__, c__, e__, n2_],
        x_free: [a__, b__, c__, d__, e__, n_, p_, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__, n_, p_, q_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && eqq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && eqq!(Atom::num(2) * &c__ * &d__ - &b__ * &e__, 0)
                && !integerq!(p_)
                && integerq!(&q_ / Atom::num(2))
        },
        rhs: {
            let trinomial =
                &a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_);
            let recursive_integrand =
                &u__ * trinomial.pow(&p_ + &q_ / Atom::num(2));
            rubi_star(e__.pow(&q_) / c__.pow(&q_ / Atom::num(2)), rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1382(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, n2_, p_, q_, u__, x_);
    rules.push(rubi_rule!(
        order: 1382,
        source: "Int[u_.*(d_+e_.*x_^n_)^q_*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
          e^(q-1)/c^((q-1)/2) \\[Star] Int[u*(d+e*x^n)*(a+b*x^n+c*x^(2*n))^(p+(q-1)/2),x] /;
        FreeQ[{a,b,c,d,e,p},x] && EqQ[b^2-4*a*c,0] && EqQ[2*c*d-b*e,0] && Not[IntegerQ[p]] && IntegerQ[(q-1)/2]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_19(symbols),
        with: [u__, a__, b__, c__, d__, e__, n_, n2_, p_, q_, x_],
        optional: [u__, b__, c__, e__, n2_],
        x_free: [a__, b__, c__, d__, e__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, p_], x_)
                && eqq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && eqq!(Atom::num(2) * &c__ * &d__ - &b__ * &e__, 0)
                && !integerq!(p_)
                && integerq!((&q_ - Atom::num(1)) / Atom::num(2))
        },
        rhs: {
            let half_q_minus_one = (&q_ - Atom::num(1)) / Atom::num(2);
            let binomial = &d__ + &e__ * x_.pow(&n_);
            let trinomial =
                &a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_);
            let recursive_integrand =
                &u__ * &binomial * trinomial.pow(&p_ + &half_q_minus_one);
            rubi_star(e__.pow(&q_ - Atom::num(1)) / c__.pow(&half_q_minus_one), rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1386(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, n_, n2_, p_, q_, u__, x_);
    rules.push(rubi_rule!(
        order: 1386,
        source: "Int[u_.*(d_+e_.*x_^n_)^q_.*(a_+c_.*x_^n2_.)^p_.,x_Symbol] :=
          (-e^2/c)^q \\[Star] Int[u*(d-e*x^n)^p,x] /;
        FreeQ[{a,c,d,e,n,p,q},x] && EqQ[n2,2*n] && EqQ[c*d^2+a*e^2,0] && EqQ[p+q,0] && GtQ[d,0] && LtQ[c,0] && GtQ[e^2,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_20(symbols),
        with: [u__, a__, c__, d__, e__, n_, n2_, p_, q_, x_],
        optional: [u__, c__, e__, n2_, p_, q_],
        x_free: [a__, c__, d__, e__, n_, p_, q_],
        scaled: [(n2_, 2, n_)],
        when: {
            freeq!([a__, c__, d__, e__, n_, p_, q_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && eqq!(&c__ * d__.pow(2) + &a__ * e__.pow(2), 0)
                && eqq!(&p_ + &q_, 0)
                && gtq!(d__, 0)
                && ltq!(c__, 0)
                && gtq!(e__.pow(2), 0)
        },
        rhs: {
            let recursive_integrand =
                &u__ * (&d__ - &e__ * x_.pow(&n_)).pow(&p_);
            rubi_star((-e__.pow(2) / &c__).pow(&q_), rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1387(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, n2_, p_, q_, u__, x_);
    rules.push(rubi_rule!(
        order: 1387,
        source: "Int[u_.*(d_+e_.*x_^n_)^q_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_.,x_Symbol] :=
          Int[u*(d+e*x^n)^(p+q)*(a/d+c/e*x^n)^p,x] /;
        FreeQ[{a,b,c,d,e,n,p,q},x] && EqQ[n2,2*n] && EqQ[c*d^2-b*d*e+a*e^2,0] && (IntegerQ[p] || GtQ[a,0] && GtQ[d,0] && LtQ[c,0])",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_19(symbols),
        with: [u__, a__, b__, c__, d__, e__, n_, n2_, p_, q_, x_],
        optional: [u__, b__, c__, e__, n2_, p_, q_],
        x_free: [a__, b__, c__, d__, e__, n_, p_, q_],
        scaled: [(n2_, 2, n_)],
        when: {
            freeq!([a__, b__, c__, d__, e__, n_, p_, q_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && eqq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && (integerq!(p_)
                    || gtq!(a__, 0) && gtq!(d__, 0) && ltq!(c__, 0))
        },
        rhs: {
            let recursive_integrand = &u__
                * (&d__ + &e__ * x_.pow(&n_)).pow(&p_ + &q_)
                * (&a__ / &d__ + &c__ * x_.pow(&n_) / &e__).pow(&p_);
            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_1388(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, n_, n2_, p_, q_, u__, x_);
    rules.push(rubi_rule!(
        order: 1388,
        source: "Int[u_.*(d_+e_.*x_^n_)^q_.*(a_+c_.*x_^n2_.)^p_.,x_Symbol] :=
          Int[u*(d+e*x^n)^(p+q)*(a/d+c/e*x^n)^p,x] /;
        FreeQ[{a,c,d,e,n,p,q},x] && EqQ[n2,2*n] && EqQ[c*d^2+a*e^2,0] && (IntegerQ[p] || GtQ[a,0] && GtQ[d,0])",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_20(symbols),
        with: [u__, a__, c__, d__, e__, n_, n2_, p_, q_, x_],
        optional: [u__, c__, e__, n2_, p_, q_],
        x_free: [a__, c__, d__, e__, n_, p_, q_],
        scaled: [(n2_, 2, n_)],
        when: {
            freeq!([a__, c__, d__, e__, n_, p_, q_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && eqq!(&c__ * d__.pow(2) + &a__ * e__.pow(2), 0)
                && (integerq!(p_) || gtq!(a__, 0) && gtq!(d__, 0))
        },
        rhs: {
            let recursive_integrand = &u__
                * (&d__ + &e__ * x_.pow(&n_)).pow(&p_ + &q_)
                * (&a__ / &d__ + &c__ * x_.pow(&n_) / &e__).pow(&p_);
            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_1383(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, n2_, p_, q_, u__, x_);
    rules.push(rubi_rule!(
        order: 1383,
        source: "Int[u_.*(d_+e_.*x_^n_)^q_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
          (a+b*x^n+c*x^(2*n))^p/(d+e*x^n)^(2*p) \\[Star] Int[u (d+e*x^n)^(q+2*p),x] /;
        FreeQ[{a,b,c,d,e,n,p,q},x] && EqQ[n2,2*n] && EqQ[b^2-4*a*c,0] && EqQ[2*c*d-b*e,0] && Not[IntegerQ[p]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_19(symbols),
        with: [u__, d__, e__, n_, q_, a__, b__, c__, n2_, p_, x_],
        optional: [u__, e__, q_, b__, c__, n2_],
        x_free: [a__, b__, c__, d__, e__, n_, p_, q_],
        scaled: [(n2_, 2, n_)],
        when: {
            freeq!([a__, b__, c__, d__, e__, n_, p_, q_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && eqq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && !integerq!(p_)
                && eqq!(Atom::num(2) * &c__ * &d__ - &b__ * &e__, 0)
        },
        rhs: {
            let binomial = &d__ + &e__ * x_.pow(&n_);
            let trinomial = &a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_);
            let factor = trinomial.pow(&p_) / binomial.pow(Atom::num(2) * &p_);
            let recursive_integrand = &u__ * binomial.pow(&q_ + Atom::num(2) * &p_);
            rubi_star(factor, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1727(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, n2_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1727,
        source: "Int[(d_+e_.*x_^n_)^q_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_.,x_Symbol] :=
          Int[x^(n*(2*p+q))*(e+d*x^(-n))^q*(c+b*x^(-n)+a*x^(-2*n))^p,x] /;
        FreeQ[{a,b,c,d,e,n},x] && EqQ[n2,2*n] && IntegersQ[p,q] && NegQ[n]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [d__, e__, n_, q_, a__, b__, c__, n2_, p_, x_],
        optional: [e__, q_, b__, c__, n2_, p_],
        x_free: [a__, b__, c__, d__, e__, n_],
        integer: [p_, q_],
        scaled: [(n2_, 2, n_)],
        when: {
            freeq!([a__, b__, c__, d__, e__, n_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && integersq!([p_, q_])
                && negq!(n_)
        },
        rhs: {
            let recursive_integrand = x_.pow(&n_ * (Atom::num(2) * &p_ + &q_))
                * (&e__ + &d__ * x_.pow(-&n_)).pow(&q_)
                * (&c__ + &b__ * x_.pow(-&n_) + &a__ * x_.pow(Atom::num(-2) * &n_)).pow(&p_);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_1728(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, n_, n2_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1728,
        source: "Int[(d_+e_.*x_^n_)^q_.*(a_+c_.*x_^n2_.)^p_.,x_Symbol] :=
          Int[x^(n*(2*p+q))*(e+d*x^(-n))^q*(c+a*x^(-2*n))^p,x] /;
        FreeQ[{a,c,d,e,n},x] && EqQ[n2,2*n] && IntegersQ[p,q] && NegQ[n]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_12(symbols),
        with: [d__, e__, n_, q_, a__, c__, n2_, p_, x_],
        optional: [e__, q_, c__, n2_, p_],
        x_free: [a__, c__, d__, e__, n_],
        integer: [p_, q_],
        scaled: [(n2_, 2, n_)],
        when: {
            freeq!([a__, c__, d__, e__, n_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && integersq!([p_, q_])
                && negq!(n_)
        },
        rhs: {
            let recursive_integrand = x_.pow(&n_ * (Atom::num(2) * &p_ + &q_))
                * (&e__ + &d__ * x_.pow(-&n_)).pow(&q_)
                * (&c__ + &a__ * x_.pow(Atom::num(-2) * &n_)).pow(&p_);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_1729(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, n2_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1729,
        source: "Int[(d_+e_.*x_^n_)^q_.*(a_.+b_.*x_^n_+c_.*x_^n2_)^p_,x_Symbol] :=
          -Subst[Int[(d+e*x^(-n))^q*(a+b*x^(-n)+c*x^(-2*n))^p/x^2,x],x,1/x] /;
        FreeQ[{a,b,c,d,e,p,q},x] && EqQ[n2,2*n] && ILtQ[n,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [d__, e__, n_, q_, a__, b__, c__, n2_, p_, x_],
        optional: [e__, q_, a__, b__, c__],
        x_free: [a__, b__, c__, d__, e__, n_, p_, q_],
        integer_lt: [(n_, 0)],
        scaled: [(n2_, 2, n_)],
        when: {
            freeq!([a__, b__, c__, d__, e__, p_, q_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && iltq!(n_, 0)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = (&d__ + &e__ * sub_atom.pow(-&n_)).pow(&q_)
                * (&a__ + &b__ * sub_atom.pow(-&n_) + &c__ * sub_atom.pow(Atom::num(-2) * &n_)).pow(&p_)
                / sub_atom.pow(2);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);

            -rubi_subst(&transformed, sub, Atom::num(1) / x_)
        },
    ));
}

fn push_rules_rule_1730(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, n_, n2_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1730,
        source: "Int[(d_+e_.*x_^n_)^q_.*(a_+c_.*x_^n2_)^p_,x_Symbol] :=
          -Subst[Int[(d+e*x^(-n))^q*(a+c*x^(-2*n))^p/x^2,x],x,1/x] /;
        FreeQ[{a,c,d,e,p,q},x] && EqQ[n2,2*n] && ILtQ[n,0]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_12(symbols),
        with: [d__, e__, n_, q_, a__, c__, n2_, p_, x_],
        optional: [e__, q_, c__],
        x_free: [a__, c__, d__, e__, n_, p_, q_],
        when: {
            freeq!([a__, c__, d__, e__, p_, q_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && iltq!(n_, 0)
        },
        rhs: {
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = (&d__ + &e__ * sub_atom.pow(-&n_)).pow(&q_)
                * (&a__ + &c__ * sub_atom.pow(Atom::num(-2) * &n_)).pow(&p_)
                / sub_atom.pow(2);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);

            -rubi_subst(&transformed, sub, Atom::num(1) / x_)
        },
    ));
}

fn push_rules_rule_1731(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, n2_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1731,
        source: "Int[(d_+e_.*x_^n_)^q_.*(a_.+b_.*x_^n_+c_.*x_^n2_.)^p_.,x_Symbol] :=
          With[{g=Denominator[n]},
          g \\[Star] Subst[Int[x^(g-1)*(d+e*x^(g*n))^q*(a+b*x^(g*n)+c*x^(2*g*n))^p,x],x,x^(1/g)]] /;
        FreeQ[{a,b,c,d,e,p,q},x] && EqQ[n2,2*n] && FractionQ[n]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [d__, e__, n_, q_, a__, b__, c__, n2_, p_, x_],
        optional: [e__, q_, a__, b__, c__, n2_, p_],
        x_free: [a__, b__, c__, d__, e__, n_, p_, q_],
        scaled: [(n2_, 2, n_)],
        when: {
            freeq!([a__, b__, c__, d__, e__, p_, q_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && fractionq!(n_)
        },
        rhs: {
            let g_i = rubi_denominator(&n_).unwrap();
            let g = Atom::num(g_i);
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = sub_atom.pow(&g - Atom::num(1))
                * (&d__ + &e__ * sub_atom.pow(&g * &n_)).pow(&q_)
                * (&a__
                    + &b__ * sub_atom.pow(&g * &n_)
                    + &c__ * sub_atom.pow(Atom::num(2) * &g * &n_))
                .pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);
            let substituted =
                rubi_subst(&transformed, sub, x_.pow(Atom::num(1) / &g));

            rubi_star(g, substituted)
        },
    ));
}

fn push_rules_rule_1732(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, n_, n2_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1732,
        source: "Int[(d_+e_.*x_^n_)^q_.*(a_+c_.*x_^n2_.)^p_.,x_Symbol] :=
          With[{g=Denominator[n]},
          g \\[Star] Subst[Int[x^(g-1)*(d+e*x^(g*n))^q*(a+c*x^(2*g*n))^p,x],x,x^(1/g)]] /;
        FreeQ[{a,c,d,e,p,q},x] && EqQ[n2,2*n] && FractionQ[n]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_12(symbols),
        with: [d__, e__, n_, q_, a__, c__, n2_, p_, x_],
        optional: [e__, q_, c__, n2_, p_],
        x_free: [a__, c__, d__, e__, n_, p_, q_],
        scaled: [(n2_, 2, n_)],
        when: {
            freeq!([a__, c__, d__, e__, p_, q_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && fractionq!(n_)
        },
        rhs: {
            let g_i = rubi_denominator(&n_).unwrap();
            let g = Atom::num(g_i);
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = sub_atom.pow(&g - Atom::num(1))
                * (&d__ + &e__ * sub_atom.pow(&g * &n_)).pow(&q_)
                * (&a__ + &c__ * sub_atom.pow(Atom::num(2) * &g * &n_)).pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);
            let substituted =
                rubi_subst(&transformed, sub, x_.pow(Atom::num(1) / &g));

            rubi_star(g, substituted)
        },
    ));
}

fn push_rules_rule_1733(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; b__, c__, d__, e__, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 1733,
        source: "Int[(d_+e_.*x_^n_)*(b_.*x_^n_+c_.*x_^n2_)^p_,x_Symbol] :=
          (b*e-d*c)*(b*x^n+c*x^(2*n))^(p+1)/(b*c*n*(p+1)*x^(2*n*(p+1))) +
          e/c \\[Star] Int[x^(-n)*(b*x^n+c*x^(2*n))^(p+1),x] /;
        FreeQ[{b,c,d,e,n,p},x] && EqQ[n2,2*n] && Not[IntegerQ[p]] && EqQ[n*(2*p+1)+1,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [d__, e__, n_, b__, c__, n2_, p_, x_],
        optional: [e__, b__, c__],
        x_free: [b__, c__, d__, e__, n_, p_],
        when: {
            freeq!([b__, c__, d__, e__, n_, p_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && !integerq!(p_)
                && eqq!(&n_ * (Atom::num(2) * &p_ + Atom::num(1)) + Atom::num(1), 0)
        },
        rhs: {
            let trinomial = &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_);
            let recursive_integrand = x_.pow(-&n_) * trinomial.pow(&p_ + Atom::num(1));
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let coefficient = &e__ / &c__;

            rubi_simp(&((&b__ * &e__ - &d__ * &c__) * trinomial.pow(&p_ + Atom::num(1))
                    / (&b__
                        * &c__
                        * &n_
                        * (&p_ + Atom::num(1))
                        * x_.pow(Atom::num(2) * &n_ * (&p_ + Atom::num(1))))), x_)
                    + rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_1734(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; b__, c__, d__, e__, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 1734,
        source: "Int[(d_+e_.*x_^n_)*(b_.*x_^n_+c_.*x_^n2_)^p_,x_Symbol] :=
          e*x^(-n+1)*(b*x^n+c*x^(2*n))^(p+1)/(c*(n*(2*p+1)+1)) /;
        FreeQ[{b,c,d,e,n,p},x] && EqQ[n2,2*n] && Not[IntegerQ[p]] && NeQ[n*(2*p+1)+1,0] && EqQ[b*e*(n*p+1)-c*d*(n*(2*p+1)+1),0]",
        desc: "Apply the direct antiderivative formula.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [d__, e__, n_, b__, c__, n2_, p_, x_],
        optional: [e__, b__, c__],
        x_free: [b__, c__, d__, e__, n_, p_],
        when: {
            let balance = &n_ * (Atom::num(2) * &p_ + Atom::num(1)) + Atom::num(1);
            freeq!([b__, c__, d__, e__, n_, p_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && !integerq!(p_)
                && neq!(balance, 0)
                && eqq!(
                    &b__ * &e__ * (&n_ * &p_ + Atom::num(1)) - &c__ * &d__ * balance,
                    0
                )
        },
        rhs: {
            let balance = &n_ * (Atom::num(2) * &p_ + Atom::num(1)) + Atom::num(1);
            let trinomial = &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_);

            rubi_simp(&(&e__ * x_.pow(-&n_ + Atom::num(1)) * trinomial.pow(&p_ + Atom::num(1))
                    / (&c__ * balance)), x_)
        },
    ));
}

fn push_rules_rule_1735(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; b__, c__, d__, e__, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 1735,
        source: "Int[(d_+e_.*x_^n_)*(b_.*x_^n_+c_.*x_^n2_)^p_,x_Symbol] :=
          e*x^(-n+1)*(b*x^n+c*x^(2*n))^(p+1)/(c*(n*(2*p+1)+1)) -
          (b*e*(n*p+1)-c*d*(n*(2*p+1)+1))/(c*(n*(2*p+1)+1)) \\[Star] Int[(b*x^n+c*x^(2*n))^p,x] /;
        FreeQ[{b,c,d,e,n,p},x] && EqQ[n2,2*n] && Not[IntegerQ[p]] && NeQ[n*(2*p+1)+1,0] && NeQ[b*e*(n*p+1)-c*d*(n*(2*p+1)+1),0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [d__, e__, n_, b__, c__, n2_, p_, x_],
        optional: [e__, b__, c__],
        x_free: [b__, c__, d__, e__, n_, p_],
        when: {
            let balance = &n_ * (Atom::num(2) * &p_ + Atom::num(1)) + Atom::num(1);
            let coefficient = &b__ * &e__ * (&n_ * &p_ + Atom::num(1)) - &c__ * &d__ * &balance;
            freeq!([b__, c__, d__, e__, n_, p_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && !integerq!(p_)
                && neq!(balance, 0)
                && neq!(coefficient, 0)
        },
        rhs: {
            let balance = &n_ * (Atom::num(2) * &p_ + Atom::num(1)) + Atom::num(1);
            let coefficient = &b__ * &e__ * (&n_ * &p_ + Atom::num(1)) - &c__ * &d__ * &balance;
            let trinomial = &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_);
            let recursive = rubi_rhs_int(&trinomial.pow(&p_), x_);
            let recursive_coefficient = &coefficient / (&c__ * &balance);

            rubi_simp(&(&e__ * x_.pow(-&n_ + Atom::num(1)) * trinomial.pow(&p_ + Atom::num(1))
                    / (&c__ * &balance)), x_)
                    - rubi_star(recursive_coefficient, recursive)
        },
    ));
}

fn push_rules_rule_1736(rules: &mut Vec<RubiRule>) {
    rubi_symb!(b__, c__, d__, e__, n_, n2_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1736,
        source: "Int[(d_+e_.*x_^n_)^q_.*(b_.*x_^n_+c_.*x_^n2_)^p_,x_Symbol] :=
          (b*x^n+c*x^(2*n))^FracPart[p]/(x^(n*FracPart[p])*(b+c*x^n)^FracPart[p]) \\[Star] Int[x^(n*p)*(d+e*x^n)^q*(b+c*x^n)^p,x] /;
        FreeQ[{b,c,d,e,n,p,q},x] && EqQ[n2,2*n] && Not[IntegerQ[p]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: (d__ + e__ * x_.pow(n_)).pow(q_) * (b__ * x_.pow(n_) + c__ * x_.pow(n2_)).pow(p_),
        with: [d__, e__, n_, q_, b__, c__, n2_, p_, x_],
        optional: [e__, q_, b__, c__],
        x_free: [b__, c__, d__, e__, n_, p_, q_],
        when: {
            freeq!([b__, c__, d__, e__, n_, p_, q_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && !integerq!(p_)
        },
        rhs: {
            let frac_p = rubi_frac_part(&p_);
            let trinomial = &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_);
            let reduced = &b__ + &c__ * x_.pow(&n_);
            let recursive_integrand = x_.pow(&n_ * &p_)
                * (&d__ + &e__ * x_.pow(&n_)).pow(&q_)
                * reduced.pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let coefficient = trinomial.pow(&frac_p)
                / (x_.pow(&n_ * &frac_p) * reduced.pow(frac_p));

            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_1395(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, n2_, p_, q_, u__, x_);
    rules.push(rubi_rule!(
        order: 1395,
        source: "Int[u_.*(d_+e_.*x_^n_)^q_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
          (a+b*x^n+c*x^(2*n))^FracPart[p]/((d+e*x^n)^FracPart[p]*(a/d+c*x^n/e)^FracPart[p]) \\[Star] Int[u*(d+e*x^n)^(p+q)*(a/d+c/e*x^n)^p,x] /;
        FreeQ[{a,b,c,d,e,n,p,q},x] && EqQ[n2,2*n] && EqQ[c*d^2-b*d*e+a*e^2,0] && Not[IntegerQ[p]] && Not[EqQ[q,1] && EqQ[n,2]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_19(symbols),
        with: [u__, d__, e__, n_, q_, a__, b__, c__, n2_, p_, x_],
        optional: [u__, e__, q_, b__, c__, n2_],
        x_free: [a__, b__, c__, d__, e__, n_, p_, q_],
        scaled: [(n2_, 2, n_)],
        when: {
            freeq!([a__, b__, c__, d__, e__, n_, p_, q_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && eqq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && !integerq!(p_)
                && !(eqq!(q_, 1) && eqq!(n_, 2))
        },
        rhs: {
            let frac_p = rubi_frac_part(&p_);
            let binomial = &d__ + &e__ * x_.pow(&n_);
            let transformed = &a__ / &d__ + &c__ * x_.pow(&n_) / &e__;
            let trinomial = &a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_);
            let factor = trinomial.pow(&frac_p)
                / (binomial.pow(&frac_p) * transformed.pow(&frac_p));
            let recursive_integrand =
                &u__ * binomial.pow(&p_ + &q_) * transformed.pow(&p_);
            rubi_star(factor, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1396(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, n_, n2_, p_, q_, u__, x_);
    rules.push(rubi_rule!(
        order: 1396,
        source: "Int[u_.*(d_+e_.*x_^n_)^q_.*(a_+c_.*x_^n2_.)^p_,x_Symbol] :=
          (a+c*x^(2*n))^FracPart[p]/((d+e*x^n)^FracPart[p]*(a/d+c*x^n/e)^FracPart[p]) \\[Star] Int[u*(d+e*x^n)^(p+q)*(a/d+c/e*x^n)^p,x] /;
        FreeQ[{a,c,d,e,n,p,q},x] && EqQ[n2,2*n] && EqQ[c*d^2+a*e^2,0] && Not[IntegerQ[p]] && Not[EqQ[q,1] && EqQ[n,2]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_20(symbols),
        with: [u__, d__, e__, n_, q_, a__, c__, n2_, p_, x_],
        optional: [u__, e__, q_, c__, n2_],
        x_free: [a__, c__, d__, e__, n_, p_, q_],
        when: {
            freeq!([a__, c__, d__, e__, n_, p_, q_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && eqq!(&c__ * d__.pow(2) + &a__ * e__.pow(2), 0)
                && !integerq!(p_)
                && !(eqq!(q_, 1) && eqq!(n_, 2))
        },
        rhs: {
            let frac_p = rubi_frac_part(&p_);
            let binomial = &d__ + &e__ * x_.pow(&n_);
            let transformed = &a__ / &d__ + &c__ * x_.pow(&n_) / &e__;
            let trinomial = &a__ + &c__ * x_.pow(Atom::num(2) * &n_);
            let factor = trinomial.pow(&frac_p)
                / (binomial.pow(&frac_p) * transformed.pow(&frac_p));
            let recursive_integrand =
                &u__ * binomial.pow(&p_ + &q_) * transformed.pow(&p_);
            rubi_star(factor, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1737(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, n2_, q_, x_);
    rules.push(rubi_rule!(
        order: 1737,
        source: "Int[(d_+e_.*x_^n_)^q_.*(a_+b_.*x_^n_+c_.*x_^n2_),x_Symbol] :=
          Int[ExpandIntegrand[(d+e*x^n)^q*(a+b*x^n+c*x^(2*n)),x],x] /;
        FreeQ[{a,b,c,d,e,n},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && IGtQ[q,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [d__, e__, n_, q_, a__, b__, c__, n2_, x_],
        optional: [e__, q_, b__, c__],
        x_free: [a__, b__, c__, d__, e__, n_],
        integer_gt: [(q_, 0)],
        scaled: [(n2_, 2, n_)],
        when: {
            freeq!([a__, b__, c__, d__, e__, n_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && neq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && igtq!(q_, 0)
        },
        rhs: {
            let integrand = (&d__ + &e__ * x_.pow(&n_)).pow(&q_)
                * (&a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_));
            let expanded = rubi_expand_integrand(&integrand, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_1738(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, n_, n2_, q_, x_);
    rules.push(rubi_rule!(
        order: 1738,
        source: "Int[(d_+e_.*x_^n_)^q_.*(a_+c_.*x_^n2_),x_Symbol] :=
          Int[ExpandIntegrand[(d+e*x^n)^q*(a+c*x^(2*n)),x],x] /;
        FreeQ[{a,c,d,e,n},x] && EqQ[n2,2*n] && NeQ[c*d^2+a*e^2,0] && IGtQ[q,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_11(symbols),
        with: [d__, e__, n_, q_, a__, c__, n2_, x_],
        optional: [e__, q_, c__],
        x_free: [a__, c__, d__, e__, n_],
        integer_gt: [(q_, 0)],
        scaled: [(n2_, 2, n_)],
        when: {
            freeq!([a__, c__, d__, e__, n_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && neq!(&c__ * d__.pow(2) + &a__ * e__.pow(2), 0)
                && igtq!(q_, 0)
        },
        rhs: {
            let integrand = (&d__ + &e__ * x_.pow(&n_)).pow(&q_)
                * (&a__ + &c__ * x_.pow(Atom::num(2) * &n_));
            let expanded = rubi_expand_integrand(&integrand, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_1739(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, n2_, q_, x_);
    rules.push(rubi_rule!(
        order: 1739,
        source: "Int[(d_+e_.*x_^n_)^q_*(a_+b_.*x_^n_+c_.*x_^n2_),x_Symbol] :=
          -(c*d^2-b*d*e+a*e^2)*x*(d+e*x^n)^(q+1)/(d*e^2*n*(q+1)) +
          1/(n*(q+1)*d*e^2) \\[Star] Int[(d+e*x^n)^(q+1)*Simp[c*d^2-b*d*e+a*e^2*(n*(q+1)+1)+c*d*e*n*(q+1)*x^n,x],x] /;
        FreeQ[{a,b,c,d,e,n},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && LtQ[q,-1]",
        desc: "???",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [d__, e__, n_, q_, a__, b__, c__, n2_, x_],
        optional: [e__, b__, c__],
        x_free: [a__, b__, c__, d__, e__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, n_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && neq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && ltq!(q_, -1)
        },
        rhs: {
            let relation = &c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2);
            let binomial = &d__ + &e__ * x_.pow(&n_);
            let direct = -&relation * x_ * binomial.pow(&q_ + Atom::num(1))
                / (&d__ * e__.pow(2) * &n_ * (&q_ + Atom::num(1)));
            let simp_payload = rubi_simp(
                &(&c__ * d__.pow(2) - &b__ * &d__ * &e__
                    + &a__ * e__.pow(2) * (&n_ * (&q_ + Atom::num(1)) + Atom::num(1))
                    + &c__ * &d__ * &e__ * &n_ * (&q_ + Atom::num(1)) * x_.pow(&n_)),
                x_,
            );
            let recursive_integrand = binomial.pow(&q_ + Atom::num(1)) * simp_payload;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let coefficient = Atom::num(1)
                / (&n_ * (&q_ + Atom::num(1)) * &d__ * e__.pow(2));

            rubi_simp(&(direct), x_) + rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_1740(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, n_, n2_, q_, x_);
    rules.push(rubi_rule!(
        order: 1740,
        source: "Int[(d_+e_.*x_^n_)^q_*(a_+c_.*x_^n2_),x_Symbol] :=
          -(c*d^2+a*e^2)*x*(d+e*x^n)^(q+1)/(d*e^2*n*(q+1)) +
          1/(n*(q+1)*d*e^2) \\[Star] Int[(d+e*x^n)^(q+1)*Simp[c*d^2+a*e^2*(n*(q+1)+1)+c*d*e*n*(q+1)*x^n,x],x] /;
        FreeQ[{a,c,d,e,n},x] && EqQ[n2,2*n] && NeQ[c*d^2+a*e^2,0] && LtQ[q,-1]",
        desc: "???",
        refs: [],
        pattern:  rubi_shared_pattern_11(symbols),
        with: [d__, e__, n_, q_, a__, c__, n2_, x_],
        optional: [e__, c__],
        x_free: [a__, c__, d__, e__, n_],
        when: {
            freeq!([a__, c__, d__, e__, n_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && neq!(&c__ * d__.pow(2) + &a__ * e__.pow(2), 0)
                && ltq!(q_, -1)
        },
        rhs: {
            let relation = &c__ * d__.pow(2) + &a__ * e__.pow(2);
            let binomial = &d__ + &e__ * x_.pow(&n_);
            let direct = -&relation * x_ * binomial.pow(&q_ + Atom::num(1))
                / (&d__ * e__.pow(2) * &n_ * (&q_ + Atom::num(1)));
            let simp_payload = rubi_simp(
                &(&c__ * d__.pow(2)
                    + &a__ * e__.pow(2) * (&n_ * (&q_ + Atom::num(1)) + Atom::num(1))
                    + &c__ * &d__ * &e__ * &n_ * (&q_ + Atom::num(1)) * x_.pow(&n_)),
                x_,
            );
            let recursive_integrand = binomial.pow(&q_ + Atom::num(1)) * simp_payload;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let coefficient = Atom::num(1)
                / (&n_ * (&q_ + Atom::num(1)) * &d__ * e__.pow(2));

            rubi_simp(&(direct), x_) + rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_1741(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, n2_, q_, x_);
    rules.push(rubi_rule!(
        order: 1741,
        source: "Int[(d_+e_.*x_^n_)^q_*(a_+b_.*x_^n_+c_.*x_^n2_),x_Symbol] :=
          c*x^(n+1)*(d+e*x^n)^(q+1)/(e*(n*(q+2)+1)) +
          1/(e*(n*(q+2)+1)) \\[Star] Int[(d+e*x^n)^q*(a*e*(n*(q+2)+1)-(c*d*(n+1)-b*e*(n*(q+2)+1))*x^n),x] /;
        FreeQ[{a,b,c,d,e,n,q},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [d__, e__, n_, q_, a__, b__, c__, n2_, x_],
        optional: [e__, b__, c__],
        x_free: [a__, b__, c__, d__, e__, n_, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__, n_, q_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && neq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
        },
        rhs: {
            let denominator = &n_ * (&q_ + Atom::num(2)) + Atom::num(1);
            let binomial = &d__ + &e__ * x_.pow(&n_);
            let direct =
                &c__ * x_.pow(&n_ + Atom::num(1)) * binomial.pow(&q_ + Atom::num(1))
                    / (&e__ * &denominator);
            let recursive_integrand = binomial.pow(&q_)
                * (&a__ * &e__ * &denominator
                    - (&c__ * &d__ * (&n_ + Atom::num(1)) - &b__ * &e__ * &denominator)
                        * x_.pow(&n_));
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let coefficient = Atom::num(1) / (&e__ * &denominator);

            rubi_simp(&(direct), x_) + rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_1742(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, n_, n2_, q_, x_);
    rules.push(rubi_rule!(
        order: 1742,
        source: "Int[(d_+e_.*x_^n_)^q_*(a_+c_.*x_^n2_),x_Symbol] :=
          c*x^(n+1)*(d+e*x^n)^(q+1)/(e*(n*(q+2)+1)) +
          1/(e*(n*(q+2)+1)) \\[Star] Int[(d+e*x^n)^q*(a*e*(n*(q+2)+1)-c*d*(n+1)*x^n),x] /;
        FreeQ[{a,c,d,e,n,q},x] && EqQ[n2,2*n] && NeQ[c*d^2+a*e^2,0]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_11(symbols),
        with: [d__, e__, n_, q_, a__, c__, n2_, x_],
        optional: [e__, c__],
        x_free: [a__, c__, d__, e__, n_, q_],
        when: {
            freeq!([a__, c__, d__, e__, n_, q_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && neq!(&c__ * d__.pow(2) + &a__ * e__.pow(2), 0)
        },
        rhs: {
            let denominator = &n_ * (&q_ + Atom::num(2)) + Atom::num(1);
            let binomial = &d__ + &e__ * x_.pow(&n_);
            let direct =
                &c__ * x_.pow(&n_ + Atom::num(1)) * binomial.pow(&q_ + Atom::num(1))
                    / (&e__ * &denominator);
            let recursive_integrand = binomial.pow(&q_)
                * (&a__ * &e__ * &denominator - &c__ * &d__ * (&n_ + Atom::num(1)) * x_.pow(&n_));
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let coefficient = Atom::num(1) / (&e__ * &denominator);

            rubi_simp(&(direct), x_) + rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_1743(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, n_, n2_, x_);
    rules.push(rubi_rule!(
        order: 1743,
        source: "Int[(d_+e_.*x_^n_)/(a_+c_.*x_^n2_),x_Symbol] :=
          With[{q=Rt[2*d*e,2]},
          e^2/(2*c) \\[Star] Int[1/(d+q*x^(n/2)+e*x^n),x] + e^2/(2*c) \\[Star] Int[1/(d-q*x^(n/2)+e*x^n),x]] /;
        FreeQ[{a,c,d,e},x] && EqQ[n2,2*n] && EqQ[c*d^2-a*e^2,0] && IGtQ[n/2,0] && PosQ[d*e]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_18(symbols),
        with: [d__, e__, n_, a__, c__, n2_, x_],
        optional: [e__, c__],
        x_free: [a__, c__, d__, e__],
        when: {
            freeq!([a__, c__, d__, e__], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && eqq!(&c__ * d__.pow(2) - &a__ * e__.pow(2), 0)
                && igtq!(&n_ / Atom::num(2), 0)
                && posq!(&d__ * &e__)
        },
        rhs: {
            let q = rubi_rt(&(Atom::num(2) * &d__ * &e__), 2);
            let first_integrand = Atom::num(1)
                / (&d__ + &q * x_.pow(&n_ / Atom::num(2)) + &e__ * x_.pow(&n_));
            let second_integrand = Atom::num(1)
                / (&d__ - &q * x_.pow(&n_ / Atom::num(2)) + &e__ * x_.pow(&n_));
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);
            let coefficient = e__.pow(2) / (Atom::num(2) * &c__);

            rubi_star(&coefficient, first) + rubi_star(coefficient, second)
        },
    ));
}

fn push_rules_rule_1744(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, n_, n2_, x_);
    rules.push(rubi_rule!(
        order: 1744,
        source: "Int[(d_+e_.*x_^n_)/(a_+c_.*x_^n2_),x_Symbol] :=
          With[{q=Rt[-2*d*e,2]},
          d/(2*a) \\[Star] Int[(d-q*x^(n/2))/(d-q*x^(n/2)-e*x^n),x] +
          d/(2*a) \\[Star] Int[(d+q*x^(n/2))/(d+q*x^(n/2)-e*x^n),x]] /;
        FreeQ[{a,c,d,e},x] && EqQ[n2,2*n] && EqQ[c*d^2-a*e^2,0] && IGtQ[n/2,0] && NegQ[d*e]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_18(symbols),
        with: [d__, e__, n_, a__, c__, n2_, x_],
        optional: [e__, c__],
        x_free: [a__, c__, d__, e__],
        when: {
            freeq!([a__, c__, d__, e__], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && eqq!(&c__ * d__.pow(2) - &a__ * e__.pow(2), 0)
                && igtq!(&n_ / Atom::num(2), 0)
                && negq!(&d__ * &e__)
        },
        rhs: {
            let q = rubi_rt(&(-Atom::num(2) * &d__ * &e__), 2);
            let half_n = &n_ / Atom::num(2);
            let first_integrand =
                (&d__ - &q * x_.pow(&half_n)) / (&d__ - &q * x_.pow(&half_n) - &e__ * x_.pow(&n_));
            let second_integrand =
                (&d__ + &q * x_.pow(&half_n)) / (&d__ + &q * x_.pow(&half_n) - &e__ * x_.pow(&n_));
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);
            let coefficient = &d__ / (Atom::num(2) * &a__);

            rubi_star(&coefficient, first) + rubi_star(coefficient, second)
        },
    ));
}

fn push_rules_rule_1745(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, n_, n2_, x_);
    rules.push(rubi_rule!(
        order: 1745,
        source: "Int[(d_+e_.*x_^n_)/(a_+c_.*x_^n2_),x_Symbol] :=
          With[{q=Rt[a/c,4]},
          1/(2*Sqrt[2]*c*q^3) \\[Star] Int[(Sqrt[2]*d*q-(d-e*q^2)*x^(n/2))/(q^2-Sqrt[2]*q*x^(n/2)+x^n),x] +
          1/(2*Sqrt[2]*c*q^3) \\[Star] Int[(Sqrt[2]*d*q+(d-e*q^2)*x^(n/2))/(q^2+Sqrt[2]*q*x^(n/2)+x^n),x]] /;
        FreeQ[{a,c,d,e},x] && EqQ[n2,2*n] && NeQ[c*d^2+a*e^2,0] && NeQ[c*d^2-a*e^2,0] && IGtQ[n/2,0] && PosQ[a*c]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_18(symbols),
        with: [d__, e__, n_, a__, c__, n2_, x_],
        optional: [e__, c__],
        x_free: [a__, c__, d__, e__],
        when: {
            freeq!([a__, c__, d__, e__], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && neq!(&c__ * d__.pow(2) + &a__ * e__.pow(2), 0)
                && neq!(&c__ * d__.pow(2) - &a__ * e__.pow(2), 0)
                && igtq!(&n_ / Atom::num(2), 0)
                && posq!(&a__ * &c__)
        },
        rhs: {
            let q = rubi_rt(&(&a__ / &c__), 4);
            let sqrt_two = Atom::num(2).sqrt();
            let half_n = &n_ / Atom::num(2);
            let first_integrand = (&sqrt_two * &d__ * &q
                - (&d__ - &e__ * q.pow(2)) * x_.pow(&half_n))
                / (q.pow(2) - &sqrt_two * &q * x_.pow(&half_n) + x_.pow(&n_));
            let second_integrand = (&sqrt_two * &d__ * &q
                + (&d__ - &e__ * q.pow(2)) * x_.pow(&half_n))
                / (q.pow(2) + &sqrt_two * &q * x_.pow(&half_n) + x_.pow(&n_));
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);
            let coefficient = Atom::num(1) / (Atom::num(2) * sqrt_two * c__ * q.pow(3));

            rubi_star(&coefficient, first) + rubi_star(coefficient, second)
        },
    ));
}

fn push_rules_rule_1746(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 1746,
        source: "Int[(d_+e_.*x_^3)/(a_+c_.*x_^6),x_Symbol] :=
          With[{q=Rt[c/a,6]},
          1/(3*a*q^2) \\[Star] Int[(q^2*d-e*x)/(1+q^2*x^2),x] +
          1/(6*a*q^2) \\[Star] Int[(2*q^2*d-(Sqrt[3]*q^3*d-e)*x)/(1-Sqrt[3]*q*x+q^2*x^2),x] +
          1/(6*a*q^2) \\[Star] Int[(2*q^2*d+(Sqrt[3]*q^3*d+e)*x)/(1+Sqrt[3]*q*x+q^2*x^2),x]] /;
        FreeQ[{a,c,d,e},x] && NeQ[c*d^2+a*e^2,0] && PosQ[c/a]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (d__ + e__ * x_.pow(3)) / (a__ + c__ * x_.pow(6)),
        with: [d__, e__, a__, c__, x_],
        optional: [e__, c__],
        x_free: [a__, c__, d__, e__],
        when: {
            freeq!([a__, c__, d__, e__], x_)
                && neq!(&c__ * d__.pow(2) + &a__ * e__.pow(2), 0)
                && posq!(&c__ / &a__)
        },
        rhs: {
            let q = rubi_rt(&(&c__ / &a__), 6);
            let sqrt_three = Atom::num(3).sqrt();
            let first_integrand = (q.pow(2) * &d__ - &e__ * x_)
                / (Atom::num(1) + q.pow(2) * x_.pow(2));
            let second_integrand = (Atom::num(2) * q.pow(2) * &d__
                - (&sqrt_three * q.pow(3) * &d__ - &e__) * x_)
                / (Atom::num(1) - &sqrt_three * &q * x_ + q.pow(2) * x_.pow(2));
            let third_integrand = (Atom::num(2) * q.pow(2) * &d__
                + (&sqrt_three * q.pow(3) * &d__ + &e__) * x_)
                / (Atom::num(1) + &sqrt_three * &q * x_ + q.pow(2) * x_.pow(2));
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);
            let third = rubi_rhs_int(&third_integrand, x_);
            let first_coefficient = Atom::num(1) / (Atom::num(3) * &a__ * q.pow(2));
            let other_coefficient = Atom::num(1) / (Atom::num(6) * &a__ * q.pow(2));

            rubi_star(first_coefficient, first)
                    + rubi_star(&other_coefficient, second)
                    + rubi_star(other_coefficient, third)
        },
    ));
}

fn push_rules_rule_1747(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, n_, n2_, x_);
    rules.push(rubi_rule!(
        order: 1747,
        source: "Int[(d_+e_.*x_^n_)/(a_+c_.*x_^n2_),x_Symbol] :=
          With[{q=Rt[-a/c,2]},
          (d+e*q)/2 \\[Star] Int[1/(a+c*q*x^n),x] + (d-e*q)/2 \\[Star] Int[1/(a-c*q*x^n),x]] /;
        FreeQ[{a,c,d,e,n},x] && EqQ[n2,2*n] && NeQ[c*d^2+a*e^2,0] && NegQ[a*c] && IntegerQ[n]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_18(symbols),
        with: [d__, e__, n_, a__, c__, n2_, x_],
        optional: [e__, c__],
        x_free: [a__, c__, d__, e__, n_],
        when: {
            freeq!([a__, c__, d__, e__, n_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && neq!(&c__ * d__.pow(2) + &a__ * e__.pow(2), 0)
                && negq!(&a__ * &c__)
                && integerq!(n_)
        },
        rhs: {
            let q = rubi_rt(&(-&a__ / &c__), 2);
            let first_integrand = Atom::num(1) / (&a__ + &c__ * &q * x_.pow(&n_));
            let second_integrand = Atom::num(1) / (&a__ - &c__ * &q * x_.pow(&n_));
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);
            let first_coefficient = (&d__ + &e__ * &q) / Atom::num(2);
            let second_coefficient = (&d__ - &e__ * &q) / Atom::num(2);

            rubi_star(first_coefficient, first)
                    + rubi_star(second_coefficient, second)
        },
    ));
}

fn push_rules_rule_1748(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, n_, n2_, x_);
    rules.push(rubi_rule!(
        order: 1748,
        source: "Int[(d_+e_.*x_^n_)/(a_+c_.*x_^n2_),x_Symbol] :=
          d \\[Star] Int[1/(a+c*x^(2*n)),x] + e \\[Star] Int[x^n/(a+c*x^(2*n)),x] /;
        FreeQ[{a,c,d,e,n},x] && EqQ[n2,2*n] && NeQ[c*d^2+a*e^2,0] && (PosQ[a*c] || Not[IntegerQ[n]])",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_18(symbols),
        with: [d__, e__, n_, a__, c__, n2_, x_],
        optional: [e__, c__],
        x_free: [a__, c__, d__, e__, n_],
        when: {
            freeq!([a__, c__, d__, e__, n_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && neq!(&c__ * d__.pow(2) + &a__ * e__.pow(2), 0)
                && (posq!(&a__ * &c__) || !integerq!(n_))
        },
        rhs: {
            let denominator = &a__ + &c__ * x_.pow(Atom::num(2) * &n_);
            let first = rubi_rhs_int(&(Atom::num(1) / &denominator), x_);
            let second = rubi_rhs_int(&(x_.pow(&n_) / denominator), x_);

            rubi_star(d__, first) + rubi_star(e__, second)
        },
    ));
}

fn push_rules_rule_1749(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, n2_, x_);
    rules.push(rubi_rule!(
        order: 1749,
        source: "Int[(d_+e_.*x_^n_)/(a_+b_.*x_^n_+c_.*x_^n2_),x_Symbol] :=
          With[{q=Rt[2*d/e-b/c,2]},
          e/(2*c) \\[Star] Int[1/Simp[d/e+q*x^(n/2)+x^n,x],x] +
          e/(2*c) \\[Star] Int[1/Simp[d/e-q*x^(n/2)+x^n,x],x]] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c,0] && EqQ[c*d^2-a*e^2,0] && IGtQ[n/2,0] && (GtQ[2*d/e-b/c,0] || Not[LtQ[2*d/e-b/c,0]] && EqQ[d,e*Rt[a/c,2]])",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_17(symbols),
        with: [d__, e__, n_, a__, b__, c__, n2_, x_],
        optional: [e__, b__, c__],
        x_free: [a__, b__, c__, d__, e__],
        when: {
            let discriminant = b__.pow(2) - Atom::num(4) * &a__ * &c__;
            let radicand = Atom::num(2) * &d__ / &e__ - &b__ / &c__;
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && neq!(discriminant, 0)
                && eqq!(&c__ * d__.pow(2) - &a__ * e__.pow(2), 0)
                && igtq!(&n_ / Atom::num(2), 0)
                && (gtq!(radicand, 0)
                    || !ltq!(&radicand, 0) && eqq!(d__, &e__ * rubi_rt(&(&a__ / &c__), 2)))
        },
        rhs: {
            let q = rubi_rt(&(Atom::num(2) * &d__ / &e__ - &b__ / &c__), 2);
            let half_n = &n_ / Atom::num(2);
            let first_denominator =
                rubi_simp(&(&d__ / &e__ + &q * x_.pow(&half_n) + x_.pow(&n_)), x_);
            let second_denominator =
                rubi_simp(&(&d__ / &e__ - &q * x_.pow(&half_n) + x_.pow(&n_)), x_);
            let first = rubi_rhs_int(&(Atom::num(1) / first_denominator), x_);
            let second = rubi_rhs_int(&(Atom::num(1) / second_denominator), x_);
            let coefficient = &e__ / (Atom::num(2) * &c__);

            rubi_star(&coefficient, first) + rubi_star(coefficient, second)
        },
    ));
}

fn push_rules_rule_1750(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, n2_, x_);
    rules.push(rubi_rule!(
        order: 1750,
        source: "Int[(d_+e_.*x_^n_)/(a_+b_.*x_^n_+c_.*x_^n2_),x_Symbol] :=
          With[{q=Rt[b^2-4*a*c,2]},
          (e/2+(2*c*d-b*e)/(2*q)) \\[Star] Int[1/(b/2-q/2+c*x^n),x] + (e/2-(2*c*d-b*e)/(2*q)) \\[Star] Int[1/(b/2+q/2+c*x^n),x]] /;
        FreeQ[{a,b,c,d,e,n},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c,0] && EqQ[c*d^2-a*e^2,0] && IGtQ[n/2,0] && GtQ[b^2-4*a*c,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_17(symbols),
        with: [d__, e__, n_, a__, b__, c__, n2_, x_],
        optional: [e__, b__, c__],
        x_free: [a__, b__, c__, d__, e__, n_],
        when: {
            let discriminant = b__.pow(2) - Atom::num(4) * &a__ * &c__;
            freeq!([a__, b__, c__, d__, e__, n_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && neq!(discriminant, 0)
                && eqq!(&c__ * d__.pow(2) - &a__ * e__.pow(2), 0)
                && igtq!(&n_ / Atom::num(2), 0)
                && gtq!(discriminant, 0)
        },
        rhs: {
            let q = rubi_rt(&(b__.pow(2) - Atom::num(4) * &a__ * &c__), 2);
            let first_coefficient = &e__ / Atom::num(2) + (Atom::num(2) * &c__ * &d__ - &b__ * &e__) / (Atom::num(2) * &q);
            let second_coefficient = &e__ / Atom::num(2) - (Atom::num(2) * &c__ * &d__ - &b__ * &e__) / (Atom::num(2) * &q);
            let first_integrand = Atom::num(1)
                / (&b__ / Atom::num(2) - &q / Atom::num(2) + &c__ * x_.pow(&n_));
            let second_integrand = Atom::num(1)
                / (&b__ / Atom::num(2) + &q / Atom::num(2) + &c__ * x_.pow(&n_));
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(first_coefficient, first)
                    + rubi_star(second_coefficient, second)
        },
    ));
}

fn push_rules_rule_1751(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, n2_, x_);
    rules.push(rubi_rule!(
        order: 1751,
        source: "Int[(d_+e_.*x_^n_)/(a_+b_.*x_^n_+c_.*x_^n2_),x_Symbol] :=
          With[{q=Rt[-2*d/e-b/c,2]},
          e/(2*c*q) \\[Star] Int[(q-2*x^(n/2))/Simp[d/e+q*x^(n/2)-x^n,x],x] +
          e/(2*c*q) \\[Star] Int[(q+2*x^(n/2))/Simp[d/e-q*x^(n/2)-x^n,x],x]] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c,0] && EqQ[c*d^2-a*e^2,0] && IGtQ[n/2,0] && Not[GtQ[b^2-4*a*c,0]]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_17(symbols),
        with: [d__, e__, n_, a__, b__, c__, n2_, x_],
        optional: [e__, b__, c__],
        x_free: [a__, b__, c__, d__, e__],
        when: {
            let discriminant = b__.pow(2) - Atom::num(4) * &a__ * &c__;
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && neq!(discriminant, 0)
                && eqq!(&c__ * d__.pow(2) - &a__ * e__.pow(2), 0)
                && igtq!(&n_ / Atom::num(2), 0)
                && !gtq!(discriminant, 0)
        },
        rhs: {
            let q = rubi_rt(&(-Atom::num(2) * &d__ / &e__ - &b__ / &c__), 2);
            let half_n = &n_ / Atom::num(2);
            let first_numerator = &q - Atom::num(2) * x_.pow(&half_n);
            let second_numerator = &q + Atom::num(2) * x_.pow(&half_n);
            let first_denominator =
                rubi_simp(&(&d__ / &e__ + &q * x_.pow(&half_n) - x_.pow(&n_)), x_);
            let second_denominator =
                rubi_simp(&(&d__ / &e__ - &q * x_.pow(&half_n) - x_.pow(&n_)), x_);
            let first = rubi_rhs_int(&(first_numerator / first_denominator), x_);
            let second = rubi_rhs_int(&(second_numerator / second_denominator), x_);
            let coefficient = &e__ / (Atom::num(2) * &c__ * &q);

            rubi_star(&coefficient, first) + rubi_star(coefficient, second)
        },
    ));
}

fn push_rules_rule_1752(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, n2_, x_);
    rules.push(rubi_rule!(
        order: 1752,
        source: "Int[(d_+e_.*x_^n_)/(a_+b_.*x_^n_+c_.*x_^n2_),x_Symbol] :=
          With[{q=Rt[b^2-4*a*c,2]},
          (e/2+(2*c*d-b*e)/(2*q)) \\[Star] Int[1/(b/2-q/2+c*x^n),x] + (e/2-(2*c*d-b*e)/(2*q)) \\[Star] Int[1/(b/2+q/2+c*x^n),x]] /;
        FreeQ[{a,b,c,d,e,n},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && (PosQ[b^2-4*a*c] || Not[IGtQ[n/2,0]])",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_17(symbols),
        with: [d__, e__, n_, a__, b__, c__, n2_, x_],
        optional: [e__, b__, c__],
        x_free: [a__, b__, c__, d__, e__, n_],
        when: {
            let discriminant = b__.pow(2) - Atom::num(4) * &a__ * &c__;
            freeq!([a__, b__, c__, d__, e__, n_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && neq!(discriminant, 0)
                && neq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && (posq!(discriminant) || !igtq!(&n_ / Atom::num(2), 0))
        },
        rhs: {
            let q = rubi_rt(&(b__.pow(2) - Atom::num(4) * &a__ * &c__), 2);
            let first_coefficient = &e__ / Atom::num(2) + (Atom::num(2) * &c__ * &d__ - &b__ * &e__) / (Atom::num(2) * &q);
            let second_coefficient = &e__ / Atom::num(2) - (Atom::num(2) * &c__ * &d__ - &b__ * &e__) / (Atom::num(2) * &q);
            let first_integrand = Atom::num(1)
                / (&b__ / Atom::num(2) - &q / Atom::num(2) + &c__ * x_.pow(&n_));
            let second_integrand = Atom::num(1)
                / (&b__ / Atom::num(2) + &q / Atom::num(2) + &c__ * x_.pow(&n_));
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(first_coefficient, first)
                    + rubi_star(second_coefficient, second)
        },
    ));
}

fn push_rules_rule_1753(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, n2_, x_);
    rules.push(rubi_rule!(
        order: 1753,
        source: "Int[(d_+e_.*x_^n_)/(a_+b_.*x_^n_+c_.*x_^n2_),x_Symbol] :=
          With[{q=Rt[a/c,2]},
          With[{r=Rt[2*q-b/c,2]},
          1/(2*c*q*r) \\[Star] Int[(d*r-(d-e*q)*x^(n/2))/(q-r*x^(n/2)+x^n),x] +
          1/(2*c*q*r) \\[Star] Int[(d*r+(d-e*q)*x^(n/2))/(q+r*x^(n/2)+x^n),x]]] /;
        FreeQ[{a,b,c,d,e},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && IGtQ[n/2,0] && NegQ[b^2-4*a*c]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_17(symbols),
        with: [d__, e__, n_, a__, b__, c__, n2_, x_],
        optional: [e__, b__, c__],
        x_free: [a__, b__, c__, d__, e__],
        when: {
            let discriminant = b__.pow(2) - Atom::num(4) * &a__ * &c__;
            freeq!([a__, b__, c__, d__, e__], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && neq!(discriminant, 0)
                && neq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && igtq!(&n_ / Atom::num(2), 0)
                && negq!(discriminant)
        },
        rhs: {
            let q = rubi_rt(&(&a__ / &c__), 2);
            let r = rubi_rt(&(Atom::num(2) * &q - &b__ / &c__), 2);
            let half_n = &n_ / Atom::num(2);
            let first_integrand = (&d__ * &r - (&d__ - &e__ * &q) * x_.pow(&half_n))
                / (&q - &r * x_.pow(&half_n) + x_.pow(&n_));
            let second_integrand = (&d__ * &r + (&d__ - &e__ * &q) * x_.pow(&half_n))
                / (&q + &r * x_.pow(&half_n) + x_.pow(&n_));
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);
            let coefficient = Atom::num(1) / (Atom::num(2) * c__ * q * r);

            rubi_star(&coefficient, first)
                    + rubi_star(coefficient, second)
        },
    ));
}

fn push_rules_rule_1754(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, n2_, q_, x_);
    rules.push(rubi_rule!(
        order: 1754,
        source: "Int[(d_+e_.*x_^n_)^q_/(a_+b_.*x_^n_+c_.*x_^n2_),x_Symbol] :=
          Int[ExpandIntegrand[(d+e*x^n)^q/(a+b*x^n+c*x^(2*n)),x],x] /;
        FreeQ[{a,b,c,d,e,n},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && IntegerQ[q]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_15(symbols),
        with: [d__, e__, n_, q_, a__, b__, c__, n2_, x_],
        optional: [e__, b__, c__],
        x_free: [a__, b__, c__, d__, e__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, n_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && neq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && integerq!(q_)
        },
        rhs: {
            let integrand = (&d__ + &e__ * x_.pow(&n_)).pow(&q_)
                / (&a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_));
            let expanded = rubi_expand_integrand(&integrand, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_1755(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, n_, n2_, q_, x_);
    rules.push(rubi_rule!(
        order: 1755,
        source: "Int[(d_+e_.*x_^n_)^q_/(a_+c_.*x_^n2_),x_Symbol] :=
          Int[ExpandIntegrand[(d+e*x^n)^q/(a+c*x^(2*n)),x],x] /;
        FreeQ[{a,c,d,e,n},x] && EqQ[n2,2*n] && NeQ[c*d^2+a*e^2,0] && IntegerQ[q]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_16(symbols),
        with: [d__, e__, n_, q_, a__, c__, n2_, x_],
        optional: [e__, c__],
        x_free: [a__, c__, d__, e__, n_],
        when: {
            freeq!([a__, c__, d__, e__, n_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && neq!(&c__ * d__.pow(2) + &a__ * e__.pow(2), 0)
                && integerq!(q_)
        },
        rhs: {
            let integrand = (&d__ + &e__ * x_.pow(&n_)).pow(&q_)
                / (&a__ + &c__ * x_.pow(Atom::num(2) * &n_));
            let expanded = rubi_expand_integrand(&integrand, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_1756(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, n2_, q_, x_);
    rules.push(rubi_rule!(
        order: 1756,
        source: "Int[(d_+e_.*x_^n_)^q_/(a_+b_.*x_^n_+c_.*x_^n2_),x_Symbol] :=
          e^2/(c*d^2-b*d*e+a*e^2) \\[Star] Int[(d+e*x^n)^q,x] +
          1/(c*d^2-b*d*e+a*e^2) \\[Star] Int[(d+e*x^n)^(q+1)*(c*d-b*e-c*e*x^n)/(a+b*x^n+c*x^(2*n)),x] /;
        FreeQ[{a,b,c,d,e,n},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && Not[IntegerQ[q]] && LtQ[q,-1]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_15(symbols),
        with: [d__, e__, n_, q_, a__, b__, c__, n2_, x_],
        optional: [e__, b__, c__],
        x_free: [a__, b__, c__, d__, e__, n_],
        when: {
            let discriminant = b__.pow(2) - Atom::num(4) * &a__ * &c__;
            let relation = &c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2);
            freeq!([a__, b__, c__, d__, e__, n_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && neq!(discriminant, 0)
                && neq!(relation, 0)
                && !integerq!(q_)
                && ltq!(q_, -1)
        },
        rhs: {
            let relation = &c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2);
            let binomial = &d__ + &e__ * x_.pow(&n_);
            let first = rubi_rhs_int(&binomial.pow(&q_), x_);
            let recursive_integrand = binomial.pow(&q_ + Atom::num(1))
                * (&c__ * &d__ - &b__ * &e__ - &c__ * &e__ * x_.pow(&n_))
                / (&a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_));
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let first_coefficient = e__.pow(2) / &relation;
            let recursive_coefficient = Atom::num(1) / &relation;

            rubi_star(first_coefficient, first)
                    + rubi_star(recursive_coefficient, recursive)
        },
    ));
}

fn push_rules_rule_1757(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, n_, n2_, q_, x_);
    rules.push(rubi_rule!(
        order: 1757,
        source: "Int[(d_+e_.*x_^n_)^q_/(a_+c_.*x_^n2_),x_Symbol] :=
          e^2/(c*d^2+a*e^2) \\[Star] Int[(d+e*x^n)^q,x] +
          c/(c*d^2+a*e^2) \\[Star] Int[(d+e*x^n)^(q+1)*(d-e*x^n)/(a+c*x^(2*n)),x] /;
        FreeQ[{a,c,d,e,n},x] && EqQ[n2,2*n] && NeQ[c*d^2+a*e^2,0] && Not[IntegerQ[q]] && LtQ[q,-1]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_16(symbols),
        with: [d__, e__, n_, q_, a__, c__, n2_, x_],
        optional: [e__, c__],
        x_free: [a__, c__, d__, e__, n_],
        when: {
            let relation = &c__ * d__.pow(2) + &a__ * e__.pow(2);
            freeq!([a__, c__, d__, e__, n_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && neq!(relation, 0)
                && !integerq!(q_)
                && ltq!(q_, -1)
        },
        rhs: {
            let relation = &c__ * d__.pow(2) + &a__ * e__.pow(2);
            let binomial = &d__ + &e__ * x_.pow(&n_);
            let first = rubi_rhs_int(&binomial.pow(&q_), x_);
            let recursive_integrand = binomial.pow(&q_ + Atom::num(1))
                * (&d__ - &e__ * x_.pow(&n_))
                / (&a__ + &c__ * x_.pow(Atom::num(2) * &n_));
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let first_coefficient = e__.pow(2) / &relation;
            let recursive_coefficient = &c__ / &relation;

            rubi_star(first_coefficient, first)
                    + rubi_star(recursive_coefficient, recursive)
        },
    ));
}

fn push_rules_rule_1758(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, n2_, q_, x_);
    rules.push(rubi_rule!(
        order: 1758,
        source: "Int[(d_+e_.*x_^n_)^q_/(a_+b_.*x_^n_+c_.*x_^n2_),x_Symbol] :=
          With[{r=Rt[b^2-4*a*c,2]},
          2*c/r \\[Star] Int[(d+e*x^n)^q/(b-r+2*c*x^n),x] - 2*c/r \\[Star] Int[(d+e*x^n)^q/(b+r+2*c*x^n),x]] /;
        FreeQ[{a,b,c,d,e,n,q},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && Not[IntegerQ[q]]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_15(symbols),
        with: [d__, e__, n_, q_, a__, b__, c__, n2_, x_],
        optional: [e__, b__, c__],
        x_free: [a__, b__, c__, d__, e__, n_, q_],
        when: {
            let discriminant = b__.pow(2) - Atom::num(4) * &a__ * &c__;
            freeq!([a__, b__, c__, d__, e__, n_, q_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && neq!(discriminant, 0)
                && neq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && !integerq!(q_)
        },
        rhs: {
            let r = rubi_rt(&(b__.pow(2) - Atom::num(4) * &a__ * &c__), 2);
            let binomial = &d__ + &e__ * x_.pow(&n_);
            let first_integrand = binomial.pow(&q_)
                / (&b__ - &r + Atom::num(2) * &c__ * x_.pow(&n_));
            let second_integrand = binomial.pow(&q_)
                / (&b__ + &r + Atom::num(2) * &c__ * x_.pow(&n_));
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);
            let coefficient = Atom::num(2) * &c__ / &r;

            rubi_star(&coefficient, first) - rubi_star(coefficient, second)
        },
    ));
}

fn push_rules_rule_1759(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, n_, n2_, q_, x_);
    rules.push(rubi_rule!(
        order: 1759,
        source: "Int[(d_+e_.*x_^n_)^q_/(a_+c_.*x_^n2_),x_Symbol] :=
          With[{r=Rt[-a*c,2]},
          -c/(2*r) \\[Star] Int[(d+e*x^n)^q/(r-c*x^n),x] - c/(2*r) \\[Star] Int[(d+e*x^n)^q/(r+c*x^n),x]] /;
        FreeQ[{a,c,d,e,n,q},x] && EqQ[n2,2*n] && NeQ[c*d^2+a*e^2,0] && Not[IntegerQ[q]]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_16(symbols),
        with: [d__, e__, n_, q_, a__, c__, n2_, x_],
        optional: [e__, c__],
        x_free: [a__, c__, d__, e__, n_, q_],
        when: {
            freeq!([a__, c__, d__, e__, n_, q_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && neq!(&c__ * d__.pow(2) + &a__ * e__.pow(2), 0)
                && !integerq!(q_)
        },
        rhs: {
            let r = rubi_rt(&(-&a__ * &c__), 2);
            let binomial = &d__ + &e__ * x_.pow(&n_);
            let first = rubi_rhs_int(&(binomial.pow(&q_) / (&r - &c__ * x_.pow(&n_))), x_);
            let second = rubi_rhs_int(&(binomial.pow(&q_) / (&r + &c__ * x_.pow(&n_))), x_);
            let coefficient = &c__ / (Atom::num(2) * &r);

            rubi_star(-(&coefficient), first) - rubi_star(coefficient, second)
        },
    ));
}

fn push_rules_rule_1760(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 1760,
        source: "Int[(d_+e_.*x_^n_)*(a_+b_.*x_^n_+c_.*x_^n2_)^p_,x_Symbol] :=
          -x*(d*b^2-a*b*e-2*a*c*d+(b*d-2*a*e)*c*x^n)*(a+b*x^n+c*x^(2*n))^(p+1)/(a*n*(p+1)*(b^2-4*a*c)) +
          1/(a*n*(p+1)*(b^2-4*a*c)) \\[Star]
            Int[Simp[(n*p+n+1)*d*b^2-a*b*e-2*a*c*d*(2*n*p+2*n+1)+(2*n*p+3*n+1)*(d*b-2*a*e)*c*x^n,x]*
              (a+b*x^n+c*x^(2*n))^(p+1),x] /;
        FreeQ[{a,b,c,d,e,n},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c,0] && ILtQ[p,-1]",
        desc: "Trinomial recurrence 2b with m=0",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [d__, e__, n_, a__, b__, c__, n2_, p_, x_],
        optional: [e__, b__, c__],
        x_free: [a__, b__, c__, d__, e__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, n_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && iltq!(p_, -1)
        },
        rhs: {
            let trinomial = &a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_);
            let discriminant = b__.pow(2) - Atom::num(4) * &a__ * &c__;
            let denominator = &a__ * &n_ * (&p_ + Atom::num(1)) * &discriminant;
            let direct = Atom::num(-1) * x_
                * (&d__ * b__.pow(2)
                    - &a__ * &b__ * &e__
                    - Atom::num(2) * &a__ * &c__ * &d__
                    + (&b__ * &d__ - Atom::num(2) * &a__ * &e__) * &c__ * x_.pow(&n_))
                * trinomial.pow(&p_ + Atom::num(1))
                / &denominator;
            let simp_payload = rubi_simp(
                &((&n_ * &p_ + &n_ + Atom::num(1)) * &d__ * b__.pow(2)
                    - &a__ * &b__ * &e__
                    - Atom::num(2)
                        * &a__
                        * &c__
                        * &d__
                        * (Atom::num(2) * &n_ * &p_ + Atom::num(2) * &n_ + Atom::num(1))
                    + (Atom::num(2) * &n_ * &p_ + Atom::num(3) * &n_ + Atom::num(1))
                        * (&d__ * &b__ - Atom::num(2) * &a__ * &e__)
                        * &c__
                        * x_.pow(&n_)),
                x_,
            );
            let recursive =
                rubi_rhs_int(&(simp_payload * trinomial.pow(&p_ + Atom::num(1))), x_);
            let coefficient = Atom::num(1) / &denominator;

            rubi_simp(&(direct), x_) + rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_1761(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 1761,
        source: "Int[(d_+e_.*x_^n_)*(a_+c_.*x_^n2_)^p_,x_Symbol] :=
          -x*(d+e*x^n)*(a+c*x^(2*n))^(p+1)/(2*a*n*(p+1)) +
          1/(2*a*n*(p+1)) \\[Star] Int[(d*(2*n*p+2*n+1)+e*(2*n*p+3*n+1)*x^n)*(a+c*x^(2*n))^(p+1),x] /;
        FreeQ[{a,c,d,e,n},x] && EqQ[n2,2*n] && ILtQ[p,-1]",
        desc: "Trinomial recurrence 2b with m=0",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [d__, e__, n_, a__, c__, n2_, p_, x_],
        optional: [e__, c__],
        x_free: [a__, c__, d__, e__, n_],
        when: {
            freeq!([a__, c__, d__, e__, n_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && iltq!(p_, -1)
        },
        rhs: {
            let trinomial = &a__ + &c__ * x_.pow(Atom::num(2) * &n_);
            let denominator = Atom::num(2) * &a__ * &n_ * (&p_ + Atom::num(1));
            let direct = Atom::num(-1) * x_
                * (&d__ + &e__ * x_.pow(&n_))
                * trinomial.pow(&p_ + Atom::num(1))
                / &denominator;
            let recursive_integrand = (&d__ * (Atom::num(2) * &n_ * &p_ + Atom::num(2) * &n_ + Atom::num(1))
                + &e__ * (Atom::num(2) * &n_ * &p_ + Atom::num(3) * &n_ + Atom::num(1)) * x_.pow(&n_))
                * trinomial.pow(&p_ + Atom::num(1));
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let coefficient = Atom::num(1) / &denominator;

            rubi_simp(&(direct), x_) + rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_1762(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 1762,
        source: "Int[(d_+e_.*x_^n_)*(a_+b_.*x_^n_+c_.*x_^n2_)^p_,x_Symbol] :=
          Int[ExpandIntegrand[(d+e*x^n)*(a+b*x^n+c*x^(2*n))^p,x],x] /;
        FreeQ[{a,b,c,d,e,n},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [d__, e__, n_, a__, b__, c__, n2_, p_, x_],
        optional: [e__, b__, c__],
        x_free: [a__, b__, c__, d__, e__, n_],
        when: {
            freeq!([a__, b__, c__, d__, e__, n_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
        },
        rhs: {
            let integrand = (&d__ + &e__ * x_.pow(&n_))
                * (&a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_)).pow(&p_);
            let expanded = rubi_expand_integrand(&integrand, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_1763(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, n_, n2_, p_, x_);
    rules.push(rubi_rule!(
        order: 1763,
        source: "Int[(d_+e_.*x_^n_)*(a_+c_.*x_^n2_)^p_,x_Symbol] :=
          Int[ExpandIntegrand[(d+e*x^n)*(a+c*x^(2*n))^p,x],x] /;
        FreeQ[{a,c,d,e,n},x] && EqQ[n2,2*n]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [d__, e__, n_, a__, c__, n2_, p_, x_],
        optional: [e__, c__],
        x_free: [a__, c__, d__, e__, n_],
        when: {
            freeq!([a__, c__, d__, e__, n_], x_) && eqq!(n2_, Atom::num(2) * &n_)
        },
        rhs: {
            let integrand =
                (&d__ + &e__ * x_.pow(&n_)) * (&a__ + &c__ * x_.pow(Atom::num(2) * &n_)).pow(&p_);
            let expanded = rubi_expand_integrand(&integrand, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_1764(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, n2_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1764,
        source: "Int[(d_+e_.*x_^n_)^q_*(a_+b_.*x_^n_+c_.*x_^n2_)^p_,x_Symbol] :=
          c^p*x^(2*n*p-n+1)*(d+e*x^n)^(q+1)/(e*(2*n*p+n*q+1)) +
          Int[(d+e*x^n)^q*ExpandToSum[(a+b*x^n+c*x^(2*n))^p-c^p*x^(2*n*p)-d*c^p*(2*n*p-n+1)*x^(2*n*p-n)/(e*(2*n*p+n*q+1)),x],x] /;
        FreeQ[{a,b,c,d,e,n,q},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c,0] && IGtQ[p,0] && NeQ[2*n*p+n*q+1,0] && IGtQ[n,0] && Not[IGtQ[q,0]]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [d__, e__, n_, q_, a__, b__, c__, n2_, p_, x_],
        optional: [e__, b__, c__],
        x_free: [a__, b__, c__, d__, e__, n_, q_],
        when: {
            let denominator = Atom::num(2) * &n_ * &p_ + &n_ * &q_ + Atom::num(1);
            freeq!([a__, b__, c__, d__, e__, n_, q_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && igtq!(p_, 0)
                && neq!(denominator, 0)
                && igtq!(n_, 0)
                && !igtq!(q_, 0)
        },
        rhs: {
            let denominator = Atom::num(2) * &n_ * &p_ + &n_ * &q_ + Atom::num(1);
            let binomial = &d__ + &e__ * x_.pow(&n_);
            let direct =
                c__.pow(&p_) * x_.pow(Atom::num(2) * &n_ * &p_ - &n_ + Atom::num(1))
                    * binomial.pow(&q_ + Atom::num(1))
                    / (&e__ * &denominator);
            let expand_to_sum_payload = (&a__
                + &b__ * x_.pow(&n_)
                + &c__ * x_.pow(Atom::num(2) * &n_))
            .pow(&p_)
                - c__.pow(&p_) * x_.pow(Atom::num(2) * &n_ * &p_)
                - &d__ * c__.pow(&p_) * (Atom::num(2) * &n_ * &p_ - &n_ + Atom::num(1))
                    * x_.pow(Atom::num(2) * &n_ * &p_ - &n_)
                    / (&e__ * &denominator);
            let expanded = rubi_expand_to_sum(&expand_to_sum_payload, x_);
            let recursive = rubi_rhs_int(&(binomial.pow(&q_) * expanded), x_);

            rubi_simp(&(direct), x_) + recursive
        },
    ));
}

fn push_rules_rule_1765(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, n_, n2_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1765,
        source: "Int[(d_+e_.*x_^n_)^q_*(a_+c_.*x_^n2_)^p_,x_Symbol] :=
          c^p*x^(2*n*p-n+1)*(d+e*x^n)^(q+1)/(e*(2*n*p+n*q+1)) +
          Int[(d+e*x^n)^q*ExpandToSum[(a+c*x^(2*n))^p-c^p*x^(2*n*p)-d*c^p*(2*n*p-n+1)*x^(2*n*p-n)/(e*(2*n*p+n*q+1)),x],x] /;
        FreeQ[{a,c,d,e,n,q},x] && EqQ[n2,2*n] && IGtQ[p,0] && NeQ[2*n*p+n*q+1,0] && IGtQ[n,0] && Not[IGtQ[q,0]]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_12(symbols),
        with: [d__, e__, n_, q_, a__, c__, n2_, p_, x_],
        optional: [e__, c__],
        x_free: [a__, c__, d__, e__, n_, q_],
        when: {
            let denominator = Atom::num(2) * &n_ * &p_ + &n_ * &q_ + Atom::num(1);
            freeq!([a__, c__, d__, e__, n_, q_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && igtq!(p_, 0)
                && neq!(denominator, 0)
                && igtq!(n_, 0)
                && !igtq!(q_, 0)
        },
        rhs: {
            let denominator = Atom::num(2) * &n_ * &p_ + &n_ * &q_ + Atom::num(1);
            let binomial = &d__ + &e__ * x_.pow(&n_);
            let direct =
                c__.pow(&p_) * x_.pow(Atom::num(2) * &n_ * &p_ - &n_ + Atom::num(1))
                    * binomial.pow(&q_ + Atom::num(1))
                    / (&e__ * &denominator);
            let expand_to_sum_payload = (&a__ + &c__ * x_.pow(Atom::num(2) * &n_)).pow(&p_)
                - c__.pow(&p_) * x_.pow(Atom::num(2) * &n_ * &p_)
                - &d__ * c__.pow(&p_) * (Atom::num(2) * &n_ * &p_ - &n_ + Atom::num(1))
                    * x_.pow(Atom::num(2) * &n_ * &p_ - &n_)
                    / (&e__ * &denominator);
            let expanded = rubi_expand_to_sum(&expand_to_sum_payload, x_);
            let recursive = rubi_rhs_int(&(binomial.pow(&q_) * expanded), x_);

            rubi_simp(&(direct), x_) + recursive
        },
    ));
}

fn push_rules_rule_1766(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, n2_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1766,
        source: "Int[(d_+e_.*x_^n_)^q_*(a_+b_.*x_^n_+c_.*x_^n2_)^p_,x_Symbol] :=
          Int[ExpandIntegrand[(d+e*x^n)^q*(a+b*x^n+c*x^(2*n))^p,x],x] /;
        FreeQ[{a,b,c,d,e,n,p,q},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] &&
          (IntegersQ[p,q] && Not[IntegerQ[n]] || IGtQ[p,0] || IGtQ[q,0] && Not[IntegerQ[n]])",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [d__, e__, n_, q_, a__, b__, c__, n2_, p_, x_],
        optional: [e__, b__, c__],
        x_free: [a__, b__, c__, d__, e__, n_, p_, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__, n_, p_, q_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && neq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && (integersq!([p_, q_]) && !integerq!(n_)
                    || igtq!(p_, 0)
                    || igtq!(q_, 0) && !integerq!(n_))
        },
        rhs: {
            let integrand = (&d__ + &e__ * x_.pow(&n_)).pow(&q_)
                * (&a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_)).pow(&p_);
            let expanded = rubi_expand_integrand(&integrand, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_1767(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, n_, n2_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1767,
        source: "Int[(d_+e_.*x_^n_)^q_*(a_+c_.*x_^n2_)^p_,x_Symbol] :=
          Int[ExpandIntegrand[(d+e*x^n)^q*(a+c*x^(2*n))^p,x],x] /;
        FreeQ[{a,c,d,e,n,p,q},x] && EqQ[n2,2*n] && NeQ[c*d^2+a*e^2,0] &&
          (IntegersQ[p,q] && Not[IntegerQ[n]] || IGtQ[p,0] || IGtQ[q,0] && Not[IntegerQ[n]])",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_12(symbols),
        with: [d__, e__, n_, q_, a__, c__, n2_, p_, x_],
        optional: [e__, c__],
        x_free: [a__, c__, d__, e__, n_, p_, q_],
        when: {
            freeq!([a__, c__, d__, e__, n_, p_, q_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && neq!(&c__ * d__.pow(2) + &a__ * e__.pow(2), 0)
                && (integersq!([p_, q_]) && !integerq!(n_)
                    || igtq!(p_, 0)
                    || igtq!(q_, 0) && !integerq!(n_))
        },
        rhs: {
            let integrand = (&d__ + &e__ * x_.pow(&n_)).pow(&q_)
                * (&a__ + &c__ * x_.pow(Atom::num(2) * &n_)).pow(&p_);
            let expanded = rubi_expand_integrand(&integrand, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_1768(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, n_, n2_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1768,
        source: "Int[(d_+e_.*x_^n_)^q_*(a_+c_.*x_^n2_)^p_,x_Symbol] :=
          Int[ExpandIntegrand[(a+c*x^(2*n))^p,(d/(d^2-e^2*x^(2*n))-e*x^n/(d^2-e^2*x^(2*n)))^(-q),x],x] /;
        FreeQ[{a,c,d,e,n,p},x] && EqQ[n2,2*n] && NeQ[c*d^2+a*e^2,0] && Not[IntegerQ[p]] && ILtQ[q,0]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_12(symbols),
        with: [d__, e__, n_, q_, a__, c__, n2_, p_, x_],
        optional: [e__, c__],
        x_free: [a__, c__, d__, e__, n_, p_],
        when: {
            freeq!([a__, c__, d__, e__, n_, p_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && neq!(&c__ * d__.pow(2) + &a__ * e__.pow(2), 0)
                && !integerq!(p_)
                && iltq!(q_, 0)
        },
        rhs: {
            let u = (&a__ + &c__ * x_.pow(Atom::num(2) * &n_)).pow(&p_);
            let denominator = d__.pow(2) - e__.pow(2) * x_.pow(Atom::num(2) * &n_);
            let v_expr = (&d__ / &denominator - &e__ * x_.pow(&n_) / denominator).pow(-&q_);
            let expanded = rubi_expand_integrand_product(&u, &v_expr, x_);

            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_1769(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, n2_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1769,
        source: "Int[(d_+e_.*x_^n_)^q_*(a_+b_.*x_^n_+c_.*x_^n2_)^p_,x_Symbol] :=
          Unintegrable[(d+e*x^n)^q*(a+b*x^n+c*x^(2*n))^p,x] /;
        FreeQ[{a,b,c,d,e,n,p,q},x] && EqQ[n2,2*n]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [d__, e__, n_, q_, a__, b__, c__, n2_, p_, x_],
        optional: [e__, b__, c__],
        x_free: [a__, b__, c__, d__, e__, n_, p_, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__, n_, p_, q_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
        },
        rhs: {
            let integrand = (&d__ + &e__ * x_.pow(&n_)).pow(&q_)
                * (&a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_))
                    .pow(&p_);

            rubi_unintegrable(integrand, x_)
        },
    ));
}

fn push_rules_rule_1770(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, n_, n2_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1770,
        source: "Int[(d_+e_.*x_^n_)^q_*(a_+c_.*x_^n2_)^p_,x_Symbol] :=
          Unintegrable[(d+e*x^n)^q*(a+c*x^(2*n))^p,x] /;
        FreeQ[{a,c,d,e,n,p,q},x] && EqQ[n2,2*n]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_12(symbols),
        with: [d__, e__, n_, q_, a__, c__, n2_, p_, x_],
        optional: [e__, c__],
        x_free: [a__, c__, d__, e__, n_, p_, q_],
        when: {
            freeq!([a__, c__, d__, e__, n_, p_, q_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
        },
        rhs: {
            let integrand = (&d__ + &e__ * x_.pow(&n_)).pow(&q_)
                * (&a__ + &c__ * x_.pow(Atom::num(2) * &n_)).pow(&p_);

            rubi_unintegrable(integrand, x_)
        },
    ));
}

fn push_rules_rule_1771(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, n_, n2_, p_, q_, u__);
    let rule = rubi_rule!(
        order: 1771,
        source: "Int[(d_+e_.*u_^n_)^q_.*(a_+b_.*u_^n_+c_.*u_^n2_)^p_.,x_Symbol] :=
          1/Coefficient[u,x,1] \\[Star] Subst[Int[(d+e*x^n)^q*(a+b*x^n+c*x^(2*n))^p,x],x,u] /;
        FreeQ[{a,b,c,d,e,n,p,q},x] && EqQ[n2,2*n] && LinearQ[u,x] && NeQ[u,x]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (d__ + e__ * u__.pow(n_)).pow(q_)
            * (a__ + b__ * u__.pow(n_) + c__ * u__.pow(n2_)).pow(p_),
        with: [d__, e__, u__, n_, q_, a__, b__, c__, n2_, p_, x_],
        optional: [e__, q_, b__, c__, p_],
        x_dep: [u__],
        x_free: [a__, b__, c__, d__, e__, n_, p_, q_],
        x_linear: [u__],
        when: {
            freeq!([a__, b__, c__, d__, e__, n_, p_, q_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && neq!(u__, x_)
        },
        rhs: {
            let linear_coefficient = rubi_coeff(&u__, x_, 1).unwrap();
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = (&d__ + &e__ * sub_atom.pow(&n_)).pow(&q_)
                * (&a__
                    + &b__ * sub_atom.pow(&n_)
                    + &c__ * sub_atom.pow(Atom::num(2) * &n_))
                .pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);
            let substituted = rubi_subst(&transformed, sub, u__);
            let coefficient = Atom::num(1) / linear_coefficient;

            rubi_star(coefficient, substituted)
        },
    );
    rules.push(
        rule.with_early_not_integration_variable(u__)
            .with_repeated_proper_x_dependent_subexpression(),
    );
}

fn push_rules_rule_1772(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, c__, d__, e__, n_, n2_, p_, q_, u__);
    let rule = rubi_rule!(
        order: 1772,
        source: "Int[(d_+e_.*u_^n_)^q_.*(a_+c_.*u_^n2_)^p_.,x_Symbol] :=
          1/Coefficient[u,x,1] \\[Star] Subst[Int[(d+e*x^n)^q*(a+c*x^(2*n))^p,x],x,u] /;
        FreeQ[{a,c,d,e,n,p,q},x] && EqQ[n2,2*n] && LinearQ[u,x] && NeQ[u,x]",
        desc: "Integration by substitution",
        refs: [],
        pattern: (d__ + e__ * u__.pow(n_)).pow(q_) * (a__ + c__ * u__.pow(n2_)).pow(p_),
        with: [d__, e__, u__, n_, q_, a__, c__, n2_, p_, x_],
        optional: [e__, q_, c__, p_],
        x_dep: [u__],
        x_free: [a__, c__, d__, e__, n_, p_, q_],
        x_linear: [u__],
        when: {
            freeq!([a__, c__, d__, e__, n_, p_, q_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && neq!(u__, x_)
        },
        rhs: {
            let linear_coefficient = rubi_coeff(&u__, x_, 1).unwrap();
            let substitution_guard = fresh_substitution_symbol().unwrap();
            let sub = substitution_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = (&d__ + &e__ * sub_atom.pow(&n_)).pow(&q_)
                * (&a__ + &c__ * sub_atom.pow(Atom::num(2) * &n_)).pow(&p_);
            let transformed = rubi_rhs_int(&transformed_integrand, sub);
            let substituted = rubi_subst(&transformed, sub, u__);
            let coefficient = Atom::num(1) / linear_coefficient;

            rubi_star(coefficient, substituted)
        },
    );
    rules.push(
        rule.with_early_not_integration_variable(u__)
            .with_repeated_proper_x_dependent_subexpression(),
    );
}

fn push_rules_rule_1773(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, x_, mn_, n_, n2_, p_, q_);
    rules.push(rubi_rule!(
        order: 1773,
        source: "Int[(d_+e_.*x_^mn_.)^q_.*(a_.+b_.*x_^n_.+c_.*x_^n2_.)^p_.,x_Symbol] :=
          Int[x^(-n*q)*(e+d*x^n)^q*(a+b*x^n+c*x^(2*n))^p,x] /;
        FreeQ[{a,b,c,d,e,n,p},x] && EqQ[n2,2*n] && EqQ[mn,-n] && IntegerQ[q] && (PosQ[n] || Not[IntegerQ[p]])",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [d__, e__, mn_, q_, a__, b__, n_, c__, n2_, p_, x_],
        optional: [e__, mn_, q_, a__, b__, n_, c__, n2_, p_],
        x_free: [a__, b__, c__, d__, e__, n_, p_],
        integer: [q_],
        scaled: [(n2_, 2, n_), (mn_, -1, n_)],
        when: {
            freeq!([a__, b__, c__, d__, e__, n_, p_], x_)
                && integerq!(q_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && eqq!(mn_, -&n_)
                && (posq!(n_) || !integerq!(p_))
        },
        rhs: {
            let recursive_integrand = x_.pow(-&n_ * &q_)
                * (&e__ + &d__ * x_.pow(&n_)).pow(&q_)
                * (&a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_)).pow(&p_);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_1774(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, x_, mn_, n2_, p_, q_);
    rules.push(rubi_rule!(
        order: 1774,
        source: "Int[(d_+e_.*x_^mn_.)^q_.*(a_+c_.*x_^n2_.)^p_.,x_Symbol] :=
          Int[x^(mn*q)*(e+d*x^(-mn))^q*(a+c*x^n2)^p,x] /;
        FreeQ[{a,c,d,e,mn,p},x] && EqQ[n2,-2*mn] && IntegerQ[q] && (PosQ[n2] || Not[IntegerQ[p]])",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [d__, e__, mn_, q_, a__, c__, n2_, p_, x_],
        optional: [e__, mn_, q_, c__, n2_, p_],
        x_free: [a__, c__, d__, e__, mn_, p_],
        integer: [q_],
        scaled: [(n2_, -2, mn_)],
        when: {
            freeq!([a__, c__, d__, e__, mn_, p_], x_)
                && integerq!(q_)
                && eqq!(n2_, Atom::num(-2) * &mn_)
                && (posq!(n2_) || !integerq!(p_))
        },
        rhs: {
            let recursive_integrand = x_.pow(&mn_ * &q_)
                * (&e__ + &d__ * x_.pow(-&mn_)).pow(&q_)
                * (&a__ + &c__ * x_.pow(&n2_)).pow(&p_);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_1775(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, x_, mn_, mn2_, n_, p_, q_);
    rules.push(rubi_rule!(
        order: 1775,
        source: "Int[(d_+e_.*x_^n_.)^q_.*(a_.+b_.*x_^mn_.+c_.*x_^mn2_.)^p_.,x_Symbol] :=
          Int[x^(-2*n*p)*(d+e*x^n)^q*(c+b*x^n+a*x^(2*n))^p,x] /;
        FreeQ[{a,b,c,d,e,n,q},x] && EqQ[mn,-n] && EqQ[mn2,2*mn] && IntegerQ[p]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [d__, e__, n_, q_, a__, b__, mn_, c__, mn2_, p_, x_],
        optional: [e__, n_, q_, a__, b__, mn_, c__, mn2_, p_],
        x_free: [a__, b__, c__, d__, e__, n_, q_],
        integer: [p_],
        scaled: [(mn_, -1, n_), (mn2_, 2, mn_)],
        when: {
            freeq!([a__, b__, c__, d__, e__, n_, q_], x_)
                && integerq!(p_)
                && eqq!(mn_, -&n_)
                && eqq!(mn2_, Atom::num(2) * &mn_)
        },
        rhs: {
            let recursive_integrand = x_.pow(Atom::num(-2) * &n_ * &p_)
                * (&d__ + &e__ * x_.pow(&n_)).pow(&q_)
                * (&c__ + &b__ * x_.pow(&n_) + &a__ * x_.pow(Atom::num(2) * &n_)).pow(&p_);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_1776(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, x_, mn2_, n_, p_, q_);
    rules.push(rubi_rule!(
        order: 1776,
        source: "Int[(d_+e_.*x_^n_.)^q_.*(a_.+c_.*x_^mn2_.)^p_.,x_Symbol] :=
          Int[x^(-2*n*p)*(d+e*x^n)^q*(c+a*x^(2*n))^p,x] /;
        FreeQ[{a,c,d,e,n,q},x] && EqQ[mn2,-2*n] && IntegerQ[p]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_10(symbols),
        with: [d__, e__, n_, q_, a__, c__, mn2_, p_, x_],
        optional: [e__, n_, q_, a__, c__, mn2_, p_],
        x_free: [a__, c__, d__, e__, n_, q_],
        integer: [p_],
        scaled: [(mn2_, -2, n_)],
        when: {
            freeq!([a__, c__, d__, e__, n_, q_], x_)
                && integerq!(p_)
                && eqq!(mn2_, Atom::num(-2) * &n_)
        },
        rhs: {
            let recursive_integrand = x_.pow(Atom::num(-2) * &n_ * &p_)
                * (&d__ + &e__ * x_.pow(&n_)).pow(&q_)
                * (&c__ + &a__ * x_.pow(Atom::num(2) * &n_)).pow(&p_);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_1777(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, x_, mn_, n_, n2_, p_, q_);
    rules.push(rubi_rule!(
        order: 1777,
        source: "Int[(d_+e_.*x_^mn_.)^q_*(a_.+b_.*x_^n_.+c_.*x_^n2_.)^p_.,x_Symbol] :=
          e^IntPart[q]*x^(n*FracPart[q])*(d+e*x^(-n))^FracPart[q]/(1+d*x^n/e)^FracPart[q] \\[Star] Int[x^(-n*q)*(1+d*x^n/e)^q*(a+b*x^n+c*x^(2*n))^p,x] /;
        FreeQ[{a,b,c,d,e,n,p,q},x] && EqQ[n2,2*n] && EqQ[mn,-n] && Not[IntegerQ[p]] && Not[IntegerQ[q]] && PosQ[n]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [d__, e__, mn_, q_, a__, b__, n_, c__, n2_, p_, x_],
        optional: [e__, mn_, a__, b__, n_, c__, n2_, p_],
        x_free: [a__, b__, c__, d__, e__, n_, p_, q_],
        scaled: [(n2_, 2, n_), (mn_, -1, n_)],
        when: {
            freeq!([a__, b__, c__, d__, e__, n_, p_, q_], x_)
                && !integerq!(p_)
                && !integerq!(q_)
                && posq!(n_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && eqq!(mn_, -&n_)
        },
        rhs: {
            let frac_q = rubi_frac_part(&q_);
            let recursive_integrand = x_.pow(-&n_ * &q_)
                * (Atom::num(1) + &d__ * x_.pow(&n_) / &e__).pow(&q_)
                * (&a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_)).pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let coefficient = e__.pow(rubi_int_part(&q_))
                * x_.pow(&n_ * &frac_q)
                * (&d__ + &e__ * x_.pow(-&n_)).pow(&frac_q)
                / (Atom::num(1) + &d__ * x_.pow(&n_) / &e__).pow(frac_q);

            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_1778(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, x_, mn_, n2_, p_, q_);
    rules.push(rubi_rule!(
        order: 1778,
        source: "Int[(d_+e_.*x_^mn_.)^q_*(a_+c_.*x_^n2_.)^p_.,x_Symbol] :=
          e^IntPart[q]*x^(-mn*FracPart[q])*(d+e*x^mn)^FracPart[q]/(1+d*x^(-mn)/e)^FracPart[q] \\[Star] Int[x^(mn*q)*(1+d*x^(-mn)/e)^q*(a+c*x^n2)^p,x] /;
        FreeQ[{a,c,d,e,mn,p,q},x] && EqQ[n2,-2*mn] && Not[IntegerQ[p]] && Not[IntegerQ[q]] && PosQ[n2]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [d__, e__, mn_, q_, a__, c__, n2_, p_, x_],
        optional: [e__, mn_, c__, n2_, p_],
        x_free: [a__, c__, d__, e__, mn_, p_, q_],
        scaled: [(n2_, -2, mn_)],
        when: {
            freeq!([a__, c__, d__, e__, mn_, p_, q_], x_)
                && !integerq!(p_)
                && !integerq!(q_)
                && posq!(n2_)
                && eqq!(n2_, Atom::num(-2) * &mn_)
        },
        rhs: {
            let frac_q = rubi_frac_part(&q_);
            let recursive_integrand = x_.pow(&mn_ * &q_)
                * (Atom::num(1) + &d__ * x_.pow(-&mn_) / &e__).pow(&q_)
                * (&a__ + &c__ * x_.pow(&n2_)).pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let coefficient = e__.pow(rubi_int_part(&q_))
                * x_.pow(-&mn_ * &frac_q)
                * (&d__ + &e__ * x_.pow(&mn_)).pow(&frac_q)
                / (Atom::num(1) + &d__ * x_.pow(-&mn_) / &e__).pow(frac_q);

            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_1779(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, mn_, mn2_, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1779,
        source: "Int[(d_+e_.*x_^n_.)^q_.*(a_.+b_.*x_^mn_.+c_.*x_^mn2_.)^p_,x_Symbol] :=
          x^(2*n*FracPart[p])*(a+b*x^(-n)+c*x^(-2*n))^FracPart[p]/(c+b*x^n+a*x^(2*n))^FracPart[p] \\[Star]
            Int[x^(-2*n*p)*(d+e*x^n)^q*(c+b*x^n+a*x^(2*n))^p,x] /;
        FreeQ[{a,b,c,d,e,n,p,q},x] && EqQ[mn,-n] && EqQ[mn2,2*mn] && Not[IntegerQ[p]] && Not[IntegerQ[q]] && PosQ[n]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [d__, e__, n_, q_, a__, b__, mn_, c__, mn2_, p_, x_],
        optional: [e__, n_, q_, a__, b__, mn_, c__, mn2_],
        x_free: [a__, b__, c__, d__, e__, n_, p_, q_],
        scaled: [(mn_, -1, n_), (mn2_, 2, mn_)],
        when: {
            freeq!([a__, b__, c__, d__, e__, n_, p_, q_], x_)
                && eqq!(mn_, -&n_)
                && eqq!(mn2_, Atom::num(2) * &mn_)
                && !integerq!(p_)
                && !integerq!(q_)
                && posq!(n_)
        },
        rhs: {
            let frac_p = rubi_frac_part(&p_);
            let original = &a__ + &b__ * x_.pow(-&n_) + &c__ * x_.pow(Atom::num(-2) * &n_);
            let transformed = &c__ + &b__ * x_.pow(&n_) + &a__ * x_.pow(Atom::num(2) * &n_);
            let recursive_integrand = x_.pow(Atom::num(-2) * &n_ * &p_)
                * (&d__ + &e__ * x_.pow(&n_)).pow(&q_)
                * transformed.pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let coefficient = x_.pow(Atom::num(2) * &n_ * &frac_p)
                * original.pow(&frac_p)
                / transformed.pow(frac_p);

            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_1780(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, mn2_, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1780,
        source: "Int[(d_+e_.*x_^n_.)^q_.*(a_.+c_.*x_^mn2_.)^p_,x_Symbol] :=
          x^(2*n*FracPart[p])*(a+c*x^(-2*n))^FracPart[p]/(c+a*x^(2*n))^FracPart[p] \\[Star]
            Int[x^(-2*n*p)*(d+e*x^n)^q*(c+a*x^(2*n))^p,x] /;
        FreeQ[{a,c,d,e,n,p,q},x] && EqQ[mn2,-2*n] && Not[IntegerQ[p]] && Not[IntegerQ[q]] && PosQ[n]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_10(symbols),
        with: [d__, e__, n_, q_, a__, c__, mn2_, p_, x_],
        optional: [e__, n_, q_, a__, c__, mn2_],
        x_free: [a__, c__, d__, e__, n_, p_, q_],
        scaled: [(mn2_, -2, n_)],
        when: {
            freeq!([a__, c__, d__, e__, n_, p_, q_], x_)
                && eqq!(mn2_, Atom::num(-2) * &n_)
                && !integerq!(p_)
                && !integerq!(q_)
                && posq!(n_)
        },
        rhs: {
            let frac_p = rubi_frac_part(&p_);
            let original = &a__ + &c__ * x_.pow(Atom::num(-2) * &n_);
            let transformed = &c__ + &a__ * x_.pow(Atom::num(2) * &n_);
            let recursive_integrand = x_.pow(Atom::num(-2) * &n_ * &p_)
                * (&d__ + &e__ * x_.pow(&n_)).pow(&q_)
                * transformed.pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let coefficient = x_.pow(Atom::num(2) * &n_ * &frac_p)
                * original.pow(&frac_p)
                / transformed.pow(frac_p);

            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_1781(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, mn_, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1781,
        source: "Int[(d_+e_.*x_^n_)^q_.*(a_+b_.*x_^mn_+c_.*x_^n_.)^p_.,x_Symbol] :=
          Int[x^(-n*p)*(d+e*x^n)^q*(b+a*x^n+c*x^(2*n))^p,x] /;
        FreeQ[{a,b,c,d,e,n,q},x] && EqQ[mn,-n] && IntegerQ[p]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [d__, e__, n_, q_, a__, b__, mn_, c__, p_, x_],
        optional: [e__, n_, q_, b__, c__, p_],
        x_free: [a__, b__, c__, d__, e__, n_, q_],
        integer: [p_],
        scaled: [(mn_, -1, n_)],
        when: {
            freeq!([a__, b__, c__, d__, e__, n_, q_], x_)
                && eqq!(mn_, -&n_)
                && integerq!(p_)
        },
        rhs: {
            let recursive_integrand = x_.pow(-&n_ * &p_)
                * (&d__ + &e__ * x_.pow(&n_)).pow(&q_)
                * (&b__ + &a__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_)).pow(&p_);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_1782(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, mn_, n_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1782,
        source: "Int[(d_+e_.*x_^n_)^q_.*(a_+b_.*x_^mn_+c_.*x_^n_.)^p_.,x_Symbol] :=
          x^(n*FracPart[p])*(a+b/x^n+c*x^n)^FracPart[p]/(b+a*x^n+c*x^(2*n))^FracPart[p] \\[Star]
            Int[x^(-n*p)*(d+e*x^n)^q*(b+a*x^n+c*x^(2*n))^p,x] /;
        FreeQ[{a,b,c,d,e,n,p,q},x] && EqQ[mn,-n] && Not[IntegerQ[p]]",
        desc: "Apply a recurrence relation that reduces the integral.",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [d__, e__, n_, q_, a__, b__, mn_, c__, p_, x_],
        optional: [e__, n_, q_, b__, c__, p_],
        x_free: [a__, b__, c__, d__, e__, n_, p_, q_],
        scaled: [(mn_, -1, n_)],
        when: {
            freeq!([a__, b__, c__, d__, e__, n_, p_, q_], x_)
                && eqq!(mn_, -&n_)
                && !integerq!(p_)
        },
        rhs: {
            let frac_p = rubi_frac_part(&p_);
            let original = &a__ + &b__ / x_.pow(&n_) + &c__ * x_.pow(&n_);
            let transformed = &b__ + &a__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_);
            let recursive_integrand = x_.pow(-&n_ * &p_)
                * (&d__ + &e__ * x_.pow(&n_)).pow(&q_)
                * transformed.pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let coefficient =
                x_.pow(&n_ * &frac_p) * original.pow(&frac_p) / transformed.pow(frac_p);

            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_1783(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, n2_, f__, g__, p_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 1783,
        source: "Int[(d_+e_.*x_^n_)^q_.*(f_+g_.*x_^n_)^r_.*(a_+b_.*x_^n_+c_.*x_^n2_)^p_,x_Symbol] :=
          (a+b*x^n+c*x^(2*n))^FracPart[p]/((4*c)^IntPart[p]*(b+2*c*x^n)^(2*FracPart[p])) \\[Star]
            Int[(d+e*x^n)^q*(f+g*x^n)^r*(b+2*c*x^n)^(2*p),x] /;
        FreeQ[{a,b,c,d,e,f,g,n,p,q,r},x] && EqQ[n2,2*n] && EqQ[b^2-4*a*c,0] && Not[IntegerQ[p]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_13(symbols),
        with: [d__, e__, n_, q_, f__, g__, r_, a__, b__, c__, n2_, p_, x_],
        optional: [e__, q_, g__, r_, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, n_, p_, q_, r_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && eqq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && !integerq!(p_)
        },
        rhs: {
            let frac_p = rubi_frac_part(&p_);
            let trinomial = &a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_);
            let linear = &b__ + Atom::num(2) * &c__ * x_.pow(&n_);
            let recursive_integrand = (&d__ + &e__ * x_.pow(&n_)).pow(&q_)
                * (&f__ + &g__ * x_.pow(&n_)).pow(&r_)
                * linear.pow(Atom::num(2) * &p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let coefficient = trinomial.pow(&frac_p)
                / ((Atom::num(4) * &c__).pow(rubi_int_part(&p_))
                    * linear.pow(Atom::num(2) * frac_p));

            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_1784(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, n2_, f__, g__, p_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 1784,
        source: "Int[(d_+e_.*x_^n_)^q_.*(f_+g_.*x_^n_)^r_.*(a_+b_.*x_^n_+c_.*x_^n2_)^p_.,x_Symbol] :=
          Int[(d+e*x^n)^(p+q)*(f+g*x^n)^r*(a/d+c/e*x^n)^p,x] /;
        FreeQ[{a,b,c,d,e,f,g,n,q,r},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c,0] && EqQ[c*d^2-b*d*e+a*e^2,0] && IntegerQ[p]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_13(symbols),
        with: [d__, e__, n_, q_, f__, g__, r_, a__, b__, c__, n2_, p_, x_],
        optional: [e__, q_, g__, r_, b__, c__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, n_, q_, r_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && eqq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && integerq!(p_)
        },
        rhs: {
            let recursive_integrand = (&d__ + &e__ * x_.pow(&n_)).pow(&p_ + &q_)
                * (&f__ + &g__ * x_.pow(&n_)).pow(&r_)
                * (&a__ / &d__ + &c__ * x_.pow(&n_) / &e__).pow(&p_);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_1785(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, n_, n2_, f__, g__, p_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 1785,
        source: "Int[(d_+e_.*x_^n_)^q_.*(f_+g_.*x_^n_)^r_.*(a_+c_.*x_^n2_)^p_.,x_Symbol] :=
          Int[(d+e*x^n)^(p+q)*(f+g*x^n)^r*(a/d+c/e*x^n)^p,x] /;
        FreeQ[{a,c,d,e,f,g,n,q,r},x] && EqQ[n2,2*n] && EqQ[c*d^2+a*e^2,0] && IntegerQ[p]",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_14(symbols),
        with: [d__, e__, n_, q_, f__, g__, r_, a__, c__, n2_, p_, x_],
        optional: [e__, q_, g__, r_, c__, p_],
        when: {
            freeq!([a__, c__, d__, e__, f__, g__, n_, q_, r_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && eqq!(&c__ * d__.pow(2) + &a__ * e__.pow(2), 0)
                && integerq!(p_)
        },
        rhs: {
            let recursive_integrand = (&d__ + &e__ * x_.pow(&n_)).pow(&p_ + &q_)
                * (&f__ + &g__ * x_.pow(&n_)).pow(&r_)
                * (&a__ / &d__ + &c__ * x_.pow(&n_) / &e__).pow(&p_);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_1786(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, n_, n2_, f__, g__, p_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 1786,
        source: "Int[(d_+e_.*x_^n_)^q_.*(f_+g_.*x_^n_)^r_.*(a_+b_.*x_^n_+c_.*x_^n2_)^p_,x_Symbol] :=
          (a+b*x^n+c*x^(2*n))^FracPart[p]/((d+e*x^n)^FracPart[p]*(a/d+(c*x^n)/e)^FracPart[p]) \\[Star]
            Int[(d+e*x^n)^(p+q)*(f+g*x^n)^r*(a/d+c/e*x^n)^p,x] /;
        FreeQ[{a,b,c,d,e,f,g,n,p,q,r},x] && EqQ[n2,2*n] && NeQ[b^2-4*a*c,0] && EqQ[c*d^2-b*d*e+a*e^2,0] && Not[IntegerQ[p]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_13(symbols),
        with: [d__, e__, n_, q_, f__, g__, r_, a__, b__, c__, n2_, p_, x_],
        optional: [e__, q_, g__, r_, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, g__, n_, p_, q_, r_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && eqq!(&c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2), 0)
                && !integerq!(p_)
        },
        rhs: {
            let frac_p = rubi_frac_part(&p_);
            let trinomial = &a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_);
            let binomial = &d__ + &e__ * x_.pow(&n_);
            let transformed = &a__ / &d__ + &c__ * x_.pow(&n_) / &e__;
            let recursive_integrand = binomial.pow(&p_ + &q_)
                * (&f__ + &g__ * x_.pow(&n_)).pow(&r_)
                * transformed.pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let coefficient =
                trinomial.pow(&frac_p) / (binomial.pow(&frac_p) * transformed.pow(frac_p));

            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_1787(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, n_, n2_, f__, g__, p_, q_, r_, x_);
    rules.push(rubi_rule!(
        order: 1787,
        source: "Int[(d_+e_.*x_^n_)^q_.*(f_+g_.*x_^n_)^r_.*(a_+c_.*x_^n2_)^p_,x_Symbol] :=
          (a+c*x^(2*n))^FracPart[p]/((d+e*x^n)^FracPart[p]*(a/d+(c*x^n)/e)^FracPart[p]) \\[Star]
            Int[(d+e*x^n)^(p+q)*(f+g*x^n)^r*(a/d+c/e*x^n)^p,x] /;
        FreeQ[{a,c,d,e,f,g,n,p,q,r},x] && EqQ[n2,2*n] && EqQ[c*d^2+a*e^2,0] && Not[IntegerQ[p]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_14(symbols),
        with: [d__, e__, n_, q_, f__, g__, r_, a__, c__, n2_, p_, x_],
        optional: [e__, q_, g__, r_, c__],
        when: {
            freeq!([a__, c__, d__, e__, f__, g__, n_, p_, q_, r_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && eqq!(&c__ * d__.pow(2) + &a__ * e__.pow(2), 0)
                && !integerq!(p_)
        },
        rhs: {
            let frac_p = rubi_frac_part(&p_);
            let trinomial = &a__ + &c__ * x_.pow(Atom::num(2) * &n_);
            let binomial = &d__ + &e__ * x_.pow(&n_);
            let transformed = &a__ / &d__ + &c__ * x_.pow(&n_) / &e__;
            let recursive_integrand = binomial.pow(&p_ + &q_)
                * (&f__ + &g__ * x_.pow(&n_)).pow(&r_)
                * transformed.pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let coefficient =
                trinomial.pow(&frac_p) / (binomial.pow(&frac_p) * transformed.pow(frac_p));

            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_1788(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        a__, b__, c__, d1__, d2__, e1__, e2__, n_, n2_, non2_, p_, q_, x_
    );
    rules.push(rubi_rule!(
        order: 1788,
        source: "Int[(d1_+e1_.*x_^non2_.)^q_.*(d2_+e2_.*x_^non2_.)^q_.*(a_.+b_.*x_^n_+c_.*x_^n2_)^p_.,x_Symbol] :=
          Int[(d1*d2+e1*e2*x^n)^q*(a+b*x^n+c*x^(2*n))^p,x] /;
        FreeQ[{a,b,c,d1,e1,d2,e2,n,p,q},x] && EqQ[n2,2*n] && EqQ[non2,n/2] && EqQ[d2*e1+d1*e2,0] && (IntegerQ[q] || GtQ[d1,0] && GtQ[d2,0])",
        desc: "Algebraic simplification",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [d1__, e1__, non2_, q_, d2__, e2__, a__, b__, n_, c__, n2_, p_, x_],
        optional: [e1__, non2_, q_, e2__, a__, b__, c__, p_],
        when: {
            freeq!([a__, b__, c__, d1__, e1__, d2__, e2__, n_, p_, q_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && eqq!(non2_, &n_ / Atom::num(2))
                && eqq!(&d2__ * &e1__ + &d1__ * &e2__, 0)
                && (integerq!(q_) || gtq!(d1__, 0) && gtq!(d2__, 0))
        },
        rhs: {
            let recursive_integrand = (&d1__ * &d2__ + &e1__ * &e2__ * x_.pow(&n_)).pow(&q_)
                * (&a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_)).pow(&p_);

            rubi_rhs_int(&recursive_integrand, x_)
        },
    ));
}

fn push_rules_rule_1789(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols;
        a__, b__, c__, d1__, d2__, e1__, e2__, n_, n2_, non2_, p_, q_, x_
    );
    rules.push(rubi_rule!(
        order: 1789,
        source: "Int[(d1_+e1_.*x_^non2_.)^q_.*(d2_+e2_.*x_^non2_.)^q_.*(a_.+b_.*x_^n_+c_.*x_^n2_)^p_.,x_Symbol] :=
          (d1+e1*x^(n/2))^FracPart[q]*(d2+e2*x^(n/2))^FracPart[q]/(d1*d2+e1*e2*x^n)^FracPart[q] \\[Star]
            Int[(d1*d2+e1*e2*x^n)^q*(a+b*x^n+c*x^(2*n))^p,x] /;
        FreeQ[{a,b,c,d1,e1,d2,e2,n,p,q},x] && EqQ[n2,2*n] && EqQ[non2,n/2] && EqQ[d2*e1+d1*e2,0]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [d1__, e1__, non2_, q_, d2__, e2__, a__, b__, n_, c__, n2_, p_, x_],
        optional: [e1__, non2_, q_, e2__, a__, b__, c__, p_],
        when: {
            freeq!([a__, b__, c__, d1__, e1__, d2__, e2__, n_, p_, q_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && eqq!(non2_, &n_ / Atom::num(2))
                && eqq!(&d2__ * &e1__ + &d1__ * &e2__, 0)
        },
        rhs: {
            let frac_q = rubi_frac_part(&q_);
            let merged = &d1__ * &d2__ + &e1__ * &e2__ * x_.pow(&n_);
            let recursive_integrand = merged.pow(&q_)
                * (&a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_)).pow(&p_);
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let coefficient =
                (&d1__ + &e1__ * x_.pow(&n_ / Atom::num(2))).pow(&frac_q)
                    * (&d2__ + &e2__ * x_.pow(&n_ / Atom::num(2))).pow(&frac_q)
                    / merged.pow(frac_q);

            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_1790(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        a__,
        b__,
        c__,
        d__,
        e__,
        n_,
        n2_,
        capital_a__,
        capital_b__,
        m_,
        p_,
        q_,
        x_
    );
    rules.push(rubi_rule!(
        order: 1790,
        source: "Int[(A_+B_.*x_^m_.)*(d_+e_.*x_^n_)^q_.*(a_+b_.*x_^n_+c_.*x_^n2_)^p_.,x_Symbol] :=
          A \\[Star] Int[(d+e*x^n)^q*(a+b*x^n+c*x^(2*n))^p,x] + B \\[Star] Int[x^m*(d+e*x^n)^q*(a+b*x^n+c*x^(2*n))^p,x] /;
        FreeQ[{a,b,c,d,e,A,B,m,n,p,q},x] && EqQ[n2,2*n] && EqQ[m-n+1,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (capital_a__ + capital_b__ * x_.pow(m_))
            * (d__ + e__ * x_.pow(n_)).pow(q_)
            * (a__ + b__ * x_.pow(n_) + c__ * x_.pow(n2_)).pow(p_),
        with: [capital_a__, capital_b__, m_, d__, e__, n_, q_, a__, b__, c__, n2_, p_, x_],
        optional: [capital_b__, m_, e__, q_, b__, c__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, capital_a__, capital_b__, m_, n_, p_, q_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && eqq!(&m_ - &n_ + Atom::num(1), 0)
        },
        rhs: {
            let first_integrand = (&d__ + &e__ * x_.pow(&n_)).pow(&q_)
                * (&a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_)).pow(&p_);
            let second_integrand = x_.pow(&m_)
                * (&d__ + &e__ * x_.pow(&n_)).pow(&q_)
                * (&a__ + &b__ * x_.pow(&n_) + &c__ * x_.pow(Atom::num(2) * &n_)).pow(&p_);
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(capital_a__, first) + rubi_star(capital_b__, second)
        },
    ));
}

fn push_rules_rule_1791(rules: &mut Vec<RubiRule>) {
    rubi_symb!(
        a__,
        c__,
        d__,
        e__,
        n_,
        n2_,
        capital_a__,
        capital_b__,
        m_,
        p_,
        q_,
        x_
    );
    rules.push(rubi_rule!(
        order: 1791,
        source: "Int[(A_+B_.*x_^m_.)*(d_+e_.*x_^n_)^q_.*(a_+c_.*x_^n2_)^p_.,x_Symbol] :=
          A \\[Star] Int[(d+e*x^n)^q*(a+c*x^(2*n))^p,x] + B \\[Star] Int[x^m*(d+e*x^n)^q*(a+c*x^(2*n))^p,x] /;
        FreeQ[{a,c,d,e,A,B,m,n,p,q},x] && EqQ[n2,2*n] && EqQ[m-n+1,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern: (capital_a__ + capital_b__ * x_.pow(m_))
            * (d__ + e__ * x_.pow(n_)).pow(q_)
            * (a__ + c__ * x_.pow(n2_)).pow(p_),
        with: [capital_a__, capital_b__, m_, d__, e__, n_, q_, a__, c__, n2_, p_, x_],
        optional: [capital_b__, m_, e__, q_, c__, p_],
        when: {
            freeq!([a__, c__, d__, e__, capital_a__, capital_b__, m_, n_, p_, q_], x_)
                && eqq!(n2_, Atom::num(2) * &n_)
                && eqq!(&m_ - &n_ + Atom::num(1), 0)
        },
        rhs: {
            let first_integrand =
                (&d__ + &e__ * x_.pow(&n_)).pow(&q_) * (&a__ + &c__ * x_.pow(Atom::num(2) * &n_)).pow(&p_);
            let second_integrand = x_.pow(&m_)
                * (&d__ + &e__ * x_.pow(&n_)).pow(&q_)
                * (&a__ + &c__ * x_.pow(Atom::num(2) * &n_)).pow(&p_);
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(capital_a__, first) + rubi_star(capital_b__, second)
        },
    ));
}

// Generated shared pattern builders.

#[inline(never)]
fn rubi_shared_pattern_0(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d1__ = symbols.d1__;
    let d2__ = symbols.d2__;
    let e1__ = symbols.e1__;
    let e2__ = symbols.e2__;
    let n2_ = symbols.n2_;
    let n_ = symbols.n_;
    let non2_ = symbols.non2_;
    let p_ = symbols.p_;
    let q_ = symbols.q_;
    let x_ = symbols.x_;
    (d1__ + e1__ * x_.pow(non2_)).pow(q_)
        * (d2__ + e2__ * x_.pow(non2_)).pow(q_)
        * (a__ + b__ * x_.pow(n_) + c__ * x_.pow(n2_)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let mn_ = symbols.mn_;
    let n2_ = symbols.n2_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let q_ = symbols.q_;
    let x_ = symbols.x_;
    (d__ + e__ * x_.pow(mn_)).pow(q_) * (a__ + b__ * x_.pow(n_) + c__ * x_.pow(n2_)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_2(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let mn_ = symbols.mn_;
    let n2_ = symbols.n2_;
    let p_ = symbols.p_;
    let q_ = symbols.q_;
    let x_ = symbols.x_;
    (d__ + e__ * x_.pow(mn_)).pow(q_) * (a__ + c__ * x_.pow(n2_)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_3(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let n2_ = symbols.n2_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (d__ + e__ * x_.pow(n_)) * (a__ + b__ * x_.pow(n_) + c__ * x_.pow(n2_)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_4(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let n2_ = symbols.n2_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (d__ + e__ * x_.pow(n_)) * (a__ + c__ * x_.pow(n2_)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_5(symbols: &RubiSymbols) -> Atom {
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let n2_ = symbols.n2_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (d__ + e__ * x_.pow(n_)) * (b__ * x_.pow(n_) + c__ * x_.pow(n2_)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_6(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let mn2_ = symbols.mn2_;
    let mn_ = symbols.mn_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let q_ = symbols.q_;
    let x_ = symbols.x_;
    (d__ + e__ * x_.pow(n_)).pow(q_) * (a__ + b__ * x_.pow(mn_) + c__ * x_.pow(mn2_)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_7(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let mn_ = symbols.mn_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let q_ = symbols.q_;
    let x_ = symbols.x_;
    (d__ + e__ * x_.pow(n_)).pow(q_) * (a__ + b__ * x_.pow(mn_) + c__ * x_.pow(n_)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_8(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let n2_ = symbols.n2_;
    let n_ = symbols.n_;
    let q_ = symbols.q_;
    let x_ = symbols.x_;
    (d__ + e__ * x_.pow(n_)).pow(q_) * (a__ + b__ * x_.pow(n_) + c__ * x_.pow(n2_))
}

#[inline(never)]
fn rubi_shared_pattern_9(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let n2_ = symbols.n2_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let q_ = symbols.q_;
    let x_ = symbols.x_;
    (d__ + e__ * x_.pow(n_)).pow(q_) * (a__ + b__ * x_.pow(n_) + c__ * x_.pow(n2_)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_10(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let mn2_ = symbols.mn2_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let q_ = symbols.q_;
    let x_ = symbols.x_;
    (d__ + e__ * x_.pow(n_)).pow(q_) * (a__ + c__ * x_.pow(mn2_)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_11(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let n2_ = symbols.n2_;
    let n_ = symbols.n_;
    let q_ = symbols.q_;
    let x_ = symbols.x_;
    (d__ + e__ * x_.pow(n_)).pow(q_) * (a__ + c__ * x_.pow(n2_))
}

#[inline(never)]
fn rubi_shared_pattern_12(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let n2_ = symbols.n2_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let q_ = symbols.q_;
    let x_ = symbols.x_;
    (d__ + e__ * x_.pow(n_)).pow(q_) * (a__ + c__ * x_.pow(n2_)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_13(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let g__ = symbols.g__;
    let n2_ = symbols.n2_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let q_ = symbols.q_;
    let r_ = symbols.r_;
    let x_ = symbols.x_;
    (d__ + e__ * x_.pow(n_)).pow(q_)
        * (f__ + g__ * x_.pow(n_)).pow(r_)
        * (a__ + b__ * x_.pow(n_) + c__ * x_.pow(n2_)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_14(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let g__ = symbols.g__;
    let n2_ = symbols.n2_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let q_ = symbols.q_;
    let r_ = symbols.r_;
    let x_ = symbols.x_;
    (d__ + e__ * x_.pow(n_)).pow(q_)
        * (f__ + g__ * x_.pow(n_)).pow(r_)
        * (a__ + c__ * x_.pow(n2_)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_15(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let n2_ = symbols.n2_;
    let n_ = symbols.n_;
    let q_ = symbols.q_;
    let x_ = symbols.x_;
    (d__ + e__ * x_.pow(n_)).pow(q_) / (a__ + b__ * x_.pow(n_) + c__ * x_.pow(n2_))
}

#[inline(never)]
fn rubi_shared_pattern_16(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let n2_ = symbols.n2_;
    let n_ = symbols.n_;
    let q_ = symbols.q_;
    let x_ = symbols.x_;
    (d__ + e__ * x_.pow(n_)).pow(q_) / (a__ + c__ * x_.pow(n2_))
}

#[inline(never)]
fn rubi_shared_pattern_17(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let n2_ = symbols.n2_;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    (d__ + e__ * x_.pow(n_)) / (a__ + b__ * x_.pow(n_) + c__ * x_.pow(n2_))
}

#[inline(never)]
fn rubi_shared_pattern_18(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let n2_ = symbols.n2_;
    let n_ = symbols.n_;
    let x_ = symbols.x_;
    (d__ + e__ * x_.pow(n_)) / (a__ + c__ * x_.pow(n2_))
}

#[inline(never)]
fn rubi_shared_pattern_19(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let n2_ = symbols.n2_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let q_ = symbols.q_;
    let u__ = symbols.u__;
    let x_ = symbols.x_;
    u__ * (d__ + e__ * x_.pow(n_)).pow(q_) * (a__ + b__ * x_.pow(n_) + c__ * x_.pow(n2_)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_20(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let n2_ = symbols.n2_;
    let n_ = symbols.n_;
    let p_ = symbols.p_;
    let q_ = symbols.q_;
    let u__ = symbols.u__;
    let x_ = symbols.x_;
    u__ * (d__ + e__ * x_.pow(n_)).pow(q_) * (a__ + c__ * x_.pow(n2_)).pow(p_)
}
