use super::super::*;

pub(super) fn push_rules(rules: &mut Vec<RubiRule>) {
    push_rules_rule_1572(rules);
    push_rules_rule_1573(rules);
    push_rules_rule_1574(rules);
    push_rules_rule_1575(rules);
    push_rules_rule_1576(rules);
    push_rules_rule_1577(rules);
    push_rules_rule_1578(rules);
    push_rules_rule_1579(rules);
    push_rules_rule_1580(rules);
    push_rules_rule_1581(rules);
    push_rules_rule_1582(rules);
    push_rules_rule_1583(rules);
    push_rules_rule_1584(rules);
    push_rules_rule_1585(rules);
    push_rules_rule_1586(rules);
    push_rules_rule_1587(rules);
    push_rules_rule_1588(rules);
    push_rules_rule_1589(rules);
    push_rules_rule_1590(rules);
    push_rules_rule_1591(rules);
    push_rules_rule_1592(rules);
    push_rules_rule_1593(rules);
    push_rules_rule_1594(rules);
    push_rules_rule_1595(rules);
    push_rules_rule_1596(rules);
    push_rules_rule_1597(rules);
    push_rules_rule_1598(rules);
    push_rules_rule_1599(rules);
    push_rules_rule_1600(rules);
    push_rules_rule_1601(rules);
    push_rules_rule_1602(rules);
    push_rules_rule_1603(rules);
    push_rules_rule_1604(rules);
    push_rules_rule_1605(rules);
    push_rules_rule_1606(rules);
    push_rules_rule_1607(rules);
    push_rules_rule_1608(rules);
    push_rules_rule_1609(rules);
    push_rules_rule_1610(rules);
    push_rules_rule_1611(rules);
    push_rules_rule_1612(rules);
    push_rules_rule_1613(rules);
    push_rules_rule_1614(rules);
    push_rules_rule_1615(rules);
    push_rules_rule_1616(rules);
    push_rules_rule_1617(rules);
    push_rules_rule_1618(rules);
    push_rules_rule_1619(rules);
    push_rules_rule_1620(rules);
    push_rules_rule_1621(rules);
    push_rules_rule_1622(rules);
    push_rules_rule_1623(rules);
    push_rules_rule_1624(rules);
    push_rules_rule_1625(rules);
    push_rules_rule_1626(rules);
    push_rules_rule_1627(rules);
    push_rules_rule_1628(rules);
    push_rules_rule_1629(rules);
    push_rules_rule_1630(rules);
    push_rules_rule_1631(rules);
    push_rules_rule_1632(rules);
    push_rules_rule_1633(rules);
    push_rules_rule_1634(rules);
    push_rules_rule_1635(rules);
    push_rules_rule_1636(rules);
    push_rules_rule_1637(rules);
    push_rules_rule_1638(rules);
    push_rules_rule_1639(rules);
    push_rules_rule_1640(rules);
    push_rules_rule_1641(rules);
    push_rules_rule_1642(rules);
    push_rules_rule_1643(rules);
    push_rules_rule_1644(rules);
    push_rules_rule_1645(rules);
    push_rules_rule_1646(rules);
    push_rules_rule_1647(rules);
    push_rules_rule_1648(rules);
    push_rules_rule_1649(rules);
    push_rules_rule_1650(rules);
    push_rules_rule_1651(rules);
    push_rules_rule_1652(rules);
    push_rules_rule_1653(rules);
    push_rules_rule_1654(rules);
    push_rules_rule_1655(rules);
    push_rules_rule_1656(rules);
    push_rules_rule_1657(rules);
    push_rules_rule_1658(rules);
    push_rules_rule_1659(rules);
    push_rules_rule_1664(rules);
    push_rules_rule_1665(rules);
    push_rules_rule_1660(rules);
    push_rules_rule_1661(rules);
    push_rules_rule_1662(rules);
    push_rules_rule_1663(rules);
    push_rules_rule_1666(rules);
    push_rules_rule_1667(rules);
    push_rules_rule_1668(rules);
    push_rules_rule_1669(rules);
    push_rules_rule_1670(rules);
    push_rules_rule_1671(rules);
    push_rules_rule_1672(rules);
    push_rules_rule_1673(rules);
    push_rules_rule_1674(rules);
    push_rules_rule_1675(rules);
    push_rules_rule_1676(rules);
    push_rules_rule_1677(rules);
    push_rules_rule_1678(rules);
}

fn push_rules_rule_1572(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, e__, m_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1572,
        source: "Int[x_^m_.*(e_.*x_^2)^q_*(a_+b_.*x_^2+c_.*x_^4)^p_.,x_Symbol] :=
          1/(2*e^((m-1)/2)) \\[Star] Subst[Int[(e*x)^(q+(m-1)/2)*(a+b*x+c*x^2)^p,x],x,x^2] /;
        FreeQ[{a,b,c,e,p,q},x] && Not[IntegerQ[q]] && IntegerQ[(m-1)/2]",
        desc: "Integration by substitution",
        refs: [],
        pattern: x_.pow(m_) * (e__ * x_.pow(2)).pow(q_) * (a__ + b__ * x_.pow(2) + c__ * x_.pow(4)).pow(p_),
        with: [a__, b__, c__, e__, m_, p_, q_, x_],
        optional: [m_, e__, b__, c__, p_],
        x_free: [a__, b__, c__, e__, p_, q_],
        when: {
            freeq!([a__, b__, c__, e__, p_, q_], x_)
                && !integerq!(q_)
                && integerq!((&m_ - Atom::num(1)) / Atom::num(2))
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = (&e__ * &sub_atom).pow(&q_ + (&m_ - Atom::num(1)) / Atom::num(2))
                * (&a__ + &b__ * &sub_atom + &c__ * sub_atom.pow(2)).pow(&p_);
            let substituted = rubi_subst(
                &rubi_rhs_int(&transformed_integrand, sub),
                sub,
                x_.pow(2),
            );
            rubi_star(Atom::num(1)
                    / (Atom::num(2) * e__.pow((&m_ - Atom::num(1)) / Atom::num(2))), substituted)
        },
    ));
}

fn push_rules_rule_1573(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, c__, e__, m_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1573,
        source: "Int[x_^m_.*(e_.*x_^2)^q_*(a_+c_.*x_^4)^p_.,x_Symbol] :=
          1/(2*e^((m-1)/2)) \\[Star] Subst[Int[(e*x)^(q+(m-1)/2)*(a+c*x^2)^p,x],x,x^2] /;
        FreeQ[{a,c,e,p,q},x] && Not[IntegerQ[q]] && IntegerQ[(m-1)/2]",
        desc: "Integration by substitution",
        refs: [],
        pattern: x_.pow(m_) * (e__ * x_.pow(2)).pow(q_) * (a__ + c__ * x_.pow(4)).pow(p_),
        with: [a__, c__, e__, m_, p_, q_, x_],
        optional: [m_, e__, c__, p_],
        x_free: [a__, c__, e__, p_, q_],
        when: {
            freeq!([a__, c__, e__, p_, q_], x_)
                && !integerq!(q_)
                && integerq!((&m_ - Atom::num(1)) / Atom::num(2))
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand =
                (&e__ * &sub_atom).pow(&q_ + (&m_ - Atom::num(1)) / Atom::num(2)) * (&a__ + &c__ * sub_atom.pow(2)).pow(&p_);
            let substituted = rubi_subst(
                &rubi_rhs_int(&transformed_integrand, sub),
                sub,
                x_.pow(2),
            );
            rubi_star(Atom::num(1)
                    / (Atom::num(2) * e__.pow((&m_ - Atom::num(1)) / Atom::num(2))), substituted)
        },
    ));
}

fn push_rules_rule_1574(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, e__, f__, m_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1574,
        source: "Int[(f_.*x_)^m_.*(e_.*x_^2)^q_*(a_+b_.*x_^2+c_.*x_^4)^p_.,x_Symbol] :=
          e^IntPart[q]*(e*x^2)^FracPart[q]/(f^(2*IntPart[q])*(f*x)^(2*FracPart[q])) \\[Star] Int[(f*x)^(m+2*q)*(a+b*x^2+c*x^4)^p,x] /;
        FreeQ[{a,b,c,e,f,m,p,q},x] && Not[IntegerQ[q]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: (f__ * x_).pow(m_) * (e__ * x_.pow(2)).pow(q_) * (a__ + b__ * x_.pow(2) + c__ * x_.pow(4)).pow(p_),
        with: [a__, b__, c__, e__, f__, m_, p_, q_, x_],
        optional: [f__, m_, e__, b__, c__, p_],
        x_free: [a__, b__, c__, e__, f__, m_, p_, q_],
        when: {
            freeq!([a__, b__, c__, e__, f__, m_, p_, q_], x_)
                && !integerq!(q_)
        },
        rhs: {
            let int_q = rubi_int_part(&q_);
            let frac_q = rubi_frac_part(&q_);
            let denominator = f__.pow(Atom::num(2) * &int_q) * (&f__ * x_).pow(Atom::num(2) * &frac_q);
            let recursive_integrand =
                (&f__ * x_).pow(&m_ + Atom::num(2) * &q_) * (&a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4)).pow(&p_);
            rubi_star(e__.pow(&int_q) * (&e__ * x_.pow(2)).pow(&frac_q)
                    / denominator, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1575(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, c__, e__, f__, m_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1575,
        source: "Int[(f_.*x_)^m_.*(e_.*x_^2)^q_*(a_+c_.*x_^4)^p_.,x_Symbol] :=
          e^IntPart[q]*(e*x^2)^FracPart[q]/(f^(2*IntPart[q])*(f*x)^(2*FracPart[q])) \\[Star] Int[(f*x)^(m+2*q)*(a+c*x^4)^p,x] /;
        FreeQ[{a,c,e,f,m,p,q},x] && Not[IntegerQ[q]]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: (f__ * x_).pow(m_) * (e__ * x_.pow(2)).pow(q_) * (a__ + c__ * x_.pow(4)).pow(p_),
        with: [a__, c__, e__, f__, m_, p_, q_, x_],
        optional: [f__, m_, e__, c__, p_],
        x_free: [a__, c__, e__, f__, m_, p_, q_],
        when: {
            freeq!([a__, c__, e__, f__, m_, p_, q_], x_)
                && !integerq!(q_)
        },
        rhs: {
            let int_q = rubi_int_part(&q_);
            let frac_q = rubi_frac_part(&q_);
            let denominator = f__.pow(Atom::num(2) * &int_q) * (&f__ * x_).pow(Atom::num(2) * &frac_q);
            let recursive_integrand =
                (&f__ * x_).pow(&m_ + Atom::num(2) * &q_) * (&a__ + &c__ * x_.pow(4)).pow(&p_);
            rubi_star(e__.pow(&int_q) * (&e__ * x_.pow(2)).pow(&frac_q)
                    / denominator, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1576(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1576,
        source: "Int[x_*(d_+e_.*x_^2)^q_.*(a_+b_.*x_^2+c_.*x_^4)^p_.,x_Symbol] :=
          1/2 \\[Star] Subst[Int[(d+e*x)^q*(a+b*x+c*x^2)^p,x],x,x^2] /;
        FreeQ[{a,b,c,d,e,p,q},x]",
        desc: "Integration by substitution",
        refs: [],
        pattern: x_ * (d__ + e__ * x_.pow(2)).pow(q_) * (a__ + b__ * x_.pow(2) + c__ * x_.pow(4)).pow(p_),
        with: [a__, b__, c__, d__, e__, p_, q_, x_],
        optional: [q_, e__, b__, c__, p_],
        x_free: [a__, b__, c__, d__, e__, p_, q_],
        when: { freeq!([a__, b__, c__, d__, e__, p_, q_], x_) },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand =
                (&d__ + &e__ * &sub_atom).pow(&q_) * (&a__ + &b__ * &sub_atom + &c__ * sub_atom.pow(2)).pow(&p_);
            let substituted = rubi_subst(
                &rubi_rhs_int(&transformed_integrand, sub),
                sub,
                x_.pow(2),
            );
            rubi_star(Atom::num(1) / Atom::num(2), substituted)
        },
    ));
}

fn push_rules_rule_1577(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, c__, d__, e__, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1577,
        source: "Int[x_*(d_+e_.*x_^2)^q_.*(a_+c_.*x_^4)^p_.,x_Symbol] :=
          1/2 \\[Star] Subst[Int[(d+e*x)^q*(a+c*x^2)^p,x],x,x^2] /;
        FreeQ[{a,c,d,e,p,q},x]",
        desc: "Integration by substitution",
        refs: [],
        pattern: x_ * (d__ + e__ * x_.pow(2)).pow(q_) * (a__ + c__ * x_.pow(4)).pow(p_),
        with: [a__, c__, d__, e__, p_, q_, x_],
        optional: [q_, e__, c__, p_],
        x_free: [a__, c__, d__, e__, p_, q_],
        when: { freeq!([a__, c__, d__, e__, p_, q_], x_) },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = (&d__ + &e__ * &sub_atom).pow(&q_) * (&a__ + &c__ * sub_atom.pow(2)).pow(&p_);
            let substituted = rubi_subst(
                &rubi_rhs_int(&transformed_integrand, sub),
                sub,
                x_.pow(2),
            );
            rubi_star(Atom::num(1) / Atom::num(2), substituted)
        },
    ));
}

fn push_rules_rule_1578(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1578,
        source: "Int[x_^m_.*(d_+e_.*x_^2)^q_.*(a_+b_.*x_^2+c_.*x_^4)^p_.,x_Symbol] :=
          1/2 \\[Star] Subst[Int[x^((m-1)/2)*(d+e*x)^q*(a+b*x+c*x^2)^p,x],x,x^2] /;
        FreeQ[{a,b,c,d,e,p,q},x] && IntegerQ[(m-1)/2]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_16(symbols),
        with: [a__, b__, c__, d__, e__, m_, p_, q_, x_],
        optional: [m_, q_, e__, b__, c__, p_],
        x_free: [a__, b__, c__, d__, e__, p_, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__, p_, q_], x_)
                && integerq!((&m_ - Atom::num(1)) / Atom::num(2))
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = sub_atom.pow((&m_ - Atom::num(1)) / Atom::num(2))
                * (&d__ + &e__ * &sub_atom).pow(&q_)
                * (&a__ + &b__ * &sub_atom + &c__ * sub_atom.pow(2)).pow(&p_);
            let substituted = rubi_subst(
                &rubi_rhs_int(&transformed_integrand, sub),
                sub,
                x_.pow(2),
            );
            rubi_star(Atom::num(1) / Atom::num(2), substituted)
        },
    ));
}

fn push_rules_rule_1579(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, m_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1579,
        source: "Int[x_^m_.*(d_+e_.*x_^2)^q_.*(a_+c_.*x_^4)^p_.,x_Symbol] :=
          1/2 \\[Star] Subst[Int[x^((m-1)/2)*(d+e*x)^q*(a+c*x^2)^p,x],x,x^2] /;
        FreeQ[{a,c,d,e,p,q},x] && IntegerQ[(m+1)/2]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_17(symbols),
        with: [a__, c__, d__, e__, m_, p_, q_, x_],
        optional: [m_, q_, e__, c__, p_],
        x_free: [a__, c__, d__, e__, p_, q_],
        when: {
            freeq!([a__, c__, d__, e__, p_, q_], x_)
                && integerq!((&m_ + Atom::num(1)) / Atom::num(2))
        },
        rhs: {
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand =
                sub_atom.pow((&m_ - Atom::num(1)) / Atom::num(2)) * (&d__ + &e__ * &sub_atom).pow(&q_) * (&a__ + &c__ * sub_atom.pow(2)).pow(&p_);
            let substituted = rubi_subst(
                &rubi_rhs_int(&transformed_integrand, sub),
                sub,
                x_.pow(2),
            );
            rubi_star(Atom::num(1) / Atom::num(2), substituted)
        },
    ));
}

fn push_rules_rule_1580(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1580,
        source: "Int[x_^m_.*(d_+e_.*x_^2)^q_*(a_+b_.*x_^2+c_.*x_^4)^p_.,x_Symbol] :=
          (-d)^(m/2-1)*(c*d^2-b*d*e+a*e^2)^p*x*(d+e*x^2)^(q+1)/(2*e^(2*p+m/2)*(q+1)) +
          1/(2*e^(2*p+m/2)*(q+1)) \\[Star] Int[(d+e*x^2)^(q+1)*
            ExpandToSum[Together[1/(d+e*x^2)*(2*e^(2*p+m/2)*(q+1)*x^m*(a+b*x^2+c*x^4)^p-
              (-d)^(m/2-1)*(c*d^2-b*d*e+a*e^2)^p*(d+e*(2*q+3)*x^2))],x],x] /;
        FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && IGtQ[p,0] && ILtQ[q,-1] && IGtQ[m/2,0]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_16(symbols),
        with: [a__, b__, c__, d__, e__, m_, p_, q_, x_],
        optional: [m_, e__, b__, c__, p_],
        x_free: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && igtq!(p_, 0)
                && iltq!(q_, -1)
                && igtq!(&m_ / Atom::num(2), 0)
        },
        rhs: {
            let denominator = Atom::num(2) * e__.pow(Atom::num(2) * &p_ + &m_ / Atom::num(2)) * (&q_ + Atom::num(1));
            let quadratic = &d__ + &e__ * x_.pow(2);
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let invariant = &c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2);
            let direct = (-&d__).pow(&m_ / Atom::num(2) - Atom::num(1))
                * invariant.pow(&p_)
                * x_
                * quadratic.pow(&q_ + Atom::num(1))
                / &denominator;
            let together_inner = Atom::num(2)
                * e__.pow(Atom::num(2) * &p_ + &m_ / Atom::num(2))
                * (&q_ + Atom::num(1))
                * x_.pow(&m_)
                * quartic.pow(&p_)
                - (-&d__).pow(&m_ / Atom::num(2) - Atom::num(1))
                    * invariant.pow(&p_)
                    * (&d__ + &e__ * (Atom::num(2) * &q_ + Atom::num(3)) * x_.pow(2));
            let together_argument = Atom::num(1) / &quadratic * together_inner;
            let together_payload = rubi_together(&together_argument);
            let expand_to_sum = rubi_expand_to_sum(&together_payload, x_);
            let recursive_integrand = quadratic.pow(&q_ + Atom::num(1)) * expand_to_sum;

            rubi_simp(&(direct), x_)
                    + rubi_star(Atom::num(1) / denominator, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1581(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, m_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1581,
        source: "Int[x_^m_.*(d_+e_.*x_^2)^q_*(a_+c_.*x_^4)^p_.,x_Symbol] :=
          (-d)^(m/2-1)*(c*d^2+a*e^2)^p*x*(d+e*x^2)^(q+1)/(2*e^(2*p+m/2)*(q+1)) +
          1/(2*e^(2*p+m/2)*(q+1)) \\[Star] Int[(d+e*x^2)^(q+1)*
            ExpandToSum[Together[1/(d+e*x^2)*(2*e^(2*p+m/2)*(q+1)*x^m*(a+c*x^4)^p-
              (-d)^(m/2-1)*(c*d^2+a*e^2)^p*(d+e*(2*q+3)*x^2))],x],x] /;
        FreeQ[{a,c,d,e},x] && IGtQ[p,0] && ILtQ[q,-1] && IGtQ[m/2,0]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_17(symbols),
        with: [a__, c__, d__, e__, m_, p_, q_, x_],
        optional: [m_, e__, c__, p_],
        x_free: [a__, c__, d__, e__],
        when: {
            freeq!([a__, c__, d__, e__], x_)
                && igtq!(p_, 0)
                && iltq!(q_, -1)
                && igtq!(&m_ / Atom::num(2), 0)
        },
        rhs: {
            let denominator = Atom::num(2) * e__.pow(Atom::num(2) * &p_ + &m_ / Atom::num(2)) * (&q_ + Atom::num(1));
            let quadratic = &d__ + &e__ * x_.pow(2);
            let quartic = &a__ + &c__ * x_.pow(4);
            let invariant = &c__ * d__.pow(2) + &a__ * e__.pow(2);
            let direct = (-&d__).pow(&m_ / Atom::num(2) - Atom::num(1))
                * invariant.pow(&p_)
                * x_
                * quadratic.pow(&q_ + Atom::num(1))
                / &denominator;
            let together_inner = Atom::num(2)
                * e__.pow(Atom::num(2) * &p_ + &m_ / Atom::num(2))
                * (&q_ + Atom::num(1))
                * x_.pow(&m_)
                * quartic.pow(&p_)
                - (-&d__).pow(&m_ / Atom::num(2) - Atom::num(1))
                    * invariant.pow(&p_)
                    * (&d__ + &e__ * (Atom::num(2) * &q_ + Atom::num(3)) * x_.pow(2));
            let together_argument = Atom::num(1) / &quadratic * together_inner;
            let together_payload = rubi_together(&together_argument);
            let expand_to_sum = rubi_expand_to_sum(&together_payload, x_);
            let recursive_integrand = quadratic.pow(&q_ + Atom::num(1)) * expand_to_sum;

            rubi_simp(&(direct), x_)
                    + rubi_star(Atom::num(1) / denominator, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1582(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1582,
        source: "Int[x_^m_*(d_+e_.*x_^2)^q_*(a_+b_.*x_^2+c_.*x_^4)^p_.,x_Symbol] :=
          (-d)^(m/2-1)*(c*d^2-b*d*e+a*e^2)^p*x*(d+e*x^2)^(q+1)/(2*e^(2*p+m/2)*(q+1)) +
          (-d)^(m/2-1)/(2*e^(2*p)*(q+1)) \\[Star] Int[x^m*(d+e*x^2)^(q+1)*
            ExpandToSum[Together[1/(d+e*x^2)*(2*(-d)^(-m/2+1)*e^(2*p)*(q+1)*(a+b*x^2+c*x^4)^p -
              (e^(-m/2)*(c*d^2-b*d*e+a*e^2)^p*x^(-m))*(d+e*(2*q+3)*x^2))],x],x] /;
        FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && IGtQ[p,0] && ILtQ[q,-1] && ILtQ[m/2,0]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_16(symbols),
        with: [a__, b__, c__, d__, e__, m_, p_, q_, x_],
        optional: [e__, b__, c__, p_],
        x_free: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && igtq!(p_, 0)
                && iltq!(q_, -1)
                && iltq!(&m_ / Atom::num(2), 0)
        },
        rhs: {
            let direct_denominator =
                Atom::num(2) * e__.pow(Atom::num(2) * &p_ + &m_ / Atom::num(2)) * (&q_ + Atom::num(1));
            let recursive_denominator =
                Atom::num(2) * e__.pow(Atom::num(2) * &p_) * (&q_ + Atom::num(1));
            let quadratic = &d__ + &e__ * x_.pow(2);
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let invariant = &c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2);
            let direct = (-&d__).pow(&m_ / Atom::num(2) - Atom::num(1))
                * invariant.pow(&p_)
                * x_
                * quadratic.pow(&q_ + Atom::num(1))
                / &direct_denominator;
            let together_inner = Atom::num(2)
                * (-&d__).pow(-&m_ / Atom::num(2) + Atom::num(1))
                * e__.pow(Atom::num(2) * &p_)
                * (&q_ + Atom::num(1))
                * quartic.pow(&p_)
                - e__.pow(-&m_ / Atom::num(2))
                    * invariant.pow(&p_)
                    * x_.pow(-&m_)
                    * (&d__ + &e__ * (Atom::num(2) * &q_ + Atom::num(3)) * x_.pow(2));
            let together_argument = Atom::num(1) / &quadratic * together_inner;
            let together_payload = rubi_together(&together_argument);
            let expand_to_sum = rubi_expand_to_sum(&together_payload, x_);
            let recursive_integrand = x_.pow(&m_) * quadratic.pow(&q_ + Atom::num(1)) * expand_to_sum;

            rubi_simp(&(direct), x_)
                    + rubi_star((-&d__).pow(&m_ / Atom::num(2) - Atom::num(1))
                            / recursive_denominator, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1583(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, m_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1583,
        source: "Int[x_^m_*(d_+e_.*x_^2)^q_*(a_+c_.*x_^4)^p_.,x_Symbol] :=
          (-d)^(m/2-1)*(c*d^2+a*e^2)^p*x*(d+e*x^2)^(q+1)/(2*e^(2*p+m/2)*(q+1)) +
          (-d)^(m/2-1)/(2*e^(2*p)*(q+1)) \\[Star] Int[x^m*(d+e*x^2)^(q+1)*
            ExpandToSum[Together[1/(d+e*x^2)*(2*(-d)^(-m/2+1)*e^(2*p)*(q+1)*(a+c*x^4)^p -
              (e^(-m/2)*(c*d^2+a*e^2)^p*x^(-m))*(d+e*(2*q+3)*x^2))],x],x] /;
        FreeQ[{a,c,d,e},x] && IGtQ[p,0] && ILtQ[q,-1] && ILtQ[m/2,0]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_17(symbols),
        with: [a__, c__, d__, e__, m_, p_, q_, x_],
        optional: [e__, c__, p_],
        x_free: [a__, c__, d__, e__],
        when: {
            freeq!([a__, c__, d__, e__], x_)
                && igtq!(p_, 0)
                && iltq!(q_, -1)
                && iltq!(&m_ / Atom::num(2), 0)
        },
        rhs: {
            let direct_denominator =
                Atom::num(2) * e__.pow(Atom::num(2) * &p_ + &m_ / Atom::num(2)) * (&q_ + Atom::num(1));
            let recursive_denominator =
                Atom::num(2) * e__.pow(Atom::num(2) * &p_) * (&q_ + Atom::num(1));
            let quadratic = &d__ + &e__ * x_.pow(2);
            let quartic = &a__ + &c__ * x_.pow(4);
            let invariant = &c__ * d__.pow(2) + &a__ * e__.pow(2);
            let direct = (-&d__).pow(&m_ / Atom::num(2) - Atom::num(1))
                * invariant.pow(&p_)
                * x_
                * quadratic.pow(&q_ + Atom::num(1))
                / &direct_denominator;
            let together_inner = Atom::num(2)
                * (-&d__).pow(-&m_ / Atom::num(2) + Atom::num(1))
                * e__.pow(Atom::num(2) * &p_)
                * (&q_ + Atom::num(1))
                * quartic.pow(&p_)
                - e__.pow(-&m_ / Atom::num(2))
                    * invariant.pow(&p_)
                    * x_.pow(-&m_)
                    * (&d__ + &e__ * (Atom::num(2) * &q_ + Atom::num(3)) * x_.pow(2));
            let together_argument = Atom::num(1) / &quadratic * together_inner;
            let together_payload = rubi_together(&together_argument);
            let expand_to_sum = rubi_expand_to_sum(&together_payload, x_);
            let recursive_integrand = x_.pow(&m_) * quadratic.pow(&q_ + Atom::num(1)) * expand_to_sum;

            rubi_simp(&(direct), x_)
                    + rubi_star((-&d__).pow(&m_ / Atom::num(2) - Atom::num(1))
                            / recursive_denominator, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1584(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1584,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^q_.*(a_+b_.*x_^2+c_.*x_^4)^p_.,x_Symbol] :=
          Int[ExpandIntegrand[(f*x)^m(d+e*x^2)^q*(a+b*x^2+c*x^4)^p,x],x] /;
        FreeQ[{a,b,c,d,e,f,m,q},x] && NeQ[b^2-4*a*c,0] && IGtQ[p,0] && IGtQ[q,-2]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, b__, c__, d__, e__, f__, m_, p_, q_, x_],
        optional: [f__, m_, e__, q_, b__, c__, p_],
        x_free: [a__, b__, c__, d__, e__, f__, m_, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, q_], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && igtq!(p_, 0)
                && igtq!(q_, -2)
        },
        rhs: {
            let integrand = (&f__ * x_).pow(&m_)
                * (&d__ + &e__ * x_.pow(2)).pow(&q_)
                * (&a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4)).pow(&p_);
            let expanded = rubi_expand_integrand(&integrand, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_1585(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, m_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1585,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^q_.*(a_+c_.*x_^4)^p_.,x_Symbol] :=
          Int[ExpandIntegrand[(f*x)^m(d+e*x^2)^q*(a+c*x^4)^p,x],x] /;
        FreeQ[{a,c,d,e,f,m,q},x] && IGtQ[p,0] && IGtQ[q,-2]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [a__, c__, d__, e__, f__, m_, p_, q_, x_],
        optional: [f__, m_, e__, q_, c__, p_],
        x_free: [a__, c__, d__, e__, f__, m_, q_],
        when: {
            freeq!([a__, c__, d__, e__, f__, m_, q_], x_)
                && igtq!(p_, 0)
                && igtq!(q_, -2)
        },
        rhs: {
            let integrand = (&f__ * x_).pow(&m_)
                * (&d__ + &e__ * x_.pow(2)).pow(&q_)
                * (&a__ + &c__ * x_.pow(4)).pow(&p_);
            let expanded = rubi_expand_integrand(&integrand, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_1586(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1586,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^q_*(a_+b_.*x_^2+c_.*x_^4)^p_.,x_Symbol] :=
          With[{Qx=PolynomialQuotient[(a+b*x^2+c*x^4)^p,d+e*x^2,x],
                R=Coeff[PolynomialRemainder[(a+b*x^2+c*x^4)^p,d+e*x^2,x],x,0]},
          -R*(f*x)^(m+1)*(d+e*x^2)^(q+1)/(2*d*f*(q+1)) +
          f/(2*d*(q+1)) \\[Star] Int[(f*x)^(m-1)*(d+e*x^2)^(q+1)*ExpandToSum[2*d*(q+1)*x*Qx+R*(m+2*q+3)*x,x],x]] /;
        FreeQ[{a,b,c,d,e,f},x] && NeQ[b^2-4*a*c,0] && IGtQ[p,0] && LtQ[q,-1] && GtQ[m,0]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, b__, c__, d__, e__, f__, m_, p_, q_, x_],
        optional: [f__, m_, e__, b__, c__, p_],
        x_free: [a__, b__, c__, d__, e__, f__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && igtq!(p_, 0)
                && ltq!(q_, -1)
                && gtq!(m_, 0)
        },
        rhs: {
            let direct_denominator = Atom::num(2) * &d__ * &f__ * (&q_ + Atom::num(1));
            let recursive_denominator = Atom::num(2) * &d__ * (&q_ + Atom::num(1));
            let fx = &f__ * x_;
            let quadratic = &d__ + &e__ * x_.pow(2);
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let quartic_power = quartic.pow(&p_).expand();
            let Qx = rubi_polynomial_quotient(&quartic_power, &quadratic, x_).rubi_rhs();
            let polynomial_remainder = rubi_polynomial_remainder(&quartic_power, &quadratic, x_).rubi_rhs();
            let R = rubi_coeff(&polynomial_remainder, x_, 0).rubi_rhs();
            let direct = -&R * fx.pow(&m_ + Atom::num(1)) * quadratic.pow(&q_ + Atom::num(1))
                / &direct_denominator;
            let expand_to_sum = rubi_expand_to_sum(
                &(Atom::num(2) * &d__ * (&q_ + Atom::num(1)) * x_ * Qx
                    + &R * (&m_ + Atom::num(2) * &q_ + Atom::num(3)) * x_),
                x_,
            );
            let recursive_integrand =
                fx.pow(&m_ - Atom::num(1)) * quadratic.pow(&q_ + Atom::num(1)) * expand_to_sum;

            rubi_simp(&(direct), x_)
                    + rubi_star(&f__ / recursive_denominator, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1587(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, m_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1587,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^q_*(a_+c_.*x_^4)^p_.,x_Symbol] :=
          With[{Qx=PolynomialQuotient[(a+c*x^4)^p,d+e*x^2,x],
                R=Coeff[PolynomialRemainder[(a+c*x^4)^p,d+e*x^2,x],x,0]},
          -R*(f*x)^(m+1)*(d+e*x^2)^(q+1)/(2*d*f*(q+1)) +
          f/(2*d*(q+1)) \\[Star] Int[(f*x)^(m-1)*(d+e*x^2)^(q+1)*ExpandToSum[2*d*(q+1)*x*Qx+R*(m+2*q+3)*x,x],x]] /;
        FreeQ[{a,c,d,e,f},x] && IGtQ[p,0] && LtQ[q,-1] && GtQ[m,0]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [a__, c__, d__, e__, f__, m_, p_, q_, x_],
        optional: [f__, m_, e__, c__, p_],
        x_free: [a__, c__, d__, e__, f__],
        when: {
            freeq!([a__, c__, d__, e__, f__], x_)
                && igtq!(p_, 0)
                && ltq!(q_, -1)
                && gtq!(m_, 0)
        },
        rhs: {
            let direct_denominator = Atom::num(2) * &d__ * &f__ * (&q_ + Atom::num(1));
            let recursive_denominator = Atom::num(2) * &d__ * (&q_ + Atom::num(1));
            let fx = &f__ * x_;
            let quadratic = &d__ + &e__ * x_.pow(2);
            let quartic = &a__ + &c__ * x_.pow(4);
            let quartic_power = quartic.pow(&p_).expand();
            let Qx = rubi_polynomial_quotient(&quartic_power, &quadratic, x_).rubi_rhs();
            let polynomial_remainder = rubi_polynomial_remainder(&quartic_power, &quadratic, x_).rubi_rhs();
            let R = rubi_coeff(&polynomial_remainder, x_, 0).rubi_rhs();
            let direct = -&R * fx.pow(&m_ + Atom::num(1)) * quadratic.pow(&q_ + Atom::num(1))
                / &direct_denominator;
            let expand_to_sum = rubi_expand_to_sum(
                &(Atom::num(2) * &d__ * (&q_ + Atom::num(1)) * x_ * Qx
                    + &R * (&m_ + Atom::num(2) * &q_ + Atom::num(3)) * x_),
                x_,
            );
            let recursive_integrand =
                fx.pow(&m_ - Atom::num(1)) * quadratic.pow(&q_ + Atom::num(1)) * expand_to_sum;

            rubi_simp(&(direct), x_)
                    + rubi_star(&f__ / recursive_denominator, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1588(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1588,
        source: "Int[(f_.*x_)^m_*(d_+e_.*x_^2)^q_.*(a_+b_.*x_^2+c_.*x_^4)^p_.,x_Symbol] :=
          With[{Qx=PolynomialQuotient[(a+b*x^2+c*x^4)^p,f*x,x], R=PolynomialRemainder[(a+b*x^2+c*x^4)^p,f*x,x]},
          R*(f*x)^(m+1)*(d+e*x^2)^(q+1)/(d*f*(m+1)) +
          1/(d*f^2*(m+1)) \\[Star] Int[(f*x)^(m+2)*(d+e*x^2)^q*ExpandToSum[d*f*(m+1)*Qx/x-e*R*(m+2*q+3),x],x]] /;
        FreeQ[{a,b,c,d,e,f,q},x] && NeQ[b^2-4*a*c,0] && IGtQ[p,0] && LtQ[m,-1]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, b__, c__, d__, e__, f__, m_, p_, q_, x_],
        optional: [f__, e__, q_, b__, c__, p_],
        x_free: [a__, b__, c__, d__, e__, f__, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, q_], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && igtq!(p_, 0)
                && ltq!(m_, -1)
        },
        rhs: {
            let direct_denominator = &d__ * &f__ * (&m_ + Atom::num(1));
            let recursive_denominator = &d__ * f__.pow(2) * (&m_ + Atom::num(1));
            let fx = &f__ * x_;
            let quadratic = &d__ + &e__ * x_.pow(2);
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let quartic_power = quartic.pow(&p_).expand();
            let Qx = rubi_polynomial_quotient(&quartic_power, &fx, x_).rubi_rhs();
            let R = rubi_polynomial_remainder(&quartic_power, &fx, x_).rubi_rhs();
            let direct =
                &R * fx.pow(&m_ + Atom::num(1)) * quadratic.pow(&q_ + Atom::num(1)) / &direct_denominator;
            let expand_to_sum = rubi_expand_to_sum(
                &(&d__ * &f__ * (&m_ + Atom::num(1)) * Qx / x_
                    - &e__ * &R * (&m_ + Atom::num(2) * &q_ + Atom::num(3))),
                x_,
            );
            let recursive_integrand = fx.pow(&m_ + Atom::num(2)) * quadratic.pow(&q_) * expand_to_sum;

            rubi_simp(&(direct), x_)
                    + rubi_star(Atom::num(1) / recursive_denominator, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1589(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, m_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1589,
        source: "Int[(f_.*x_)^m_*(d_+e_.*x_^2)^q_.*(a_+c_.*x_^4)^p_.,x_Symbol] :=
          With[{Qx=PolynomialQuotient[(a+c*x^4)^p,f*x,x], R=PolynomialRemainder[(a+c*x^4)^p,f*x,x]},
          R*(f*x)^(m+1)*(d+e*x^2)^(q+1)/(d*f*(m+1)) +
          1/(d*f^2*(m+1)) \\[Star] Int[(f*x)^(m+2)*(d+e*x^2)^q*ExpandToSum[d*f*(m+1)*Qx/x-e*R*(m+2*q+3),x],x]] /;
        FreeQ[{a,c,d,e,f,q},x] && IGtQ[p,0] && LtQ[m,-1]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [a__, c__, d__, e__, f__, m_, p_, q_, x_],
        optional: [f__, e__, q_, c__, p_],
        x_free: [a__, c__, d__, e__, f__, q_],
        when: {
            freeq!([a__, c__, d__, e__, f__, q_], x_)
                && igtq!(p_, 0)
                && ltq!(m_, -1)
        },
        rhs: {
            let direct_denominator = &d__ * &f__ * (&m_ + Atom::num(1));
            let recursive_denominator = &d__ * f__.pow(2) * (&m_ + Atom::num(1));
            let fx = &f__ * x_;
            let quadratic = &d__ + &e__ * x_.pow(2);
            let quartic = &a__ + &c__ * x_.pow(4);
            let quartic_power = quartic.pow(&p_).expand();
            let Qx = rubi_polynomial_quotient(&quartic_power, &fx, x_).rubi_rhs();
            let R = rubi_polynomial_remainder(&quartic_power, &fx, x_).rubi_rhs();
            let direct =
                &R * fx.pow(&m_ + Atom::num(1)) * quadratic.pow(&q_ + Atom::num(1)) / &direct_denominator;
            let expand_to_sum = rubi_expand_to_sum(
                &(&d__ * &f__ * (&m_ + Atom::num(1)) * Qx / x_
                    - &e__ * &R * (&m_ + Atom::num(2) * &q_ + Atom::num(3))),
                x_,
            );
            let recursive_integrand = fx.pow(&m_ + Atom::num(2)) * quadratic.pow(&q_) * expand_to_sum;

            rubi_simp(&(direct), x_)
                    + rubi_star(Atom::num(1) / recursive_denominator, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1590(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1590,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^q_.*(a_+b_.*x_^2+c_.*x_^4)^p_.,x_Symbol] :=
          c^p*(f*x)^(m+4*p-1)*(d+e*x^2)^(q+1)/(e*f^(4*p-1)*(m+4*p+2*q+1)) +
          1/(e*(m+4*p+2*q+1)) \\[Star] Int[(f*x)^m*(d+e*x^2)^q*
            ExpandToSum[e*(m+4*p+2*q+1)*((a+b*x^2+c*x^4)^p-c^p*x^(4*p))-d*c^p*(m+4*p-1)*x^(4*p-2),x],x] /;
        FreeQ[{a,b,c,d,e,f,m,q},x] && NeQ[b^2-4*a*c,0] && IGtQ[p,0] && Not[IntegerQ[q]] && NeQ[m+4*p+2*q+1,0]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, b__, c__, d__, e__, f__, m_, p_, q_, x_],
        optional: [f__, m_, e__, q_, b__, c__, p_],
        x_free: [a__, b__, c__, d__, e__, f__, m_, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, q_], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && igtq!(p_, 0)
                && !integerq!(q_)
                && neq!(&m_ + Atom::num(4) * &p_ + Atom::num(2) * &q_ + Atom::num(1), 0)
        },
        rhs: {
            let k = &m_ + Atom::num(4) * &p_ + Atom::num(2) * &q_ + Atom::num(1);
            let direct_denominator = &e__ * f__.pow(Atom::num(4) * &p_ - Atom::num(1)) * &k;
            let recursive_denominator = &e__ * &k;
            let fx = &f__ * x_;
            let quadratic = &d__ + &e__ * x_.pow(2);
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let c_power = c__.pow(&p_);
            let direct = &c_power
                * fx.pow(&m_ + Atom::num(4) * &p_ - Atom::num(1))
                * quadratic.pow(&q_ + Atom::num(1))
                / &direct_denominator;
            let expand_to_sum = rubi_expand_to_sum(
                &(&e__ * &k * (quartic.pow(&p_) - &c_power * x_.pow(Atom::num(4) * &p_))
                    - &d__
                        * &c_power
                        * (&m_ + Atom::num(4) * &p_ - Atom::num(1))
                        * x_.pow(Atom::num(4) * &p_ - Atom::num(2))),
                x_,
            );
            let recursive_integrand = fx.pow(&m_) * quadratic.pow(&q_) * expand_to_sum;

            rubi_simp(&(direct), x_)
                    + rubi_star(Atom::num(1) / recursive_denominator, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1591(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, m_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1591,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^q_.*(a_+c_.*x_^4)^p_.,x_Symbol] :=
          c^p*(f*x)^(m+4*p-1)*(d+e*x^2)^(q+1)/(e*f^(4*p-1)*(m+4*p+2*q+1)) +
          1/(e*(m+4*p+2*q+1)) \\[Star] Int[(f*x)^m*(d+e*x^2)^q*
            ExpandToSum[e*(m+4*p+2*q+1)*((a+c*x^4)^p-c^p*x^(4*p))-d*c^p*(m+4*p-1)*x^(4*p-2),x],x] /;
        FreeQ[{a,c,d,e,f,m,q},x] && IGtQ[p,0] && Not[IntegerQ[q]] && NeQ[m+4*p+2*q+1,0]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [a__, c__, d__, e__, f__, m_, p_, q_, x_],
        optional: [f__, m_, e__, q_, c__, p_],
        x_free: [a__, c__, d__, e__, f__, m_, q_],
        when: {
            freeq!([a__, c__, d__, e__, f__, m_, q_], x_)
                && igtq!(p_, 0)
                && !integerq!(q_)
                && neq!(&m_ + Atom::num(4) * &p_ + Atom::num(2) * &q_ + Atom::num(1), 0)
        },
        rhs: {
            let k = &m_ + Atom::num(4) * &p_ + Atom::num(2) * &q_ + Atom::num(1);
            let direct_denominator = &e__ * f__.pow(Atom::num(4) * &p_ - Atom::num(1)) * &k;
            let recursive_denominator = &e__ * &k;
            let fx = &f__ * x_;
            let quadratic = &d__ + &e__ * x_.pow(2);
            let quartic = &a__ + &c__ * x_.pow(4);
            let c_power = c__.pow(&p_);
            let direct = &c_power
                * fx.pow(&m_ + Atom::num(4) * &p_ - Atom::num(1))
                * quadratic.pow(&q_ + Atom::num(1))
                / &direct_denominator;
            let expand_to_sum = rubi_expand_to_sum(
                &(&e__ * &k * (quartic.pow(&p_) - &c_power * x_.pow(Atom::num(4) * &p_))
                    - &d__
                        * &c_power
                        * (&m_ + Atom::num(4) * &p_ - Atom::num(1))
                        * x_.pow(Atom::num(4) * &p_ - Atom::num(2))),
                x_,
            );
            let recursive_integrand = fx.pow(&m_) * quadratic.pow(&q_) * expand_to_sum;

            rubi_simp(&(direct), x_)
                    + rubi_star(Atom::num(1) / recursive_denominator, rubi_rhs_int(&recursive_integrand, x_))
        },
    ));
}

fn push_rules_rule_1592(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1592,
        source: "Int[(f_.*x_)^m_*(d_+e_.*x_^2)^q_.*(a_+b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
          With[{k=Denominator[m]},
          k/f \\[Star] Subst[Int[x^(k*(m+1)-1)*(d+e*x^(2*k)/f^2)^q*(a+b*x^(2*k)/f^k+c*x^(4*k)/f^4)^p,x],x,(f*x)^(1/k)]] /;
        FreeQ[{a,b,c,d,e,f,p,q},x] && NeQ[b^2-4*a*c,0] && FractionQ[m] && IntegerQ[p]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, b__, c__, d__, e__, f__, m_, p_, q_, x_],
        optional: [f__, e__, q_, b__, c__],
        x_free: [a__, b__, c__, d__, e__, f__, p_, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, p_, q_], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && fractionq!(m_)
                && integerq!(p_)
        },
        rhs: {
            let k_i = rubi_denominator(&m_).rubi_rhs();
            let k = Atom::num(k_i);
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = sub_atom.pow((&k * (&m_ + Atom::num(1))).expand() - Atom::num(1))
                * (&d__ + &e__ * sub_atom.pow(Atom::num(2) * &k) / f__.pow(2)).pow(&q_)
                * (&a__
                    + &b__ * sub_atom.pow(Atom::num(2) * &k) / f__.pow(&k)
                    + &c__ * sub_atom.pow(Atom::num(4) * &k) / f__.pow(4))
                .pow(&p_);
            let substituted = rubi_subst(
                &rubi_rhs_int(&transformed_integrand, sub),
                sub,
                (&f__ * x_).pow(Atom::num(1) / Atom::num(k_i)),
            );
            rubi_star(&k / &f__, substituted)
        },
    ));
}

fn push_rules_rule_1593(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, m_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1593,
        source: "Int[(f_.*x_)^m_*(d_+e_.*x_^2)^q_.*(a_+c_.*x_^4)^p_,x_Symbol] :=
          With[{k=Denominator[m]},
          k/f \\[Star] Subst[Int[x^(k*(m+1)-1)*(d+e*x^(2*k)/f)^q*(a+c*x^(4*k)/f)^p,x],x,(f*x)^(1/k)]] /;
        FreeQ[{a,c,d,e,f,p,q},x] && FractionQ[m] && IntegerQ[p]",
        desc: "Integration by substitution",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [a__, c__, d__, e__, f__, m_, p_, q_, x_],
        optional: [f__, e__, q_, c__],
        x_free: [a__, c__, d__, e__, f__, p_, q_],
        when: {
            freeq!([a__, c__, d__, e__, f__, p_, q_], x_)
                && fractionq!(m_)
                && integerq!(p_)
        },
        rhs: {
            let k_i = rubi_denominator(&m_).rubi_rhs();
            let k = Atom::num(k_i);
            let sub_guard = fresh_substitution_symbol().unwrap();
            let sub = sub_guard.symbol();
            let sub_atom = Atom::var(sub);
            let transformed_integrand = sub_atom.pow((&k * (&m_ + Atom::num(1))).expand() - Atom::num(1))
                * (&d__ + &e__ * sub_atom.pow(Atom::num(2) * &k) / &f__).pow(&q_)
                * (&a__ + &c__ * sub_atom.pow(Atom::num(4) * &k) / &f__).pow(&p_);
            let substituted = rubi_subst(
                &rubi_rhs_int(&transformed_integrand, sub),
                sub,
                (&f__ * x_).pow(Atom::num(1) / Atom::num(k_i)),
            );
            rubi_star(&k / &f__, substituted)
        },
    ));
}

fn push_rules_rule_1594(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1594,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^2)*(a_+b_.*x_^2+c_.*x_^4)^p_.,x_Symbol] :=
          (f*x)^(m+1)*(a+b*x^2+c*x^4)^p*(d*(m+4*p+3)+e*(m+1)*x^2)/(f*(m+1)*(m+4*p+3)) +
          2*p/(f^2*(m+1)*(m+4*p+3)) \\[Star] Int[(f*x)^(m+2)*(a+b*x^2+c*x^4)^(p-1)*
            Simp[2*a*e*(m+1)-b*d*(m+4*p+3)+(b*e*(m+1)-2*c*d*(m+4*p+3))*x^2,x],x] /;
        FreeQ[{a,b,c,d,e,f},x] && NeQ[b^2-4*a*c,0] && GtQ[p,0] && LtQ[m,-1] && m+4*p+3!=0 && IntegerQ[2*p] && (IntegerQ[p] || IntegerQ[m])",
        desc: "Trinomial recurrence 1a",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, e__, f__, m_, p_, x_],
        optional: [f__, m_, e__, b__, c__, p_],
        x_free: [a__, b__, c__, d__, e__, f__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && gtq!(p_, 0)
                && ltq!(m_, -1)
                && &m_ + Atom::num(4) * &p_ + Atom::num(3) != Atom::num(0)
                && integerq!(Atom::num(2) * &p_)
                && (integerq!(p_) || integerq!(m_))
        },
        rhs: {
            let k = &m_ + Atom::num(4) * &p_ + Atom::num(3);
            let direct_denominator = &f__ * (&m_ + Atom::num(1)) * &k;
            let recursive_denominator = f__.pow(2) * (&m_ + Atom::num(1)) * &k;
            let fx = &f__ * x_;
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let direct = fx.pow(&m_ + Atom::num(1))
                * quartic.pow(&p_)
                * (&d__ * &k + &e__ * (&m_ + Atom::num(1)) * x_.pow(2))
                / &direct_denominator;
            let simp = rubi_simp(
                &(Atom::num(2) * &a__ * &e__ * (&m_ + Atom::num(1)) - &b__ * &d__ * &k
                    + (&b__ * &e__ * (&m_ + Atom::num(1)) - Atom::num(2) * &c__ * &d__ * &k)
                        * x_.pow(2)),
                x_,
            );
            let recursive_integrand = fx.pow(&m_ + Atom::num(2)) * quartic.pow(&p_ - Atom::num(1)) * simp;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) + rubi_star(Atom::num(2) * &p_ / recursive_denominator, recursive)
        },
    ));
}

fn push_rules_rule_1595(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1595,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^2)*(a_+c_.*x_^4)^p_.,x_Symbol] :=
          (f*x)^(m+1)*(a+c*x^4)^p*(d*(m+4*p+3)+e*(m+1)*x^2)/(f*(m+1)*(m+4*p+3)) +
          4*p/(f^2*(m+1)*(m+4*p+3)) \\[Star] Int[(f*x)^(m+2)*(a+c*x^4)^(p-1)*(a*e*(m+1)-c*d*(m+4*p+3)*x^2),x] /;
        FreeQ[{a,c,d,e,f},x] && GtQ[p,0] && LtQ[m,-1] && m+4*p+3!=0 && IntegerQ[2*p] && (IntegerQ[p] || IntegerQ[m])",
        desc: "Trinomial recurrence 1a",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, c__, d__, e__, f__, m_, p_, x_],
        optional: [f__, m_, e__, c__, p_],
        x_free: [a__, c__, d__, e__, f__],
        when: {
            freeq!([a__, c__, d__, e__, f__], x_)
                && gtq!(p_, 0)
                && ltq!(m_, -1)
                && &m_ + Atom::num(4) * &p_ + Atom::num(3) != Atom::num(0)
                && integerq!(Atom::num(2) * &p_)
                && (integerq!(p_) || integerq!(m_))
        },
        rhs: {
            let k = &m_ + Atom::num(4) * &p_ + Atom::num(3);
            let direct_denominator = &f__ * (&m_ + Atom::num(1)) * &k;
            let recursive_denominator = f__.pow(2) * (&m_ + Atom::num(1)) * &k;
            let fx = &f__ * x_;
            let quartic = &a__ + &c__ * x_.pow(4);
            let direct = fx.pow(&m_ + Atom::num(1))
                * quartic.pow(&p_)
                * (&d__ * &k + &e__ * (&m_ + Atom::num(1)) * x_.pow(2))
                / &direct_denominator;
            let recursive_integrand = fx.pow(&m_ + Atom::num(2))
                * quartic.pow(&p_ - Atom::num(1))
                * (&a__ * &e__ * (&m_ + Atom::num(1)) - &c__ * &d__ * &k * x_.pow(2));
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) + rubi_star(Atom::num(4) * &p_ / recursive_denominator, recursive)
        },
    ));
}

fn push_rules_rule_1596(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1596,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^2)*(a_+b_.*x_^2+c_.*x_^4)^p_.,x_Symbol] :=
          (f*x)^(m+1)*(a+b*x^2+c*x^4)^p*(b*e*2*p+c*d*(m+4*p+3)+c*e*(4*p+m+1)*x^2)/
            (c*f*(4*p+m+1)*(m+4*p+3)) +
          2*p/(c*(4*p+m+1)*(m+4*p+3)) \\[Star] Int[(f*x)^m*(a+b*x^2+c*x^4)^(p-1)*
            Simp[2*a*c*d*(m+4*p+3)-a*b*e*(m+1)+(2*a*c*e*(4*p+m+1)+b*c*d*(m+4*p+3)-b^2*e*(m+2*p+1))*x^2,x],x] /;
        FreeQ[{a,b,c,d,e,f,m},x] && NeQ[b^2-4*a*c,0] && GtQ[p,0] && NeQ[4*p+m+1,0] && NeQ[m+4*p+3,0] && IntegerQ[2*p] && (IntegerQ[p] || IntegerQ[m])",
        desc: "Trinomial recurrence 1b",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, e__, f__, m_, p_, x_],
        optional: [f__, m_, e__, b__, c__, p_],
        x_free: [a__, b__, c__, d__, e__, f__, m_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && gtq!(p_, 0)
                && neq!(Atom::num(4) * &p_ + &m_ + Atom::num(1), 0)
                && neq!(&m_ + Atom::num(4) * &p_ + Atom::num(3), 0)
                && integerq!(Atom::num(2) * &p_)
                && (integerq!(p_) || integerq!(m_))
        },
        rhs: {
            let k1 = Atom::num(4) * &p_ + &m_ + Atom::num(1);
            let k3 = &m_ + Atom::num(4) * &p_ + Atom::num(3);
            let direct_denominator = &c__ * &f__ * &k1 * &k3;
            let recursive_denominator = &c__ * &k1 * &k3;
            let fx = &f__ * x_;
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let direct = fx.pow(&m_ + Atom::num(1))
                * quartic.pow(&p_)
                * (&b__ * &e__ * Atom::num(2) * &p_ + &c__ * &d__ * &k3 + &c__ * &e__ * &k1 * x_.pow(2))
                / &direct_denominator;
            let simp = rubi_simp(
                &(Atom::num(2) * &a__ * &c__ * &d__ * &k3 - &a__ * &b__ * &e__ * (&m_ + Atom::num(1))
                    + (Atom::num(2) * &a__ * &c__ * &e__ * &k1
                        + &b__ * &c__ * &d__ * &k3
                        - b__.pow(2) * &e__ * (&m_ + Atom::num(2) * &p_ + Atom::num(1)))
                        * x_.pow(2)),
                x_,
            );
            let recursive_integrand = fx.pow(&m_) * quartic.pow(&p_ - Atom::num(1)) * simp;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) + rubi_star(Atom::num(2) * &p_ / recursive_denominator, recursive)
        },
    ));
}

fn push_rules_rule_1597(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1597,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^2)*(a_+c_.*x_^4)^p_.,x_Symbol] :=
          (f*x)^(m+1)*(a+c*x^4)^p*(c*d*(m+4*p+3)+c*e*(4*p+m+1)*x^2)/(c*f*(4*p+m+1)*(m+4*p+3)) +
          4*a*p/((4*p+m+1)*(m+4*p+3)) \\[Star] Int[(f*x)^m*(a+c*x^4)^(p-1)*Simp[d*(m+4*p+3)+e*(4*p+m+1)*x^2,x],x] /;
        FreeQ[{a,c,d,e,f,m},x] && GtQ[p,0] && NeQ[4*p+m+1,0] && NeQ[m+4*p+3,0] && IntegerQ[2*p] && (IntegerQ[p] || IntegerQ[m])",
        desc: "Trinomial recurrence 1b",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, c__, d__, e__, f__, m_, p_, x_],
        optional: [f__, m_, e__, c__, p_],
        x_free: [a__, c__, d__, e__, f__, m_],
        when: {
            freeq!([a__, c__, d__, e__, f__, m_], x_)
                && gtq!(p_, 0)
                && neq!(Atom::num(4) * &p_ + &m_ + Atom::num(1), 0)
                && neq!(&m_ + Atom::num(4) * &p_ + Atom::num(3), 0)
                && integerq!(Atom::num(2) * &p_)
                && (integerq!(p_) || integerq!(m_))
        },
        rhs: {
            let k1 = Atom::num(4) * &p_ + &m_ + Atom::num(1);
            let k3 = &m_ + Atom::num(4) * &p_ + Atom::num(3);
            let direct_denominator = &c__ * &f__ * &k1 * &k3;
            let recursive_denominator = &k1 * &k3;
            let fx = &f__ * x_;
            let quartic = &a__ + &c__ * x_.pow(4);
            let direct = fx.pow(&m_ + Atom::num(1))
                * quartic.pow(&p_)
                * (&c__ * &d__ * &k3 + &c__ * &e__ * &k1 * x_.pow(2))
                / &direct_denominator;
            let simp = rubi_simp(&(&d__ * &k3 + &e__ * &k1 * x_.pow(2)), x_);
            let recursive_integrand = fx.pow(&m_) * quartic.pow(&p_ - Atom::num(1)) * simp;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) + rubi_star(Atom::num(4) * &a__ * &p_ / recursive_denominator, recursive)
        },
    ));
}

fn push_rules_rule_1598(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1598,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^2)*(a_+b_.*x_^2+c_.*x_^4)^p_.,x_Symbol] :=
          f*(f*x)^(m-1)*(a+b*x^2+c*x^4)^(p+1)*(b*d-2*a*e-(b*e-2*c*d)*x^2)/(2*(p+1)*(b^2-4*a*c)) -
          f^2/(2*(p+1)*(b^2-4*a*c)) \\[Star] Int[(f*x)^(m-2)*(a+b*x^2+c*x^4)^(p+1)*
            Simp[(m-1)*(b*d-2*a*e)-(4*p+4+m+1)*(b*e-2*c*d)*x^2,x],x] /;
        FreeQ[{a,b,c,d,e,f},x] && NeQ[b^2-4*a*c,0] && LtQ[p,-1] && GtQ[m,1] && IntegerQ[2*p] && (IntegerQ[p] || IntegerQ[m])",
        desc: "Trinomial recurrence 2a",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, e__, f__, m_, p_, x_],
        optional: [f__, m_, e__, b__, c__, p_],
        x_free: [a__, b__, c__, d__, e__, f__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && ltq!(p_, -1)
                && gtq!(m_, 1)
                && integerq!(Atom::num(2) * &p_)
                && (integerq!(p_) || integerq!(m_))
        },
        rhs: {
            let discriminant = b__.pow(2) - Atom::num(4) * &a__ * &c__;
            let denominator = Atom::num(2) * (&p_ + Atom::num(1)) * &discriminant;
            let fx = &f__ * x_;
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let direct = &f__
                * fx.pow(&m_ - Atom::num(1))
                * quartic.pow(&p_ + Atom::num(1))
                * (&b__ * &d__ - Atom::num(2) * &a__ * &e__
                    - (&b__ * &e__ - Atom::num(2) * &c__ * &d__) * x_.pow(2))
                / &denominator;
            let simp = rubi_simp(
                &((&m_ - Atom::num(1)) * (&b__ * &d__ - Atom::num(2) * &a__ * &e__)
                    - (Atom::num(4) * &p_ + Atom::num(4) + &m_ + Atom::num(1))
                        * (&b__ * &e__ - Atom::num(2) * &c__ * &d__)
                        * x_.pow(2)),
                x_,
            );
            let recursive_integrand =
                fx.pow(&m_ - Atom::num(2)) * quartic.pow(&p_ + Atom::num(1)) * simp;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) + rubi_star(-f__.pow(2) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_1599(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1599,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^2)*(a_+c_.*x_^4)^p_.,x_Symbol] :=
          f*(f*x)^(m-1)*(a+c*x^4)^(p+1)*(a*e-c*d*x^2)/(4*a*c*(p+1)) -
          f^2/(4*a*c*(p+1)) \\[Star] Int[(f*x)^(m-2)*(a+c*x^4)^(p+1)*(a*e*(m-1)-c*d*(4*p+4+m+1)*x^2),x] /;
        FreeQ[{a,c,d,e,f},x] && LtQ[p,-1] && GtQ[m,1] && IntegerQ[2*p] && (IntegerQ[p] || IntegerQ[m])",
        desc: "Trinomial recurrence 2a",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, c__, d__, e__, f__, m_, p_, x_],
        optional: [f__, m_, e__, c__, p_],
        x_free: [a__, c__, d__, e__, f__],
        when: {
            freeq!([a__, c__, d__, e__, f__], x_)
                && ltq!(p_, -1)
                && gtq!(m_, 1)
                && integerq!(Atom::num(2) * &p_)
                && (integerq!(p_) || integerq!(m_))
        },
        rhs: {
            let denominator = Atom::num(4) * &a__ * &c__ * (&p_ + Atom::num(1));
            let fx = &f__ * x_;
            let quartic = &a__ + &c__ * x_.pow(4);
            let direct = &f__
                * fx.pow(&m_ - Atom::num(1))
                * quartic.pow(&p_ + Atom::num(1))
                * (&a__ * &e__ - &c__ * &d__ * x_.pow(2))
                / &denominator;
            let recursive_integrand = fx.pow(&m_ - Atom::num(2))
                * quartic.pow(&p_ + Atom::num(1))
                * (&a__ * &e__ * (&m_ - Atom::num(1))
                    - &c__
                        * &d__
                        * (Atom::num(4) * &p_ + Atom::num(4) + &m_ + Atom::num(1))
                        * x_.pow(2));
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) + rubi_star(-f__.pow(2) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_1600(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1600,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^2)*(a_+b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
          -(f*x)^(m+1)*(a+b*x^2+c*x^4)^(p+1)*(d*(b^2-2*a*c)-a*b*e+(b*d-2*a*e)*c*x^2)/(2*a*f*(p+1)*(b^2-4*a*c)) +
          1/(2*a*(p+1)*(b^2-4*a*c)) \\[Star] Int[(f*x)^m*(a+b*x^2+c*x^4)^(p+1)*
            Simp[d*(b^2*(m+2*(p+1)+1)-2*a*c*(m+4*(p+1)+1))-a*b*e*(m+1)+c*(m+2*(2*p+3)+1)*(b*d-2*a*e)*x^2,x],x] /;
        FreeQ[{a,b,c,d,e,f,m},x] && NeQ[b^2-4*a*c,0] && LtQ[p,-1] && IntegerQ[2*p] && (IntegerQ[p] || IntegerQ[m])",
        desc: "Trinomial recurrence 2b",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, e__, f__, m_, p_, x_],
        optional: [f__, m_, e__, b__, c__],
        x_free: [a__, b__, c__, d__, e__, f__, m_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && ltq!(p_, -1)
                && integerq!(Atom::num(2) * &p_)
                && (integerq!(p_) || integerq!(m_))
        },
        rhs: {
            let discriminant = b__.pow(2) - Atom::num(4) * &a__ * &c__;
            let direct_denominator = Atom::num(2) * &a__ * &f__ * (&p_ + Atom::num(1)) * &discriminant;
            let recursive_denominator = Atom::num(2) * &a__ * (&p_ + Atom::num(1)) * &discriminant;
            let fx = &f__ * x_;
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let direct = -fx.pow(&m_ + Atom::num(1))
                * quartic.pow(&p_ + Atom::num(1))
                * (&d__ * (b__.pow(2) - Atom::num(2) * &a__ * &c__)
                    - &a__ * &b__ * &e__
                    + (&b__ * &d__ - Atom::num(2) * &a__ * &e__) * &c__ * x_.pow(2))
                / &direct_denominator;
            let simp = rubi_simp(
                &(&d__
                    * (b__.pow(2) * (&m_ + Atom::num(2) * (&p_ + Atom::num(1)) + Atom::num(1))
                        - Atom::num(2)
                            * &a__
                            * &c__
                            * (&m_ + Atom::num(4) * (&p_ + Atom::num(1)) + Atom::num(1)))
                    - &a__ * &b__ * &e__ * (&m_ + Atom::num(1))
                    + &c__
                        * (&m_ + Atom::num(2) * (Atom::num(2) * &p_ + Atom::num(3)) + Atom::num(1))
                        * (&b__ * &d__ - Atom::num(2) * &a__ * &e__)
                        * x_.pow(2)),
                x_,
            );
            let recursive_integrand = fx.pow(&m_) * quartic.pow(&p_ + Atom::num(1)) * simp;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / recursive_denominator, recursive)
        },
    ));
}

fn push_rules_rule_1601(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1601,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^2)*(a_+c_.*x_^4)^p_,x_Symbol] :=
          -(f*x)^(m+1)*(a+c*x^4)^(p+1)*(d+e*x^2)/(4*a*f*(p+1)) +
          1/(4*a*(p+1)) \\[Star] Int[(f*x)^m*(a+c*x^4)^(p+1)*Simp[d*(m+4*(p+1)+1)+e*(m+2*(2*p+3)+1)*x^2,x],x] /;
        FreeQ[{a,c,d,e,f,m},x] && LtQ[p,-1] && IntegerQ[2*p] && (IntegerQ[p] || IntegerQ[m])",
        desc: "Trinomial recurrence 2b",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, c__, d__, e__, f__, m_, p_, x_],
        optional: [f__, m_, e__, c__],
        x_free: [a__, c__, d__, e__, f__, m_],
        when: {
            freeq!([a__, c__, d__, e__, f__, m_], x_)
                && ltq!(p_, -1)
                && integerq!(Atom::num(2) * &p_)
                && (integerq!(p_) || integerq!(m_))
        },
        rhs: {
            let direct_denominator = Atom::num(4) * &a__ * &f__ * (&p_ + Atom::num(1));
            let recursive_denominator = Atom::num(4) * &a__ * (&p_ + Atom::num(1));
            let fx = &f__ * x_;
            let quartic = &a__ + &c__ * x_.pow(4);
            let direct = -fx.pow(&m_ + Atom::num(1))
                * quartic.pow(&p_ + Atom::num(1))
                * (&d__ + &e__ * x_.pow(2))
                / &direct_denominator;
            let simp = rubi_simp(
                &(&d__ * (&m_ + Atom::num(4) * (&p_ + Atom::num(1)) + Atom::num(1))
                    + &e__
                        * (&m_ + Atom::num(2) * (Atom::num(2) * &p_ + Atom::num(3)) + Atom::num(1))
                        * x_.pow(2)),
                x_,
            );
            let recursive_integrand = fx.pow(&m_) * quartic.pow(&p_ + Atom::num(1)) * simp;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / recursive_denominator, recursive)
        },
    ));
}

fn push_rules_rule_1602(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1602,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^2)*(a_+b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
          e*f*(f*x)^(m-1)*(a+b*x^2+c*x^4)^(p+1)/(c*(m+4*p+3)) -
          f^2/(c*(m+4*p+3)) \\[Star] Int[(f*x)^(m-2)*(a+b*x^2+c*x^4)^p*Simp[a*e*(m-1)+(b*e*(m+2*p+1)-c*d*(m+4*p+3))*x^2,x],x] /;
        FreeQ[{a,b,c,d,e,f,p},x] && NeQ[b^2-4*a*c,0] && GtQ[m,1] && NeQ[m+4*p+3,0] && IntegerQ[2*p] && (IntegerQ[p] || IntegerQ[m])",
        desc: "Trinomial recurrence 3a",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, e__, f__, m_, p_, x_],
        optional: [f__, m_, e__, b__, c__],
        x_free: [a__, b__, c__, d__, e__, f__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, p_], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && gtq!(m_, 1)
                && neq!(&m_ + Atom::num(4) * &p_ + Atom::num(3), 0)
                && integerq!(Atom::num(2) * &p_)
                && (integerq!(p_) || integerq!(m_))
        },
        rhs: {
            let k = &m_ + Atom::num(4) * &p_ + Atom::num(3);
            let denominator = &c__ * &k;
            let fx = &f__ * x_;
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let direct = &e__ * &f__ * fx.pow(&m_ - Atom::num(1)) * quartic.pow(&p_ + Atom::num(1)) / &denominator;
            let simp = rubi_simp(
                &(&a__ * &e__ * (&m_ - Atom::num(1))
                    + (&b__ * &e__ * (&m_ + Atom::num(2) * &p_ + Atom::num(1)) - &c__ * &d__ * &k)
                        * x_.pow(2)),
                x_,
            );
            let recursive_integrand = fx.pow(&m_ - Atom::num(2)) * quartic.pow(&p_) * simp;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) + rubi_star(-f__.pow(2) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_1603(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1603,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^2)*(a_+c_.*x_^4)^p_,x_Symbol] :=
          e*f*(f*x)^(m-1)*(a+c*x^4)^(p+1)/(c*(m+4*p+3)) -
          f^2/(c*(m+4*p+3)) \\[Star] Int[(f*x)^(m-2)*(a+c*x^4)^p*(a*e*(m-1)-c*d*(m+4*p+3)*x^2),x] /;
        FreeQ[{a,c,d,e,f,p},x] && GtQ[m,1] && NeQ[m+4*p+3,0] && IntegerQ[2*p] && (IntegerQ[p] || IntegerQ[m])",
        desc: "Trinomial recurrence 3a",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, c__, d__, e__, f__, m_, p_, x_],
        optional: [f__, m_, e__, c__],
        x_free: [a__, c__, d__, e__, f__, p_],
        when: {
            freeq!([a__, c__, d__, e__, f__, p_], x_)
                && gtq!(m_, 1)
                && neq!(&m_ + Atom::num(4) * &p_ + Atom::num(3), 0)
                && integerq!(Atom::num(2) * &p_)
                && (integerq!(p_) || integerq!(m_))
        },
        rhs: {
            let k = &m_ + Atom::num(4) * &p_ + Atom::num(3);
            let denominator = &c__ * &k;
            let fx = &f__ * x_;
            let quartic = &a__ + &c__ * x_.pow(4);
            let direct = &e__ * &f__ * fx.pow(&m_ - Atom::num(1)) * quartic.pow(&p_ + Atom::num(1)) / &denominator;
            let recursive_integrand = fx.pow(&m_ - Atom::num(2))
                * quartic.pow(&p_)
                * (&a__ * &e__ * (&m_ - Atom::num(1)) - &c__ * &d__ * &k * x_.pow(2));
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) + rubi_star(-f__.pow(2) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_1604(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1604,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^2)*(a_+b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
          d*(f*x)^(m+1)*(a+b*x^2+c*x^4)^(p+1)/(a*f*(m+1)) +
          1/(a*f^2*(m+1)) \\[Star] Int[(f*x)^(m+2)*(a+b*x^2+c*x^4)^p*Simp[a*e*(m+1)-b*d*(m+2*p+3)-c*d*(m+4*p+5)*x^2,x],x] /;
        FreeQ[{a,b,c,d,e,f,p},x] && NeQ[b^2-4*a*c,0] && LtQ[m,-1] && IntegerQ[2*p] && (IntegerQ[p] || IntegerQ[m])",
        desc: "Trinomial recurrence 3b",
        refs: [],
        pattern:  rubi_shared_pattern_2(symbols),
        with: [a__, b__, c__, d__, e__, f__, m_, p_, x_],
        optional: [f__, m_, e__, b__, c__],
        x_free: [a__, b__, c__, d__, e__, f__, p_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, p_], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && ltq!(m_, -1)
                && integerq!(Atom::num(2) * &p_)
                && (integerq!(p_) || integerq!(m_))
        },
        rhs: {
            let direct_denominator = &a__ * &f__ * (&m_ + Atom::num(1));
            let recursive_denominator = &a__ * f__.pow(2) * (&m_ + Atom::num(1));
            let fx = &f__ * x_;
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let direct =
                &d__ * fx.pow(&m_ + Atom::num(1)) * quartic.pow(&p_ + Atom::num(1)) / &direct_denominator;
            let simp = rubi_simp(
                &(&a__ * &e__ * (&m_ + Atom::num(1))
                    - &b__ * &d__ * (&m_ + Atom::num(2) * &p_ + Atom::num(3))
                    - &c__ * &d__ * (&m_ + Atom::num(4) * &p_ + Atom::num(5)) * x_.pow(2)),
                x_,
            );
            let recursive_integrand = fx.pow(&m_ + Atom::num(2)) * quartic.pow(&p_) * simp;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / recursive_denominator, recursive)
        },
    ));
}

fn push_rules_rule_1605(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1605,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^2)*(a_+c_.*x_^4)^p_,x_Symbol] :=
          d*(f*x)^(m+1)*(a+c*x^4)^(p+1)/(a*f*(m+1)) +
          1/(a*f^2*(m+1)) \\[Star] Int[(f*x)^(m+2)*(a+c*x^4)^p*(a*e*(m+1)-c*d*(m+4*p+5)*x^2),x] /;
        FreeQ[{a,c,d,e,f,p},x] && LtQ[m,-1] && IntegerQ[2*p] && (IntegerQ[p] || IntegerQ[m])",
        desc: "Trinomial recurrence 3b",
        refs: [],
        pattern:  rubi_shared_pattern_3(symbols),
        with: [a__, c__, d__, e__, f__, m_, p_, x_],
        optional: [f__, m_, e__, c__],
        x_free: [a__, c__, d__, e__, f__, p_],
        when: {
            freeq!([a__, c__, d__, e__, f__, p_], x_)
                && ltq!(m_, -1)
                && integerq!(Atom::num(2) * &p_)
                && (integerq!(p_) || integerq!(m_))
        },
        rhs: {
            let direct_denominator = &a__ * &f__ * (&m_ + Atom::num(1));
            let recursive_denominator = &a__ * f__.pow(2) * (&m_ + Atom::num(1));
            let fx = &f__ * x_;
            let quartic = &a__ + &c__ * x_.pow(4);
            let direct =
                &d__ * fx.pow(&m_ + Atom::num(1)) * quartic.pow(&p_ + Atom::num(1)) / &direct_denominator;
            let recursive_integrand = fx.pow(&m_ + Atom::num(2))
                * quartic.pow(&p_)
                * (&a__ * &e__ * (&m_ + Atom::num(1))
                    - &c__ * &d__ * (&m_ + Atom::num(4) * &p_ + Atom::num(5)) * x_.pow(2));
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) + rubi_star(Atom::num(1) / recursive_denominator, recursive)
        },
    ));
}

fn push_rules_rule_1606(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, x_);
    rules.push(rubi_rule!(
        order: 1606,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^2)/(a_+b_.*x_^2+c_.*x_^4), x_Symbol] :=
          With[{r=Rt[c/e*(2*c*d-b*e),2]},
          e/2 \\[Star] Int[(f*x)^m/(c*d/e-r*x+c*x^2),x] +
          e/2 \\[Star] Int[(f*x)^m/(c*d/e+r*x+c*x^2),x]] /;
        FreeQ[{a,b,c,d,e,f,m},x] && NeQ[b^2-4*a*c,0] && EqQ[c*d^2-a*e^2,0] && GtQ[d/e,0] && PosQ[c/e*(2*c*d-b*e)]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [a__, b__, c__, d__, e__, f__, m_, x_],
        optional: [f__, m_, e__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && eqq!(&c__ * d__.pow(2) - &a__ * e__.pow(2), 0)
                && gtq!(&d__ / &e__, 0)
                && posq!(&c__ / &e__ * (Atom::num(2) * &c__ * &d__ - &b__ * &e__))
        },
        rhs: {
            if e__.expand().is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let fx = &f__ * x_;
            let r = rubi_rt(&(&c__ / &e__ * (Atom::num(2) * &c__ * &d__ - &b__ * &e__)), 2);
            let constant = &c__ * &d__ / &e__;
            let first_integrand = fx.pow(&m_) / (&constant - &r * x_ + &c__ * x_.pow(2));
            let second_integrand = fx.pow(&m_) / (&constant + &r * x_ + &c__ * x_.pow(2));
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(&e__, first / Atom::num(2)) + rubi_star(e__, second / Atom::num(2))
        },
    ));
}

fn push_rules_rule_1607(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, m_, x_);
    rules.push(rubi_rule!(
        order: 1607,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^2)/(a_+c_.*x_^4), x_Symbol] :=
          With[{r=Rt[2*c^2*d/e,2]},
          e/2 \\[Star] Int[(f*x)^m/(c*d/e-r*x+c*x^2),x] +
          e/2 \\[Star] Int[(f*x)^m/(c*d/e+r*x+c*x^2),x]] /;
        FreeQ[{a,c,d,e,f,m},x] && EqQ[c*d^2-a*e^2,0] && GtQ[d/e,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [a__, c__, d__, e__, f__, m_, x_],
        optional: [f__, m_, e__, c__],
        when: {
            freeq!([a__, c__, d__, e__, f__, m_], x_)
                && eqq!(&c__ * d__.pow(2) - &a__ * e__.pow(2), 0)
                && gtq!(&d__ / &e__, 0)
        },
        rhs: {
            if e__.expand().is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let fx = &f__ * x_;
            let r = rubi_rt(&(Atom::num(2) * c__.pow(2) * &d__ / &e__), 2);
            let constant = &c__ * &d__ / &e__;
            let first_integrand = fx.pow(&m_) / (&constant - &r * x_ + &c__ * x_.pow(2));
            let second_integrand = fx.pow(&m_) / (&constant + &r * x_ + &c__ * x_.pow(2));
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(&e__, first / Atom::num(2)) + rubi_star(e__, second / Atom::num(2))
        },
    ));
}

fn push_rules_rule_1608(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, x_);
    rules.push(rubi_rule!(
        order: 1608,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^2)/(a_+b_.*x_^2+c_.*x_^4),x_Symbol] :=
          With[{q=Rt[b^2-4*a*c,2]},
          (e/2+(2*c*d-b*e)/(2*q)) \\[Star] Int[(f*x)^m/(b/2-q/2+c*x^2),x] + (e/2-(2*c*d-b*e)/(2*q)) \\[Star] Int[(f*x)^m/(b/2+q/2+c*x^2),x]] /;
        FreeQ[{a,b,c,d,e,f,m},x] && NeQ[b^2-4*a*c,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_8(symbols),
        with: [a__, b__, c__, d__, e__, f__, m_, x_],
        optional: [f__, m_, e__, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
        },
        rhs: {
            let fx = &f__ * x_;
            let q = rubi_rt(&(b__.pow(2) - Atom::num(4) * &a__ * &c__), 2);
            let two_q = Atom::num(2) * &q;
            if two_q.expand().is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let split_numerator = Atom::num(2) * &c__ * &d__ - &b__ * &e__;
            let first_coefficient = &e__ / Atom::num(2) + &split_numerator / &two_q;
            let second_coefficient = &e__ / Atom::num(2) - &split_numerator / &two_q;
            let first_integrand =
                fx.pow(&m_) / (&b__ / Atom::num(2) - &q / Atom::num(2) + &c__ * x_.pow(2));
            let second_integrand =
                fx.pow(&m_) / (&b__ / Atom::num(2) + &q / Atom::num(2) + &c__ * x_.pow(2));
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(first_coefficient, first) + rubi_star(second_coefficient, second)
        },
    ));
}

fn push_rules_rule_1609(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, m_, x_);
    rules.push(rubi_rule!(
        order: 1609,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^2)/(a_+c_.*x_^4),x_Symbol] :=
          With[{q=Rt[-a*c,2]},
          -(e/2+c*d/(2*q)) \\[Star] Int[(f*x)^m/(q-c*x^2),x] + (e/2-c*d/(2*q)) \\[Star] Int[(f*x)^m/(q+c*x^2),x]] /;
        FreeQ[{a,c,d,e,f,m},x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_9(symbols),
        with: [a__, c__, d__, e__, f__, m_, x_],
        optional: [f__, m_, e__, c__],
        when: { freeq!([a__, c__, d__, e__, f__, m_], x_) },
        rhs: {
            let fx = &f__ * x_;
            let q = rubi_rt(&(-&a__ * &c__), 2);
            let two_q = Atom::num(2) * &q;
            if two_q.expand().is_zero() {
                panic!("Rubi RHS invariant was not established by the rule condition");
            }

            let first_coefficient = -(&e__ / Atom::num(2) + &c__ * &d__ / &two_q);
            let second_coefficient = &e__ / Atom::num(2) - &c__ * &d__ / &two_q;
            let first_integrand = fx.pow(&m_) / (&q - &c__ * x_.pow(2));
            let second_integrand = fx.pow(&m_) / (&q + &c__ * x_.pow(2));
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(first_coefficient, first) + rubi_star(second_coefficient, second)
        },
    ));
}

fn push_rules_rule_1610(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, q_, x_);
    rules.push(rubi_rule!(
        order: 1610,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^q_./(a_+b_.*x_^2+c_.*x_^4),x_Symbol] :=
          Int[ExpandIntegrand[(f*x)^m*(d+e*x^2)^q/(a+b*x^2+c*x^4),x],x] /;
        FreeQ[{a,b,c,d,e,f,m},x] && NeQ[b^2-4*a*c,0] && IntegerQ[q] && IntegerQ[m]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [a__, b__, c__, d__, e__, f__, m_, q_, x_],
        optional: [f__, m_, e__, q_, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && integerq!(q_)
                && integerq!(m_)
        },
        rhs: {
            let integrand = (&f__ * x_).pow(&m_)
                * (&d__ + &e__ * x_.pow(2)).pow(&q_)
                / (&a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4));
            let expanded = rubi_expand_integrand(&integrand, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_1611(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, m_, q_, x_);
    rules.push(rubi_rule!(
        order: 1611,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^q_./(a_+c_.*x_^4),x_Symbol] :=
          Int[ExpandIntegrand[(f*x)^m*(d+e*x^2)^q/(a+c*x^4),x],x] /;
        FreeQ[{a,c,d,e,f,m},x] && IntegerQ[q] && IntegerQ[m]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [a__, c__, d__, e__, f__, m_, q_, x_],
        optional: [f__, m_, e__, q_, c__],
        when: { freeq!([a__, c__, d__, e__, f__, m_], x_) && integerq!(q_) && integerq!(m_) },
        rhs: {
            let integrand =
                (&f__ * x_).pow(&m_) * (&d__ + &e__ * x_.pow(2)).pow(&q_) / (&a__ + &c__ * x_.pow(4));
            let expanded = rubi_expand_integrand(&integrand, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_1612(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, q_, x_);
    rules.push(rubi_rule!(
        order: 1612,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^q_./(a_+b_.*x_^2+c_.*x_^4),x_Symbol] :=
          Int[ExpandIntegrand[(f*x)^m,(d+e*x^2)^q/(a+b*x^2+c*x^4),x],x] /;
        FreeQ[{a,b,c,d,e,f,m},x] && NeQ[b^2-4*a*c,0] && IntegerQ[q] && Not[IntegerQ[m]]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [a__, b__, c__, d__, e__, f__, m_, q_, x_],
        optional: [f__, m_, e__, q_, b__, c__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && integerq!(q_)
                && !integerq!(m_)
        },
        rhs: {
            let u = (&f__ * x_).pow(&m_);
            let expanded_factor = (&d__ + &e__ * x_.pow(2)).pow(&q_)
                / (&a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4));
            let expanded = rubi_expand_integrand_product(&u, &expanded_factor, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_1613(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, m_, q_, x_);
    rules.push(rubi_rule!(
        order: 1613,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^q_./(a_+c_.*x_^4),x_Symbol] :=
          Int[ExpandIntegrand[(f*x)^m,(d+e*x^2)^q/(a+c*x^4),x],x] /;
        FreeQ[{a,c,d,e,f,m},x] && IntegerQ[q] && Not[IntegerQ[m]]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [a__, c__, d__, e__, f__, m_, q_, x_],
        optional: [f__, m_, e__, q_, c__],
        when: { freeq!([a__, c__, d__, e__, f__, m_], x_) && integerq!(q_) && !integerq!(m_) },
        rhs: {
            let u = (&f__ * x_).pow(&m_);
            let expanded_factor =
                (&d__ + &e__ * x_.pow(2)).pow(&q_) / (&a__ + &c__ * x_.pow(4));
            let expanded = rubi_expand_integrand_product(&u, &expanded_factor, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_1614(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, q_, x_);
    rules.push(rubi_rule!(
        order: 1614,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^q_/(a_+b_.*x_^2+c_.*x_^4),x_Symbol] :=
          f^4/c^2 \\[Star] Int[(f*x)^(m-4)*(c*d-b*e+c*e*x^2)*(d+e*x^2)^(q-1),x] -
          f^4/c^2 \\[Star] Int[(f*x)^(m-4)*(d+e*x^2)^(q-1)*Simp[a*(c*d-b*e)+(b*c*d-b^2*e+a*c*e)*x^2,x]/(a+b*x^2+c*x^4),x] /;
        FreeQ[{a,b,c,d,e,f},x] && NeQ[b^2-4*a*c,0] && Not[IntegerQ[q]] && GtQ[q,0] && GtQ[m,3]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [a__, b__, c__, d__, e__, f__, m_, q_, x_],
        optional: [f__, m_, e__, b__, c__],
        x_free: [a__, b__, c__, d__, e__, f__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && !integerq!(q_)
                && gtq!(q_, 0)
                && gtq!(m_, 3)
        },
        rhs: {
            let coefficient_denominator = c__.pow(2);
            let fx = &f__ * x_;
            let quadratic = &d__ + &e__ * x_.pow(2);
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let coefficient = f__.pow(4) / &coefficient_denominator;
            let first_integrand = fx.pow(&m_ - Atom::num(4))
                * (&c__ * &d__ - &b__ * &e__ + &c__ * &e__ * x_.pow(2))
                * quadratic.pow(&q_ - Atom::num(1));
            let first = rubi_rhs_int(&first_integrand, x_);
            let simp = rubi_simp(
                &(&a__ * (&c__ * &d__ - &b__ * &e__)
                    + (&b__ * &c__ * &d__ - b__.pow(2) * &e__ + &a__ * &c__ * &e__) * x_.pow(2)),
                x_,
            );
            let second_integrand =
                fx.pow(&m_ - Atom::num(4)) * quadratic.pow(&q_ - Atom::num(1)) * simp / quartic;
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(&coefficient, first) + rubi_star(-coefficient, second)
        },
    ));
}

fn push_rules_rule_1615(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, m_, q_, x_);
    rules.push(rubi_rule!(
        order: 1615,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^q_/(a_+c_.*x_^4),x_Symbol] :=
          f^4/c \\[Star] Int[(f*x)^(m-4)*(d+e*x^2)^q,x] -
          a*f^4/c \\[Star] Int[(f*x)^(m-4)*(d+e*x^2)^q/(a+c*x^4),x] /;
        FreeQ[{a,c,d,e,f,q},x] && Not[IntegerQ[q]] && GtQ[m,3]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [a__, c__, d__, e__, f__, m_, q_, x_],
        optional: [f__, m_, e__, c__],
        x_free: [a__, c__, d__, e__, f__, q_],
        when: { freeq!([a__, c__, d__, e__, f__, q_], x_) && !integerq!(q_) && gtq!(m_, 3) },
        rhs: {
            let fx = &f__ * x_;
            let quadratic = &d__ + &e__ * x_.pow(2);
            let first_integrand = fx.pow(&m_ - Atom::num(4)) * quadratic.pow(&q_);
            let second_integrand =
                fx.pow(&m_ - Atom::num(4)) * quadratic.pow(&q_) / (&a__ + &c__ * x_.pow(4));
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(f__.pow(4) / &c__, first)
                    + rubi_star(-&a__ * f__.pow(4) / &c__, second)
        },
    ));
}

fn push_rules_rule_1616(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, q_, x_);
    rules.push(rubi_rule!(
        order: 1616,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^q_/(a_+b_.*x_^2+c_.*x_^4),x_Symbol] :=
          e*f^2/c \\[Star] Int[(f*x)^(m-2)*(d+e*x^2)^(q-1),x] -
          f^2/c \\[Star] Int[(f*x)^(m-2)*(d+e*x^2)^(q-1)*Simp[a*e-(c*d-b*e)*x^2,x]/(a+b*x^2+c*x^4),x] /;
        FreeQ[{a,b,c,d,e,f},x] && NeQ[b^2-4*a*c,0] && Not[IntegerQ[q]] && GtQ[q,0] && GtQ[m,1] && LeQ[m,3]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [a__, b__, c__, d__, e__, f__, m_, q_, x_],
        optional: [f__, m_, e__, b__, c__],
        x_free: [a__, b__, c__, d__, e__, f__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && !integerq!(q_)
                && gtq!(q_, 0)
                && gtq!(m_, 1)
                && leq!(m_, 3)
        },
        rhs: {
            let fx = &f__ * x_;
            let quadratic = &d__ + &e__ * x_.pow(2);
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let first_integrand = fx.pow(&m_ - Atom::num(2)) * quadratic.pow(&q_ - Atom::num(1));
            let first = rubi_rhs_int(&first_integrand, x_);
            let simp = rubi_simp(
                &(&a__ * &e__ - (&c__ * &d__ - &b__ * &e__) * x_.pow(2)),
                x_,
            );
            let second_integrand =
                fx.pow(&m_ - Atom::num(2)) * quadratic.pow(&q_ - Atom::num(1)) * simp / quartic;
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(&e__ * f__.pow(2) / &c__, first)
                    + rubi_star(-f__.pow(2) / &c__, second)
        },
    ));
}

fn push_rules_rule_1617(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, m_, q_, x_);
    rules.push(rubi_rule!(
        order: 1617,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^q_/(a_+c_.*x_^4),x_Symbol] :=
          e*f^2/c \\[Star] Int[(f*x)^(m-2)*(d+e*x^2)^(q-1),x] -
          f^2/c \\[Star] Int[(f*x)^(m-2)*(d+e*x^2)^(q-1)*Simp[a*e-c*d*x^2,x]/(a+c*x^4),x] /;
        FreeQ[{a,c,d,e,f},x] && Not[IntegerQ[q]] && GtQ[q,0] && GtQ[m,1] && LeQ[m,3]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [a__, c__, d__, e__, f__, m_, q_, x_],
        optional: [f__, m_, e__, c__],
        x_free: [a__, c__, d__, e__, f__],
        when: {
            freeq!([a__, c__, d__, e__, f__], x_)
                && !integerq!(q_)
                && gtq!(q_, 0)
                && gtq!(m_, 1)
                && leq!(m_, 3)
        },
        rhs: {
            let fx = &f__ * x_;
            let quadratic = &d__ + &e__ * x_.pow(2);
            let quartic = &a__ + &c__ * x_.pow(4);
            let first_integrand = fx.pow(&m_ - Atom::num(2)) * quadratic.pow(&q_ - Atom::num(1));
            let first = rubi_rhs_int(&first_integrand, x_);
            let simp = rubi_simp(&(&a__ * &e__ - &c__ * &d__ * x_.pow(2)), x_);
            let second_integrand =
                fx.pow(&m_ - Atom::num(2)) * quadratic.pow(&q_ - Atom::num(1)) * simp / quartic;
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(&e__ * f__.pow(2) / &c__, first)
                    + rubi_star(-f__.pow(2) / &c__, second)
        },
    ));
}

fn push_rules_rule_1618(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, q_, x_);
    rules.push(rubi_rule!(
        order: 1618,
        source: "Int[(f_.*x_)^m_*(d_+e_.*x_^2)^q_/(a_+b_.*x_^2+c_.*x_^4),x_Symbol] :=
          d/a \\[Star] Int[(f*x)^m*(d+e*x^2)^(q-1),x] -
          1/(a*f^2) \\[Star] Int[(f*x)^(m+2)*(d+e*x^2)^(q-1)*Simp[b*d-a*e+c*d*x^2,x]/(a+b*x^2+c*x^4),x] /;
        FreeQ[{a,b,c,d,e,f},x] && NeQ[b^2-4*a*c,0] && Not[IntegerQ[q]] && GtQ[q,0] && LtQ[m,0]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [a__, b__, c__, d__, e__, f__, m_, q_, x_],
        optional: [f__, e__, b__, c__],
        x_free: [a__, b__, c__, d__, e__, f__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && !integerq!(q_)
                && gtq!(q_, 0)
                && ltq!(m_, 0)
        },
        rhs: {
            let recursive_denominator = &a__ * f__.pow(2);
            let fx = &f__ * x_;
            let quadratic = &d__ + &e__ * x_.pow(2);
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let first_integrand = fx.pow(&m_) * quadratic.pow(&q_ - Atom::num(1));
            let first = rubi_rhs_int(&first_integrand, x_);
            let simp = rubi_simp(
                &(&b__ * &d__ - &a__ * &e__ + &c__ * &d__ * x_.pow(2)),
                x_,
            );
            let second_integrand =
                fx.pow(&m_ + Atom::num(2)) * quadratic.pow(&q_ - Atom::num(1)) * simp / quartic;
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(&d__ / &a__, first)
                    + rubi_star(-Atom::num(1) / recursive_denominator, second)
        },
    ));
}

fn push_rules_rule_1619(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, m_, q_, x_);
    rules.push(rubi_rule!(
        order: 1619,
        source: "Int[(f_.*x_)^m_*(d_+e_.*x_^2)^q_/(a_+c_.*x_^4),x_Symbol] :=
          d/a \\[Star] Int[(f*x)^m*(d+e*x^2)^(q-1),x] +
          1/(a*f^2) \\[Star] Int[(f*x)^(m+2)*(d+e*x^2)^(q-1)*Simp[a*e-c*d*x^2,x]/(a+c*x^4),x] /;
        FreeQ[{a,c,d,e,f},x] && Not[IntegerQ[q]] && GtQ[q,0] && LtQ[m,0]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [a__, c__, d__, e__, f__, m_, q_, x_],
        optional: [f__, e__, c__],
        x_free: [a__, c__, d__, e__, f__],
        when: {
            freeq!([a__, c__, d__, e__, f__], x_)
                && !integerq!(q_)
                && gtq!(q_, 0)
                && ltq!(m_, 0)
        },
        rhs: {
            let recursive_denominator = &a__ * f__.pow(2);
            let fx = &f__ * x_;
            let quadratic = &d__ + &e__ * x_.pow(2);
            let quartic = &a__ + &c__ * x_.pow(4);
            let first_integrand = fx.pow(&m_) * quadratic.pow(&q_ - Atom::num(1));
            let first = rubi_rhs_int(&first_integrand, x_);
            let simp = rubi_simp(&(&a__ * &e__ - &c__ * &d__ * x_.pow(2)), x_);
            let second_integrand =
                fx.pow(&m_ + Atom::num(2)) * quadratic.pow(&q_ - Atom::num(1)) * simp / quartic;
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(&d__ / &a__, first)
                    + rubi_star(Atom::num(1) / recursive_denominator, second)
        },
    ));
}

fn push_rules_rule_1620(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, q_, x_);
    rules.push(rubi_rule!(
        order: 1620,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^q_/(a_+b_.*x_^2+c_.*x_^4),x_Symbol] :=
          d^2*f^4/(c*d^2-b*d*e+a*e^2) \\[Star] Int[(f*x)^(m-4)*(d+e*x^2)^q,x] -
          f^4/(c*d^2-b*d*e+a*e^2) \\[Star] Int[(f*x)^(m-4)*(d+e*x^2)^(q+1)*Simp[a*d+(b*d-a*e)*x^2,x]/(a+b*x^2+c*x^4),x] /;
        FreeQ[{a,b,c,d,e,f},x] && NeQ[b^2-4*a*c,0] && Not[IntegerQ[q]] && LtQ[q,-1] && GtQ[m,3]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [a__, b__, c__, d__, e__, f__, m_, q_, x_],
        optional: [f__, m_, e__, b__, c__],
        x_free: [a__, b__, c__, d__, e__, f__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && !integerq!(q_)
                && ltq!(q_, -1)
                && gtq!(m_, 3)
        },
        rhs: {
            let denominator = &c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2);
            let fx = &f__ * x_;
            let quadratic = &d__ + &e__ * x_.pow(2);
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let first_integrand = fx.pow(&m_ - Atom::num(4)) * quadratic.pow(&q_);
            let first = rubi_rhs_int(&first_integrand, x_);
            let simp = rubi_simp(
                &(&a__ * &d__ + (&b__ * &d__ - &a__ * &e__) * x_.pow(2)),
                x_,
            );
            let second_integrand =
                fx.pow(&m_ - Atom::num(4)) * quadratic.pow(&q_ + Atom::num(1)) * simp / quartic;
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(d__.pow(2) * f__.pow(4) / &denominator, first)
                    + rubi_star(-f__.pow(4) / denominator, second)
        },
    ));
}

fn push_rules_rule_1621(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, m_, q_, x_);
    rules.push(rubi_rule!(
        order: 1621,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^q_/(a_+c_.*x_^4),x_Symbol] :=
          d^2*f^4/(c*d^2+a*e^2) \\[Star] Int[(f*x)^(m-4)*(d+e*x^2)^q,x] -
          a*f^4/(c*d^2+a*e^2) \\[Star] Int[(f*x)^(m-4)*(d+e*x^2)^(q+1)*(d-e*x^2)/(a+c*x^4),x] /;
        FreeQ[{a,c,d,e,f},x] && Not[IntegerQ[q]] && LtQ[q,-1] && GtQ[m,3]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [a__, c__, d__, e__, f__, m_, q_, x_],
        optional: [f__, m_, e__, c__],
        x_free: [a__, c__, d__, e__, f__],
        when: {
            freeq!([a__, c__, d__, e__, f__], x_)
                && !integerq!(q_)
                && ltq!(q_, -1)
                && gtq!(m_, 3)
        },
        rhs: {
            let denominator = &c__ * d__.pow(2) + &a__ * e__.pow(2);
            let fx = &f__ * x_;
            let quadratic = &d__ + &e__ * x_.pow(2);
            let quartic = &a__ + &c__ * x_.pow(4);
            let first_integrand = fx.pow(&m_ - Atom::num(4)) * quadratic.pow(&q_);
            let second_integrand = fx.pow(&m_ - Atom::num(4))
                * quadratic.pow(&q_ + Atom::num(1))
                * (&d__ - &e__ * x_.pow(2))
                / quartic;
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(d__.pow(2) * f__.pow(4) / &denominator, first)
                    + rubi_star(-&a__ * f__.pow(4) / denominator, second)
        },
    ));
}

fn push_rules_rule_1622(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, q_, x_);
    rules.push(rubi_rule!(
        order: 1622,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^q_/(a_+b_.*x_^2+c_.*x_^4),x_Symbol] :=
          -d*e*f^2/(c*d^2-b*d*e+a*e^2) \\[Star] Int[(f*x)^(m-2)*(d+e*x^2)^q,x] +
          f^2/(c*d^2-b*d*e+a*e^2) \\[Star] Int[(f*x)^(m-2)*(d+e*x^2)^(q+1)*Simp[a*e+c*d*x^2,x]/(a+b*x^2+c*x^4),x] /;
        FreeQ[{a,b,c,d,e,f},x] && NeQ[b^2-4*a*c,0] && Not[IntegerQ[q]] && LtQ[q,-1] && GtQ[m,1] && LeQ[m,3]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [a__, b__, c__, d__, e__, f__, m_, q_, x_],
        optional: [f__, m_, e__, b__, c__],
        x_free: [a__, b__, c__, d__, e__, f__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && !integerq!(q_)
                && ltq!(q_, -1)
                && gtq!(m_, 1)
                && leq!(m_, 3)
        },
        rhs: {
            let denominator = &c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2);
            let fx = &f__ * x_;
            let quadratic = &d__ + &e__ * x_.pow(2);
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let first_integrand = fx.pow(&m_ - Atom::num(2)) * quadratic.pow(&q_);
            let simp = rubi_simp(&(&a__ * &e__ + &c__ * &d__ * x_.pow(2)), x_);
            let second_integrand =
                fx.pow(&m_ - Atom::num(2)) * quadratic.pow(&q_ + Atom::num(1)) * simp / quartic;
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(-&d__ * &e__ * f__.pow(2) / &denominator, first)
                    + rubi_star(f__.pow(2) / denominator, second)
        },
    ));
}

fn push_rules_rule_1623(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, m_, q_, x_);
    rules.push(rubi_rule!(
        order: 1623,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^q_/(a_+c_.*x_^4),x_Symbol] :=
          -d*e*f^2/(c*d^2+a*e^2) \\[Star] Int[(f*x)^(m-2)*(d+e*x^2)^q,x] +
          f^2/(c*d^2+a*e^2) \\[Star] Int[(f*x)^(m-2)*(d+e*x^2)^(q+1)*Simp[a*e+c*d*x^2,x]/(a+c*x^4),x] /;
        FreeQ[{a,c,d,e,f},x] && Not[IntegerQ[q]] && LtQ[q,-1] && GtQ[m,1] && LeQ[m,3]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [a__, c__, d__, e__, f__, m_, q_, x_],
        optional: [f__, m_, e__, c__],
        x_free: [a__, c__, d__, e__, f__],
        when: {
            freeq!([a__, c__, d__, e__, f__], x_)
                && !integerq!(q_)
                && ltq!(q_, -1)
                && gtq!(m_, 1)
                && leq!(m_, 3)
        },
        rhs: {
            let denominator = &c__ * d__.pow(2) + &a__ * e__.pow(2);
            let fx = &f__ * x_;
            let quadratic = &d__ + &e__ * x_.pow(2);
            let quartic = &a__ + &c__ * x_.pow(4);
            let first_integrand = fx.pow(&m_ - Atom::num(2)) * quadratic.pow(&q_);
            let simp = rubi_simp(&(&a__ * &e__ + &c__ * &d__ * x_.pow(2)), x_);
            let second_integrand =
                fx.pow(&m_ - Atom::num(2)) * quadratic.pow(&q_ + Atom::num(1)) * simp / quartic;
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(-&d__ * &e__ * f__.pow(2) / &denominator, first)
                    + rubi_star(f__.pow(2) / denominator, second)
        },
    ));
}

fn push_rules_rule_1624(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, q_, x_);
    rules.push(rubi_rule!(
        order: 1624,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^q_/(a_+b_.*x_^2+c_.*x_^4),x_Symbol] :=
          e^2/(c*d^2-b*d*e+a*e^2) \\[Star] Int[(f*x)^m*(d+e*x^2)^q,x] +
          1/(c*d^2-b*d*e+a*e^2) \\[Star] Int[(f*x)^m*(d+e*x^2)^(q+1)*Simp[c*d-b*e-c*e*x^2,x]/(a+b*x^2+c*x^4),x] /;
        FreeQ[{a,b,c,d,e,f,m},x] && NeQ[b^2-4*a*c,0] && Not[IntegerQ[q]] && LtQ[q,-1]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [a__, b__, c__, d__, e__, f__, m_, q_, x_],
        optional: [f__, m_, e__, b__, c__],
        x_free: [a__, b__, c__, d__, e__, f__, m_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && !integerq!(q_)
                && ltq!(q_, -1)
        },
        rhs: {
            let denominator = &c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2);
            let fx = &f__ * x_;
            let quadratic = &d__ + &e__ * x_.pow(2);
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let first_integrand = fx.pow(&m_) * quadratic.pow(&q_);
            let first = rubi_rhs_int(&first_integrand, x_);
            let simp = rubi_simp(
                &(&c__ * &d__ - &b__ * &e__ - &c__ * &e__ * x_.pow(2)),
                x_,
            );
            let second_integrand =
                fx.pow(&m_) * quadratic.pow(&q_ + Atom::num(1)) * simp / quartic;
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(e__.pow(2) / &denominator, first)
                    + rubi_star(Atom::num(1) / denominator, second)
        },
    ));
}

fn push_rules_rule_1625(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, m_, q_, x_);
    rules.push(rubi_rule!(
        order: 1625,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^q_/(a_+c_.*x_^4),x_Symbol] :=
          e^2/(c*d^2+a*e^2) \\[Star] Int[(f*x)^m*(d+e*x^2)^q,x] +
          c/(c*d^2+a*e^2) \\[Star] Int[(f*x)^m*(d+e*x^2)^(q+1)*(d-e*x^2)/(a+c*x^4),x] /;
        FreeQ[{a,c,d,e,f,m},x] && Not[IntegerQ[q]] && LtQ[q,-1]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [a__, c__, d__, e__, f__, m_, q_, x_],
        optional: [f__, m_, e__, c__],
        x_free: [a__, c__, d__, e__, f__, m_],
        when: {
            freeq!([a__, c__, d__, e__, f__, m_], x_)
                && !integerq!(q_)
                && ltq!(q_, -1)
        },
        rhs: {
            let denominator = &c__ * d__.pow(2) + &a__ * e__.pow(2);
            let fx = &f__ * x_;
            let quadratic = &d__ + &e__ * x_.pow(2);
            let quartic = &a__ + &c__ * x_.pow(4);
            let first_integrand = fx.pow(&m_) * quadratic.pow(&q_);
            let second_integrand =
                fx.pow(&m_) * quadratic.pow(&q_ + Atom::num(1)) * (&d__ - &e__ * x_.pow(2)) / quartic;
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(e__.pow(2) / &denominator, first)
                    + rubi_star(&c__ / denominator, second)
        },
    ));
}

fn push_rules_rule_1626(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, q_, x_);
    rules.push(rubi_rule!(
        order: 1626,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^q_/(a_+b_.*x_^2+c_.*x_^4),x_Symbol] :=
          Int[ExpandIntegrand[(d+e*x^2)^q,(f*x)^m/(a+b*x^2+c*x^4),x],x] /;
        FreeQ[{a,b,c,d,e,f,q},x] && NeQ[b^2-4*a*c,0] && Not[IntegerQ[q]] && IntegerQ[m]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [a__, b__, c__, d__, e__, f__, m_, q_, x_],
        optional: [f__, m_, e__, b__, c__],
        x_free: [a__, b__, c__, d__, e__, f__, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, q_], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && !integerq!(q_)
                && integerq!(m_)
        },
        rhs: {
            let u = (&d__ + &e__ * x_.pow(2)).pow(&q_);
            let expanded_factor =
                (&f__ * x_).pow(&m_) / (&a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4));
            let expanded = rubi_expand_integrand_product(&u, &expanded_factor, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_1627(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, m_, q_, x_);
    rules.push(rubi_rule!(
        order: 1627,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^q_/(a_+c_.*x_^4),x_Symbol] :=
          Int[ExpandIntegrand[(d+e*x^2)^q,(f*x)^m/(a+c*x^4),x],x] /;
        FreeQ[{a,c,d,e,f,q},x] && Not[IntegerQ[q]] && IntegerQ[m]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [a__, c__, d__, e__, f__, m_, q_, x_],
        optional: [f__, m_, e__, c__],
        x_free: [a__, c__, d__, e__, f__, q_],
        when: {
            freeq!([a__, c__, d__, e__, f__, q_], x_)
                && !integerq!(q_)
                && integerq!(m_)
        },
        rhs: {
            let u = (&d__ + &e__ * x_.pow(2)).pow(&q_);
            let expanded_factor = (&f__ * x_).pow(&m_) / (&a__ + &c__ * x_.pow(4));
            let expanded = rubi_expand_integrand_product(&u, &expanded_factor, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_1628(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, q_, x_);
    rules.push(rubi_rule!(
        order: 1628,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^q_/(a_+b_.*x_^2+c_.*x_^4),x_Symbol] :=
          With[{r=Rt[b^2-4*a*c,2]},
          2*c/r \\[Star] Int[(f*x)^m*(d+e*x^2)^q/(b-r+2*c*x^2),x] - 2*c/r \\[Star] Int[(f*x)^m*(d+e*x^2)^q/(b+r+2*c*x^2),x]] /;
        FreeQ[{a,b,c,d,e,f,m,q},x] && NeQ[b^2-4*a*c,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_6(symbols),
        with: [a__, b__, c__, d__, e__, f__, m_, q_, x_],
        optional: [f__, m_, e__, b__, c__],
        x_free: [a__, b__, c__, d__, e__, f__, m_, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, q_], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
        },
        rhs: {
            let r = rubi_rt(&(b__.pow(2) - Atom::num(4) * &a__ * &c__), 2);
            let fx = &f__ * x_;
            let quadratic = &d__ + &e__ * x_.pow(2);
            let first_integrand =
                fx.pow(&m_) * quadratic.pow(&q_) / (&b__ - &r + Atom::num(2) * &c__ * x_.pow(2));
            let second_integrand =
                fx.pow(&m_) * quadratic.pow(&q_) / (&b__ + &r + Atom::num(2) * &c__ * x_.pow(2));
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(Atom::num(2) * &c__ / &r, first)
                    + rubi_star(-Atom::num(2) * &c__ / r, second)
        },
    ));
}

fn push_rules_rule_1629(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, m_, q_, x_);
    rules.push(rubi_rule!(
        order: 1629,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^q_/(a_+c_.*x_^4),x_Symbol] :=
          With[{r=Rt[-a*c,2]},
          -c/(2*r) \\[Star] Int[(f*x)^m*(d+e*x^2)^q/(r-c*x^2),x] - c/(2*r) \\[Star] Int[(f*x)^m*(d+e*x^2)^q/(r+c*x^2),x]] /;
        FreeQ[{a,c,d,e,f,m,q},x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_7(symbols),
        with: [a__, c__, d__, e__, f__, m_, q_, x_],
        optional: [f__, m_, e__, c__],
        x_free: [a__, c__, d__, e__, f__, m_, q_],
        when: { freeq!([a__, c__, d__, e__, f__, m_, q_], x_) },
        rhs: {
            let r = rubi_rt(&(-&a__ * &c__), 2);
            let denominator = Atom::num(2) * &r;
            let fx = &f__ * x_;
            let quadratic = &d__ + &e__ * x_.pow(2);
            let first_integrand = fx.pow(&m_) * quadratic.pow(&q_) / (&r - &c__ * x_.pow(2));
            let second_integrand = fx.pow(&m_) * quadratic.pow(&q_) / (&r + &c__ * x_.pow(2));
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(-&c__ / &denominator, first)
                    + rubi_star(-&c__ / denominator, second)
        },
    ));
}

fn push_rules_rule_1630(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1630,
        source: "Int[x_^m_*(a_.+b_.*x_^2+c_.*x_^4)^p_/(d_+e_.*x_^2),x_Symbol] :=
          -(-d/e)^(m/2)*(c*d^2-b*d*e+a*e^2)^(p+1/2)/(e^(2*p)*(c*d^2-a*e^2)) \\[Star]
            Int[(a*d*Rt[c/a,2]+a*e+(c*d+a*e*Rt[c/a,2])*x^2)/((d+e*x^2)*Sqrt[a+b*x^2+c*x^4]),x] +
          1/(e^(2*p)*(c*d^2-a*e^2)) \\[Star] Int[1/Sqrt[a+b*x^2+c*x^4]*
              ExpandToSum[(e^(2*p)*(c*d^2-a*e^2)*x^m*(a+b*x^2+c*x^4)^(p+1/2) +
                (-d/e)^(m/2)*(c*d^2-b*d*e+a*e^2)^(p+1/2)*(a*d*Rt[c/a,2]+a*e+(c*d+a*e*Rt[c/a,2])*x^2))/(d+e*x^2),x],x] /;
        FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && IGtQ[p+1/2,0] && IGtQ[m/2,0] && NeQ[c*d^2-a*e^2,0] && PosQ[c/a]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_14(symbols),
        with: [m_, a__, b__, c__, p_, d__, e__, x_],
        optional: [a__, b__, c__, e__],
        x_free: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && igtq!(&p_ + Atom::num((1, 2)), 0)
                && igtq!(&m_ / Atom::num(2), 0)
                && neq!(&c__ * d__.pow(2) - &a__ * e__.pow(2), 0)
                && posq!(&c__ / &a__)
        },
        rhs: {
            let half = Atom::num((1, 2));
            let m_half = &m_ / Atom::num(2);
            let p_half = &p_ + &half;
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let quadratic = &d__ + &e__ * x_.pow(2);
            let root = rubi_rt(&(&c__ / &a__), 2);
            let delta = &c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2);
            let k = &c__ * d__.pow(2) - &a__ * e__.pow(2);
            let numerator = &a__ * &d__ * &root
                + &a__ * &e__
                + (&c__ * &d__ + &a__ * &e__ * &root) * x_.pow(2);
            let e_2p = e__.pow(Atom::num(2) * &p_);
            let base_power = (-&d__ / &e__).pow(&m_half);
            let delta_power = delta.pow(&p_half);
            let first_integrand = &numerator / (&quadratic * quartic.sqrt());
            let first = rubi_rhs_int(&first_integrand, x_);
            let expand_payload = (&e_2p
                * &k
                * x_.pow(&m_)
                * quartic.pow(&p_half)
                + &base_power * &delta_power * &numerator)
                / &quadratic;
            let second_integrand = rubi_expand_to_sum(&expand_payload, x_) / quartic.sqrt();
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(-&base_power * &delta_power / (&e_2p * &k), first) + rubi_star(Atom::num(1) / (&e_2p * &k), second)
        },
    ));
}

fn push_rules_rule_1631(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1631,
        source: "Int[x_^m_*(a_+c_.*x_^4)^p_/(d_+e_.*x_^2),x_Symbol] :=
          -(-d/e)^(m/2)*(c*d^2+a*e^2)^(p+1/2)/(e^(2*p)*(c*d^2-a*e^2)) \\[Star]
            Int[(a*d*Rt[c/a,2]+a*e+(c*d+a*e*Rt[c/a,2])*x^2)/((d+e*x^2)*Sqrt[a+c*x^4]),x] +
          1/(e^(2*p)*(c*d^2-a*e^2)) \\[Star] Int[1/Sqrt[a+c*x^4]*
              ExpandToSum[(e^(2*p)*(c*d^2-a*e^2)*x^m*(a+c*x^4)^(p+1/2) +
                (-d/e)^(m/2)*(c*d^2+a*e^2)^(p+1/2)*(a*d*Rt[c/a,2]+a*e+(c*d+a*e*Rt[c/a,2])*x^2))/(d+e*x^2),x],x] /;
        FreeQ[{a,c,d,e},x] && IGtQ[p+1/2,0] && IGtQ[m/2,0] && NeQ[c*d^2-a*e^2,0] && PosQ[c/a]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_15(symbols),
        with: [m_, a__, c__, p_, d__, e__, x_],
        optional: [c__, e__],
        x_free: [a__, c__, d__, e__],
        when: {
            freeq!([a__, c__, d__, e__], x_)
                && igtq!(&p_ + Atom::num((1, 2)), 0)
                && igtq!(&m_ / Atom::num(2), 0)
                && neq!(&c__ * d__.pow(2) - &a__ * e__.pow(2), 0)
                && posq!(&c__ / &a__)
        },
        rhs: {
            let half = Atom::num((1, 2));
            let m_half = &m_ / Atom::num(2);
            let p_half = &p_ + &half;
            let quartic = &a__ + &c__ * x_.pow(4);
            let quadratic = &d__ + &e__ * x_.pow(2);
            let root = rubi_rt(&(&c__ / &a__), 2);
            let delta = &c__ * d__.pow(2) + &a__ * e__.pow(2);
            let k = &c__ * d__.pow(2) - &a__ * e__.pow(2);
            let numerator = &a__ * &d__ * &root
                + &a__ * &e__
                + (&c__ * &d__ + &a__ * &e__ * &root) * x_.pow(2);
            let e_2p = e__.pow(Atom::num(2) * &p_);
            let base_power = (-&d__ / &e__).pow(&m_half);
            let delta_power = delta.pow(&p_half);
            let first_integrand = &numerator / (&quadratic * quartic.sqrt());
            let first = rubi_rhs_int(&first_integrand, x_);
            let expand_payload = (&e_2p
                * &k
                * x_.pow(&m_)
                * quartic.pow(&p_half)
                + &base_power * &delta_power * &numerator)
                / &quadratic;
            let second_integrand = rubi_expand_to_sum(&expand_payload, x_) / quartic.sqrt();
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(-&base_power * &delta_power / (&e_2p * &k), first) + rubi_star(Atom::num(1) / (&e_2p * &k), second)
        },
    ));
}

fn push_rules_rule_1632(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1632,
        source: "Int[x_^m_*(a_.+b_.*x_^2+c_.*x_^4)^p_/(d_+e_.*x_^2),x_Symbol] :=
          (-d/e)^(m/2)*(c*d^2-b*d*e+a*e^2)^(p+1/2)/e^(2*p+1) \\[Star] Int[1/((d+e*x^2)*Sqrt[a+b*x^2+c*x^4]),x] +
          1/e^(2*p+1) \\[Star] Int[1/Sqrt[a+b*x^2+c*x^4]*ExpandToSum[(e^(2*p+1)*x^m*(a+b*x^2+c*x^4)^(p+1/2)-(-d/e)^(m/2)*(c*d^2-b*d*e+a*e^2)^(p+1/2))/(d+e*x^2),x],x] /;
        FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && IGtQ[p+1/2,0] && IGtQ[m/2,0] && NeQ[c*d^2-a*e^2,0] && NegQ[c/a]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_14(symbols),
        with: [m_, a__, b__, c__, p_, d__, e__, x_],
        optional: [a__, b__, c__, e__],
        x_free: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && igtq!(&p_ + Atom::num((1, 2)), 0)
                && igtq!(&m_ / Atom::num(2), 0)
                && neq!(&c__ * d__.pow(2) - &a__ * e__.pow(2), 0)
                && negq!(&c__ / &a__)
        },
        rhs: {
            let p_half = &p_ + Atom::num((1, 2));
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let quadratic = &d__ + &e__ * x_.pow(2);
            let delta = &c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2);
            let base_power = (-&d__ / &e__).pow(&m_ / Atom::num(2));
            let delta_power = delta.pow(&p_half);
            let e_power = e__.pow(Atom::num(2) * &p_ + 1);
            let first = rubi_rhs_int(
                &(Atom::num(1) / (&quadratic * quartic.sqrt())),
                x_,
            );
            let expand_payload = (&e_power * x_.pow(&m_) * quartic.pow(&p_half)
                - &base_power * &delta_power)
                / &quadratic;
            let second_integrand = rubi_expand_to_sum(&expand_payload, x_) / quartic.sqrt();
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(&base_power * &delta_power / &e_power, first) + rubi_star(Atom::num(1) / e_power, second)
        },
    ));
}

fn push_rules_rule_1633(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1633,
        source: "Int[x_^m_*(a_+c_.*x_^4)^p_/(d_+e_.*x_^2),x_Symbol] :=
          (-d/e)^(m/2)*(c*d^2+a*e^2)^(p+1/2)/e^(2*p+1) \\[Star] Int[1/((d+e*x^2)*Sqrt[a+c*x^4]),x] +
          1/e^(2*p+1) \\[Star] Int[1/Sqrt[a+c*x^4]*ExpandToSum[(e^(2*p+1)*x^m*(a+c*x^4)^(p+1/2)-(-d/e)^(m/2)*(c*d^2+a*e^2)^(p+1/2))/(d+e*x^2),x],x] /;
        FreeQ[{a,c,d,e},x] && IGtQ[p+1/2,0] && IGtQ[m/2,0] && NeQ[c*d^2-a*e^2,0] && NegQ[c/a]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_15(symbols),
        with: [m_, a__, c__, p_, d__, e__, x_],
        optional: [c__, e__],
        x_free: [a__, c__, d__, e__],
        when: {
            freeq!([a__, c__, d__, e__], x_)
                && igtq!(&p_ + Atom::num((1, 2)), 0)
                && igtq!(&m_ / Atom::num(2), 0)
                && neq!(&c__ * d__.pow(2) - &a__ * e__.pow(2), 0)
                && negq!(&c__ / &a__)
        },
        rhs: {
            let p_half = &p_ + Atom::num((1, 2));
            let quartic = &a__ + &c__ * x_.pow(4);
            let quadratic = &d__ + &e__ * x_.pow(2);
            let delta = &c__ * d__.pow(2) + &a__ * e__.pow(2);
            let base_power = (-&d__ / &e__).pow(&m_ / Atom::num(2));
            let delta_power = delta.pow(&p_half);
            let e_power = e__.pow(Atom::num(2) * &p_ + 1);
            let first = rubi_rhs_int(
                &(Atom::num(1) / (&quadratic * quartic.sqrt())),
                x_,
            );
            let expand_payload = (&e_power * x_.pow(&m_) * quartic.pow(&p_half)
                - &base_power * &delta_power)
                / &quadratic;
            let second_integrand = rubi_expand_to_sum(&expand_payload, x_) / quartic.sqrt();
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(&base_power * &delta_power / &e_power, first) + rubi_star(Atom::num(1) / e_power, second)
        },
    ));
}

fn push_rules_rule_1634(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1634,
        source: "Int[x_^m_*(a_.+b_.*x_^2+c_.*x_^4)^p_/(d_+e_.*x_^2),x_Symbol] :=
          -(-d/e)^(m/2)*(c*d^2-b*d*e+a*e^2)^(p+1/2)/(e^(2*p)*(c*d^2-a*e^2)) \\[Star]
            Int[(a*d*Rt[c/a,2]+a*e+(c*d+a*e*Rt[c/a,2])*x^2)/((d+e*x^2)*Sqrt[a+b*x^2+c*x^4]),x] +
          (-d/e)^(m/2)/(e^(2*p)*(c*d^2-a*e^2)) \\[Star] Int[x^m/Sqrt[a+b*x^2+c*x^4]*
              ExpandToSum[(e^(2*p)*(-d/e)^(-m/2)*(c*d^2-a*e^2)*(a+b*x^2+c*x^4)^(p+1/2) +
                (a*d*Rt[c/a,2]+a*e+(c*d+a*e*Rt[c/a,2])*x^2)*(c*d^2-b*d*e+a*e^2)^(p+1/2)*x^(-m))/(d+e*x^2),x],x] /;
        FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && IGtQ[p+1/2,0] && ILtQ[m/2,0] && NeQ[c*d^2-a*e^2,0] && PosQ[c/a]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_14(symbols),
        with: [m_, a__, b__, c__, p_, d__, e__, x_],
        optional: [a__, b__, c__, e__],
        x_free: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && igtq!(&p_ + Atom::num((1, 2)), 0)
                && iltq!(&m_ / Atom::num(2), 0)
                && neq!(&c__ * d__.pow(2) - &a__ * e__.pow(2), 0)
                && posq!(&c__ / &a__)
        },
        rhs: {
            let p_half = &p_ + Atom::num((1, 2));
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let quadratic = &d__ + &e__ * x_.pow(2);
            let root = rubi_rt(&(&c__ / &a__), 2);
            let delta = &c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2);
            let k = &c__ * d__.pow(2) - &a__ * e__.pow(2);
            let numerator = &a__ * &d__ * &root
                + &a__ * &e__
                + (&c__ * &d__ + &a__ * &e__ * &root) * x_.pow(2);
            let e_2p = e__.pow(Atom::num(2) * &p_);
            let base = -&d__ / &e__;
            let base_power = base.pow(&m_ / Atom::num(2));
            let inverse_base_power = base.pow(-&m_ / Atom::num(2));
            let delta_power = delta.pow(&p_half);
            let first_integrand = &numerator / (&quadratic * quartic.sqrt());
            let first = rubi_rhs_int(&first_integrand, x_);
            let expand_payload = (&e_2p
                * &inverse_base_power
                * &k
                * quartic.pow(&p_half)
                + &numerator * &delta_power * x_.pow(-&m_))
                / &quadratic;
            let second_integrand = x_.pow(&m_) * rubi_expand_to_sum(&expand_payload, x_)
                / quartic.sqrt();
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(-&base_power * &delta_power / (&e_2p * &k), first) + rubi_star(&base_power / (&e_2p * &k), second)
        },
    ));
}

fn push_rules_rule_1635(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1635,
        source: "Int[x_^m_*(a_+c_.*x_^4)^p_/(d_+e_.*x_^2),x_Symbol] :=
          -(-d/e)^(m/2)*(c*d^2+a*e^2)^(p+1/2)/(e^(2*p)*(c*d^2-a*e^2)) \\[Star]
            Int[(a*d*Rt[c/a,2]+a*e+(c*d+a*e*Rt[c/a,2])*x^2)/((d+e*x^2)*Sqrt[a+c*x^4]),x] +
          (-d/e)^(m/2)/(e^(2*p)*(c*d^2-a*e^2)) \\[Star] Int[x^m/Sqrt[a+c*x^4]*
              ExpandToSum[(e^(2*p)*(-d/e)^(-m/2)*(c*d^2-a*e^2)*(a+c*x^4)^(p+1/2) +
                (a*d*Rt[c/a,2]+a*e+(c*d+a*e*Rt[c/a,2])*x^2)*(c*d^2+a*e^2)^(p+1/2)*x^(-m))/(d+e*x^2),x],x] /;
        FreeQ[{a,c,d,e},x] && IGtQ[p+1/2,0] && ILtQ[m/2,0] && NeQ[c*d^2-a*e^2,0] && PosQ[c/a]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_15(symbols),
        with: [m_, a__, c__, p_, d__, e__, x_],
        optional: [c__, e__],
        x_free: [a__, c__, d__, e__],
        when: {
            freeq!([a__, c__, d__, e__], x_)
                && igtq!(&p_ + Atom::num((1, 2)), 0)
                && iltq!(&m_ / Atom::num(2), 0)
                && neq!(&c__ * d__.pow(2) - &a__ * e__.pow(2), 0)
                && posq!(&c__ / &a__)
        },
        rhs: {
            let p_half = &p_ + Atom::num((1, 2));
            let quartic = &a__ + &c__ * x_.pow(4);
            let quadratic = &d__ + &e__ * x_.pow(2);
            let root = rubi_rt(&(&c__ / &a__), 2);
            let delta = &c__ * d__.pow(2) + &a__ * e__.pow(2);
            let k = &c__ * d__.pow(2) - &a__ * e__.pow(2);
            let numerator = &a__ * &d__ * &root
                + &a__ * &e__
                + (&c__ * &d__ + &a__ * &e__ * &root) * x_.pow(2);
            let e_2p = e__.pow(Atom::num(2) * &p_);
            let base = -&d__ / &e__;
            let base_power = base.pow(&m_ / Atom::num(2));
            let inverse_base_power = base.pow(-&m_ / Atom::num(2));
            let delta_power = delta.pow(&p_half);
            let first_integrand = &numerator / (&quadratic * quartic.sqrt());
            let first = rubi_rhs_int(&first_integrand, x_);
            let expand_payload = (&e_2p
                * &inverse_base_power
                * &k
                * quartic.pow(&p_half)
                + &numerator * &delta_power * x_.pow(-&m_))
                / &quadratic;
            let second_integrand = x_.pow(&m_) * rubi_expand_to_sum(&expand_payload, x_)
                / quartic.sqrt();
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(-&base_power * &delta_power / (&e_2p * &k), first) + rubi_star(&base_power / (&e_2p * &k), second)
        },
    ));
}

fn push_rules_rule_1636(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1636,
        source: "Int[x_^m_*(a_.+b_.*x_^2+c_.*x_^4)^p_/(d_+e_.*x_^2),x_Symbol] :=
          (-d/e)^(m/2)*(c*d^2-b*d*e+a*e^2)^(p+1/2)/e^(2*p+1) \\[Star] Int[1/((d+e*x^2)*Sqrt[a+b*x^2+c*x^4]),x] +
          (-d/e)^(m/2)/e^(2*p+1) \\[Star] Int[x^m/Sqrt[a+b*x^2+c*x^4]*
              ExpandToSum[(e^(2*p+1)*(-d/e)^(-m/2)*(a+b*x^2+c*x^4)^(p+1/2)-(c*d^2-b*d*e+a*e^2)^(p+1/2)*x^(-m))/(d+e*x^2),x],x] /;
        FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && IGtQ[p+1/2,0] && ILtQ[m/2,0] && NeQ[c*d^2-a*e^2,0] && NegQ[c/a]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_14(symbols),
        with: [m_, a__, b__, c__, p_, d__, e__, x_],
        optional: [a__, b__, c__, e__],
        x_free: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && igtq!(&p_ + Atom::num((1, 2)), 0)
                && iltq!(&m_ / Atom::num(2), 0)
                && neq!(&c__ * d__.pow(2) - &a__ * e__.pow(2), 0)
                && negq!(&c__ / &a__)
        },
        rhs: {
            let p_half = &p_ + Atom::num((1, 2));
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let quadratic = &d__ + &e__ * x_.pow(2);
            let delta = &c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2);
            let base = -&d__ / &e__;
            let base_power = base.pow(&m_ / Atom::num(2));
            let inverse_base_power = base.pow(-&m_ / Atom::num(2));
            let delta_power = delta.pow(&p_half);
            let e_power = e__.pow(Atom::num(2) * &p_ + 1);
            let first = rubi_rhs_int(
                &(Atom::num(1) / (&quadratic * quartic.sqrt())),
                x_,
            );
            let expand_payload = (&e_power
                * &inverse_base_power
                * quartic.pow(&p_half)
                - &delta_power * x_.pow(-&m_))
                / &quadratic;
            let second_integrand = x_.pow(&m_) * rubi_expand_to_sum(&expand_payload, x_)
                / quartic.sqrt();
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(&base_power * &delta_power / &e_power, first) + rubi_star(&base_power / e_power, second)
        },
    ));
}

fn push_rules_rule_1637(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1637,
        source: "Int[x_^m_*(a_+c_.*x_^4)^p_/(d_+e_.*x_^2),x_Symbol] :=
          (-d/e)^(m/2)*(c*d^2+a*e^2)^(p+1/2)/e^(2*p+1) \\[Star] Int[1/((d+e*x^2)*Sqrt[a+c*x^4]),x] +
          (-d/e)^(m/2)/e^(2*p+1) \\[Star] Int[x^m/Sqrt[a+c*x^4]*
              ExpandToSum[(e^(2*p+1)*(-d/e)^(-m/2)*(a+c*x^4)^(p+1/2)-(c*d^2+a*e^2)^(p+1/2)*x^(-m))/(d+e*x^2),x],x] /;
        FreeQ[{a,c,d,e},x] && IGtQ[p+1/2,0] && ILtQ[m/2,0] && NeQ[c*d^2-a*e^2,0] && NegQ[c/a]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_15(symbols),
        with: [m_, a__, c__, p_, d__, e__, x_],
        optional: [c__, e__],
        x_free: [a__, c__, d__, e__],
        when: {
            freeq!([a__, c__, d__, e__], x_)
                && igtq!(&p_ + Atom::num((1, 2)), 0)
                && iltq!(&m_ / Atom::num(2), 0)
                && neq!(&c__ * d__.pow(2) - &a__ * e__.pow(2), 0)
                && negq!(&c__ / &a__)
        },
        rhs: {
            let p_half = &p_ + Atom::num((1, 2));
            let quartic = &a__ + &c__ * x_.pow(4);
            let quadratic = &d__ + &e__ * x_.pow(2);
            let delta = &c__ * d__.pow(2) + &a__ * e__.pow(2);
            let base = -&d__ / &e__;
            let base_power = base.pow(&m_ / Atom::num(2));
            let inverse_base_power = base.pow(-&m_ / Atom::num(2));
            let delta_power = delta.pow(&p_half);
            let e_power = e__.pow(Atom::num(2) * &p_ + 1);
            let first = rubi_rhs_int(
                &(Atom::num(1) / (&quadratic * quartic.sqrt())),
                x_,
            );
            let expand_payload = (&e_power
                * &inverse_base_power
                * quartic.pow(&p_half)
                - &delta_power * x_.pow(-&m_))
                / &quadratic;
            let second_integrand = x_.pow(&m_) * rubi_expand_to_sum(&expand_payload, x_)
                / quartic.sqrt();
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(&base_power * &delta_power / &e_power, first) + rubi_star(&base_power / e_power, second)
        },
    ));
}

fn push_rules_rule_1638(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1638,
        source: "Int[x_^m_*(a_.+b_.*x_^2+c_.*x_^4)^p_/(d_+e_.*x_^2),x_Symbol] :=
          -(-d/e)^(m/2)*(c*d^2-b*d*e+a*e^2)^(p+1/2)/(e^(2*p)*(Rt[c/a,2]*d-e)) \\[Star]
            Int[(1+Rt[c/a,2]*x^2)/((d+e*x^2)*Sqrt[a+b*x^2+c*x^4]),x] +
          (c*d^2-b*d*e+a*e^2)^(p+1/2)/(Rt[c/a,2]*d-e) \\[Star] Int[(a+b*x^2+c*x^4)^p*
              ExpandToSum[((Rt[c/a,2]*d-e)*(c*d^2-b*d*e+a*e^2)^(-p-1/2)*x^m+e^(-2*p)*(-d/e)^(m/2)*(1+Rt[c/a,2]*x^2)*(a+b*x^2+c*x^4)^(-p-1/2))/(d+e*x^2),x],x] /;
        FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && ILtQ[p+1/2,0] && IGtQ[m/2,0] && NeQ[c*d^2-a*e^2,0] && PosQ[c/a]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_14(symbols),
        with: [m_, a__, b__, c__, p_, d__, e__, x_],
        optional: [a__, b__, c__, e__],
        x_free: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && iltq!(&p_ + Atom::num((1, 2)), 0)
                && igtq!(&m_ / Atom::num(2), 0)
                && neq!(&c__ * d__.pow(2) - &a__ * e__.pow(2), 0)
                && posq!(&c__ / &a__)
        },
        rhs: {
            let half = Atom::num((1, 2));
            let p_half = &p_ + &half;
            let negative_p_half = -&p_ - &half;
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let quadratic = &d__ + &e__ * x_.pow(2);
            let root = rubi_rt(&(&c__ / &a__), 2);
            let delta = &c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2);
            let root_denominator = &root * &d__ - &e__;
            let root_numerator = Atom::num(1) + &root * x_.pow(2);
            let base_power = (-&d__ / &e__).pow(&m_ / Atom::num(2));
            let delta_power = delta.pow(&p_half);
            let e_2p = e__.pow(Atom::num(2) * &p_);
            let first_integrand = &root_numerator / (&quadratic * quartic.sqrt());
            let first = rubi_rhs_int(&first_integrand, x_);
            let expand_payload = (&root_denominator
                * delta.pow(&negative_p_half)
                * x_.pow(&m_)
                + e__.pow(-Atom::num(2) * &p_)
                    * &base_power
                    * &root_numerator
                    * quartic.pow(&negative_p_half))
                / &quadratic;
            let second_integrand = quartic.pow(&p_) * rubi_expand_to_sum(&expand_payload, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(-&base_power * &delta_power / (&e_2p * &root_denominator), first) + rubi_star(&delta_power / root_denominator, second)
        },
    ));
}

fn push_rules_rule_1639(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1639,
        source: "Int[x_^m_*(a_+c_.*x_^4)^p_/(d_+e_.*x_^2),x_Symbol] :=
          -(-d/e)^(m/2)*(c*d^2+a*e^2)^(p+1/2)/(e^(2*p)*(Rt[c/a,2]*d-e)) \\[Star]
            Int[(1+Rt[c/a,2]*x^2)/((d+e*x^2)*Sqrt[a+c*x^4]),x] +
          (c*d^2+a*e^2)^(p+1/2)/(Rt[c/a,2]*d-e) \\[Star] Int[(a+c*x^4)^p*
              ExpandToSum[((Rt[c/a,2]*d-e)*(c*d^2+a*e^2)^(-p-1/2)*x^m+e^(-2*p)*(-d/e)^(m/2)*(1+Rt[c/a,2]*x^2)*(a+c*x^4)^(-p-1/2))/(d+e*x^2),x],x] /;
        FreeQ[{a,c,d,e},x] && ILtQ[p+1/2,0] && IGtQ[m/2,0] && NeQ[c*d^2-a*e^2,0] && PosQ[c/a]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_15(symbols),
        with: [m_, a__, c__, p_, d__, e__, x_],
        optional: [c__, e__],
        x_free: [a__, c__, d__, e__],
        when: {
            freeq!([a__, c__, d__, e__], x_)
                && iltq!(&p_ + Atom::num((1, 2)), 0)
                && igtq!(&m_ / Atom::num(2), 0)
                && neq!(&c__ * d__.pow(2) - &a__ * e__.pow(2), 0)
                && posq!(&c__ / &a__)
        },
        rhs: {
            let half = Atom::num((1, 2));
            let p_half = &p_ + &half;
            let negative_p_half = -&p_ - &half;
            let quartic = &a__ + &c__ * x_.pow(4);
            let quadratic = &d__ + &e__ * x_.pow(2);
            let root = rubi_rt(&(&c__ / &a__), 2);
            let delta = &c__ * d__.pow(2) + &a__ * e__.pow(2);
            let root_denominator = &root * &d__ - &e__;
            let root_numerator = Atom::num(1) + &root * x_.pow(2);
            let base_power = (-&d__ / &e__).pow(&m_ / Atom::num(2));
            let delta_power = delta.pow(&p_half);
            let e_2p = e__.pow(Atom::num(2) * &p_);
            let first_integrand = &root_numerator / (&quadratic * quartic.sqrt());
            let first = rubi_rhs_int(&first_integrand, x_);
            let expand_payload = (&root_denominator
                * delta.pow(&negative_p_half)
                * x_.pow(&m_)
                + e__.pow(-Atom::num(2) * &p_)
                    * &base_power
                    * &root_numerator
                    * quartic.pow(&negative_p_half))
                / &quadratic;
            let second_integrand = quartic.pow(&p_) * rubi_expand_to_sum(&expand_payload, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(-&base_power * &delta_power / (&e_2p * &root_denominator), first) + rubi_star(&delta_power / root_denominator, second)
        },
    ));
}

fn push_rules_rule_1640(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1640,
        source: "Int[x_^m_*(a_.+b_.*x_^2+c_.*x_^4)^p_/(d_+e_.*x_^2),x_Symbol] :=
          (-d/e)^(m/2)*(c*d^2-b*d*e+a*e^2)^(p+1/2)/e^(2*p+1) \\[Star]
            Int[1/((d+e*x^2)*Sqrt[a+b*x^2+c*x^4]),x] +
          (c*d^2-b*d*e+a*e^2)^(p+1/2) \\[Star] Int[(a+b*x^2+c*x^4)^p*
              ExpandToSum[((c*d^2-b*d*e+a*e^2)^(-p-1/2)*x^m-e^(-2*p-1)*(-d/e)^(m/2)*(a+b*x^2+c*x^4)^(-p-1/2))/(d+e*x^2),x],x] /;
        FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && ILtQ[p+1/2,0] && IGtQ[m/2,0] && NeQ[c*d^2-a*e^2,0] && NegQ[c/a]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_14(symbols),
        with: [m_, a__, b__, c__, p_, d__, e__, x_],
        optional: [a__, b__, c__, e__],
        x_free: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && iltq!(&p_ + Atom::num((1, 2)), 0)
                && igtq!(&m_ / Atom::num(2), 0)
                && neq!(&c__ * d__.pow(2) - &a__ * e__.pow(2), 0)
                && negq!(&c__ / &a__)
        },
        rhs: {
            let half = Atom::num((1, 2));
            let p_half = &p_ + &half;
            let negative_p_half = -&p_ - &half;
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let quadratic = &d__ + &e__ * x_.pow(2);
            let delta = &c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2);
            let base_power = (-&d__ / &e__).pow(&m_ / Atom::num(2));
            let delta_power = delta.pow(&p_half);
            let e_power = e__.pow(Atom::num(2) * &p_ + 1);
            let first = rubi_rhs_int(
                &(Atom::num(1) / (&quadratic * quartic.sqrt())),
                x_,
            );
            let expand_payload = (delta.pow(&negative_p_half) * x_.pow(&m_)
                - e__.pow(-Atom::num(2) * &p_ - 1)
                    * &base_power
                    * quartic.pow(&negative_p_half))
                / &quadratic;
            let second_integrand = quartic.pow(&p_) * rubi_expand_to_sum(&expand_payload, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(&base_power * &delta_power / &e_power, first) + rubi_star(delta_power, second)
        },
    ));
}

fn push_rules_rule_1641(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1641,
        source: "Int[x_^m_*(a_+c_.*x_^4)^p_/(d_+e_.*x_^2),x_Symbol] :=
          (-d/e)^(m/2)*(c*d^2+a*e^2)^(p+1/2)/e^(2*p+1) \\[Star]
            Int[1/((d+e*x^2)*Sqrt[a+c*x^4]),x] +
          (c*d^2+a*e^2)^(p+1/2) \\[Star] Int[(a+c*x^4)^p*
              ExpandToSum[((c*d^2+a*e^2)^(-p-1/2)*x^m-e^(-2*p-1)*(-d/e)^(m/2)*(a+c*x^4)^(-p-1/2))/(d+e*x^2),x],x] /;
        FreeQ[{a,c,d,e},x] && ILtQ[p+1/2,0] && IGtQ[m/2,0] && NeQ[c*d^2-a*e^2,0] && NegQ[c/a]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_15(symbols),
        with: [m_, a__, c__, p_, d__, e__, x_],
        optional: [c__, e__],
        x_free: [a__, c__, d__, e__],
        when: {
            freeq!([a__, c__, d__, e__], x_)
                && iltq!(&p_ + Atom::num((1, 2)), 0)
                && igtq!(&m_ / Atom::num(2), 0)
                && neq!(&c__ * d__.pow(2) - &a__ * e__.pow(2), 0)
                && negq!(&c__ / &a__)
        },
        rhs: {
            let half = Atom::num((1, 2));
            let p_half = &p_ + &half;
            let negative_p_half = -&p_ - &half;
            let quartic = &a__ + &c__ * x_.pow(4);
            let quadratic = &d__ + &e__ * x_.pow(2);
            let delta = &c__ * d__.pow(2) + &a__ * e__.pow(2);
            let base_power = (-&d__ / &e__).pow(&m_ / Atom::num(2));
            let delta_power = delta.pow(&p_half);
            let e_power = e__.pow(Atom::num(2) * &p_ + 1);
            let first = rubi_rhs_int(
                &(Atom::num(1) / (&quadratic * quartic.sqrt())),
                x_,
            );
            let expand_payload = (delta.pow(&negative_p_half) * x_.pow(&m_)
                - e__.pow(-Atom::num(2) * &p_ - 1)
                    * &base_power
                    * quartic.pow(&negative_p_half))
                / &quadratic;
            let second_integrand = quartic.pow(&p_) * rubi_expand_to_sum(&expand_payload, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(&base_power * &delta_power / &e_power, first) + rubi_star(delta_power, second)
        },
    ));
}

fn push_rules_rule_1642(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1642,
        source: "Int[x_^m_*(a_.+b_.*x_^2+c_.*x_^4)^p_/(d_+e_.*x_^2),x_Symbol] :=
          -(-d/e)^(m/2)*(c*d^2-b*d*e+a*e^2)^(p+1/2)/(e^(2*p)*(Rt[c/a,2]*d-e)) \\[Star]
            Int[(1+Rt[c/a,2]*x^2)/((d+e*x^2)*Sqrt[a+b*x^2+c*x^4]),x] +
          (-d/e)^(m/2)*(c*d^2-b*d*e+a*e^2)^(p+1/2)/(Rt[c/a,2]*d-e) \\[Star] Int[x^m*(a+b*x^2+c*x^4)^p*
              ExpandToSum[((-d/e)^(-m/2)*(Rt[c/a,2]*d-e)*(c*d^2-b*d*e+a*e^2)^(-p-1/2)+e^(-2*p)*(1+Rt[c/a,2]*x^2)*x^(-m)*(a+b*x^2+c*x^4)^(-p-1/2))/(d+e*x^2),x],x] /;
        FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && ILtQ[p+1/2,0] && ILtQ[m/2,0] && NeQ[c*d^2-a*e^2,0] && PosQ[c/a]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_14(symbols),
        with: [m_, a__, b__, c__, p_, d__, e__, x_],
        optional: [a__, b__, c__, e__],
        x_free: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && iltq!(&p_ + Atom::num((1, 2)), 0)
                && iltq!(&m_ / Atom::num(2), 0)
                && neq!(&c__ * d__.pow(2) - &a__ * e__.pow(2), 0)
                && posq!(&c__ / &a__)
        },
        rhs: {
            let half = Atom::num((1, 2));
            let p_half = &p_ + &half;
            let negative_p_half = -&p_ - &half;
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let quadratic = &d__ + &e__ * x_.pow(2);
            let root = rubi_rt(&(&c__ / &a__), 2);
            let delta = &c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2);
            let root_denominator = &root * &d__ - &e__;
            let root_numerator = Atom::num(1) + &root * x_.pow(2);
            let base = -&d__ / &e__;
            let base_power = base.pow(&m_ / Atom::num(2));
            let inverse_base_power = base.pow(-&m_ / Atom::num(2));
            let delta_power = delta.pow(&p_half);
            let e_2p = e__.pow(Atom::num(2) * &p_);
            let first_integrand = &root_numerator / (&quadratic * quartic.sqrt());
            let first = rubi_rhs_int(&first_integrand, x_);
            let expand_payload = (&inverse_base_power
                * &root_denominator
                * delta.pow(&negative_p_half)
                + e__.pow(-Atom::num(2) * &p_)
                    * &root_numerator
                    * x_.pow(-&m_)
                    * quartic.pow(&negative_p_half))
                / &quadratic;
            let second_integrand = x_.pow(&m_)
                * quartic.pow(&p_)
                * rubi_expand_to_sum(&expand_payload, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(-&base_power * &delta_power / (&e_2p * &root_denominator), first) + rubi_star(&base_power * &delta_power / root_denominator, second)
        },
    ));
}

fn push_rules_rule_1643(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1643,
        source: "Int[x_^m_*(a_+c_.*x_^4)^p_/(d_+e_.*x_^2),x_Symbol] :=
          -(-d/e)^(m/2)*(c*d^2+a*e^2)^(p+1/2)/(e^(2*p)*(Rt[c/a,2]*d-e)) \\[Star]
            Int[(1+Rt[c/a,2]*x^2)/((d+e*x^2)*Sqrt[a+c*x^4]),x] +
          (-d/e)^(m/2)*(c*d^2+a*e^2)^(p+1/2)/(Rt[c/a,2]*d-e) \\[Star] Int[x^m*(a+c*x^4)^p*
              ExpandToSum[((-d/e)^(-m/2)*(Rt[c/a,2]*d-e)*(c*d^2+a*e^2)^(-p-1/2)+e^(-2*p)*(1+Rt[c/a,2]*x^2)*x^(-m)*(a+c*x^4)^(-p-1/2))/(d+e*x^2),x],x] /;
        FreeQ[{a,c,d,e},x] && ILtQ[p+1/2,0] && ILtQ[m/2,0] && NeQ[c*d^2-a*e^2,0] && PosQ[c/a]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_15(symbols),
        with: [m_, a__, c__, p_, d__, e__, x_],
        optional: [c__, e__],
        x_free: [a__, c__, d__, e__],
        when: {
            freeq!([a__, c__, d__, e__], x_)
                && iltq!(&p_ + Atom::num((1, 2)), 0)
                && iltq!(&m_ / Atom::num(2), 0)
                && neq!(&c__ * d__.pow(2) - &a__ * e__.pow(2), 0)
                && posq!(&c__ / &a__)
        },
        rhs: {
            let half = Atom::num((1, 2));
            let p_half = &p_ + &half;
            let negative_p_half = -&p_ - &half;
            let quartic = &a__ + &c__ * x_.pow(4);
            let quadratic = &d__ + &e__ * x_.pow(2);
            let root = rubi_rt(&(&c__ / &a__), 2);
            let delta = &c__ * d__.pow(2) + &a__ * e__.pow(2);
            let root_denominator = &root * &d__ - &e__;
            let root_numerator = Atom::num(1) + &root * x_.pow(2);
            let base = -&d__ / &e__;
            let base_power = base.pow(&m_ / Atom::num(2));
            let inverse_base_power = base.pow(-&m_ / Atom::num(2));
            let delta_power = delta.pow(&p_half);
            let e_2p = e__.pow(Atom::num(2) * &p_);
            let first_integrand = &root_numerator / (&quadratic * quartic.sqrt());
            let first = rubi_rhs_int(&first_integrand, x_);
            let expand_payload = (&inverse_base_power
                * &root_denominator
                * delta.pow(&negative_p_half)
                + e__.pow(-Atom::num(2) * &p_)
                    * &root_numerator
                    * x_.pow(-&m_)
                    * quartic.pow(&negative_p_half))
                / &quadratic;
            let second_integrand = x_.pow(&m_)
                * quartic.pow(&p_)
                * rubi_expand_to_sum(&expand_payload, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(-&base_power * &delta_power / (&e_2p * &root_denominator), first) + rubi_star(&base_power * &delta_power / root_denominator, second)
        },
    ));
}

fn push_rules_rule_1644(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1644,
        source: "Int[x_^m_*(a_.+b_.*x_^2+c_.*x_^4)^p_/(d_+e_.*x_^2),x_Symbol] :=
          (-d/e)^(m/2)*(c*d^2-b*d*e+a*e^2)^(p+1/2)/e^(2*p+1) \\[Star]
            Int[1/((d+e*x^2)*Sqrt[a+b*x^2+c*x^4]),x] +
          (-d/e)^(m/2)*(c*d^2-b*d*e+a*e^2)^(p+1/2) \\[Star] Int[x^m*(a+b*x^2+c*x^4)^p*
              ExpandToSum[((-d/e)^(-m/2)*(c*d^2-b*d*e+a*e^2)^(-p-1/2)-e^(-2*p-1)*x^(-m)*(a+b*x^2+c*x^4)^(-p-1/2))/(d+e*x^2),x],x] /;
        FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && ILtQ[p+1/2,0] && ILtQ[m/2,0] && NeQ[c*d^2-a*e^2,0] && NegQ[c/a]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_14(symbols),
        with: [m_, a__, b__, c__, p_, d__, e__, x_],
        optional: [a__, b__, c__, e__],
        x_free: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && iltq!(&p_ + Atom::num((1, 2)), 0)
                && iltq!(&m_ / Atom::num(2), 0)
                && neq!(&c__ * d__.pow(2) - &a__ * e__.pow(2), 0)
                && negq!(&c__ / &a__)
        },
        rhs: {
            let half = Atom::num((1, 2));
            let p_half = &p_ + &half;
            let negative_p_half = -&p_ - &half;
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let quadratic = &d__ + &e__ * x_.pow(2);
            let delta = &c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2);
            let base = -&d__ / &e__;
            let base_power = base.pow(&m_ / Atom::num(2));
            let inverse_base_power = base.pow(-&m_ / Atom::num(2));
            let delta_power = delta.pow(&p_half);
            let e_power = e__.pow(Atom::num(2) * &p_ + 1);
            let first = rubi_rhs_int(
                &(Atom::num(1) / (&quadratic * quartic.sqrt())),
                x_,
            );
            let expand_payload = (&inverse_base_power * delta.pow(&negative_p_half)
                - e__.pow(-Atom::num(2) * &p_ - 1)
                    * x_.pow(-&m_)
                    * quartic.pow(&negative_p_half))
                / &quadratic;
            let second_integrand = x_.pow(&m_)
                * quartic.pow(&p_)
                * rubi_expand_to_sum(&expand_payload, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(&base_power * &delta_power / &e_power, first) + rubi_star(&base_power * &delta_power, second)
        },
    ));
}

fn push_rules_rule_1645(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1645,
        source: "Int[x_^m_*(a_+c_.*x_^4)^p_/(d_+e_.*x_^2),x_Symbol] :=
          (-d/e)^(m/2)*(c*d^2+a*e^2)^(p+1/2)/e^(2*p+1) \\[Star]
            Int[1/((d+e*x^2)*Sqrt[a+c*x^4]),x] +
          (-d/e)^(m/2)*(c*d^2+a*e^2)^(p+1/2) \\[Star] Int[x^m*(a+c*x^4)^p*
              ExpandToSum[((-d/e)^(-m/2)*(c*d^2+a*e^2)^(-p-1/2)-e^(-2*p-1)*x^(-m)*(a+c*x^4)^(-p-1/2))/(d+e*x^2),x],x] /;
        FreeQ[{a,c,d,e},x] && ILtQ[p+1/2,0] && ILtQ[m/2,0] && NeQ[c*d^2-a*e^2,0] && NegQ[c/a]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_15(symbols),
        with: [m_, a__, c__, p_, d__, e__, x_],
        optional: [c__, e__],
        x_free: [a__, c__, d__, e__],
        when: {
            freeq!([a__, c__, d__, e__], x_)
                && iltq!(&p_ + Atom::num((1, 2)), 0)
                && iltq!(&m_ / Atom::num(2), 0)
                && neq!(&c__ * d__.pow(2) - &a__ * e__.pow(2), 0)
                && negq!(&c__ / &a__)
        },
        rhs: {
            let half = Atom::num((1, 2));
            let p_half = &p_ + &half;
            let negative_p_half = -&p_ - &half;
            let quartic = &a__ + &c__ * x_.pow(4);
            let quadratic = &d__ + &e__ * x_.pow(2);
            let delta = &c__ * d__.pow(2) + &a__ * e__.pow(2);
            let base = -&d__ / &e__;
            let base_power = base.pow(&m_ / Atom::num(2));
            let inverse_base_power = base.pow(-&m_ / Atom::num(2));
            let delta_power = delta.pow(&p_half);
            let e_power = e__.pow(Atom::num(2) * &p_ + 1);
            let first = rubi_rhs_int(
                &(Atom::num(1) / (&quadratic * quartic.sqrt())),
                x_,
            );
            let expand_payload = (&inverse_base_power * delta.pow(&negative_p_half)
                - e__.pow(-Atom::num(2) * &p_ - 1)
                    * x_.pow(-&m_)
                    * quartic.pow(&negative_p_half))
                / &quadratic;
            let second_integrand = x_.pow(&m_)
                * quartic.pow(&p_)
                * rubi_expand_to_sum(&expand_payload, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(&base_power * &delta_power / &e_power, first) + rubi_star(&base_power * &delta_power, second)
        },
    ));
}

fn push_rules_rule_1646(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1646,
        source: "Int[(f_.*x_)^m_*(a_.+b_.*x_^2+c_.*x_^4)^p_./(d_+e_.*x_^2),x_Symbol] :=
          1/d^2 \\[Star] Int[(f*x)^m*(a*d+(b*d-a*e)*x^2)*(a+b*x^2+c*x^4)^(p-1),x] +
          (c*d^2-b*d*e+a*e^2)/(d^2*f^4) \\[Star] Int[(f*x)^(m+4)*(a+b*x^2+c*x^4)^(p-1)/(d+e*x^2),x] /;
        FreeQ[{a,b,c,d,e,f},x] && NeQ[b^2-4*a*c,0] && GtQ[p,0] && LtQ[m,-2]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, e__, f__, m_, p_, x_],
        optional: [f__, a__, b__, c__, p_, e__],
        x_free: [a__, b__, c__, d__, e__, f__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && gtq!(p_, 0)
                && ltq!(m_, -2)
        },
        rhs: {
            let fx = &f__ * x_;
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let quadratic = &d__ + &e__ * x_.pow(2);
            let first_integrand = fx.pow(&m_)
                * (&a__ * &d__ + (&b__ * &d__ - &a__ * &e__) * x_.pow(2))
                * quartic.pow(&p_ - Atom::num(1));
            let second_integrand = fx.pow(&m_ + Atom::num(4)) * quartic.pow(&p_ - Atom::num(1)) / quadratic;
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);
            let delta = &c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2);

            rubi_star(Atom::num(1) / d__.pow(2), first)
                    + rubi_star(&delta / (d__.pow(2) * f__.pow(4)), second)
        },
    ));
}

fn push_rules_rule_1647(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1647,
        source: "Int[(f_.*x_)^m_*(a_+c_.*x_^4)^p_./(d_+e_.*x_^2),x_Symbol] :=
          a/d^2 \\[Star] Int[(f*x)^m*(d-e*x^2)*(a+c*x^4)^(p-1),x] +
          (c*d^2+a*e^2)/(d^2*f^4) \\[Star] Int[(f*x)^(m+4)*(a+c*x^4)^(p-1)/(d+e*x^2),x] /;
        FreeQ[{a,c,d,e,f},x] && GtQ[p,0] && LtQ[m,-2]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, c__, d__, e__, f__, m_, p_, x_],
        optional: [f__, c__, p_, e__],
        x_free: [a__, c__, d__, e__, f__],
        when: { freeq!([a__, c__, d__, e__, f__], x_) && gtq!(p_, 0) && ltq!(m_, -2) },
        rhs: {
            let fx = &f__ * x_;
            let quartic = &a__ + &c__ * x_.pow(4);
            let quadratic = &d__ + &e__ * x_.pow(2);
            let first_integrand =
                fx.pow(&m_) * (&d__ - &e__ * x_.pow(2)) * quartic.pow(&p_ - Atom::num(1));
            let second_integrand = fx.pow(&m_ + Atom::num(4)) * quartic.pow(&p_ - Atom::num(1)) / quadratic;
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);
            let delta = &c__ * d__.pow(2) + &a__ * e__.pow(2);

            rubi_star(&a__ / d__.pow(2), first)
                    + rubi_star(&delta / (d__.pow(2) * f__.pow(4)), second)
        },
    ));
}

fn push_rules_rule_1648(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1648,
        source: "Int[(f_.*x_)^m_*(a_.+b_.*x_^2+c_.*x_^4)^p_./(d_+e_.*x_^2),x_Symbol] :=
          1/(d*e) \\[Star] Int[(f*x)^m*(a*e+c*d*x^2)*(a+b*x^2+c*x^4)^(p-1),x] -
          (c*d^2-b*d*e+a*e^2)/(d*e*f^2) \\[Star] Int[(f*x)^(m+2)*(a+b*x^2+c*x^4)^(p-1)/(d+e*x^2),x] /;
        FreeQ[{a,b,c,d,e,f},x] && NeQ[b^2-4*a*c,0] && GtQ[p,0] && LtQ[m,0]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, e__, f__, m_, p_, x_],
        optional: [f__, a__, b__, c__, p_, e__],
        x_free: [a__, b__, c__, d__, e__, f__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && gtq!(p_, 0)
                && ltq!(m_, 0)
        },
        rhs: {
            let fx = &f__ * x_;
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let quadratic = &d__ + &e__ * x_.pow(2);
            let first_integrand =
                fx.pow(&m_) * (&a__ * &e__ + &c__ * &d__ * x_.pow(2)) * quartic.pow(&p_ - Atom::num(1));
            let second_integrand = fx.pow(&m_ + Atom::num(2)) * quartic.pow(&p_ - Atom::num(1)) / quadratic;
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);
            let delta = &c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2);

            rubi_star(Atom::num(1) / (&d__ * &e__), first)
                    + rubi_star(-&delta / (&d__ * &e__ * f__.pow(2)), second)
        },
    ));
}

fn push_rules_rule_1649(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1649,
        source: "Int[(f_.*x_)^m_*(a_+c_.*x_^4)^p_./(d_+e_.*x_^2),x_Symbol] :=
          1/(d*e) \\[Star] Int[(f*x)^m*(a*e+c*d*x^2)*(a+c*x^4)^(p-1),x] -
          (c*d^2+a*e^2)/(d*e*f^2) \\[Star] Int[(f*x)^(m+2)*(a+c*x^4)^(p-1)/(d+e*x^2),x] /;
        FreeQ[{a,c,d,e,f},x] && GtQ[p,0] && LtQ[m,0]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, c__, d__, e__, f__, m_, p_, x_],
        optional: [f__, c__, p_, e__],
        x_free: [a__, c__, d__, e__, f__],
        when: { freeq!([a__, c__, d__, e__, f__], x_) && gtq!(p_, 0) && ltq!(m_, 0) },
        rhs: {
            let fx = &f__ * x_;
            let quartic = &a__ + &c__ * x_.pow(4);
            let quadratic = &d__ + &e__ * x_.pow(2);
            let first_integrand =
                fx.pow(&m_) * (&a__ * &e__ + &c__ * &d__ * x_.pow(2)) * quartic.pow(&p_ - Atom::num(1));
            let second_integrand = fx.pow(&m_ + Atom::num(2)) * quartic.pow(&p_ - Atom::num(1)) / quadratic;
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);
            let delta = &c__ * d__.pow(2) + &a__ * e__.pow(2);

            rubi_star(Atom::num(1) / (&d__ * &e__), first)
                    + rubi_star(-&delta / (&d__ * &e__ * f__.pow(2)), second)
        },
    ));
}

fn push_rules_rule_1650(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1650,
        source: "Int[(f_.*x_)^m_.*(a_.+b_.*x_^2+c_.*x_^4)^p_/(d_+e_.*x_^2),x_Symbol] :=
          -f^4/(c*d^2-b*d*e+a*e^2) \\[Star] Int[(f*x)^(m-4)*(a*d+(b*d-a*e)*x^2)*(a+b*x^2+c*x^4)^p,x] +
          d^2*f^4/(c*d^2-b*d*e+a*e^2) \\[Star] Int[(f*x)^(m-4)*(a+b*x^2+c*x^4)^(p+1)/(d+e*x^2),x] /;
        FreeQ[{a,b,c,d,e,f},x] && NeQ[b^2-4*a*c,0] && LtQ[p,-1] && GtQ[m,2]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, e__, f__, m_, p_, x_],
        optional: [f__, m_, a__, b__, c__, e__],
        x_free: [a__, b__, c__, d__, e__, f__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && ltq!(p_, -1)
                && gtq!(m_, 2)
        },
        rhs: {
            let fx = &f__ * x_;
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let quadratic = &d__ + &e__ * x_.pow(2);
            let first_integrand =
                fx.pow(&m_ - Atom::num(4)) * (&a__ * &d__ + (&b__ * &d__ - &a__ * &e__) * x_.pow(2)) * quartic.pow(&p_);
            let second_integrand = fx.pow(&m_ - Atom::num(4)) * quartic.pow(&p_ + Atom::num(1)) / quadratic;
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);
            let delta = &c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2);

            rubi_star(-f__.pow(4) / &delta, first)
                    + rubi_star(d__.pow(2) * f__.pow(4) / delta, second)
        },
    ));
}

fn push_rules_rule_1651(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1651,
        source: "Int[(f_.*x_)^m_.*(a_+c_.*x_^4)^p_/(d_+e_.*x_^2),x_Symbol] :=
          -a*f^4/(c*d^2+a*e^2) \\[Star] Int[(f*x)^(m-4)*(d-e*x^2)*(a+c*x^4)^p,x] +
          d^2*f^4/(c*d^2+a*e^2) \\[Star] Int[(f*x)^(m-4)*(a+c*x^4)^(p+1)/(d+e*x^2),x] /;
        FreeQ[{a,c,d,e,f},x] && LtQ[p,-1] && GtQ[m,2]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, c__, d__, e__, f__, m_, p_, x_],
        optional: [f__, m_, c__, e__],
        x_free: [a__, c__, d__, e__, f__],
        when: { freeq!([a__, c__, d__, e__, f__], x_) && ltq!(p_, -1) && gtq!(m_, 2) },
        rhs: {
            let fx = &f__ * x_;
            let quartic = &a__ + &c__ * x_.pow(4);
            let quadratic = &d__ + &e__ * x_.pow(2);
            let first_integrand =
                fx.pow(&m_ - Atom::num(4)) * (&d__ - &e__ * x_.pow(2)) * quartic.pow(&p_);
            let second_integrand = fx.pow(&m_ - Atom::num(4)) * quartic.pow(&p_ + Atom::num(1)) / quadratic;
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);
            let delta = &c__ * d__.pow(2) + &a__ * e__.pow(2);

            rubi_star(-&a__ * f__.pow(4) / &delta, first)
                    + rubi_star(d__.pow(2) * f__.pow(4) / delta, second)
        },
    ));
}

fn push_rules_rule_1652(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1652,
        source: "Int[(f_.*x_)^m_.*(a_.+b_.*x_^2+c_.*x_^4)^p_/(d_+e_.*x_^2),x_Symbol] :=
          f^2/(c*d^2-b*d*e+a*e^2) \\[Star] Int[(f*x)^(m-2)*(a*e+c*d*x^2)*(a+b*x^2+c*x^4)^p,x] -
          d*e*f^2/(c*d^2-b*d*e+a*e^2) \\[Star] Int[(f*x)^(m-2)*(a+b*x^2+c*x^4)^(p+1)/(d+e*x^2),x] /;
        FreeQ[{a,b,c,d,e,f},x] && NeQ[b^2-4*a*c,0] && LtQ[p,-1] && GtQ[m,0]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern:  rubi_shared_pattern_0(symbols),
        with: [a__, b__, c__, d__, e__, f__, m_, p_, x_],
        optional: [f__, m_, a__, b__, c__, e__],
        x_free: [a__, b__, c__, d__, e__, f__],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && ltq!(p_, -1)
                && gtq!(m_, 0)
        },
        rhs: {
            let fx = &f__ * x_;
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let quadratic = &d__ + &e__ * x_.pow(2);
            let first_integrand =
                fx.pow(&m_ - Atom::num(2)) * (&a__ * &e__ + &c__ * &d__ * x_.pow(2)) * quartic.pow(&p_);
            let second_integrand = fx.pow(&m_ - Atom::num(2)) * quartic.pow(&p_ + Atom::num(1)) / quadratic;
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);
            let delta = &c__ * d__.pow(2) - &b__ * &d__ * &e__ + &a__ * e__.pow(2);

            rubi_star(f__.pow(2) / &delta, first)
                    + rubi_star(-&d__ * &e__ * f__.pow(2) / delta, second)
        },
    ));
}

fn push_rules_rule_1653(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, m_, p_, x_);
    rules.push(rubi_rule!(
        order: 1653,
        source: "Int[(f_.*x_)^m_.*(a_+c_.*x_^4)^p_/(d_+e_.*x_^2),x_Symbol] :=
          f^2/(c*d^2+a*e^2) \\[Star] Int[(f*x)^(m-2)*(a*e+c*d*x^2)*(a+c*x^4)^p,x] -
          d*e*f^2/(c*d^2+a*e^2) \\[Star] Int[(f*x)^(m-2)*(a+c*x^4)^(p+1)/(d+e*x^2),x] /;
        FreeQ[{a,c,d,e,f},x] && LtQ[p,-1] && GtQ[m,0]",
        desc: "Decompose the integrand into a sum of simpler integrals.",
        refs: [],
        pattern:  rubi_shared_pattern_1(symbols),
        with: [a__, c__, d__, e__, f__, m_, p_, x_],
        optional: [f__, m_, c__, e__],
        x_free: [a__, c__, d__, e__, f__],
        when: { freeq!([a__, c__, d__, e__, f__], x_) && ltq!(p_, -1) && gtq!(m_, 0) },
        rhs: {
            let fx = &f__ * x_;
            let quartic = &a__ + &c__ * x_.pow(4);
            let quadratic = &d__ + &e__ * x_.pow(2);
            let first_integrand =
                fx.pow(&m_ - Atom::num(2)) * (&a__ * &e__ + &c__ * &d__ * x_.pow(2)) * quartic.pow(&p_);
            let second_integrand = fx.pow(&m_ - Atom::num(2)) * quartic.pow(&p_ + Atom::num(1)) / quadratic;
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);
            let delta = &c__ * d__.pow(2) + &a__ * e__.pow(2);

            rubi_star(f__.pow(2) / &delta, first)
                    + rubi_star(-&d__ * &e__ * f__.pow(2) / delta, second)
        },
    ));
}

fn push_rules_rule_1654(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 1654,
        source: "Int[x_^2/((d_+e_.*x_^2)*Sqrt[a_+b_.*x_^2+c_.*x_^4]),x_Symbol] :=
          1/(2*e) \\[Star] Int[1/Sqrt[a+b*x^2+c*x^4],x] -
          1/(2*e) \\[Star] Int[(d-e*x^2)/((d+e*x^2)*Sqrt[a+b*x^2+c*x^4]),x] /;
        FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && PosQ[c/a] && EqQ[c*d^2-a*e^2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_10(symbols),
        with: [a__, b__, c__, d__, e__, x_],
        optional: [e__, b__, c__],
        x_free: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && posq!(&c__ / &a__)
                && eqq!(&c__ * d__.pow(2) - &a__ * e__.pow(2), 0)
        },
        rhs: {
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let quadratic = &d__ + &e__ * x_.pow(2);
            let first_integrand = Atom::num(1) / quartic.sqrt();
            let second_integrand = (&d__ - &e__ * x_.pow(2)) / (quadratic * quartic.sqrt());
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);
            let coefficient = Atom::num(1) / (Atom::num(2) * &e__);

            rubi_star(&coefficient, first)
                    + rubi_star(-coefficient, second)
        },
    ));
}

fn push_rules_rule_1655(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 1655,
        source: "Int[x_^2/((d_+e_.*x_^2)*Sqrt[a_+c_.*x_^4]),x_Symbol] :=
          1/(2*e) \\[Star] Int[1/Sqrt[a+c*x^4],x] -
          1/(2*e) \\[Star] Int[(d-e*x^2)/((d+e*x^2)*Sqrt[a+c*x^4]),x] /;
        FreeQ[{a,c,d,e},x] && PosQ[c/a] && EqQ[c*d^2-a*e^2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_11(symbols),
        with: [a__, c__, d__, e__, x_],
        optional: [e__, c__],
        x_free: [a__, c__, d__, e__],
        when: {
            freeq!([a__, c__, d__, e__], x_)
                && posq!(&c__ / &a__)
                && eqq!(&c__ * d__.pow(2) - &a__ * e__.pow(2), 0)
        },
        rhs: {
            let quartic = &a__ + &c__ * x_.pow(4);
            let quadratic = &d__ + &e__ * x_.pow(2);
            let first_integrand = Atom::num(1) / quartic.sqrt();
            let second_integrand = (&d__ - &e__ * x_.pow(2)) / (quadratic * quartic.sqrt());
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);
            let coefficient = Atom::num(1) / (Atom::num(2) * &e__);

            rubi_star(&coefficient, first)
                    + rubi_star(-coefficient, second)
        },
    ));
}

fn push_rules_rule_1656(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 1656,
        source: "Int[x_^2/((d_+e_.*x_^2)*Sqrt[a_+b_.*x_^2+c_.*x_^4]),x_Symbol] :=
          With[{q=Rt[c/a,2]},
          -a*(e+d*q)/(c*d^2-a*e^2) \\[Star] Int[1/Sqrt[a+b*x^2+c*x^4],x] +
          a*d*(e+d*q)/(c*d^2-a*e^2) \\[Star] Int[(1+q*x^2)/((d+e*x^2)*Sqrt[a+b*x^2+c*x^4]),x]] /;
        FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && PosQ[c/a] && NeQ[c*d^2-a*e^2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_10(symbols),
        with: [a__, b__, c__, d__, e__, x_],
        optional: [e__, b__, c__],
        x_free: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && posq!(&c__ / &a__)
                && neq!(&c__ * d__.pow(2) - &a__ * e__.pow(2), 0)
        },
        rhs: {
            let q = rubi_rt(&(&c__ / &a__), 2);
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let quadratic = &d__ + &e__ * x_.pow(2);
            let coefficient = &e__ + &d__ * &q;
            let first_integrand = Atom::num(1) / quartic.sqrt();
            let second_integrand = (Atom::num(1) + &q * x_.pow(2)) / (quadratic * quartic.sqrt());
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);
            let denominator = &c__ * d__.pow(2) - &a__ * e__.pow(2);

            rubi_star(-&a__ * &coefficient / &denominator, first)
                    + rubi_star(&a__ * &d__ * coefficient / denominator, second)
        },
    ));
}

fn push_rules_rule_1657(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 1657,
        source: "Int[x_^2/((d_+e_.*x_^2)*Sqrt[a_+c_.*x_^4]),x_Symbol] :=
          With[{q=Rt[c/a,2]},
          -a*(e+d*q)/(c*d^2-a*e^2) \\[Star] Int[1/Sqrt[a+c*x^4],x] +
          a*d*(e+d*q)/(c*d^2-a*e^2) \\[Star] Int[(1+q*x^2)/((d+e*x^2)*Sqrt[a+c*x^4]),x]] /;
        FreeQ[{a,c,d,e},x] && PosQ[c/a] && NeQ[c*d^2-a*e^2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_11(symbols),
        with: [a__, c__, d__, e__, x_],
        optional: [e__, c__],
        x_free: [a__, c__, d__, e__],
        when: {
            freeq!([a__, c__, d__, e__], x_)
                && posq!(&c__ / &a__)
                && neq!(&c__ * d__.pow(2) - &a__ * e__.pow(2), 0)
        },
        rhs: {
            let q = rubi_rt(&(&c__ / &a__), 2);
            let quartic = &a__ + &c__ * x_.pow(4);
            let quadratic = &d__ + &e__ * x_.pow(2);
            let coefficient = &e__ + &d__ * &q;
            let first_integrand = Atom::num(1) / quartic.sqrt();
            let second_integrand = (Atom::num(1) + &q * x_.pow(2)) / (quadratic * quartic.sqrt());
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);
            let denominator = &c__ * d__.pow(2) - &a__ * e__.pow(2);

            rubi_star(-&a__ * &coefficient / &denominator, first)
                    + rubi_star(&a__ * &d__ * coefficient / denominator, second)
        },
    ));
}

fn push_rules_rule_1658(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 1658,
        source: "Int[x_^2/((d_+e_.*x_^2)*Sqrt[a_+b_.*x_^2+c_.*x_^4]),x_Symbol] :=
          1/e \\[Star] Int[1/Sqrt[a+b*x^2+c*x^4],x] - d/e \\[Star] Int[1/((d+e*x^2)*Sqrt[a+b*x^2+c*x^4]),x] /;
        FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_10(symbols),
        with: [d__, e__, a__, b__, c__, x_],
        optional: [e__, b__, c__],
        x_free: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
        },
        rhs: {
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let quadratic = &d__ + &e__ * x_.pow(2);
            let first = rubi_rhs_int(&(Atom::num(1) / quartic.sqrt()), x_);
            let second = rubi_rhs_int(&(Atom::num(1) / (quadratic * quartic.sqrt())), x_);

            rubi_star(Atom::num(1) / &e__, first)
                    + rubi_star(-&d__ / &e__, second)
        },
    ));
}

fn push_rules_rule_1659(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 1659,
        source: "Int[x_^2/((d_+e_.*x_^2)*Sqrt[a_+c_.*x_^4]),x_Symbol] :=
          1/e \\[Star] Int[1/Sqrt[a+c*x^4],x] - d/e \\[Star] Int[1/((d+e*x^2)*Sqrt[a+c*x^4]),x] /;
        FreeQ[{a,c,d,e},x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_11(symbols),
        with: [d__, e__, a__, c__, x_],
        optional: [e__, c__],
        x_free: [a__, c__, d__, e__],
        when: { freeq!([a__, c__, d__, e__], x_) },
        rhs: {
            let quartic = &a__ + &c__ * x_.pow(4);
            let quadratic = &d__ + &e__ * x_.pow(2);
            let first = rubi_rhs_int(&(Atom::num(1) / quartic.sqrt()), x_);
            let second = rubi_rhs_int(&(Atom::num(1) / (quadratic * quartic.sqrt())), x_);

            rubi_star(Atom::num(1) / &e__, first)
                    + rubi_star(-&d__ / &e__, second)
        },
    ));
}

fn push_rules_rule_1664(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 1664,
        source: "Int[x_^4/((d_+e_.*x_^2)*Sqrt[a_+b_.*x_^2+c_.*x_^4]),x_Symbol] :=
          d^2/e^2 \\[Star] Int[1/((d+e*x^2)*Sqrt[a+b*x^2+c*x^4]),x] - 1/e^2 \\[Star] Int[(d-e*x^2)/Sqrt[a+b*x^2+c*x^4],x] /;
        FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_12(symbols),
        with: [a__, b__, c__, d__, e__, x_],
        optional: [e__, b__, c__],
        x_free: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
        },
        rhs: {
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let quadratic = &d__ + &e__ * x_.pow(2);
            let first_integrand = Atom::num(1) / (quadratic * quartic.sqrt());
            let second_integrand = (&d__ - &e__ * x_.pow(2)) / quartic.sqrt();
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(d__.pow(2) / e__.pow(2), first)
                    + rubi_star(Atom::num(-1) / e__.pow(2), second)
        },
    ));
}

fn push_rules_rule_1665(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 1665,
        source: "Int[x_^4/((d_+e_.*x_^2)*Sqrt[a_+c_.*x_^4]),x_Symbol] :=
          d^2/e^2 \\[Star] Int[1/((d+e*x^2)*Sqrt[a+c*x^4]),x] - 1/e^2 \\[Star] Int[(d-e*x^2)/Sqrt[a+c*x^4],x] /;
        FreeQ[{a,c,d,e},x]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_13(symbols),
        with: [a__, c__, d__, e__, x_],
        optional: [e__, c__],
        x_free: [a__, c__, d__, e__],
        when: { freeq!([a__, c__, d__, e__], x_) },
        rhs: {
            let quartic = &a__ + &c__ * x_.pow(4);
            let quadratic = &d__ + &e__ * x_.pow(2);
            let first_integrand = Atom::num(1) / (quadratic * quartic.sqrt());
            let second_integrand = (&d__ - &e__ * x_.pow(2)) / quartic.sqrt();
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(d__.pow(2) / e__.pow(2), first)
                    + rubi_star(Atom::num(-1) / e__.pow(2), second)
        },
    ));
}

fn push_rules_rule_1660(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 1660,
        source: "Int[x_^4/((d_+e_.*x_^2)*Sqrt[a_+b_.*x_^2+c_.*x_^4]),x_Symbol] :=
          With[{q=Rt[c/a,2]},
          -1/(e*q) \\[Star] Int[(1-q*x^2)/Sqrt[a+b*x^2+c*x^4],x] +
          d^2/(e*(e-d*q)) \\[Star] Int[(1+q*x^2)/((d+e*x^2)*Sqrt[a+b*x^2+c*x^4]),x] /;
         EqQ[2*c*d-a*e*q,0]] /;
        FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && PosQ[c/a] && NeQ[c*d^2-a*e^2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_12(symbols),
        with: [a__, b__, c__, d__, e__, x_],
        optional: [e__, b__, c__],
        x_free: [a__, b__, c__, d__, e__],
        when: {
            let ok = freeq!([a__, b__, c__, d__, e__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && posq!(&c__ / &a__)
                && neq!(&c__ * d__.pow(2) - &a__ * e__.pow(2), 0);
            ok && {
                let q = rubi_rt(&(&c__ / &a__), 2);
                eqq!(Atom::num(2) * &c__ * &d__ - &a__ * &e__ * q, 0)
            }
        },
        rhs: {
            let q = rubi_rt(&(&c__ / &a__), 2);
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let quadratic = &d__ + &e__ * x_.pow(2);
            let first_integrand = (Atom::num(1) - &q * x_.pow(2)) / quartic.sqrt();
            let second_integrand = (Atom::num(1) + &q * x_.pow(2)) / (quadratic * quartic.sqrt());
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(Atom::num(-1) / (&e__ * &q), first)
                    + rubi_star(d__.pow(2) / (&e__ * (&e__ - &d__ * &q)), second)
        },
    ));
}

fn push_rules_rule_1661(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 1661,
        source: "Int[x_^4/((d_+e_.*x_^2)*Sqrt[a_+c_.*x_^4]),x_Symbol] :=
          With[{q=Rt[c/a,2]},
          -1/(e*q) \\[Star] Int[(1-q*x^2)/Sqrt[a+c*x^4],x] +
          d^2/(e*(e-d*q)) \\[Star] Int[(1+q*x^2)/((d+e*x^2)*Sqrt[a+c*x^4]),x] /;
         EqQ[2*c*d-a*e*q,0]] /;
        FreeQ[{a,c,d,e},x] && PosQ[c/a] && NeQ[c*d^2-a*e^2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_13(symbols),
        with: [a__, c__, d__, e__, x_],
        optional: [e__, c__],
        x_free: [a__, c__, d__, e__],
        when: {
            let ok = freeq!([a__, c__, d__, e__], x_)
                && posq!(&c__ / &a__)
                && neq!(&c__ * d__.pow(2) - &a__ * e__.pow(2), 0);
            ok && {
                let q = rubi_rt(&(&c__ / &a__), 2);
                eqq!(Atom::num(2) * &c__ * &d__ - &a__ * &e__ * q, 0)
            }
        },
        rhs: {
            let q = rubi_rt(&(&c__ / &a__), 2);
            let quartic = &a__ + &c__ * x_.pow(4);
            let quadratic = &d__ + &e__ * x_.pow(2);
            let first_integrand = (Atom::num(1) - &q * x_.pow(2)) / quartic.sqrt();
            let second_integrand = (Atom::num(1) + &q * x_.pow(2)) / (quadratic * quartic.sqrt());
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);

            rubi_star(Atom::num(-1) / (&e__ * &q), first)
                    + rubi_star(d__.pow(2) / (&e__ * (&e__ - &d__ * &q)), second)
        },
    ));
}

fn push_rules_rule_1662(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 1662,
        source: "Int[x_^4/((d_+e_.*x_^2)*Sqrt[a_+b_.*x_^2+c_.*x_^4]),x_Symbol] :=
          With[{q=Rt[c/a,2]},
          -(2*c*d-a*e*q)/(c*e*(e-d*q)) \\[Star] Int[1/Sqrt[a+b*x^2+c*x^4],x] -
          1/(e*q) \\[Star] Int[(1-q*x^2)/Sqrt[a+b*x^2+c*x^4],x] +
          d^2/(e*(e-d*q)) \\[Star] Int[(1+q*x^2)/((d+e*x^2)*Sqrt[a+b*x^2+c*x^4]),x]] /;
        FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && PosQ[c/a] && NeQ[c*d^2-a*e^2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_12(symbols),
        with: [a__, b__, c__, d__, e__, x_],
        optional: [e__, b__, c__],
        x_free: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && posq!(&c__ / &a__)
                && neq!(&c__ * d__.pow(2) - &a__ * e__.pow(2), 0)
        },
        rhs: {
            let q = rubi_rt(&(&c__ / &a__), 2);
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let quadratic = &d__ + &e__ * x_.pow(2);
            let first_integrand = Atom::num(1) / quartic.sqrt();
            let second_integrand = (Atom::num(1) - &q * x_.pow(2)) / quartic.sqrt();
            let third_integrand = (Atom::num(1) + &q * x_.pow(2)) / (quadratic * quartic.sqrt());
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);
            let third = rubi_rhs_int(&third_integrand, x_);
            let first_numerator = Atom::num(2) * &c__ * &d__ - &a__ * &e__ * &q;

            rubi_star(-first_numerator / (&c__ * &e__ * (&e__ - &d__ * &q)), first) + rubi_star(Atom::num(-1) / (&e__ * &q), second)
                    + rubi_star(d__.pow(2) / (&e__ * (&e__ - &d__ * &q)), third)
        },
    ));
}

fn push_rules_rule_1663(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, x_);
    rules.push(rubi_rule!(
        order: 1663,
        source: "Int[x_^4/((d_+e_.*x_^2)*Sqrt[a_+c_.*x_^4]),x_Symbol] :=
          With[{q=Rt[c/a,2]},
          -(2*c*d-a*e*q)/(c*e*(e-d*q)) \\[Star] Int[1/Sqrt[a+c*x^4],x] -
          1/(e*q) \\[Star] Int[(1-q*x^2)/Sqrt[a+c*x^4],x] +
          d^2/(e*(e-d*q)) \\[Star] Int[(1+q*x^2)/((d+e*x^2)*Sqrt[a+c*x^4]),x]] /;
        FreeQ[{a,c,d,e},x] && PosQ[c/a] && NeQ[c*d^2-a*e^2,0]",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_13(symbols),
        with: [a__, c__, d__, e__, x_],
        optional: [e__, c__],
        x_free: [a__, c__, d__, e__],
        when: {
            freeq!([a__, c__, d__, e__], x_)
                && posq!(&c__ / &a__)
                && neq!(&c__ * d__.pow(2) - &a__ * e__.pow(2), 0)
        },
        rhs: {
            let q = rubi_rt(&(&c__ / &a__), 2);
            let quartic = &a__ + &c__ * x_.pow(4);
            let quadratic = &d__ + &e__ * x_.pow(2);
            let first_integrand = Atom::num(1) / quartic.sqrt();
            let second_integrand = (Atom::num(1) - &q * x_.pow(2)) / quartic.sqrt();
            let third_integrand = (Atom::num(1) + &q * x_.pow(2)) / (quadratic * quartic.sqrt());
            let first = rubi_rhs_int(&first_integrand, x_);
            let second = rubi_rhs_int(&second_integrand, x_);
            let third = rubi_rhs_int(&third_integrand, x_);
            let first_numerator = Atom::num(2) * &c__ * &d__ - &a__ * &e__ * &q;

            rubi_star(-first_numerator / (&c__ * &e__ * (&e__ - &d__ * &q)), first) + rubi_star(Atom::num(-1) / (&e__ * &q), second)
                    + rubi_star(d__.pow(2) / (&e__ * (&e__ - &d__ * &q)), third)
        },
    ));
}

fn push_rules_rule_1666(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, x_);
    rules.push(rubi_rule!(
        order: 1666,
        source: "Int[x_^m_/((d_+e_.*x_^2)*Sqrt[a_+b_.*x_^2+c_.*x_^4]),x_Symbol] :=
          x^(m-5)*Sqrt[a+b*x^2+c*x^4]/(c*e*(m-3)) -
          1/(c*e*(m-3)) \\[Star] Int[x^(m-6)/((d+e*x^2)*Sqrt[a+b*x^2+c*x^4])*
            Simp[a*d*(m-5)+(a*e*(m-5)+b*d*(m-4))*x^2+(b*e*(m-4)+c*d*(m-3))*x^4,x],x] /;
        FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && IGtQ[m/2,2]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_18(symbols),
        with: [a__, b__, c__, d__, e__, m_, x_],
        optional: [e__, b__, c__],
        x_free: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && igtq!(&m_ / Atom::num(2), 2)
        },
        rhs: {
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let quadratic = &d__ + &e__ * x_.pow(2);
            let denominator = &c__ * &e__ * (&m_ - Atom::num(3));
            let direct = x_.pow(&m_ - Atom::num(5)) * quartic.sqrt() / &denominator;
            let simp = rubi_simp(
                &(&a__ * &d__ * (&m_ - Atom::num(5))
                    + (&a__ * &e__ * (&m_ - Atom::num(5)) + &b__ * &d__ * (&m_ - Atom::num(4))) * x_.pow(2)
                    + (&b__ * &e__ * (&m_ - Atom::num(4)) + &c__ * &d__ * (&m_ - Atom::num(3))) * x_.pow(4)),
                x_,
            );
            let recursive_integrand = x_.pow(&m_ - Atom::num(6)) * simp / (quadratic * quartic.sqrt());
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) + rubi_star(Atom::num(-1) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_1667(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, m_, x_);
    rules.push(rubi_rule!(
        order: 1667,
        source: "Int[x_^m_/((d_+e_.*x_^2)*Sqrt[a_+c_.*x_^4]),x_Symbol] :=
          x^(m-5)*Sqrt[a+c*x^4]/(c*e*(m-3)) -
          1/(c*e*(m-3)) \\[Star] Int[x^(m-6)/((d+e*x^2)*Sqrt[a+c*x^4])*Simp[a*d*(m-5)+a*e*(m-5)*x^2+c*d*(m-3)*x^4,x],x] /;
        FreeQ[{a,c,d,e},x] && IGtQ[m/2,2]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_19(symbols),
        with: [a__, c__, d__, e__, m_, x_],
        optional: [e__, c__],
        x_free: [a__, c__, d__, e__],
        when: { freeq!([a__, c__, d__, e__], x_) && igtq!(&m_ / Atom::num(2), 2) },
        rhs: {
            let quartic = &a__ + &c__ * x_.pow(4);
            let quadratic = &d__ + &e__ * x_.pow(2);
            let denominator = &c__ * &e__ * (&m_ - Atom::num(3));
            let direct = x_.pow(&m_ - Atom::num(5)) * quartic.sqrt() / &denominator;
            let simp = rubi_simp(
                &(&a__ * &d__ * (&m_ - Atom::num(5))
                    + &a__ * &e__ * (&m_ - Atom::num(5)) * x_.pow(2)
                    + &c__ * &d__ * (&m_ - Atom::num(3)) * x_.pow(4)),
                x_,
            );
            let recursive_integrand = x_.pow(&m_ - Atom::num(6)) * simp / (quadratic * quartic.sqrt());
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) + rubi_star(Atom::num(-1) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_1668(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, x_);
    rules.push(rubi_rule!(
        order: 1668,
        source: "Int[x_^m_/((d_+e_.*x_^2)*Sqrt[a_+b_.*x_^2+c_.*x_^4]),x_Symbol] :=
          x^(m+1)*Sqrt[a+b*x^2+c*x^4]/(a*d*(m+1)) -
          1/(a*d*(m+1)) \\[Star] Int[x^(m+2)/((d+e*x^2)*Sqrt[a+b*x^2+c*x^4])*
            Simp[a*e*(m+1)+b*d*(m+2)+(b*e*(m+2)+c*d*(m+3))*x^2+c*e*(m+3)*x^4,x],x] /;
        FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && ILtQ[m/2,0]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_18(symbols),
        with: [a__, b__, c__, d__, e__, m_, x_],
        optional: [e__, b__, c__],
        x_free: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && iltq!(&m_ / Atom::num(2), 0)
        },
        rhs: {
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let quadratic = &d__ + &e__ * x_.pow(2);
            let denominator = &a__ * &d__ * (&m_ + Atom::num(1));
            let direct = x_.pow(&m_ + Atom::num(1)) * quartic.sqrt() / &denominator;
            let simp = rubi_simp(
                &(&a__ * &e__ * (&m_ + Atom::num(1))
                    + &b__ * &d__ * (&m_ + Atom::num(2))
                    + (&b__ * &e__ * (&m_ + Atom::num(2)) + &c__ * &d__ * (&m_ + Atom::num(3))) * x_.pow(2)
                    + &c__ * &e__ * (&m_ + Atom::num(3)) * x_.pow(4)),
                x_,
            );
            let recursive_integrand = x_.pow(&m_ + Atom::num(2)) * simp / (quadratic * quartic.sqrt());
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) + rubi_star(Atom::num(-1) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_1669(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, m_, x_);
    rules.push(rubi_rule!(
        order: 1669,
        source: "Int[x_^m_/((d_+e_.*x_^2)*Sqrt[a_+c_.*x_^4]),x_Symbol] :=
          x^(m+1)*Sqrt[a+c*x^4]/(a*d*(m+1)) -
          1/(a*d*(m+1)) \\[Star] Int[x^(m+2)/((d+e*x^2)*Sqrt[a+c*x^4])*Simp[a*e*(m+1)+c*d*(m+3)*x^2+c*e*(m+3)*x^4,x],x] /;
        FreeQ[{a,c,d,e},x] && ILtQ[m/2,0]",
        desc: "Simplify the integrand and continue with the simpler form.",
        refs: [],
        pattern:  rubi_shared_pattern_19(symbols),
        with: [a__, c__, d__, e__, m_, x_],
        optional: [e__, c__],
        x_free: [a__, c__, d__, e__],
        when: { freeq!([a__, c__, d__, e__], x_) && iltq!(&m_ / Atom::num(2), 0) },
        rhs: {
            let quartic = &a__ + &c__ * x_.pow(4);
            let quadratic = &d__ + &e__ * x_.pow(2);
            let denominator = &a__ * &d__ * (&m_ + Atom::num(1));
            let direct = x_.pow(&m_ + Atom::num(1)) * quartic.sqrt() / &denominator;
            let simp = rubi_simp(
                &(&a__ * &e__ * (&m_ + Atom::num(1))
                    + &c__ * &d__ * (&m_ + Atom::num(3)) * x_.pow(2)
                    + &c__ * &e__ * (&m_ + Atom::num(3)) * x_.pow(4)),
                x_,
            );
            let recursive_integrand = x_.pow(&m_ + Atom::num(2)) * simp / (quadratic * quartic.sqrt());
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_) + rubi_star(Atom::num(-1) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_1670(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, b__, c__, d__, e__, m_, x_);
    rules.push(rubi_rule!(
        order: 1670,
        source: "Int[x_^m_/(Sqrt[d_+e_.*x_^2]*Sqrt[a_+b_.*x_^2+c_.*x_^4]),x_Symbol] :=
          x^3*Sqrt[e+d/x^2]*Sqrt[c+b/x^2+a/x^4]/(Sqrt[d+e*x^2]*Sqrt[a+b*x^2+c*x^4]) \\[Star]
            Int[x^(m-3)/(Sqrt[e+d/x^2]*Sqrt[c+b/x^2+a/x^4]),x] /;
        FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && IntegerQ[m/2]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: x_.pow(m_) / ((d__ + e__ * x_.pow(2)).sqrt() * (a__ + b__ * x_.pow(2) + c__ * x_.pow(4)).sqrt()),
        with: [a__, b__, c__, d__, e__, m_, x_],
        optional: [e__, b__, c__],
        x_free: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && integerq!(&m_ / Atom::num(2))
        },
        rhs: {
            let quadratic = &d__ + &e__ * x_.pow(2);
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let inverted_quadratic = &e__ + &d__ / x_.pow(2);
            let inverted_quartic = &c__ + &b__ / x_.pow(2) + &a__ / x_.pow(4);
            let recursive_integrand =
                x_.pow(&m_ - Atom::num(3)) / (inverted_quadratic.sqrt() * inverted_quartic.sqrt());
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let coefficient = x_.pow(3) * inverted_quadratic.sqrt() * inverted_quartic.sqrt()
                / (quadratic.sqrt() * quartic.sqrt());

            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_1671(rules: &mut Vec<RubiRule>) {
    rubi_symb!(a__, c__, d__, e__, m_, x_);
    rules.push(rubi_rule!(
        order: 1671,
        source: "Int[x_^m_/(Sqrt[d_+e_.*x_^2]*Sqrt[a_+c_.*x_^4]),x_Symbol] :=
          x^3*Sqrt[e+d/x^2]*Sqrt[c+a/x^4]/(Sqrt[d+e*x^2]*Sqrt[a+c*x^4]) \\[Star]
            Int[x^(m-3)/(Sqrt[e+d/x^2]*Sqrt[c+a/x^4]),x] /;
        FreeQ[{a,c,d,e},x] && IntegerQ[m/2]",
        desc: "Piecewise constant extraction",
        refs: [],
        pattern: x_.pow(m_) / ((d__ + e__ * x_.pow(2)).sqrt() * (a__ + c__ * x_.pow(4)).sqrt()),
        with: [a__, c__, d__, e__, m_, x_],
        optional: [e__, c__],
        x_free: [a__, c__, d__, e__],
        when: { freeq!([a__, c__, d__, e__], x_) && integerq!(&m_ / Atom::num(2)) },
        rhs: {
            let quadratic = &d__ + &e__ * x_.pow(2);
            let quartic = &a__ + &c__ * x_.pow(4);
            let inverted_quadratic = &e__ + &d__ / x_.pow(2);
            let inverted_quartic = &c__ + &a__ / x_.pow(4);
            let recursive_integrand =
                x_.pow(&m_ - Atom::num(3)) / (inverted_quadratic.sqrt() * inverted_quartic.sqrt());
            let recursive = rubi_rhs_int(&recursive_integrand, x_);
            let coefficient = x_.pow(3) * inverted_quadratic.sqrt() * inverted_quartic.sqrt()
                / (quadratic.sqrt() * quartic.sqrt());

            rubi_star(coefficient, recursive)
        },
    ));
}

fn push_rules_rule_1672(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1672,
        source: "Int[x_^m_*(d_+e_.*x_^2)^q_*(a_+b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
          With[{f=Coeff[PolynomialRemainder[x^m*(d+e*x^2)^q,a+b*x^2+c*x^4,x],x,0],
                g=Coeff[PolynomialRemainder[x^m*(d+e*x^2)^q,a+b*x^2+c*x^4,x],x,2]},
          x*(a+b*x^2+c*x^4)^(p+1)*(a*b*g-f*(b^2-2*a*c)-c*(b*f-2*a*g)*x^2)/(2*a*(p+1)*(b^2-4*a*c)) +
          1/(2*a*(p+1)*(b^2-4*a*c)) \\[Star] Int[(a+b*x^2+c*x^4)^(p+1)*
            Simp[ExpandToSum[2*a*(p+1)*(b^2-4*a*c)*PolynomialQuotient[x^m*(d+e*x^2)^q,a+b*x^2+c*x^4,x]+
              b^2*f*(2*p+3)-2*a*c*f*(4*p+5)-a*b*g+c*(4*p+7)*(b*f-2*a*g)*x^2,x],x],x]] /;
        FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && LtQ[p,-1] && IGtQ[q,1] && IGtQ[m/2,0]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_16(symbols),
        with: [a__, b__, c__, d__, e__, m_, p_, q_, x_],
        optional: [e__, b__, c__],
        x_free: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && ltq!(p_, -1)
                && igtq!(q_, 1)
                && igtq!(&m_ / Atom::num(2), 0)
        },
        rhs: {
            let discriminant = b__.pow(2) - Atom::num(4) * &a__ * &c__;
            let denominator = Atom::num(2) * &a__ * (&p_ + Atom::num(1)) * &discriminant;
            let quadratic = &d__ + &e__ * x_.pow(2);
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let dividend = x_.pow(&m_) * quadratic.pow(&q_);
            let remainder = rubi_polynomial_remainder(&dividend, &quartic, x_).rubi_rhs();
            let f_coeff = rubi_coeff(&remainder, x_, 0).rubi_rhs();
            let g_coeff = rubi_coeff(&remainder, x_, 2).rubi_rhs();
            let quotient = rubi_polynomial_quotient(&dividend, &quartic, x_).rubi_rhs();

            let direct_numerator = &a__ * &b__ * &g_coeff
                - &f_coeff * (b__.pow(2) - Atom::num(2) * &a__ * &c__)
                - &c__ * (&b__ * &f_coeff - Atom::num(2) * &a__ * &g_coeff) * x_.pow(2);
            let direct = x_ * quartic.pow(&p_ + Atom::num(1)) * direct_numerator / &denominator;
            let expand_to_sum = rubi_expand_to_sum(
                &(Atom::num(2) * &a__ * (&p_ + Atom::num(1)) * &discriminant * quotient
                    + b__.pow(2) * &f_coeff * (Atom::num(2) * &p_ + Atom::num(3))
                    - Atom::num(2) * &a__ * &c__ * &f_coeff * (Atom::num(4) * &p_ + Atom::num(5))
                    - &a__ * &b__ * &g_coeff
                    + &c__ * (Atom::num(4) * &p_ + Atom::num(7)) * (&b__ * &f_coeff - Atom::num(2) * &a__ * &g_coeff) * x_.pow(2)),
                x_,
            );
            let simp = rubi_simp(&expand_to_sum, x_);
            let recursive_integrand = quartic.pow(&p_ + Atom::num(1)) * simp;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_)
                    + rubi_star(Atom::num(1) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_1673(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, m_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1673,
        source: "Int[x_^m_*(d_+e_.*x_^2)^q_*(a_+b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
          With[{f=Coeff[PolynomialRemainder[x^m*(d+e*x^2)^q,a+b*x^2+c*x^4,x],x,0],
                g=Coeff[PolynomialRemainder[x^m*(d+e*x^2)^q,a+b*x^2+c*x^4,x],x,2]},
          x*(a+b*x^2+c*x^4)^(p+1)*(a*b*g-f*(b^2-2*a*c)-c*(b*f-2*a*g)*x^2)/(2*a*(p+1)*(b^2-4*a*c)) +
          1/(2*a*(p+1)*(b^2-4*a*c)) \\[Star] Int[x^m*(a+b*x^2+c*x^4)^(p+1)*
            Simp[ExpandToSum[2*a*(p+1)*(b^2-4*a*c)*x^(-m)*PolynomialQuotient[x^m*(d+e*x^2)^q,a+b*x^2+c*x^4,x]+
              (b^2*f*(2*p+3)-2*a*c*f*(4*p+5)-a*b*g)*x^(-m)+c*(4*p+7)*(b*f-2*a*g)*x^(2-m),x],x],x]] /;
        FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && LtQ[p,-1] && IGtQ[q,1] && ILtQ[m/2,0]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_16(symbols),
        with: [a__, b__, c__, d__, e__, m_, p_, q_, x_],
        optional: [e__, b__, c__],
        x_free: [a__, b__, c__, d__, e__],
        when: {
            freeq!([a__, b__, c__, d__, e__], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && ltq!(p_, -1)
                && igtq!(q_, 1)
                && iltq!(&m_ / Atom::num(2), 0)
        },
        rhs: {
            let discriminant = b__.pow(2) - Atom::num(4) * &a__ * &c__;
            let denominator = Atom::num(2) * &a__ * (&p_ + Atom::num(1)) * &discriminant;
            let quadratic = &d__ + &e__ * x_.pow(2);
            let quartic = &a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4);
            let dividend = x_.pow(&m_) * quadratic.pow(&q_);
            let remainder = rubi_polynomial_remainder(&dividend, &quartic, x_).rubi_rhs();
            let f_coeff = rubi_coeff(&remainder, x_, 0).rubi_rhs();
            let g_coeff = rubi_coeff(&remainder, x_, 2).rubi_rhs();
            let quotient = rubi_polynomial_quotient(&dividend, &quartic, x_).rubi_rhs();

            let direct_numerator = &a__ * &b__ * &g_coeff
                - &f_coeff * (b__.pow(2) - Atom::num(2) * &a__ * &c__)
                - &c__ * (&b__ * &f_coeff - Atom::num(2) * &a__ * &g_coeff) * x_.pow(2);
            let direct = x_ * quartic.pow(&p_ + Atom::num(1)) * direct_numerator / &denominator;
            let expand_to_sum = rubi_expand_to_sum(
                &(Atom::num(2) * &a__ * (&p_ + Atom::num(1)) * &discriminant * x_.pow(-&m_) * quotient
                    + (b__.pow(2) * &f_coeff * (Atom::num(2) * &p_ + Atom::num(3))
                        - Atom::num(2) * &a__ * &c__ * &f_coeff * (Atom::num(4) * &p_ + Atom::num(5))
                        - &a__ * &b__ * &g_coeff)
                        * x_.pow(-&m_)
                    + &c__
                        * (Atom::num(4) * &p_ + Atom::num(7))
                        * (&b__ * &f_coeff - Atom::num(2) * &a__ * &g_coeff)
                        * x_.pow(Atom::num(2) - &m_)),
                x_,
            );
            let simp = rubi_simp(&expand_to_sum, x_);
            let recursive_integrand = x_.pow(&m_) * quartic.pow(&p_ + Atom::num(1)) * simp;
            let recursive = rubi_rhs_int(&recursive_integrand, x_);

            rubi_simp(&(direct), x_)
                    + rubi_star(Atom::num(1) / denominator, recursive)
        },
    ));
}

fn push_rules_rule_1674(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1674,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^q_.*(a_+b_.*x_^2+c_.*x_^4)^p_.,x_Symbol] :=
          Int[ExpandIntegrand[(f*x)^m*(d+e*x^2)^q*(a+b*x^2+c*x^4)^p,x],x] /;
        FreeQ[{a,b,c,d,e,f,m,p,q},x] && NeQ[b^2-4*a*c,0] && (IGtQ[p,0] || IGtQ[q,0] || IntegersQ[m,q])",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [a__, b__, c__, d__, e__, f__, m_, p_, q_, x_],
        optional: [f__, m_, e__, q_, b__, c__, p_],
        x_free: [a__, b__, c__, d__, e__, f__, m_, p_, q_],
        when: {
            freeq!([a__, b__, c__, d__, e__, f__, m_, p_, q_], x_)
                && neq!(b__.pow(2) - Atom::num(4) * &a__ * &c__, 0)
                && (igtq!(p_, 0) || igtq!(q_, 0) || integersq!([m_, q_]))
        },
        rhs: {
            let integrand = (&f__ * x_).pow(&m_)
                * (&d__ + &e__ * x_.pow(2)).pow(&q_)
                * (&a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4)).pow(&p_);
            let expanded = rubi_expand_integrand(&integrand, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_1675(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, m_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1675,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^q_.*(a_+c_.*x_^4)^p_.,x_Symbol] :=
          Int[ExpandIntegrand[(f*x)^m*(d+e*x^2)^q*(a+c*x^4)^p,x],x] /;
        FreeQ[{a,c,d,e,f,m,p,q},x] && (IGtQ[p,0] || IGtQ[q,0] || IntegersQ[m,q])",
        desc: "Algebraic expansion",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [a__, c__, d__, e__, f__, m_, p_, q_, x_],
        optional: [f__, m_, e__, q_, c__, p_],
        x_free: [a__, c__, d__, e__, f__, m_, p_, q_],
        when: {
            freeq!([a__, c__, d__, e__, f__, m_, p_, q_], x_)
                && (igtq!(p_, 0) || igtq!(q_, 0) || integersq!([m_, q_]))
        },
        rhs: {
            let integrand =
                (&f__ * x_).pow(&m_) * (&d__ + &e__ * x_.pow(2)).pow(&q_) * (&a__ + &c__ * x_.pow(4)).pow(&p_);
            let expanded = rubi_expand_integrand(&integrand, x_);
            rubi_rhs_int(&expanded, x_)
        },
    ));
}

fn push_rules_rule_1676(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, m_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1676,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^q_*(a_+c_.*x_^4)^p_,x_Symbol] :=
          (f*x)^m/x^m \\[Star] Int[ExpandIntegrand[x^m*(a+c*x^4)^p,(d/(d^2-e^2*x^4)-e*x^2/(d^2-e^2*x^4))^(-q),x],x] /;
        FreeQ[{a,c,d,e,f,m,p},x] && Not[IntegerQ[p]] && ILtQ[q,0]",
        desc: "Expand the integrand and integrate the resulting terms.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [a__, c__, d__, e__, f__, m_, p_, q_, x_],
        optional: [f__, m_, e__, c__],
        x_free: [a__, c__, d__, e__, f__, m_, p_],
        when: {
            freeq!([a__, c__, d__, e__, f__, m_, p_], x_)
                && !integerq!(p_)
                && iltq!(q_, 0)
        },
        rhs: {
            let fx = &f__ * x_;
            let quartic = &a__ + &c__ * x_.pow(4);
            let denominator = d__.pow(2) - e__.pow(2) * x_.pow(4);
            let u = x_.pow(&m_) * quartic.pow(&p_);
            let v = (&d__ / &denominator - &e__ * x_.pow(2) / denominator).pow(-&q_);
            let expanded = rubi_expand_integrand_product(&u, &v, x_);
            let recursive = rubi_rhs_int(&expanded, x_);

            rubi_star(fx.pow(&m_) / x_.pow(&m_), recursive)
        },
    ));
}

fn push_rules_rule_1677(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, b__, c__, d__, e__, f__, m_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1677,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^q_.*(a_+b_.*x_^2+c_.*x_^4)^p_.,x_Symbol] :=
          Unintegrable[(f*x)^m*(d+e*x^2)^q*(a+b*x^2+c*x^4)^p,x] /;
        FreeQ[{a,b,c,d,e,f,m,p,q},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_4(symbols),
        with: [f__, m_, d__, e__, q_, a__, b__, c__, p_, x_],
        optional: [f__, m_, e__, q_, b__, c__, p_],
        x_free: [a__, b__, c__, d__, e__, f__, m_, p_, q_],
        when: { freeq!([a__, b__, c__, d__, e__, f__, m_, p_, q_], x_) },
        rhs: {
            let integrand = (&f__ * x_).pow(&m_)
                * (&d__ + &e__ * x_.pow(2)).pow(&q_)
                * (&a__ + &b__ * x_.pow(2) + &c__ * x_.pow(4)).pow(&p_);
            rubi_unintegrable(integrand, x_)
        },
    ));
}

fn push_rules_rule_1678(rules: &mut Vec<RubiRule>) {
    rubi_symb!(symbols; a__, c__, d__, e__, f__, m_, p_, q_, x_);
    rules.push(rubi_rule!(
        order: 1678,
        source: "Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^q_.*(a_+c_.*x_^4)^p_.,x_Symbol] :=
          Unintegrable[(f*x)^m*(d+e*x^2)^q*(a+c*x^4)^p,x] /;
        FreeQ[{a,c,d,e,f,m,p,q},x]",
        desc: "Mark the integral as unintegrable by Rubi's terminal rule.",
        refs: [],
        pattern:  rubi_shared_pattern_5(symbols),
        with: [f__, m_, d__, e__, q_, a__, c__, p_, x_],
        optional: [f__, m_, e__, q_, c__, p_],
        x_free: [a__, c__, d__, e__, f__, m_, p_, q_],
        when: { freeq!([a__, c__, d__, e__, f__, m_, p_, q_], x_) },
        rhs: {
            let integrand =
                (&f__ * x_).pow(&m_) * (&d__ + &e__ * x_.pow(2)).pow(&q_) * (&a__ + &c__ * x_.pow(4)).pow(&p_);
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
    let m_ = symbols.m_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (f__ * x_).pow(m_) * (a__ + b__ * x_.pow(2) + c__ * x_.pow(4)).pow(p_) / (d__ + e__ * x_.pow(2))
}

#[inline(never)]
fn rubi_shared_pattern_1(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (f__ * x_).pow(m_) * (a__ + c__ * x_.pow(4)).pow(p_) / (d__ + e__ * x_.pow(2))
}

#[inline(never)]
fn rubi_shared_pattern_2(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (f__ * x_).pow(m_) * (d__ + e__ * x_.pow(2)) * (a__ + b__ * x_.pow(2) + c__ * x_.pow(4)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_3(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    (f__ * x_).pow(m_) * (d__ + e__ * x_.pow(2)) * (a__ + c__ * x_.pow(4)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_4(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let p_ = symbols.p_;
    let q_ = symbols.q_;
    let x_ = symbols.x_;
    (f__ * x_).pow(m_)
        * (d__ + e__ * x_.pow(2)).pow(q_)
        * (a__ + b__ * x_.pow(2) + c__ * x_.pow(4)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_5(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let p_ = symbols.p_;
    let q_ = symbols.q_;
    let x_ = symbols.x_;
    (f__ * x_).pow(m_) * (d__ + e__ * x_.pow(2)).pow(q_) * (a__ + c__ * x_.pow(4)).pow(p_)
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
    let q_ = symbols.q_;
    let x_ = symbols.x_;
    (f__ * x_).pow(m_) * (d__ + e__ * x_.pow(2)).pow(q_) / (a__ + b__ * x_.pow(2) + c__ * x_.pow(4))
}

#[inline(never)]
fn rubi_shared_pattern_7(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let q_ = symbols.q_;
    let x_ = symbols.x_;
    (f__ * x_).pow(m_) * (d__ + e__ * x_.pow(2)).pow(q_) / (a__ + c__ * x_.pow(4))
}

#[inline(never)]
fn rubi_shared_pattern_8(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let x_ = symbols.x_;
    (f__ * x_).pow(m_) * (d__ + e__ * x_.pow(2)) / (a__ + b__ * x_.pow(2) + c__ * x_.pow(4))
}

#[inline(never)]
fn rubi_shared_pattern_9(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let f__ = symbols.f__;
    let m_ = symbols.m_;
    let x_ = symbols.x_;
    (f__ * x_).pow(m_) * (d__ + e__ * x_.pow(2)) / (a__ + c__ * x_.pow(4))
}

#[inline(never)]
fn rubi_shared_pattern_10(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let x_ = symbols.x_;
    x_.pow(2) / ((d__ + e__ * x_.pow(2)) * (a__ + b__ * x_.pow(2) + c__ * x_.pow(4)).sqrt())
}

#[inline(never)]
fn rubi_shared_pattern_11(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let x_ = symbols.x_;
    x_.pow(2) / ((d__ + e__ * x_.pow(2)) * (a__ + c__ * x_.pow(4)).sqrt())
}

#[inline(never)]
fn rubi_shared_pattern_12(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let x_ = symbols.x_;
    x_.pow(4) / ((d__ + e__ * x_.pow(2)) * (a__ + b__ * x_.pow(2) + c__ * x_.pow(4)).sqrt())
}

#[inline(never)]
fn rubi_shared_pattern_13(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let x_ = symbols.x_;
    x_.pow(4) / ((d__ + e__ * x_.pow(2)) * (a__ + c__ * x_.pow(4)).sqrt())
}

#[inline(never)]
fn rubi_shared_pattern_14(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let m_ = symbols.m_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    x_.pow(m_) * (a__ + b__ * x_.pow(2) + c__ * x_.pow(4)).pow(p_) / (d__ + e__ * x_.pow(2))
}

#[inline(never)]
fn rubi_shared_pattern_15(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let m_ = symbols.m_;
    let p_ = symbols.p_;
    let x_ = symbols.x_;
    x_.pow(m_) * (a__ + c__ * x_.pow(4)).pow(p_) / (d__ + e__ * x_.pow(2))
}

#[inline(never)]
fn rubi_shared_pattern_16(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let m_ = symbols.m_;
    let p_ = symbols.p_;
    let q_ = symbols.q_;
    let x_ = symbols.x_;
    x_.pow(m_) * (d__ + e__ * x_.pow(2)).pow(q_) * (a__ + b__ * x_.pow(2) + c__ * x_.pow(4)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_17(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let m_ = symbols.m_;
    let p_ = symbols.p_;
    let q_ = symbols.q_;
    let x_ = symbols.x_;
    x_.pow(m_) * (d__ + e__ * x_.pow(2)).pow(q_) * (a__ + c__ * x_.pow(4)).pow(p_)
}

#[inline(never)]
fn rubi_shared_pattern_18(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let b__ = symbols.b__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let m_ = symbols.m_;
    let x_ = symbols.x_;
    x_.pow(m_) / ((d__ + e__ * x_.pow(2)) * (a__ + b__ * x_.pow(2) + c__ * x_.pow(4)).sqrt())
}

#[inline(never)]
fn rubi_shared_pattern_19(symbols: &RubiSymbols) -> Atom {
    let a__ = symbols.a__;
    let c__ = symbols.c__;
    let d__ = symbols.d__;
    let e__ = symbols.e__;
    let m_ = symbols.m_;
    let x_ = symbols.x_;
    x_.pow(m_) / ((d__ + e__ * x_.pow(2)) * (a__ + c__ * x_.pow(4)).sqrt())
}
